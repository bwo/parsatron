(ns the.parsatron
  (:refer-clojure :exclude [char])
  (:require [clojure.string :as str]))

(defrecord InputState [input pos])

(defrecord Continue [fn])
(defrecord Ok [item])
(defrecord Err [errors])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; position

(defprotocol ParseError
  (show-error [this])
  (merge-errors [this other]))

(defprotocol Position
  (increment-position [self item])
  (show-pos [self])
  (error-at [self msgs]))

(defrecord LineColParseError [pos msgs]
  ParseError
  (show-error [_] (str (str/join ", " msgs)
                       " at "
                       (show-pos pos)))
  (merge-errors [this other]
    (LineColParseError. pos (mapcat :msgs this other))))

(defrecord LineColPos [line column]
  Position
  (increment-position [_ item]
    (if (= item \newline)
      (LineColPos. (inc line) 1)
      (LineColPos. line (inc column))))
  (show-pos [_] (str "line: " line " column: " column))
  (error-at [this msg] (LineColParseError. this [msg])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; errors


(defn unknown-error [{:keys [pos] :as state}]
  (error-at pos "Error"))

(defn unexpect-error [msg pos]
  (error-at pos (str "Unexpected " msg)))

(defn expect-error [msg pos]
  (error-at pos (str "Expected " msg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; trampoline
(defn parsatron-poline
  "A trampoline for executing potentially stack-blowing recursive
   functions without running out of stack space. This particular
   trampoline differs from clojure.core/trampoline by requiring
   continuations to be wrapped in a Continue record. Will loop until
   the value is no longer a Continue record, returning that."
  [f & args]
  (loop [value (apply f args)]
    (condp instance? value
      Continue (recur ((:fn value)))
      value)))

(defn sequentially [f value]
  (condp instance? value
    Continue (Continue. #(sequentially f ((:fn value))))
    (f value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; m
(defn always
  "A parser that always succeeds with the value given and consumes no
   input"
  [x]
  (fn [state cok cerr eok eerr]
    (eok x state)))

(defn bind
  "Parse p, and then q. The function f must be of one argument, it
   will be given the value of p and must return the q to follow p"
  [p f]
  (fn [state cok cerr eok eerr]
    (letfn [(pcok [item state]
              (sequentially
               (fn [q] (Continue. #(q state cok cerr cok cerr)))
               (f item)))
            (peok [item state]
              (sequentially
               (fn [q] (Continue. #(q state cok cerr eok eerr)))
               (f item)))]
      (Continue. #(p state pcok cerr peok eerr)))))

(defn nxt
  "Parse p and then q, returning q's value and discarding p's"
  [p q]
  (bind p (fn [_] q)))

(defmacro defparser
  "Defines a new parser. Parsers are simply functions that accept the
   5 arguments state, cok, cerr, eok, eerr but this macro takes care
   of writing that ceremony for you and wraps the body in a >>"
  [name args & body]
  `(defn ~name ~args
     (fn [state# cok# cerr# eok# eerr#]
       (let [p# (>> ~@body)]
         (Continue. #(p# state# cok# cerr# eok# eerr#))))))

(defmacro >>
  "Expands into nested nxt forms"
  ([m] m)
  ([m n] `(nxt ~m ~n))
  ([m n & ms] `(nxt ~m (>> ~n ~@ms))))

(defmacro let->>
  "Expands into nested bind forms"
  [[& bindings] & body]
  (let [[bind-form p] (take 2 bindings)]
    (if (= 2 (count bindings))
      `(bind ~p (fn [~bind-form] ~@body))
      `(bind ~p (fn [~bind-form] (let->> ~(drop 2 bindings) ~@body))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; m+
(defn never
  "A parser that always fails, consuming no input"
  []
  (fn [state cok cerr eok eerr]
    (eerr (unknown-error state))))

(defn either
  "A parser that tries p, upon success, returning its value, and upon
   failure (if no input was consumed) tries to parse q"
  [p q]
  (fn [state cok cerr eok eerr]
    (letfn [(peerr [err-from-p]
              (letfn [(qeerr [err-from-q]
                        (eerr (merge-errors err-from-p err-from-q)))]
                (Continue. #(q state cok cerr eok qeerr))))]
      (Continue. #(p state cok cerr eok peerr)))))

(defn attempt
  "A parser that will attempt to parse p, and upon failure never
   consume any input"
  [p]
  (fn [state cok cerr eok eerr]
    (Continue. #(p state cok eerr eok eerr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; token
(defn token
  "Consume a single item from the head of the input if (consume? item)
   is not nil. This parser will fail to consume if either the consume?
   test returns nil or if the input is empty"
  [consume?]
  (fn [{:keys [input pos] :as state} cok cerr eok eerr]
    (if-let [tok (first input)]
      (if (consume? tok)
        (cok tok (InputState. (rest input) (increment-position pos tok)))
        (eerr (unexpect-error (str "token '" tok "'") pos)))
      (eerr (unexpect-error "end of input" pos)))))

(defn many
  "Consume zero or more p. A RuntimeException will be thrown if this
   combinator is applied to a parser that accepts the empty string, as
   that would cause the parser to loop forever"
  [p]
  (letfn [(many-err [_ _]
            (throw (RuntimeException. "Combinator '*' is applied to a parser that accepts an empty string")))
          (safe-p [state cok cerr eok eerr]
            (Continue. #(p state cok cerr many-err eerr)))]
    (either
     (let->> [x safe-p
              xs (many safe-p)]
       (always (cons x xs)))
     (always []))))

(defn times
  "Consume exactly n number of p"
  [n p]
  (if (= n 0)
    (always [])
    (fn [state cok cerr eok eerr]
      (letfn [(pcok [item state]
                (let [q (times (dec n) p)]
                  (letfn [(qcok [items state]
                            (cok (cons item items) state))]
                    (Continue. #(q state qcok cerr qcok eerr)))))
              (peok [item state]
                (eok (repeat n item) state))]
        (Continue. #(p state pcok cerr peok eerr))))))

(defn lookahead
  "A parser that upon success consumes no input, but returns what was
   parsed"
  [p]
  (fn [state cok cerr eok eerr]
    (letfn [(ok [item _]
              (eok item state))]
      (Continue. #(p state ok cerr eok eerr)))))

(defn choice
  "A varargs version of either that tries each given parser in turn,
   returning the value of the first one that succeeds"
  [& parsers]
  (if (empty? parsers)
    (never)
    (let [p (first parsers)]
      (either p (apply choice (rest parsers))))))

(defn eof
  "A parser to detect the end of input. If there is nothing more to
   consume from the underlying input, this parser suceeds with a nil
   value, otherwise it fails"
  []
  (fn [{:keys [input pos] :as state} cok cerr eok eerr]
    (if (empty? input)
      (eok nil state)
      (eerr (expect-error "end of input" pos)))))

(defn char
  "Consume the given character"
  [c]
  (token #(= c %)))

(defn any-char
  "Consume any character"
  []
  (token #(char? %)))

(defn digit
  "Consume a digit [0-9] character"
  []
  (token #(Character/isDigit %)))

(defn letter
  "Consume a letter [a-zA-Z] character"
  []
  (token #(Character/isLetter %)))

(defn between
  "Parse p after parsing open and before parsing close, returning the
   value of p and discarding the values of open and close"
  [open close p]
  (let->> [_ open
           x p
           _ close]
    (always x)))

(defn many1
  "Consume 1 or more p"
  [p]
  (let->> [x p
           xs (many p)]
    (always (cons x xs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; run parsers
(defn run-parser
  "Execute a parser p, given some state, Returns Ok or Err"
  [p state]
  (parsatron-poline p state
                    (fn cok [item _]
                      (Ok. item))
                    (fn cerr [err]
                      (Err. err))
                    (fn eok [item _]
                      (Ok. item))
                    (fn eerr [err]
                      (Err. err))))

(defn run
  "Run a parser p over some input. The input can be a string or a seq
   of tokens, if the parser produces an error, its message is wrapped
   in a RuntimeException and thrown, and if the parser succeeds, its
   value is returned"
  [postype p input]
  (let [result (run-parser p (InputState. input (postype 1 1)))]
    (condp instance? result
      Ok (:item result)
      Err (throw (RuntimeException. (show-error (:errors result)))))))
