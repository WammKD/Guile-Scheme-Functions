;;; -*- mode: scheme; coding: utf-8; -*-
;;;
;;; Copyright (C) 2010, 2011 Free Software Foundation, Inc.
;;;
;;; This library is free software; you can redistribute it and/or
;;; modify it under the terms of the GNU Lesser General Public
;;; License as published by the Free Software Foundation; either
;;; version 3 of the License, or (at your option) any later version.
;;;
;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Lesser General Public License for more details.
;;;
;;; You should have received a copy of the GNU Lesser General Public
;;; License along with this library; if not, write to the Free Software
;;; Foundation, Inc., 51 Franklin Str, Fifth Floor, Boston, MA 02110-1301 USA

(define-module (jaft functs)
  #:autoload (srfi srfi-1) (every fold-right member iota)
  ;; #:use-module (srfi srfi-43)
  ;; #:use-module (srfi srfi-60)
  #:autoload (ice-9 match) (match)
  #:autoload (ice-9 rdelim) (read-line)
  ;; #:use-module (compat racket for)
  #:export (!
	    %
            &
            |
	    ^
            ~
	    &&
	    ||
	    <<
	    >>
	    ++
	    --
            ==
            !=
	    /=
	    neq?
	    neqv?
	    nequal?
            true?
            false?
            int
            float
            add
            sub
            mul
            div
	    invert
	    ..
            ...
	    len
	    rev
            print
            readline
            read-lines
            print-lines
            contains
            replace
            endswith
	    ->string
	    first
	    head
	    rest
	    tail
	    init
	    cpr
	    ctr
	    nth
	    members-remove
	    members-keep
	    :
	    str
	    lst
	    vct
            vector-append
	    !!
            at
	    ;; zip
	    elem
            ;; index
	    haskell-foldl
	    replicate)
  #:replace (+
             -
             *
             /
             car
             cdr
             number?
             string?
             char?
             zero?
             first
             last
             filt))

(import (prefix (rnrs base) base:))
;; (import (prefix (rnrs lists) lists:))
(base:define +T base:+)
(base:define -T base:-)
(base:define *T base:*)
(base:define /T base:/)
(base:define carT base:car)
(base:define cdrT base:cdr)
(base:define number?T base:number?)
(base:define string?T base:string?)
(base:define char?T base:char?)
(base:define zero?T base:zero?)
;; (base:define filterT lists:filter)

(define ! not)

(define (fact n)
  (if (< n 0)
      (error "!: contract violation\n  expected: number greater than -1")
    (if (or (= n 0) (= n 1))
        1
      (let fact ([m (- n 2)] [l (*T n (-- n))])
        (if (or (= m 0) (= m 1))
            l
          (fact (-- m) (*T l m)))))))

(define (+ . xs)
  ;; (let ([f (if (negative? atom) ceiling floor)])
  (inexact->exact (apply +T (map (lambda (n) (if (negative? n)
                                                   (ceiling n)
                                                 (floor n))) xs))))

(define (- . xs)
  (inexact->exact (apply -T (map (lambda (n) (if (negative? n)
                                                   (ceiling n)
                                                 (floor n))) xs))))

(define (* . xs)
  (inexact->exact (apply *T (map (lambda (n) (if (negative? n)
                                                   (ceiling n)
                                                 (floor n))) xs))))

(define (/ . xs)
  (let ([m (exact->inexact (apply /T (map (lambda (n) (if (negative? n)
                                                          (ceiling n)
                                                        (floor n))) xs)))])
    (inexact->exact (if (negative? m)
                        (ceiling m)
                      (floor m)))))

(define % modulo)

(define & logand)

(define | logior)

(define ^ logxor)

(define ~ lognot)

(define-syntax &&
  (syntax-rules ()
    ((&&) #t)
    ((&& test) test)
    ((&& test1 test2 ...)
     (if test1 (&& test2 ...) #f))))

(define-syntax ||
  (syntax-rules ()
    ((||) #f)
    ((|| test) test)
    ((|| test1 test2 ...)
     (let ((x test1))
       (if x x (|| test2 ...))))))

;; (define (def|| f)
;;   (if (defined? (car f))
;;       #f
;;     (define f)))

(define (<< x y)
  (ash x y))

(define (>> x y)
  (ash x (invert y)))

(define ** expt)

(define ++ 1+)

(define -- 1-)

(define (number? . xs)
  (every number?T xs))

(define (string? . xs)
  (every string?T xs))

(define (char? . xs)
  (every char?T xs))

;; (define (== . xs)
;;   (apply (if (apply number? xs) = equal?) xs))

;; (define (== . xs)
;;   (let ([t (apply string? xs)])
;;     (apply (cond
;;             [t           string=?]
;;             [(apply number? xs) =]
;;             [else equal?]) (map (lambda (x) (cond
;;                                              [(string? x) (if t x (string->list x))]
;;                                              [(vector? x)         (vector->list x)]
;;                                              [else     x])) xs))))

(define (== . xs)
  (apply (cond
          [(apply string? xs) string=?]
          [(apply number? xs)        =]
          [(apply char?   xs)   char=?]
          [else                 equal?]) xs))

(define (!= . xs)
  (not (apply == xs)))

(define (/= . xs)
  (not (apply = xs)))

(define (=/= . xs)
  (if (apply number? xs)
      (apply /= xs)
    (apply nequal? xs)))

(define (neq? . xs)
  (not (apply eq? xs)))

(define (neqv? . xs)
  (not (apply eqv? xs)))

(define (nequal? . xs)
  (not (apply equal? xs)))

(define (true? . xs)
  (every (lambda (x) (neq? x #f)) xs))

;; (define (false? . xs)
;;   (for/and ([x (map (lambda (y) (eq? y #f)) xs)])
;;     x))
(define (false? . xs)
  (every (lambda (x) (eq? x #f)) xs))

(define (zero? . xs)
  (every zero?T xs))

;; (define (list-and . xs)
;;   (cond
;;    [(null? xs) #t]
;;    [(null? (cdr xs)) (car xs)]
;;    [else (and (car xs) (apply list-and (cdr xs)))]))

(define num string->number)

(define* (int atom #:optional [radix 10])
  (cond
   [(number? atom) (inexact->exact ((if (negative? atom)
                                        ceiling
                                      floor) (string->number
                                               (number->string
                                                 atom
                                                 radix))))]
   [(string? atom) (inexact->exact ((if (negative? (string->number atom radix))
                                        ceiling
                                      floor) (string->number atom radix)))]
   [else (error "int: contract violation\n  expected: number?, string?")]))

(define* (float atom #:optional [radix 10])
  (cond
   [(number? atom) (exact->inexact ((if (negative? atom)
                                        ceiling
                                      floor) (string->number
                                               (number->string
                                                 atom
                                                 radix))))]
   [(string? atom) (exact->inexact ((if (negative? (string->number atom radix))
                                        ceiling
                                      floor) (string->number atom radix)))]
   [else (error "float: contract violation\n  expected: number?, string?")]))

(define (add . xs)
  (exact->inexact (apply +T xs)))

(define (sub . xs)
  (exact->inexact (apply -T xs)))

(define (mul . xs)
  (exact->inexact (apply *T xs)))

(define (div . xs)
  (apply /T xs))

(define (invert n)
  (*T n -1))

(define* (.. x y #:optional [z 1])
  (cond
   [(&& (number?T x) (number?T y))
    (let ([nz (if (> x y) (invert z) z)])
    ;; (if (> x y)
    ;;     (reverse (iota (int (++ (/ (- x y) z))) y z))
      (iota (int (++ (abs (/T (-T y x) z)))) x nz))]
   [(&& (char? x) (char? y))
    (let ([cx (char->integer x)] [cy (char->integer y)])
      (map integer->char (map int (.. cx cy z))))]))

;; (define* (... x y #:optional [z 1])
;;   (cond
;;    [(&& (number?T x) (number?T y))
;;     (let ([nz (if (> x y) (invert z) z)])
;;       (iota (int (abs (/T (-T y x) z))) x nz))]
;;    [(&& (char? x) (char? y))
;;     (let ([cx (char->integer x)] [cy (char->integer y)])
;;       (map integer->char (map int (.. cx cy z))))]))

(define* (... x y #:optional [z 1])
  (let* ([xt (if (char? x) (char->integer x) x)]
         [yt (if (char? y) (char->integer y) y)]
         [f  (if (> xt yt) ++ --)]
         [ff (if (char? y) (integer->char y) (lambda (z) z))]
         [sf (if (char? y) (char->integer y) (lambda (z) z))])
    (.. x (ff (f (sf y))) z)))

;; Python functions
(define (len a)
  (cond
   [(list?       a)                         (length a)]
   [(pair?       a)                                  2]
   [(string?     a)                  (string-length a)]
   [(vector?     a)                  (vector-length a)]
   ;; [(hash-table? a)          (hash-count (const #t) a)]
   [(number?     a) (string-length (number->string a))]
   [else (error "len: contract violation\n  expected: list?, pair?, string?, vector?, hash-table?, number?")]))

(define (rev a)
  (cond
   [(list?   a)              (reverse a)]
   [(pair?   a) (cons (cdrT a) (carT a))]
   [(string? a)       (string-reverse a)]
   [(vector? a)   (list->vector
                    (reverse
                      (vector->list a)))]
   [(number? a) (string->number
                  (rev
                    (number->string a)))]
   [else (error "rev: contract violation\n  expected: list?, pair?, string?, vector?")]))

(define* (print s #:optional [port (current-output-port)])
  (display s port)
  (newline port))

(define (readline)
  (read-line (current-input-port)))

(define* (read-lines #:optional [arg '()])
  (let ([p (cond
            [(null?   arg)  (current-input-port)]
            [(port?   arg)                   arg]
            [(string? arg) (open-input-file arg)]
            [else (error 'read-lines "bad argument")])])
    (let loop ([line (read-line p)]
               [lines (list)])
      (if (eof-object? line)
          (begin
            (when (string? arg)
              (close-input-port p))
            (reverse lines))
        (loop (read-line p) (cons line lines))))))

(define* (print-lines l #:optional [arg '()])
  (let ([p (cond
            [(null?   arg)  (current-output-port)]
            [(port?   arg)                    arg]
            [(string? arg) (open-output-file arg)]
            [else (error 'display-lines "bad argument")])])
    (let loop ([line (carT l)]
               [lines (cdrT l)])
      (if (null? lines)
          (begin
            (display line p)
            (when (string? arg)
              (close-output-port p)))
        (begin
          (print line p)
          (loop (carT lines) (cdrT lines)))))))

;; (define (contains sub orig)
;;   (cond
;;    [(list? orig)
;;     (let ([sub2 (cond
;;                  [(list?   sub)                sub]
;;                  [(string? sub) (string->list sub)]
;;                  [(vector? sub) (vector->list sub)])])
;;       (let temp ([c orig])
;;         (cond
;;          [(null? sub2) #f]
;;          [(null?    c) #f]
;;          [(not (== (carT c) (carT sub2))) (temp (cdrT c))]
;;          [else (let temp2 ([d (cdrT c)] [s (cdrT sub2)])
;;                  (cond
;;                   [(null? s)                (-T (len orig) (len c))]
;;                   [(null? d)                                     #f]
;;                   [(== (carT d) (carT s)) (temp2 (cdrT d) (cdrT s))]
;;                   [else (temp (cdrT d))]))])))]
;;    [(string? orig) (contains sub (string->list orig))]
;;    [(vector? orig) (contains sub (vector->list orig))]))

(define (contains sub orig)
  (cond
   [(!= (count (lambda (x)
		 (and (x sub) (x orig))) (list string? list? vector?)) 1)
           (error "contains: contract violation\n  expected matching: string?, list?, vector?")]
   [(list? orig)
           (let ([sub2 (cond
			[(list?   sub)                sub]
			[(vector? sub) (vector->list sub)])])
	     (let temp ([c orig])
	       (cond
		[(null? sub2)                                 #f]
		[(null?    c)                                 #f]
		[(not (== (carT c) (carT sub2))) (temp (cdrT c))]
		[else (let temp2 ([d (cdrT c)] [s (cdrT sub2)])
			(cond
			 [(null? s)                (-T (len orig) (len c))]
			 [(null? d)                                     #f]
			 [(== (carT d) (carT s)) (temp2 (cdrT d) (cdrT s))]
			 [else (temp (cdrT d))]))])))]
   [(string? orig)         (string-contains orig sub)]
   [(vector? orig) (contains sub (vector->list orig))]))

(define* (replace old new orig #:optional [n -1])
  (let ([funct (cond
                [(string? orig) str]
                [(list?   orig) lst]
                [(vector? orig) vct])]
        [fin   (cond
                [(string? orig)
                   (cond
                    [(string? new)                               new]
                    [(list?   new)                (list->string new)]
                    [(vector? new) (list->string (vector->list new))])]
                [(list?   orig)
                   (cond
                    [(string? new) (string->list new)]
                    [(list?   new)                new]
                    [(vector? new) (vector->list new)])]
                [(vector? orig)
                   (cond
                    [(string? new) (list->vector (string->list new))]
                    [(list?   new)                (list->vector new)]
                    [(vector? new)                               new])])])
    (if (contains old orig)
        (let ([temp (funct
                      (: orig 0 (contains old orig))
                      fin
                      (: orig (+T (contains old orig) (len old))))])
          (cond
           [(== n -1) (if (contains old temp)
                          (replace old new temp)
                        temp)]
           [(>  n  1) (if (contains old temp)
                          (replace old new temp (-- n))
                        temp)]
           [(== n  1) temp]))
      #f)))

(define (endswith end orig)
  (== (: orig (invert (len end))) end))

(define (->string x)
  (cond
   [(number?       x)                            (number->string x)]
   [(char?         x) (string-append "#\\" (list->string (list x)))]
   [(boolean?      x)                 (match x [#t "#t"] [#f "#f"])]
   [(symbol?       x)       (string-append "'"  (symbol->string x))]
   [(string?       x)                                             x]
   [(||
      (list?       x)
      (vector?     x)
      (hash-table? x))
    (let ([s (cond
              [(list?       x)      "'("]
              [(vector?     x)      "#("]
              [(hash-table? x) "'#hash("])]
          [f (cond
              [(list?       x)                       (lambda (x) x)]
              [(vector?     x)                         vector->list]
              [(hash-table? x) (lambda (x) (hash-map->list list x))])])
      (str
        s
        (:
          (fold-right
            (lambda (x y)
              (str
                " "
                (cond
                 [(number?   x)       (->string x)]
                 [(char?     x)       (->string x)]
                 [(boolean?  x)       (->string x)]
                 [(symbol?   x)       (->string x)]
                 [(pair?     x) (: (->string x) 1)]
                 [(string?   x)  (str "\"" x "\"")]
                 [(list?     x) (: (->string x) 1)]
                 [(vector?   x)       (->string x)])
                y))
            ")"
            (f x))
          1)))]
   [(pair?         x) (str
                        "'("
                        (->string (carT x))
                        " . "
                        (->string (cdrT x))
                        ")")]))

;; List functions
(define (first a)
  (cond
   [(pair? a) (carT a)]
   [else      (!! a 0)]))

(define head first)

(define car first)

(define (rest a)
  (cond
   [(pair? a) (cdrT a)]
   [else (: a 1)]))

(define tail rest)

(define cdr rest)

(define (init a)
  (cond
   [(list? a) (rev (cdrT (rev a)))]
   [(pair? a) (carT a)]
   [else (: a 0 -1)]))

(define cpr init)

;; (define (cpr l)
;;   (cond
;;    [(list? l) (rev (cdrT (rev l)))]
;;    [else (carT l)]))

(define (last a)
  (cond
   [(pair? a) (carT (rev a))]
   [else           (!! a -1)]))

(define ctr last)

;; (define (ctr l)
;;   (carT (rev l)))

(define (nth n a)
  (!! a n))

(define (members-remove x y)
  (let ([f1 (cond
             [(list?   y)   (lambda (x) x)]
             [(string? y)     list->string]
             [(vector? y)     list->vector])]
        [f2 (cond
             [(list?   y)   (lambda (x) x)]
             [(string? y)     string->list]
             [(vector? y)     vector->list])]
        [x2 (cond
             [(list?   x)                x]
             [(string? x) (string->list x)]
             [(vector? x) (vector->list x)])])
    (f1 (filter (lambda (z) (not (member z x2))) (f2 y)))))

(define (members-keep x y)
  (let ([f1 (cond
             [(list?   y)   (lambda (x) x)]
             [(string? y)     list->string]
             [(vector? y)     list->vector])]
        [f2 (cond
             [(list?   y)   (lambda (x) x)]
             [(string? y)     string->list]
             [(vector? y)     vector->list])]
        [x2 (cond
             [(list?   x)                x]
             [(string? x) (string->list x)]
             [(vector? x) (vector->list x)])])
    (f1 (filter (lambda (z) (member z x2)) (f2 y)))))

;; Haskell functions
;; (define* (: received-atom startIndex #:optional [endIndex (len received-atom)])
;;   (let ([sI (if (negative? startIndex)
;;                 (+T (len received-atom) startIndex)
;;               startIndex)]
;;         [eI (if (negative? endIndex)
;;                 (if (> (+T (len received-atom) endIndex) (len received-atom))
;;                     (len received-atom)
;;                   (+T (len received-atom) endIndex))
;;               (if (> endIndex (len received-atom))
;;                   (len received-atom)
;;                 endIndex))])
;;     (cond
;;      [(list?   received-atom) (let newList ([a received-atom]
;;                                             [n sI]
;;                                             [m eI]
;;                                             [l (-T eI sI)]
;;                                             [k 0])
;;                                 (cond
;;                                  [(equal? a '[]) '[]]
;;                                  [(< k n)        (newList
;;                                                    (cdrT a)
;;                                                    n
;;                                                    m
;;                                                    l
;;                                                    (++ k))]
;;                                  [(= (len a) l)  a]
;;                                  [else (newList
;;                                          (cpr a)
;;                                          n
;;                                          m
;;                                          l
;;                                          k)]))]
;;      [(string? received-atom) (if (> sI eI)
;;                                   ""
;;                                 (substring received-atom sI (if (> eI (len received-atom))
;;                                                                 (len received-atom)
;;                                                               eI)))]
;;      [(vector? received-atom) (list->vector
;;                                 (:
;;                                   (vector->list received-atom)
;;                                   startIndex
;;                                   endIndex))])))

(define* (: received-atom startIndex #:optional [endIndex (len received-atom)])
  (let* ([lra (len received-atom)]
         [sI (if (negative? startIndex)
                 (if (negative? (+T lra startIndex))
                     0
                   (+T lra startIndex))
               startIndex)]
         [eI (if (negative? endIndex)
                 (if (> (+T lra endIndex) lra)
                     lra
                   (+T lra endIndex))
                 (if (> endIndex lra)
                     lra
                   endIndex))])
    (cond
     [(list?   received-atom) (if (> sI eI)
                                  '()
                                (let* ([listhead    (list-head received-atom eI)]
                                       [lenlisthead               (len listhead)])
                                  (list-tail listhead (if (> sI lenlisthead)
                                                          lenlisthead
                                                        sI))))]
     [(string? received-atom) (if (> sI eI)
                                  ""
                                (substring received-atom sI (if (> eI lra)
                                                                lra
                                                              eI)))]
     [(vector? received-atom) (list->vector
                                (:
                                  (vector->list received-atom)
                                  startIndex
                                  endIndex))])))

(define* (str #:key [sep ""] . xs)
  (let ([xs1 (if (== (!! xs 0) #:sep)
                 (: xs 2)
               xs)])
    (string-join
      (map
        (lambda (x)
          (if (char? x)
              (list->string (list x))
            (if (symbol? x)
                (symbol->string x)
              (->string x))))
        xs1)
      sep)))

(define (lst . xs)
  (apply
    append
    (map (lambda (x)
           (if (list? x)
               x
             (list x))) xs)))

(define (vector-append . xs)
  (list->vector (apply append (map vector->list xs))))

(define (vct . xs)
  (apply
    vector-append
    (map
      (lambda (x)
         (if (vector? x)
             x
           (vector x)))
      xs)))

(define (!! received-atom index)
  (let ([func-type (cond
                    [(string? received-atom) string-ref]
                    [(list?   received-atom)   list-ref]
                    [(vector? received-atom) vector-ref]
                    [else #f])]
        [findex    (if (negative? index)
                       (+T (len received-atom) index)
                     index)])
    (if (not func-type)
        (error "!!: contract violation\n  expected: string?, list?, vector?")
      (func-type received-atom findex))))

(define at !!)

;; (define (zip x y)
;;   (cond
;;    [(= (len x) (len y))               (map list x y)]
;;    [(> (len x) (len y)) (map list (: x 0 (len y)) y)]
;;    [else (map list x (: y 0 (len x)))]))

(define* (elem x y #:optional [z equal?])
  (cond
   [(list?   y)                               (member x y z)]
   [(string? y) (list->string (member x (string->list y) z))]
   [(vector? y) (list->vector (member x (vector->list y) z))]))

;; (define (index memb l)
;;   (- (len l) (len (elem memb l))))

(define (filt pred iter)
  (cond
   [(list?   iter)                               (filter pred iter)]
   ;; [(string? iter) (list->string (filterT pred (string->list iter)))]
   [(string? iter)                         (string-filter pred iter)]
   [(vector? iter) (list->vector (filter pred (vector->list iter)))]))

(define (haskell-foldl f x y)
  (if (null? (cdrT y))
      (f x (carT y))
    (f (haskell-foldl f x (cpr y)) (ctr y))))

(define (replicate n x)
  (if (zero?T n)
      '()
    (cons x (replicate (-- n) x))))
