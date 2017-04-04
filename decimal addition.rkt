#lang racket

(require "make-Turing-machine.rkt")

(define (make-TM base)
 (define rules
  (append
   (for*/list ((n (in-range 0 base)) (m (in-range 0 base)))
    (list (list 0 (list n m))
     (let ((sum (+ n m)))
      (if (>= sum base) (list 1 (- sum base) 'R)
                        (list 0 sum 'R)))))
   (for*/list ((n (in-range 0 base)) (m (in-range 0 base)))
    (list (list 1 (list n m))
     (let ((sum (+ n m 1)))
      (if (>= sum base) (list 1 (- sum base) 'R)
                        (list 0 sum 'R)))))
   (list
    '((0 Blank) (T b R))
    '((1 Blank) (T 1 R)))))
 (printf "~nbase ~s, nr-of-rules ~s~n" base (length rules))
 (define (nr->lst n)
  (define (nr->lst n)
   (cond
    ((zero? n) '())
    (else
     (define-values (q r) (quotient/remainder n base))
     (cons r (nr->lst q)))))
  (if (zero? n) '(0) (nr->lst n)))
 (define (prepare-input n m)
  (let ((n (nr->lst n)) (m (nr->lst m)))
    (define ln (length n))
    (define lm (length m))
    (define len (max ln lm))
    (map list (append n (make-list (- len ln) 0))
              (append m (make-list (- len lm) 0)))))
 (define (output->nr lst)
  (if (null? lst) 0
   (+ (car lst) (* base (output->nr (cdr lst))))))
 (values (make-Turing-machine 0 '(T) 'Blank 'b '_ rules)
         nr->lst
         prepare-input
         output->nr))

(define (test base)
 (let-values (((TM nr->lst prepare-input output->nr) (make-TM base)))
  (and   
   (let ((n 987) (m 99765))
    (let-values (((state output) (let ((input (prepare-input n m))) (time (TM input)))))
     (define sum (output->nr output))
     (and (= sum (+ n m)) (eq? state 'T))))
   (for/and ((k (in-range 0 1000)))
    (define n (random 1000000000))
    (define m (random 1000000000))
    (define input (prepare-input n m))
    (define-values (state result) (TM input))
    (and
     (= (output->nr result) (+ n m))
     (eq? state 'T))))))

(for/and ((base (in-range 2 251))) (test base))

; end
