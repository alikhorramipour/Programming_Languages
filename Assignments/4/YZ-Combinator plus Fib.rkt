#lang racket
(define Y (lambda (b) ((lambda (f) (b (lambda (x) ((f f) x))))
                 	 (lambda (f) (b (lambda (x) ((f f) x)))))))

(define (Z f) 
  ((lambda (x) (x x)) 
   (lambda (x) (f (lambda (y) ((x x) y))))))

(define Fib-Y
  (Y (lambda (fib) (lambda (n) (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2))))))))

(define Fib-Z
  (Y (lambda (fib) (lambda (n) (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2))))))))

(Fib-Y 16)
(Fib-Z 16)
