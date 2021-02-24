;; PL Project - Fall 2020
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool  (b)    #:transparent)  ;; a boolean
(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct minus  (e1 e2)  #:transparent)  ;; subtract one expression from the other
(struct mult  (e1 e2)  #:transparent)  ;; multiply two expressions
(struct div  (e1 e2)  #:transparent)  ;; divide one expression by the other
(struct neg  (e1)  #:transparent)  ;; negate an expression
(struct andalso  (e1 e2)  #:transparent)  ;; logical conjuntion of two expressions
(struct orelse  (e1 e2)  #:transparent)  ;; logical disjuntion of two expressions
(struct cnd  (e1 e2 e3)  #:transparent)  ;; conditional
(struct iseq  (e1 e2)  #:transparent)  ;; whether two expressions are equal or not
(struct ifnzero  (e1 e2 e3)  #:transparent)  ;; check zero conditional
(struct ifleq  (e1 e2 e3 e4)  #:transparent)  ;; less or equal conditional
(struct with  (s e1 e2)  #:transparent)  ;; let expression; value of e1 is bound to s in e2
(struct apair  (e1 e2)  #:transparent)  ;; pair constructor
(struct 1st  (e1)  #:transparent)  ;; first part of a pair
(struct 2nd  (e1)  #:transparent)  ;; second part of a pair
(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application


(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e1)     #:transparent) ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 


(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k mr) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r
;; (struct fib (n) #:transparent) ;; n-th number in fibonacci sequence

(struct letrec (s1 e1 s2 e2 s3 e3 s4 e4 e5) #:transparent) ;; a letrec expression for recursive definitions
;; NUMEX value: number constant, boolean constant, closure, munit, pair of values, numex list(ends in munit)
;; SYNTAX CHECKING needs to be added


#|
(define (fib n)
  (if (< n 2)
      1
      (+ (fib (- n 1)) (fib (- n 2)))))|#



;; Warm-up

;; Problem 1
;; input: list, null, undefined
#|
(define (racketlist->numexlist xs)
  ;; since NUMEX doesn't have lists, we use 'apair'
  (cond[(null? xs) (munit)]
    [(list? xs) (apair (car xs) (racketlist->numexlist (cdr xs)))]
    [#t (error("[warm-up (a)]invalid input"))]
  )
)

(define (numexlist->racketlist xs)
  ;; since NUMEX doesn't have lists, we use 'apair'
  (cond[(munit? xs) (null)]
    [(apair? xs) (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
    [#t (error("[warm-up (b)]invalid input"))]
  )
)|#
(define (racketlist->numexlist racketList)
  (cond [(null? racketList) (munit)]
        [(list? racketList) (apair (car racketList) (racketlist->numexlist (cdr racketList)))]
        [#t (error ("it's not a racket list"))]
  )
)

(define (numexlist->racketlist numexList)
  (cond [(munit? numexList) null]
        [(apair? numexList) (cons (apair-e1 numexList) (numexlist->racketlist (apair-e2 numexList)))]
        [#t (error ("it's not a numex list"))]
  )
)


;; Implementing NUMEX
;; Problem 2

;; lookup a variable in an environment
;; Complete this function
;; environment represented as racket list of racket pairs (initially empty)
#|
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? (list? env) #f) (error("[envlookup]environment is not a racket list"))]
  	[(equal? (string? str) #f) (error("[envlookup]variable is not a string"))]
        [equal? str (car(car env)) (cdr(car env))] ;eval
        [else (envlookup (cdr env) str)] ;recursion
   )
)|#

(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? str (caar env)) (cdar env)]
        [#t (envlookup (cdr env) str)]
	)
 )

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond #|[(var? e) 
         (cond[(string? (var-string e))(envlookup env (var-string e))]
              [else (error "NUMEX var applied to non-racket-string")])]|#
       [(var? e)
       (envlookup env (var-string e))]
        
        [(num? e)
         (cond[(integer? (num-int e)) e]
              [else (error "NUMEX num applied to non-racket-integer")])]
        
        [(bool? e)
         (cond[(boolean? (bool-b e)) e]
              [else (error "NUMEX bool applied to non-racket-boolean")])]

        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]
        
        [(minus? e)
          (let ([v1 (eval-under-env (minus-e1 e) env)]
                [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(mult? e)
          (let ([v1 (eval-under-env (mult-e1 e) env)]
                [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(div? e)
          (let ([v1 (eval-under-env (div-e1 e) env)]
                [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               ;; using quotient to return int value (based on the test cases)
               (num (quotient (num-int v1) 
                       (num-int v2)))
               (error "NUMEX division applied to non-number")))]

        
        [(andalso? e)
          (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (cond[(bool? v1)(cond[(equal? (bool-b v1) #f) v1]
                                [else (let ([v2 (eval-under-env (andalso-e2 e) env)])
                                      (cond[(bool? v2) v2]
                                           [else (error "NUMEX logical conjunction applied to non-number")]))])]
                [else (let ([v2 (eval-under-env (andalso-e2 e) env)])
                      (cond[(bool? v2) v2]
                           [else (error "NUMEX logical conjunction applied to non-number")]))]))]


          [(apply? e)
          (let ([v (eval-under-env (apply-actual e) env)]
                [funexp (eval-under-env (apply-funexp e) env)])
            (if (closure? funexp)
              (let ([fun (closure-f funexp)])
                (if (null? (lam-nameopt fun))
                  (eval-under-env (lam-body fun) (cons (cons (lam-formal fun) v) (closure-env funexp)))
                  (eval-under-env (lam-body fun) (cons (cons (lam-nameopt fun) funexp) (cons (cons (lam-formal fun) v) (closure-env funexp))))))
              (if (lam? funexp)
                (eval-under-env (apply funexp (apply-actual e)) env)
                (error "NUMEX apply invalidly used"))))]
        
      
        [(orelse? e)
          (let ([v1 (eval-under-env (orelse-e1 e) env)])
           (cond[(bool? v1)(cond[(equal? (bool-b v1) #t) v1]
                                [else (let ([v2 (eval-under-env (orelse-e2 e) env)])
                                      (cond[(bool? v2) v2]
                                           [else (error "NUMEX logical disjunction applied to non-number")]))])]
                [else (let ([v2 (eval-under-env (orelse-e2 e) env)])
                      (cond[(bool? v2) v2]
                           [else (error "NUMEX logical disjunction applied to non-number")]))]))]

        [(neg? e)
          (let ([v1 (eval-under-env (neg-e1 e) env)])
            (cond[(bool? v1)
              (cond[(equal? (bool-b v1) #t) (bool #f)][(equal? (bool-b v1) #f) (bool #t)])]
            [(num? v1) (num (- 0 (num-int v1)))]
            [else(error "NUMEX negation applied to non-bool or non-number")]))]


        [(cnd? e)
          (let ([v1 (eval-under-env (cnd-e1 e) env)])
            (cond [(bool? v1)
              (cond[(equal? (bool-b v1) #t)(let ([v2 (eval-under-env (cnd-e2 e) env)]) v2)]
                   [(equal? (bool-b v1) #f)(let ([v3 (eval-under-env (cnd-e3 e) env)]) v3)])]
              [else (error "NUMEX conditional applied to non-bool")]))]


        [(iseq? e)
          (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (cond[(and (or (bool? v1) (num? v1))(or (bool? v2) (num? v2)))(cond[(and (bool? v1) (bool? v2))(cond[(equal? (bool-b v1) (bool-b v2))(bool #t)]
                                                                                                               [else (bool #f)])]
                                                                              [(and (num? v1) (num? v2))(cond[(equal? (num-int v1) (num-int v2))(bool #t)]
                                                                                                             [else (bool #f)])]
                                                                              [else (bool #f)])]
                [else (error "NUMEX iseq applied to non-boolean or non-number")]))]


        [(ifnzero? e)
          (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
            (if (num? v1)
               (cond[(not (equal? (num-int v1) 0))(let ([v2 (eval-under-env (ifnzero-e2 e) env)]) v2)]
                    [(equal? (num-int v1) 0)(let ([v3 (eval-under-env (ifnzero-e3 e) env)]) v3)])
               (error "NUMEX ifnzero applied to non-number")))]
        

        #|[(ifleq? e)
          (let ([v1 (eval-under-env (ifleq-e1 e) env)]
                [v2 (eval-under-env (ifleq-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (cond[(> (num-int v1) (num-int v2))(let ([v4 (eval-under-env (ifleq-e4 e) env)]) v4)]
                    [(not (> (num-int v1) (num-int v2)))(let ([v3 (eval-under-env (ifleq-e3 e) env)]) v3)])
           (error "NUMEX ifleq applied to non-number")))]|#

         [(ifleq? e)
          (let ([v1 (eval-under-env (ifleq-e1 e) env)]
                [v2 (eval-under-env (ifleq-e2 e) env)])
            (if (and (num? v1)
                     (num? v2))
              (if (> (num-int v1) 
                      (num-int v2))
                (eval-under-env (ifleq-e4 e) env)
                (eval-under-env (ifleq-e3 e) env))
              (error "NUMEX ifleq applied to non-number")))]


        [(with? e)
          (let ([v1 (eval-under-env (with-e1 e) env)])
           (cond[(string? (with-s e)) (eval-under-env (with-e2 e) (cons (cons (with-s e) v1) env))]
                [(null?   (with-s e)) (eval-under-env (with-e2 e) (cons v1 env))]
                [else (error "NUMEX with applied to non-string")]))]
        


        [(lam? e)
          (closure env e)]

        
        #|[(apply? e)
          (let ([fun-closure (eval-under-env (apply-funexp e) env)])
            (cond[(closure? fun-closure) (let ([fun-def (closure-f fun-closure)])
                                       (let ([eval-actual (eval-under-env (apply-actual e) env)])
                                             (cond[(lam? fun-def)(eval-under-env (lam-body fun-def) (cons (cons (lam-formal fun-def) eval-actual)
                                                                                          (cons (cons (lam-nameopt fun-def) fun-closure) (closure-env fun-closure))))]
                                                  [else (error "closure function isn't lam")])))]

                 [(lam? fun-closure) (let* ([lam-closure (eval-under-env fun-closure env)]
                                           [lam-def (closure-f lam-closure)])
                                       (let ([eval-actual (eval-under-env (apply-actual e) env)])
                                             (cond[(lam? lam-def)(eval-under-env (lam-body lam-def) (cons (cons (lam-formal lam-def) eval-actual)
                                                                                          (cons (cons (lam-nameopt lam-def) lam-closure) (closure-env lam-closure))))]
                                                  [else (error "closure function isn't lam")])))]
                 [else (error "NUMEX lam invalidly applied")]))]|#


        [(apair? e)
          (let ([v1 (eval-under-env (apair-e1 e) env)]
                [v2 (eval-under-env (apair-e2 e) env)])
          (apair v1 v2))]


        [(1st? e)
          (let ([v1 (eval-under-env (1st-e1 e) env)])
            (cond[(apair? v1)(apair-e1 v1)][else(error "NUMEX 1st applied to non-apair")]))]


        [(2nd? e)
          (let ([v1 (eval-under-env (2nd-e1 e) env)])
            (cond[(apair? v1)(apair-e2 v1)][else(error "NUMEX 2nd applied to non-apair")]))]

        [(munit? e) (munit)]

        [(ismunit? e)
         (let ([v1 (eval-under-env (ismunit-e1 e) env)])
           (cond[(munit? v1)(bool #t)]
                [else (bool #f)]))]


        [(closure? e) e]


        [(letrec? e)
          (eval-under-env (letrec-e5 e)
           (cons (cons (letrec-s1 e) (letrec-e1 e))
            (cons (cons (letrec-s2 e) (letrec-e2 e))
              (cons (cons (letrec-s3 e) (letrec-e3 e))
                (cons (cons (letrec-s4 e) (letrec-e4 e)) env)))))]


        [(key? e)
          (let ([ek (eval-under-env (key-e e) env)])
               (cond[(string? (key-s e)) e]
                    [else (error "NUMEX key applied to non-string")]))]

        [(record? e)
          (let ([k (eval-under-env (record-k e) env)]
               [mr (eval-under-env (record-mr e) env)])
               (cond[(key? k) (cond[(or (munit? (eval-exp mr)) (record? mr)) (record k mr)]
                                   [else (error "invalid value of record")])]
                [else (error "invalid key")]))]

        [(value? e)
          (let ([rec (eval-under-env (value-r e) env)])
               (cond[(and (string? (value-s e)) (record? rec))
                 (define (find-key goal-str rec)
                 (let ([key-str (key-s (record-k rec))] ;string of record
                       [key-val (key-e (record-k rec))] ;value of record
                       [next-rec (record-mr rec)]) ;next record
                       (cond[(equal? goal-str key-str) key-val]
                            [(munit? (eval-exp next-rec)) (munit)]
                            [else (find-key goal-str next-rec)])))(find-key (value-s e) rec)]
                    [else (error "NUMEX value applied to non-string")]))]

        ;; CHANGE add more cases here
        [#t (error (format "bad NUMEX expression: ~v" e))]))





;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3


(define (ifmunit e1 e2 e3) (cnd (ismunit e1) e2 e3))

(define (with* bs e2) (let ([pair (car bs)]
                            [next-pair (cdr bs)]
                            [pair-s (car (car bs))]
                            [pair-e (cdr (car bs))])
                            (cond[(null? next-pair) (with pair-s pair-e e2)]
                                 [else (with pair-s pair-e (with* next-pair e2))])))

(define (ifneq e1 e2 e3 e4) (cnd (iseq e1 e2) e4 e3))



;; Problem 4

(define numex-filter (lam "f" "g" (lam "h" "list" (cnd (ismunit (var "list"))
                                                          (munit)
                                                          (with "val" (apply (var "g") (1st (var "list"))) (ifnzero (var "val")
                                                                                                              (apair (var "val") (apply (var "h") (2nd (var "list"))))
                                                                                                              (apply (var "h") (2nd (var "list")))))))))



(define numex-all-gt
  (with "filter" numex-filter
        (lam null "i" (lam null "list" (apply (apply (var "filter") (lam null "element" (ifleq (var "element") (var "i")
                                                                                               (num 0)
                                                                                               (var "element"))))   (var "list")))))) ;




;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e) "CHANGE")

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env) "CHANGE")

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))




#|
(define fib
  (lam "f1" "n"
       [(ifleq (var "n") (num 2) (num 1)
                 [plus (apply ((var "f1") (minus ((var "n") (num 1))))) (apply ((var "f1") (minus ((var "n") (num 2)))))])]))|#


(define fib
 ( lam "f1" "n"
       (ifleq (var "n") (num 2) (num 1) (plus (apply (var "f1") (minus (var "n") (num 1))) (apply (var "f1") (minus (var "n") (num 2)))))))
