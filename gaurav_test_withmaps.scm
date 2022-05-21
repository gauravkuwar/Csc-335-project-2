(define (atom? x)
  (and (not (null? x)) (not (pair? x))))

; Contructors:
; we want to be able to create a prop given some operands.


(define (make-and op1 op2)
  (list op1 '^ op2))

;; recusive make-and
;
;(define (make-and-rec lst-ops)
;  (cond ((null? (cdr lst-ops)) lst-ops)
;        (else (append (list (car lst-ops) '^) (make-and-rec (cdr lst-ops))))))
;
;(make-and-rec '(p q r s t))
;(define x (make-and-rec '(p (t ^ u) r s)))
;x

(define (make-or op1 op2)
  (list op1 'v op2))

(define (make-not op1)
  (list '- op1))

(define (make-implies op1 op2)
  (list op1 '=> op2))


; ----- OLD ABOVE -----

(define (first-term prop)
  (car prop))
(define (second-term prop)
  (cadr prop))
(define (third-term prop) ; double check if there is an issure with the not prop for this(since it has 2 terms).
  (caddr prop))

; can make it easier to write propositions.
; Puts negation into parentheses
; with this function negation will always have 2 terms the (- symbol and the operand) and be in a separate list
; but it doesnt work for double negation of the form (- - p), i assume this is not valid prop

; sep-not as a func for rec-map
(define (sep-not-f P)
  (cond ((= (length P) 5) (list (make-not (list-ref P 1)) (list-ref P 2) (make-not (list-ref P 4))))
        ((= (length P) 4)
         (cond ((equal? (car P) '-) (cons (make-not (list-ref P 1)) (cddr P)))  
               ((equal? (list-ref P 2) '-) (list (list-ref P 0) (list-ref P 1) (make-not (list-ref P 3))))))
        (else P)))

; these can be generalized
(define (or-prop? prop)
  (and (pair? prop) (>= (length prop) 2) (eq? (second-term prop) 'v)))
(define (implies-prop? prop)
  (and (pair? prop) (>= (length prop) 2) (eq? (second-term prop) '=>)))
(define (not-prop? prop)
  (and (pair? prop) (>= (length prop) 2) (eq? (first-term prop) '-)))


(define (transform-or-func prop)
  (cond ((or-prop? prop) (make-not (make-and (make-not (first-term prop)) (make-not (third-term prop)))))
        (else prop)))
(define (transform-implies-func prop)
  (cond ((implies-prop? prop) (make-not (make-and (first-term prop) (make-not (third-term prop)))))
        (else prop)))

(define (remove-double-negs-f prop)
  (define (double-not? prop)
    (and (not-prop? prop) (not-prop? (second-term prop))))
  (define (double-neg prop)
    (second-term (second-term prop)))
  
  (cond ((double-not? prop) (double-neg prop))
        (else prop)))

; ________________________________________________________________________________________________
;
; rec-map
; ________________________________________________________________________________________________

; pre-cond : a function f, and a list of lists lst
; post-cond : returns a list with f called on every lst and every sublist in lst.

; Explain why we need this func and what it does

; DI: 

; Basis Step:
; IH:
; IS:

; Termination Argument

;(define (lst-of-atoms? lst)
;  (cond ((null? lst) #t)
;        (else (and (not (pair? (car lst))) (lst-of-atoms? (cdr lst))))))
;
;(lst-of-atoms? '(1 2 3 4))
;(lst-of-atoms? '(1 2 3 (4 5 6)))
;
;(define (rec-map-2 f lst)
;  (cond ((null? lst) lst)
;        ((atom? lst) lst)
;        ((lst-of-atoms? (car lst)) (f lst))
;        (else (f (cons (rec-map-2 f (car lst)) (rec-map-2 f (cdr lst)))))))

; tests:
;"rec-map-2 tests"
;(rec-map-2 (lambda (x) (list 'a x)) '(1 2 (3 4 5)))

; this maps f to every list ; just 1 recusive function for transform and removing double nots so 1 proof 
(define (rec-map f lst)
  (cond ((null? lst) lst)
        ((atom? lst) lst)
        (else (f (cons (rec-map f (car lst)) (rec-map f (cdr lst)))))))

; tests:
"rec-map tests"
(define (test-f x)
  ((list '- x))

(rec-map test-f '((- 1) (- 2) (- 3) (- 4) (- 5)))
; (a (1 2 (a (3 4 5))
; audit:


; ________________________________________________________________________________________________

(define (transform prop)
  (rec-map remove-double-negs-f (rec-map transform-implies-func (rec-map transform-or-func (rec-map sep-not-f prop)))))

"transform with rec-map tests"

(define p1 '(- p => (- q v r)))
(define p2 '(r => (q v r)))
(define p3 '(p => q))


(transform p1)
(transform p2)
(transform p3)


;"double-negation test"
;(rec-map remove-double-negs-f '(- p)) ; -> (- p)
;(rec-map remove-double-negs-f '(- (- p))) ; -> p
;(rec-map remove-double-negs-f '(- (- (- (- (- p)))))) ; -> (- p)