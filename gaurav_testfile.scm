;; Part 1

;; Design a data type suitable for representing infix propositions, as described in my notes for Class 19.

;; Give a complete specification and development (including a proof) for a program which inputs a proposition
;; which uses and (^), or (v), not (-) and implies (=>) and which returns a logically equivalent proposition
;; using just ^ and - .  Both the input and output should use infix notation.
;;
; we know with logical equivalence that:
; Demorgan's law: A or B = (not ((not A) and (not B)))
; implicite rule: A => B = ((not A) or B) = (not (A and (not B))

; we can change implicit rule using demorgans rule so we can turn any prop of and, or, not, implies into a prop of just and, not.


; example:
;          input: ('x 'v 'y), ouput: (-(-x ^ -y))


; need to create constructors, selectors and classifiers
;
; Contructors:
; we want to be able to create a prop given some operands.

; what about p ^ q ^ r ^ ...

(define (make-and op1 op2)
  (list op1 '^ op2))

; recusive make-and

(define (make-and-rec lst-ops)
  (cond ((null? (cdr lst-ops)) lst-ops)
        (else (append (list (car lst-ops) '^) (make-and-rec (cdr lst-ops))))))
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

; professor said we make need to create a make-true, make-false


; Selectors:
; we want to be able to select each term of the prop
(define (first-term prop)
  (car prop))

(define (second-term prop)
  (cadr prop))

(define (third-term prop) ; double check if there is an issure with the not prop for this(since it has 2 terms).
  (caddr prop))

; Classifiers
; we want to be able to classify if a prop is and, or, not, implies
;
(define (and-prop? prop)
  (eq? (second-term prop) '^))

(define (or-prop? prop)
  (eq? (second-term prop) 'v))

(define (not-prop? prop)
  (eq? (first-term prop) '-))

(define (implies-prop? prop)
  (eq? (second-term prop) '=>))

; DRAFT:
; how to implement demorgans law? we check if it is an or proposition with or-prop?, if it is then we can apply demorgans
; to transform it. possible approach:
(define (transform-or prop)
  (make-not (make-and (make-not (first-term prop)) (make-not (third-term prop))))
  )
;
;(define (transform-or prop-lst)
;  (make-not (make-and 

; test
;input: (transform-or (list '4 'v '5))
;output: (- ((- 4) ^ (- 5)))

; how to implement implicit rule? we check if it is an implies proposition with implies-prop? if it is then we
; apply implicite rule to transform it. we first will change it to an or prop, then call transform-or. possible approach:
(define (transform-implies prop)
  (transform-or (make-or (make-not (first-term prop)) (third-term prop)))
  )

; test
; input: (transform-implies (list '1 '=> '2))
; output: (- ((- (- 1)) ^ (- 2)))

; test 2, without transform-or (just check if implicit rule transforms correctly)
;
; (define (transform-implies-test prop)
;  (make-or (make-not (first-term prop)) (third-term prop)))
;
; input: (transform-implies-test (list '1 '=> '2))
; output: ((- 1) v 2)

; may be we can just check the term?
(define (or? term)
  (eq? term 'v))

; splits the prop by v (kinda like split in python)

(define (split-by-or prop)
  (define (helper prop result block)
    (cond ((null? prop) result)
          (else (let ((t (car prop)))
                  (cond ((list? t) (helper (cdr prop)))
                        ((or? t) (helper (cdr prop) (append result '()) block))
                        (block (helper (cdr prop) (append result (list (list t))) block)))))))
  (helper prop '() #t))
              

;(define (split-by-or prop)
;  (define (helper prop result)
;        (cond ((null? prop) result)
;        (else (let ((t (car prop))) ; t=term / current element
;                (cond ((list? t) ))
;                      ((or? t) (split-by-or (cdr prop))) ; just skip or
;                      ; not a or term
;                      (else (cons t (split-by-or (cdr prop)))))))))
; tests:
;(split-by-or '((p ^ (q v t)) v r))
(split-by-or '())
(split-by-or '(p))
(split-by-or '((p ^ q) ^ s v r))


(define (make-prop prop)
  (let ((t1 (car prop)))
  (cond ((list? t1) (make-prop t1)) ; for nested props inside (...)
        ((not-prop? prop) (cond ((= (cadr prop) '-) 1); double neglation/cancel   ; assume that if we see - operand there must be a term after it
                                (else 1)))))); else next term must be a prop



;; Part 2

;; Give a complete specification and development (including proof) for an interpreter of infix propositions:
;; your interpreter will input a proposition and an a-list of T,F values for variables, and will return the
;; computed value of the input proposition using those values for its variables.


;; Part 3

;; Demonstrate your interpreter by using it in conjunction with the front-end of Part 1.