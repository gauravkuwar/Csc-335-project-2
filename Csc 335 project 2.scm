;; Part 1

;; Design a data type suitable for representing infix propositions, as described in my notes for Class 19.

;; Give a complete specification and development (including a proof) for a program which inputs a proposition
;; which uses and (^), or (v), not (-) and implies (=>) and which returns a logically equivalent proposition
;; using just ^ and - .  Both the input and output should use infix notation.
;;
; we know with logical equivalence that:
; Demorgan's law: A or B = (not ((not A) and (not B)))
; implicite rule: A => B = ((not A) or B)

; we can change implicit rule using demorgans rule so we can turn any prop of and, or, not, implies into a prop of just and, not.


; example:
;          input: ('x 'v 'y), ouput: (-(-x ^ -y))


; need to create constructors, selectors and classifiers
;
; Contructors:
; we want to be able to create a prop given some operands.
(define (make-and op1 op2)
  (list op1 '^ op2))

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

; so now we can transform a single proposition of or, implies to just and, not. now we need to be able to transform nested
; propositions as needed, that are mixed with propositions we dont need to transform.
;
;; Part 2

;; Give a complete specification and development (including proof) for an interpreter of infix propositions:
;; your interpreter will input a proposition and an a-list of T,F values for variables, and will return the
;; computed value of the input proposition using those values for its variables.

; looking up values from the a-list recursively

(define (lookup val a-list)
  (cond ((eq? val (caar a-list)) (cadr (car a-list)))
        (else (or #f (lookup val (cdr a-list))))
        ))
;test
(define t1 (list (list 'x #t) (list 'y #t) (list 'z #f)))
;(lookup 'z t1) ; f
;
;
(define(operand? prop)
  (and (not (list? prop)) (not(equal? prop '^)) (not (equal? prop '-)))
  )

(define (compute prop a-list)
  (cond ((null? prop) ) ; check atom prop or empty list prop
        ((operand? prop) (lookup prop a-list))
        ((not-prop? prop) (eval-not (compute (second-term prop) a-list))) ; for single not
        (else (let ((p (compute (first-term prop) a-list))
                    (q (compute (third-term prop) a-list)))
                (eval-and p q)))))

(define (eval-not prop)
  (not prop)
  )

(define (eval-and prop1 prop2)
  (and prop1 prop2)
  )
  
;; Part 3

;; Demonstrate your interpreter by using it in conjunction with the front-end of Part 1.

;; computed value of the input proposition using those values for its variables.

; safe input
; error checking;

; check for valid list / valid propsition
; check if assosiation list works with the prop

; we should call prop -> P


; grading:
; overall quality of package


(define (interpreter P lst)
  (backend (frontend P) lst))

; or (we could call it frontend)

(define (frontend P lst)
  ;; Error checking:
  ; test prop - check maybe len of prop 2=not-prop, check first value is not operator; 3=else, check middle value is a valid operator
  ; test lst - check variables occur in prop
  
  ; then we compute
  (backend (transform-func P) lst))
