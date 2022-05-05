;; Part 1

;; Design a data type suitable for representing infix propositions, as described in my notes for Class 19.

;; Give a complete specification and development (including a proof) for a program which inputs a proposition
;; which uses and (^), or (v), not (-) and implies (=>) and which returns a logically equivalent proposition
;; using just ^ and - .  Both the input and output should use infix notation.
;;
; we know with logical equivalence that:
; Demorgan's law: A or B = (not ((not A) and (not B)))
; implicite rule: A => B = ((not A) or B)

; we can change implicit rule using demorgans rule so we can turn any prop of and, or, not, implies into a prop of just and and not.


; example:
;          input: ('x 'v 'y), ouput: (-(-x ^ -y))


; need to create constructors, selectors and classifiers
;
; Contructors:
; we want to be able to create a prop given some operands.

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



;; Part 2

;; Give a complete specification and development (including proof) for an interpreter of infix propositions:
;; your interpreter will input a proposition and an a-list of T,F values for variables, and will return the
;; computed value of the input proposition using those values for its variables.


;; Part 3

;; Demonstrate your interpreter by using it in conjunction with the front-end of Part 1.