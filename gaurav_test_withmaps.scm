;; Project 2
;; CSC 335
;; Spring 2022
;
; Authors: Gaurav Kuwar (gkuwar000@citymail.cuny.edu)
;          Kevin Peter (kpeter000@citymail.cuny.edu)
; ________________________________________________________________________________________________
;
; Introduction
;
; ** EVERY THING we were able to complete
;

; ________________________________________________________________________________________________
;
; Note: ****Some notes about terminology or something else***
; we could also define what a proposition is in the context of this project

; prop variable is a proposition
; Logical symbols:
; AND = '^ 
; OR = 'v 
; NOT = '-
; IMPLIES = '=> 

; ________________________________________________________________________________________________
;
; Construtors - we want to be able to create a prop given some operands.
; ________________________________________________________________________________________________

(define (make-and op1 op2)
  (list op1 '^ op2))
(define (make-or op1 op2)
  (list op1 'v op2))
(define (make-not op1)
  (list '- op1))
(define (make-implies op1 op2)
  (list op1 '=> op2))

; ________________________________________________________________________________________________
;
; Selector: (is that what they are called?)
; ________________________________________________________________________________________________

(define (first-term prop)
  (car prop))
(define (second-term prop)
  (cadr prop))
(define (third-term prop) ; double check if there is an issure with the not prop for this(since it has 2 terms). (NO ISSUES!)
  (caddr prop))

; ________________________________________________________________________________________________
;
; atom?
; ________________________________________________________________________________________________

; pre-cond : a value x
; post-cond : checks if x is an atom, so it checks if its not a null value, and that its
;             not a pair (since a list is a pair, this also checks if x is not a list)

(define (atom? x)
  (and (not (null? x)) (not (pair? x))))

; tests:
"atom? tests"
(atom? 1)
(atom? 'p)
(atom? '(1 . 2))
(atom? '())
(atom? '(p v q))

; ________________________________________________________________________________________________
;
; not-prop?
; ________________________________________________________________________________________________

; pre-cond : a value x
; post-cond : checks if x is an atom, so it checks if its not a null value, and that its
;             not a pair (since a list is a pair, this also checks if x is not a list)

(define (not-prop? prop)
  (eq? (first-term prop) '-))

; tests

; ________________________________________________________________________________________________
;
; or-prop?
; ________________________________________________________________________________________________

(define (or-prop? prop)
  (eq? (second-term prop) 'v))

; ________________________________________________________________________________________________
;
; and-prop?
; ________________________________________________________________________________________________

(define (and-prop? prop)
  (eq? (second-term prop) '^))

; ________________________________________________________________________________________________
;
; implies-prop?
; ________________________________________________________________________________________________

(define (implies-prop? prop)
  (eq? (second-term prop) '=>))

; ________________________________________________________________________________________________
;
; valid-prop?
; ________________________________________________________________________________________________

; our definition of a valid proposition is one that is list not an atom
;(define (valid-prop? P)
;  (and (not (atom? P)) (or (and (= (length P) 3) (or (or-prop? P) (and-prop? P) (implies-prop? P)))
;                           (and (= (length P) 2) (not-prop? P)))))

; ________________________________________________________________________________________________
;
; double-not?
; ________________________________________________________________________________________________

(define (double-not? prop)
    (and (not-prop? prop)
         (not (atom? (second-term prop)))
         (not-prop? (second-term prop))))

; ________________________________________________________________________________________________
;
; transform-or
; ________________________________________________________________________________________________

; pre-cond : p and q are both propositions, which were previously of the form (p v q)
; post-cond : returns (- ((- p) ^ (- q))) proposition

; Demorgan's law: (p v q) = (- ((- p) ^ (- q)))
; this is used to represet OR proposition using only NOT and AND propositions
; (Note: ofcourse this is not recursive)

(define (transform-or p q)
  (make-not (make-and (make-not p) (make-not q))))

; tests:
"transform-or tests"
; lets say we got 'p 'q from '(p v q)
(transform-or 'p 'q)
; lets say we got '(p v r) 'q from '((p v r) v q)
(transform-or '(p v r) 'q)


; ________________________________________________________________________________________________
;
; transform-implies
; ________________________________________________________________________________________________

; pre-cond : p and q are both propositions, which were previously of the form (p => q)
; post-cond : returns (- (p ^ (- q)) proposition

; Implicite rule: (p => q) = ((- p) v q)
; then using Demorgan's law: ((- p) v q) = (- (p ^ (- q))
; So, (p => q) = (- (p ^ (- q))

; this is used to represet IMPLIES proposition using only NOT and AND propositions
; (Note: ofcourse this is not recursive)

(define (transform-implies p q)
  (make-not (make-and p (make-not q))))

; tests:
"transform-implies tests"
; lets say we got 'p 'q from '(p => q)
(transform-implies 'p 'q)
; lets say we got '(p => r) 'q from '((p => r) => q)
(transform-implies '(p => r) 'q)

; ________________________________________________________________________________________________
;
; transform
; ________________________________________________________________________________________________

; pre-cond : a function f, and a list of lists lst
; post-cond : returns a list with f called on every lst and every sublist in lst.

; Explain why we need this func and what it does

; DI: 

; Basis Step:
; IH:
; IS:

; Termination Argument


; code

(define (transform prop)
  (cond ((or (null? prop) (atom? prop)) prop)
        ((double-not? prop) (transform (second-term prop)))
        ((not-prop? prop) (make-not (transform (second-term prop))))
        (else (let ((p (transform (first-term prop))) (q (transform (third-term prop))))
                (cond ((or-prop? prop) (transform-or p q))
                      ((implies-prop? prop) (transform-implies p q))
                      (else (make-and p q)))))))


; tests:
"transform tests"

(define p1 '((- p) => ((- q) v r)))
(define p2 '(r => (q v r)))
(define p3 '(p => q))

(transform p1)
(transform p2)
(transform p3)


; audit:


; ________________________________________________________________________________________________
;
; double-negation
; ________________________________________________________________________________________________

; pre-cond : a function f, and a list of lists lst
; post-cond : returns a list with f called on every lst and every sublist in lst.

; Explain why we need this func and what it does

; DI: 

; Basis Step:
; IH:
; IS:

; Termination Argument


(define (double-negation prop)
  (cond ((or (null? prop) (atom? prop)) prop)
        ((double-not? prop) (double-negation (second-term (second-term prop))))
        ((not-prop? prop) (make-not (double-negation (second-term prop))))
        (else (list (double-negation (first-term prop)) (second-term prop) (double-negation (third-term prop))))))


; tests:
"double-negation test"

(double-negation '(- p)) ; -> (- p)
(double-negation '(- (- p))) ; -> p
(double-negation '(- (- (- (- (- p)))))) ; -> (- p)

; audit:


; ________________________________________________________________________________________________
;
; frontend
; ________________________________________________________________________________________________

(define (frontend prop)
  (double-negation (transform prop)))