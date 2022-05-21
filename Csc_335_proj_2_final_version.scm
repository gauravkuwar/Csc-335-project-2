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
; Notes: A valid proposition in the context of this project is either an atomic (atom) such as 'p
;        or a list such as '(p v q), '(- p), '(p ^ q) and '(p => q). 'p and 'q
;        are also propositions. A null list '(), is not a valid proposition.
;        (***Maybe you can explain it better idk***)

;        Terminology used in the project:
;             prop: variable is a proposition
;             DI: Design Idea, GI: Guess Invariant, IH: Inductive Hypothesis, IS: Inductive Step
 
;        Logical symbols:
;             AND = '^ 
;             OR = 'v 
;             NOT = '-
;             IMPLIES = '=> 

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
; PART 1 Description:

;; Design a data type suitable for representing infix propositions, as described in my notes for Class 19.

;; Give a complete specification and development (including a proof) for a program which inputs a proposition
;; which uses and (^), or (v), not (-) and implies (=>) and which returns a logically equivalent proposition
;; using just ^ and - .  Both the input and output should use infix notation.

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

; pre-cond : a valid proposition prop
; post-cond : returns a proposition using only AND and NOT for prop and its every sub-prop,
;             where OR prop and IMPLIES prop are transformed using transform-or and transform-implies repectively.
;             

; The main purpose of this function is to recursively apply the transform-or and
; the transform-implies function to prop, when it encounter a OR prop or IMPLIES prop
; accordingly.

; DI: If prop is an atom we just return the prop, if its a NOT prop
;     we recurse on the second-term of prop, otherwise we recurse on the first-term
;     and the third-term of prop. If the prop is a OR proposition, we transform it
;     with transform-or, if the prop is a IMPLIES proposition, we transform it
;     with transform-implies, otherwise (only option left is that is a AND prop)
;     we join the recursed first and third terms of prop using make-and.

; Basis Step: an atomic prop returns prop

; IH: We assume that (transform (second-term prop)) for a NOT prop, and
;     (transform (first-term prop)) and (transform (third-term prop)) for AND, OR, and IMPLIES prop
;     will output a proposition that meets the post conditions.
; 
; IS: Then (transform prop) will return (make-not (transform (second-term prop))) if (not-prop? prop)
;     and the pre-cond holds since we first checked if the prop is an atom and a NOT prop must
;     have a second-term which is a proposition.
;     Let p = (transform (first-term prop)) and q = (transform (third-term prop)) and
;     the pre-cond holds since everyother proposition must have a first-term which is a proposition and
;     a second-term which is a proposition, then
;     if (or-prop? prop) we get (transform-or p q), if (implies-prop? prop) we get (transform-implies p q)
;     and otherwise/AND prop we get (make-and p q).
;     So, we know that (transform prop) and all its possible sub-propositions meet the post conditions.
;     

; Termination Argument:
; Since, every recursive call we recurse on all possible sub-propositions within prop, so prop
; will eventually be an atomic prop (such as 'p or 'q) and the recursion will terminate.


; code

(define (transform prop)
  (cond ((atom? prop) prop)
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
; Our code does implement our Design Idea because we check if prop is an atom and return the prop.
; Then we check every possible proposition type NOT, OR, IMPLIES, and AND, and process the prop
; according to our design idea for each type of proposition.

; ________________________________________________________________________________________________
;
; double-negation
; ________________________________________________________________________________________________

; pre-cond : a valid proposition prop
; post-cond : returns a proposition where prop and all its sub-propositions do not
;             have double NOTs.
;             

; Double negation theorem: (- (- p)) = p

; The main purpose of this function is to recursively check if there are double NOTs in
; prop, and remove according to the double negation theorem. This function is actually,
; very similar to the transform function, so I did try to generalize them into one function,
; but later came to the conclusion that not generalizing them, would make the code much
; less complicated, and overall just easier to understand.

; DI: If prop is an atom we just return the prop, if it is a double NOT prop
;     which we check using double-not?, we recurse on the second-term of the second-term
;     of the prop, which pretty much cancels the double nots
;     If it is a single NOT prop, we recurse on the second-term of prop,
;     otherwise we recurse on the first-term and the third-term of prop, and join it using the second-term.

; Basis Step: an atomic prop returns prop

; IH: We assume that (double-negation (second-term (second-term prop))) for double NOTs prop,
;     (double-negation (second-term prop)) for a NOT prop, and
;     (double-negation (first-term prop)) and (double-negation (third-term prop)) for AND, OR, and IMPLIES prop
;     will output a proposition that meets the post conditions.
; 
; IS: Then (double-negation prop) will return (double-negation (second-term (second-term prop))) if (double-not? prop)
;     and the pre-condition holds since double-not? checks if the prop is a not prop and if the second-term of prop
;     is not an atom and if its also a not prop, so we know that (second-term (second-term prop)) is a proposition.
;     It will return (make-not (double-negation (second-term prop))) if (not-prop? prop)
;     and the pre-cond holds since we first checked if the prop is an atom and a NOT prop must
;     have a second-term which is a proposition.

;     And for everyother prop (AND, OR, and IMPLIES) (double-negation (first-term prop)) and (double-negation (third-term prop)),
;     will both be propositions, so the pre-cond holds since everyother proposition must have a first-term which is a proposition and
;     a second-term which is a proposition, then we join them using the (second-term prop) like
;     (list (double-negation (first-term prop)) (second-term prop) (double-negation (third-term prop)))
;     So, we know that (double-negation prop) and all its possible sub-propositions meet the post conditions.
;     

; Termination Argument:
; Since, every recursive call we recurse on all possible sub-propositions within prop, so prop
; will eventually be an atomic prop (such as 'p or 'q) and the recursion will terminate.


; code

(define (double-negation prop)
  (cond ((atom? prop) prop)
        ((double-not? prop) (double-negation (second-term (second-term prop)))) ; double NOTs
        ((not-prop? prop) (make-not (double-negation (second-term prop)))) ; single NOT
        (else (list (double-negation (first-term prop)) (second-term prop) (double-negation (third-term prop))))))


; tests:
"double-negation test"

(double-negation '(- p)) ; -> (- p)
(double-negation '(- (- p))) ; -> p
(double-negation '(- (- (- (- (- p)))))) ; -> (- p)

; audit:
; Our code does implement our Design Idea because we check if prop is an atom and return the prop.
; Then we check if the prop is a double NOT using double-not? function and then process it
; according to the design idea.
; Then we check every possible proposition type NOT, OR, IMPLIES, and AND, and process the prop
; according to our design idea for each type of proposition.

; ________________________________________________________________________________________________
;
; front-end
; ________________________________________________________________________________________________

; pre-cond - a valid proposition prop
; post-cond - returns a proposition with prop transformed using transform function, and with
;             double nots removed with double-negation function.

(define (front-end prop)
  (double-negation (transform prop)))

; tests:
"front-end tests"
(define p1 '((- p) => ((- q) v r)))
(define p2 '(r => (q v r)))
(define p3 '(p => q))

(front-end p1)
(front-end p2)
(front-end p3)

; ________________________________________________________________________________________________
;
; PART 2 Description:

;; Give a complete specification and development (including proof) for an interpreter of infix propositions:
;; your interpreter will input a proposition and an a-list of T,F values for variables, and will return the
;; computed value of the input proposition using those values for its variables.

; ________________________________________________________________________________________________
