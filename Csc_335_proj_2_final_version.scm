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
; 
; Lookup
;________________________________________________________________________________________________
;
; We want to be able to look up a T/F value given to a variable in an a-list.
;
; precondition: an a-list that is a list of lists that contain variables and the T/F values they are paired to
;               and a variable that is in the a-list.
;
; postcondition: The value that is associated to the variable given as input.

; The main purpose of this function is to look at every list in the a-list recursively and see if the first element in that list is
; equal to the variable we are looking for. If it is then we will return the second element in the list which is the T/F value
; associated with the variable.
;
; DI: We will be recursing on the size of the list. Since we know that the variable needs to be in the a-list (since  we checked before)
;     we can check the first pair of variables/ values and recursive

; Basis step: When the variable is equal to the first item in the list we stop recursing and return the cadr of the car of the list
;             which is the second element in the list. This is the T/F value that we need for the postcondition.

; IH: var is unchanged from the next call so we can still assume that it is still a variable in the a-list. When we make the recursive
;     call we are taking the cdr of a-list. Since we know that a-list contains var we will never reach the null case so there is no
;     need to test for that. taking the cdr of a list will have a-list continue to be a list and since we have the condition to stop
;     recursing if var is found in the a-list we know that on the next call a-list remains a list that contains var in it.

; IS: When we have our recursive call returned we will logical or this result with #f. Since #f logical or'ed with a second truth value
;     will give the identity of the second value we know that it is computing whatever the value that is associated with var that was
;     returned.

; Termination arguement: we also know that this function will end because we know that var is in the a-list and since we are decrementing the a-list by 1
; element each call we will eventually reach the list element that contains var.

; code
(define (lookup var a-list)
  (cond ((eq? var (caar a-list)) (cadr (car a-list)))
        (else (or #f (lookup var (cdr a-list))))
        ))

; test:
"Lookup Test"
 (define t1 (list (list 'x #t) (list 'y #t) (list 'z #f)))
 (lookup 'z t1) ;returned #f
 (lookup 'x t1) ; returned #t

;audit:
; Our code does implement our design idea because we check is the var is in the first list element of a-list
; (caar a-list, since the first value will be the variable). If it is then we
; we return the second value of the list element which is the T/F value associated with the variable(cadr (car a-list since the
; second element of the list element is always the value). This is our desired result.
; Otherwise we will or #f with the recrusive call of the cdr of a-list.

;________________________________________________________________________________________________
;
; variable?
;________________________________________________________________________________________________

; precondition: a value x
; postcondition: return #t if the value is not a list, '^, '- and #f otherwise.
; DI: if the value isn't a list, '^ or '- then it must be a variable for the proposition.

(define(variable? prop)
  (and (not (list? prop)) (not(equal? prop '^)) (not (equal? prop '-))) ;may need to also check null?
  )
;
; Test
"varaible? test"
(variable? '^)
(variable? '-)
(variable? (list 1 2 3))
(variable? 'x)
;_____________________________________________________________________________________________________
;
; And/Not proposition evaluation.
;_______________________________________________________________________________________________________
;
; this will simply evaluate a not proposition
; precondition: a #t or #f value prop.
; postcondition: output will be the logical not of prop. 
(define (eval-not prop)
  (not prop))


; this will simply evaluate an and proposition
; precondition: a #t or #f value prop2 and a #t or #f value prop2.
; postcondition: output will be the logical and of prop1 and prop 1
(define (eval-and prop1 prop2)
  (and prop1 prop2))
;
; These uses primitives so there shouldn't be a need for proof 
;_______________________________________________________________________________________________________
;
; Interpreter
;________________________________________________________________________________________________________
;
; precondition: a valid proposition prop(of only and, not), an a-list that contains the truth value assiciated with each varaible
;               in prop.
; postcondition: returns the computed value of the input proposition using those values for its variables.
;
; The main purpose of this function is to lookup the associated value of each variable in the proposition and to recursively
; evaluate the proposition. since the proposition is of finite size we can recurse on the size of the proposition.

; DI: If prop is null then we can just return since there is nothing to evaluate. If prop is just a single variable then we can
;     look up the associated truth value for that variable using lookup. if it doesn't get caught by the 2 previous conditions then it
;     is a not, and proposition. We check if it is an or proposition and evaluate it, after recursively interpreting any proposition
;     inside the not proposition. If it is an and proposition then we evaluate that after interpreting any proposition inside the and
;     proposition.
;
; Basis step: If the prop is null then we shouldn't return any value, there is no truth value to evaluate. If the prop is a varaible
;             then we want to return the truth value for that varaible which is evaluating the proposition and satisfies the postocndition.

; IH: We assume that both a-list and prop are valid inputs. a-list is unchanged so on the next recursive call a-list remains a
;     a valid a-list that contains values for all variables in the proposition. After the recursive call prop in going to be either
;     the first term or third term in an and proposition, which is still a proposition. or it is going to be the second term in a not
;     proposition which is also still going to be a proposition. Since all 3 of these are in the original proposition then prop
;     will remain a valid proposition that only contains not, and while also still being a variable in the a-list. The precondition
;     is held.
;
; IS: We need to know that we are correctly evaluating what the recursive call returns. since the returned value will be a truth value,
;     either T/F based on the lookup function. We take that returned value and apply the eval-not function to it if it is a not
;     proposition and the eval-and function if it is an and proposition. These functions with evaluate an or and an and proposition
;     respectively so we know that we are evaluating the returned result correctly.
;
; Termination Argument: Since the proposition in finite and every recursive call is done on a term inside the original proposition we
;                       we will reach a single varible and the recursion will terminate.
(define (interpreter prop a-list)
  (cond ((null? prop) ) ; check atom prop or empty list prop
        ((variable? prop) (lookup prop a-list))
        ((not-prop? prop) (eval-not (interpreter (second-term prop) a-list))) ; for single not
        (else (let ((p (interpreter (first-term prop) a-list))
                    (q (interpreter (third-term prop) a-list)))
                (eval-and p q)))))
;
; Tests:
 "Interpreter Test"
 (define alist1 (list (list 'p #t) (list 'q #f)))
 (define ex1 '(- ((- p) ^ (- q))))
 (interpreter ex1 alist1)
; Result : #t
;
(define alist1 (list (list 'p #f) (list 'q #f)))
(interpreter ex1 alist1)
; Result: #f

; audit:
; Our code correctly implements our design idea because we check if the prop is null and simply return. We then check if prop is a
; variable then lookup the associated truth value for that variable. If those two conditions fail then we check if it is a not
; proposition; if it is then we evaluate not on the recrusive result of the proposition inside the not proposition. Similarly then we
; know it has to be an and proposition and we evaluate the and proposition on the recursive result of the 2 propositions inside the
; and proposition.

; ________________________________________________________________________________________________
;
; PART 3 Description:

;; Demonstrate your interpreter by using it in conjunction with the front-end of Part 1.

; ________________________________________________________________________________________________
