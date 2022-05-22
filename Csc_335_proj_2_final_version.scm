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
; We were able to complete all parts of the project, part 1 - the front-end (with double negation),
; part 2 - backend, part 3 - combining the backend and front-end in a function called eval-prop.
; For part 3, we also first check if the variables in the prop are in the association list.
;

; ________________________________________________________________________________________________

; Notes:

; Define Datatype:
; A valid proposition in the context of this project is either atomic (atom) such as 'p
; or a list such as '(p v q), '(- p), '(p ^ q) and '(p => q). 'p and 'q
; are also propositions. A proposition build with the constructors is a valid proposition.
; A null list '(), is not a valid proposition.
 
; Logical symbols:
;     AND = '^ 
;     OR = 'v 
;     NOT = '-
;     IMPLIES = '=>

; Terminology used in the project:
;     prop: variable is a proposition
;     DI: Design Idea, GI: Guess Invariant, IH: Inductive Hypothesis, IS: Inductive Step

; ________________________________________________________________________________________________
;
; Helper function: atom?
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
; Construtors - make-and, make-or, make-not, make-implies (Tools for making propositions)
; ________________________________________________________________________________________________

; we want to be able to create a prop given some operands.

"Construtors tests"

; ________________________________________________________________________________________________

; make-and

; pre-cond : a proposition p and a proposition q
; post-cond : returns AND representation of p and q: '(p ^ q)

(define (make-and p q)
  (list p '^ q))

; test:
(make-and 'p 'q)

; ________________________________________________________________________________________________

; make-or

; pre-cond : a proposition p and a proposition q
; post-cond : returns OR representation of p and q: '(p v q)

(define (make-or p q)
  (list p 'v q))

; test:
(make-or 'p 'q)

; ________________________________________________________________________________________________

; make-not

; pre-cond : a proposition p
; post-cond : returns NOT representation of p: '(- p)

(define (make-not p)
  (list '- p))

; test:
(make-not 'p)

; ________________________________________________________________________________________________

; make-implies

; pre-cond : a proposition p and a proposition q
; post-cond : returns IMPLIES representation of p and q: '(p => q)

(define (make-implies p q)
  (list p '=> q))

; test:
(make-implies 'p 'q)

; ________________________________________________________________________________________________
;
; Selectors - first-term, second-term, third-term
; ________________________________________________________________________________________________

; we want to be able to select each term of the prop

"Selector tests"

; ________________________________________________________________________________________________

; first-term

; pre-cond : takes a non-atomic prop, which is an IMPLIES, AND, NOT, and OR prop.
; post-cond : returns the first-term of the prop.

(define (first-term prop)
  (car prop))

; tests:
(first-term '(p v q))

; ________________________________________________________________________________________________

; second-term

; pre-cond : takes a non-atomic prop, which is an IMPLIES, AND, NOT, and OR prop.
; post-cond : returns the second-term of the prop.

(define (second-term prop)
  (cadr prop))

; tests:
(second-term '(- (p => q)))
(second-term '(p ^ q))

; ________________________________________________________________________________________________

; third-term

; pre-cond : takes a non-atomic prop, which is an IMPLIES, AND, and OR prop.
; post-cond : returns the third-term of the prop.

(define (third-term prop)
  (caddr prop))

; test:
(third-term '(p => (p v q))) 

; ________________________________________________________________________________________________
;
; Classifiers - not-prop?, or-prop?, and-prop?, implies-prop?
; ________________________________________________________________________________________________

; we want to be able to classify if a prop is and, or, not, implies

"Classifiers tests"

; ________________________________________________________________________________________________

; not-prop?

; pre-cond : any non-atomic valid proposition prop.
; post-cond : returns true if the prop is a NOT prop else false

(define (not-prop? prop)
  (eq? (first-term prop) '-))

; tests:
(not-prop? '(- p))
(not-prop? '(p v q))

; ________________________________________________________________________________________________

; or-prop?

; pre-cond : any non-atomic valid proposition prop.
; post-cond : returns true if the prop is a OR prop else false

(define (or-prop? prop)
  (eq? (second-term prop) 'v))

; tests:
(or-prop? '(p v (p ^ q)))
(or-prop? '(- p))

; ________________________________________________________________________________________________

; and-prop?

; pre-cond : any non-atomic valid proposition prop.
; post-cond : returns true if the prop is a AND prop else false

(define (and-prop? prop)
  (eq? (second-term prop) '^))

; tests:
(and-prop? '(p ^ (-q)))
(and-prop? '(p v q))

; ________________________________________________________________________________________________

; implies-prop?

; pre-cond : any non-atomic valid proposition prop.
; post-cond : returns true if the prop is a IMPLIES prop else false

(define (implies-prop? prop)
  (eq? (second-term prop) '=>))

; tests:
(implies-prop? '(p => (-q)))
(implies-prop? '(p ^ q))

; ________________________________________________________________________________________________
;
; double-not?
; ________________________________________________________________________________________________

; This is a special classifier that checks if a prop is double NOT

; pre-cond : any non-atomic valid proposition prop.
; post-cond : returns true if the prop is a NOT proposition, and the second-term of
;             of prop is a non-atomic valid proposition prop that is also a NOT proposition.

(define (double-not? prop)
    (and (not-prop? prop)
         (not (atom? (second-term prop)))
         (not-prop? (second-term prop))))

; tests:
"double-not? tests"
(double-not? '(- ( - p))) ; -> #t
(double-not? '( - p)) ; -> #f
(double-not? '(p v (- ( - p)))) ; -> #f, because double-not? is not recursive

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
; PART 1 Description:

;; Design a data type suitable for representing infix propositions, as described in my notes for Class 19.

;; Give a complete specification and development (including a proof) for a program which inputs a proposition
;; which uses and (^), or (v), not (-) and implies (=>) and which returns a logically equivalent proposition
;; using just ^ and - .  Both the input and output should use infix notation.

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
; propositions build with lists, easier to write/read
(define p1 '((- p) => ((- q) v r)))
(define p2 '(((- (p v q)) => (p => q)) ^ q))

; we can use a proposition build by constructors as well
(define p3 (make-implies 'r (make-or 'q 'r)))
(define p4 (make-implies 'p 'q))

(front-end p1)
(front-end p2)
(front-end p3)
(front-end p4)

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

; audit:
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
  (and (not (list? prop)) (not (equal? prop '^)) (not (equal? prop '-))) ;may need to also check null?
  )
;
; Test
"variable? test"
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
; Interpreter / backend
;________________________________________________________________________________________________________
;
; precondition: a valid proposition prop(of only and, not), an a-list that contains the truth value associated with each variable
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
; Basis step: If the prop is null then we shouldn't return any value, there is no truth value to evaluate. If the prop is a variable
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
;
; Helper function: element-of?
; ________________________________________________________________________________________________

; pre-cond: a val and a list of atoms lst
; post-cond: returns of val is an element of lst or not

; LST is lst initially
; GI: val is an element of LST iff val is an element of lst

; DI: Iterates through every element of lst, until lst is null, or element is eq
;     to val, while maintaining the GI.

; weak-enough?
; Since, LST=lst initially, then value will be in LST only if its in lst, so our GI holds

; preserved?
; lst will terminate if (car lst) is val, so for all elements in LST and not in lst we know for sure
; are not eq to val. So, our GI holds since val is an element of LST iff val is an element of lst.

; strong-enough?
; At the end of the iteration, will either be a null list of a lst where val is (car lst)
; So if lst is null, then val is not an element of LST, and if it is not null val is in LST,
; since val is (car lst) so our GI holds.

; Termination argument:
; At every iteration the length of lst is decreased by 1 with (cdr lst), so
; eventually, lst will be a null list (if val is not found in lst beforehand) so
; the program will always terminate.

; code:

(define (element-of? val lst)
  (cond ((null? lst) #f)
        ((eq? val (car lst)) #t)
        (else (element-of? val (cdr lst)))))

; tests:
"element-of? tests"
(element-of? 2 '(1 3 4 2 5))
(element-of? 2 '(1 3 4 5))

; audit:
; Our code implements our DI, since we iterate through every element of lst
; with (car lst) and (cdr lst), we terminate if lst is null, or (car lst) is val,
; so our GI is maintained.

; ________________________________________________________________________________________________
;
; Helper function: remove-dublicates
; ________________________________________________________________________________________________

; pre-cond : a list of atoms lst
; post-cond : returns a list with all elements of lst, but no dublicates

; Note: the order of the initial lst is not maintained, but we can reverse the output
;       to maintain the order, but the order is not relevant to our use case, so
;       I decided not to implement it here.

; LST is lst initially
; GI: new-lst is all unique elements in LST for elements in LST but not in lst

; DI: maintain a list new-lst, which is a null list initially, and iterate through lst,
;     while maintaining the GI.

; weak-enough?
; Initially, LST=lst so there would be no elements in LST but not in lst, and so new-lst
; is a null list and the GI holds.

; preserved?
; At every iteration, an element of lst is only added to new-list if the element is
; not already an element of new-lst, so new-lst will always have unique elements in LST
; for elements in LST but not in lst, which is our GI, so our GI holds

; strong-enough?
; At the end of the iteration, lst will be a null list, so new-lst will be all unique
; elements in LST which is our post condition and our GI holds.

; Termination Argument:
; At every iteration the length of lst is decreased by 1 with (cdr lst),
; so eventually lst will be a null list and the program will terminate.


; code:
(define (remove-dublicates lst)
  (define (iter lst new-lst)
    (cond ((null? lst) new-lst)
          (else (iter (cdr lst) (cond ((element-of? (car lst) new-lst) new-lst)
                                      (else (cons (car lst) new-lst)))))))
  (iter lst '()))

; tests:
"remove-dublicates tests"
(remove-dublicates '(a b c d a))
(remove-dublicates '(1 2 3 1 3 5))

; audit:
; Our code implements the DI, because new-lst is initially, and we iterate through
; lst with (car lst) and (cdr lst), and only add (car lst) to new-lst if
; it not already in new-lst, so our GI is maintained.

; ________________________________________________________________________________________________
;
; Helper function: elems-in?
; ________________________________________________________________________________________________

; pre-cond : two list of atoms lst1 and lst2
; post-cond : checks if all elements in lst1 are in lst2

; Note: this doesn't check if the all elemenets in lst2 are in lst1
;       so lst2 can have extra elements that are not in lst1.

; DI: For every element for lst1 check if it is in element of lst2 with the
;     element-of? function, until lst1 is a null list, then return #t.


; Basis Step: (elems-in? ()' lst2) = #t since there are no elements in lst1
;             all elements in lst1 are in lst2 by default.

; IH: assume (elems-in? (cdr lst1) lst2)) returns #t if all elements in (cdr lst1)
;     are in lst2 and #f otherwise.

; IS: for (elems-in? lst1 lst2) we check is lst1 is a null list, so (cdr lst1)
;     will not produce an error and the preconditions are met for (elems-in? (cdr lst1) lst2).
;     Then we do (element-of? (car lst1) lst2) to check if (car lst) is in lst2, if it is
;     we will get #t,and #f otherwise. Then we perform and on (element-of? (car lst1) lst2)
;     (elems-in? (cdr lst1) lst2)), so if either are false the output will be #f. So,
;     our post-conditions are met.

; Termination Argument:
; Since we do (cdr lst1) for every recursive call, and so decrease the length of lst1
; by 1 for every recursive call, lst1 will eventually be a null list which is our basis
; step and our program will terminate.

; checks if every element of lst1 is in lst2
(define (elems-in? lst1 lst2)
  (cond ((null? lst1) #t)
        (else (and (element-of? (car lst1) lst2) (elems-in? (cdr lst1) lst2)))))

; tests:
"elems-in? tests"
(elems-in? '(1 2 3) '(1 2 3 4)) ; #t
(elems-in? '(1 2 3) '(1 2 4)) ; removed 3 so should be #f

; audit:
; Our code implements the design idea because for every element of lst1 we check if
; the element is in lst2 with element-of? function, when stop when lst1 is a null list
; and return #t.

; ________________________________________________________________________________________________
;
; vars-in-prop
; ________________________________________________________________________________________________

; pre-cond : a valid proposition prop
; post-cond : returns a list of all the variables/(valid atomic propositions) in prop but with no
;             repeated values / dublicates.

; vars-in-prop-with-dubs proof:

; pre-cond : a valid proposition prop
; post-cond : returns a list of all the variables/(valid atomic propositions) in prop             

; DI: If prop is an atom we just return the (list prop), 
;     If it is a NOT prop, we recurse on the second-term of prop,
;     otherwise we recurse on the first-term and the third-term of prop, and then append both.

; Basis Step: an atomic prop returns (list prop)

; IH: We assume that (vars-in-prop-with-dubs (second-term prop)) for NOT prop, and
;     (vars-in-prop-with-dubs (first-term prop)) and (vars-in-prop-with-dubs (third-term prop)) for AND, OR, and IMPLIES prop
;     will output a list of all the variables within the propositions within prop.
; 
; IS: Then (vars-in-prop-with-dubs prop) will return (vars-in-prop-with-dubs (second-term prop)) if (not-prop? prop)
;     and (append (vars-in-prop-with-dubs (first-term prop)) (vars-in-prop-with-dubs (third-term prop))) otherwise.
;     Since, we first check that prop is not an atom? using the selectors will not return an error,
;     and the precondition will be met. Then (vars-in-prop-with-dubs (second-term prop)) will return the list of all the variables
;     in (second-term prop), and (append (vars-in-prop-with-dubs (first-term prop)) (vars-in-prop-with-dubs (third-term prop))) will
;     return the list of variables in (first-term prop) and (third-term prop) combined with append. So (vars-in-prop-with-dubs prop)
;     meets the post-conditions.
;     

; Termination Argument:
; Since, every recursive call we recurse on all possible sub-propositions within prop, so prop
; will eventually be an atomic prop (such as 'p or 'q) and the recursion will terminate.

(define (vars-in-prop prop) ; vars-in-prop is only to remove dublicates from the output of vars-in-prop-with-dubs
  (define (vars-in-prop-with-dubs prop)
    (cond ((atom? prop) (list prop))
          ((not-prop? prop) (vars-in-prop-with-dubs (second-term prop)))
          (else (append (vars-in-prop-with-dubs (first-term prop)) (vars-in-prop-with-dubs (third-term prop))))))
  
  (remove-dublicates (vars-in-prop-with-dubs prop)))

; test:
"vars-in-prop tests"
(vars-in-prop '(p v q))
(vars-in-prop '(p v ((r ^ s) => q)))

; audit:
; Our code does implement our Design Idea because we check if prop is an atom and return the (list prop).
; Then we check every possible proposition type NOT, OR, IMPLIES, and AND, and process the prop
; according to our design idea for each type of proposition, resulting in a list of atoms of all
; the variables in prop.

; ________________________________________________________________________________________________
;
; vars-in-alist
; ________________________________________________________________________________________________

; pre-cond : a list of variables and an a-list that contains the truth value associated with a variable.
; post-cond : returns if the variables in lst are in a-list

; DI: (map car a-list) will return a list of all the variables in a-list, then we can use
;     elems-in? function to check if variables in lst are in a-list.

(define (vars-in-alist lst a-list)
  (elems-in? lst (map car a-list)))

; tests:
"vars-in-alist tests"
(define p2 '(((- (p v q)) => (p => r)) ^ s))
(define alist1 '((p #t) (q #f) (r #t) (s #t))) ; #t

(vars-in-alist (vars-in-prop p2) alist1)

(define p3 '(((- (p v q)) => (p => r)) ^ s))
(define alist2 '((p #t) (q #f) (r #t))) ; s is removed

(vars-in-alist (vars-in-prop p3) alist2) ; returns #f

; ________________________________________________________________________________________________
;
; eval-prop
; ________________________________________________________________________________________________

; pre-cond : a valid proposition, and an a-list that contains the truth value associated with a variable.
; post-cond : returns the boolean evaluation of the proposition using variables in the a-list, if each
;             variable in the prop matchs a variable in the a-list otherwise throws error. 

; DI: This func brings everythign together, does checks prior to evaluating the prop, then
;     uses front-end to convert the prop to a prop using only NOT and AND, then uses output of the
;     front-end as the prop for the interpreter function (backend), and with the a-list, outputs the
;     boolean value of the proposition.

; Tools for making propositions:
; we can use constructors to make propositions and we can use lists to make a valid proposition.
; both are acceptable inputs.

; Tools for checking association list:
; we check association list with vars-in-alist, if it fails we return an error

(define (eval-prop prop a-list)
  (cond ((not (vars-in-alist (vars-in-prop prop) a-list)) (display "ERROR: a-list variable not in prop\n"))
        (else (interpreter (front-end prop) a-list))))

; tests:
"Final eval-prop tests"
(define p1 '(p v q))
(define alist1 '((p #t) (q #f)))

(eval-prop p1 alist1) ; -> #t

(define p1 '(p v q))
(define alist1 '((p #f) (q #f) (r #t))) ; added extra variable, since we can still get output there is no error

(eval-prop p1 alist1) ; -> #f


(define p2 '(((- (p v q)) => (p => r)) ^ s))
(define alist2 '((p #t) (q #f) (r #t) (s #t)))

(eval-prop p2 alist2) ; -> #t


(define p3 '(((- (p v q)) => (p => r)) ^ s))
(define alist3 '((p #t) (q #f) (r #t))) ; removed the s variable

(eval-prop p3 alist3) ; -> error




