```{.maude .vabs}
load ../src/intersection.maude

--- VARIABLE ABSTRACTION
---
--- Input: Two modules M1, M2, and an Equational Conjunction: a conjunction of 
--- equations of the form T ?= T' and T != T'. 
--- Optimally intersectable signatures are assumed.
---
--- Output: A new Equational Conjunction, where each Equational Atom is of the
--- form "T1 = T2", where either T1 or T2 (or both) is a variable, and the other
--- is of the form f(V1, ..., Vn) for variables V1 through Vn.

fmod VABS is
    pr FOFORM .
    pr FOFORMSIMPLIFY-IMPL .
    pr BREAK-EQATOMS .

    vars V NV : Variable .
    var F : Qid .
    vars T T' : Term .
    vars TL TL' : TermList .
    var M : ModuleExpression .
    var EqA : EqAtom .
    vars EqC EqC' : EqConj .

    op vabs : ModuleExpression EqConj -> EqConj .

    ceq vabs(M, T ?= T') = vabs(M, break-eqatoms(M, M, T ?= T'))
      if not (T :: Variable or T' :: Variable) .
      
    ceq vabs(M, T != T') = vabs(M, break-eqatoms(M, M, T != T'))
      if not (T :: Variable or T' :: Variable) .

    ceq vabs(M, F[TL, T, TL'] ?= V)
      = vabs(M, F[TL, NV, TL'] ?= V) /\ vabs(M, NV ?= T)
      if not (T :: Variable) 
      /\ NV := joint-variable(M, M, T) .

    ceq vabs(M, F[TL, T, TL'] != V)
      = vabs(M, F[TL, NV, TL'] != V) /\ vabs(M, NV ?= T)
      if not (T :: Variable) 
      /\ NV := joint-variable(M, M, T) .

    eq vabs(M, EqC /\ EqC') = vabs(M, EqC) /\ vabs(M, EqC') .
    eq vabs(M, EqA) = EqA [owise] .
endfm

--- One module test cases
---reduce vabs('TEST-MODULE, 'TEST-MODULE, 'x:A ?= 'f['a.A]) .
---reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['b.A]) .
---reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['f['a.A]]] != 'f['a.A]) .
---reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['a.A]] != 'f['a.A]) .

--- Two modules test cases
```

Test cases:

One module (TEST-MODULE):

Input:  x ?= f(a)
Output: V0 ?= a /\ x ?= f(V0)

Input:  f(f(a)) ?= f(b)
Output: V0 ?= a /\ V1 ?= b /\ V2 ?= f(V0) /\ V3 ?= f(V1) /\ V3 ?= f(V2)

Input:  f(f(a)) ?= f(a) /\ f(f(f(a))) != f(a)
Output: V0 ?= a /\ V1 ?= f(V0) /\ V1 ?= f(V1) /\ V2 ?= f(V1) /\ V1 != V2

Input:  f(f(a)) ?= f(a) /\ f(f(a)) != f(a)
Output: V0 ?= a /\ V1 ?= f(V0) /\ V1 ?= f(V1) /\ V1 != f(V1)


Two modules (MYINT, MYINT-RAT):

Input:  
