```{.maude .vabs}
load foform.maude
load ../src/intersection.maude
load ../tests/test-modules.maude

--- VARIABLE ABSTRACTION
--- Input: Conjunction of Equations of the form T ?= T' and T != T'

fmod VABS is
    pr FOFORM .
    pr FOFORMSIMPLIFY-IMPL .
    pr TEST-MODULE .
    pr BREAK-EQATOMS .

    vars V NV : Variable .
    var F : Qid .
    vars T T' : Term .
    vars TL TL' : TermList .
    vars M1 M2 : ModuleExpression .
    var EqA : EqAtom .
    vars EqC EqC' : EqConj .

    op vabs :     ModuleExpression ModuleExpression EqConj -> EqConj .

    ceq vabs(M1, M2, T ?= T') = vabs(M1, M2, break-eqatoms(M1, M2, T ?= T'))
      if not (T :: Variable or T' :: Variable) .
      
    ceq vabs(M1, M2, T != T') = vabs(M1, M2, break-eqatoms(M1, M2, T != T'))
      if not (T :: Variable or T' :: Variable) .

    ceq vabs(M1, M2, F[TL, T, TL'] ?= V)
      = vabs(M1, M2, F[TL, NV, TL'] ?= V) /\ vabs(M1, M2, NV ?= T)
      if not (T :: Variable) 
      /\ NV := joint-variable(M1, M2, T) .

    ceq vabs(M1, M2, F[TL, T, TL'] != V)
      = vabs(M1, M2, F[TL, NV, TL'] != V) /\ vabs(M1, M2, NV ?= T)
      if not (T :: Variable) 
      /\ NV := joint-variable(M1, M2, T) .

    eq vabs(M1, M2, EqC /\ EqC') = vabs(M1, M2, EqC) /\ vabs(M1, M2, EqC') .
    eq vabs(M1, M2, EqA) = EqA [owise] .
endfm
    
reduce upModule('VABS, false) .
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'x:A ?= 'f['a.A]) .
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A]) .
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['f['a.A]]] ?= 'f['a.A]) .
```
