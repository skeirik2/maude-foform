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
    pr FVAR-CONCRETE .

    vars V NV : Variable .
    var F : Qid .
    vars T T' : Term .
    vars TL TL' : TermList .
    vars M1 M2 : ModuleExpression .
    vars EqC EqC' : EqConj .

    op destruct : ModuleExpression ModuleExpression EqConj -> EqConj .
    op vabs :     ModuleExpression ModuleExpression EqConj -> EqConj .

    ceq destruct(M1, M2, T ?= T') = T ?= NV /\ T' ?= NV
      if not (T :: Variable or T' :: Variable)
      /\ NV := joint-variable(M1, M2, T) .

    ceq destruct(M1, M2, T != T') = T ?= NV /\ T' != NV
      if not (T :: Variable or T' :: Variable)
      /\ NV := joint-variable(M1, M2, T) 
      /\ sortLeq(upModule(M1, false), leastSort(upModule(M1, false), T), leastSort(upModule(M1, false), NV)) = true .

    ceq destruct(M1, M2, T != T') = T ?= NV /\ T' != NV
      if not (T :: Variable or T' :: Variable)
      /\ NV := joint-variable(M1, M2, T) 
      /\ sortLeq(upModule(M2, false), leastSort(upModule(M2, false), T), leastSort(upModule(M2, false), NV)) = true .
      
    ceq vabs(M1, M2, T ?= T') = vabs(M1, M2, destruct(M1, M2, T ?= T'))
      if not (T :: Variable or T' :: Variable) .
      
    ceq vabs(M1, M2, T != T') = vabs(M1, M2, destruct(M1, M2, T != T'))
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