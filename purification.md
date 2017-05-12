Purification
============

Purification ensures that a conjunction of equational atoms has sub-conjuncts strictly formed of equational atoms from the individual theories.
The resulting formulas will always be of the form

-   `T ?= T'` or `T != T'` with `T` and `T'` in the same signature.
-   `x ?= T` or `x != T` with `x` a variable of appropriate sort in the signature of `T`.

```{.maude .purification}
load intersection.maude .

fmod PURIFICATION is
  protecting META-LEVEL .
  protecting FOFORMSIMPLIFY-IMPL .
  protecting CTERM-SET * ( op _;;_ to _;;;_ ) .
  protecting BREAK-EQATOMS .

  var Q : Qid . var TA : TruthAtom . vars EqC EqC' : EqConj .
  vars ME1 ME2 : ModuleExpression . vars M M' : Module . 
  vars FV : Variable . vars T T' T1 T2 : Term .
  vars NeTL NeTL' : NeTermList . vars TL TL' : TermList . vars TL? TL?' : [TermList] .

  op _in_ : EqConj Module -> Bool .
  ---------------------------------
  eq TA            in M = true .
  eq (EqC /\ EqC') in M = (EqC in M) and (EqC' in M) .
  eq (T ?= T')     in M = wellFormed(M, T) and wellFormed(M, T') .
  eq (T != T')     in M = wellFormed(M, T) and wellFormed(M, T') .
```

When purifying we'll generate extra constraints we want to bubble to the top.
Allowing QF equality atoms to bubble to the top is safe.

```{.maude .purification}
  op _?=_ : CTerm CTerm -> EqConj [ditto] .
  op _!=_ : CTerm CTerm -> EqConj [ditto] .
  -----------------------------------------
  eq T ?= (T' | EqC)         = (T ?= T') /\ EqC .
  eq T != (T' | EqC)         = (T != T') /\ EqC .
  eq Q[TL?, (T | EqC), TL?'] = Q[TL?, T, TL?'] | EqC .
```

Purifying Equational Conjunctions
---------------------------------

Purification first checks if the conjunction is well-formed in one of the modules.
If so, then it 

```{.maude .purification}
  op purify : ModuleExpression ModuleExpression EqConj -> [EqConj] .
  ------------------------------------------------------------------
  eq purify(ME1, ME2, EqC) = purify(upModule(ME1, true), upModule(ME2, true), EqC) .

  op purify : Module Module EqConj -> [EqConj] .
  ----------------------------------------------
  ceq purify(M, M', EqC)         = EqC if (EqC in M) or (EqC in M') .
  eq  purify(M, M', EqC /\ EqC') = purify(M, M', EqC) /\ purify(M, M', EqC') .
```

If one of the sides of the equality is not in the first module, purify it with respect to the first module 

```{.maude .purification}
  ceq purify(M, M', T1 ?= T2) = purify(M, M', purify(M, M', T1) ?= T2) if not wellFormed(M, T1) .
  ceq purify(M, M', T1 != T2) = purify(M, M', purify(M, M', T1) != T2) if not wellFormed(M, T1) .
```

If the term is well-formed in the first module, return it.

```{.maude .purification}
  op purify : ModuleExpression ModuleExpression TermList -> [CTerm] .
  -------------------------------------------------------------------
  eq purify(ME1, ME2, TL) = purify(upModule(ME1, true), upModule(ME2, true), TL) .

  op purify : Module Module TermList -> [CTerm] .
  -----------------------------------------------
  eq purify(M, M', empty)          = empty .
  eq purify(M, M', (NeTL , NeTL')) = purify(M, M', NeTL) , purify(M, M', NeTL') .

  ceq purify(M, M', T)     = T                       if wellFormed(M, T) .
  ceq purify(M, M', Q[TL]) = Q[purify(M, M', TL)]   if Q in asTemplate(M) .
  ceq purify(M, M', Q[TL]) = FV | ((FV ?= T) /\ EqC) if (not Q in asTemplate(M)) /\ Q in asTemplate(M')
                                                      /\ T | EqC := purify(M', M, Q[TL])
                                                      /\ FV      := joint-variable(M, M', Q[TL]) .
endfm
```
