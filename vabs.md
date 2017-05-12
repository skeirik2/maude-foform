Variable Abstraction
====================

Variable abstraction reduces a conjunction of equality atoms to the cases:

-   `x ?= T` and `x != T` where `x` is a variable of the same sort as term `T`.

VARIABLE ABSTRACTION

Input: Two modules M1, M2, and an Equational Conjunction: a conjunction of 
equations of the form T ?= T' and T != T'. 
Optimally intersectable signatures are assumed.

Output: A new Equational Conjunction, where each Equational Atom is of the
form "T1 = T2", where either T1 or T2 (or both) is a variable, and the other
is of the form f(V1, ..., Vn) for variables V1 through Vn.

```{.maude .vabs}
load ../src/intersection.maude

fmod VABS is
    pr FOFORM .
    pr FOFORMSIMPLIFY-IMPL .
    pr BREAK-EQATOMS .

    vars V FV : Variable . var F : Qid . vars T T' : Term .
    vars TL TL' : TermList . var ME : ModuleExpression . var M : Module .
    var EqA : EqAtom . vars EqC EqC' : EqConj . var TA : TruthAtom .

    op vabs : ModuleExpression EqConj -> EqConj .
    ---------------------------------------------
    eq vabs(ME, EqC) = vabs(upModule(ME, true), EqC) .
```

The operation `vabs : Module EqConj -> EqConj` takes in an equational conjunction and variable abstracts all the equational atoms.

```{.maude .vabs}
    op vabs : Module EqConj -> EqConj .
    -----------------------------------
    eq vabs(M, EqC)         = EqC [owise] .
    eq vabs(M, EqC /\ EqC') = vabs(M, EqC) /\ vabs(M, EqC') .
```

If the top terms in the equality atom are both not variables, then `break-eqatoms` is used to make it a conjunct of simple equalities.

```{.maude .vabs}
    ceq vabs(M, T ?= T') = vabs(M, break-eqatoms(M, M, T ?= T')) if not (T :: Variable or T' :: Variable) .
    ceq vabs(M, T != T') = vabs(M, break-eqatoms(M, M, T != T')) if not (T :: Variable or T' :: Variable) .
```

If there is a non-variable subterm, it is extracted as an equality.
Both the remaining subterms and the new equality are variable abstracted.

```{.maude .vabs}
    ceq vabs(M, F[TL, T, TL'] ?= V) = vabs(M, F[TL, FV, TL'] ?= V) /\ vabs(M, FV ?= T)
                                    if not (T :: Variable) /\ FV := joint-variable(M, M, T) .

    ceq vabs(M, F[TL, T, TL'] != V) = vabs(M, F[TL, FV, TL'] != V) /\ vabs(M, FV ?= T)
                                    if not (T :: Variable) /\ FV := joint-variable(M, M, T) .
endfm
```

### Examples

```
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'x:A ?= 'f['a.A]) .
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['b.A]) .
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['f['a.A]]] != 'f['a.A]) .
reduce vabs('TEST-MODULE, 'TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['a.A]] != 'f['a.A]) .
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
