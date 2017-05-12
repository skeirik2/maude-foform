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

    vars V FV : Variable . var C : Constant . var Q : Qid . vars T T' T'' : Term .
    vars TL TL' : TermList . vars NeTL NeTL' : NeTermList . 
    var ME : ModuleExpression . var M : Module .
    var EqA : EqAtom . vars EqC EqC' : EqConj . var TA : TruthAtom .

    op vabs : ModuleExpression EqConj -> [EqConj] .
    -----------------------------------------------
    eq vabs(ME, EqC) = vabs(upModule(ME, true), EqC) .
```

`abstracted : Term -> Bool` returns true if the current is abstracted.

```{.maude .vabs}
    op abstracted : Term -> Bool .
    ------------------------------
    eq  abstracted(T)             = true [owise] .
    ceq abstracted(Q[TL, T, TL']) = false if not (T :: Variable) .
```

The operation `vabs : Module EqConj -> EqConj` takes in an equational conjunction and variable abstracts all the equational atoms.

```{.maude .vabs}
    op vabs : Module EqConj -> [EqConj] .
    -------------------------------------
    eq  vabs(M, EqC /\ EqC') = vabs(M, EqC) /\ vabs(M, EqC') .
    ceq vabs(M, V ?= T)      = V ?= T if abstracted(T) .
    ceq vabs(M, V != T)      = V != T if abstracted(T) .
```

If the top terms in the equality atom are both not variables and abstracted, then `break-eqatoms` is used to make it a conjunct of simple equalities.

```{.maude .vabs}
    ceq vabs(M, T ?= T') = break-eqatoms(M, M, T ?= T') if not (T :: Variable or T' :: Variable) /\ abstracted(T) /\ abstracted(T') .
    ceq vabs(M, T != T') = break-eqatoms(M, M, T != T') if not (T :: Variable or T' :: Variable) /\ abstracted(T) /\ abstracted(T') .
```

If there is a non-variable subterm, it is extracted as an equality.
Both the remaining subterms and the new equality are variable abstracted.

```{.maude .vabs}
    ceq vabs(M, Q[TL, T, TL'] ?= T') = vabs(M, Q[TL, FV, TL'] ?= T') /\ vabs(M, FV ?= T) if not (T :: Variable) /\ FV := joint-variable(M, M, T) .
    ceq vabs(M, Q[TL, T, TL'] != T') = vabs(M, Q[TL, FV, TL'] != T') /\ vabs(M, FV ?= T) if not (T :: Variable) /\ FV := joint-variable(M, M, T) .
endfm
```

### Examples

This is a sampling of the test cases in `tests/test-modules.maude` with a more human-readable output, using this module:

```
fmod TEST-MODULE is
  sorts A B .
  subsort A < B .
    
  op a : -> A .
  op b : -> B .
    
  op f : B -> A .
  ---------------
  eq f(b) = a .
endfm

reduce vabs('TEST-MODULE, 'x:A ?= 'f['a.A]) .
Output: V0 ?= a /\ x ?= f(V0)

reduce vabs('TEST-MODULE, 'f['f['a.A]] ?= 'f['b.A]) .
Output: V0 ?= a /\ V1 ?= b /\ V2 ?= f(V0) /\ V3 ?= f(V1) /\ V3 ?= f(V2)

reduce vabs('TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['f['a.A]]] != 'f['a.A]) .
Output: V0 ?= a /\ V1 ?= f(V0) /\ V1 ?= f(V1) /\ V2 ?= f(V1) /\ V1 != V2

reduce vabs('TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f['a.A]] != 'f['a.A]) .
Output: V0 ?= a /\ V1 ?= f(V0) /\ V1 ?= f(V1) /\ V1 != f(V1)

reduce vabs('TEST-MODULE, 'f['f['a.A]] ?= 'f['a.A] /\ 'f['f'['f['x:A]]] != 'f['a.A]) .
Output: V0 ?= a /\ V1 ?= f(V0) /\ V1 ?= f(V1) /\ V2 ?= f(V3) /\ V3 ?= f(x) /\ V1 != f(V2)

reduce vabs('TEST-MODULE, 'f['b.A] ?= 'f['a.A] /\ 'f['f'['f['x:A]]] != 'f['b.A]) .
Output: V0 ?= a /\ V1 ?= b /\ V2 ?= f(V0) /\ V2 ?= f(V1) /\ V3 ?= f(V1) /\ V4 ?= f(V5) /\ V5 ?= f(x) /\ V3 != f(V4)
```

For more test cases using more complex modules, see `tests/test-modules.maude`.
