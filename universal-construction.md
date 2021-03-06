Universal Constructions
=======================

Universal constructions are a pair of a theory `FTH` and a parametized module
`FMOD{X :: FTH}` such that deciding if some module `MOD` has a view from `FTH`
can be done purely with matching. If so, then the resulting substitution is used
to instantiate `FMOD{X :: FTH}`, and the resulting module is
`MOD + FMOD{X :: FTH}`. For this, we'll heavily use the machinery of
`MODULE-TEMPLATE`.

```{.maude .univ}
load module-template.maude

fmod UNIVERSAL-CONSTRUCTION is
  protecting MODULE-TEMPLATE .

  sorts UniversalConstruction ModUniversalConstruction .
  ------------------------------------------------------
  subsort ModUniversalConstruction < UniversalConstruction .

  vars SU SU' : Substitution . var SUBSTS : SubstitutionSet . var MOD : Module .
  vars MDS MDS' MDS'' : ModuleDeclSet . vars MTS MTS' : ModuleTemplateSet . vars UC UC' UC'' : UniversalConstruction .
  vars S S' S'' NeS : Sort . vars SS SS' : SortSet . vars OP Nil Q : Qid . var AS : AttrSet . var NES : Variable .
  vars NeMTS NeMTS' : NeModuleTemplateSet . var SPS : SortPoset . var SDS : SortDeclSet . var SSDS : SubsortDeclSet . vars X Y Z TH TH' : Sort . vars T T' : Term .

  op _<_> : ModUniversalConstruction Qid -> UniversalConstruction [ctor] .
  ------------------------------------------------------------------------

  op _;_ : UniversalConstruction UniversalConstruction -> UniversalConstruction [ctor assoc prec 76 format(d n d d)] .
  op _|_ : UniversalConstruction UniversalConstruction -> UniversalConstruction [ctor assoc comm prec 77 format(d n d d)] .
  -------------------------------------------------------------------------------------------------------------------------
  eq (forall MTS exists none) ; UC = UC .
  eq UC | UC = UC .

  op exists_        : ModuleTemplateSet                      -> UniversalConstruction [prec 75] .
  op forall_exists_ : ModuleTemplateSet ModuleTemplateSet    -> UniversalConstruction [ctor prec 75] .
  ----------------------------------------------------------------------------------------------------
  eq exists MTS = forall none exists MTS .
  eq forall MTS exists NeMTS | NeMTS' = (forall MTS exists NeMTS) | (forall MTS exists NeMTS) .

  op for_in__ : Sort SortDeclSet UniversalConstruction -> UniversalConstruction [prec 76] .
  -----------------------------------------------------------------------------------------
  eq  for S in none                      UC                      = exists none .
  eq  for S in SDS                       (UC ; UC')              = (for S in SDS UC) ; (for S in SDS UC') .
  eq  for S in SDS                       (UC | UC')              = (for S in SDS UC) | (for S in SDS UC') .
  eq  for S in ( sorts S' ; S'' ; SS . ) UC                      = (for S in ( sorts S' . ) UC) | (for S in ( sorts S'' . ) UC) | (for S in ( sorts SS . ) UC) .
  ceq for S in ( sorts S' . )            (forall MTS exists MDS) = forall (MTS << SU) exists (MDS << SU) if SU := upTerm(S) <- upTerm(S') .

---  op _over_ : UniversalConstruction ModuleTemplate -> UniversalConstruction [prec 76] .
---  -------------------------------------------------------------------------------------
---  eq (forall MT exists MT' | UC) over MT'' = (forall MT exists MT' over MT'') | (UC over MT'') .
---  eq (forall MT exists MT' ; UC) over MT'' = (forall MT exists MT' over MT'') ; (UC over MT'') .
---  eq forall MT exists MT' over MT'' = forall (MT \ (( sorts none . ) \ MT'')) exists MT' .

  op univ_ : ModuleDeclSet -> UniversalConstruction [prec 75] .
  -------------------------------------------------------------
  eq univ MDS = forall ( sorts fv<Sort>(MDS) . ) exists MDS .

  op _<<_ : UniversalConstruction SubstitutionSet -> UniversalConstruction .
  --------------------------------------------------------------------------
  eq UC << empty                   = UC .
  eq UC << (SU | SU' | SUBSTS)     = (UC << SU) | (UC << SU') | (UC << SUBSTS) .
  eq (UC | UC') << SU              = (UC << SU) | (UC' << SU) .
  eq (UC ; UC') << SU              = (UC << SU) ; (UC' << SU) .
  eq (forall MTS exists MDS) << SU = (forall (MTS << SU) exists (MDS << SU)) | (forall MTS exists MDS) .
```

```{.maude .univ}
  op _deriving_ : ModuleDeclSet UniversalConstruction -> ModuleDeclSet [prec 76] .
  --------------------------------------------------------------------------------
  ceq MDS deriving forall MTS exists MDS'           = ++(MDS | (MDS' << SUBSTS))                          if SUBSTS := match MTS with MDS .
  ceq MDS deriving forall MTS exists (MDS' \ NeMTS) = ++(MDS | not-instance-of?((MDS' << SUBSTS), NeMTS)) if SUBSTS := match MTS with MDS .
  eq  MDS deriving (UC ; UC')                       = (MDS deriving UC) deriving UC' .
  eq  MDS deriving (UC | UC')                       = (MDS deriving UC) (MDS deriving UC') .

  op not-instance-of? : ModuleTemplateSet ModuleTemplateSet -> ModuleTemplateSet .
  --------------------------------------------------------------------------------
  ceq not-instance-of?(MDS, MTS)              = if SUBSTS == empty then MDS else none fi if SUBSTS := match MTS with MDS .
  eq  not-instance-of?((NeMTS | NeMTS'), MTS) = not-instance-of?(NeMTS, MTS) | not-instance-of?(NeMTS', MTS) .
```

Covariant Constructions
-----------------------

Covariant constructions copy sort structure and subsort relations, preserving
the ordering. In general, you may want to just copy the sort structure with a
new name, or copy the sort structure and then make the copies subsorts (or
supersorts) of the original.

-   `covariant : Sort Sort -> UniversalConstruction` will just copy the sort and
    subsort structure. The first sort serves as a template for which sorts to
    copy, and the secord sort serves as a template for the sort to build.

-   `covariant-data-up : Sort Sort -> UniversalConstruction` creates a copy of
    the sort structure and makes the copy super-sorts of the original.

-   `covariant-data-down : Sort Sort -> UniversalConstruction` creates a copy of
    the sort structure and makes the copy subsorts of the original.

```{.maude .univ}
  op covariant : Sort Sort -> UniversalConstruction .
  ---------------------------------------------------
  eq covariant(S, S') =   forall ( sorts S . )
                          exists ( sorts S' . )
                        ; forall ( sorts S        ; S'
                                       ; prime(S) ; prime(S') .
                                 )
                                 ( subsort S  < prime(S) . )
                          exists ( subsort S' < prime(S') . ) .

  op covariant-data-up : Sort Sort -> UniversalConstruction .
  -----------------------------------------------------------
  eq covariant-data-up(S, S') =   covariant(S, S')
                                ; forall ( sorts S ; S' . )
                                  exists ( subsort S < S' . ) .

  op covariant-data-down : Sort Sort -> UniversalConstruction .
  -------------------------------------------------------------
  eq covariant-data-down(S, S') =   covariant(S, S')
                                  ; forall ( sorts S ; S' . )
                                    exists ( subsort S < S' . ) .
```

A common idiom is to create the subsort-chain `X < NeF{X} < F{X}`, where `F` is
some data-structure and `NeF` is the non-empty version. These data-structures
are often over binary operators with given axioms. Here, `covariant-data-up` is
used twice to build the desired sort structure, then the appropriate binary
operators with unit are declared.

-   `covariant-data-binary : Sort Qid AttrSet -> UniversalConstruction` makes a
    covariant data-structure with a binary operator as constructor.

```{.maude .univ}
  op covariant-data-binary : Sort Qid AttrSet -> UniversalConstruction .
  ----------------------------------------------------------------------
  ceq covariant-data-binary(S, OP, AS) =   covariant-data-up(X, NeS{X})
                                         ; covariant-data-up(NeS{X}, S{X})
                                         ; forall ( sorts X ; S{X} ; NeS{X} . )
                                                  ( subsorts X < NeS{X} < S{X} . )
                                           exists ( op Nil : nil -> S{X} [ctor] .
                                                    op OP : (S{X})   (S{X}) ->   S{X} [ctor id(const(Nil, S{X})) AS] .
                                                    op OP : (S{X}) (NeS{X}) -> NeS{X} [ctor id(const(Nil, S{X})) AS] .
                                                  )
                                       if NeS := qid("Ne" + string(S))
                                       /\ Nil := qid("." + string(S))
                                       /\ X   := var<Sort>('X) .
```

The universal constructions for the list and set data-types are provided here in
terms of `covariant-binary-data`.

-   `LIST : -> UniversalConstruction` constructs the sorts
    `X < NeList{X} < List{X}` for every `X` in the module, using `_,_` as the
    associative constructor and `.List` as the empty list.

-   `MSET : -> UniversalConstruction` constructs the sorts
    `X < NeMSet{X} < MSet{X}` for every `X` in the module, using `_;_` as the
    associative-commutative constructor and `.MSet` as the empty set.

-   `SET : -> UniversalConstruction` constructs the sorts
    `X < NeSet{X} < Set{X}` for every `X` in the module, using `_;_` as the
    associative-commutative constructor and `.Set` as the empty set.
    Additionally, the set-idempotency equation is added.

```{.maude .univ}
  ops LIST MSET SET : -> UniversalConstruction .
  ----------------------------------------------
  eq  LIST = covariant-data-binary('List, '_`,_, assoc) .
  eq  MSET = covariant-data-binary('MSet, '_;_, assoc comm) .
  ceq SET  =   covariant-data-binary('Set, '_;_, assoc comm)
             ; forall ( sorts 'NeSet{var<Sort>('X)} . )
               exists ( eq '_;_[NES, NES] = NES [none] . )
           if NES := var('NeS, 'NeSet{var<Sort>('X)}) .
```

Signature Refinement
--------------------

Signature refinements add subsorts to every sort (adding the annotation that
they are refined), as well as copying operators over only the refined sorts
down. Right now only operators up to arity 2 are handled (until we have a better
way to generate them).

```{.maude .univ}
  op signature-refinement : Qid -> UniversalConstruction .
  --------------------------------------------------------
  eq signature-refinement(Q) =   covariant-data-down(var<Sort>('X), var<Sort>('X){Q})
                               ; signature-refinement(0, Q)
                               ; signature-refinement(1, Q)
                               ; signature-refinement(2, Q) .

  op signature-refinement : Nat Qid -> UniversalConstruction .
  ------------------------------------------------------------
  ceq signature-refinement(0, Q) = forall ( sorts X ; X{Q} . )
                                          ( op OP : nil -> X [var<AttrSet>('AS)] . )
                                   exists ( op OP : nil -> X{Q} [var<AttrSet>('AS)] . )
                                 if X  := var<Sort>('X)
                                 /\ OP := var<Qid>('OP) .
  ceq signature-refinement(1, Q) = ( forall ( sorts X ; X{Q} ; Y ; Y{Q}. )
                                            ( op OP : Y -> X [var<AttrSet>('AS)] . )
                                     exists ( op OP : Y{Q} -> X{Q} [var<AttrSet>('AS)] . )
                                   ) << ('X:Sort <- 'Y:Sort)
                                 if X  := var<Sort>('X)
                                 /\ Y  := var<Sort>('Y)
                                 /\ OP := var<Qid>('OP) .
  ceq signature-refinement(2, Q) = ( forall ( sorts X ; X{Q} ; Y ; Y{Q} ; Z ; Z{Q} . )
                                            ( op OP : Y Z -> X [var<AttrSet>('AS)] . )
                                     exists ( op OP : (Y{Q}) (Z{Q}) -> X{Q} [var<AttrSet>('AS)] . )
                                   ) << (('X:Sort <- 'Y:Sort) | ('X:Sort <- 'Z:Sort) | ('Y:Sort <- 'Z:Sort) | ('Y:Sort <- 'X:Sort ; 'Z:Sort <- 'X:Sort))
                                 if X  := var<Sort>('X)
                                 /\ Y  := var<Sort>('Y)
                                 /\ Z  := var<Sort>('Z)
                                 /\ OP := var<Qid>('OP) .
```

Exponential Objects
-------------------

For functional-style programming (including higher-order functional
programming), it's necessary to reify arrows between sorts (functions) as
objects themselves. This `EXPONENTIAL` universal construction does that.

```{.maude .univ}
--- todo:
--- make identify functions actually behave like identity in composition

  op EXPONENTIAL : -> UniversalConstruction .
  -------------------------------------------
  ceq EXPONENTIAL =   ( forall ( sorts X ; Y . )
                        exists ( sorts X ==> Y . )
                               ( op '__ : (X ==> Y) X -> Y [none] . )
                      ) << ('Y:Sort <- 'X:Sort)
                    ; forall ( sorts X ==> X . )
                      exists ( op 'id < X > : nil -> X ==> X [ctor] . )
                             ( eq '__[const('id < X >, X ==> X), var('X, X)] = var('X, X) [none] . )
                    ; forall ( sorts X ; Y ; Z ; X ==> Y ; X ==> Z . )
                             ( subsort Y < Z . )
                      exists ( subsort X ==> Y < X ==> Z . )
                    ; forall ( sorts X ; Y ; Z ; X ==> Y ; Z ==> Y . )
                             ( subsort Z < X . )
                      exists ( subsort X ==> Y < Z ==> Y . )
                    ; forall ( sorts X ==> Y ; Y ==> Z ; X ==> Z . )
                      exists ( op '_._ : (Y ==> Z) (X ==> Y) -> X ==> Z [none] .
                               op '_;_ : (X ==> Y) (Y ==> Z) -> X ==> Z [none] .
                             )
                  if X := var<Sort>('X)
                  /\ Y := var<Sort>('Y)
                  /\ Z := var<Sort>('Z) .
```

Meta Theory
-----------

Sometimes you want a "meta theory" specific to your module. For example, you may
want to express using just a sort that a meta-level `Term` is a well-formed term
in your theory, or that it is a well-formed term of a specific sort in your
theory. This universal construction will extend your module with its meta-theory, so
that this can be done. This is a construction that refines the module
`META-TERM` and adds it to your module, as well as adding in conditional
memberships which push elements of the sort `Term` into the subsort of
`Term{MYMOD}` when appropriate.

```{.maude .univ}
  op cmb-pred : Sort Sort Qid -> MembAx .
  ---------------------------------------
  eq cmb-pred(S, S', Q) = ( cmb var('X, S) : S' if Q[var('X, S)] = 'true.Bool [none] . ) .

  op top-sorts : Sort -> ModuleTemplateSet .
  ------------------------------------------
  eq top-sorts(S) = (sorts S .) \ ((sorts S ; prime(S) .) subsort S < prime(S) .) .

  op sort-intersect : Sort -> UniversalConstruction .
  ---------------------------------------------------
  ceq sort-intersect(S) = forall ( sorts S{X} ; S{Y} . )
                          exists ( sorts S{X Y} . )
                                 ( subsorts S{X Y} < S{X} ; S{Y} . )
                                 ( cmb var('T, S{X}) : S{X Y} if var('T, S{X}) : S{Y} [none] .
                                   cmb var('T, S{Y}) : S{X Y} if var('T, S{Y}) : S{X} [none] .
                                 )
                        if X := var<Sort>('X)
                        /\ Y := var<Sort>('Y) .

  op DOWN-TERM : -> ModUniversalConstruction .
  --------------------------------------------
  ceq DOWN-TERM < Q > =   exists ( pr 'META-LEVEL .
                                   pr Q .
                                 )
                        ; covariant-data-up(X, X ?)
                        ; forall ( sorts X ; X ? . )
                                 ( subsort X < X ? . )
                          exists ( op 'downTermError < X > : nil   -> X ?   [ctor] .
                                   op 'downTerm      < X > : 'Term -> X ?   [none] .
                                   op 'wellFormed    < X > : 'Term -> 'Bool [none] .
                                 )
                                 ( ceq 'downTerm   < X > [var('T, 'Term)] = var('X, X) if var('X, X) := 'downTerm[var('T, 'Term), const('downTermError < X >, X ?)] [none] .
                                   ceq 'wellFormed < X > [var('T, 'Term)] = 'true.Bool if var('X, X) := 'downTerm < X > [var('T, 'Term)] [none] .
                                 )
                      if X := var<Sort>('X) .

  op META-TERM : -> ModUniversalConstruction .
  --------------------------------------------
  ceq META-TERM < Q > =   DOWN-TERM < Q >
                        ; exists tag-sorts(Q, (SDS SSDS))
                        ; for TH in SDS ( exists ( subsort TH{Q} < TH . )
                                        ; forall ( sorts X ; X ? . ) exists ( sorts TH{X @ Q} . )
                                        ; forall top-sorts(X ?)      exists ( subsort TH{X @ Q} < TH{Q} . )
                                        )
                        ; covariant(TH{Q}, TH{X @ Q})
                        ; covariant(X, TH{X @ Q})
                      if SDS SSDS := connected-component(asTemplate('META-TERM), ( sorts 'Term . ))
                      /\ X        := var<Sort>('X)
                      /\ Y        := var<Sort>('Y)
                      /\ TH       := var<Sort>('TH) .
endfm
```

Module Expressions
==================

This module simply provides the hookup to our extension of the Meta-Level module
expressions. A memo-ised version of `upModule` is provided too for the
extensions. In addition, free constructions are provided. Universal constructions
provide a module template with variables to determine anonymous views, and a
second module template to determine the associated parameterized module.

```{.maude .univ}
fmod MODULE-EXPRESSION is
  extending UNIVERSAL-CONSTRUCTION .

  var MOD : Module . var ME : ModuleExpression . var SUBSTS : SubstitutionSet .
  vars UC UC' : UniversalConstruction . var MUC : ModUniversalConstruction .
  var MDS : ModuleDeclSet . var MTS : ModuleTemplateSet . var Q : Qid . vars S S' : Sort . var SS : SortSet .
  vars X Y T : Sort .

  op #upModule : ModuleExpression -> Module [memo] .
  --------------------------------------------------
  eq #upModule(ME) = upModule(ME, false) [owise] .

  op _deriving_ : ModuleExpression UniversalConstruction -> ModuleExpression [prec 80] .
  --------------------------------------------------------------------------------------
  eq #upModule(ME deriving UC) = #upModule(ME) deriving UC .

---  op META-TERM : -> ModUniversalConstruction .
---  --------------------------------------------
---  ceq META-TERM < Q > =   exists ( pr 'META-LEVEL . )
---                        ; forall ( sorts X . )
---                          exists asTemplate(#upModule('META-TERM deriving ( covariant-data-down(T, T{Q})
---                                                                          ; covariant(T{Q}, T{Q @ X})
---                                                                          )
---                                                     )
---                                           )
---                        ; forall ( sorts X ; T{Q @ X}
---                                       ; Y ; T{Q @ Y} .
---                                 )
---                                 ( subsort X < Y . )
---                          exists ( subsort T{Q @ X} < T{Q @ Y} . )
---                       ;  forall ( sorts X ; T{Q @ X} ; T{Q} . )
---                               \ ( sorts X ; T{Q @ X}
---                                       ; Y ; T{Q @ Y} .
---                                 )
---                                 ( subsort X < Y .
---                                   subsort T{Q @ X} < T{Q @ X} .
---                                 )
---                          exists ( subsort T{Q @ X} < T{Q} . )
---                      if X := var<Sort>('X)
---                      /\ Y := var<Sort>('Y)
---                      /\ T := var<Sort>('T) .

  op tmp-mb : Sort Sort Qid -> UniversalConstruction .
  ----------------------------------------------------
  eq tmp-mb(S, S', Q) = forall ( sorts S ; S ? ; S'{Q @ S} . )
                        exists ( cmb-pred( S' , S'{Q @ S} , 'wellFormed < S > ) ) .

  op META-THEORY : -> ModUniversalConstruction .
  ----------------------------------------------
  ceq META-THEORY < Q > =   ( DOWN-TERM | META-TERM < Q > )
                          ; tmp-mb(X, 'Constant,   Q)
                          ; tmp-mb(X, 'GroundTerm, Q)
                          ; tmp-mb(X, 'Variable,   Q)
                          ; tmp-mb(X, 'Term,       Q)
                        if X := var<Sort>('X) .

---    vars M1 M2          : ModuleExpression .
---    vars TM TM' TM1 TM2 : Variable .
---    op PURIFICATION : ModuleExpression ModuleExpression -> UniversalConstruction .
---    ------------------------------------------------------------------------------
---    ceq PURIFICATION(M1, M2)
---      =   META-THEORY < M1 >
---        ; META-THEORY < M2 >
---        ; exists ( extending 'FOFORM .
---                   extending M1 .
---                   extending M2 . )
---                 ( sorts none . )
---                 ( op 'purify : 'EqAtom -> 'EqConj [none] .
---                   op 'fvar   : 'Term 'Term -> 'Variable [none] . )
---        ; forall ( sorts 'Term ; 'Term{svar('M)} . )
---                 ( subsort 'Term{svar('M)} < 'Term . )
---          exists ( sorts none . )
---                 ( eq 'purify['_?=_[TM, TM']] = '_?=_[TM, TM'] [none] . )
---        ; forall ( sorts 'Term ; 'Term{svar('M1)} ; 'Term{svar('M2)} . )
---                 ( subsorts 'Term{svar('M1)} ; 'Term{svar('M2)} < 'Term . )
---          exists ( sorts none . )
---                 ( eq 'purify['_?=_[TM1, TM2]] = '_/\_['_?=_['fvar[TM1, TM2], TM1], '_?=_['fvar[TM1, TM2], TM2]] [none] . )
---
---      if TM  := var('TM,  'Term{svar('M)})
---      /\ TM' := var('TM', 'Term{svar('M)})
---      /\ TM1 := var('TM1, 'Term{svar('M1)})
---      /\ TM2 := var('TM2, 'Term{svar('M2)}) .

  op _deriving_ : Module UniversalConstruction -> [Module] [prec 80] .
  --------------------------------------------------------------------
  eq MOD deriving UC = fromTemplate(getName(MOD), asTemplate(MOD) deriving UC) .
endfm
```
