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
  subsort ModUniversalConstruction < UniversalConstruction .

  var SUBSTS : SubstitutionSet . var MOD : Module . vars MT MT' MT'' : ModuleTemplate . vars UC UC' UC'' : UniversalConstruction .
  vars S S' NeS : Sort . vars SS : SortSet . vars Op Nil Q : Qid . var AS : AttrSet . var NES : Variable .
  vars SUB SUB' : Substitution . var SUBS : SubstitutionSet . vars NeMTS NeMTS' : NeModuleTemplateSet . var SPS : SortPoset .
  var SSDS : SubsortDeclSet .

  op _<_> : ModUniversalConstruction Qid -> UniversalConstruction [ctor] .
  ------------------------------------------------------------------------

  op exists_        : ModuleTemplate                   -> UniversalConstruction [prec 75] .
  op forall_exists_ : ModuleTemplateSet ModuleTemplate -> UniversalConstruction [prec 75] .
  op forall_exists_ : ModuleTemplate    ModuleTemplate -> UniversalConstruction [ctor prec 75] .
  ----------------------------------------------------------------------------------------------
  eq exists MT                       = forall (sorts none .) exists MT .
  eq forall NeMTS | NeMTS' exists MT = forall NeMTS exists MT | forall NeMTS' exists MT .

  op _over_ : UniversalConstruction ModuleTemplate -> UniversalConstruction [prec 76] .
  -------------------------------------------------------------------------------------
  eq (forall MT exists MT' | UC) over MT'' = (forall MT exists MT' over MT'') | (UC over MT'') .
  eq (forall MT exists MT' ; UC) over MT'' = (forall MT exists MT' over MT'') ; (UC over MT'') .
  eq forall MT exists MT' over MT'' = forall (MT \ (( sorts none . ) \ MT'')) exists MT' .

  op univ_ : SubsortDeclSet -> UniversalConstruction [prec 75] .
  --------------------------------------------------------------
  eq univ SSDS = forall #extractParametersSSDS(SSDS) exists ( sorts none . ) SSDS .

  op _;_ : UniversalConstruction UniversalConstruction -> UniversalConstruction [ctor assoc prec 76 format(d n d d)] .
  op _|_ : UniversalConstruction UniversalConstruction -> UniversalConstruction [ctor assoc comm prec 77 format(d n d d)] .
  -------------------------------------------------------------------------------------------------------------------------
  eq UC | UC = UC .
  eq (UC | UC') ; UC''         = (UC ; UC'') | (UC' ; UC'') .
  eq         UC ; (UC' | UC'') = (UC ; UC')  | (UC  ; UC'') .

  op _<<_ : UniversalConstruction SubstitutionSet -> UniversalConstruction [right id: empty] .
  --------------------------------------------------------------------------------------------
  eq (forall MT exists MT') << SUB = forall (MT << SUB) exists (MT' << SUB) | forall MT exists MT' .
  eq UC << (SUB | SUB' | SUBS)     = (UC << SUB) | (UC << SUB') | (UC << SUBS) .
  eq (UC | UC') << SUB             = (UC << SUB) | (UC' << SUB) .
  eq (UC ; UC') << SUB             = (UC << SUB) ; (UC' << SUB) .
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
                                 ( subsort S < prime(S) . )
                          exists ( sorts none . )
                                 ( subsort S' < prime(S') . ) .

  op covariant-data-up : Sort Sort -> UniversalConstruction .
  -----------------------------------------------------------
  eq covariant-data-up(S, S') =   covariant(S, S')
                                ; univ ( subsorts S < S' . ) .

  op covariant-data-down : Sort Sort -> UniversalConstruction .
  -------------------------------------------------------------
  eq covariant-data-down(S, S') =   covariant(S, S')
                                  ; univ ( subsorts S' < S . ) .
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
  ceq covariant-data-binary(S, Op, AS) =   covariant-data-up(svar('X), NeS{svar('X)})
                                         ; covariant-data-up(NeS{svar('X)}, S{svar('X)})
                                         ; forall ( sorts svar('X) ; S{svar('X)} ; NeS{svar('X)} . )
                                                  ( subsorts svar('X) < NeS{svar('X)} < S{svar('X)} . )
                                           exists ( sorts none . )
                                                  ( op Nil : nil -> S{svar('X)} [ctor] .
                                                    op Op : (S{svar('X)})   (S{svar('X)}) ->   S{svar('X)} [ctor id(const(Nil, S{svar('X)})) AS] .
                                                    op Op : (S{svar('X)}) (NeS{svar('X)}) -> NeS{svar('X)} [ctor id(const(Nil, S{svar('X)})) AS] .
                                                  )
                                       if NeS := qid("Ne" + string(S))
                                       /\ Nil := qid("." + string(S)) .
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
             ; forall ( sorts 'NeSet{svar('X)} . )
               exists ( sorts none . )
                      ( eq '_;_[NES, NES] = NES [none] . )
           if NES := var('NeS, 'NeSet{svar('X)}) .
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
  eq signature-refinement(Q) =   covariant-data-down(svar('X), svar('X){Q})
                               ; signature-refinement(0, Q)
                               ; signature-refinement(1, Q)
                               ; signature-refinement(2, Q) .

  op signature-refinement : Nat Qid -> UniversalConstruction .
  ------------------------------------------------------------
  eq signature-refinement(0, Q) = forall ( sorts svar('X) ; svar('X){Q} . )
                                         ( op qvar('OP) : nil -> svar('X) [attrsetvar('AS)] . )
                                  exists ( sorts none . )
                                         ( op qvar('OP) : nil -> svar('X){Q} [attrsetvar('AS)] . ) .
  eq signature-refinement(1, Q) = ( forall ( sorts svar('X) ; svar('X){Q} ; svar('Y) ; svar('Y){Q}. )
                                           ( op qvar('OP) : svar('Y) -> svar('X) [attrsetvar('AS)] . )
                                    exists ( sorts none . )
                                           ( op qvar('OP) : svar('Y){Q} -> svar('X){Q} [attrsetvar('AS)] . )
                                  ) << ('X:Sort <- 'Y:Sort) .
  eq signature-refinement(2, Q) = ( forall ( sorts svar('X) ; svar('X){Q} ; svar('Y) ; svar('Y){Q} ; svar('Z) ; svar('Z){Q} . )
                                           ( op qvar('OP) : svar('Y) svar('Z) -> svar('X) [attrsetvar('AS)] . )
                                    exists ( sorts none . )
                                           ( op qvar('OP) : (svar('Y){Q}) (svar('Z){Q}) -> svar('X){Q} [attrsetvar('AS)] . )
                                  ) << (('X:Sort <- 'Y:Sort) | ('X:Sort <- 'Z:Sort) | ('Y:Sort <- 'Z:Sort) | ('Y:Sort <- 'X:Sort ; 'Z:Sort <- 'X:Sort)) .
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
  eq EXPONENTIAL =   ( forall ( sorts svar('X) ; svar('Y) . )
                       exists ( sorts svar('X) ==> svar('Y) . )
                              ( op '__ : (svar('X) ==> svar('Y)) svar('X) -> svar('Y) [none] . )
                     ) << ('X:Sort <- 'Y:Sort)
                   ; forall ( sorts svar('X) ==> svar('X) . )
                     exists ( sorts none . )
                            ( op 'id < svar('X) > : nil -> svar('X) ==> svar('X) [ctor] . )
                            ( eq '__[const('id < svar('X) >, svar('X) ==> svar('X)), var('X, svar('X))] = var('X, svar('X)) [none] . )
                   ; forall ( sorts svar('X) ; svar('Y) ; svar('Z) ; svar('X) ==> svar('Y) ; svar('X) ==> svar('Z) . )
                            ( subsort svar('Y) < svar('Z) . )
                     exists ( sorts none . )
                            ( subsort svar('X) ==> svar('Y) < svar('X) ==> svar('Z) . )
                   ; forall ( sorts svar('X) ; svar('Y) ; svar('W) ; svar('X) ==> svar('Y) ; svar('W) ==> svar('Y) . )
                            ( subsort svar('W) < svar('X) . )
                     exists ( sorts none . )
                            ( subsort svar('X) ==> svar('Y) < svar('W) ==> svar('Y) . )
                   ; forall ( sorts svar('X) ==> svar('Y) ; svar('Y) ==> svar('Z) ; svar('X) ==> svar('Z) . )
                     exists ( sorts none . )
                            ( op '_._ : (svar('Y) ==> svar('Z)) (svar('X) ==> svar('Y)) -> svar('X) ==> svar('Z) [none] .
                              op '_;_ : (svar('X) ==> svar('Y)) (svar('Y) ==> svar('Z)) -> svar('X) ==> svar('Z) [none] .
                            ) .
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

  op top-sorts : Sort -> ModuleTemplate .
  ---------------------------------------
  eq top-sorts(S) = (sorts S .) \ (sorts S ; prime(S) . subsort S < prime(S) .) .

  op DOWN-TERM : -> ModUniversalConstruction .
  --------------------------------------------
  eq DOWN-TERM < Q > =   exists ( protecting 'META-LEVEL .
                                  protecting Q .
                                )
                                ( sorts none . )
                       ; covariant-data-up(svar('X), svar('X) ?)
                       ; forall ( sorts svar('X) ; svar('X) ? . )
                                ( subsort svar('X) < svar('X) ? . )
                         exists ( sorts none . )
                                ( op 'downTermError < svar('X) > : nil   -> svar('X) ? [ctor] .
                                  op 'downTerm      < svar('X) > : 'Term -> svar('X) ? [none] .
                                  op 'wellFormed    < svar('X) > : 'Term -> 'Bool      [none] .
                                )
                                ( ceq 'downTerm   < svar('X) > [var('T, 'Term)] = var('X, svar('X)) if var('X, svar('X)) := 'downTerm[var('T, 'Term), const('downTermError < svar('X) >, svar('X) ?)] [none] .
                                  ceq 'wellFormed < svar('X) > [var('T, 'Term)] = 'true.Bool        if var('X, svar('X)) := 'downTerm < svar('X) > [var('T, 'Term)] [none] .
                                  eq  'wellFormed < svar('X) > [var('T, 'Term)] = 'false.Bool [owise] .
                                ) .
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
  vars MT MT' : ModuleTemplate . var Q : Qid . vars S S' : Sort . var SS : SortSet .

  op #upModule : ModuleExpression -> Module [memo] .
  --------------------------------------------------
  eq #upModule(ME) = upModule(ME, false) [owise] .

  op _deriving_ : ModuleExpression UniversalConstruction -> ModuleExpression [prec 80] .
  --------------------------------------------------------------------------------------
  eq #upModule(ME deriving UC) = #upModule(ME) deriving UC .

  op META-TERM : -> ModUniversalConstruction .
  --------------------------------------------
  eq META-TERM < Q > =   exists ( extending 'META-LEVEL . )
                                ( sorts none . )
                       ; forall ( sorts svar('X) . )
                         exists asTemplate(#upModule('META-TERM deriving ( covariant-data-down(svar('T), svar('T){Q})
                                                                         ; covariant(svar('T){Q}, svar('T){Q @ svar('X)})
                                                                         )
                                                    )
                                          )
                       ; forall ( sorts svar('X) ; svar('T){Q @ svar('X)}
                                      ; svar('Y) ; svar('T){Q @ svar('Y)} .
                                )
                                ( subsort svar('X) < svar('Y) . )
                         exists ( sorts none . )
                                ( subsort svar('T){Q @ svar('X)} < svar('T){Q @ svar('Y)} . )
                      ;  forall ( sorts svar('X) ; svar('T){Q @ svar('X)} ; svar('T){Q} . )
                              \ ( sorts svar('X) ; svar('T){Q @ svar('X)}
                                      ; svar('Y) ; svar('T){Q @ svar('Y)} .
                                )
                                ( subsort svar('X) < svar('Y) .
                                  subsort svar('T){Q @ svar('X)} < svar('T){Q @ svar('X)} .
                                )
                         exists ( sorts none . )
                                ( subsort svar('T){Q @ svar('X)} < svar('T){Q} . ) .

  op tmp-mb : Sort Sort Qid -> UniversalConstruction .
  ----------------------------------------------------
  eq tmp-mb(S, S', Q) = forall ( sorts S ; S ? ; S'{Q @ S} . )
                        exists ( sorts none . )
                               ( cmb-pred( S' , S'{Q @ S} , 'wellFormed < S > ) ) .

  op META-THEORY : -> ModUniversalConstruction .
  ----------------------------------------------
  eq META-THEORY < Q > =   ( DOWN-TERM | META-TERM < Q > )
                         ; tmp-mb( svar('X) , 'Constant   , Q )
                         ; tmp-mb( svar('X) , 'GroundTerm , Q )
                         ; tmp-mb( svar('X) , 'Variable   , Q )
                         ; tmp-mb( svar('X) , 'Term       , Q ) .

    vars M1 M2          : ModuleExpression .
    vars TM TM' TM1 TM2 : Variable .
    op PURIFICATION : ModuleExpression ModuleExpression -> UniversalConstruction .
    ------------------------------------------------------------------------------
    ceq PURIFICATION(M1, M2)
      =   META-THEORY < M1 >
        ; META-THEORY < M2 >
        ; exists ( extending 'FOFORM .
                   extending M1 .
                   extending M2 . )
                 ( sorts none . )
                 ( op 'purify : 'EqAtom -> 'EqConj [none] .
                   op 'fvar   : 'Term 'Term -> 'Variable [none] . )
        ; forall ( sorts 'Term ; 'Term{svar('M)} . )
                 ( subsort 'Term{svar('M)} < 'Term . )
          exists ( sorts none . )
                 ( eq 'purify['_?=_[TM, TM']] = '_?=_[TM, TM'] [none] . )
        ; forall ( sorts 'Term ; 'Term{svar('M1)} ; 'Term{svar('M2)} . )
                 ( subsorts 'Term{svar('M1)} ; 'Term{svar('M2)} < 'Term . )
          exists ( sorts none . )
                 ( eq 'purify['_?=_[TM1, TM2]] = '_/\_['_?=_['fvar[TM1, TM2], TM1], '_?=_['fvar[TM1, TM2], TM2]] [none] . )

      if TM  := var('TM,  'Term{svar('M)})
      /\ TM' := var('TM', 'Term{svar('M)})
      /\ TM1 := var('TM1, 'Term{svar('M1)})
      /\ TM2 := var('TM2, 'Term{svar('M2)}) .

  op _deriving_ : Module UniversalConstruction -> [Module] [prec 80] .
  --------------------------------------------------------------------
  ceq MOD deriving forall MT exists MT' = MOD ++ (MT' << SUBSTS) if SUBSTS := match MT with asTemplate(MOD) .
  eq  MOD deriving MUC                  = MOD deriving MUC < getName(MOD) > .
  eq  MOD deriving (UC ; UC')           = (MOD deriving UC) deriving UC' .
  eq  MOD deriving (UC | UC')           = (MOD deriving UC) ++ (MOD deriving UC') .
endfm
```
