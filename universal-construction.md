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

  var SUBSTS : SubstitutionSet . var MOD : Module . vars MT MT' : ModuleTemplate . vars FC FC' FC'' : UniversalConstruction .
  vars S S' NeS : Sort . vars SS : SortSet . vars Op Nil Q : Qid . var AS : AttrSet . var NES : Variable .
  vars SUB SUB' : Substitution . var SUBS : SubstitutionSet . vars NeMTS NeMTS' : NeModuleTemplateSet .

  op _<_> : ModUniversalConstruction Qid -> UniversalConstruction [ctor] .
  ------------------------------------------------------------------------

  op exists_        : ModuleTemplate                   -> UniversalConstruction [ctor prec 75] .
  op forall_exists_ : ModuleTemplateSet ModuleTemplate -> UniversalConstruction [ctor prec 75] .
  ----------------------------------------------------------------------------------------------
  eq exists MT                       = forall (sorts none .) exists MT .
  eq forall NeMTS | NeMTS' exists MT = forall NeMTS exists MT | forall NeMTS' exists MT .

  op _;_ : UniversalConstruction UniversalConstruction -> UniversalConstruction [ctor assoc prec 76 format(d n d d)] .
  op _|_ : UniversalConstruction UniversalConstruction -> UniversalConstruction [ctor assoc comm prec 77 format(d n d d)] .
  -------------------------------------------------------------------------------------------------------------------------
  eq FC | FC = FC .
  eq (FC | FC') ; FC''         = (FC ; FC'') | (FC' ; FC'') .
  eq         FC ; (FC' | FC'') = (FC ; FC')  | (FC  ; FC'') .

  op _<<_ : UniversalConstruction SubstitutionSet -> UniversalConstruction [right id: empty] .
  --------------------------------------------------------------------------------------------
  eq (forall MT exists MT') << SUB = forall (MT << SUB) exists (MT' << SUB) | forall MT exists MT' .
  eq FC << (SUB | SUB' | SUBS)     = (FC << SUB) | (FC << SUB') | (FC << SUBS) .
  eq (FC | FC') << SUB             = (FC << SUB) | (FC' << SUB) .
  eq (FC ; FC') << SUB             = (FC << SUB) ; (FC' << SUB) .
```

Covariant Data
--------------

Covariant data are data-structures that follow the normal
`subsorts X < NeData{X} < Data{X} .` pattern. The universal construction
`covariant-data` will build the sort-structure for you.

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

  op subsort : Sort Sort -> UniversalConstruction .
  -------------------------------------------------
  eq subsort(S, S') =   forall ( sorts S ; S' . )
                        exists ( sorts none . )
                               ( subsort S < S' . ) .

  op covariant-data : Sort Sort -> UniversalConstruction .
  --------------------------------------------------------
  eq covariant-data(S, S') = covariant(S, S') ; subsort(S, S') .

  op covariant-data-binary : Sort Qid AttrSet -> UniversalConstruction .
  ----------------------------------------------------------------------
  ceq covariant-data-binary(S, Op, AS) =   covariant-data(svar('X), NeS{svar('X)})
                                         ; covariant-data(NeS{svar('X)}, S{svar('X)})
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

The universal constructions for data-types `LIST` and `SET` are provided here.

```{.maude .univ}
  ops LIST SET : -> UniversalConstruction .
  -----------------------------------------
  eq LIST = covariant-data-binary('List, '_`,_, assoc) .
  ceq SET = ( covariant-data-binary('Set, '_;_, assoc comm)
            ; forall ( sorts 'NeSet{svar('X)} . )
              exists ( sorts none . )
                     ( eq '_;_[NES, NES] = NES [none] . )
            )
          if NES := var('NeS, 'NeSet{svar('X)}) .
```

Signature Refinement
--------------------

Signature refinements add subsorts to every sort (adding the annotation that
they are refined), as well as copying operators over only the refined sorts
down. Right now only operators up to arity 2 are handled (until we have a better
way to generate them).

```{.maude .univ}
  op sort-refinement : Qid -> UniversalConstruction .
  ---------------------------------------------------
  eq sort-refinement(Q) =   forall ( sorts svar('X) . )
                            exists ( sorts svar('X){Q} . )
                                   ( subsort svar('X){Q} < svar('X) . )
                          ; forall ( sorts svar('X) ; svar('X){Q}
                                         ; svar('Y) ; svar('Y){Q} . )
                                   ( subsort svar('X) < svar('Y) . )
                            exists ( sorts none . )
                                   ( subsort svar('X){Q} < svar('Y){Q} . ) .

  op signature-refinement : Qid -> UniversalConstruction .
  --------------------------------------------------------
  eq signature-refinement(Q) =   sort-refinement(Q)
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
--- fix arrow sorts, add qid construct for arrows
--- covariance/contravariance separately
--- subsorts arent what i think they are
--- do everything at double arrow level

  op EXPONENTIAL : -> UniversalConstruction .
  ----------------------------------------------
  eq EXPONENTIAL =   forall ( sorts svar('X) ; svar('Y) . )
                     exists ( sorts svar('X) ==> svar('Y) . )
                   ; forall ( sorts svar('X) ; svar('Y) ; svar('Z) ; svar('X) ==> svar('Y) ; svar('X) ==> svar('Z) . )
                            ( subsort svar('Y) < svar('Z) . )
                     exists ( sorts none . )
                            ( subsort svar('X) ==> svar('Y) < svar('X) ==> svar('Z) . )
                   ; forall ( sorts svar('X) ; svar('Y) ; svar('W) ; svar('X) ==> svar('Y) ; svar('W) ==> svar('Y) . )
                            ( subsort svar('W) < svar('X) . )
                     exists ( sorts none . )
                            ( subsort svar('X) ==> svar('Y) < svar('W) ==> svar('Y) . )
                   ; forall ( sorts svar('X) ; svar('Y) ; svar('X) ==> svar('Y) ; svar('Y) ==> svar('Z) . )
                            ( op qvar('OP1) : svar('X) -> svar('Y) [none] .
                              op qvar('OP2) : svar('Y) -> svar('Z) [none] . )
                     exists ( sorts svar('X) ==> svar('Z) . )
                            ( op qvar('OP12) : svar('X) -> svar('Z) [none] . ) .
endfm
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
  vars FC FC' : UniversalConstruction . var MFC : ModUniversalConstruction .
  vars MT MT' : ModuleTemplate . var Q : Qid . vars S S' : Sort . var SS : SortSet .

  op #upModule : ModuleExpression -> Module [memo] .
  --------------------------------------------------
  eq #upModule(ME) = upModule(ME, false) [owise] .

  op _deriving_ : ModuleExpression UniversalConstruction -> ModuleExpression [prec 80] .
  --------------------------------------------------------------------------------------
  eq #upModule(ME deriving FC) = #upModule(ME) deriving FC .

  op top-sorts : Sort -> ModuleTemplate .
  ---------------------------------------
  eq top-sorts(S) = (sorts S .) \ (sorts S ; svar('##SOMEOTHERSORT##) . subsort S < svar('##SOMEOTHERSORT##) .) .

  op DOWN-TERM : -> UniversalConstruction .
  ---------------------------------------------
  eq DOWN-TERM =   exists ( extending 'META-LEVEL . )
                          ( sorts none . )
                 ; forall ( sorts svar('X) . )
                   exists ( sorts svar('X) ? . )
                          ( subsort svar('X) < svar('X) ? . )
                          ( op 'downTerm < svar('X) > : 'Term -> svar('X) ? [none] .
                            op 'wellFormed < svar('X) > : 'Term -> 'Bool [none] .
                          )
                          ( ceq 'downTerm < svar('X) > [var('T, 'Term)] = var('X, svar('X)) if var('X, svar('X)) := 'downTerm[var('T, 'Term), 'downTerm < svar('X) > [var('T, 'Term)]] [none] .
                            ceq 'wellFormed < svar('X) > [var('T, 'Term)] = 'true.Bool if var('X, svar('X)) := 'downTerm < svar('X) > [var('T, 'Term)] [none] .
                            eq  'wellFormed < svar('X) > [var('T, 'Term)] = 'false.Bool [owise] .
                          )
                 ; forall ( sorts svar('X) ; svar('X) ?
                                ; svar('Y) ; svar('Y) ? . )
                          ( subsort svar('X) < svar('Y) . )
                   exists ( sorts none . )
                          ( subsort svar('X) ? < svar('Y) ? . ) .

  op META-TERM : -> ModUniversalConstruction .
  --------------------------------------------
  eq META-TERM < Q > =   exists ( extending 'META-LEVEL . )
                                ( sorts none . )
                       ; forall ( sorts svar('X) . )
                         exists ( sorts 'Constant{Q @ svar('X)} ; 'Variable{Q @ svar('X)} ; 'GroundTerm{Q @ svar('X)} ; 'Term{Q @ svar('X)}
                                      ; 'Constant{Q}            ; 'Variable{Q}            ; 'GroundTerm{Q}            ; 'Term{Q} . )
                                ( subsorts 'Constant{Q} < 'GroundTerm{Q} < 'Term{Q} .
                                  subsort 'Variable{Q} < 'Term{Q} . )
                       ; forall ( sorts svar('X) ; svar('T){Q @ svar('X)}
                                      ; svar('Y) ; svar('T){Q @ svar('Y)} . )
                                ( subsort svar('X) < svar('Y) . )
                         exists ( sorts none . )
                                ( subsort svar('T){Q @ svar('X)} < svar('T){Q @ svar('Y)} . )
                       ; forall top-sorts(svar('T){Q @ svar('X)})
                         exists ( sorts none . )
                                ( subsorts svar('T){Q @ svar('X)} < svar('T){Q} < svar('T) . )
                       ; forall ( sorts svar('T1){Q} ; svar('T1){Q @ svar('X)}
                                      ; svar('T2){Q} ; svar('T2){Q @ svar('X)} . )
                                ( subsort svar('T1){Q} < svar('T2){Q} . )
                         exists ( sorts none . )
                                ( subsort svar('T1){Q @ svar('X)} < svar('T2){Q @ svar('X)} . ) .

  op cmb-pred : Sort Sort Qid -> MembAx .
  ---------------------------------------
  eq cmb-pred(S, S', Q) = ( cmb var('X, S) : S' if Q[var('X, S)] = 'true.Bool [none] . ) .

  op META-THEORY : -> ModUniversalConstruction .
  ----------------------------------------------
  eq META-THEORY < Q > =   ( DOWN-TERM | META-TERM )
                         ; forall ( sorts svar('X) ; svar('X) ? ; svar('T){Q @ svar('X)} ; svar('T){Q} . )
                           exists ( sorts none . )
                                  ( cmb-pred( svar('T) , svar('T){Q @ svar('X)} , 'wellFormed < svar('X) > ) ) .


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
  eq  MOD deriving MFC                  = MOD deriving MFC < getName(MOD) > .
  eq  MOD deriving (FC ; FC')           = (MOD deriving FC) deriving FC' .
  eq  MOD deriving (FC | FC')           = (MOD deriving FC) ++ (MOD deriving FC') .
endfm
```
