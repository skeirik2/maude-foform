Universal Constructions
=======================

Universal constructions are a pair of a theory `FTH` and a parametized module
`FMOD{X :: FTH}` such that deciding if some module `MOD` has a view from `FTH`
can be done purely with matching. If so, then the resulting substitution is used
to instantiate `FMOD{X :: FTH}`, and the resulting module is
`MOD + FMOD{X :: FTH}`. For this, we'll heavily use the machinery of
`MODULE-TEMPLATE`.

```{.maude .module-exp}
load mod-template.maude

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

```{.maude .module-exp}
  op covariant-data : Sort -> UniversalConstruction .
  ---------------------------------------------------
  ceq covariant-data(S) =   forall sorts svar('X) .
                            exists ( sorts S{svar('X)} ; NeS{svar('X)} . )
                                   ( subsorts svar('X) < NeS{svar('X)} < S{svar('X)} . )
                          ; forall ( sorts svar('X) ; S{svar('X)} ; NeS{svar('X)}
                                         ; svar('Y) ; S{svar('Y)} ; NeS{svar('Y)} .
                                   )
                                   ( subsort svar('X) < svar('Y) . )
                            exists ( sorts none . )
                                   ( subsort   S{svar('X)} <   S{svar('Y)} .
                                     subsort NeS{svar('X)} < NeS{svar('Y)} .
                                   )
                        if NeS := qid("Ne" + string(S)) .

  op covariant-data-binary : Sort Qid AttrSet -> UniversalConstruction .
  ----------------------------------------------------------------------
  ceq covariant-data-binary(S, Op, AS) =   covariant-data(S)
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

```{.maude .module-exp}
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

```{.maude .module-exp}
  op sort-refinement : Qid -> UniversalConstruction .
  ---------------------------------------------------
  eq sort-refinement(Q) =   forall ( sorts svar('X) . )
                            exists ( sorts svar('X){Q} . )
                                   ( subsort svar('X){Q} < svar('X) . )
                          ; forall ( sorts svar('X) ; svar('Y) ; svar('X){Q} ; svar('Y){Q} . )
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

```{.maude .module-exp}
fmod MODULE-EXPRESSION is
  extending UNIVERSAL-CONSTRUCTION .

  var MOD : Module . var ME : ModuleExpression . var SUBSTS : SubstitutionSet .
  vars FC FC' : UniversalConstruction . var MFC : ModUniversalConstruction .
  vars MT MT' : ModuleTemplate . var Q : Qid .

  op #upModule : ModuleExpression -> Module [memo] .
  --------------------------------------------------
  eq #upModule(ME) = upModule(ME, false) [owise] .

  op _deriving_ : ModuleExpression UniversalConstruction -> ModuleExpression [prec 80] .
  --------------------------------------------------------------------------------------
  eq #upModule(ME deriving FC) = #upModule(ME) deriving FC .

  op META-THEORY : -> ModUniversalConstruction .
  ----------------------------------------------
  eq META-THEORY < Q > =   exists ( extending 'META-LEVEL . )
                                  ( sorts none . )
                         ; exists asTemplate(#upModule('META-TERM deriving sort-refinement(Q)))
                         ; forall ( sorts 'Constant   ; 'Constant{svar('MOD)}
                                        ; 'Variable   ; 'Variable{svar('MOD)}
                                        ; 'GroundTerm ; 'GroundTerm{svar('MOD)}
                                        ; 'Term       ; 'Term{svar('MOD)} .
                                  )
                           exists ( sorts none . )
                                  ( cmb 'C:Constant    : 'Constant{svar('MOD)}   if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'C:Constant]    = 'true.Bool [none] .
                                    cmb 'V:Variable    : 'Variable{svar('MOD)}   if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'V:Variable]    = 'true.Bool [none] .
                                    cmb 'GT:GroundTerm : 'GroundTerm{svar('MOD)} if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'GT:GroundTerm] = 'true.Bool [none] .
                                    cmb 'T:Term        : 'Term{svar('MOD)}       if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'T:Term]        = 'true.Bool [none] .
                                  ) .

  op _deriving_ : Module UniversalConstruction -> [Module] [prec 80] .
  --------------------------------------------------------------------
  ceq MOD deriving forall MT exists MT' = MOD ++ (MT' << SUBSTS) if SUBSTS := match MT with asTemplate(MOD) .
  eq  MOD deriving MFC                  = MOD deriving MFC < getName(MOD) > .
  eq  MOD deriving (FC ; FC')           = (MOD deriving FC) deriving FC' .
  eq  MOD deriving (FC | FC')           = (MOD deriving FC) ++ (MOD deriving FC') .
endfm
```
