Module Templates
================

First, we'll need a way to generate variables at the object level because
writing all our syntax at the meta-level can be a pain. Additionally, we'll need
a way to have "structured" sort names and operator names. For this, a few
constructors are provided.

```{.maude .module-exp}
fmod STRUCTURED-QID is
  extending META-LEVEL .

  vars Q Q' : Qid . var S : Sort . var SS : SortSet . var SSDS : SubsortDeclSet . var AS : AttrSet .
  var OPDS : OpDeclSet . var MAS : MembAxSet . var EQS : EquationSet . var RLS : RuleSet . var IL : ImportList .

  op _<_> : Qid  TypeList -> Qid  [prec 23] .
  op _<_> : Sort TypeList -> Sort [prec 23] .
  op var : Qid Sort -> Variable .
  op _._ : Qid Sort -> Constant [prec 24] .
  -----------------------------------------

  op downQidError?        : -> [Qid] .
  op downImportListError? : -> [ImportList] .
  op downSortsError?      : -> [SortSet] .
  op downSubsortsError?   : -> [SubsortDeclSet] .
  op downAttrSetError?    : -> [AttrSet] .
  op downOpSetError?      : -> [OpDeclSet] .
  op downMembAxSetError?  : -> [MembAxSet] .
  op downEqSetError?      : -> [EquationSet] .
  op downRuleSetError?    : -> [RuleSet] .
  -------------------------------------------

  op qvar          : Qid -> Qid .
  op importlistvar : Qid -> ImportList .
  op svar          : Qid -> Sort .
  op ssetvar       : Qid -> SortSet .
  op subsvar       : Qid -> SubsortDeclSet .
  op attrsetvar    : Qid -> AttrSet .
  op opsetvar      : Qid -> OpDeclSet .
  op membaxsetvar  : Qid -> MembAxSet .
  op eqsetvar      : Qid -> EquationSet .
  op rulesetvar    : Qid -> RuleSet .
  -----------------------------------
  ceq qvar(Q)          = Q'   if Q'   := downTerm(qid(string(Q) + ":Qid"),            downQidError?) .
  ceq importlistvar(Q) = IL   if IL   := downTerm(qid(string(Q) + ":ImportList"),     downImportListError?) .
  ceq svar(Q)          = S    if S    := downTerm(qid(string(Q) + ":Sort"),           downSortsError?) .
  ceq ssetvar(Q)       = SS   if SS   := downTerm(qid(string(Q) + ":SortSet"),        downSortsError?) .
  ceq subsvar(Q)       = SSDS if SSDS := downTerm(qid(string(Q) + ":SubsortDeclSet"), downSubsortsError?) .
  ceq attrsetvar(Q)    = AS   if AS   := downTerm(qid(string(Q) + ":AttrSet"),        downAttrSetError?) .
  ceq opsetvar(Q)      = OPDS if OPDS := downTerm(qid(string(Q) + ":OpDeclSet"),      downOpSetError?) .
  ceq membaxsetvar(Q)  = MAS  if MAS  := downTerm(qid(string(Q) + ":MembAxSet"),      downMembAxSetError?) .
  ceq eqsetvar(Q)      = EQS  if EQS  := downTerm(qid(string(Q) + ":EquationSet"),    downEqSetError?) .
  ceq rulesetvar(Q)    = RLS  if RLS  := downTerm(qid(string(Q) + ":RuleSet"),        downRuleSetError?) .
endfm
```

Module templates serve as more flexible module data-structures than what the
`META-LEVEL` provides for modules. The main functionality exported is:

-   `_++_ : ModuleTemplate ModuleTemplate -> ModuleTemplate` and
    `_++_ : Module ModuleTemplate -> Module` will respectively union together
    two module templates and add the data in a module template into a module.

-   `asTemplate : Module -> ModuleTemplate` and
    `fromTemplate : ModuleTemplate -> Module` provide functions between the
    normal Maude modules and the module templates defined here.

-   `match_with_ : ModuleTemplate ModuleTemplate -> SubstitutionSet` will extend
    the first module template by padding it with variables in all the "sensible"
    places, then call `metaMatch` on the result to the second module. This
    achieves "matching with extension" over module templates.

-   `_<<_ : ModuleTemplate SubstitutionSet -> ModuleTemplate`: This will apply
    each substitution to the module template and union together the resulting
    module templates.

```{.maude .module-exp}
load cterm.maude

fmod MODULE-TEMPLATE is
  protecting STRUCTURED-QID .
  protecting CTERM-SET .

  sorts SortTemplate SubsortTemplate OpTemplate MembAxTemplate EqTemplate RuleTemplate ModuleTemplate .
  subsort SortTemplate < SubsortTemplate < OpTemplate < MembAxTemplate < EqTemplate < RuleTemplate < ModuleTemplate .

  vars H H' : Header . vars IL IL' : ImportList . var S : Sort . vars SS SS' : SortSet . vars SSDS SSDS' : SubsortDeclSet .
  vars OPDS OPDS' : OpDeclSet . vars MAS MAS' : MembAxSet . vars EQS EQS' : EquationSet . vars RLS RLS' : RuleSet .
  var AS : AttrSet . var EQC : EqCondition . var C : Condition . vars MT MT' : ModuleTemplate .
  var MOD : Module . var Q : Qid . var TL : TypeList . var TYPE : Type . vars T T' : Term .
  vars SU SU' : Substitution . var SUBSTS : SubstitutionSet .

  op (sorts_.) : SortSet -> SortTemplate [format(d d d d) prec 60] .
  op __ : SortTemplate    SubsortDeclSet -> SubsortTemplate [right id: none format(d ni d) prec 61] .
  op __ : SubsortTemplate OpDeclSet      -> OpTemplate      [right id: none format(d ni d) prec 62] .
  op __ : OpTemplate      MembAxSet      -> MembAxTemplate  [right id: none format(d ni d) prec 63] .
  op __ : MembAxTemplate  EquationSet    -> EqTemplate      [right id: none format(d ni d) prec 64] .
  op __ : EqTemplate      RuleSet        -> RuleTemplate    [right id: none format(d ni d) prec 65] .
  op __ : ImportList      RuleTemplate   -> ModuleTemplate  [left  id: nil  format(d ni d) prec 66] .
  ---------------------------------------------------------------------------------------------------

  op _++_ : ModuleTemplate ModuleTemplate -> ModuleTemplate [assoc comm prec 72] .
  --------------------------------------------------------------------------------
  eq (IL sorts SS . SSDS OPDS MAS EQS RLS) ++ (IL' sorts SS' . SSDS' OPDS' MAS' EQS' RLS')
   = (IL IL') (sorts SS ; SS' .) (SSDS SSDS') (OPDS OPDS') (MAS MAS') (EQS EQS') (RLS RLS') .

  op _++_ : Module ModuleTemplate -> Module [prec 72] .
  -----------------------------------------------------
  eq MOD ++ MT = fromTemplate(getName(MOD), asTemplate(MOD) ++ MT) .

  op asTemplate : Module -> [ModuleTemplate] .
  --------------------------------------------
  eq asTemplate(fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) = (IL sorts SS . SSDS OPDS MAS EQS) .
  eq asTemplate( mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  = (IL sorts SS . SSDS OPDS MAS EQS RLS) .

  op fromTemplate : Header ModuleTemplate -> [Module] .
  -----------------------------------------------------
  eq fromTemplate(H, IL sorts SS . SSDS OPDS MAS EQS)     = (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) .
  eq fromTemplate(H, IL sorts SS . SSDS OPDS MAS EQS RLS) = (mod  H is IL sorts SS . SSDS OPDS MAS EQS RLS endm) .

  op match_with_ : ModuleTemplate ModuleTemplate -> [SubstitutionSet] .
  ---------------------------------------------------------------------
  ceq match MT with MT' = SUBSTS if SUBSTS := #subsumesWith(upModule('MODULE-TEMPLATE, true), upTerm(#varExtendTemplate(MT)), upTerm(MT')) .

  op moduleTemplateError? : -> [ModuleTemplate] .
  op _<<_ : ModuleTemplate SubstitutionSet -> ModuleTemplate .
  ------------------------------------------------------------
  ceq MT << SU                  = MT' if MT' := downTerm(upTerm(MT) << SU, moduleTemplateError?) .
  eq  MT << empty               = (sorts none .) .
  eq  MT << (SU | SU' | SUBSTS) = (MT << SU) ++ (MT << SU') ++ (MT << SUBSTS) .

  op #varExtendTemplate : ModuleTemplate -> [ModuleTemplate] .
  ------------------------------------------------------------
  eq #varExtendTemplate(IL sorts SS . SSDS OPDS MAS EQS RLS) = ( (IL                      importlistvar('##MTCTXILIST##))
                                                                 (sorts SS ;              ssetvar('##MTMTXSORTS##) .)
                                                                 (SSDS                    subsvar('##MTCTXSUBSORT##))
                                                                 (#varExtendOpDecls(OPDS) opsetvar('##MTCTXOPSET##))
                                                                 (#varExtendMembAxs(MAS)  membaxsetvar('##MTCTXMEMBAXSET##))
                                                                 (#varExtendEqs(EQS)      eqsetvar('##MTCTXEQSET##))
                                                                 (#varExtendRules(RLS)    rulesetvar('##MTCTXRULESET##))
                                                               ) .

  --- TODO: All of these variables need to be made actually fresh.

  op #varExtendOpDecls : OpDeclSet -> [OpDeclSet] .
  -------------------------------------------------
  eq #varExtendOpDecls(none) = none .
  eq #varExtendOpDecls(op Q : TL -> TYPE [AS] .) = (op Q : TL -> TYPE [AS attrsetvar('##MTCTXATTRSET##)] .) .

  op #varExtendMembAxs : MembAxSet -> [MembAxSet] .
  -------------------------------------------------
  eq #varExtendMembAxs(none) = none .
  eq #varExtendMembAxs( mb T : S        [AS] .) = ( mb T : S        [AS attrsetvar('##MTCTXATTRSET##)] .) .
  eq #varExtendMembAxs(cmb T : S if EQC [AS] .) = (cmb T : S if EQC [AS attrsetvar('##MTCTXATTRSET##)] .) .

  op #varExtendEqs : EquationSet -> [EquationSet] .
  -------------------------------------------------
  eq #varExtendEqs(none) = none .
  eq #varExtendEqs( eq T = T'        [AS] .) = ( eq T = T'        [AS attrsetvar('##MTCTXATTRSE##)] .) .
  eq #varExtendEqs(ceq T = T' if EQC [AS] .) = (ceq T = T' if EQC [AS attrsetvar('##MTCTXATTRSE##)] .) .

  op #varExtendRules : RuleSet -> [RuleSet] .
  -------------------------------------------
  eq #varExtendRules(none) = none .
  eq #varExtendRules( rl T => T'      [AS] .) = ( rl T => T'      [AS attrsetvar('##MTCTXATTRSE##)] .) .
  eq #varExtendRules(crl T => T' if C [AS] .) = (crl T => T' if C [AS attrsetvar('##MTCTXATTRSE##)] .) .
endfm
```

Free Constructions
==================

Free constructions are a pair of a theory `FTH` and a parametized module
`FMOD{X :: FTH}` such that deciding if some module `MOD` has a view from `FTH`
can be done purely with matching. If so, then the resulting substitution is used
to instantiate `FMOD{X :: FTH}`, and the resulting module is
`MOD + FMOD{X :: FTH}`. For this, we'll heavily use the machinery of
`MODULE-TEMPLATE`.

```{.maude .module-exp}
fmod FREE-CONSTRUCTION is
  protecting MODULE-TEMPLATE .

  sorts FreeConstruction ModFreeConstruction .
  subsort ModFreeConstruction < FreeConstruction .

  var SUBSTS : SubstitutionSet . var MOD : Module . vars MT MT' : ModuleTemplate .
  vars S NeS : Sort . vars Op Nil Q : Qid . var AS : AttrSet . var NES : Variable .

  op _<_> : ModFreeConstruction Qid -> FreeConstruction [ctor] .
  --------------------------------------------------------------

  op _;_ : FreeConstruction FreeConstruction -> FreeConstruction [ctor assoc prec 76 format(d n d d)] .
  -----------------------------------------------------------------------------------------------------

  op forall_exists_ : ModuleTemplate ModuleTemplate -> FreeConstruction [ctor prec 75 format(d n++i n ni-- d)] .
  --------------------------------------------------------------------------------------------------------------
```

Covariant Data
--------------

Covariant data are data-structures that follow the normal
`subsorts X < NeData{X} < Data{X} .` pattern. The free construction
`covariant-data` will build the sort-structure for you.

```{.maude .module-exp}
  op covariant-data : Sort -> FreeConstruction .
  ----------------------------------------------
  ceq covariant-data(S) = ( forall sorts svar('X) .
                            exists ( sorts S < svar('X) > ; NeS < svar('X) > . )
                                   ( subsort       svar('X)   < NeS < svar('X) > .
                                     subsort NeS < svar('X) > <   S < svar('X) > .
                                   )
                          ; forall ( sorts svar('X) ; S < svar('X) > ; NeS < svar('X) >
                                         ; svar('Y) ; S < svar('Y) > ; NeS < svar('Y) > .
                                   )
                                   ( subsort svar('X) < svar('Y) . )
                            exists ( sorts none . )
                                   ( subsort   S < svar('X) > <   S < svar('Y) > .
                                     subsort NeS < svar('X) > < NeS < svar('Y) > .
                                   )
                          )
                        if NeS := qid("Ne" + string(S)) .

  op covariant-data-binary : Sort Qid AttrSet -> FreeConstruction .
  -----------------------------------------------------------------
  ceq covariant-data-binary(S, Op, AS) = ( covariant-data(S)
                                         ; forall ( sorts svar('X) ; S < svar('X) > ; NeS < svar('X) > . )
                                                  ( subsort       svar('X)   < NeS < svar('X) > .
                                                    subsort NeS < svar('X) > <   S < svar('X) > .
                                                  )
                                           exists ( sorts none . )
                                                  ( op Nil : nil -> S < svar('X) > [ctor] .
                                                    op Op : S < svar('X) >   S < svar('X) > ->   S < svar('X) > [ctor id(Nil . S < svar('X) >) AS] .
                                                    op Op : S < svar('X) > NeS < svar('X) > -> NeS < svar('X) > [ctor id(Nil . S < svar('X) >) AS] .
                                                  )
                                         )
                                       if NeS := qid("Ne" + string(S))
                                       /\ Nil := qid("." + string(S)) < svar('X) > .
```

The free constructions for data-types `List` and `Set` are provided here.

```{.maude .module-exp}
  ops LIST SET : -> FreeConstruction .
  ------------------------------------
  eq LIST = covariant-data-binary('List, '_`,_, assoc) .
  ceq SET = ( covariant-data-binary('Set, '_;_, assoc comm)
            ; forall ( sorts 'NeSet < svar('X) > . )
              exists ( sorts none . )
                     ( eq '_;_[NES, NES] = NES [none] . )
            )
          if NES := var('NeS < svar('X) >, 'NeSet < svar('X) >) .
```

Meta Level
----------

Sometimes you want a "meta theory" specific to your module. For example, you may
want to express using just a sort that a meta-level `Term` is a well-formed term
in your theory, or that it is a well-formed term of a specific sort in your
theory. This free construction will extend your module with its meta-theory, so
that this can be done.

```{.maude .module-exp}
  vars SMOD SMODX : Sort . vars T TMOD TMODX : Term . var CMOD : Constant .

  op MetaLevel : -> ModFreeConstruction .
  ---------------------------------------
  ceq MetaLevel < Q > = forall ( sorts svar('X) . )
                        exists ( extending 'META-LEVEL . )
                               ( sorts SMOD ; SMODX . )
                               ( subsort SMOD < 'Term .
                                 subsort SMODX < SMOD .
                               )
                               ( cmb T    : SMOD  if 'true.Bool = 'wellFormed['upModule[upTerm(CMOD), 'true.Bool], upTerm(T)] [none] .
                                 cmb TMOD : SMODX if 'true.Bool = 'sortLeq['upModule[upTerm(CMOD), 'true.Bool], 'leastSort['upModule[upTerm(CMOD), 'true.Bool], upTerm(TMOD)], svar('X) . 'Sort] [none] .
                               )
                      if CMOD  := Q . 'Qid
                      /\ SMOD  := 'Term < Q >
                      /\ SMODX := 'Term < Q svar('X) >
                      /\ T     := var('T, 'Term)
                      /\ TMOD  := var( 'T < SMOD >,  SMOD)
                      /\ TMODX := var('TM < SMODX >, SMODX) .
endfm
```

Module Expressions
==================

This module simply provides the hookup to our extension of the Meta-Level module
expressions. A memo-ised version of `upModule` is provided too for the
extensions. In addition, free constructions are provided. Free constructions
provide a module template with variables to determine anonymous views, and a
second module template to determine the associated parameterized module.

```{.maude .module-exp}
fmod MODULE-EXPRESSION is
  protecting FREE-CONSTRUCTION .

  sort ModuleConstruction .
  subsort ModuleExpression < ModuleConstruction .

  var MOD : Module . var ME : ModuleExpression . var SUBSTS : SubstitutionSet .
  var MC : ModuleConstruction . vars FC FC' : FreeConstruction . var MFC : ModFreeConstruction .
  vars MT MT' : ModuleTemplate .

  op #upModule : ModuleConstruction -> Module [memo] .
  ----------------------------------------------------
  eq #upModule(ME) = upModule(ME, true) .

  op _deriving_ : ModuleConstruction FreeConstruction -> ModuleConstruction [prec 80] .
  -------------------------------------------------------------------------------------
  eq #upModule((MC deriving FC)) = #upModule(MC) deriving FC .

  op _deriving_ : Module FreeConstruction -> [Module] [prec 80] .
  ---------------------------------------------------------------
  eq  MOD deriving (FC ; FC')           = (MOD deriving FC) deriving FC' .
  eq  MOD deriving MFC                  = MOD deriving MFC < getName(MOD) > .
  ceq MOD deriving forall MT exists MT' = MOD ++ (MT' << SUBSTS) if SUBSTS := match MT with asTemplate(MOD) .
endfm
```
