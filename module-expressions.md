Structured Sorts
================

First we need structured sorts (sorts that have meaning in how they're built).
Maude's built-in structured sorts (eg. `List{X}`) don't have enough flexibility.
For example, they can't handle multiple levels of nesting (eg. `List{Set{X}}`).

This module still needs `#parseSort` so that it can go from the unstructured
sorts of Maude to these structured sorts.

Eventually we should remove the dependency on `cterm` by moving `#subsumesWith`
and `#subsumesXWith` away from that module.

```{.maude .module-exp}
fmod STRUCTURED-QID is
  extending META-LEVEL .

  var Q : Qid . var V : Variable . var QL : QidList . vars NeQL NeQL' : NeQidList . 

  op _<_> : Qid QidList -> Qid [prec 23] .
  ----------------------------------------

  op #unparseQid : Qid -> String .
  --------------------------------
  eq  #unparseQid(Q < QL >) = #unparseQid(Q) + "{" + #unparseQids(QL) + "}" .
  ceq #unparseQid(Q)        = string(V) if V := upTerm(Q) .
  eq  #unparseQid(Q)        = string(Q) [owise] .

  op #unparseQids : QidList -> String .
  -------------------------------------
  eq #unparseQids(none)         = "" .
  eq #unparseQids(Q)            = #unparseQid(Q) .
  eq #unparseQids(NeQL ; NeQL') = #unparseQids(NeQL) + ";" + #unparseQids(NeQL') .
endfm
```

Module Templates
================

Module templates serve as "anonymous views". If the template matches, then the
substitutions generated serve as the `view` from the template to the module. The
`match_with_` function is provided, which will extend a module template in the
appropriate ways to match as generally as possible (a sort of custom "matching
with extension").

Instantiation of a module template is done the same way as variable
substitution. The operator `_<<_` is lifted over module templates.

```{.maude .module-exp}
load cterm.maude

fmod MODULE-TEMPLATE is
  protecting STRUCTURED-QID .
  protecting META-LEVEL .
  protecting CTERM-SET .

  sorts SortTemplate ModuleTemplate .
  subsort SortTemplate < ModuleTemplate .

  vars MT MT' : ModuleTemplate . var Q : Qid . vars SU SU' : Substitution . var SUBSTS : SubstitutionSet .
  var H : Header . var IL : ImportList . var S : Sort . vars SS SS' : SortSet . vars SSDS SSDS' : SubsortDeclSet .
  vars OPDS OPDS' : OpDeclSet . var MAS : MembAxSet . var EQS : EquationSet . var RLS : RuleSet .
  var TL : TypeList . var T : Type . var AS : AttrSet .

  op sorts_._ : SortSet SubsortDeclSet -> SortTemplate [format(d d d n d)] .
  op __ : SortTemplate OpDeclSet -> ModuleTemplate [right id: none format(d ni d)] .
  ----------------------------------------------------------------------------------

  op downSortsError?    : -> [SortSet] .
  op downSubsortsError? : -> [SubsortDeclSet] .
  op downAttrSetError? : -> [AttrSet] .
  op downOpSetError? : -> [OpDeclSet] .
  op svar    : Qid -> Sort .
  op ssetvar : Qid -> SortSet .
  op subsvar : Qid -> SubsortDeclSet .
  op attrsetvar : Qid -> AttrSet .
  op opsetvar : Qid -> OpDeclSet .
  --------------------------------
  ceq svar(Q)       = S    if S    := downTerm(qid(string(Q) + ":Sort"),           downSortsError?) .
  ceq ssetvar(Q)    = SS   if SS   := downTerm(qid(string(Q) + ":SortSet"),        downSortsError?) .
  ceq subsvar(Q)    = SSDS if SSDS := downTerm(qid(string(Q) + ":SubsortDeclSet"), downSubsortsError?) .
  ceq attrsetvar(Q) = AS   if AS   := downTerm(qid(string(Q) + ":AttrSet"),        downAttrSetError?) .
  ceq opsetvar(Q)   = OPDS if OPDS := downTerm(qid(string(Q) + ":OpDeclSet"),      downOpSetError?) .

  op match_with_ : ModuleTemplate ModuleTemplate -> [SubstitutionSet] .
  ---------------------------------------------------------------------
  ceq match MT with MT' = SUBSTS if SUBSTS := #subsumesWith(upModule('MODULE-TEMPLATE, true), upTerm(#varExtendTemplate(MT)), upTerm(MT')) .

  op _++_ : ModuleTemplate ModuleTemplate -> ModuleTemplate [assoc comm] .
  ------------------------------------------------------------------------
  eq (sorts SS . SSDS OPDS) ++ (sorts SS' . SSDS' OPDS') = sorts SS ; SS' . SSDS SSDS' (OPDS OPDS') .

  op _++_ : Module ModuleTemplate -> [Module] .
  ---------------------------------------------
  eq (fmod H is IL sorts SS .       SSDS       OPDS       MAS EQS     endfm) ++ (sorts SS' . SSDS' OPDS')
   = (fmod H is IL sorts SS ; SS' . SSDS SSDS' OPDS OPDS' MAS EQS     endfm) .
  eq (mod  H is IL sorts SS .       SSDS       OPDS       MAS EQS RLS endm)  ++ (sorts SS' . SSDS' OPDS')
   = (mod  H is IL sorts SS ; SS' . SSDS SSDS' OPDS OPDS' MAS EQS RLS endm) .

  op moduleTemplateError? : -> [ModuleTemplate] .
  op _<<_ : ModuleTemplate SubstitutionSet -> ModuleTemplate .
  ------------------------------------------------------------
  ceq MT << SU                  = MT' if MT' := downTerm(upTerm(MT) << SU, moduleTemplateError?) .
  eq  MT << empty               = sorts none . none .
  eq  MT << (SU | SU' | SUBSTS) = (MT << SU) ++ (MT << SU') ++ (MT << SUBSTS) .

  op #varExtendTemplate : ModuleTemplate -> ModuleTemplate .
  ----------------------------------------------------------
  eq #varExtendTemplate(sorts SS . SSDS OPDS) = ( sorts SS ; ssetvar('##MTMTXSORTS##) .
                                                  SSDS subsvar('##MTCTXSUBSORT##)
                                                  (#varExtendOpDecls(OPDS) opsetvar('##MTCTXOPSET##))
                                                ) .

  op #varExtendOpDecls : OpDeclSet -> OpDeclSet .
  -----------------------------------------------
  eq #varExtendOpDecls(none) = none .
  eq #varExtendOpDecls(op Q : TL -> T [AS] .) = (op Q : TL -> T [AS attrsetvar('##MTCTXATTRSET##)] .) .

  op #mkTemplate : Module -> [ModuleTemplate] .
  ---------------------------------------------
  eq #mkTemplate(fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) = sorts SS . SSDS OPDS .
  eq #mkTemplate(mod  H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  = sorts SS . SSDS OPDS .
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
  protecting MODULE-TEMPLATE .

  sorts ModuleConstruction FreeConstruction .
  subsort ModuleExpression < ModuleConstruction .

  var ME : ModuleExpression . var MC : ModuleConstruction . vars FC FC' : FreeConstruction .
  var SUBSTS : SubstitutionSet . var MOD : Module . vars MT MT' : ModuleTemplate .
  vars S NeS : Sort . vars Op Nil : Qid . var AS : AttrSet .

  op #upModule : ModuleConstruction -> Module [memo] .
  ----------------------------------------------------
  eq #upModule(ME) = upModule(ME, true) .

  op _;_ : FreeConstruction FreeConstruction -> FreeConstruction [ctor assoc prec 110 format(d n d d)] .
  ------------------------------------------------------------------------------------------------------

  op _deriving_ : ModuleConstruction FreeConstruction -> ModuleConstruction [ctor prec 120] .
  op _deriving_ : Module FreeConstruction -> [Module] [ctor prec 120] .
  ---------------------------------------------------------------------
  eq #upModule((MC deriving FC)) = #upModule(MC) deriving FC .
  eq MOD deriving (FC ; FC')     = (MOD deriving FC) deriving FC' .

  op forall_exists_ : ModuleTemplate ModuleTemplate -> FreeConstruction [ctor prec 100 format(d n++i n ni-- d)] .
  ---------------------------------------------------------------------------------------------------------------
  ceq MOD deriving forall MT exists MT' = MOD ++ (MT' << SUBSTS) if SUBSTS := match MT with #mkTemplate(MOD) .
```

Covariant data are data-structures that follow the normal
`subsorts X < NeData{X} < Data{X} .` pattern. The free construction
`covariant-data` will build the sort-structure for you. The default
data-structures for `List` and `Set` are provided.

We'll need structured operator names (in addition to structured sort names)
order to fully express these constructions. Perhaps this suggests "structured
Qid" as a thing to build?

```{.maude .module-exp}
  op covariant-data : Sort -> FreeConstruction .
  ----------------------------------------------
  ceq covariant-data(S) = ( forall sorts svar('X) .
                                   none
                            exists sorts S < svar('X) > ; NeS < svar('X) > .
                                   subsort       svar('X)   < NeS < svar('X) > .
                                   subsort NeS < svar('X) > <   S < svar('X) > .
                                   --- op Nil < svar('X) > : nil -> S < svar('X) > [ctor] .
                          ; forall sorts svar('X) ; S < svar('X) > ; NeS < svar('X) >
                                       ; svar('Y) ; S < svar('Y) > ; NeS < svar('Y) > .
                                   subsort svar('X) < svar('Y) .
                            exists sorts none .
                                   subsort   S < svar('X) > <   S < svar('Y) > .
                                   subsort NeS < svar('X) > < NeS < svar('Y) > .
                          )
                        if NeS := qid("Ne" + string(S))
                        /\ Nil := qid("." + string(S)) .

  var Q : Qid .
  op const : Qid Sort -> Term .
  -----------------------------
  eq const(Q, S) = qid(string(Q) + "." + string(S)) .

  op covariant-data-with-binops : Sort Qid AttrSet -> FreeConstruction .
  ----------------------------------------------------------------------
  ceq covariant-data-with-binops(S, Op, AS) = ( covariant-data(S)
                                              ; forall sorts svar('X) ; S < svar('X) > ; NeS < svar('X) > .
                                                       subsort       svar('X)   < NeS < svar('X) > .
                                                       subsort NeS < svar('X) > <   S < svar('X) > .
                                                exists sorts none .
                                                       none
                                                       ( op Nil < svar('X) > : nil -> S < svar('X) > [ctor] .
                                                         op Op :   S < svar('X) > S < svar('X) > ->   S < svar('X) > [ctor id(const(Nil < svar('X) >, S < svar('X) >)) AS] .
                                                         op Op : NeS < svar('X) > S < svar('X) > -> NeS < svar('X) > [ctor id(const(Nil < svar('X) >, S < svar('X) >)) AS] .
                                                       )
                                              )
                                            if NeS := qid("Ne" + string(S))
                                            /\ Nil := qid("." + string(S)) .

  ops List Set : -> FreeConstruction .
  ------------------------------------
  eq List = covariant-data('List) .
  eq Set  = covariant-data-with-binops('Set, '_;_, assoc comm) .
endfm
```
