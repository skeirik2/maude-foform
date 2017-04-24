Module Templates
================

First, we'll need a way to generate variables at the object level because
writing all our syntax at the meta-level can be a pain. Additionally, we'll need
a way to have "structured" sort names and operator names. For this, a few
constructors are provided.

```{.maude .module-exp}
fmod STRUCTURED-QID is
  extending META-LEVEL .

  vars Q Q' : Qid . vars S S' : Sort . var SS : SortSet . var SSDS : SubsortDeclSet . var AS : AttrSet .
  var OPDS : OpDeclSet . var MAS : MembAxSet . var EQS : EquationSet . var RLS : RuleSet . var IL : ImportList .
  vars NeTL NeTL' : TypeList . var TL : TypeList .
  var TERM : Term . var TERML : TermList . vars NeTERML NeTERML' : NeTermList .

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

  op #resolveSorts : SortSet -> SortSet .
  ---------------------------------------
  eq #resolveSorts(none)        = none .
  eq #resolveSorts(S < TL >)    = qid(string(#resolveSorts(S)) + "{" + #string(#resolveTypeList(TL)) + "}") .
  eq #resolveSorts(S ; S' ; SS) = #resolveSorts(S) ; #resolveSorts(S') ; #resolveSorts(SS) .
  eq #resolveSorts(S)           = S [owise] .

  op #resolveTypeList : TypeList -> TypeList .
  --------------------------------------------
  eq #resolveTypeList(nil)        = nil .
  eq #resolveTypeList(S)          = #resolveSorts(S) .
  eq #resolveTypeList(NeTL NeTL') = #resolveTypeList(NeTL) #resolveTypeList(NeTL') .

  op #string : TypeList -> String .
  ---------------------------------
  eq #string(nil)        = "" .
  eq #string(S)          = string(S) .
  eq #string(NeTL NeTL') = string(NeTL) + ";" + string(NeTL') .

  op #resolveQid : Qid -> Qid .
  -----------------------------
  eq #resolveQid(Q < TL >) = qid(string(#resolveQid(Q)) + "{" + string(#resolveTypeList(TL)) + "}") .
  eq #resolveQid(Q)        = Q [owise] .

  op #resolveTerm : TermList -> TermList .
  ----------------------------------------
  eq #resolveTerm(var(Q, S))            = qid(string(#resolveQid(Q)) + ":" + string(#resolveSorts(S))) .
  eq #resolveTerm(Q . S)                = qid(string(#resolveQid(Q)) + "." + string(#resolveSorts(S))) .
  eq #resolveTerm(Q [ TERML ])          = #resolveQid(Q) [ #resolveTerm(TERML) ] .
  eq #resolveTerm((NeTERML , NeTERML')) = #resolveTerm(NeTERML) , #resolveTerm(NeTERML') .
  eq #resolveTerm(TERM)                 = TERM [owise] .
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

  sort SortPoset .
  subsort SortSet < SortPoset .
  sorts SortTemplate SubsortTemplate OpTemplate MembAxTemplate EqTemplate RuleTemplate ModuleTemplate .
  subsort SortTemplate < SubsortTemplate < OpTemplate < MembAxTemplate < EqTemplate < RuleTemplate < ModuleTemplate .

  vars H H' : Header . vars I I' : Import . vars IL IL' IL'' : ImportList . vars S S' S'' : Sort . vars SS SS' SS'' : SortSet . var SPS : SortPoset . vars SSDS SSDS' : SubsortDeclSet .
  vars OPDS OPDS' : OpDeclSet . vars MAS MAS' : MembAxSet . vars EQS EQS' : EquationSet . vars RLS RLS' : RuleSet .
  var AS : AttrSet . vars A A' : Attr . var EQC : EqCondition . vars C C' : Condition . vars MT MT' : ModuleTemplate .
  vars MOD MOD' : Module . var Q : Qid . var TL : TypeList . var TYPE : Type . vars T T' : Term .
  vars SU SU' : Substitution . var SUBSTS : SubstitutionSet .
  var ST : SortTemplate . var SST : SubsortTemplate . var OPT : OpTemplate . var MAT : MembAxTemplate . var EQT : EqTemplate . var RLT : RuleTemplate .
  vars NeTL NeTL' : NeTypeList .
  vars OP OP' : OpDecl . vars EQ EQ' : Equation . vars MB MB' : MembAx . vars RL RL' : Rule .

  op _<_ : SortPoset SortPoset -> SortPoset [assoc id: none prec 122] .
  op (subsorts_.) : SortPoset -> SubsortDeclSet .
  -----------------------------------------------
  eq ( subsorts SS . )
   = none .
  eq ( subsorts S < S' . )
   = ( subsort S < S' . ) .
  eq ( subsorts S < S' ; S'' ; SS' . )
   = ( subsorts S < S' .
       subsorts S < S'' .
       subsorts S < SS' .
     ) .
  eq ( subsorts S ; S' ; SS < S'' ; SS' . )
   = ( subsorts S  < S'' ; SS' .
       subsorts S' < S'' ; SS' .
       subsorts SS < S'' ; SS' .
     ) .
  eq ( subsorts S ; SS < S' ; SS' < SPS . )
   = ( subsorts S  < S' ; SS' .
       subsorts SS < S' ; SS' .
       subsorts      S' ; SS'  < SPS .
     ) .

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

  op _++_ : Module Module -> Module [assoc prec 73] .
  ---------------------------------------------------
  eq MOD ++ MOD' = MOD ++ asTemplate(MOD') .

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
  eq #varExtendTemplate(IL sorts SS . SSDS OPDS MAS EQS RLS) = ( (IL         importlistvar('##MTCTXILIST##))
                                                                 (sorts SS ; ssetvar('##MTMTXSORTS##) .)
                                                                 (SSDS       subsvar('##MTCTXSUBSORT##))
                                                                 (OPDS       opsetvar('##MTCTXOPSET##))
                                                                 (MAS        membaxsetvar('##MTCTXMEMBAXSET##))
                                                                 (EQS        eqsetvar('##MTCTXEQSET##))
                                                                 (RLS        rulesetvar('##MTCTXRULESET##))
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

  op #resolveModule : Module -> [Module] .
  ----------------------------------------
  eq #resolveModule(MOD) = fromTemplate(getName(MOD), #resolveNames(asTemplate(MOD))) .

  op #resolveNames : ModuleTemplate -> ModuleTemplate .
  -----------------------------------------------------
  eq  #resolveNames(sorts SS .) = (sorts #resolveSorts(SS) .) .
  ceq #resolveNames(ST   SSDS)  = #resolveNames(ST)   #resolveSubsorts(SSDS)   if not (SSDS == none) .
  ceq #resolveNames(SST  OPDS)  = #resolveNames(SST)  #resolveOps(OPDS)        if not (OPDS == none) .
  ceq #resolveNames(OPT  MAS)   = #resolveNames(OPT)  #resolveMemberships(MAS) if not (MAS  == none) .
  ceq #resolveNames(MAT  EQS)   = #resolveNames(MAT)  #resolveEquations(EQS)   if not (EQS  == none) .
  ceq #resolveNames(EQT  RLS)   = #resolveNames(EQT)  #resolveRules(RLS)       if not (RLS  == none) .
  ceq #resolveNames(IL   RLT)   = #resolveImports(IL) #resolveNames(RLT)       if not (IL   == nil) .

  op #resolveSubsorts : SubsortDeclSet -> SubsortDeclSet .
  --------------------------------------------------------
  eq #resolveSubsorts(none)                  = none .
  eq #resolveSubsorts(subsort S < S' . SSDS) = ( subsort #resolveSorts(S) < #resolveSorts(S') .
                                                 #resolveSubsorts(SSDS)
                                               ) .

  op #resolveAttrs : AttrSet -> AttrSet .
  ---------------------------------------
  eq #resolveAttrs(none)    = none .
  eq #resolveAttrs(id(T))   = id(#resolveTerm(T)) .
  eq #resolveAttrs(A A' AS) = #resolveAttrs(A) #resolveAttrs(A') #resolveAttrs(AS) .
  eq #resolveAttrs(A)       = A [owise] .

  op #resolveCondition : Condition -> Condition .
  ----------------------------------------------
  eq  #resolveCondition(nil) = nil .
  eq  #resolveCondition(T = T')  = #resolveTerm(T) =  #resolveTerm(T') .
  eq  #resolveCondition(T : S)   = #resolveTerm(T) :  #resolveSorts(S) .
  eq  #resolveCondition(T := T') = #resolveTerm(T) := #resolveTerm(T') .
  eq  #resolveCondition(T => T') = #resolveTerm(T) => #resolveTerm(T') .
  ceq #resolveCondition(C /\ C') = #resolveCondition(C) /\ #resolveCondition(C') if not (C == nil or C' == nil) .

  op #resolveOps : OpDeclSet -> OpDeclSet .
  -----------------------------------------
  eq #resolveOps(none) = none .
  eq #resolveOps(OP OP' OPDS) = #resolveOps(OP) #resolveOps(OP') #resolveOps(OPDS) .
  eq #resolveOps(op Q : TL -> TYPE [AS] .) = (op #resolveQid(Q) : #resolveTypeList(TL) -> #resolveTypeList(TYPE) [#resolveAttrs(AS)] .) .

  op #resolveMemberships : MembAxSet -> MembAxSet .
  -------------------------------------------------
  eq #resolveMemberships(none) = none .
  eq #resolveMemberships(MB MB' MAS) = #resolveMemberships(MB) #resolveMemberships(MB') #resolveMemberships(MAS) .
  eq #resolveMemberships( mb T : S        [AS] .) = ( mb #resolveTerm(T) : #resolveSorts(S)                           [#resolveAttrs(AS)] .) .
  eq #resolveMemberships(cmb T : S if EQC [AS] .) = (cmb #resolveTerm(T) : #resolveSorts(S) if #resolveCondition(EQC) [#resolveAttrs(AS)] .) .
  
  op #resolveEquations : EquationSet -> EquationSet .
  ---------------------------------------------------
  eq #resolveEquations(none) = none .
  eq #resolveEquations(EQ EQ' EQS) = #resolveEquations(EQ) #resolveEquations(EQ') #resolveEquations(EQS) .
  eq #resolveEquations( eq T = T'        [AS] .) = ( eq #resolveTerm(T) = #resolveTerm(T')                           [#resolveAttrs(AS)] .) .
  eq #resolveEquations(ceq T = T' if EQC [AS] .) = (ceq #resolveTerm(T) = #resolveTerm(T') if #resolveCondition(EQC) [#resolveAttrs(AS)] .) .

  op #resolveRules : RuleSet -> RuleSet .
  ---------------------------------------
  eq #resolveRules(none) = none .
  eq #resolveRules(RL RL' RLS) = #resolveRules(RL) #resolveRules(RL') #resolveRules(RLS) .
  eq #resolveRules( rl T => T'      [AS] .) = ( rl #resolveTerm(T) => #resolveTerm(T')                         [#resolveAttrs(AS)] .) .
  eq #resolveRules(crl T => T' if C [AS] .) = (crl #resolveTerm(T) => #resolveTerm(T') if #resolveCondition(C) [#resolveAttrs(AS)] .) .

  op #resolveImports : ImportList -> ImportList .
  -----------------------------------------------
  eq #resolveImports(nil) = nil .
  eq #resolveImports(I IL I IL')       = #resolveImports(I IL IL') .
  eq #resolveImports(I)                = I .
  eq #resolveImports(I I' IL)          = I #resolveImports(I' IL) [owise] .
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

  var SUBSTS : SubstitutionSet . var MOD : Module . vars MT MT' : ModuleTemplate . vars FC FC' FC'' : FreeConstruction .
  vars S S' NeS : Sort . vars SS : SortSet . vars Op Nil Q : Qid . var AS : AttrSet . var NES : Variable .
  vars SUB SUB' : Substitution . var SUBS : SubstitutionSet .

  op _<_> : ModFreeConstruction Qid -> FreeConstruction [ctor] .
  --------------------------------------------------------------

  op forall_exists_ : ModuleTemplate ModuleTemplate -> FreeConstruction [ctor prec 75 format(d n++i n ni-- d)] .
  --------------------------------------------------------------------------------------------------------------

  op exists_ : ModuleTemplate -> FreeConstruction [ctor prec 75 format(d n d)] .
  ------------------------------------------------------------------------------
  eq exists MT = forall (sorts none .) exists MT .

  op _;_ : FreeConstruction FreeConstruction -> FreeConstruction [ctor assoc prec 76 format(d n d d)] .
  op _|_ : FreeConstruction FreeConstruction -> FreeConstruction [ctor assoc comm prec 77 format(d n d d)] .
  ----------------------------------------------------------------------------------------------------------
  eq FC | FC = FC .
  eq (FC | FC') ; FC''         = (FC ; FC'') | (FC' ; FC'') .
  eq         FC ; (FC' | FC'') = (FC ; FC')  | (FC  ; FC'') .

  op _<<_ : FreeConstruction SubstitutionSet -> FreeConstruction [right id: empty] .
  ----------------------------------------------------------------------------------
  eq (forall MT exists MT') << SUB = forall (MT << SUB) exists (MT' << SUB) | forall MT exists MT' .
  eq FC << (SUB | SUB' | SUBS)     = (FC << SUB) | (FC << SUB') | (FC << SUBS) .
  eq (FC | FC') << SUB             = (FC << SUB) | (FC' << SUB) .
  eq (FC ; FC') << SUB             = (FC << SUB) ; (FC' << SUB) .
```

Covariant Data
--------------

Covariant data are data-structures that follow the normal
`subsorts X < NeData{X} < Data{X} .` pattern. The free construction
`covariant-data` will build the sort-structure for you.

```{.maude .module-exp}
  op covariant-data : Sort -> FreeConstruction .
  ----------------------------------------------
  ceq covariant-data(S) =   forall sorts svar('X) .
                            exists ( sorts S < svar('X) > ; NeS < svar('X) > . )
                                   ( subsorts svar('X) < (NeS < svar('X) >) < (S < svar('X) >) . )
                          ; forall ( sorts svar('X) ; S < svar('X) > ; NeS < svar('X) >
                                         ; svar('Y) ; S < svar('Y) > ; NeS < svar('Y) > .
                                   )
                                   ( subsort svar('X) < svar('Y) . )
                            exists ( sorts none . )
                                   ( subsort   S < svar('X) > <   S < svar('Y) > .
                                     subsort NeS < svar('X) > < NeS < svar('Y) > .
                                   )
                        if NeS := qid("Ne" + string(S)) .

  op covariant-data-binary : Sort Qid AttrSet -> FreeConstruction .
  -----------------------------------------------------------------
  ceq covariant-data-binary(S, Op, AS) =   covariant-data(S)
                                         ; forall ( sorts svar('X) ; S < svar('X) > ; NeS < svar('X) > . )
                                                  ( subsorts svar('X) < (NeS < svar('X) >) < (S < svar('X) >) . )
                                           exists ( sorts none . )
                                                  ( op Nil : nil -> S < svar('X) > [ctor] .
                                                    op Op : S < svar('X) >   S < svar('X) > ->   S < svar('X) > [ctor id(Nil . S < svar('X) >) AS] .
                                                    op Op : S < svar('X) > NeS < svar('X) > -> NeS < svar('X) > [ctor id(Nil . S < svar('X) >) AS] .
                                                  )
                                       if NeS := qid("Ne" + string(S))
                                       /\ Nil := qid("." + string(S)) .
```

The free constructions for data-types `LIST` and `SET` are provided here.

```{.maude .module-exp}
  ops LIST SET QFML : -> FreeConstruction .
  -----------------------------------------
  eq LIST = covariant-data-binary('List, '_`,_, assoc) .
  ceq SET = ( covariant-data-binary('Set, '_;_, assoc comm)
            ; forall ( sorts 'NeSet < svar('X) > . )
              exists ( sorts none . )
                     ( eq '_;_[NES, NES] = NES [none] . )
            )
          if NES := var('NeS < svar('X) >, 'NeSet < svar('X) >) .
```

Signature Refinement
--------------------

Signature refinements add subsorts to every sort (adding the annotation that
they are refined), as well as copying operators over only the refined sorts
down. Right now only operators up to arity 2 are handled (until we have a better
way to generate them).

```{.maude .module-exp}
  op sort-refinement : Qid -> FreeConstruction .
  ----------------------------------------------
  eq sort-refinement(Q) =   forall ( sorts svar('X) . )
                            exists ( sorts (svar('X) < Q >) . )
                                   ( subsort (svar('X) < Q >) < svar('X) . )
                          ; forall ( sorts svar('X) ; svar('Y) ; (svar('X) < Q >) ; (svar('Y) < Q >) . )
                                   ( subsort svar('X) < svar('Y) . )
                            exists ( sorts none . )
                                   ( subsort (svar('X) < Q >) < (svar('Y) < Q >) . ) .

  op signature-refinement : Qid -> FreeConstruction .
  ---------------------------------------------------
  eq signature-refinement(Q) =   sort-refinement(Q)
                               ; signature-refinement(0, Q)
                               ; signature-refinement(1, Q)
                               ; signature-refinement(2, Q) .

  op signature-refinement : Nat Qid -> FreeConstruction .
  ---------------------------------------------------
  eq signature-refinement(0, Q) = forall ( sorts svar('X) ; (svar('X) < Q >) . )
                                         ( op qvar('OP) : nil -> svar('X) [attrsetvar('AS)] . )
                                  exists ( sorts none . )
                                         ( op qvar('OP) : nil -> (svar('X) < Q >) [attrsetvar('AS)] . ) .
  eq signature-refinement(1, Q) = ( forall ( sorts svar('X) ; (svar('X) < Q >) ; svar('Y) ; (svar('Y) < Q >). )
                                           ( op qvar('OP) : svar('Y) -> svar('X) [attrsetvar('AS)] . )
                                    exists ( sorts none . )
                                           ( op qvar('OP) : (svar('Y) < Q >) -> (svar('X) < Q >) [attrsetvar('AS)] . )
                                  ) << ('X:Sort <- 'Y:Sort) .
  eq signature-refinement(2, Q) = ( forall ( sorts svar('X) ; (svar('X) < Q >) ; svar('Y) ; (svar('Y) < Q >) ; svar('Z) ; (svar('Z) < Q >) . )
                                           ( op qvar('OP) : svar('Y) svar('Z) -> svar('X) [attrsetvar('AS)] . )
                                    exists ( sorts none . )
                                           ( op qvar('OP) : (svar('Y) < Q >) (svar('Z) < Q >) -> (svar('X) < Q >) [attrsetvar('AS)] . )
                                  ) << (('X:Sort <- 'Y:Sort) | ('X:Sort <- 'Z:Sort) | ('Y:Sort <- 'Z:Sort) | ('Y:Sort <- 'X:Sort ; 'Z:Sort <- 'X:Sort)) .
endfm
```

Meta Theory
-----------

Sometimes you want a "meta theory" specific to your module. For example, you may
want to express using just a sort that a meta-level `Term` is a well-formed term
in your theory, or that it is a well-formed term of a specific sort in your
theory. This free construction will extend your module with its meta-theory, so
that this can be done. This is a construction that refines the module
`META-TERM` and adds it to your module, as well as adding in conditional
memberships which push elements of the sort `Term` into the subsort of
`Term{MYMOD}` when appropriate.


Module Expressions
==================

This module simply provides the hookup to our extension of the Meta-Level module
expressions. A memo-ised version of `upModule` is provided too for the
extensions. In addition, free constructions are provided. Free constructions
provide a module template with variables to determine anonymous views, and a
second module template to determine the associated parameterized module.

```{.maude .module-exp}
fmod MODULE-EXPRESSION is
  extending FREE-CONSTRUCTION .

  var MOD : Module . var ME : ModuleExpression . var SUBSTS : SubstitutionSet .
  vars FC FC' : FreeConstruction . var MFC : ModFreeConstruction .
  vars MT MT' : ModuleTemplate .

  op #upModule : ModuleExpression -> Module [memo] .
  --------------------------------------------------
  eq #upModule(ME) = upModule(ME, false) [owise] .

  op _deriving_ : ModuleExpression FreeConstruction -> ModuleExpression [prec 80] .
  ---------------------------------------------------------------------------------
  eq #upModule(ME deriving FC) = #upModule(ME) deriving FC .

  var Q : Qid .

  op META-THEORY : -> ModFreeConstruction .
  -----------------------------------------
  eq META-THEORY < Q > =   exists ( extending 'META-LEVEL . )
                                  ( sorts none . )
                         ; exists asTemplate(#upModule('META-TERM deriving sort-refinement(Q)))
                         ; forall ( sorts 'Constant   ; 'Constant   < svar('MOD) >
                                        ; 'Variable   ; 'Variable   < svar('MOD) >
                                        ; 'GroundTerm ; 'GroundTerm < svar('MOD) >
                                        ; 'Term       ; 'Term       < svar('MOD) > .
                                  )
                           exists ( sorts none . )
                                  ( --- cmb 'C:Constant    : 'Constant   < svar('MOD) > if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'C:Constant]    = 'true.Bool [none] .
                                    cmb 'V:Variable    : 'Variable   < svar('MOD) > if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'V:Variable]    = 'true.Bool [none] .
                                    cmb 'GT:GroundTerm : 'GroundTerm < svar('MOD) > if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'GT:GroundTerm] = 'true.Bool [none] .
                                    cmb 'T:Term        : 'Term       < svar('MOD) > if 'wellFormed['upModule[upTerm(Q), 'false.Bool], 'T:Term]        = 'true.Bool [none] .
                                  ) .

  op _deriving_ : Module FreeConstruction -> [Module] [prec 80] .
  ---------------------------------------------------------------
  ceq MOD deriving forall MT exists MT' = MOD ++ (MT' << SUBSTS) if SUBSTS := match MT with asTemplate(MOD) .
  eq  MOD deriving MFC                  = MOD deriving MFC < getName(MOD) > .
  eq  MOD deriving (FC ; FC')           = (MOD deriving FC) deriving FC' .
  eq  MOD deriving (FC | FC')           = (MOD deriving FC) ++ (MOD deriving FC') .
endfm
```
