Module Templates
================

Module templates serve as a slightly more flexible data-structure than the ones
provided in the prelude for expressing syntactic theories.

Structured Names
----------------

First, we'll need a way to generate variables at the object level because
writing all our syntax at the meta-level can be a pain. Additionally, we'll need
a way to have "structured" sort names and operator names. For this, a few
constructors are provided.

```{.maude .mod-template}
fmod STRUCTURED-NAME is
  extending META-LEVEL .

  vars I I' : Import . vars IL IL' : ImportList . vars S S' : Sort . var SS : SortSet . var SSDS : SubsortDeclSet .
  vars Q Q' : Qid . vars A A' : Attr . var AS : AttrSet . var SU : Substitution .
  vars OP OP' : OpDecl . var OPDS : OpDeclSet . vars MB MB' : MembAx . var MAS : MembAxSet .
  vars EQ EQ' : Equation . var EQS : EquationSet . vars RL RL' : Rule . var RLS : RuleSet .
  var TYPE : Type . vars NeTL NeTL' : NeTypeList . var TL : TypeList . vars C C' : Condition . vars EQC EQC' : EqCondition .
  vars TERM TERM' : Term . var TERML : TermList . vars NeTERML NeTERML' : NeTermList . var VAR : Variable . var CONST : Constant . var N : Nat .

  op _<_>  : Qid  TypeList -> Qid      [prec 23] .
  op _{_}  : Sort TypeList -> Sort     [prec 23] .
  op _@_   : Qid  Sort     -> Sort     [prec 23] .
  op _?    : Sort          -> Sort     [prec 23] .
  op _==>_ : Sort Sort     -> Sort     [prec 25] .
  op const : Qid  Sort     -> Constant .
  op var   : Qid  Sort     -> Variable .
  --------------------------------------

  op downQidError?          : -> [Qid] .
  op downSubstitutionError? : -> [Substitution] .
  op downImportListError?   : -> [ImportList] .
  op downSortsError?        : -> [SortSet] .
  op downSubsortsError?     : -> [SubsortDeclSet] .
  op downAttrSetError?      : -> [AttrSet] .
  op downOpSetError?        : -> [OpDeclSet] .
  op downMembAxSetError?    : -> [MembAxSet] .
  op downEqSetError?        : -> [EquationSet] .
  op downRuleSetError?      : -> [RuleSet] .
  ------------------------------------------

  op qvar          : Qid -> Qid .
  op subvar        : Qid -> Substitution .
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
  ceq subvar(Q)        = SU   if SU   := downTerm(qid(string(Q) + ":Substitution"),   downSubstitutionError?) .
  ceq importlistvar(Q) = IL   if IL   := downTerm(qid(string(Q) + ":ImportList"),     downImportListError?) .
  ceq svar(Q)          = S    if S    := downTerm(qid(string(Q) + ":Sort"),           downSortsError?) .
  ceq ssetvar(Q)       = SS   if SS   := downTerm(qid(string(Q) + ":SortSet"),        downSortsError?) .
  ceq subsvar(Q)       = SSDS if SSDS := downTerm(qid(string(Q) + ":SubsortDeclSet"), downSubsortsError?) .
  ceq attrsetvar(Q)    = AS   if AS   := downTerm(qid(string(Q) + ":AttrSet"),        downAttrSetError?) .
  ceq opsetvar(Q)      = OPDS if OPDS := downTerm(qid(string(Q) + ":OpDeclSet"),      downOpSetError?) .
  ceq membaxsetvar(Q)  = MAS  if MAS  := downTerm(qid(string(Q) + ":MembAxSet"),      downMembAxSetError?) .
  ceq eqsetvar(Q)      = EQS  if EQS  := downTerm(qid(string(Q) + ":EquationSet"),    downEqSetError?) .
  ceq rulesetvar(Q)    = RLS  if RLS  := downTerm(qid(string(Q) + ":RuleSet"),        downRuleSetError?) .
```

It's useful when building universal constructions to generate the same
structure, but with incremented variable names.

-   `prime` will prime every variable in a given term.

```{.maude .mod-template}
  op prime :     Sort -> Sort .
  op prime : Nat Sort -> Sort .
  -----------------------------
  eq  prime(S)    = prime(1, S) .
  ceq prime(N, S) = S' if S' := downTerm(primeVars(N, upTerm(S)), downSortsError?) .

  op primeVars : Nat TermList -> TermList .
  -----------------------------------------
  eq primeVars(N, VAR)                  = qid(string(getName(VAR)) + #primes(N) + ":" + string(getType(VAR))) .
  eq primeVars(N, CONST)                = CONST .
  eq primeVars(N, Q[NeTERML])           = Q[primeVars(N, NeTERML)] .
  eq primeVars(N, (NeTERML , NeTERML')) = primeVars(N, NeTERML) , primeVars(N, NeTERML') .

  op #primes : Nat -> String .
  ----------------------------
  eq #primes(0)    = "" .
  eq #primes(s(N)) = "'" + #primes(N) .
```

We'll also need ways to "resolve" these names into proper Maude names, so that
we can do execution in Maude with the results. Here we provide the "base"
resolution, as well as lifting it over the various meta-level data.

```{.maude .mod-template}
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
  eq #resolveQid(Q < TL >) = qid(string(#resolveQid(Q)) + "<" + #string(#resolveTypeList(TL)) + ">") .
  eq #resolveQid(Q)        = Q [owise] .

  op #resolveTerm : TermList -> TermList .
  ----------------------------------------
  eq #resolveTerm(const(Q, S))          = qid(string(#resolveQid(Q)) + "." + string(#resolveSorts(S))) .
  eq #resolveTerm(var(Q, S))            = qid(string(#resolveQid(Q)) + ":" + string(#resolveSorts(S))) .
  eq #resolveTerm(Q [ TERML ])          = #resolveQid(Q) [ #resolveTerm(TERML) ] .
  eq #resolveTerm((NeTERML , NeTERML')) = #resolveTerm(NeTERML) , #resolveTerm(NeTERML') .
  eq #resolveTerm(TERM)                 = TERM [owise] .

  op #resolveImports : ImportList -> ImportList .
  -----------------------------------------------
  eq #resolveImports(nil)        = nil .
  eq #resolveImports(I)          = I .
  eq #resolveImports(I IL I IL') = #resolveImports(I IL IL') .
  eq #resolveImports(I I' IL)    = I #resolveImports(I' IL) [owise] .

  op #resolveSorts : SortSet -> SortSet .
  ---------------------------------------
  eq #resolveSorts(none)        = none .
  eq #resolveSorts(S { TL })    = qid(string(#resolveSorts(S)) + "{" + #string(#resolveTypeList(TL)) + "}") .
  eq #resolveSorts(Q @ S)       = qid(string(#resolveQid(Q)) + "@" + string(#resolveSorts(S))) .
  eq #resolveSorts(S ==> S')    = qid(string(#resolveSorts(S)) + "==>" + string(#resolveSorts(S'))) .
  eq #resolveSorts(S ?)         = qid(string(#resolveSorts(S)) + "?") .
  eq #resolveSorts(S ; S' ; SS) = #resolveSorts(S) ; #resolveSorts(S') ; #resolveSorts(SS) .
  eq #resolveSorts(S)           = S [owise] .

  op #resolveSubsorts : SubsortDeclSet -> SubsortDeclSet .
  --------------------------------------------------------
  eq #resolveSubsorts(none)                  = none .
  eq #resolveSubsorts(subsort S < S' . SSDS) = ( subsort #resolveSorts(S) < #resolveSorts(S') .
                                                 #resolveSubsorts(SSDS)
                                               ) .

  op #resolveAttrs : AttrSet -> AttrSet .
  ---------------------------------------
  eq #resolveAttrs(none)     = none .
  eq #resolveAttrs(id(TERM)) = id(#resolveTerm(TERM)) .
  eq #resolveAttrs(A A' AS)  = #resolveAttrs(A) #resolveAttrs(A') #resolveAttrs(AS) .
  eq #resolveAttrs(A)        = A [owise] .

  op #resolveOps : OpDeclSet -> OpDeclSet .
  -----------------------------------------
  eq #resolveOps(none) = none .
  eq #resolveOps(OP OP' OPDS) = #resolveOps(OP) #resolveOps(OP') #resolveOps(OPDS) .
  eq #resolveOps(op Q : TL -> TYPE [AS] .) = (op #resolveQid(Q) : #resolveTypeList(TL) -> #resolveTypeList(TYPE) [#resolveAttrs(AS)] .) .

  op #resolveCondition : Condition -> Condition .
  -----------------------------------------------
  eq  #resolveCondition(nil)           = nil .
  eq  #resolveCondition(TERM = TERM')  = #resolveTerm(TERM) =  #resolveTerm(TERM') .
  eq  #resolveCondition(TERM : S)      = #resolveTerm(TERM) :  #resolveSorts(S) .
  eq  #resolveCondition(TERM := TERM') = #resolveTerm(TERM) := #resolveTerm(TERM') .
  eq  #resolveCondition(TERM => TERM') = #resolveTerm(TERM) => #resolveTerm(TERM') .
  ceq #resolveCondition(C /\ C')       = #resolveCondition(C) /\ #resolveCondition(C') if not (C == nil or C' == nil) .

  op #resolveMemberships : MembAxSet -> MembAxSet .
  -------------------------------------------------
  eq #resolveMemberships(none) = none .
  eq #resolveMemberships(MB MB' MAS) = #resolveMemberships(MB) #resolveMemberships(MB') #resolveMemberships(MAS) .
  eq #resolveMemberships( mb TERM : S        [AS] .) = ( mb #resolveTerm(TERM) : #resolveSorts(S)                           [#resolveAttrs(AS)] .) .
  eq #resolveMemberships(cmb TERM : S if EQC [AS] .) = (cmb #resolveTerm(TERM) : #resolveSorts(S) if #resolveCondition(EQC) [#resolveAttrs(AS)] .) .

  op #resolveEquations : EquationSet -> EquationSet .
  ---------------------------------------------------
  eq #resolveEquations(none) = none .
  eq #resolveEquations(EQ EQ' EQS) = #resolveEquations(EQ) #resolveEquations(EQ') #resolveEquations(EQS) .
  eq #resolveEquations( eq TERM = TERM'        [AS] .) = ( eq #resolveTerm(TERM) = #resolveTerm(TERM')                           [#resolveAttrs(AS)] .) .
  eq #resolveEquations(ceq TERM = TERM' if EQC [AS] .) = (ceq #resolveTerm(TERM) = #resolveTerm(TERM') if #resolveCondition(EQC) [#resolveAttrs(AS)] .) .

  op #resolveRules : RuleSet -> RuleSet .
  ---------------------------------------
  eq #resolveRules(none) = none .
  eq #resolveRules(RL RL' RLS) = #resolveRules(RL) #resolveRules(RL') #resolveRules(RLS) .
  eq #resolveRules( rl TERM => TERM'      [AS] .) = ( rl #resolveTerm(TERM) => #resolveTerm(TERM')                         [#resolveAttrs(AS)] .) .
  eq #resolveRules(crl TERM => TERM' if C [AS] .) = (crl #resolveTerm(TERM) => #resolveTerm(TERM') if #resolveCondition(C) [#resolveAttrs(AS)] .) .
endfm
```

Module Templates
----------------

Module templates serve as more flexible module data-structures than what the
`META-LEVEL` provides for modules. The main functionality exported is:

-   `_++_ : ModuleTemplate ModuleTemplate -> ModuleTemplate [assoc comm]` allows
    unioning two module templates.

-   `_|_ : ModuleTemplateSet ModuleTemplateSet -> ModuleTemplateSet [assoc comm id: .ModuleTemplateSet]`
    and `_\_ : ModuleTemplate ModuleTemplateSet -> ModuleTemplate [right id: .ModuleTemplateSet]`
    are the union and difference of module templates respectively.

-   `++ : ModuleTemplateSet -> ModuleTemplate` folds the operation `_++_` over
    its argument (unioning together the set of module templates).

-   `_<<_ : ModuleTemplateSet SubstitutionSet -> ModuleTemplateSet` generates
    the all module templates from the first argument instantiated with any of
    the substitutions in the second argument.

-   `match_with_ : ModuleTemplateSet ModuleTemplate -> SubstitutionSet` will
    give all the substitutions which make elements of the second module template
    set instances of an element of the first module template set.

```{.maude .mod-template}
load constrained-terms.maude

fmod MODULE-TEMPLATE-DATA is
  protecting STRUCTURED-NAME .
  protecting CTERM-SET .

  sort SortPoset .
  subsort SortSet < SortPoset .
  sorts SortTemplate SubsortTemplate OpTemplate MembAxTemplate EqTemplate RuleTemplate ModuleTemplate .
  subsort SortTemplate < SubsortTemplate < OpTemplate < MembAxTemplate < EqTemplate < RuleTemplate < ModuleTemplate .
  sorts NeModuleTemplateSet ModuleTemplateSet .
  subsort ModuleTemplate < NeModuleTemplateSet < ModuleTemplateSet .

  var H : Header . vars SU SU' SU'' : Substitution . var SUBSTS : SubstitutionSet . vars MT MT' MT'' : ModuleTemplate .
  vars IL IL' : ImportList . vars S S' S'' : Sort . vars SS SS' : SortSet . var SPS : SortPoset .
  vars SSDS SSDS' : SubsortDeclSet . vars OPDS OPDS' : OpDeclSet . vars MAS MAS' : MembAxSet . vars EQS EQS' : EquationSet . vars RLS RLS' : RuleSet .
  var ST : SortTemplate . var SST : SubsortTemplate . var OPT : OpTemplate . var MAT : MembAxTemplate . var EQT : EqTemplate . var RLT : RuleTemplate .
  vars MTS MTS' : ModuleTemplateSet . vars NeMTS NeMTS' NeMTS'' : NeModuleTemplateSet .

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

  op .ModuleTemplateSet : -> ModuleTemplateSet [ctor] .
  op _|_ : ModuleTemplateSet ModuleTemplateSet   -> ModuleTemplateSet   [ctor assoc comm id: .ModuleTemplateSet prec 73] .
  op _|_ : ModuleTemplateSet NeModuleTemplateSet -> NeModuleTemplateSet [ctor ditto] .
  ------------------------------------------------------------------------------------
  eq NeMTS | NeMTS = NeMTS .
  
  op _\_ : ModuleTemplate    ModuleTemplateSet -> ModuleTemplate    [ctor right id: .ModuleTemplateSet prec 74] .
  op _\_ : ModuleTemplateSet ModuleTemplateSet -> ModuleTemplateSet [ditto] .
  ---------------------------------------------------------------------------
  eq .ModuleTemplateSet \ NeMTS = .ModuleTemplateSet .
  eq MT \ (MT | MTS)            = .ModuleTemplateSet .
  eq (NeMTS | NeMTS') \ NeMTS'' = (NeMTS \ NeMTS'') | (NeMTS' \ NeMTS'') .
  eq (NeMTS \ NeMTS') \ NeMTS'' = NeMTS \ (NeMTS' | NeMTS'') .

  op _++_ : ModuleTemplate ModuleTemplate -> ModuleTemplate [assoc comm prec 72] .
  --------------------------------------------------------------------------------
  eq (IL sorts SS . SSDS OPDS MAS EQS RLS) ++ (IL' sorts SS' . SSDS' OPDS' MAS' EQS' RLS')
   = (IL IL') (sorts SS ; SS' .) (SSDS SSDS') (OPDS OPDS') (MAS MAS') (EQS EQS') (RLS RLS') .
  eq MT ++ (MT' \ NeMTS') = (MT ++ MT') \ NeMTS' .

  op ++ : ModuleTemplateSet -> ModuleTemplate .
  ---------------------------------------------
  eq ++(.ModuleTemplateSet) = (sorts none .) .
  eq ++(MT)                 = MT .
  eq ++(MT | NeMTS)         = MT ++ ++(NeMTS) .

  op moduleTemplateError? : -> [ModuleTemplate] .
  op _<<_ : ModuleTemplateSet SubstitutionSet -> ModuleTemplateSet .
  ------------------------------------------------------------------
  eq  MT << empty               = .ModuleTemplateSet .
  ceq MT << SU                  = MT' if MT' := downTerm(upTerm(MT) << SU, moduleTemplateError?) .
  eq  MT << (SU | SU' | SUBSTS) = (MT << SU) | (MT << SU') | (MT << SUBSTS) .
  eq  .ModuleTemplateSet << (SU | SUBSTS) = .ModuleTemplateSet .
  eq  (MT | NeMTS)       << (SU | SUBSTS) = (MT  << (SU | SUBSTS)) | (NeMTS  << (SU | SUBSTS)) .
  eq  (MTS \ NeMTS')     << (SU | SUBSTS) = (MTS << (SU | SUBSTS)) \ (NeMTS' << (SU | SUBSTS)) .

  --- TODO: ORDER HERE MATTERS!!! AAAGGHHHH!
  op match_with_ : ModuleTemplateSet ModuleTemplate -> [SubstitutionSet] .
  ------------------------------------------------------------------------
  eq  match .ModuleTemplateSet with MT  = empty .
  eq  match NeMTS | NeMTS'     with MT' = (match NeMTS with MT') | (match NeMTS' with MT') .
  ceq match MT \ NeMTS         with MT' = SUBSTS if SUBSTS := not-instance-with?(NeMTS, MT', (match MT with MT')) .
  ceq match MT                 with MT' = #varCleanSubsts(SUBSTS) if SUBSTS := #subsumesWith(upModule('MODULE-TEMPLATE, true), upTerm(#varExtendTemplate(MT)), upTerm(MT')) .
  --- eq match MT \ NeMTS               with MT' = { subvar('##SUBVAR##) in match MT with MT' | empty?(match NeMTS << subvar('##SUBVAR##) with MT') } .

  var B : [Bool] .
  op {_in_|_} : Substitution SubstitutionSet [Bool] -> SubstitutionSet [strat(2 0)] .
  -----------------------------------------------------------------------------------
  eq { SU in empty                 | B } = empty .
  eq { SU in SU'                   | B } = if downTerm(upTerm(B) << (upTerm(SU) <- upTerm(SU')), false) then SU' else empty fi .
  eq { SU in (SU' | SU'' | SUBSTS) | B } = { SU in SU' | B } | { SU in SU'' | B } | { SU in SUBSTS | B } .

  op empty? : SubstitutionSet -> Bool .
  -------------------------------------
  eq empty?(empty)       = true .
  eq empty?(SU | SUBSTS) = false .

  --- TODO: This could be generalized with some generalized comprehension
  op not-instance-with? : ModuleTemplateSet ModuleTemplate SubstitutionSet -> SubstitutionSet .
  ---------------------------------------------------------------------------------------------
  eq  not-instance-with?(MTS, MT, empty)               = empty .
  ceq not-instance-with?(MTS, MT, SU)                  = if SUBSTS == empty then SU else empty fi if SUBSTS := match (MTS << SU) with MT .
  eq  not-instance-with?(MTS, MT, (SU | SU' | SUBSTS)) = not-instance-with?(MTS, MT, SU) | not-instance-with?(MTS, MT, SU') | not-instance-with?(MTS, MT, SUBSTS) .

  var T : Term .
  op #varCleanSubst  : Substitution    -> [Substitution] .
  op #varCleanSubsts : SubstitutionSet -> [SubstitutionSet] .
  -----------------------------------------------------------
  eq #varCleanSubsts(empty)             = empty .
  eq #varCleanSubsts(SU)                = #varCleanSubst(SU) .
  eq #varCleanSubsts(SU | SU' | SUBSTS) = #varCleanSubst(SU) | #varCleanSubst(SU') | #varCleanSubsts(SUBSTS) .
  eq #varCleanSubst(SU ; '##MTCTXILIST##:ImportList       <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU ; '##MTCTXSORTS##:SortSet          <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU ; '##MTCTXSUBSORT##:SubsortDeclSet <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU ; '##MTCTXOPSET##:OpDeclSet        <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU ; '##MTCTXMEMBAXSET##:MembAxSet    <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU ; '##MTCTXEQSET##:EquationSet      <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU ; '##MTCTXRULESET##:RuleSet        <- T) = #varCleanSubst(SU) .
  eq #varCleanSubst(SU)                                         = SU [owise] .

  --- TODO: All of these variables would ideally be actually fresh.
  op #varExtendTemplate : ModuleTemplate -> [ModuleTemplate] .
  ------------------------------------------------------------
  eq #varExtendTemplate(IL sorts SS . SSDS OPDS MAS EQS RLS) = ( (IL         importlistvar('##MTCTXILIST##))
                                                                 (sorts SS ; ssetvar('##MTCTXSORTS##) .)
                                                                 (SSDS       subsvar('##MTCTXSUBSORT##))
                                                                 (OPDS       opsetvar('##MTCTXOPSET##))
                                                                 (MAS        membaxsetvar('##MTCTXMEMBAXSET##))
                                                                 (EQS        eqsetvar('##MTCTXEQSET##))
                                                                 (RLS        rulesetvar('##MTCTXRULESET##))
                                                               ) .

  op resolveNames : ModuleTemplate -> ModuleTemplate .
  ----------------------------------------------------
  eq  resolveNames(sorts SS .) = (sorts #resolveSorts(SS) .) .
  ceq resolveNames(ST   SSDS)  = resolveNames(ST)    #resolveSubsorts(SSDS)   if not (SSDS == none) .
  ceq resolveNames(SST  OPDS)  = resolveNames(SST)   #resolveOps(OPDS)        if not (OPDS == none) .
  ceq resolveNames(OPT  MAS)   = resolveNames(OPT)   #resolveMemberships(MAS) if not (MAS  == none) .
  ceq resolveNames(MAT  EQS)   = resolveNames(MAT)   #resolveEquations(EQS)   if not (EQS  == none) .
  ceq resolveNames(EQT  RLS)   = resolveNames(EQT)   #resolveRules(RLS)       if not (RLS  == none) .
  ceq resolveNames(IL   RLT)   = #resolveImports(IL) resolveNames(RLT)        if not (IL   == nil) .
endfm
```

Interface to `Module`
---------------------

To actually do execution in the modules generated by a module template, we need
functions to convert between `Module` and `ModuleTemplate`.

-   `asTemplate : Module -> ModuleTemplate` and
    `fromTemplate : ModuleTemplate -> Module` provide functions between the
    normal Maude modules and the module templates defined here.

-   `_++_ : Module ModuleTemplateSet -> Module` and
    `_++_ : Module Module -> Module` are the lifting of operator `_++_` in
    `MODULE-TEMPLATE-DATA` to work directly on Maude modules.

-   `resolveModule: ModuleTemplate -> ModuleTemplate` resolves the structured
    names of a module into proper Core Maude names.

```{.maude .mod-template}
fmod MODULE-TEMPLATE is
  protecting MODULE-TEMPLATE-DATA .
  protecting META-LEVEL .

  var H : Header . var IL : ImportList . var SS : SortSet . var SSDS : SubsortDeclSet . var OPDS : OpDeclSet .
  var MAS : MembAxSet . var EQS : EquationSet . var RLS : RuleSet . vars MOD MOD' : Module . var NeMTS : NeModuleTemplateSet .

  op asTemplate : Module -> [ModuleTemplate] .
  --------------------------------------------
  eq asTemplate(fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) = (IL sorts SS . SSDS OPDS MAS EQS) .
  eq asTemplate( mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  = (IL sorts SS . SSDS OPDS MAS EQS RLS) .

  op fromTemplate : Header ModuleTemplate -> [Module] .
  -----------------------------------------------------
  eq fromTemplate(H, IL sorts SS . SSDS OPDS MAS EQS)     = (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) .
  eq fromTemplate(H, IL sorts SS . SSDS OPDS MAS EQS RLS) = (mod  H is IL sorts SS . SSDS OPDS MAS EQS RLS endm) .

  op _++_ : Module ModuleTemplateSet -> [Module] [right id: .ModuleTemplateSet prec 72] .
  ---------------------------------------------------------------------------------------
  eq MOD ++ NeMTS = fromTemplate(getName(MOD), asTemplate(MOD) ++ ++(NeMTS)) .

  op _++_ : Module Module -> [Module] [assoc prec 73] .
  -----------------------------------------------------
  eq MOD ++ MOD' = MOD ++ asTemplate(MOD') .

  op resolveModule : Module -> [Module] .
  ---------------------------------------
  eq resolveModule(MOD) = fromTemplate(getName(MOD), resolveNames(asTemplate(MOD))) .
endfm
```
