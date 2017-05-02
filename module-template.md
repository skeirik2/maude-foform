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
  var TYPE : Type . vars NeTL NeTL' : NeTypeList . var TL : TypeList . vars COND COND' : Condition . vars EQC EQC' : EqCondition .
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

  op #primeVars : Nat TermList -> TermList .
  ------------------------------------------
  eq #primeVars(N, VAR)                  = qid(string(getName(VAR)) + #primes(N) + ":" + string(getType(VAR))) .
  eq #primeVars(N, CONST)                = CONST .
  eq #primeVars(N, Q[NeTERML])           = Q[#primeVars(N, NeTERML)] .
  eq #primeVars(N, (NeTERML , NeTERML')) = #primeVars(N, NeTERML) , #primeVars(N, NeTERML') .

  op #primes : Nat -> String .
  ----------------------------
  eq #primes(0)    = "" .
  eq #primes(s(N)) = "'" + #primes(N) .
```

We'll need the ability to get the free variables of some specific sorts.

```{.maude .mod-template}
  op #fv<Sort> : TermList -> SortSet .
  ------------------------------------
  eq #fv<Sort>(VAR)                  = if getType(VAR) == 'Sort then svar(getName(VAR)) else none fi .
  eq #fv<Sort>(CONST)                = none .
  eq #fv<Sort>(Q[NeTERML])           = #fv<Sort>(Q) ; #fv<Sort>(NeTERML) .
  eq #fv<Sort>((NeTERML , NeTERML')) = #fv<Sort>(NeTERML) , #fv<Sort>(N, NeTERML') .
```

We'll also need ways to "resolve" these names into proper Maude names, so that
we can do execution in Maude with the results. Here we provide the "base"
resolution, as well as lifting it over the various meta-level data.

```{.maude .mod-template}
  op #tl-string : TypeList -> String .
  ------------------------------------
  eq #tl-string(nil)        = "" .
  eq #tl-string(S)          = string(S) .
  eq #tl-string(NeTL NeTL') = #tl-string(NeTL) + ";" + #tl-string(NeTL') .

  op resolveNames : TypeList -> TypeList .
  ----------------------------------------
  eq resolveNames(nil)        = nil .
  eq resolveNames(S)          = resolveNames(S) .
  eq resolveNames(NeTL NeTL') = resolveNames(NeTL) resolveNames(NeTL') .

  op resolveNames: Qid -> Qid .
  -----------------------------
  eq resolveNames(Q < TL >) = qid(string(resolveNames(Q)) + "<" + #string(resolveNames(TL)) + ">") .
  eq resolveNames(Q)        = Q [owise] .

  op resolveNames : TermList -> TermList .
  ----------------------------------------
  eq resolveNames(const(Q, S))          = resolveNames(Q)) + "." + resolveNames(S))) .
  eq resolveNames(var(Q, S))            = resolveNames(Q)) + ":" + resolveNames(S))) .
  eq resolveNames(Q[TERML])             = resolveNames(Q)[resolveNames(TERML)] .
  eq resolveNames((NeTERML , NeTERML')) = resolveNames(NeTERML) , resolveNames(NeTERML') .
  eq resolveNames(TERM)                 = TERM [owise] .

  op resolveNames : SortSet -> SortSet .
  --------------------------------------
  eq resolveNames(none)        = none .
  eq resolveNames(S { TL })    = qid(string(resolveNames(S)) + "{" + #tl-string(resolveNames(TL)) + "}") .
  eq resolveNames(Q @ S)       = qid(string(resolveNames(Q)) + "@" + string(resolveNames(S))) .
  eq resolveNames(S ==> S')    = qid(string(resolveNames(S)) + "==>" + string(resolveNames(S'))) .
  eq resolveNames(S ?)         = qid(string(resolveNames(S)) + "?") .
  eq resolveNames(S ; S' ; SS) = resolveNames(S) ; resolveNames(S') ; resolveNames(SS) .
  eq resolveNames(S)           = S [owise] .

  op resolveNames : AttrSet -> AttrSet .
  --------------------------------------
  eq resolveNames(none)     = none .
  eq resolveNames(id(TERM)) = id(resolveNames(TERM)) .
  eq resolveNames(A A' AS)  = resolveNames(A) resolveNames(A') resolveNames(AS) .
  eq resolveNames(A)        = A [owise] .

  op resolveNames : SubsortDecl -> SubsortDecl .
  ----------------------------------------------
  eq resolveNames(subsort S < S' .) = ( subsort resolveNames(S) < resolveNames(S') . ) .

  op resolveNames: Condition -> Condition .
  -----------------------------------------
  eq  resolveNames(nil)           = nil .
  eq  resolveNames(TERM : S)      = resolveNames(TERM) :  resolveNames(S) .
  eq  resolveNames(TERM = TERM')  = resolveNames(TERM) =  resolveNames(TERM') .
  eq  resolveNames(TERM := TERM') = resolveNames(TERM) := resolveNames(TERM') .
  eq  resolveNames(TERM => TERM') = resolveNames(TERM) => resolveNames(TERM') .
  ceq resolveNames(COND /\ COND') = resolveNames(COND) /\ resolveNames(COND') if not (COND == nil or COND' == nil) .

  op resolveNames: OpDecl -> OpDecl .
  -----------------------------------
  eq resolveNames(op Q : TL -> TYPE [AS] .) = (op resolveNames(Q) : resolveNames(TL) -> resolveNames(TYPE) [resolveNames(AS)] .) .

  op resolveNames: MembAxSet -> MembAxSet .
  -------------------------------------------------
  eq resolveNames( mb TERM : S        [AS] .) = ( mb resolveNames(TERM) : resolveNames(S)                      [resolveNames(AS)] .) .
  eq resolveNames(cmb TERM : S if EQC [AS] .) = (cmb resolveNames(TERM) : resolveNames(S) if resolveNames(EQC) [resolveNames(AS)] .) .

  op resolveNames: EquationSet -> EquationSet .
  ---------------------------------------------
  eq resolveNames( eq TERM = TERM'        [AS] .) = ( eq resolveNames(TERM) = resolveNames(TERM')                      [resolveNames(AS)] .) .
  eq resolveNames(ceq TERM = TERM' if EQC [AS] .) = (ceq resolveNames(TERM) = resolveNames(TERM') if resolveNames(EQC) [resolveNames(AS)] .) .

  op resolveNames: RuleSet -> RuleSet .
  -------------------------------------
  eq resolveNames( rl TERM => TERM'      [AS] .) = ( rl resolveNames(TERM) => resolveNames(TERM')                    [resolveNames(AS)] .) .
  eq resolveNames(crl TERM => TERM' if C [AS] .) = (crl resolveNames(TERM) => resolveNames(TERM') if resolveNames(C) [resolveNames(AS)] .) .
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

fmod MODULE-DECLARATION is
  protecting STRUCTURED-NAME .
  protecting CTERM-SET .

  sorts SortDecl ModuleDecl NeModuleDeclSet ModuleDeclSet .
  subsorts ModuleDecl < NeModuleDeclSet < ModuleDeclSet .
  subsorts Import SortDecl SubsortDecl OpDecl MembAx Equation Rule < ModuleDecl .
  subsorts SubsortDeclSet OpDeclSet MembAxSet EquationSet RuleSet  < ModuleDeclSet .

  vars S S' S'' : Sort . vars SS SS' : SortSet . var SPS : SortPoset .
  var SU : Substitution . var SUBSTS : SubstitutionSet .
  vars NeMDS NeMDS' : NeModuleDeclSet . var MDS : ModuleDeclSet .

  op none : -> ModuleDeclSet [ctor] .
  op __ : ModuleDeclSet   ModuleDeclSet ->   ModuleDeclSet [ctor ditto] .
  op __ : ModuleDeclSet NeModuleDeclSet -> NeModuleDeclSet [ctor ditto] .
  -----------------------------------------------------------------------
  eq NeMDS NeMDS = NeMDS .

  op (sorts_.) : SortSet -> SortDeclSet [format(d d d d) prec 60] .
  -----------------------------------------------------------------
  eq ( sorts SS .
       sorts SS' .
     )
   = ( sorts SS ; SS' . ) .

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

  op error<ModuleDeclSet> : -> [ModuleDeclSet] .
  op mdsvar : Qid -> [ModuleDeclSet] .
  ------------------------------------
  ceq mdsvar(Q) = MDS if MDS := downTerm(qid(string(Q) + ":ModuleDeclSet"), error<ModuleDeclSet>) .

  op _<<_ : ModuleDeclSet Substitution -> ModuleDeclSet .
  -------------------------------------------------------
  eq  MDS   << empty = MDS .
  eq  none  << SU    = none .
  ceq NeMDS << SU    = NeMDS' if NeMDS' := downTerm(upTerm(NeMDS) << SU, error<ModuleDeclSet>) .

  op match_with_ : ModuleDeclSet ModuleDeclSet -> SubstitutionSet .
  -----------------------------------------------------------------
  eq match MDS with none  = empty .
  eq match MDS with NeMDS = SUBSTS if SUBSTS := #subsumesWith(upModule('MODULE-DECLARATION, true), upTerm(MDS mdsdvar('##MDSCTX##)), upTerm(NeMDS)) .

  op resolveNames : ModuleDeclSet -> ModuleDeclSet .
  --------------------------------------------------
  eq resolveNames(none)         = none .
  eq resolveNames(NeMDS NeMDS') = resolveNames(NeMDS) resolveNames(NeMDS') .

  op fv<Sort> : ModuleDeclSet -> SortSet .
  ----------------------------------------
  eq fv<Sort>(MDS) = #fv<Sort>(upTerm(MDS)) .
endfm

fmod MODULE-TEMPLATE is
  protecting MODULE-DECLARATION .

  sorts ModuleTemplate NeModuleTemplateSet ModuleTemplateSet .
  subsorts   ModuleDeclSet <   ModuleTemplate < ModuleTemplateSet .
  subsorts NeModuleDeclSet < NeModuleTemplate < ModuleTemplateSet .

  var MT : ModuleTemplate . vars NeMTS NeMTS' NeMTS'' : NeModuleTemplateSet . var MTS : ModuleTemplateSet .

  op none : -> ModuleTemplateSet [ctor] .
  op _|_ : ModuleTemplateSet ModuleTemplateSet   -> ModuleTemplateSet   [ctor assoc comm id: none prec 73] .
  op _|_ : ModuleTemplateSet NeModuleTemplateSet -> NeModuleTemplateSet [ctor ditto] .
  ------------------------------------------------------------------------------------
  eq NeMTS | NeMTS = NeMTS .

  op _\_ : ModuleTemplateSet ModuleTemplateSet -> ModuleTemplateSet [ctor right id: none prec 74] .
  -------------------------------------------------------------------------------------------------
  eq MT               \ (MT | MTS) = none .
  eq none             \ NeMTS      = none .
  eq (NeMTS | NeMTS') \ NeMTS''    = (NeMTS \ NeMTS'') | (NeMTS' \ NeMTS'') .
  eq (NeMTS \ NeMTS') \ NeMTS''    = NeMTS \ (NeMTS' | NeMTS'') .

  op ++ : ModuleTemplateSet -> ModuleDeclSet .
  --------------------------------------------
  eq ++(none)       = none .
  eq ++(MT)         = MT .
  eq ++(MT | NeMTS) = MT ++(NeMTS) .

  op error<ModuleTemplateSet> : -> [ModuleTemplateSet] .
  op _<<_ : ModuleTemplateSet SubstitutionSet -> ModuleTemplateSet .
  ------------------------------------------------------------------
  eq MTS          << empty               = MTS .
  eq MTS          << (SU | SU' | SUBSTS) = (MTS << SU) | (MTS << SU') | (MTS << SUBSTS) .
  eq (MT | NeMTS) << SUBSTS              = (MT << SUBSTS) | (NeMTS << SUBSTS) .
  eq (MT \ NeMTS) << SUBSTS              = (MT << SUBSTS) \ (NeMTS << SUBSTS) .

  op match_with_ : ModuleTemplateSet ModuleTemplate -> [SubstitutionSet] .
  ------------------------------------------------------------------------
  eq match NeMTS | NeMTS' with MT  = (match NeMTS with MT) | (match NeMTS' with MT) .
  eq match    MT \ NeMTS  with MT' = SUBSTS if SUBSTS := not-instance-with?(NeMTS, MT', (match MT with MT')) .

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

  op not-instance-with? : ModuleTemplateSet ModuleTemplate SubstitutionSet -> SubstitutionSet .
  ---------------------------------------------------------------------------------------------
  eq  not-instance-with?(MTS, MT, empty)               = empty .
  ceq not-instance-with?(MTS, MT, SU)                  = if SUBSTS == empty then SU else empty fi if SUBSTS := match (MTS << SU) with MT .
  eq  not-instance-with?(MTS, MT, (SU | SU' | SUBSTS)) = not-instance-with?(MTS, MT, SU) | not-instance-with?(MTS, MT, SU') | not-instance-with?(MTS, MT, SUBSTS) .

  op resolveNames : ModuleTemplateSet -> ModuleTemplateSet .
  ----------------------------------------------------------
  eq resolveNames(NeMTS | NeMTS') = resolveNames(NeMTS) | resolveNames(NeMTS') .
  eq resolveNames(NeMTS / NeMTS') = resolveNames(NeMTS) / resolveNames(NeMTS') .

  op fv<Sort>: ModuleTemplateSet -> ModuleTemplateSet .
  -----------------------------------------------------
  eq fv<Sort>(NeMTS | NeMTS') = fv<Sort>(NeMTS) | fv<Sort>(NeMTS') .
  eq fv<Sort>(NeMTS / NeMTS') = fv<Sort>(NeMTS) / fv<Sort>(NeMTS') .
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

  op importSet : ImportList -> ModuleDeclSet .
  --------------------------------------------
  eq importSet(nil)     = none .
  eq importSet(I)       = I .
  eq importSet(I I' IL) = I I' importSet(IL) .

  op importList : ModuleDeclSet -> ImportList .
  ---------------------------------------------
  eq importList(I MDS) = I importList(MDS) .  
  eq importList(MDS)   = nil [owise] .

  op asTemplate : Module -> [ModuleTemplate] .
  --------------------------------------------
  eq asTemplate(fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) = (importSet(IL) (sorts SS .) SSDS OPDS MAS EQS) .
  eq asTemplate( mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  = (importSet(IL) (sorts SS .) SSDS OPDS MAS EQS RLS) .

  op fromTemplate : Header ModuleTemplate -> [Module] .
  -----------------------------------------------------
  ceq fromTemplate(H, MTS RLS) =  (mod H is nil sorts none . none none none none none endm)  ++ MTS RLS if not (RLS == none) .
  eq  fromTemplate(H, MTS)     = (fmod H is nil sorts none . none none none none      endfm) ++ MTS     [owise] .

  op _++_ : Module ModuleTemplate -> [Module] [right id: none prec 72] .
  ----------------------------------------------------------------------
  eq (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) ++ (I MDS)             = (fmod H is importList(importSet(IL) I) sorts SS .         SSDS OPDS MAS EQS               endfm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ (I MDS)             =  (mod H is importList(importSet(IL) I) sorts SS .         SSDS OPDS MAS EQS RLS           endm) .
  eq (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) ++ ((sorts SS' .) MDS) = (fmod H is IL                          sorts (SS ; SS') . SSDS OPDS MAS EQS               endfm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ ((sorts SS' .) MDS) =  (mod H is IL                          sorts (SS ; SS') . SSDS OPDS MAS EQS RLS           endm) .
  eq (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) ++ (SSDS' MDS)         = (fmod H is IL                          sorts SS .         SSDS SSDS' OPDS MAS EQS         endfm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ (SSDS' MDS)         =  (mod H is IL                          sorts SS .         SSDS SSDS' OPDS MAS EQS RLS     endm) .
  eq (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) ++ (OPDS' MDS)         = (fmod H is IL                          sorts SS .         SSDS OPDS OPDS' MAS EQS         endfm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ (OPDS' MDS)         =  (mod H is IL                          sorts SS .         SSDS OPDS OPDS' MAS EQS RLS     endm) .
  eq (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) ++ (MAS' MDS)          = (fmod H is IL                          sorts SS .         SSDS OPDS MAS MAS' EQS          endfm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ (MAS' MDS)          =  (mod H is IL                          sorts SS .         SSDS OPDS MAS MAS' EQS RLS      endm) .
  eq (fmod H is IL sorts SS . SSDS OPDS MAS EQS     endfm) ++ (EQS' MDS)          = (fmod H is IL                          sorts SS .         SSDS OPDS MAS EQS EQS'          endfm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ (EQS' MDS)          =  (mod H is IL                          sorts SS .         SSDS OPDS MAS EQS EQS' RLS      endm) .
  eq  (mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)  ++ (RLS' MDS)          =  (mod H is IL                          sorts SS .         SSDS OPDS MAS EQS      RLS RLS' endm) .

  op _++_ : Module Module -> [Module] [assoc prec 73] .
  -----------------------------------------------------
  eq MOD ++ MOD' = MOD ++ asTemplate(MOD') .

  op resolveNames: Module -> [Module] .
  -------------------------------------
  eq resolveNames(MOD) = fromTemplate(getName(MOD), resolveNames(asTemplate(MOD))) .
endfm
```
