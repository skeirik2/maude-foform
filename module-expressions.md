Module Expressions
==================

```{.maude .module-exp}
load cterm

fmod MODULE-EXPRESSION is
  protecting CTERM-SET .
  protecting META-LEVEL .

  sorts FreeConstruction ModuleConstruction .
  subsort ModuleExpression < ModuleConstruction .

  var N : Nat . var CTX : Context .
  var MC : ModuleConstruction . var FC : FreeConstruction . var ME : ModuleExpression . var H : Header . var ID : Qid .
  var IL : ImportList . var S : Sort . vars SS SS' SS'' : SortSet . var SSDS : SubsortDeclSet .
  var OPDS : OpDeclSet . var MAS : MembAxSet . var EQS : EquationSet . var RLS : RuleSet .
  var NeSS : NeTypeSet . var SUBST : Substitution . var SUBSTS : SubstitutionSet .

  op #upModule : ModuleConstruction -> Module [memo] .
  ----------------------------------------------------
  eq #upModule(ME) = upModule(ME, true) .
  

  op List : Sort -> FreeConstruction [ctor] .
  op Set  : Sort -> FreeConstruction [ctor] .

  op ditto : -> Attr .

  op #.List  : Sort -> Constant .
  op #NeList : Sort -> Sort .
  op #List   : Sort -> Sort .
  ---------------------------
  eq #.List(S)  = qid(".List{"  + string(S) + "}") .
  eq #NeList(S) = qid("NeList{" + string(S) + "}") .
  eq #List(S)   = qid("List{"   + string(S) + "}") .

  op #ListSorts    : Sort -> SortSet .
  op #ListSubsorts : Sort -> SubsortDeclSet .
  op #ListOps      : Sort -> OpDeclSet .
  op #ListEqs      : Sort -> EquationSet .
  ----------------------------------------
  eq #ListSorts(S)    = #NeList(S) ; #List(S) .
  eq #ListSubsorts(S) = (subsort S < #NeList(S) .)
                        (subsort #NeList(S) < #List(S) .) .
  eq #ListOps(S)      = (op #.List(S) : nil -> #List(S) [ctor] .)
                        (op '_`,_ : #List(S) #List(S)   -> #List(S)   [ctor assoc id(qid(string(#.List(S)) + ".List{PreState}"))] .)
                        (op '_`,_ : #List(S) #NeList(S) -> #NeList(S) [ctor assoc id(qid(string(#.List(S)) + ".List{PreState}"))] .) .

  op _deriving_ : ModuleConstruction FreeConstruction -> ModuleConstruction .
  op _deriving_ : Module FreeConstruction -> Module .
  ---------------------------------------------------
  eq #upModule(MC deriving FC) = #upModule(MC) deriving FC .
  eq fmod H is IL sorts SS .                 SSDS                  OPDS             MAS EQS endfm deriving List(S)
   = fmod H is IL sorts SS ; #ListSorts(S) . SSDS #ListSubsorts(S) OPDS #ListOps(S) MAS EQS endfm .
  eq mod  H is IL sorts SS .                 SSDS                  OPDS             MAS EQS RLS endm deriving List(S)
   = mod  H is IL sorts SS ; #ListSorts(S) . SSDS #ListSubsorts(S) OPDS #ListOps(S) MAS EQS RLS endm .


  op forall_exists_ : SortSet SortSet -> FreeConstruction .
  ---------------------------------------------------------
  ceq fmod H is IL sorts SS        . SSDS OPDS MAS EQS endfm deriving forall SS' exists SS''
    = fmod H is IL sorts SS ; NeSS . SSDS OPDS MAS EQS endfm if SUBST | SUBSTS := #sortMatches(SS', SS)
                                                             /\ NeSS           := downTerm(upTerm(SS'') << (SUBST | SUBSTS), none) .


  op _<_> : Sort TypeList -> Sort .

  op #sortMatches : SortSet SortSet -> SubstitutionSet .
  op #sortMatches : SortSet SortSet Nat -> SubstitutionSet .
  ----------------------------------------------------------
  eq  #sortMatches(SS, SS')    = #sortMatches(SS, SS', 0) .
  ceq #sortMatches(SS, SS', N) = SUBST | #sortMatches(SS, SS', s(N)) if { SUBST , CTX } := metaXmatch(#upModule('META-MODULE), upTerm(SS), upTerm(SS'), nil, 0, 0, N) .
  eq  #sortMatches(SS, SS', N) = empty [owise] .
endfm
```
