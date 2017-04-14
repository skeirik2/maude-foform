Module Expressions
==================

```{.maude .module-exp}
load cterm

fmod MODULE-EXPRESSION is
  protecting CTERM-SET .
  protecting META-LEVEL .

  sorts FreeConstruction ModuleConstruction .
  subsort ModuleExpression < ModuleConstruction .

  var N : Nat . var CTX : Context . var CT : CTerm . var CTS : CTermSet .
  var MC : ModuleConstruction . var FC : FreeConstruction . var ME : ModuleExpression . var H : Header . var ID : Qid .
  var IL : ImportList . vars S S' : Sort . vars SS SS' SS'' : SortSet . var SSDS : SubsortDeclSet .
  var OPDS : OpDeclSet . var MAS : MembAxSet . var EQS : EquationSet . var RLS : RuleSet .
  var NeSS : NeTypeSet . var SUBST : Substitution . var SUBSTS : SubstitutionSet .
  vars T T' : Term . vars NeCTS NeCTS' : NeCTermSet .

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
  op _deriving_ : Module FreeConstruction -> [Module] .
  -----------------------------------------------------
  eq #upModule(MC deriving FC) = #upModule(MC) deriving FC .
  eq fmod H is IL sorts SS .                 SSDS                  OPDS             MAS EQS endfm deriving List(S)
   = fmod H is IL sorts SS ; #ListSorts(S) . SSDS #ListSubsorts(S) OPDS #ListOps(S) MAS EQS endfm .
  eq mod  H is IL sorts SS .                 SSDS                  OPDS             MAS EQS RLS endm deriving List(S)
   = mod  H is IL sorts SS ; #ListSorts(S) . SSDS #ListSubsorts(S) OPDS #ListOps(S) MAS EQS RLS endm .

  op forall_exists_ : Term Term -> FreeConstruction .
  ---------------------------------------------------
  ceq fmod H is IL sorts SS       . SSDS OPDS MAS EQS endfm deriving forall T exists T'
    = fmod H is IL sorts SS ; SS' . SSDS OPDS MAS EQS endfm if SUBST | SUBSTS := #subsumesXWith(upModule('META-MODULE, true), T, upTerm(SS))
                                                           /\ SS'             := #resolveSorts(T' << (SUBST | SUBSTS)) .


  op _<_> : Sort TypeList -> Sort .

  op #resolveSorts : CTermSet -> [SortSet] .
  ------------------------------------------
  eq #resolveSorts(NeCTS ;; NeCTS') = #resolveSorts(NeCTS) ; #resolveSorts(NeCTS') .
  ceq #resolveSorts(CT) = S if S := #resolveSort(downTerm(CT, nil)) .

  op #resolveSort : Sort -> Sort .
  --------------------------------
  eq #resolveSort(S < S' >) = qid(string(S) + "{" + string(S') + "}") .
  eq #resolveSort(S)        = S [owise] .
endfm
```