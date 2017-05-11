```{.maude .intersection}
load module-template.maude
load full-maude.maude

-----------------------------------------------------
---- Given two order-sorted signatures (as Modules),
---- calculate the intersection of those.
-----------------------------------------------------

fmod INTERSECTION is
  protecting MODULE-TEMPLATE * ( op _;;_ to _;;;_ ) .
  protecting RENAMING-EXPR-EVALUATION .

  ---- Intersection of modules, sorts, subsorts, and ops.

  op intersect : FModule FModule -> FModule .
  op intersect : SortSet SortSet -> SortSet .
  op intersect : SubsortDeclSet SubsortDeclSet -> SubsortDeclSet .
  op intersect : OpDeclSet OpDeclSet -> OpDeclSet .

  vars ME ME' : ModuleExpression .
  vars Header1 Header2 : Qid .
  vars ImportList1 ImportList2 : ImportList .
  vars SortSet1 SortSet2 : SortSet .
  vars SubsortDeclSet1 SubsortDeclSet2 : SubsortDeclSet .
  vars OpDeclSet1 OpDeclSet2 : OpDeclSet .
  vars MembAxSet1 MembAxSet2 : MembAxSet .
  vars EquationSet1 EquationSet2 : EquationSet .

  eq intersect(none, SortSet2) = none .
  eq intersect((S:Sort ; SortSet1), 
               (S:Sort ; SortSet2))
   = S:Sort ; intersect(SortSet1, SortSet2) .
  eq intersect(SortSet1, SortSet2) = none [owise] .

  eq intersect(none, SubsortDeclSet2) = none .
  eq intersect((D:SubsortDecl SubsortDeclSet1),
               (D:SubsortDecl SubsortDeclSet2))
   = D:SubsortDecl intersect(SubsortDeclSet1, SubsortDeclSet2) .
  eq intersect(SubsortDeclSet1, SubsortDeclSet2) = none [owise] .

  eq intersect(none, OpDeclSet2) = none .
  eq intersect((D:OpDecl OpDeclSet1),
               (D:OpDecl OpDeclSet2))
   = D:OpDecl intersect(OpDeclSet1, OpDeclSet2) .
  eq intersect(OpDeclSet1, OpDeclSet2) = none [owise] . 

  eq intersect(
      (fmod Header1 is
         ImportList1
         sorts SortSet1 .
         SubsortDeclSet1
         OpDeclSet1
         MembAxSet1
         EquationSet1
       endfm),
      (fmod Header2 is
         ImportList2
         sorts SortSet2 .
         SubsortDeclSet2
         OpDeclSet2
         MembAxSet2
         EquationSet2
       endfm))
  =   (fmod qid(string(Header1) + " intersect " + string(Header2)) is
         nil
         sorts intersect(SortSet1, SortSet2) .
         intersect(SubsortDeclSet1, SubsortDeclSet2)
         intersect(OpDeclSet1, OpDeclSet2)
         none
         none
       endfm) .

  vars S S1 S2 : Sort . vars M M0 M1 M2 : FModule . var Q Q' : Qid .
  var TL : TypeList .
  vars T : Type .
  var Att : AttrSet .
  var OPDS : OpDeclSet .

  ---- Check whether a sort is in a module.

  op hasSortQ : FModule Sort -> Bool .

  eq hasSortQ(M, S) = S in getSorts(M) .

  ---- Check whether an op is in a module.

  op hasOpQ : FModule Qid -> Bool .
  op hasOpQ : OpDeclSet Qid -> Bool .

  eq hasOpQ(M, Q) = hasOpQ(getOps(M), Q) .

  ceq hasOpQ(((op Q' : nil -> T [Att] .) OPDS), Q) = true
   if Q = qid(string(Q') + "." + string(T)) .
  eq hasOpQ(((op Q  : TL -> T [Att] .) OPDS), Q) = true .
  eq hasOpQ(((op Q' : TL -> T [Att] .) OPDS), Q)
   = hasOpQ(OPDS, Q) .
  eq hasOpQ(OPDS, Q) = false .

  ---- Calculating joint sorts.
  ---- Given two modules M1 and M2, let M0 = intersect(M1, M2).
  ---- Given S is a sort of M1 (or M2), the joint sort of S, 
  ---- denoted as joint_sort(S), is defined as follows.
  ---- (Case A) If S is a sort in M0, then return S.
  ---- (Case B) If S is not a sort of M0, then
  ----     1. Calculate intersect(connected_component(S), getSorts(M0)).
  ----     2. Return the maximal sort (in M0) of the above. 

  op joint-sort : Sort FModule FModule -> Sort .

  ---- Auxiliary functions.
  op joint-sort-aux : FModule SortSet -> Sort .

  ---- (Case A)

  ceq joint-sort(S, M1, M2) = S
   if hasSortQ(intersect(M1, M2), S) .

  ---- (Case B)

  ceq joint-sort(S, M1, M2) 
    = if hasSortQ(M1, S)
      then maximalSorts(M0, kind(intersect(connectedSorts(M1, S), getSorts(M0))))
      else maximalSorts(M0, kind(intersect(connectedSorts(M2, S), getSorts(M0))))
      fi
   if M0 := intersect(M1, M2) .

endfm
---(
reduce intersect(upModule('TEST1, false), upModule('TEST2, false)) == upModule('TEST1-INTERSECT-TEST2, false) .
---)

-----------------------------------------
----     Concrete Module FVAR        ----
---- upModule(FVAR-CONCRETE) is FVAR ----
-----------------------------------------

fmod FVAR-CONCRETE is

  protecting META-LEVEL .
  protecting STRING .
  protecting CONVERSION .
  protecting INTERSECTION .

  vars ME ME' : ModuleExpression .

  ---- Convert a list of terms to a string.
  op #string : TermList -> String .

  eq #string(Q:Qid) = string(Q:Qid) .
  eq #string(Q:Qid[TL:TermList]) 
   = #string(Q:Qid) + "[" + #string(TL:TermList) + "]" .  
  eq #string((T:Term, TL:TermList)) 
   = #string(T:Term) + ", " + #string(TL:TermList) .

  ---- Convert a list of terms to a qid.
  op #qid : TermList -> Qid .
  eq #qid(TL:TermList) = qid(#string(TL:TermList)) .

  ---- Make a Variable.
  *** op #makeVariable : Qid Sort -> Variable .
  op #makeVariable : String Sort -> Variable .
  *** eq #makeVariable(Name:Qid, S:Sort)
  ***  = qid(string(Name:Qid) + ":" + string(S:Sort)) .
  *** eq #makeVariable(Name:String, S:Sort)
  ***  = qid(Name:String + ":" + string(S:Sort)) .

  vars M1 M2 : FModule . var T : Term .

  ---- Calculate the joint-variable of a Term in a signature.

  op joint-variable : ModuleExpression ModuleExpression Term -> Variable .
  eq joint-variable(ME, ME', T) = joint-variable(upModule(ME, true), upModule(ME', true), T) .

  op joint-variable : FModule FModule Term -> Variable .
  eq joint-variable(M1, M2, T)
   = if wellFormed(M1, T)
     then #makeVariable(#string(T), joint-sort(leastSort(M1, T), M1, M2))
     else #makeVariable(#string(T), joint-sort(leastSort(M2, T), M1, M2))
     fi .

endfm
---(
reduce joint-variable(upModule('MYINT-RAT, true),
                      upModule('MYINT-LIST, true),
                      '_/_['_+_['one.NzN,'X:R],'Y:NzR]) .
---)                  
```

```
------------------------------------
---- UniversalConstruction FVAR ----
------------------------------------

fmod FVAR is

  protecting MODULE-EXPRESSION .

  op FVAR : Qid Qid -> UniversalConstruction .

  eq FVAR(MOD1,MOD2) = 
    META-THEORY < MOD1 > ;
    META-THEORY < MOD2 > ;
    exists ( protecting 'META-LEVEL .
             protecting 'STRING .
             protecting 'CONVERSION . )
           ( sorts none . ) ;
    forall ( sorts 'Term ; 'Term{svar('M1)} ; 'Term{svar('M2)} . )
    exists ( sorts 'Variable{svar('M1) svar('M2)} . )
           ( subsorts 'Variable{svar('M1) svar('M2)} < 'Variable{svar('M1)} ; 'Variable{svar('M2)} . ) 
           ( op 'fvar : ( 'Term{svar('M1)} ) ( 'Term{svar('M2)} ) -> 'Variable{svar('M1) svar('M2)} [none] . 
             op 'fvar : 'Term -> 'Variable [none] . 
             op '#string : 'TermList -> 'String [none] . )
           ( eq '#string['Q:Qid] = 'string['Q:Qid] [none] .
             eq '#string['_`,_['T:Term,'TL:TermList]] = '_+_['#string['T:Term],'", ".String,'#string['TL:TermList]] [none] .

endfm
```