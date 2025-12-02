

//////////////////////////////////////////////////////////
intrinsic AllFusionSystemsYT(S::Grp:Examples:=[], SaveEach:=false,Printing:=false,OutFSOrders:=[],OpTriv:=true,pPerfect:= true)-> SeqEnum
{Makes all fusion systems with O_p(F)=1 and O^p(\F)= \F}
 
 
 
FNumber:=0; //This is to help when saving fusion systems
ZZ:= Integers(); //Integer Ring
FF:=Examples; //We will put the possible systems in here  
p:= FactoredOrder(S)[1][1];
 nn:= Valuation(#S,p);
  


//Use that we know fusion systems with an abelian subgroup

if IsAbelian(S) then return FF; end if;

///Lemma~7.1 shows that $S:Z(S) \gt p^2 or |S|\le p^3

if Index(S,Centre(S)) le p^2 and #S ge p^4  then return FF; end if;
 
 

//Here are automorphisms of S and centric subgroups of S
S:= PCGroup(S);

MakeAutos(S);
InnS:=Inn(S);
AutS:= S`autogrp;
map:= S`autopermmap;
AutSp:= S`autoperm;
InnSp:= SubMap(map,AutSp, InnS);

//We use Cor 6.2 from ANTONIO Diaz, ADAM GLESSER, NADIA MAZZA, AND SEJONG PARK
if p ge 5 and #FactoredOrder(S`autogrp) eq 1 then return []; end if;


Sbar, bar:= S/Centre(S);
TT:= Subgroups(Sbar);
SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
 
 
 
 
///////////////////////////////////
///We precalculate certain properties of S. The objective here is to eliminate
///most  p-groups S before we calculate and construct the possible Borel subgroups
///associated with S.
///We do this first as there may be many  of Borel subgroups which we don't need
///to calculate in some circumstances.
/////////////////////////////////////

ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
//
if IsMaximalClass(S) and #S ge p^5 then
    LL:= LowerCentralSeries(S);  
    T:=[];
     Append(~T,Centralizer(S, LL[2],LL[4]));
     C:= Centralizer(S, LL[nn-2]);
     if C in T eq false then
        Append(~T,C); end if;
     T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ]
     cat
     [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ];
      TT:=[];
     for x in T do
            Nx:=Normalizer(S,x);
          A:=AutYX(Nx,x);
          Ap:= SubMap(x`autopermmap,x`autoperm ,A);
          Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
            if not RadTest then continue x; end if;
          Append(~TT,x);
     end for;        
       ProtoEssentials:=   TT;
end if;

ZU:= UpperCentralSeries(S); Z:= ZU[2]; Z2:= ZU[3];    
if IsMaximalClass(S) eq false  or #S le p^4 then  
for x in SS do  
   if x eq S then continue x; end if;
   if IsCyclic(x) then  continue x; end if;
 if IsDihedral(x) and #x ge 8 then  continue x; end if;
 
   Frat:=FrattiniSubgroup(x);

k:= Max({ll: ll in [1..#ZU]|ZU[ll] subset Frat});
   if not ZU[k+1] subset x then continue x; end if;
   Nx:=Normalizer(S,x);
   P:= Index(Nx,x);
   FQTest := Index(x,Frat) ge P^2;
        //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
        //The order of such faithful modules is at least $|\Out_S(x)|^2$.
    if FQTest eq false then continue x; end if;
   CFrat := Centralizer(x,Frat);
   if IsAbelian(Frat) and not (Centralizer(S, CFrat) subset CFrat) then continue x; end if;
   if IsAbelian(Frat) and CommutatorSubgroup(Nx, x) subset CFrat and CommutatorSubgroup(Nx, CFrat) subset Center(CFrat)   
	and CommutatorSubgroup(Center(CFrat), Nx) subset Frat then continue x; end if;

   SylTest, QC:=IsStronglypSylow(Nx/x);
        //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded.
        //Here we check that the Sylow $p$-subgroup is compatible with this.
   if SylTest eq false   then continue x; end if;
   A:=AutYX(Nx,x);
   Ap:= SubMap(x`autopermmap,x`autoperm ,A);
   Inner:= Inn(x);
   Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
    RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
    if not RadTest then continue x; end if;
   if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if;
 
//Here we use information about the action of $N_G(S)$ on a Sylow $p$-subgroup of $SL_2(p^2)$ and other groups
//with a strongly p-embedded N_G(S) with $|S|=p^2$.
if QC eq false and P eq p^2 and IsOdd(p)
          then  
      MM:= MaximalSubgroups(Nx);
       MM:= [y`subgroup: y in MM| x subset y`subgroup];  
      W1:= [x: x in MM| IsIsomorphic(x,MM[1])];
      r:= p+1; s:= ZZ!((p+1)/2);
      if not #W1 in {r,s}  then continue x; end if;
      if #W1 eq r and Index(x,Centre(Rep(W1))) eq p then continue x; end if;
      if #W1 eq s then W2:= Set(MM) diff Set(W1);
         if  Index(x,Centre(Rep(W1))) eq p or Index(x,Centre(Rep(W2))) eq p then continue x; end if;
      end if;
      end if;
if p eq 2 then
ASx, bar := Nx/x; Zx:= Centre(ASx); ZASx:= Inverse(bar)(Zx); 
M:= MaximalSubgroups(ZASx); MM:= {y`subgroup:y in M |x subset y`subgroup};
for aa,bb in MM do if IsIsomorphic(aa,bb) eq false then if Printing then print "here"; end if; continue x; end if; end for;
end if;

   ProtoEssentials:= Append(ProtoEssentials,x);
end for;
end if;
////////////////////////////////
///We need some subgroups in ProtoEssentials;
///////////////////////////////////
 
print #ProtoEssentials;


///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
 
 
if OpTriv and  CharSbgrpTest(ProtoEssentials,S)   then return FF; end if;  
   
 
    ///This test takes Q as the intersection of all the members of the members
    //of ProtoEssentials and checks if any of them are characteristic in all members
    //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

   
if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>;
if  H ne S then return []; end if; end if;
 //This tests is with this set of protoessentials that O^p(\F) <F.
     
/////////////////////
///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials
///////and check that they have strongly p-embedded subgroups.
///////////////////






for i in [1..#ProtoEssentialAutClasses] do
if Printing then print "checking ProtoEssential", i, "of", #ProtoEssentialAutClasses, "Order", #ProtoEssentialAutClasses[i]; end if;
   P:= ProtoEssentialAutClasses[i];
   MakeAutos(P);
   AutP:=P`autogrp;
   mapP:= P`autopermmap;
   AutPp:= P`autoperm;
   InnP:=Inn(P);
   InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
   AutSP:=AutYX(Normalizer(S,P),P );
   AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>; 
   Q:= AutSPp/InnPp;  

   M:=SubnormalClosure(AutPp,AutSPp);
   
   Candidates :=[];
     pVal:=Valuation(#AutPp,p);
     NormVal:=Valuation(#AutSPp,p);
     
        QC:=IsQuaternionOrCyclic(Q);
        if not QC  then
      if #Q eq 9 and #P eq 3^6 and IsElementaryAbelian(P) then
         a,b:= IsIsomorphic(AutPp,GL(6,3));
            if a then  
   AutPCandidates:=[SubInvMap(b,AutPp,x): x in RepsGL63(sub<GL(6,3)|{b(mps): mps in Generators(AutSPp)}>)];  end if;
         else
      // APC:=OverGroupsSylowEmbeddedNonSolv(M,AutSPp,InnPp,p);
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            //So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
           
AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
      APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
      for kk in [1..#AutPCandidates] do  
                  GG:= AutPCandidates[kk];
               Sylow:=SylowSubgroup(GG,p);
                  a,b:=IsConjugate(AutPp,Sylow,AutSPp);
         if a then Append(~APC,GG^b); end if;
      end for;
       AutPCandidates:= APC;
      end if;//#Q eq 9 etc.
       end if;//not QC
               
     if QC and IsCyclic(Q)  then  
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p:Printing:= Printing);
        end if;
   
       if QC and not IsAbelian(Q) then  
      Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
                AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
      APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
      for kk in [1..#AutPCandidates] do  
                  GG:= AutPCandidates[kk];
               Sylow:=SylowSubgroup(GG,p);
                  a,b:=IsConjugate(AutPp,Sylow,AutSPp);
         if a then Append(~APC,GG^b); end if;
      end for;
      AutPCandidates:= APC;
   end if;//QC
   

 
   P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

          for GG in AutPCandidates do
      if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
            NGG:= Normalizer(AutPp,GG);  
            NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)|
                                GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
               for GGs in NGGsubs do
                  Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>);
              end for;
        end for;//GG  
end for;  // i in [1..ProtoEssentialAutClasses]  



ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

if #ProtoEssentialAutClasses eq 0 then return []; end if;
 
 

if OpTriv and CharSbgrpTest(ProtoEssentialAutClasses,S)   then return []; end if;  
if Printing then print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  end if;


//We calculate the possible  subgroups and S pairs.


pVal:= Valuation(#AutSp,p); m:= ZZ!(#AutSp/p^pVal);
BorelsandS:=[];
if m ne 1  then
    if IsSoluble(AutSp) then
        PAut, tt:= PCGroup(AutSp);
        H:=HallSubgroup(PAut,-p);
        K:=[];
        if OutFSOrders eq [] then
         K:= [wx`subgroup:wx in Subgroups(H)];
         else  
        for x in OutFSOrders do K:= K cat [wx`subgroup:wx in
        Subgroups(H:OrderEqual:=x)];
        end for;
        end if;
        BCand:=[];
       
    for k:= 1 to #K do  
        K1:= K[k];
            for K2 in BCand do
            if IsConjugate(PAut,K1,K2) then   continue k;   end if;
            end for;
        Append(~BCand,K1);
    end for;
    BCand:= [SubInvMap(tt, AutSp, K1):K1 in BCand];
 else
  if OutFSOrders eq [] then OutFSOrders:= [1..m]; end if;
    SubsAutS:= Subgroups(AutSp:OrderDividing:=m);  
    BCand:=  [sub<AutSp|x`subgroup,InnSp>: x in SubsAutS|Index(x`subgroup,InnSp meet x`subgroup) mod p ne 0];
    BCand:= [Random(Complements(AA,InnSp)):AA in BCand];
    BCand:=[ AA:AA in BCand| #AA in OutFSOrders];
 end if;
 

 
    for CC in BCand do
    if not IsSoluble(CC) then print "Execution failed: The Borel group is not soluble ";   return []; end if;
        f:=hom<CC->AutS|g:->Inverse(map) (g)>;
        C:= SubMap(f,AutS,CC);  
        if #C ne 1 then B,phiB:= Holomorph(GrpFP,S, sub<AutS|C>); else B,phiB:= Holomorph(S, sub<AutS|C>);  end if;
       // B,phiB:= Holomorph(S, sub<AutS|C>);  
        T:= phiB(S);  
       
         B, theta := PCGroup(B); T:= theta(T); ///This will not work if B is not soluble.
        BB:=[B,T];
       
        a, alpha:= IsIsomorphic(S,T); //phiB*theta does not work when Holomorph is calculcated with FP group
          for x in ProtoEssentialAutClasses do Append(~BB,SubMap(alpha,T,x)); end for;
        for ii in [3..#BB] do
        xx:= BB[ii];
        yy:= ProtoEssentialAutClasses[ii-2];
        MakeAutos(xx);
         
            WW:=[];
            for jj in   [1..#yy`autF] do
          Wx:= yy`autF[jj];
          WGens :=[
          Inverse(alpha)*gamma*alpha: gamma in  Generators(Wx)];
          WW[jj]:=sub<xx`autogrp|WGens>;
            end for;
            xx`autF:= WW;
        end for;
     Append(~BorelsandS,BB);
end for;
else
 T, theta := PCGroup(S);
    BB:=[T,T];
    for x in ProtoEssentialAutClasses do Append(~BB,SubMap( theta,T,x)); end for;
        for ii in [3..#BB] do
            xx:= BB[ii];yy:= ProtoEssentialAutClasses[ii-2]; MakeAutos(xx);WW:=[];
            for jj in   [1..#yy`autF] do
                WGens:=[]; Wx:= yy`autF[jj];
                    for gamma in Generators(Wx) do  
                        Append(~WGens,Inverse( theta)*gamma* theta);
                    end for;
                WW[jj]:=sub<xx`autogrp|WGens>;
            end for;
            xx`autF:= WW;
        end for;
     Append(~BorelsandS,BB);
end if;








if Printing then print "This group has ", #BorelsandS, " Borel groups";end if;

count:=0;
for Bor in BorelsandS do
   

    count := count+1;  
print "**********************************************";
print " Borel", count, "of", #BorelsandS, FactoredOrder(Bor[1]);
print "**********************************************";
 
  B:= Bor[1];    
S:= Bor[2];  

//We use the fact that if $B=S$ and p ge 5 then $O^p(\F)<\F$.
if p ge 5 and B eq S then continue; end if;
MakeAutos(S);
   
     Bbar, bar:= B/Centre(S);
   subsBS:= Subgroups(Bbar:OrderDividing:=#bar(S));
   subsBS:= [Inverse(bar)(x`subgroup):x in subsBS];
   SS:= [x:x in subsBS|IsSCentric(S,x)];
    AutFS:=AutYX(B,S);
    InnS:=Inn(S);
    AutS:= S`autogrp;
    alpha:= S`autopermmap;
    AutSp:= S`autoperm;
    InnSp:= SubMap(alpha,AutSp, InnS);
    AutBS:= AutYX(B,S);
    AutBp:= SubMap(alpha,AutSp, AutBS);
 
    NAutBp:= Normalizer(AutSp,AutBp);
    NAutB:= SubInvMap(alpha,AutS,NAutBp);
    ProtoEssentialAutClasses:=[Bor[j]:j in [3 ..#Bor]];

//We explode the autclasses to get all protoessentials and ajoin their potential autogrps.
ProtoEssentials:=[];
for x in ProtoEssentialAutClasses do
    Xx, Stx, Rx := AutOrbit(S,x,S`autogrp);
    PNew := [];
    for y in SS do
        if y in Xx then
            MakeAutos(y);
            Append(~ProtoEssentials,y);
            Append(~PNew,y);
        end if;
    end for;
   
    if #PNew ne 0 then
        for j := 1 to #PNew do
            y:= PNew[j];
            y`autF:=[];
            for AP in x`autF do
                        y`autF := Append(y`autF, sub<y`autogrp|[Inverse(Rx[Index(Xx,y)])*gamma*Rx[Index(Xx,y)]: gamma in Generators(AP)]>);
            end for;
        end for;
    end if;
end for;//x


if OpTriv then
//The next test uses Lemma 4.10 to show that P1 and P2 are not both essential.
// If P1 is essential, then P1' ne 1 and is normalized by Aut_\F(S) and Aut_F(E_1). This gives O_p(F) ne 1.
   if #ProtoEssentials eq 2 and p ge 5 and #S lt p^(p+3) then
       P1:= ProtoEssentials[1];
       P2:= ProtoEssentials[2];
        if #P1 le #P2 then PP:= P2; P2:= P1; P2:= PP; end if;
       NSP2:= Normalizer(S,P2);  
       PC:= Core(S,P2);
       if IsConjugate(B,P1,NSP2) and Index(NSP2,P2) eq p and Index(S,NSP2) eq p and
       Index(P2,PC) eq p and IsCharacteristic(NSP2,PC) and IsNormal(B,DerivedSubgroup(P1)) then      ProtoEssentials:=[P2];
        end if;
   end if;    
end if; //OpTriv
   








Candidates:= AssociativeArray(ProtoEssentials);

for x in ProtoEssentials do Candidates[x]:= x`autF; end for;

if pPerfect then
//The next check is a preliminary focal subgroup check using that we know the Borel  subgroup.
//This often gets rid of the case when $B=S$
   SB:= CommutatorSubgroup(S,B);
   S1:= sub<S|SB,ProtoEssentials>;
   if S1 ne S then   continue Bor; end if;
end if;

if OpTriv   and #ProtoEssentials eq 1   and IsNormal(B,ProtoEssentials[1]) then continue Bor; end if;
 


if Printing then print "There are", #ProtoEssentials, "proto-essential subgroups before the extension test.\nThey have orders",
 Explode([#ProtoEssentials[i]: i in [1..#ProtoEssentials]]);end if;

//We now make all the candidates for Aut_F(E) given our class representatives in
//E`autF. This means that we check if the automorphisms in $Aut(N_B(E),E)$ restrict to members of $\Aut_\F(E)$.

FirstTime := true;
ProtoEssentialsT:= ProtoEssentials;
ProtoEssentialsTT:= [];

while #ProtoEssentialsT ne #ProtoEssentialsTT  do
    ProtoEssentialsTT:= ProtoEssentialsT;
   
   if #ProtoEssentialsT eq 0 then
    if Printing then  print #ProtoEssentialsT, "proto-essentials which pass the  strongly p-embedded and extension test";
    end if; continue Bor;
    end if;
 
    Candidates1:=AssociativeArray(ProtoEssentialsT);
   
    Done :={};
    for i in [1..#ProtoEssentialsT] do
        P:=ProtoEssentialsT[i];
        if P in Done then continue i; end if;
        MakeAutos(P);
         if Printing then print "About to Apply AutFPC"; end if;
        Candidates1[P]:=AutFPCandidates(B,S,P,ProtoEssentialsT,Candidates,FirstTime:Printing:= Printing);
        //next we transfer the automorphisms to everything in the AutOrbit.
         if Printing then print "AutFPC complete"; end if;
        OrbP, SSt, Repp:= AutOrbit(S,P, NAutB);
        if Printing then print "the set Repp has", #Repp, "Members"; end if;
        for nn in [2..#Repp] do
            P1:=OrbP[nn];
            MakeAutos(P1);
            beta:= Repp[nn];
            Candidates1[P1]:= [];
            for AP in Candidates1[P] do
                Append(~Candidates1[OrbP[nn]],
                        sub<P1`autogrp|[Inverse(beta)*theta*beta: theta in Generators(AP)]>);
            end for;
        end for;
    Done := Done join Seqset(OrbP);
     if Printing then print "the set Done", #Done, "Members"; end if;
    end for; //i
  ProtoEssentialsT:=[ProtoEssentialsT[Index(ProtoEssentialsT,x)]:x in ProtoEssentialsT| #Candidates1[x] ne 0];
Candidates:= Candidates1; FirstTime:=false;
end while;    

 

ProtoEssentials:= ProtoEssentialsT;
if #ProtoEssentials eq 0 then continue Bor; end if;

if Printing then print  #ProtoEssentialsT,
"proto-essentials which pass both the  strongly p-embedded
and extension test";end if;

 		
D:= Subsets({1..#ProtoEssentials});



////////////////////////////////
///We look at the orbits of $N_Aut(S)(Aut_\F(S))$ on D.
///As we will consider all possible automisers of members of protoessentials
///It suffices to look at $N_Aut(S)(Aut_\F(S))$ orbits and this will give us all
///automorphism classes of fusion systems
//////////////////////////

NN:= NAutBp;
for Pr in ProtoEssentials do
a, NNN:= AutOrbit(S,Pr,NAutB);
NN := NN meet SubMap(alpha,AutSp,NNN);
end for;

   // NN:= sub<NAutBp|NN>;
TNB:= Transversal(NAutBp,NN);
TransAutSB:=[Inverse(alpha)(xxx):xxx in TNB];

DD:= D;
DNew:={};
while #DD ne 0 do
    x:= Rep(DD);
    DNew:= DNew join{x};
    DDD:={x};
   
    for beta in TransAutSB do
   xnew := {beta(ProtoEssentials[w]):w in x};
     L:={};
   for ll in xnew do
      for Proto in ProtoEssentials do
      aa, bb:= IsConjugate(B, ll, Proto);
         if aa then L:= L join{Index(ProtoEssentials,Proto)}; end if;
      end for;
   end for;
 

DDD:= DDD join {L};  
   end for; //beta
DD := DD diff DDD;
end while;

 
D:= DNew;
 
D:= Setseq(D);
 D1:= [#x:x in D];
ParallelSort(~D1,~D);
D:=Reverse(D);

 // this tests if there is a conjugate of essential x  which is $B$ conjugate to a subgroup of essential $y$ which using all posibilities for Aut_\F(y) is we can see $x$ is not fully Normalized
 Forbiddenpairs :={};
 
 for x in ProtoEssentials do
    NSx := Normalizer(S,x);
    for y in ProtoEssentials do
        if exists(tt){ tt: tt in Conjugates(B,x)|tt subset y} then
            if forall{w:w in Candidates[y]| exists{cc:cc in AutOrbit(y,tt,w)|#Normaliser(S,cc) gt #NSx}}
            then Forbiddenpairs:= Forbiddenpairs join{{x,y}};
            end if;
        end if;
    end for;
end for;
if Printing then print "The number of forbidden pairs of essential subgroups is ", #Forbiddenpairs;end if;
/////


////////////////Main Search starts here.



for ss in [1..#D] do//This is the main loop considering all subsets of ProtoEssentials
    EssSup:= D[ss];//This set specifies which essential subgroups we select from ProtoEssentials.

    if #EssSup eq 0 then continue ss;
    end if; //the fusion system must have rank at least one
    ssSequence:=SetToSequence(EssSup);
   
    Essentials:=[ProtoEssentials[i]: i in EssSup];
   if OpTriv then if #EssSup eq 1 and IsNormal(B,Essentials[1]) then continue ss; end if;end if;
    if exists{w: w in Forbiddenpairs| w subset Essentials} then continue ss; end if;

  max:= Max({#e: e in Essentials});
Candidates1:=Candidates;
Maxes:= {e:e in Essentials|#e eq max};


FLAG := false;
for P in Essentials do
    if p*#P ge max and IsNormal(S,P) eq false  then  
         PB:= Conjugates(B,P);
         Tst:={};  
         for M in Maxes do
            Tst := Tst join {x subset M:x in PB};
         end for;
          if Tst eq {false} or P in Maxes then
            MakeAutos(P);
            AutP:=P`autogrp;
            mapP:= P`autopermmap;
            AutPp:= P`autoperm;
            InnP:=AutYX(P,P);
            InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
            AutSP:=AutYX(Normalizer(S,P),P );
            AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>;
            AutBP:=AutYX(Normalizer(B,P),P );
            AutBPp:=sub<P`autoperm|{mapP(g): g in Generators(AutBP)}>;
            for II in [1.. #Candidates[P]] do AP:= Candidates[P][II];
                APp:=SubMap(P`autopermmap, P `autoperm,AP);
                 if Normalizer(APp,AutSPp) ne AutBPp then
                     Candidates1[P][II]:=sub<AP|>; FLAG:= true;
                 end if;
            end for;//II
        end if;// #Tst;
    end if;
end for;            
       
       
if FLAG then
CandidatesNew:=AssociativeArray(ProtoEssentials);
for x in ProtoEssentials do
CandidatesNew[x]:=[];
for y in Candidates1[x] do if #y ne 1 then Append(~CandidatesNew[x],y); end if; end for;
end for;
else CandidatesNew:=Candidates;
end if;
 

 
////This next test makes sure that if we have essential subgroups x<y then
////|N_S(x)|\ge  N_S(x\alpha) for all alpha in $\Aut_F(y)$
Candidates1 := CandidatesNew;

FLAG := false;
for x in Essentials do
    for y in Essentials do
    if x subset y and x ne y then
        for II in [1..#CandidatesNew[y]] do AutFy:= CandidatesNew[y][II];
            xOrb:= AutOrbit(y,x,AutFy);
            for w in xOrb do  
                if #Normalizer(S,w) gt #Normalizer(S,x) then    
                    Candidates1[y][II]:=sub<AutFy|>; FLAG:= true;
                end if;
            end for;
        end for;
    end if;
    end for;
end for;


if FLAG then
CandidatesNew:=AssociativeArray(ProtoEssentials);
for x in ProtoEssentials do
    CandidatesNew[x]:=[];
    for y in Candidates1[x] do
        if #y ne 1 then Append(~CandidatesNew[x],y);
        end if;
    end for;
end for;
end if;
 
 
 
 
CandidatesNewp:= AssociativeArray(ProtoEssentials);


for xP in ProtoEssentials do
    CandidatesNewp[xP]:=[ SubMap(xP`autopermmap, xP`autoperm,CandidatesNew[xP][kk]): kk in [1..#CandidatesNew[xP]]];
   
end for;

 
 

 
 
  Cart:=[];
  for e in EssSup do
    Cart:=Append(Cart,[1..#CandidatesNew[ProtoEssentials[e]]]);
  end for;

 CPCart:=CartesianProduct(Cart);

     // now run through all possible fusion systems on the chosen set of essential subgoups
 
if Printing then print "Checking", #CPCart, "automizer sequences with", #EssSup,
"essentials of orders:", Explode([#ProtoEssentials[i]: i in EssSup]);end if;


/////////////////////////////////////////////////////////////////////////////////
/////for each subset we make a cartesian product, where each element gives a
///// potential fusion system
///// The set EssSup, Essentials support, defines the essentials subgroups of the fusion system
/////  For each EssSup we run through the various assignments of automisers to the essentials
//////For example if EssSup<--> [S,E_1,dots, E_k] then we run through all the possibilities for
//// Aut_F(E_1) ...
/////////////////////////////////////////////////////////////////////////////////
 

//First we make the subgroup of Aut(S) which normalizes all the essential subgroups and B.

NAutBQp:=NAutBp;

for Q in Essentials do
Orb, NN:=AutOrbit(S, Q,NAutB);
NAutBQp:= NAutBQp meet SubMap(S`autopermmap, S`autoperm,NN);
end for;


T2:= Transversal(NAutBp,NAutBQp);
L:= Set(Essentials);
T3:= {y: y in T2|{Inverse(alpha)(y)(x): x in L} eq  L};
NAutBQp:= sub<NAutBp|NAutBQp,T3>;


NAutBQ:= SubInvMap( alpha, S`autogrp,NAutBQp);


CPCart:= Set(CPCart);

cpc:= #CPCart;
 
//This defines an action of CPCart
  alpha:=S`autopermmap;
  function Act(x)
     tup:= x[1];ff:= x[1];
     theta := x[2];
     for i in [1..#Essentials] do
               ee:= Essentials[i];  
               jj:= Index(Essentials,SubMap(theta,S,ee));
               eee:= Essentials[jj];  
                J:= sub<eee`autogrp|[Inverse(theta)*gen*theta:gen in
                Generators(CandidatesNew[ee][ff[i]])]>;
                Jp:= SubMap(eee`autopermmap, eee`autoperm,J);
                kk:= Index(CandidatesNewp[eee],Jp);
                jjj:= Index(Essentials,eee);
                tup[jjj]:=kk;
            end for;
            return tup;
 end function;

 
 
 
 
 
  while #CPCart ne 0 do  
   Bob:= false;
   possFSys:=Rep(CPCart);
 
  //POrb is a partial orbit.  This speeds things up as finding large  full orbits seems to be more time consuming. This routine will with high probability find small orbits anyway. The strange choice to perform it twice is to get a balance between speed and getting enough elements of the orbit.

     POrb:= {possFSys, Act(<possFSys,NAutBQ.1>)  };
     for i:= 1 to 2 do
      POrb2:= POrb;
      for x in Generators(NAutBQ) do;
         for ff in POrb2 do
            z:= Act(<ff,x>);
            if not z in CPCart then Bob := true; break i; end if;
            POrb:= POrb join {z};
         end for;
   end for;
     end for;
     if Bob then CPCart:= CPCart diff POrb;continue; end if;//continues while
   Bob:= false;
     POrb2:= POrb;
     for j := 1 to 3 do
      x:= Random(Generators(NAutBQ));
      POrb2:= POrb;
      for ff in POrb2 do
            z:= Act(<ff,x>);
            if not z in CPCart then Bob := true; break j; end if;
            POrb:= POrb join {z};
         end for;
     end for;
 
 
   CPCart:= CPCart diff POrb; //removes the partial orbit
   if Bob then continue; end if;//continues while
   Bob:= false;
   
    AutF:=AssociativeArray(ProtoEssentials); //this is the fusion system we will make
    AutF[S]:=AutFS; // this was fixed at the start it is Aut_B(S)
    ////We now populate AutF with the appropriate candidate automisers
    for k in [1..#possFSys] do
       AutF[ProtoEssentials[ssSequence[k]]]:=CandidatesNew[ProtoEssentials[ssSequence[k]]][possFSys[k]];
    end for;
    Autos:=[AutF[S]]; ///Autos is the automiser sequence.
           
   for e in Essentials do
          Autos:= Append(Autos,AutF[e]);    
    end for;
     
   if Printing then print "Remains to do",#CPCart, "of",cpc; end if;
     
   if pPerfect and not FocalSubgroupTest(B,S, Essentials,AutF) then  continue; //while
   end if;  


    if OpTriv and  not FCoreTest(S,Essentials,AutF) then  continue; end if;  


  //    This next test checks that if P is normal in S that its "obvious" automiser has $\Aut_S(P) as a Sylow.
   
    for xx in SS do
        if IsNormal(S,xx) eq false or #xx eq 1 then continue xx; end if;
        Exx:={w:w in Essentials|xx subset w};
        if #Exx ne 0 then
            MakeAutos(xx);
            Axx:= sub<xx`autogrp|AutYX(Normalizer(B,xx),xx)>;
            for yy in Exx do
                Oxx,xxStab := AutOrbit(yy, xx,AutF[yy]);
                Axx:= sub<xx`autogrp|Axx,Generators(xxStab)>;
            end for;
            if ZZ!(#Axx/#AutYX(S,xx)) mod p eq 0 then Bob:= true; break xx; end if;
        end if;
    end for;
   if Bob then continue; end if;//continues while
   Bob:= false;
     
//    

 
    N:= {1..#Essentials};
   NN:= Subsets(N);
   NN:= Setseq(NN);
   RO:=[#x:x in NN];
     ParallelSort(~RO,~NN);
   NN:= Reverse(NN);
       
      for sNN in NN do
                    if #sNN eq 0 or #sNN eq #Essentials then continue sNN; end if;
                    Es:=[Essentials[ww]: ww in sNN];Append(~Es,S);
                    AutE:= [Autos[ww+1]:ww in sNN];Append(~AutE,AutF[S]);
                    Cor,AutCor:= AutFCore(Es,AutE);
                    n:=ZZ!(#AutCor/#AutYX(S,Cor));
                    if n mod p eq 0 then  Bob:=true; break sNN; end if;///Tests if Aut_S(x) a sylow p of AutCore.
        end for;//sNN
           
           if Bob then continue; end if;//continues while
            Bob:=false;
           
           
           
//We now create the fusion system. We don't use the standard call as we have already done most of the calculation



bounds:=[8,6,6,6];
primes:=[2,3,4,4];
///Puts the essentials in the standard order using group names.  
//This will break if order of S is too big. Hence the else below
 
if p in primes and #S le p^bounds[Index(primes,p)]  then  
RO:=[IdentifyGroup( Group(x)):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
else
RO:=[#Group(x):x in Autos];
ParallelSort(~RO,~Autos);
Reverse(~Autos);
end if;
   
F:= New(FusionSystem);
F`prime:=p;
F`group:= S;    
F`borel:= B;
F`subgroups:=[x:x in subsBS];
F`essentialautos:= Autos;
F`essentials := [];
for x in Autos do
Append(~F`essentials, Group(x)); end for;
F`AutF:= AssociativeArray(F`subgroups);
for x in F`essentials do
F`AutF[x] := F`essentialautos[Index(F`essentials,x)];
end for;
       //We only need  to check saturation on centrics. So we make a partial fusion graph.      
if assigned(F`fusiongraph) eq false then  
    F`fusiongraph,F`maps:= FusionGraphSCentrics(F);
end if;
F`classes:= ConnectedComponents(F`fusiongraph);
       
        if assigned(F`centrics) eq false then
            F`centrics:={x:x in F`subgroups|IsCentric(F,x)}; end if;

                  for G in FF do
                          if IsIsomorphic(F,G) then delete F; Bob:= true; break; end if;
                  end for;
                  if Bob then continue; end if;Bob:=false;
            IS:= IsSaturated(F);
            if Printing then print "Executed saturation test: result is",IS; end if;
                if assigned(F`essentials) and IS then  
                 if SaveEach then FNumber:= FNumber +1;
                        SaveAsGo(FNumber, F);  
                        else    
                        Append(~FF,F);
                    end if;
                end if;
 delete F;
   end while; //  possFSys
 
end for;//ss
end for;//Bor

GG:= FF;
if #FF le 1 then return FF; end if;
FF:= [FF[1]];
 for i in [2.. #GG] do
   x:= GG[i];  
   for y in FF do
      if IsIsomorphic(x,y) then continue i; end if;
   end for;
   Append(~FF,x);
 end for;
 
return FF;
end intrinsic;


intrinsic IsDihedral (G::Grp)->Bool
{Checks is a group is Dihedral}
n:= #G;n := Integers()!(n/2);
if n le 2 then return false;end if;
tt:= IsIsomorphic(G,DihedralGroup(n));
return tt;
end intrinsic;

intrinsic IsSemiDihedral (G::Grp)->Bool
{Checks is a group is semidihedral}
n:= #G;
if n lt 8 then return false;end if;
if n eq 2^Ilog2(n) then H:=Group<a,b|a^(Integers()!(n/2))=b^2=1,b*a*b=a^(Integers()!(n/4)-1)>;
else return false;
end if;
H:=PCGroup(H);
tt:= IsIsomorphic(G,H);
return tt;
end intrinsic;

intrinsic IsWreathProductofC2 (G::Grp)->Bool
{Checks is a group is wreath product of C2}
n:= #G; m:=Ilog2(n);
if n lt 8 then return false;end if;
if IsEven(m) then return false;
elif n eq 2^m then H:=PrimitiveWreathProduct(CyclicGroup(2^Integers()!((m-1)/2)),CyclicGroup(2));
else return false;
end if;
tt:= IsIsomorphic(G,H);
return tt;
end intrinsic;




intrinsic IsDirectProduct (G::Grp)->Bool,SeqEnum{}
////Checks if a group is a direct product of normal subgroups
N:=NormalSubgroups(G);
NP:=[<N[i]`subgroup,N[j]`subgroup>:i in [2..(#N-1)],j in [2..(#N-1)]|i le j];
PR:=[];
for i in [1..#NP] do
if #NP[i][1]*#NP[i][2] ne #G then
continue;
end if;
if #(NP[i][1] meet NP[i][2]) eq 1 then
PR:=Append(PR,<NP[i][1],NP[i][2]>);
end if;
end for;
if #PR eq 0 then return false,_;
else return true,PR;
end if;
end intrinsic;




intrinsic IsSplitFus1 (G::Grp)->Bool,SeqEnum{}
////Checks if a group satisfy split-fus thm1
N:=NormalSubgroups(G);
NP:=[<N[i]`subgroup,N[j]`subgroup>:i in [2..(#N-1)],j in [2..(#N-1)]|i le j];
PR:=[];
for i in [1..#NP] do
if #NP[i][1]*#NP[i][2] ne #G then
continue;
end if;
if #(NP[i][1] meet NP[i][2]) eq 1 then
PR:=Append(PR,<NP[i][1],NP[i][2]>);
end if;
end for;
if #PR eq 0 then return false;
end if;

if #PR ne 0 then
PRR:=[PR[1]];
for i in [1..#PR] do
 for j in [1..#PRR] do
 if IsIsomorphic(PR[i][1],PRR[j][1])
 then break;
end if; 
if j le (#PRR-1)
 then continue;
end if;
PRR:=Append(PRR,PR[i]);
end for;
end for;
end if;

//Indecomposable test


for i in [1..#PRR] do 
if IsDirectProduct(PRR[i][1]) or IsDirectProduct(PRR[i][2]) then
return false;
end if;
end for;

//Condition 1

I1:=[];
for i in [1..#PRR] do
EAZ1:=AbelianSubgroups(Center(PRR[i][1]));
O1:=Max({#x`subgroup:x in EAZ1|IsElementaryAbelian(x`subgroup)});
EZ1:=AbelianSubgroups(Center(PRR[i][1]):OrderEqual:=O1);
m:=Ilog2(O1);
for j in [1..#EZ1] do
if #Generators(EZ1[j]`subgroup) eq m then 
H11:=EZ1[1]`subgroup;
end if;
end for;
H12:=DerivedSubgroup(PRR[i][1]);
if H11 subset H12 then continue;
else I1:=Append(I1,i);
end if;
end for;

for j in [1..#I1] do
	x:=Max(I1);
	PRR:=Remove(PRR,x);
	I1:=Remove(I1,#I1);
end for;

I1:=[];
for i in [1..#PRR] do
EAZ2:=AbelianSubgroups(Center(PRR[i][2]));
O2:=Max({#x`subgroup:x in EAZ2|IsElementaryAbelian(x`subgroup)});
EZ2:=AbelianSubgroups(Center(PRR[i][2]):OrderEqual:=O2);
m:=Ilog2(O2);
for j in [1..#EZ2] do
if #Generators(EZ2[j]`subgroup) eq m then 
H21:=EZ2[1]`subgroup;
end if;
end for;

H22:=DerivedSubgroup(PRR[i][2]);
if H21 subset H22 then continue;
else PRR:=Remove(PRR,i);
end if;
end for;

for j in [1..#I1] do
	x:=Max(I1);
	PRR:=Remove(PRR,x);
	I1:=Remove(I1,#I1);
end for;


if #PRR eq 0 then return false;
end if;

//Condition 1 finished
//Condition 2 as follow


for i in [1..#PRR] do
if #PRR[i][1]^2 gt #PRR[i][2] then return true,[PRR[i]];
end if;
SS:=Subgroups(PRR[i][2]:OrderEqual:=#PRR[i][1]^2);
for j in [1..#SS] do
if IsIsomorphic(DirectProduct(PRR[i][1],PRR[i][1]),SS[j]`subgroup) then
break;
end if;
if j le (#SS-1) then continue;
else return true,[PRR[i]];
end if;
end for;
end for;

if #PRR eq 0 then return false;
end if;

return false;

end intrinsic;


intrinsic IsSplitFus2 (G::Grp)->Bool,SeqEnum{}
////Checks if a group satisfy split-fus thm2
N:=NormalSubgroups(G);
NP:=[<N[i]`subgroup,N[j]`subgroup>:i in [2..(#N-1)],j in [2..(#N-1)]|i le j];
PR:=[];
for i in [1..#NP] do
if #NP[i][1]*#NP[i][2] ne #G then
continue;
end if;
if #(NP[i][1] meet NP[i][2]) eq 1 then
PR:=Append(PR,<NP[i][1],NP[i][2]>);
end if;
end for;
if #PR eq 0 then return false;
end if;

if #PR ne 0 then
PRR:=[PR[1]];
for i in [1..#PR] do
 for j in [1..#PRR] do
 if IsIsomorphic(PR[i][1],PRR[j][1])
 then break;
end if; 
if j le (#PRR-1)
 then continue;
end if;
PRR:=Append(PRR,PR[i]);
end for;
end for;
end if;

//Indecomposable test

for i in [1..#PRR] do 
if IsDirectProduct(PRR[i][1]) or IsDirectProduct(PRR[i][2]) then
return false;
end if;
end for;


PRR1:=[];
for i in [1..#PRR] do
if IsDihedral(PRR[i][1]) or IsSemiDihedral(PRR[i][1]) or IsWreathProductofC2(PRR[i][1])
then PRR1:=Append(PRR1,PRR[i]);
end if;
end for;

PRR2:=[];
for k in [1..#PRR] do
if IsDihedral(PRR[k][2]) or IsSemiDihedral(PRR[k][2]) or IsWreathProductofC2(PRR[k][2])
then PRR2:=Append(PRR2,PRR[k]);
end if;
end for;



//Condition 1 finished
//Condition 2 as follow

I1:=[];
for i in [1..#PRR1] do
if #PRR1[i][1]^2 gt #PRR1[i][2] then return true,[PRR1[i]];
end if;
SS:=Subgroups(PRR1[i][2]:OrderEqual:=#PRR1[i][1]^2);
for j in [1..#SS] do
if IsIsomorphic(DirectProduct(PRR1[i][1],PRR1[i][1]),SS[j]`subgroup) then Append(~I1,i);
break;
end if;
if j le (#SS-1) then continue;
else return true,[PRR1[i]];
end if;
end for;
end for;

for j in [1..#I1] do
	x:=Max(I1);
	PRR1:=Remove(PRR1,x);
	I1:=Remove(I1,#I1);
end for;

I2:=[];
for i in [1..#PRR2] do
if #PRR2[i][2]^2 gt #PRR2[i][1] then return true,[PRR2[i]];
end if;
SS:=Subgroups(PRR2[i][1]:OrderEqual:=#PRR2[i][2]^2);
for j in [1..#SS] do
if IsIsomorphic(DirectProduct(PRR2[i][2],PRR2[i][2]),SS[j]`subgroup) then Append(~I2,i);
break;
end if;
if j le (#SS-1) then continue;
else return true,[PRR2[i]];
end if;
end for;
end for;

for j in [1..#I2] do
	x:=Max(I2);
	PRR2:=Remove(PRR2,x);
	I2:=Remove(I2,#I2);
end for;


if #PRR1 eq 0 and #PRR2 eq 0 then return false;
end if;

return false;
end intrinsic;


intrinsic DirectProductofFusionSystems(F1,F2::FusionSystem)-> FusionSystem{}
E1:= F1`essentialautos;
E2:= F2`essentialautos;

S1 := Group(E1[1]);
S2 := Group(E2[1]);

S,p:= DirectProduct(S1,S2);

B:= [];

for jj in [1..#E1] do

A:=[];
T1:= Group(E1[jj]);
U:=sub<S|p[1](T1),p[2](S2)>;
MakeAutos(U);
for t in Generators(E1[jj]) do
 I :=[];
   	for i in {1..#PCGenerators(T1)} do
	Append(~I,<p[1](T1.i),p[1](t(T1.i))>);
	end for;

	for i in [#PCGenerators(T1)+1..#PCGenerators(T1) +#PCGenerators(S2)] do 
	Append(~I,<p[2](S2.(i-#PCGenerators(T1))),p[2](S2.(i-#PCGenerators(T1)))>);
	end for;
b:=hom<U->U|I>;

   	Append(~A,b);A;
end for;//t 
	 
for t in Generators(E2[1]) do

I:=[];
for i in {1..#PCGenerators(T1)} do
	Append(~I,<p[1](T1.i),p[1]((T1.i))>);
	end for;

	for i in [#PCGenerators(T1)+1..#PCGenerators(T1) +#PCGenerators(S2)] do 
	Append(~I,<p[2](S2.(i-#PCGenerators(T1))),p[2](t(S2.(i-#PCGenerators(T1))))>);
	end for;
b:=hom<U->U|I>;
Append(~A,b);
end for;//t
B[jj] := sub<U`autogrp|A>;
end for;//jj

for jj in [2..#E2] do

A:=[];
T2:= Group(E2[jj]);
U:=sub<S|p[1](S1),p[2](T2)>;
MakeAutos(U);
for t in Generators(E1[1]) do
 I :=[];
   	for i in {1..#PCGenerators(S1)} do
	Append(~I,<p[1](S1.i),p[1](t(S1.i))>);
	end for;

	for i in [#PCGenerators(S1)+1..#PCGenerators(S1) +#PCGenerators(T2)] do 
	Append(~I,<p[2](T2.(i-#PCGenerators(S1))),p[2](T2.(i-#PCGenerators(S1)))>);
	end for;
b:=hom<U->U|I>;

   	Append(~A,b);A;
end for;//t 
	 
for t in Generators(E2[jj]) do

	I:=[];
	for i in {1..#PCGenerators(S1)} do
	Append(~I,<p[1](S1.i),p[1]((S1.i))>);
	end for;

	for i in [#PCGenerators(S1)+1..#PCGenerators(S1) +#PCGenerators(T2)] do 
	Append(~I,<p[2](T2.(i-#PCGenerators(S1))),p[2](t(T2.(i-#PCGenerators(S1))))>);
	end for;
b:=hom<U->U|I>;
Append(~A,b);
end for;//t
B[jj-1+#E1] := sub<U`autogrp|A>;
end for;//jj

F:=CreateFusionSystem(B);
F`saturated:= true;

return F;
end intrinsic;




intrinsic AllSplitFusionSystems(S::Grp:OpTriv:=true)-> SeqEnum
{Makes all split fusion systems with O^p(\F)=O^p'(\F)= \F}
if IsSplitFus1(S) eq false and IsSplitFus2(S) eq false then return [];
print "S does not pass both split fusion systems tests";
end if;

N:=NormalSubgroups(S);
NP:=[<N[i]`subgroup,N[j]`subgroup>:i in [2..(#N-1)],j in [2..(#N-1)]|i le j];
PR:=[];
for i in [1..#NP] do
if #NP[i][1]*#NP[i][2] ne #S then
continue;
end if;
if IsIsomorphic(S,sub<S|NP[i][1],NP[i][2]>) then
PR:=Append(PR,<NP[i][1],NP[i][2]>);
end if;
end for;

if #PR ne 0 then
PRR:=[PR[1]];
for i in [1..#PR] do
 for j in [1..#PRR] do
 if IsIsomorphic(PR[i][1],PRR[j][1])
 then break;
end if; 
if j le (#PRR-1)
 then continue;
end if;
PRR:=Append(PRR,PR[i]);
end for;
end for;
end if;



//Refinement of Pairs finished.

if OpTriv then PF:=[AllFusionSystems(PRR[1][1]),AllFusionSystems(PRR[1][2])];
else PF:=[AllFusionSystems(PRR[1][1]:OpTriv:=false),AllFusionSystems(PRR[1][2]:OpTriv:=false)];
end if;

if #PF[1] eq 0 or #PF[2] eq 0 then return [];
end if;

F:=[];
for i in [1..#PF[1]] do
for j in [1..#PF[2]] do
F:=Append(F,DirectProductofFusionSystems(PF[1][i],PF[2][j]));
end for;
end for;

return F;
 
end intrinsic;





intrinsic CentralTransfer (S::Grp)-> Bool{}
Z:=Omega(Centre(S),1);
D:=DerivedSubgroup(S);
if Z subset D then 
return false;
end if;
R,phi:=S/D;
A:=Subgroups(R);
AA:={x`subgroup:x in A};
AAA:={x: x in AA| IsCyclic(R/x) and x ne R};
B:={Inverse(phi)(x): x in AAA};
BB:={x:x in B|not Z subset x};
for T in BB do
	y:=Z meet T;
	if y subset D then return true;
	end if;
end for;


return false;
end intrinsic;



intrinsic CentralTransferhard (S::Grp)-> Bool{}
Z:=Omega(Centre(S),1);
D:=DerivedSubgroup(S);
if Z subset D then 
return false;
end if;
R,phi:=S/D;
A:=Subgroups(R);
AA:={x`subgroup:x in A};
AAA:={x: x in AA| IsCyclic(R/x) and x ne R};
B:={Inverse(phi)(x): x in AAA};
BB:={x:x in B|not Z subset x};
SS:=NormalSubgroups(S);
SSS:={x`subgroup:x in SS|IsCharacteristic(S,x`subgroup) and x`subgroup ne S};

for T in BB do
	y:=Z meet T;
	if exists(K){K:K in SSS| y subset K and not Z subset K} then return true;
	end if;
end for;

return false;
end intrinsic;

intrinsic SaveProtoessentials(FileName::MonStgElt,S::Grp, EE::SeqEnum)
{Saves protoessentials to FileName so that it can be loaded}
PrintFile(FileName,"S:=");PrintFileMagma(FileName,S);PrintFile(FileName,";");
PrintFile (FileName, "PE:=[];\n");
PrintFile (FileName, "autF:=[];\n");
for k := 1 to #EE do
    E:=EE[k];
    AA:=EE[k]`autF;
    R := [S!w:w in PCGenerators(E)];
    PrintFile(FileName,"E:=sub<S|");
    PrintFile(FileName,R);
    PrintFile(FileName,">;\n");
    PrintFile(FileName,"PE:=Append(PE,E);\n");
    Autos:=[];
    PrintFile (FileName, "Autos:=[];\n");
    for j :=1 to #EE[k]`autF do
    A:=EE[k]`autF[j];
    E:=sub<S|R>;
    PrintFile(FileName, "AE:= AutomorphismGroup(E);\n");
    PrintFile(FileName,"A:=sub<AE|>;\n");
    for ii := 1 to #Generators(A) do
        alpha:=A.ii;
        PrintFile(FileName,"A:=sub<AE|A, hom<E -> E |[ ");
        gens:=SetToSequence(PCGenerators(E));
        for i in [1..#gens-1] do
            x:= E!gens[i];
            PrintFile(FileName,"<");
            PrintFile(FileName,x);
            PrintFile(FileName,",");
            PrintFile(FileName,E!alpha(x));
            PrintFile(FileName,">");
            PrintFile(FileName,",");
        end for;
        x:= gens[#gens];
        PrintFile(FileName,"<");
        PrintFile(FileName,x);
        PrintFile(FileName,",");
        PrintFile(FileName,E!alpha(x));
        PrintFile(FileName,">");
        PrintFile(FileName," ]>>;\n");
    end for;
    PrintFile(FileName,"Autos[");
    PrintFile(FileName,j);
    PrintFile(FileName,"]:=A;\n");
    end for;
PrintFile(FileName,"autF:=Append(autF,Autos);\n");
end for;

end intrinsic;


////////////////////////////////////////////////
intrinsic AllProtoEssentialsbgps(S::Grp:OpTriv:=true, pPerfect:= true,Printing:= false, Morphisms:=true)-> SeqEnum
{Makes all protosessentials up to automorphisms of S the parameters ask for  O_p(F)=1 and O^p(\F)= \F and makes their potential automorphism groups}

 
 
ZZ:= Integers(); //Integer Ring
 
p:= FactoredOrder(S)[1][1];
 nn:= Valuation(#S,p);



//Here are automorphisms of S and centric subgroups of S
S:= PCGroup(S);

Sbar, bar:= S/Centre(S);
TT:= Subgroups(Sbar);
SS:= [Inverse(bar)(x`subgroup):x in TT|IsSCentric(S,Inverse(bar)(x`subgroup))];
if Printing eq true then print "the group has", #SS, "centric subgroups"; end if;
 


///////////////////////////////////
///We precalculate certain properties of S. The objective here is to eliminate
///most  p-groups S before we calculate and construct the possible Borel subgroups
///associated with S.
///We do this first as there may be many  of Borel subgroups which we don't need
///to calculate in some circumstances.
/////////////////////////////////////
ProtoEssentials:=[];// This sequence will contain the ProtoEssential subgroups
//
if IsMaximalClass(S) and #S ge p^5 then
    LL:= LowerCentralSeries(S);  
    T:=[];
     Append(~T,Centralizer(S, LL[2],LL[4]));
     C:= Centralizer(S, LL[nn-2]);
     if C in T eq false then
        Append(~T,C); end if;
     T:= T cat [x:x in SS| #x eq p^2 and LL[nn-1] subset x and not x subset  T[1]  and not x subset C ]
     cat
     [x:x in SS| #x eq p^3 and LL[nn-2] subset x  and not x subset  T[1]  and not x subset C ];
      TT:=[];
     for x in T do
            Nx:=Normalizer(S,x);
          A:=AutYX(Nx,x);
          Ap:= SubMap(x`autopermmap,x`autoperm ,A);
          Innerp:= SubMap(x`autopermmap,x`autoperm , Inn(x));
            RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
            if not RadTest then continue x; end if;
          Append(~TT,x);
     end for;        
       ProtoEssentials:=   TT;
end if;

ZU:= UpperCentralSeries(S); Z:= ZU[2]; Z2:= ZU[3];    
if IsMaximalClass(S) eq false  or #S le p^4 then  
for x in SS do  
   if x eq S then continue x; end if;
   if IsCyclic(x) then  continue x; end if;
   Frat:=FrattiniSubgroup(x);
   if Z subset Frat and not Z2 subset x then continue x; end if;
   Nx:=Normalizer(S,x);
   P:= Index(Nx,x);
   Frat:=FrattiniSubgroup(x);
   FQTest := Index(x,Frat) ge P^2;
        //This is a bound obtained by saying that $\Out_\F(x)$ acts faithfully on $x/\Phi(x)$.  
        //The order of such faithful modules is at least $|\Out_S(x)|^2$.
    if FQTest eq false then continue x; end if;
   CFrat := Centralizer(x,Frat);
   if IsAbelian(Frat) and not (Centralizer(S, CFrat) subset CFrat) then continue x; end if;
   if IsAbelian(Frat) and CommutatorSubgroup(Nx, x) subset CFrat and CommutatorSubgroup(Nx, CFrat) subset Center(CFrat)   and CommutatorSubgroup(Center(CFrat), Nx) subset Frat then continue x; end if;

   SylTest, QC:=IsStronglypSylow(Nx/x);
        //If $x$ is essential, then $\Out_F(x)$ should have a strongly $p$-embedded.
        //Here we check that the Sylow $p$-subgroup is compatible with this.
   if SylTest eq false   then continue x; end if;
   A:=AutYX(Nx,x);
   Ap:= SubMap(x`autopermmap,x`autoperm ,A);
   Inner:= Inn(x);
   Innerp:= SubMap(x`autopermmap,x`autoperm ,Inner);
    RadTest:=#(Ap meet pCore(x`autoperm, p)) eq  #Innerp;
    if not RadTest then continue x; end if;
   if QC eq false and IsSoluble(x`autoperm)  then   continue x; end if;
 
//Here we use information about the action of $N_G(S)$ on a Sylow $p$-subgroup of $SL_2(p^2)$ and other groups
//with a strongly p-embedded N_G(S) with $|S|=p^2$.
if QC eq false and P eq p^2 and IsOdd(p)
          then  
      MM:= MaximalSubgroups(Nx);
       MM:= [y`subgroup: y in MM| x subset y`subgroup];  
      W1:= [x: x in MM| IsIsomorphic(x,MM[1])];
      r:= p+1; s:= ZZ!((p+1)/2);
      if not #W1 in {r,s}  then continue x; end if;
      if #W1 eq r and Index(x,Centre(Rep(W1))) eq p then continue x; end if;
      if #W1 eq s then W2:= Set(MM) diff Set(W1);
         if  Index(x,Centre(Rep(W1))) eq p or Index(x,Centre(Rep(W2))) eq p then continue x; end if;
      end if;
      end if;
   ProtoEssentials:= Append(ProtoEssentials,x);
end for;
end if;
if not Morphisms then "ProtoEssentials without Automorphism groups"; return ProtoEssentials; end if;


MakeAutos(S);
InnS:=Inn(S);
AutS:= S`autogrp;
map:= S`autopermmap;
AutSp:= S`autoperm;
InnSp:= SubMap(map,AutSp, InnS);

////////////////////////////////
///We need some subgroups in ProtoEssentials;
///////////////////////////////////
 
if  #ProtoEssentials eq 0 then return []; end if;


///Notice that if E is protoessential, then so is E\alpha for alpha in AutS
ProtoEssentialAutClasses:= Setseq({Set(AutOrbit(S,PE,S`autogrp)):PE in ProtoEssentials});
ProtoEssentialAutClasses:= [Rep(x):x in ProtoEssentialAutClasses];
 
 
if OpTriv then if CharSbgrpTest(ProtoEssentials,S) eq true then return []; end if; end if;
   
 
    ///This test takes Q as the intersection of all the members of the members
    //of ProtoEssentials and checks if any of them are characteristic in all members
    //of ProtoEssentials and S. If some non-trivial subgroup is then O_p(\F)\ne 1.

   
if pPerfect then H:= sub<S|ProtoEssentials,{x^-1*a(x):a in Generators(S`autogrp), x in S}>;
if  H ne S then return []; end if; end if;
 //This tests is with this set of protoessentials that O^p(\F) <F.
   
/////////////////////
///////Here we  make all the candidates for Out_\F(x) for x in ProtoEssentials
///////and check that they have strongly p-embedded subgroups.
///////////////////

for x in ProtoEssentialAutClasses do #x; end for;

for i in [1..#ProtoEssentialAutClasses] do
   P:= ProtoEssentialAutClasses[i];#P;
   MakeAutos(P);
   AutP:=P`autogrp;
   mapP:= P`autopermmap;
   AutPp:= P`autoperm;
   InnP:=Inn(P);
   InnPp:=sub<P`autoperm|{mapP(g): g in Generators(InnP)}>;
   AutSP:=AutYX(Normalizer(S,P),P );
   AutSPp:=sub<P`autoperm|{mapP(g): g in Generators(AutSP)}>; 
   Q:= AutSPp/InnPp;

   M:=SubnormalClosure(AutPp,AutSPp);
   
   Candidates :=[];
     pVal:=Valuation(#AutPp,p);
     NormVal:=Valuation(#AutSPp,p);
       
        QC:=IsQuaternionOrCyclic(Q);
        if not QC  then
            Mbgs:= NonsolvableSubgroups(M:OrderDividing:= ZZ!(#AutPp/((p^(pVal-NormVal)))));
            ///So the elements of Mbgs have a Sylow subgroup which has the same order as AutSP
            AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#sub<AutPp|xx`subgroup,InnPp>,p) eq NormVal];
      APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
      for kk in [1..#AutPCandidates] do  
                  GG:= AutPCandidates[kk];
               Sylow:=SylowSubgroup(GG,p);
                  a,b:=IsConjugate(AutPp,Sylow,AutSPp);
         if a then Append(~APC,GG^b); end if;
      end for;
      AutPCandidates:= APC;
       end if;//QC
               
     if QC and IsCyclic(Q)  then
                     AutPCandidates:= OverGroupsSylowEmbedded(M,AutSPp,InnPp,p:Printing:= Printing );
        end if;  
   
       if QC and not IsAbelian(Q) then  
      Mbgs:= Subgroups(M, InnPp:   OrderDividing:= ZZ!(#AutPp/(p^(pVal-NormVal))));
                AutPCandidates:= [sub<AutPp|xx`subgroup,InnPp> :xx in Mbgs|Valuation(#xx`subgroup,p) eq NormVal];
      APC:=[];//Now pick out the ones that have AutSPp as a Sylow.
      for kk in [1..#AutPCandidates] do  
                  GG:= AutPCandidates[kk];
               Sylow:=SylowSubgroup(GG,p);
                  a,b:=IsConjugate(AutPp,Sylow,AutSPp);
         if a then Append(~APC,GG^b); end if;
      end for;
      AutPCandidates:= APC;
   end if;
       
   P`autF:=[];//This is where we store all potential Aut_F(P) up to Aut(P) conjugacy.

          for GG in AutPCandidates do
      if  IsStronglypEmbeddedMod(GG,InnPp,p) eq false then continue GG; end if;
            NGG:= Normalizer(AutPp,GG);  
            NGGsubs:=[sub<AutPp|xx`subgroup> :xx in Subgroups(NGG: OrderMultipleOf :=#GG)|
                                GG subset xx`subgroup and Index(xx`subgroup,GG) mod p ne 0];
               for GGs in NGGsubs do
                  Append(~P`autF,sub<AutP|{Inverse(mapP)(g): g in Generators(GGs)}>);
              end for;
        end for;//GG  
end for;  // i in [1..ProtoEssentialAutClasses]  



ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|assigned(x`autF)];
ProtoEssentialAutClasses:= [x:x in ProtoEssentialAutClasses|#x`autF ne 0];

if Printing then
   print "The set ProtoEssentialAutClasses has", #ProtoEssentialAutClasses,"elements";  
end if;
if Printing then
   for x in ProtoEssentialAutClasses do  
      print "the protoessential aut class  representaive have ", #x`autF, "potential automorphism groups";
    end for;
end if;


//We explode the autclasses to get all protoessentials and ajoin their potential autogrps.
ProtoEssentials:=[];
for x in ProtoEssentialAutClasses do
    Xx, Stx, Rx := AutOrbit(S,x,S`autogrp);
    PNew := [];
    for y in SS do
        if y in Xx then
            MakeAutos(y);
            Append(~ProtoEssentials,y);
            Append(~PNew,y);
        end if;
    end for;
   
    if #PNew ne 0 then
        for j := 1 to #PNew do
            y:= PNew[j];
            y`autF:=[];
            for AP in x`autF do
                        y`autF := Append(y`autF, sub<y`autogrp|[Inverse(Rx[Index(Xx,y)])*gamma*Rx[Index(Xx,y)]: gamma in Generators(AP)]>);
            end for;
        end for;
    end if;
end for;//x


if OpTriv then
//The next test uses Lemma 4.10 to show that P1 and P2 are not both essential.
// If P1 is essential, then P1' ne 1 and is normalized by Aut_\F(S) and Aut_F(E_1). This gives O_p(F) ne 1.
   if #ProtoEssentials eq 2 and p ge 5 and #S lt p^(p+3) then
       P1:= ProtoEssentials[1];
       P2:= ProtoEssentials[2];
        if #P1 le #P2 then PP:= P2; P2:= P1; P2:= PP; end if;
       NSP2:= Normalizer(S,P2);  
       PC:= Core(S,P2);
       if IsConjugate(S,P1,NSP2) and Index(NSP2,P2) eq p and Index(S,NSP2) eq p and
       Index(P2,PC) eq p and IsCharacteristic(NSP2,PC) and IsNormal(S,DerivedSubgroup(P1)) then      ProtoEssentials:=[P2];
        end if;
   end if;    
end if; //OpTriv
   


return ProtoEssentials;
end intrinsic;



intrinsic TransportFusionSystem(F::FusionSystem, S::Grp)-> SeqEnum
{}
///Transport automorphisms of essential subgroups to subgroups of new group.

T:= F`group;

L:= [];

a,b:= IsIsomorphic (T,S);

for X in F`essentialautos do

    E:= Group(X);

    Y := b(E);

    MakeAutos(Y);

    alpha := Inverse(b);

    Theta:={};

    for x in Generators(X) do

    beta:= alpha*x*b;

    Theta:=Theta join {beta};   end for;

    Y1:= sub<Y`autogrp|Theta>;

    Append(~L,Y1);

end for;

return L;

end intrinsic;

 

intrinsic TransportAutomiserSequence(Seq::SeqEnum, b::Map, bi::Map)-> SeqEnum
{}
///Transport automiser sequence of a group to a group isomorphic to it.

L:= []; 

for X in Seq do 

    E:= Group(X);

    Y := b(E);

    MakeAutos(Y);

    alpha := bi; 



    Theta:=[];

    for x in Generators(X) do

    beta:= alpha*x*b;
    
    Append(~Theta, beta);   end for;

    Y1:= sub<Y`autogrp|Theta>;

    Append(~L,Y1);

end for;

return L;

end intrinsic;



intrinsic MBEaut(S,G::Grp,A::GrpAuto)-> SeqEnum
{Map a fusion system on S to G.}
///Make representatives of conjugates of an automorphism group.
require IsIsomorphic(S,G): "Groups are not isomorphic.";
	MakeAutos(G);
	S2A:=sub<G`autoperm|{G`autopermmap(x): x in Generators(Automizer(Normalizer(S,G),G))}>;
	ApG:=sub<G`autoperm|{G`autopermmap(x):x in Generators(A)}>; 
	N1:=Normalizer(G`autoperm,S2A);
	N2:=Normalizer(N1,ApG);
	TT:=Transversal( N1,N2);
	AGconj:=[ApG^t:t in TT];
	MBAGconj:=[];
	for x in AGconj do 
		Append(~MBAGconj,sub<G`autogrp|{Inverse(G`autopermmap)(t):t in Generators(x)}>);
	end for;
	return MBAGconj;
end intrinsic;




intrinsic IsReducedFusCriterion1(S::Grp) -> Bool
{By AOV Prop3.6}
require IsPrimePower(#S): "Group is not a p-group";
a,b:=IsDirectProduct(S);
if a eq false then return false;
end if;

for x in b do 
MakeAutos(x[1]);
MakeAutos(x[2]);
end for;

for x in b do
if IsAbelian(x[1]) and Log(Order(x[2]/FrattiniSubgroup(x[2])),2) le 5 and IsCyclic(Centre(x[2])) and Floor(Log(2,Order(x[2]`autoperm))) eq Log(2,Order(x[2]`autoperm))
then return true;break; end if;
if IsAbelian(x[2]) and Log(Order(x[1]/FrattiniSubgroup(x[1])),2) le 5 and IsCyclic(Centre(x[1])) and Floor(Log(2,Order(x[1]`autoperm))) eq Log(2,Order(x[1]`autoperm))
then return true;break; end if;
end for;

return false;

end intrinsic;


intrinsic IsReducedFusLynd(S:Grp)-> Bool{return true if satisfies the criterions in Theorem 6.2}
N:=NormalSubgroups(S);
C:=[x`subgroup:x in N|IsCharacteristic(S,x`subgroup)];
ZS:=Omega(Centre(S),1);
t:={};
Ct:=[];
for x in C do Include(~t,ZS subset x); 
	if (ZS subset x) eq false then Append(~Ct,x);end if;
end for;
if #t eq 1 then return true;end if;
L:=[x`subgroup:x in N|(ZS subset x`subgroup) eq false and IsCyclic(S/x`subgroup)];
for x in L do 
	ZL:=Omega(Centre(x),1);E:={}; for e in ZS do if e notin x then Include(~E,e);end if; end for;
	for y in C do
		if ZL subset y and ((E subset y) eq false) then return false;end if;
	end for;
end for;
return true;
end intrinsic;

intrinsic ProtoEssentialsCharacteristicIntersectioncheck(S:Grp)->SeqEnum{Find all proto-essentials without morphism but with two checks from Aov17, Prop 2.3(j) and PS21, Lemma 4.9} 

E2:=CyclicGroup(2);
E4:=DirectProduct(E2,E2);
E8:=DirectProduct(E4,E2);
P:=AllProtoEssentials(S:Morphisms:=false);
NP:=[Normalizer(S,P[i]):i in [1..#P]];
PR:=[];
Pt:=[];
for i in [1..#P] do 
	if IsIsomorphic(NP[i]/P[i],E4) or IsIsomorphic(NP[i]/P[i],E8) then SN:=Subgroups(NP[i]:OrderEqual:=#P[i]*2);
	SN:=[x`subgroup:x in SN|P[i] subset x`subgroup]; else Append(~Pt,P[i]); continue i;
	end if;
	for j in [1..#SN] do for k in [1..(#SN-j)] do if IsIsomorphic(SN[j],SN[j+k]) eq false then continue i;end if;end for;end for;
Append(~Pt,P[i]);
end for;
if #Pt eq 0 then return true;
end if;
if #Pt ge 2 then Q:=Pt[1] meet Pt[2]; elif #Pt eq 1 then Q:=Pt[1];end if;
if #Pt gt 2 then for i in [3..#Pt] do Q:=Q meet Pt[i]; end for;end if;
for i in [1..#Pt] do 
	if IsCharacteristic(Pt[i],Q) then continue i;
	else return false;
	end if;
end for;
if IsCharacteristic(S,Q) then
return true; else return false;
end if;
end intrinsic;

intrinsic Groupsuptoisomorphism(List::SeqEnum)->SeqEnum{}
///Making the list of non-isomorphic groups.
require Type(List[1]) eq GrpPC or Type(List[1]) eq GrpPerm :"Group is not pcgroup or permutation group.";
N:=List;
NO:=[N[1]];
for i in [1..#N] do
 for j in [1..#NO] do
if IsIsomorphic(N[i],NO[j])
 then break;
end if;
 if j le (#NO-1)
then continue;
end if;
NO:=Append(NO,N[i]);
end for;
end for;
return NO;
end intrinsic;

intrinsic Groupsuptoisomorphism(List::SeqEnum)->SeqEnum{}
///Making the list of non-isomorphic groups.
require Type(List[1]) eq GrpPC or Type(List[1]) eq GrpPerm :"Group is not pcgroup or permutation group.";
N:=List;
NO:=[N[1]];
for i in [1..#N] do
for j in [1..#NO] do
if IsIsomorphic(N[i],NO[j])
then continue i;
end if;
end for;
NO:=Append(NO,N[i]);
end for;
return NO;
end intrinsic;