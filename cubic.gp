my_sqrt(n)=return(sqrtint(numerator(n))/sqrtint(denominator(n)));
gettors(E,n)=local(fulln,struct,P);[fulln,struct,P]=elltors(E);return(ellmul(E,P[1],fulln/n));
tamagawa(E)=gr=ellglobalred(E);l=[[gr[4][i,1],gr[5][i][4]]|i<-[1..#gr[4][,1]]];return(prod(i=1,#l,l[i][2]));
expectedheight(E,rank=1)=localprec(19);return(elltors(E)[1]^2*ellL1(E,rank)/rank!/(if(E.disc>0,2,1)*E.omega[1])/tamagawa(E));
descend(E,limit,rankub)=local(poi,covers,Plist,hyperell,trans,i,P,x,y,hmat);poi=ellrank(E,abs(limit\200000))[4];return(poi);
\\ if(rankub==#poi,return(poi));covers=ell2cover(E);Plist=Vec([]);\
\\ [hyperell,trans]=covers[#covers];poi=hyperellratpoints(hyperell,abs(limit));for(i=1,#poi,[x,y]=poi[i];P=eval(trans);if(ellorder(E,P)==0,Plist=concat(Plist,[P]);\
\\ localprec(38);hmat=ellheightmatrix(E,Plist);if(abs(matdet(hmat))<1e-19,Plist=Plist[1..(#Plist)-1]));if(rankub==#Plist,return(Plist)));return(Plist);
mkc(n)=return(ellinit([0,4*n^2+12*n-3,0,32*(n+3),0]));
mkc2(n)=return(ellinit([0,4*n^2+12*n-3,0,-128*(n+3),-128*(n+3)*(4*n^2+12*n-3)]));
mkc3(n)=return(ellinit([0,4*n^2+12*n-3,0,-320*n^2-1248*n-1104,-1024*n^4-7168*n^3-18944*n^2-24576*n-15040]));
mkc6(n)=return(ellinit([0,4*n^2+12*n-3,0,-640*n^3-6080*n^2-18528*n-18384,-2048*n^5-39936*n^4-281088*n^3-935936*n^2-1503744*n-941248]));
heegner(n)=localprec(19);eh1=expectedheight(mkc(n));eh2=expectedheight(mkc2(n));eh3=expectedheight(mkc3(n));eh6=expectedheight(mkc6(n));\
iso2=eh1>eh2;iso3=eh1>eh3;if(iso2,if(iso3,return(map_III(n,mkc(n),map_II(n,mkc3(n),ellheegner(mkc6(n))))),return(map_II(n,mkc(n),ellheegner(mkc2(n))))),\
if(iso3,return(map_III(n,mkc(n),ellheegner(mkc3(n)))),return(ellheegner(mkc(n)))));
map_II(n,E,P)=[F,map]=ellisogeny(E,gettors(E,2));P=ellmul(ellinit(F),P,2);denom=denominator(P[1]);localprec(log(denom)/log(10)+10);kill(x);\
P[1]=round(real(polroots(map[1]/map[3]-P[1]*map[3])[1])*denom)/denom;P[2]=my_sqrt(P[1]^3+E[2]*P[1]^2+E[4]*P[1]+E[5]);return(P);
map_III(n,E,P)=[F,map]=ellisogeny(E,gettors(E,3));P=ellmul(ellinit(F),P,3);denom=denominator(P[1]);localprec(log(denom)/log(10)+10);kill(x);\
P[1]=round(real(polroots(map[1]-P[1]*map[3]^2)[1])*denom)/denom;P[2]=my_sqrt(P[1]^3+E[2]*P[1]^2+E[4]*P[1]+E[5]);return(P);
map2(n,P)=return(map_II(n,mkc(n),P));
map3(n,P)=return(map_III(n,mkc(n),P));
map6(n,P)=return(map_II(n,mkc(n),map_III(n,mkc2(n),P)));
try_isogeny_II(n,limit,rankub)=local(F,gens);F=mkc2(n);gens=descend(F,limit,rankub);if(gens==[],return([]));for(i=1,#gens,gens[i]=map_II(n,mkc(n),gens[i]));return(gens);
try_isogeny_III(n,limit,rankub)=local(F,gens);F=mkc3(n);gens=descend(F,limit,rankub);if(gens==[],return([]));for(i=1,#gens,gens[i]=map_III(n,mkc(n),gens[i]));return(gens);
try_isogeny_VI(n,limit,rankub)=local(F,gens);F=mkc6(n);gens=descend(F,limit,rankub);if(gens==[],return([]));for(i=1,#gens,gens[i]=map_III(n,mkc(n),map_II(n,mkc3(n),gens[i])));return(gens);
findgen_worker(n,limit=5*10^5)=local(E,ranklb,rankub,Plist,gens,i,P,hmat);E=mkc(n);[ranklb,rankub]=ellrank(E)[1..2];if(ranklb!=rankub,localprec(19);if(ranklb<=1,if(rankub<4,\
rankub=ranklb+2*(abs(ellL1(E,ranklb))<10^-9),rankub=ellanalyticrank(E)));print("Analytic rank of E_",n," is ",rankub));localprec(38);\
if(rankub==0,return([]));Plist=[];gens=descend(E,limit,rankub);for(i=1,#gens,P=gens[i];Plist=concat(Plist,[P]);\
hmat=ellheightmatrix(E,Plist);if(abs(matdet(hmat))<1e-19,Plist=Plist[1..(#Plist)-1],print("Found point of height ",ellheight(E,P)," via direct search")));\
if(length(Plist)==rankub,return(Plist));gens=try_isogeny_II(n,limit,rankub);for(i=1,#gens,P=gens[i];Plist=concat(Plist,[P]);hmat=ellheightmatrix(E,Plist);\
if(#Plist>1&&abs(matdet(hmat))<1e-19,Plist=Plist[1..(#Plist)-1],print("Found point of height ",ellheight(E,P)," via 2-isogeny")));\
if(length(Plist)==rankub,return(Plist));gens=try_isogeny_III(n,limit,rankub);for(i=1,#gens,P=gens[i];Plist=concat(Plist,[P]);hmat=ellheightmatrix(E,Plist);\
if(#Plist>1&&abs(matdet(hmat))<1e-19,Plist=Plist[1..(#Plist)-1],print("Found point of height ",ellheight(E,P)," via 3-isogeny")));\
if(length(Plist)==rankub,return(Plist));gens=try_isogeny_VI(n,limit,rankub);for(i=1,#gens,P=gens[i];Plist=concat(Plist,[P]);hmat=ellheightmatrix(E,Plist);\
if(#Plist>1&&abs(matdet(hmat))<1e-19,Plist=Plist[1..(#Plist)-1],print("Found point of height ",ellheight(E,P)," via 6-isogeny")));\
if(length(Plist)==rankub,return(Plist),for(i=#Plist+1,rankub,Plist=concat(Plist,[[]]));if(rankub>=2,warning("Only partial basis has been found");return(Plist),\
if(limit<0,return([[]]),print1("[heegner] ");default(debug,1);return([heegner(n)]))));
findgen(n,reg_only=0,limit=5*10^5)=if(reg_only>=1,gens=ellrank(mkc(n),5);\
if(gens[2]==length(gens[4]),return(prod(i=1,gens[2],ellheight(mkc(n),gens[4][i]))),return(expectedheight(mkc(n),gens[2]))));return(findgen_worker(n,limit));
getxyz(N,P)=a=8*(N+3)-P[1]+P[2];b=8*(N+3)-P[1]-P[2];c=-8*(N+3)-2*(N+2)*P[1];g=gcd([a,b,c]);return([a/g,b/g,c/g]);
check_pos(n,P)=x=P[1];return(x<-4*(n+3)/(n+2)&&x^2+4*n*(n+3)*x+16*(n+3)^2>0);
solve_from_point(n,Preal,height_only=0)=if(Preal[1]>0,return([]));local(E,now_prec,P,tors,mul,P2,nowP);E=mkc(n);ellheight(E,Preal);now_prec=max(round(n*log(n)),default(realprecision));\
tors=gettors(E,6);mul=1;warning("Initial precision: ",now_prec);while(1,localprec(now_prec);P=Preal*1.0;nowP=P;P2=ellmul(E,P,2);mul=1;while(mul<now_prec*2/3,\
if(check_pos(n,nowP),break);if(check_pos(n,elladd(E,nowP,tors)),mul=-mul;break);mul=mul+2;nowP=elladd(E,nowP,P2);if(mul%100==99,print1(".")));if(abs(mul)>=now_prec*2/3,\
now_prec=round(now_prec*log(n));warning("recalculating with precision "now_prec),break));add_tors=mul<0;mul=abs(mul);print1(mul,"*P");if(add_tors,print1("+tors"));\
localprec(38);h=3/2*ellheight(E,Preal)*mul^2-4*log(n)-9;print(" gives a positive solution, height>",h,", decimal digits>",h/log(10));if(height_only>=1,return(h));\
Preal=ellmul(E,Preal,mul);if(add_tors,return(getxyz(n,elladd(E,Preal,tors))),return(getxyz(n,Preal)));
solvexyz(n,height_only=0)=local(E,gens);if(n%2==1,return([]));E=mkc(n);gens=findgen(n);if(#gens==0,return([]));if(#gens>1,error("Not yet implemented"));return(solve_from_point(n,gens[1],height_only));
prepare_db(lb=1,ub=10000,limit=-5*10^5)=local(i,gens);for(i=lb,ub,print("finding generator for ",i);gens=findgen_worker(i,limit);write("cubic_db.txt",i," ",gens));
prepare_db_list(lst,limit=-5*10^5)=local(i,gens,n);for(i=1,#lst,n=lst[i];print("finding generator for ",n);gens=findgen_worker(n,limit);print("Generators of E_n: ",gens));
\\ grep -E -x '[0-9]+ \[\[\]\]' cubic_db.txt
\\
\\ SetSeed(1);
\\ SetClassGroupBounds("GRH");
\\ E := EllipticCurve([0, 147161149, 0, -142934720408016, -16846971914709437693120]);
\\ HyperE := TwoDescent(E : RemoveTorsion := true)[1];
\\ ///// below are 6-descent codes
\\ Crv3, mapA := ThreeDescentByIsogeny(E);Crv, map6to3 := SixDescent(HyperE, Crv3[1]);P6 := PointSearch(Crv, 10^6 : OnlyOne := true)[1];P3_internal := map6to3(P6);comps := Components(mapA[1]);P3_fixed := Domain(comps[1]) ! Eltseq(P3_internal);P_intermediate := comps[1](P3_fixed);P_intermediate_fixed := Domain(comps[2]) ! Eltseq(P_intermediate);PE := comps[2](P_intermediate_fixed);P := Saturation([PE], 1000 : TorsionFree := true)[1];P in E;CanonicalHeight(P);
\\ ///// below are 4-descent codes
\\ //Crv4 := FourDescent(HyperE)[1];Ps := PointsQI(Crv4, 10^7 : OnlyOne := true)[1];A, mapA := AssociatedEllipticCurve(Crv4 : E := E);P := Saturation([mapA(Ps)], 1000 : TorsionFree := true)[1];P in E;CanonicalHeight(P);
\\ ///// below are 12-descent codes
\\ //Crv4 := FourDescent(HyperE)[1];Crv3 := ThreeDescentByIsogeny(E)[1];Crvs12, maps12 := TwelveDescent(Crv3, Crv4);Crv12 := Crvs12[2]; map12 := maps12[2];P12 := PointSearch(Crv12, 10^6 : OnlyOne := true)[1];P4 := map12(P12);A, mapA := AssociatedEllipticCurve(Crv4 : E := E);P := Saturation([mapA(P4)], 1000 : TorsionFree := true)[1];P in E;CanonicalHeight(P);
