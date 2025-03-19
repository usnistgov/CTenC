(* ::Package:: *)

BeginPackage["CTenC`"];


(*Definitions*)
DefTensor::usage == "Defines a tensor";


(*Index manipulations*)
DefIndices::usages == "Set the indices used for cannonization of dummy indices";

GetIndices::usage == "Returns the indices of a tensor expression";
GetFreeIndices::usage == "Return the free indices of a tensor expression";
GetDummyIndices::usage == "Returns the dummy indices of a tensor expression";
ContainsIndices::usage == "Checks to see if expression contains the given indices";

GetIndicesTerms::usage == "Get indices for particular terms";

ContractIndices::usage == "Replace dummy indices with local variables";

ReplaceIndices::usage == "Replace indicies in a tensor expression";
PrettyIndices::usage == "Replace dummy indices with canonical indices supplied by user";

Rank::usage == "Returns the rank of a tensor";

IndexSet::usage == "Assignment operator with automatic dummy replacement";


(*what am I?*)
IndexQ::usage == "Returns true if object is a tensor";
ScalarQ::usage == "Returns ture if object is a scalar";
IdempotentQ::usage == "Returns true if object is Idempotent";
ConstantTensorQ::usage == "Returns true if object is a tensor";
DependsQ::usage == "Returns true if a tensor depends on another";


(*Simplification routines*)
SimplifyIndices::usage == "Simplify expressions somewhat";


(*builtin tenosrs*)
delta::usage == "The identity tensor";
Symdelta::usage == "Returns the the symmetrized products of deltas";

LeviC::usage == "The Levi-Civita symbol";

PermDelta::usage == "Permanent delta, the projection operator of the space of symmetric tensors";
GDelta::usage == "Generalized delta, the projection operator of the space of antisymmetric tensors";
Delta::usage == "The projection operator of the space of irreducible tensors";

ProjectionOperator::usage == "Returns the projection operator of the manifold the tensor lives in";
ProjectorSimplify::usage == "Simplify expressions invovling the projection oerator";
IndexExpand::usages == "Expand index operators"


(*Symmetry relations*)
SymmetryQ::usage == "Checks if a tensor has symmetry in a given set of indices";
AddSymmetry::usage == "Adds a symmetry to a tensor";
AddIdentity::usage == "Adds an identity operator to a tensor";
AddOrthogonal::usage == "Defines a projection operator as orthogonal to a tensor";
ConstructProjector::usage == "Constructs the projector operator for a tensor";

ProjectorForm::usage == "Write a tensor as it's projection operator acting on the tensor";
SymmetryReduce::usage == "Use symmetry properties to simplify";


(*Functions of tensors*)
IndexPower::usage == "Power of a tensor";
IndexHarmonic::usage == "Harmonic tensor from a vector"
HarmonicToCartesian::usage == "Expand a tensor harmonic into vector form" (*might consider rename*)


(*Simplification rules*)
IndexSimplify::usage == "Simplify an index expression";


(*Tensor invariants and covariants*)
PrincipalInvariant::usage == "The principal invariants of a tensor";


(*Display functions*)
TensorSymbol::usage == "Symbol for displaying object";


(*Error messages*)
Tensor::rank = "`1` indices specified for rank `2` tensor `3`";
PrettyIndices::dummies = "`1` dummy indices gives for expression with `2` dummy indices";
IndexHarmonic::rank = "`1` indices specified for rank `2` harmonic tensor in `3`";


(*Calculus*)
Di::usage = "Computes the total derivative";
Dp::usage = "Computes the partial derivative";


(*Intgrals*)
SurfaceIntegral::usage = "Compute the integral of a function over a surface";


Begin["`Private`"];

$dummyIndices={};
$nDim=3;
$internalDummies={i,j,k,l,m,p,q,r,s,t,u,v};
$internalDummies2={i1,j1,k1,l1,m1,p1,q1,r1,s1,t1,u1,v1};

$functionSimplify={};
$projectorSimplify={};
$indexExpand={};


(* ::Subsection:: *)
(*Tensor Definitions and Index Manipulation*)


(* ::Subsubsection:: *)
(*Definitions*)


(*Definitions*)

(*Objects are not index objects unless specified*)
IndexQ[x_]:=False;

SetAttributes[DependsQ,Orderless]
DependsQ[head_Symbol,head_Symbol]:=True;
DependsQ[head1_Symbol,head2_Symbol]:=False/;!SameQ[head1,head2]
DependsQ[expr_,head_Symbol]:=True/;Internal`DependsOnQ[expr,head]
ScalarQ[x_]:=GetFreeIndices[x]=={};

DefIndices[indsList_]:=Block[{},
	$dummyIndices=indsList;
	Protect[indsList];
]

Options[DefTensor]={Idempotent->False,ProjectionSuperscript->False,Symmetries-><||>,ConstantTensor->False,Depends->{}};

(*Special setup for scalar*)
DefTensor[head_,symb_String,0,opts:OptionsPattern[]]:=Module[{proj,syms},	
	
	DefTensor[head,symb,opts];
	
	(*Set the rank of the tensor*)
	Rank[head]^=0;
	
	(*Number of indices must be equal to rank*)
	head[inds___]/;(Length[{inds}]!=0):=Message[Tensor::rank,Length[{inds}],
		0,symb];

]

(*Tensor with a required number of indices*)
DefTensor[head_,symb_String,rank_Integer,opts:OptionsPattern[]]:=Module[{proj,syms},	
	
	DefTensor[head,symb,opts];
	
	(*Set the rank of the tensor*)
	Rank[head]^=rank;
	
	(*Number of indices must be equal to rank*)
	head[inds___]/;(Length[{inds}]!=rank):=Message[Tensor::rank,Length[{inds}],
		rank,symb];
		
	(*generate projection operator for the tensor*)
	If[True,
		Off[Unset::norep];
		Unset[ProjectionOperator[head][Sequence@@(Pattern[#,_]&/@$internalDummies[[1;;rank*2]])]];
		On[Unset::norep];
	
		syms=OptionValue[Symmetries];
		proj=Inner[delta,Sequence@@Partition[$internalDummies[[1;;rank*2]],rank],Times];
		Do[proj=ConstructProjector[proj,$internalDummies[[1;;rank*2]],syms[x],x];, {x, Keys[syms]}];
		Activate[ Inactive[SetDelayed][ProjectionOperator[head]@@(Pattern[#,_]&/@$internalDummies[[1;;rank*2]]),
			ContractIndices[proj]] ];
	]
]

(*Tensor that can take a variable number of indices*)
DefTensor[head_,symb_String,OptionsPattern[]]:=Module[{syms},
	(*Clear all definitions if already defined*)
	ClearAll[head];
	
	IndexQ[head]^=True;
	IndexQ[head[___]]^=True;

	IdempotentQ[head]^=OptionValue[Idempotent];
	ConstantTensorQ[head]^=OptionValue[ConstantTensor];
	
	If[Length[OptionValue[Depends]]>0,
		Do[DependsQ[head,head2]^=True,{head2,OptionValue[Depends]}];
	];

	(*Tensors arguments can alternately be supplied as a list*)
	head[left___,inds_List,right___]:=head[left,Sequence@@inds,right];
	
	(*Define the index symbol of the object*)
	TensorSymbol[head]^=symb;
	
	(*Define properties for display*)
	ProjectionSuperscriptQ[head]^=OptionValue[ProjectionSuperscript];
	
	(*Matrix power*)
	head/:head[inds1__,inds2__]head[inds2__,inds3__]/;(Length[{inds1}]==Length[{inds2}]):=
		IndexPower[head,2][inds1,inds3];
	head/:IndexPower[head,n_][inds1__,inds2__]head[inds2__,inds3__]/;(Length[{inds1}]==Length[{inds2}]):=
		IndexPower[head,n+1][inds1,inds3];
	head/:head[inds1__,inds2__]IndexPower[head,n_][inds2__,inds3__]/;(Length[{inds1}]==Length[{inds2}]):=
		IndexPower[head,n+1][inds1,inds3];
	
	(*Define the norm of a tensor*)
	(*head/:head[inds___]^2/;(Length[{inds}]==Rank[head]):=head^2*);
	
	(*Add symmetries to the tensor*)
	syms=OptionValue[Symmetries];
	Do[AddSymmetry[head,syms[x],x], {x, Keys[syms]}];
];


(* ::Subsubsection:: *)
(*Index manipulations*)


GetIndices[_?IndexQ[inds___]]:={inds};
GetIndices[HoldForm[expr_]]:=GetIndices[expr]
GetIndices[expr_Times]:=Flatten[GetIndices/@(List@@expr)]
GetIndices[expr_Power]:=Flatten[GetIndices/@{expr[[1]],expr[[1]]}]
GetIndices[head_?IndexQ]:={}/;Head[head]==Symbol;
GetIndices[x_]:={};

GetIndices[_?IndexQ[inds___],slots_]:={inds}[[slots]];

GetFreeIndices[expr_]:=Flatten[{Cases[Tally@GetIndices[expr], {_, 1}][[All,1]]}]
GetDummyIndices[expr_]:=Flatten[{Cases[Tally@GetIndices[expr], {_,z_Integer}/;z>1][[All,1]]}]

ContainsIndices[expr_,ind_]:=MemberQ[expr//GetIndices,ind];

(*extract the indices of particular terms*)
GetIndicesTerms[expr_Times,x_]:=Flatten[GetIndicesTerms[#,x]&/@(List@@expr)];
GetIndicesTerms[expr_Power,x_]:=Flatten[GetIndicesTerms[#,x]&/@{expr[[1]],expr[[1]]}];
GetIndicesTerms[x_[inds__],x_]:={inds};
GetIndicesTerms[expr_,x_]:={};



(*Contract indices*)
ContractIndices[expr_Plus]:=ContractIndices[#]&/@expr;
ContractIndices[(x_+y_)z_]:=ContractIndices[x z]+ContractIndices[y z];
ContractIndices[expr_]:=Module[{return,dums},
	dums=expr//GetDummyIndices;
	return=expr/.Thread[ dums->Take[$internalDummies,Length[dums]] ];
	(*This replaces dummy indices with a new symbol in the package context*)
	return=ReleaseHold[
		ReplacePart[With[{x=return},Hold[Module[{},x]]],GetDummyIndices[return],{1,1}]
	];
	dums = return//GetDummyIndices;
	(*Remove from the local context for prettier look*)
	return/.Thread[dums->SymbolName/@dums]
]


(*Index replacement operations*)
ReplaceIndices[expr_,oldInds_,newInds_]:=expr/.Thread@(oldInds->newInds)

(*Done use multiplication rules like this, it scales as N!*)
(*PrettyIndices[x_?NumericQ expr_]:=x PrettyIndices[expr];*)
PrettyIndices[expr_Plus]:=PrettyIndices[#]&/@expr;

PrettyIndices[expr_]:=Module[{oldInds,newInds,dummies},
	oldInds=Complement[GetDummyIndices[expr]];
	dummies=Complement[$dummyIndices,GetFreeIndices[expr]];
	If[Length[dummies]<Length[oldInds],
		Message[PrettyIndices::dummies,Length[dummies],Length[oldInds]];
		Return[expr];
	];
	newInds=Take[Complement[$dummyIndices,GetFreeIndices[expr]],Length[oldInds]];
	ReplaceIndices[expr,oldInds,newInds]
]


(* ::Subsubsection:: *)
(*Function manipulations*)


SetAttributes[IndexSet,{HoldFirst}]
IndexSet[lhs_,rhs_]:=ReplacePart[Hold[lhs:=ContractIndices[rhs]],rhs//IndexSimplify//ContractIndices,{1,2,1}]//ReleaseHold;
DotEqual=IndexSet;


(* ::Subsubsection:: *)
(*Symmetry relations*)


(*By default tensor objects have no symmetry*)
SymmetryQ[___]:=False;

(*We can use projection operators in list form*)
ProjectionOperator[f_][inds1_List,inds2_List]:=ProjectionOperator[f][Sequence@@inds1,Sequence@@inds2];

$part1[x__]:={x}[[1;;Length[{x}]/2]];
$part2[x__]:={x}[[Length[{x}]/2+1;;Length[{x}]]];

(*Adds an identity for a an index symmetry*)
AddIdentity[head_,projOperator_,inds_]:=Module[{},
	Off[Part::partw];
	head/:head[inds2__]projOperator[inds1__]/;ContainsAll[{inds2}[[inds]],$part1[inds1]]:=
		ReplaceIndices[ head[inds2], $part1[inds1], $part2[inds1] ];
	head/:head[inds2__]projOperator[inds1__]/;ContainsAll[{inds2}[[inds]],$part2[inds1]]:=
		ReplaceIndices[ head[inds2], $part2[inds1], $part1[inds1] ];
	On[Part::partw];
];

AddOrthogonal[head_,projOperator_,inds_]:=Module[{},
	Off[Part::partw];
	head/:head[inds2__]projOperator[inds1__]/;ContainsAll[{inds2}[[inds]],$part1[inds1]]:=0;
	head/:head[inds2__]projOperator[inds1__]/;ContainsAll[{inds2}[[inds]],$part2[inds1]]:=0;
	On[Part::partw];
];

AddSymmetry[head_,List[inds__List],"symmetric"]:=Scan[AddSymmetry[head,#,"symmetric"]&,List[inds]];
AddSymmetry[head_,inds_,"symmetric"]:=Module[{},
	head[inds2__]/;!OrderedQ[{inds2}[[inds]]]:=head@@ReplaceIndices[{inds2},{inds2}[[inds]],Sort[{inds2}[[inds]]]];
	
	AddIdentity[head,PermDelta,inds];
	AddOrthogonal[head,GDelta,inds];
	
	head/:SymmetryQ[head,inds2_,"symmetric"]:=ContainsAll[inds,inds2];
	(*SymmetrySimplify[head[inds2__]]^=ReplaceIndices[head[inds2],Sort@@GetIndices[head[inds2]],inds]*)
]

AddSymmetry[head_,List[inds__List],"antisymmetric"]:=Scan[AddSymmetry[head,#,"antisymmetric"]&,List[inds]];
AddSymmetry[head_,inds_,"antisymmetric"]:=Module[{},
	head[inds2__]/;!OrderedQ[{inds2}[[inds]]]:=Signature[{inds2}[[inds]]]
		head@@ReplaceIndices[{inds2},{inds2}[[inds]],Sort[{inds2}[[inds]]]];
		
	AddIdentity[head,GDelta,inds];
	AddOrthogonal[head,PermDelta,inds];
	AddOrthogonal[head,Delta,inds];
	
	AddSymmetry[head,inds,"traceless"];
			
	head/:SymmetryQ[head,inds2_,"antisymmetric"]:=ContainsAll[inds,inds2];
	]

AddSymmetry[head_,List[inds__List],"irreducible"]:=Scan[AddSymmetry[head,#,"irreducible"]&,List[inds]];
AddSymmetry[head_,inds_,"irreducible"]:=Module[{},
	AddSymmetry[head,inds,"symmetric"];
	AddSymmetry[head,inds,"traceless"];

	AddIdentity[head,Delta,inds];

	head/:SymmetryQ[head,inds2_,"irreducible"]:=ContainsAll[inds,inds2];
]

AddSymmetry[head_,List[inds__List],"traceless"]:=Scan[AddSymmetry[head,#,"traceless"]&,List[inds]];
AddSymmetry[head_,inds_,"traceless"]:=Module[{},
	head[inds2__]/;Signature[{inds2}[[inds]]]==0:=0;

	head/:SymmetryQ[head,inds2_,"traceless"]:=ContainsAll[inds,inds2];
]

AddSymmetry[head_,inds_,"blocksymmetric"]:=Module[{},
	head[inds2__]/;!OrderedQ[{inds2}[[#]]&/@inds]:=head@@ReplaceIndices[{inds2},
		Flatten[{inds2}[[#]]&/@inds],Flatten[Sort[{inds2}[[#]]&/@inds]] ];
]

AddSymmetry[head_,inds_,"blockantisymmetric"]:=Module[{},
	head[inds2__]/;!OrderedQ[{inds2}[[#]]&/@inds]:=head@@ReplaceIndices[{inds2},
		Flatten[{inds2}[[#]]&/@inds],Flatten[Sort[{inds2}[[#]]&/@inds]] ];
]


(*Construct the symmetry operator for a tensor*)
ConstructProjector[proj_,inds1_,List[inds__List],"symmetric"]:=Scan[ConstructProjector[proj,#,"symmetric"]&,List[inds]];
ConstructProjector[proj_,inds1_,inds_,"symmetric"]:=Module[{out},
	out = ReplaceIndices[proj,inds1[[inds]],$internalDummies2[[inds]]];
	ContractIndices[out PermDelta[inds1[[inds]],$internalDummies2[[inds]]]]
]

ConstructProjector[proj_,inds1_,List[inds__List],"antisymmetric"]:=Scan[ConstructProjector[proj,#,"antisymmetric"]&,List[inds]];
ConstructProjector[proj_,inds1_,inds_,"antisymmetric"]:=Module[{out},
	out=ReplaceIndices[proj,inds1[[inds]],$internalDummies2[[inds]]];
	ContractIndices[out GDelta[inds1[[inds]],$internalDummies2[[inds]]]]
]

ConstructProjector[proj_,inds1_,List[inds__List],"irreducible"]:=Scan[ConstructProjector[proj,#,"irreducible"]&,List[inds]];
ConstructProjector[proj_,inds1_,inds_,"irreducible"]:=Module[{out},
	out=ReplaceIndices[proj,inds1[[inds]],$internalDummies2[[inds]]];
	ContractIndices[out Delta[inds1[[inds]],$internalDummies2[[inds]]]]
]

ConstructProjector[proj_,inds1_,List[inds__List],"traceless"]:=Scan[ConstructProjector[proj,#,"traceless"]&,List[inds]];
ConstructProjector[proj_,inds1_,inds_,"traceless"]:=Module[{freeInds},
	proj
]


(*Simplify expressions with symmetries*)
(*SymmetryReduce[expr1_+expr2_]:=SymmetryReduce[expr1]+SymmetryReduce[expr2];*)
SymmetryReduce[expr_Plus]:=SymmetryReduce[#]&/@expr
SymmetryReduce[expr1_(expr2_+expr3_)]:=SymmetryReduce[expr1 expr2]+SymmetryReduce[expr1 expr3];

SymmetryReduce[expr_Times]:=Module[{dums,termsList,preFac},
	dums=expr//GetDummyIndices;
	termsList=List@@expr//Cases[head_?IndexQ[inds__]/;IntersectingQ[dums,{inds}]];
	If[Length[termsList]<2,Return[expr]];
	
	preFac=expr/(Times@@termsList);
	termsList=ProjectorForm/@termsList;
	termsList=termsList/.HoldForm[x_]y_->{x,y};
	termsList=Times@@termsList;
	
	(*we need the preFac inside so dummy indices aren't double counted*)
	PrettyIndices[preFac ContractIndices[Expand[IndexExpand[termsList[[1]]]termsList[[2]]]]]
];

SymmetryReduce[expr_]:=expr;

ProjectorForm[head_?IndexQ[inds__]]:=With[{proj=ProjectionOperator[head][{inds},Take[$internalDummies,Length[{inds}]]]},
	HoldForm[proj] head[Take[$internalDummies,Length[{inds}]]]//ContractIndices
];


(* ::Subsection:: *)
(*Tensor-algebra*)


(*builtin tensors*)
SetAttributes[delta,Orderless]
DefTensor[delta,"\[Delta]",2,Idempotent->True,ConstantTensor->True]
SetAttributes[delta,Orderless]
(*We need to define dummpy replacement this way so it is not slow*)
delta/:delta[i_,j_] head_?IndexQ[inds1___,j_,inds2___]:=head[inds1,i,inds2]
delta[i_,i_]:=$nDim;
delta/:delta[i_,j_]^2:=$nDim;

(*Constructs symmetric product of deltas with a given set of indices*)
Symdelta[inds__]:=Symdelta[{inds}];
Symdelta[{}]:=1;
Symdelta[{i_,j_}]:=delta[i,j];
Symdelta[inds_List]/;EvenQ[Length[inds]]:=Sum[delta[inds[[1]],inds[[n]]]
	Symdelta[Complement[inds,inds[[{1,n}]]]],{n,2,Length[inds]}]/(Length[inds]-1);


(*Operators for expanding tensor functions*)
IndexExpand[expr_]:=expr//.$indexExpand;


(* ::Subsubsection:: *)
(*Projection operators*)


(*helper functions*)

(*splits indices list into two functions arguments*)
$splitInds[inds__]:=Sequence@@Partition[{inds},Length[{inds}]/2 ];

ProjectorSimplify[expr_]:=expr//.$projectorSimplify


(*Projection operator for symmetric tensors*)	
$projectorSimplify=Join[$projectorSimplify,
	{PermDelta[inds1__,inds2__]head_?IndexQ[inds3__]/;(Length[{inds1}]==Length[{inds2}])&&
		ContainsAll[{inds3},{inds2}]&&SymmetryQ[head,Flatten[Position[{inds3},#]&/@{inds2}],"symmetric"]:>
		ReplaceIndices[head[inds3],{inds2},{inds1}],
	PermDelta[inds2__,inds1__]head_?IndexQ[inds3__]/;(Length[{inds1}]==Length[{inds2}])&&
		ContainsAll[{inds3},{inds2}]&&SymmetryQ[head,Flatten[Position[{inds3},#]&/@{inds2}],"symmetric"]:>
		ReplaceIndices[head[inds3],{inds2},{inds1}]}
];


DefTensor[PermDelta,"\[CapitalPi]",ProjectionSuperscript->True,Idempotent->True,ConstantTensor->True];
PermDelta[]:=1;
PermDelta[i_,j_]:=delta[i,j]/;!(Head[i]===Pattern)&&!(Head[j]===Pattern)


$dimSym[n_]:=Binomial[$nDim+n-1,n];

PermDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&IntersectingQ[{inds1},{inds2}]):=
	PermDelta[Complement[{inds1},{inds2}],Complement[{inds2},{inds1}]]$dimSym[Length[{inds1}]]/$dimSym[Length[Complement[{inds1},{inds2}]]];
PermDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{inds1}])):=PermDelta[Sort[{inds1}],inds2];
PermDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{inds2}])):=PermDelta[inds1,Sort[{inds2}]];
PermDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{{inds1},{inds2}}])):=PermDelta[inds2,inds1];

$indexExpand=Join[$indexExpand,{PermDelta[inds___]:>
	Permanent[Outer[delta,$splitInds[inds]]]/(Length[{inds}]/2)!}];


(*Projection operator for antisymmetric tensors*)	
$projectorSimplify=Join[$projectorSimplify,
	{GDelta[inds1__,inds2__]head_?IndexQ[inds3__]/;(Length[{inds1}]==Length[{inds2}])&&
		ContainsAll[{inds3},{inds2}]&&SymmetryQ[head,Flatten[Position[{inds3},#]&/@{inds2}],"antisymmetric"]:>
		ReplaceIndices[head[inds3],{inds2},{inds1}],
	GDelta[inds2__,inds1__]head_?IndexQ[inds3__]/;(Length[{inds1}]==Length[{inds2}])&&
		ContainsAll[{inds3},{inds2}]&&SymmetryQ[head,Flatten[Position[{inds3},#]&/@{inds2}],"antisymmetric"]:>
		ReplaceIndices[head[inds3],{inds2},{inds1}]}
];

$dimAnt[n_]:=Binomial[$nDim,n]

DefTensor[GDelta,"\[ScriptCapitalE]",ProjectionSuperscript->True,Idempotent->True,ConstantTensor->True];
GDelta[]:=1;
GDelta[i_,j_]:=delta[i,j]/;!(Head[i]===Pattern)&&!(Head[j]===Pattern)

GDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&IntersectingQ[{inds1},{inds2}]):=Module[{inters,inds1c,inds2c},
	inters=Intersection[{inds1},{inds2}];
	inds1c=Complement[{inds1},{inds2}];
	inds2c=Complement[{inds2},{inds1}];
	Signature[{inds1}]Signature[Join[inds1c,inters]]Signature[{inds2}]Signature[Join[inds2c,inters]]GDelta[inds1c,inds2c]$dimAnt[Length[{inds1}]]/$dimAnt[Length[inds1c]]
];
GDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{inds1}])):=Signature[{inds1}]GDelta[Sort[{inds1}],inds2];
GDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{inds2}])):=Signature[{inds2}]GDelta[inds1,Sort[{inds2}]];
GDelta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{{inds1},{inds2}}])):=GDelta[inds2,inds1];
$indexExpand=Join[$indexExpand,{GDelta[inds___]:>Det[Outer[delta,$splitInds[inds]]]/(Length[{inds}]/2)!}];


(*Projection operator for irreducible tensors*)	
$projectorSimplify=Join[$projectorSimplify,
	{Delta[inds1__,inds2__]head_?IndexQ[inds3__]/;(Length[{inds1}]==Length[{inds2}])&&
		ContainsAll[{inds3},{inds2}]&&SymmetryQ[head,Flatten[Position[{inds3},#]&/@{inds2}],"irreducible"]:>
		ReplaceIndices[head[inds3],{inds2},{inds1}],
	Delta[inds2__,inds1__]head_?IndexQ[inds3__]/;(Length[{inds1}]==Length[{inds2}])&&
		ContainsAll[{inds3},{inds2}]&&SymmetryQ[head,Flatten[Position[{inds3},#]&/@{inds2}],"irreducible"]:>
		ReplaceIndices[head[inds3],{inds2},{inds1}]}
];

$dimIrr[n_]:=(-2+$nDim+2 n)/(-2+$nDim+n) Binomial[$nDim+n-2,n]

DefTensor[Delta,"\[CapitalDelta]",ProjectionSuperscript->True,Idempotent->True,ConstantTensor->True];
Delta[]:=1
Delta[i_,j_]:=delta[i,j]/;!(Head[i]===Pattern)&&!(Head[j]===Pattern)

Delta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&IntersectingQ[{inds1},{inds2}]):=
	Delta[Complement[{inds1},{inds2}],Complement[{inds2},{inds1}]]$dimIrr[Length[{inds1}]]/$dimIrr[Length[Complement[{inds1},{inds2}]]];
Delta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{inds1}])):=Delta[Sort[{inds1}],inds2];
Delta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{inds2}])):=Delta[inds1,Sort[{inds2}]];
Delta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(Signature[{inds1}]==0||Signature[{inds2}]==0)):=0;
Delta[inds1__,inds2__]/;(Length[{inds1}]==Length[{inds2}]&&
	(!OrderedQ[{{inds1},{inds2}}])):=Delta[inds2,inds1];


(*Generates the product of two functions symmetric in inds1 and inds2*)
$symmetricFunction[head1_,head2_,inds1_,inds2_,n_]:=Module[
	{subs1,subs2,comps1,comps2,perms1,perms2},
	subs1=Subsets[inds1,{n,n}];
	subs2=Subsets[inds2,{n,n}];
	comps1=Complement[inds1,#]&/@Subsets[inds1,{n,n}];
	comps2=Complement[inds2,#]&/@Subsets[inds2,{n,n}];
	perms1=Length[subs1];
	perms2=Length[subs2];
	Plus@@Flatten[Outer[head1,subs1,subs2,1]*Outer[head2,comps1,comps2,1]]/perms1/perms2
];

(*coefficients for the expansion of the Delta function:
Mane, Nucl. Instrum. Methods Phys. Res. A: Accel. Spectrom. Detect. Assoc. Equip. (2013)*) 
$c[n_,p_]:=(-1/2)^p n!/p!/(n-2p)!(2n-2p+$nDim-4)!!/(2n+$nDim-4)!!;
$nDim=3;
$indexExpand=Join[$indexExpand,{Delta[inds___]:>
	Sum[$c[Length[{inds}]/2,p]$symmetricFunction[Symdelta[#1]Symdelta[#2]&,PermDelta,$splitInds[inds],2p],
	{p,0,Floor[Length[{inds}]/4]}]}
	];
	
(*Projection of a rank-p irreducible tensor onto a symmetric rank-n tensor*)
(*The lower-order harmonic is internal for now, might be worthwhile to expose it*)
(*This method arrises from the requirement that the projection operator gives the correct dimensionality*)
(*This method is unsatisfying, would be better to get something nicer*)
$Delta[n_][inds__]:=Block[{base},
	base=$symmetricFunction[Delta,Symdelta[#1]Symdelta[#2]&,$splitInds[inds],p];
	base Sqrt[Delta[Take[{inds},p],Take[{inds},p]]/Expand[IndexExpand[Expand[base base]]]]
]



(*Projection operators for isotropic harmonic tensors*)
Delta[p_?IntegerQ][inds__]:=$symmetricFunction[]


(*Symmetries*)
(*ProjectionOperator[head_][inds___]/;Length[{inds}]==2*Rank[head]:=
	Inner[delta,Sequence@@Partition[{inds},Rank[head]],Times];*)
$a[n_,p_]:=(2n-1)!!($nDim+2p-2)!!Binomial[2n+p,p]/(2n+2p+$nDim-2)!!;
Delta[p_?IntegerQ][inds__]:=$a[(Length[{inds}]/2-p)/2,p]$symmetricFunction[Delta,Symdelta[#1]Symdelta[#2]&,
	$splitInds[inds],p];


(* ::Subsubsection:: *)
(*Built-in tensors*)


$indexExpand=Join[$indexExpand,{HoldPattern[LeviC[inds1__]LeviC[inds2__]]:>$nDim!GDelta[{inds1,inds2}]}];
$functionSimplify=Join[$functionSimplify,{HoldPattern[LeviC[___,i_,___,j_,___]x_?IndexQ[i_]x_?IndexQ[j_]]:>0}]

DefTensor[LeviC,"\[CurlyEpsilon]",$nDim,ConstantTensor->True,Symmetries-><|"antisymmetric"->Table[n,{n,1,$nDim}]|>];


(* ::Subsubsection:: *)
(*Simplification rules*)


(*Simplify Indices*)
SimplifyIndices[expr_]:=expr//Expand

(*Full simplification*)
IndexSimplify[expr_]:=FixedPoint[Expand[ReplaceRepeated[Expand[#],$functionSimplify]//ContractIndices//PrettyIndices//ProjectorSimplify]&,expr];


(* ::Subsection:: *)
(*Functions*)


(* ::Subsubsection:: *)
(*Tensor-valued functions*)


(*Functions of a tensor*)
IndexQ[IndexPower[__][__]]:=True;
IndexQ[IndexPower[__]]:=True;
DependsQ[IndexPower[head1_Symbol,_],head2_Symbol]:=DependsQ[head1,head2];

IndexPower[_,0][inds__]:=delta[inds];
IndexPower[head_,1][inds__]:=head[inds];

IndexPower[head_?IdempotentQ,_][inds__]:=head[inds];

IndexPower[x_?ScalarQ expr_,n_]:=x^n IndexPower[expr,n];

IndexPower/:IndexPower[head_,n_][inds1__,inds2__]IndexPower[head_,p_][inds2__,inds3__]/;(Length[{inds1}]==Length[{inds2}]):=
		IndexPower[head,n+p][inds1,inds3];

GetIndices[IndexPower[expr_,_][inds__]]:={inds};



(*Spherical harmonics*)
IndexQ[IndexHarmonic[_,_][__]]:=True;
IndexQ[IndexHarmonic[_,_]]:=True;
DependsQ[IndexHarmonic[head1_Symbol,_],head2_Symbol]:=DependsQ[head1,head2];

(*The harmonic tensor is symmetric and traceless*)
ProjectionOperator[IndexHarmonic[head_,n_]][inds___]:=Delta[inds];
IndexHarmonic/:SymmetryQ[IndexHarmonic[head_,n_],
	inds2_,"symmetric"]:=True;
IndexHarmonic/:SymmetryQ[IndexHarmonic[head_,n_],
	inds2_,"irreducible"]:=True;

IndexHarmonic[head_,n_][inds_List]:=IndexHarmonic[head,n]@@inds;
IndexHarmonic[head_,n_][inds__]/;(Length[{inds}]!=n):=Message[IndexHarmonic::rank,Length[{inds}],
		n,head]

TensorSymbol[IndexHarmonic[head_?IndexQ,n_]]:=ToBoxes[IndexHarmonic[head,n]]

IndexHarmonic[head_,0][]:=1;
IndexHarmonic[head_,1][i_]:=head[i]/Norm[head]

IndexHarmonic[head_,n_][inds__]/;!OrderedQ[{inds}]:=IndexHarmonic[head,n][Sequence@@Sort[{inds}]];
IndexHarmonic[head_,n_][inds__]/;!DuplicateFreeQ[{inds}]:=0;

(*(19) of Ehrentraut, H. Muschik, W. 1998*)
IndexHarmonic/:IndexHarmonic[head_,n_][inds__]head_[i_]/;MemberQ[{inds},i]:=
	(n+$nDim-3)/(2*n+$nDim-4)*IndexHarmonic[head,n-1][Sequence@@Complement[{inds},{i}]]Norm[head];
	
(*(21) of Ehrentraut, H. Muschik, W. 1998*)
(*IndexHarmonic/:IndexHarmonic[head_,n_][inds__]head_[i_]/;!MemberQ[{inds},i]:=Module[{dums},
		dums=Take[$internalDummies,n-1];
		dums=ReleaseHold[ReplacePart[With[{dum=dums},Hold[Module[{},dum]]],dums,{1,1}]];
		IndexHarmonic[head,n+1][i,inds]Norm[head]+
			Expand[Norm[head]n/(2n+$nDim-2)IndexExpand[Delta[inds,Sequence@@dums,i]]IndexHarmonic[head,n-1][dums]]
		]*)
(*It's faster if we write this out explicitly*)
IndexHarmonic/:IndexHarmonic[head_,n_][inds__]head_[i_]/;!MemberQ[{inds},i]:=
	IndexHarmonic[head,n+1][i,inds]Norm[head]+
	Expand[Norm[head]n/(2n+$nDim-2)Block[{$i,$j},
		Sum[delta[i,{inds}[[$i]]]IndexHarmonic[head,n-1][Delete[{inds},$i]],{$i,1,n}]/n-
		2/n Sum[Sum[delta[{inds}[[{$i,$j}]]]IndexHarmonic[head,n-1][Append[Delete[{inds},{{$i},{$j}}],i]]
			,{$j,$i+1,n}],{$i,1,n}]/(2n+$nDim-4)]];
	
(*We could do this without the Delta if we wished*)
HarmonicToCartesian[expr_]:=expr//.{IndexHarmonic[head_?IndexQ,n_][inds__]:>
	Module[{dums},
		dums=Take[$internalDummies,n];
		dums=ReleaseHold[ReplacePart[With[{dum=dums},Hold[Module[{},dum]]],dums,{1,1}]];
		(IndexExpand[Delta[{inds},{dums}]]Times@@head/@dums)/Norm[head]^n//IndexSimplify
	]}
	
(*Not implemented yet*)
CartesianToHarmonic[expr_,head_?IndexQ]:=expr//.{head[i_]IndexHarmonic[head,n_][inds__]:>
	Module[{dums},
		dums=Take[$internalDummies,n-1];
		dums=ReleaseHold[ReplacePart[With[{dum=dums},Hold[Module[{},dum]]],dums,{1,1}]];
		IndexHarmonic[head,n+1][i,inds]Norm[head]+
			n/(2n+$nDim-2)Expand[IndexExpand[inds,Sequence@@dums,i]IndexHarmonic[head,n-1][dums]]
		]}
	


(* ::Subsubsection:: *)
(*Scalar-functions*)


(*norm of a tensor*)
$functionSimplify=Join[$functionSimplify,{(tens_?IndexQ[i_])^2:>Norm[tens]^2}];
IndexQ[Norm[_?IndexQ]]:=True;

(*dot product of two tensors*)
$functionSimplify=Join[$functionSimplify,{tens1_?IndexQ[i_]tens2_?IndexQ[i_]:>Dot[Sequence@@Sort[{tens1,tens2}]]}]
IndexQ[Dot[_?IndexQ,_?IndexQ]]:=True;


(*simplify tensor-valued functions*)
PrincipalInvariant[expr_,0]:=1;
PrincipalInvariant[delta,n_Integer]:=Binomial[$nDim,n];
IndexQ[PrincipalInvariant[__]]:=True;

(*Expand invariants in terms of powers*)
(*Dui and Chen 2005*)
$functionSimplify=Join[$functionSimplify,
	{PrincipalInvariant[tens_,n_?IntegerQ]/;n>0:>-Sum[(-1)^i PrincipalInvariant[tens,n-i]Tr[tens,i],{i,1,n}]/n,
	PrincipalInvariant[tens_,n_?IntegerQ]/;n>$nDim->0,
	Tr[tens_,n_?IntegerQ]/;n>$nDim :>-Sum[(-1)^i PrincipalInvariant[tens,i]Tr[tens,n-i],{i,1,$nDim}]}];

IndexQ[Det[head_?IndexQ]]:=True;
delta/:Det[delta]:=1;
IndexQ[Tr[head_?IndexQ]]:=True;
delta/:Tr[delta]:=3;
delta/:Tr[delta,n_]:=3;

$functionSimplify=Join[$functionSimplify,{PrincipalInvariant[tens_,n_?IntegerQ]:>0/;Rank[tens]==2&&n>$nDim}];
$functionSimplify=Join[$functionSimplify,{PrincipalInvariant[tens_,$nDim]:>Det[tens]/;Rank[tens]==2}];
$functionSimplify=Join[$functionSimplify,{IndexPower[tens_,n_][i_,i_]:>Tr[tens,n]/;Rank[tens]==2}];
$functionSimplify=Join[$functionSimplify,{tens_?IndexQ[i_,i_]:>Tr[tens]/;Rank[tens]==2}];
$functionSimplify=Join[$functionSimplify,{Tr[tens_?IndexQ,1]->Tr[tens]}];


(* ::Subsection:: *)
(*Tensor Calculus*)


(* ::Subsubsection:: *)
(*Derivatives*)


(*tensor calculus*)
(*Derivative of a constant is zero*)
Di[_?NumericQ,_]:=0;
Di[x_Symbol,_]:=0;
Di[head_?ConstantTensorQ[___],_]:=0; 

(*Derivatives can be nested as a list or a sequence*)
Di[expr_,{tens1_,tens_}]:=Di[Di[expr,tens1],tens]
Di[expr_,{tens1_,tens__}]:=Di[Di[expr,tens1],{tens}]
Di[expr_,tens1_,tens_]:=Di[Di[expr,tens1],tens]
Di[expr_,tens1_,tens__]:=Di[Di[expr,tens1],tens]

(*The operator is linear*)
(*Di[x_?NumericQ y_,tens_]:=x Di[y,tens];*)
(*Di[x_+y_,tens_]:=Di[x,tens]+Di[y,tens];*)
Di[expr_Plus,tens_]:=Di[#,tens]&/@expr

(*The operator can act on asymptotic series*)
(*Di[HoldPattern@SeriesData[x_,x0_,terms_List,nmin_,nmax_,den_],tens_]:=
	SeriesData[x,x0,Di[#,tens]&/@terms,nmin,nmax,den];*)

(*We can pull out a negative sign from argument*)
Di[expr_,-tens_]:=-Di[expr,tens];

(*There is a product rule for the operator*)
Di[x_ y_,tens_]:=x Di[y,tens]+Di[x,tens]y;

(*Leibnitz rule for integrals*)
Di[Integrate[expr_,{y_,a_,b_}],tens_]:=(expr/.y->b)Di[b,tens]-(expr/.y->a)Di[a,tens]
	+Integrate[Di[expr,tens],{y,a,b}];

(*Distributive rule for multiple variable function*)
Di[f_[arg_],tens_]/;!IndexQ[f[arg]]:=f'[arg]Di[arg,tens];
Di[f_[args__],tens_]/;!IndexQ[f[args]]/;!MemberQ[{args},_List]:=
	Plus@@(Di[{args}[[#]],tens] Derivative[ Sequence@@Table[Boole[j==#],{j,1,Length[{args}]}]][f][args]&/@Table[i,{i,1,Length[{args}]}])

(*Derivative of a tensor with itself*)
(*Di[head_[inds1__],head_?IndexQ[inds2__]]:=ProjectionOperator[head][inds1,inds2];
(*Compute the derivative of a tensor with symmetries*)
Di[expr_,head_?IndexQ[inds2__]]:=Module[{uniqueInds,dummyTens},
	uniqueInds=DeleteDuplicates[{inds2}];
	dummyTens=ReplaceIndices[head[inds2],uniqueInds,Take[$internalDummies,Length[uniqueInds]]];
	ContractIndices[Dp[expr,dummyTens]Di[dummyTens,head[inds2]]](*//SimplifyIndices*)
];*)
Di[expr_,head_?IndexQ[inds2__]]:=Module[{dummyInds},
	dummyInds=Take[$internalDummies,Length[{inds2}]];
	ContractIndices[Dp[expr,head][dummyInds]ProjectionOperator[head][dummyInds,{inds2}]]//SimplifyIndices
];


(*Derivatives of defined functions*)
IndexQ[Dp[__]]:=True;
Dp/:GetIndices[Dp[expr_,head_][inds__]]:=Flatten[{GetIndices[expr],{inds}}];
Dp[expr_,head_][inds_List]:=Dp[expr,head][Sequence@@inds]

(*Dirac delta simplicication rules for partial derivatives*)
Dp/:delta[i_,j_]Dp[expr_, head_?IndexQ][inds1___,j_,inds2___]:=Dp[expr,head][inds1,i,inds2]
Dp/:delta[i_,j_]Dp[ head_?IndexQ[inds1___,j_,inds2___],tens_][inds__]:=Dp[head[inds1,i,inds2],tens][inds]

(*Generic partial derivatives*)
Dp[expr_?NumericQ,__]:=0
Dp[head_[inds1__],head_?IndexQ][inds2__]:=Inner[delta,{inds1},{inds2},Times]
Dp[head1_?IndexQ[inds1__],head2_?IndexQ][inds2__]:=0/;!DependsQ[head1,head2]


(*Derivatives of tensor-valued functions*)
Dp[IndexPower[head_,n_?IntegerQ][i_,j_],head_][k_,l_]/;n>0:=Module[{p},
	Sum[IndexPower[head,p][i,k]IndexPower[head,n-1-p][l,j],{p,0,n-1}]
];
Dp[IndexPower[head_,n_?IntegerQ][i_,j_],head_][k_,l_]/;n<0:=Module[{p},
	Sum[-IndexPower[head,p][i,k]IndexPower[head,n-1-p][l,j],{p,n,-1}]
];

Dp[IndexHarmonic[head_,n_][inds__],head_][i_]:=
	(2-$nDim-2n)IndexHarmonic[head,n+1][i,inds]/Norm[head]+
	($nDim+n-2)head[i]IndexHarmonic[head,n][inds]/Norm[head]^2;


(*Dervatives of tensor invariants*)
(*Maybe should make the dependency more general later, in terms of chain rule*)
Dp[Norm[head_],head_?IndexQ][inds__]:=head[inds]/Norm[head];
Dp[Norm[tens_],head_?IndexQ][inds__]:=
	Dp[tens[Take[$internalDummies,Rank[tens]]],head][inds]*
	tens[Take[$internalDummies,Rank[tens]]]/Norm[tens];

Dp[Dot[head_,head2_],head3_?IndexQ][inds__]:=0/;!DependsQ[head,head3]&&!DependsQ[head2,head3]
Dp[Dot[head_,head2_],head_?IndexQ][inds__]:=ReverseApplied[head2][inds];
Dp[Dot[head2_,head_],head_?IndexQ][inds__]:=ReverseApplied[head2][inds];

(*Equation 9 of Dui and Chen 2007*)
(*It might be useful to extend this to higher-rank tensors in the future*)
Dp[PrincipalInvariant[head_?IndexQ,n_?IntegerQ],head_?IndexQ][i_,j_]/;n>0:=
	Sum[(-1)^p PrincipalInvariant[head,n-1-p]IndexPower[head,p][j,i],{p,0,n-1}]
	
(*Derivatives of builtin functions*)
Dp[Det[tens_],tens_?IndexQ][i_,j_]:=Det[tens]IndexPower[tens,-1][j,i];
Dp[Tr[tens_],tens_?IndexQ][i_,j_]:=delta[i,j];
Dp[Tr[tens_,n_],tens_?IndexQ][i_,j_]:=n IndexPower[tens,n-1][j,i];


(* ::Subsubsection:: *)
(*Integrals*)


(*Integrals of a vector tensor over a surface*)
SurfaceIntegral[a_(b_+c_),surf_]:=SurfaceIntegral[a b,surf]+SurfaceIntegral[a c,surf];
SurfaceIntegral[a_+b_,surf_]:=SurfaceIntegral[a,surf]+SurfaceIntegral[b,surf];

SurfaceIntegral[0,surf_]:=0

SurfaceIntegral[expr_,{x_,a_}]/;Rank[x]==1:=Module[{inds,n,out},
	out=expr//.{Dot[x,y_]^n_:>Module[{j},x[j]y[j]]Dot[x,y]^(n-1),Dot[x,y_]:>Module[{j},x[j]y[j]],
		Dot[y_,x]^n_:>Module[{j},x[j]y[j]]Dot[y,x]^(n-1),Dot[y_,x]:>Module[{j},x[j]y[j]]};
	inds=GetIndicesTerms[out,x];
	n=Length[inds];
	If[n//OddQ, 0,
		Symdelta[inds]4\[Pi] (n-1)!!/(n+1)!! a^(n+2) (out /.{x[_]->1,Norm[x]->a})
	]
];


(* ::Subsection:: *)
(*Formatting*)


(*Formating displays in standard form*)
MakeBoxes[IndexPower[head_?IndexQ,n_][inds___], StandardForm] := 
	SubsuperscriptBox[TensorSymbol[head],StringJoin@(ToString/@{inds}),MakeBoxes[n]];

MakeBoxes[head_?ProjectionSuperscriptQ[inds___], StandardForm] := 
	SubsuperscriptBox[TensorSymbol[head],StringJoin@(ToString/@{inds}),
	"("<>ToString[Length[{inds}]/2]<>","<>ToString[Length[{inds}]/2]<>")"];

MakeBoxes[Dp[x_,y_][inds__], StandardForm]:=
	RowBox[{FractionBox["\[PartialD]",RowBox[{"\[PartialD]",MakeBoxes[y[inds]]}]] ,MakeBoxes[x]}];

MakeBoxes[head_?IndexQ[inds___], StandardForm] := 
	SubscriptBox[TensorSymbol[head],StringJoin@(ToString/@{inds})];
	
MakeBoxes[Norm[head_?IndexQ], StandardForm]:=TemplateBox[{StyleBox[TensorSymbol[head],Bold]},"Norm"];
MakeBoxes[PrincipalInvariant[head_?IndexQ,n_?IntegerQ], StandardForm]:=SubsuperscriptBox["I",n,TensorSymbol[head]];

MakeBoxes[head_?IndexQ[inds___]^2, StandardForm]:=RowBox[{MakeBoxes[head[inds]],MakeBoxes[head[inds]]}];

MakeBoxes[Det[head_?IndexQ], StandardForm]:=RowBox[{"Det","[",StyleBox[TensorSymbol[head],Bold],"]"}]
MakeBoxes[Tr[head_?IndexQ], StandardForm]:=RowBox[{"Tr","[",StyleBox[TensorSymbol[head],Bold],"]"}]
MakeBoxes[Tr[head_?IndexQ,n_], StandardForm]:=RowBox[{"Tr","[",SuperscriptBox[StyleBox[TensorSymbol[head],Bold],MakeBoxes[n]],"]"}]


(* ::Subsection:: *)
(*Cleanup*)


End[];
EndPackage[];
