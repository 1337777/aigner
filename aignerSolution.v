(*+ Aignersolution.v +*)

(***********************************************************************************)

(*

Proph Voevodsky

https://github.com/1337777/aigner/blob/master/aignerSolution.v

solves some question of Aigner [1] [2] which is how to program polymorph counting
modulo ("combinatorics", "groups"). Some finding is that the common encoding of
"cosets" as predicates is by chance/random and the reality is that "cosets" are
polymorph functors :

Variable V_ : forall (B : obB func) (A : obA func), obV log.
Variable f_ : forall B A, log.-V(0 V_ B A |- F[0 B ~> A ]0 )0.
Axiom Ax1 : forall (A A' : obA func) (g : log.-V(0 I |- A[0 A ~> A']0 )0),
      subarrow (F|1 A A' <o g) (f_ (F|0 A) A')
        -> forall (B : obB func), subarrow (f_ B A') (f_ B A o>`func` g).

The common definition of subgroup may require 3 closure axioms 
( 1 \in G , x * y \in G , /_ y \in G ) , which may be erased to 2 closure
axioms ( 1 \in G , x * /_ y \in G ), which may be erased to 2 closure axioms
for finite groups ( 1 \in G , x * y \in G ) as in ssreflect [3]. This new
polymorph view is same as using these 2 closure axioms : 
( 1 \in G , x \in G * y ), where now this right "coset" (G * y) is in reality
the action/composition arrow output (f_ B A o>`func` g) of the polymorh functor,
some <<coin>>. Some polymorph counting-modulo lemma (Cauchy) is possible ...

This solution also contains the programming of some logic of finite functions
and monotone functions, in the ssreflect style which is the programming of
specifications (reflections) for decidable predicates. This
logic-internalization of finite functions are sequences (in ssreflect: 
{ffun aT -> rT}), such that extensional-equality of finite functions corresponds
to propositional equality of sequences. Monotone functions are quotient of
injective functions, therefore instead of manipulating predicates (the codomain)
in the old-style, one may hold monotone functions/arrows (monotone
sequences). Additionally Bauer-Cathlelay [9] may attempt to program the
enrichment-logic of the Dedekind real line for the ultrafilter monad ...

_____

This angle of view of polymorph groupoid action peut resoudre quelques questions
de Brown [4] ou Cisinski... et pourrait meme etre aussi critique que la
decouverte des <<schemas>> par Galois, puisqu'il est bien plus elegant, voire
indispensable pour y comprendre quelque chose de travailler avec des groupoides
fondamentaux par rapport a un paquet de points base convenable. De toutes les
choses de l'univers, j'ay decouvert un programme vaste et d'envergure, un
<<programme solution>> dont j'ay presente ici seulement une esquisse. Il
suffisait de voir de ses propres yeux et non avec des lunettes
brevetees. D'abord j'ay decouvert [5] que la tentative de deduction de la
coherence associative par Maclance n'est en fait pas la realite, puisque ce
fameux pentagone est en fait un carre recursif. Ensuite j'ay decouvert [6] que
les categories seulement-nommees par l'homologiste Maclane sont en fait le
polymorphisme naturel de la logique de Gentzen, ce qui permet une programmation
de la resolution congruente par elimination des coupures [7] qui servira de
technique de specification (reflection) pour semi-decider les questions de
coherence, en comparaison du style ssreflect. Ensuite j'ay decouvert [8] que
l'action de Galois pour la resolution modulo, est en fait une instance des
foncteurs polymorphes. La motivation est que les maths se font et se
communiquent dans un <<temps>> predit/deterministe (1337) et aussi dans un
<<moment>> aleatoire/random (777), sans la peur de jouer 100carats, alors la
question est : comment chercher un truc aleatoire ? ...

[1] Aigner ~Combinatorial Theory~ [[https://books.google.com/books?isbn=3642591019]]
[2] 1337777.OOO
[[https://github.com/1337777/aigner/blob/master/ocic04-where-is-combinatorics.pdf]]
[3] ~Mathematical Components~ [[https://math-comp.github.io/math-comp/]]
[4] Brown ~Topology and Groupoids~ [[http://www.groupoids.org.uk/]]
[5] 1337777.OOO [[https://github.com/1337777/dosen/blob/master/coherence2.v]]
[6] 1337777.OOO [[https://github.com/1337777/borceux/blob/master/borceuxSolution2.v]]
[7] 1337777.OOO [[https://github.com/1337777/dosen/blob/master/dosenSolution3.v]]
[8] 1337777.OOO [[https://github.com/1337777/aigner/blob/master/aignerSolution.v]]
[9] [[https://github.com/cathlelay/dedekind-reals]]

*)

(* user1@user1-computer:~$ coqtop --version

The Coq Proof Assistant, version trunk (October 2016) compiled on Oct 20 2016 16:54:50
with OCaml 4.01.0 *)

(***********************************************************************************)

Require Import borceuxSolution_half_old.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype finfun
     generic_quotient.

Set Implicit Arguments.
Unset Strict Implicits.
Unset Printing Implicit Defensive.

Module REVFUNCTOR.

  Export FUNCTORTOCAT.

  Import LOGIC.Ex_Notations3.
  Import FUNCTOR.Ex_Notations4.
  Import FUNCTORTOCAT.Ex_Notations6.

  (* ERRATA FOR OLD NOTATION ABOVE  *)
  Notation "dat .-F[0 B ~> a ]1'" := ( (dat.-F[0 B ~> - ]1) _ _ <o (a : V(0 _ |- dat.-A[0 _ ~> _ ]0 )0)) (at level 25, format "dat .-F[0  B  ~>  a  ]1'").      
  Notation "F[0 B ~> a ]1'" := (_ .-F[0 B ~> a ]1') (at level 25).

  Parameter revF
      : forall (log : logic) (dat : data) (V : obV log) (B : obB dat) (A' : obA dat),
        log.-V(0 V |- dat.-F[0 B ~> A' ]0 )0 ->
        forall A : obA dat, log.-V(0 dat.-A[0 A ~> A' ]0 |- log.-[0 V ~> dat.-F[0 B ~> A ]0 ]0 )0 .

  Notation "dat .-revF[1 b ~> X ]0" := (@revF _ dat _ _ _ b X) (at level 25, format "dat .-revF[1  b  ~>  X  ]0").
  Notation "revF[1 b ~> X ]0" := (_ .-revF[1 b ~> X ]0) (at level 25, format "revF[1  b  ~>  X  ]0").

  Axiom CongRevF : forall (log : logic) (dat : data)(V : obV log) (B : obB dat) (A : obA dat),
                      forall (f f' : V(0 V |- F[0 B ~> A ]0 )0),
                        f' ~~ f -> forall X : obA dat, revF f' X ~~ revF f X.

  Axiom revF_arrow : forall (log : logic) (dat : data), class dat -> forall
        (B : obB dat) (A : obA dat) (V V' : obV log) (v : log.-V(0 V' |- V )0)
        (f : log.-V(0 V |- dat.-F[0 B ~> A ]0 )0) (X : obA dat),
        dat.-revF[1 f <log<o v ~> X ]0 ~~log` log.-[1 v ~> dat.-F[0 B ~> X ]0 ]0 <log<o dat.-revF[1 f ~> X ]0 .

  Definition revF_unitB : forall (log : logic) (from : form log) (to : category log) (func : functorToCat from to) (A X : obA from), log.-V(0 from.-A[0 X ~> A ]0 |- to.-A[0 func.-F|0 A ~> func.-F|0 X ]0 )0
    := fun log from to func A X =>
         DesIdenObR ( func.-revF[1 (to).-uA ~> X ]0 ). 

  Notation "dat .-revF|1" := (@revF_unitB _ _ _ dat) (at level 0, format "dat .-revF|1").
  Notation "revF|1" := (_ .-revF|1) (at level 0).

  Section Section1.

    Context {log : logic}.
    Variable func : @functor log.
    Variables (A A' : obA func) (g : log.-V(0 I |- func.-A[0 A ~> A' ]0 )0).
    Variables (V : obV log) (B : obB func).

    (** dual_ is some external polyF_IdenV , may be named <<coin>> **)
    Definition dual_polyF (f : log.-V(0 V |- func.-F[0 B ~> A ]0 )0)
      : log.-V(0 V |- func.-F[0 B ~> A' ]0 )0 :=
      DesIdenObL ( F[1 f ~> A' ]0 <o g ) .

    Definition dual_revF (f : log.-V(0 V |- func.-F[0 B ~> A' ]0 )0)
      : log.-V(0 V |- func.-F[0 B ~> A ]0 )0 :=
      DesIdenObL ( revF[1 f ~> A ]0 <o g ) .

  End Section1.

  Notation "b o>F a" := (DesIdenObL (F[1 b ~> _ ]0 <o a))
                          (at level 25, right associativity).
  Notation "b o>` dat ` a" := (DesIdenObL (dat.-F[1 b ~> _ ]0 <o a))
                                (at level 25, right associativity, dat at next level,
                                 format "b  o>` dat `  a").

  Check fun log (F2 : functor log) A A' (g : log.-V(0 log.-I |- F2.-A[0 A ~> A' ]0 )0)
          V B (f : log.-V(0 V |- F2.-F[0 B ~> A ]0 )0)
        => fun _ : unit => f o>`F2` g .

  Notation "b o>/F a" := (DesIdenObL (revF[1 b ~> _ ]0 <o a))
                           (at level 25, right associativity).
  Notation "b o>/` dat ` a" := (DesIdenObL (dat.-revF[1 b ~> _ ]0 <o a))
                                 (at level 25, right associativity, dat at next level,
                                  format "b  o>/` dat `  a").

  Check fun log (F2 : functor log) V B A A' (g : log.-V(0 log.-I |- F2.-A[0 A ~> A' ]0 )0)
          (f : log.-V(0 V |- F2.-F[0 B ~> A' ]0 )0)
        => fun _ : unit => f o>/`F2` g .

  (*Notation dual_revF' g f := (@dual_revF _ _ _ _ g _ _ f) .*)

  Section Section2.

    Context {log : logic}.
    Variable func : @functor log.
    Variables (A A' : obA func) (g : log.-V(0 I |- func.-A[0 A ~> A' ]0 )0).
    Variables (V : obV log) (B : obB func).
    
    Axiom revF_polyF : forall (f : log.-V(0 V |- func.-F[0 B ~> A ]0 )0),
        (f o>`func` g) o>/`func` g ~~ f .
    
    Axiom polyF_revF : forall (f : log.-V(0 V |- func.-F[0 B ~> A' ]0 )0),
        (f o>/`func` g) o>`func` g ~~ f .

    Lemma Cong_dual_polyF : forall (f f' : log.-V(0 V |- func.-F[0 B ~> A ]0 )0),
        f ~~ f' -> f o>`func` g ~~ f' o>`func` g .
    Proof.
      move => f f' Hff'; rewrite /dual_polyF. apply/CongDesIdenObL.
      unfold polyV_relT_identitary; eapply Cong_polyV_relT;
      (* ERRATA TODO shall be some lacking Cong_polyV_relT_identitary *)
        first by eapply ReflV.
      eapply CongPolyF; exact Hff'.
    Qed.
    
    Lemma Cong_dual_revF : forall (f f' : log.-V(0 V |- func.-F[0 B ~> A' ]0 )0),
        f ~~ f' -> f o>/`func` g ~~ f' o>/`func` g.
    Proof.
      move => f f' Hff'; rewrite /dual_revF. apply/CongDesIdenObL.
      unfold polyV_relT_identitary; eapply Cong_polyV_relT;
      (* ERRATA TODO shall be some lacking Cong_polyV_relT_identitary *)
        first by eapply ReflV.
      eapply CongRevF; exact Hff'.
    Qed.

  End Section2.
  
  Lemma DesIdenObRL : forall {log : logic} (W : obV log), forall v : V(0 I |- [0 I ~> W ]0 )0, 
        DesIdenObR v ~~ DesIdenObL v.
  Admitted.

  Lemma DesIdenObL_input : forall {log : logic} (V W : obV log),
      forall (w_v : V(0 I |- [0 V ~> W ]0 )0) (V' : obV log) (v : V(0 V' |- V )0),
        DesIdenObL ( [1 v ~> W ]0 <o w_v ) ~~ (DesIdenObL w_v) <o v.
  Admitted.

  Section Section3.

    Context {log : logic}.
    Context {catA : @form log} {catB : category log}.
    Variable (func : functorToCat catA catB).

    (* coin .. coinjection  .. comono .. *)
    Variable V_ : forall (B : obB func) (A : obA func), obV log.
    Variable f_ : forall (B : obB func) (A : obA func), log.-V(0 V_ B A |- F[0 B ~> A ]0 )0.
    Arguments f_ : clear implicits.

    Definition subarrow (V1 V1' V2 : obV log) (f : log.-V(0 V1 |- V2)0)
               (f' : log.-V(0 V1' |- V2)0) :=
      exists si : log.-V(0 V1 |- V1')0, f ~~ f' <log<o si .

    Lemma subarrow_congL (V1 V1' V2 : obV log) (f f0 : log.-V(0 V1 |- V2)0)
          (f' : log.-V(0 V1' |- V2)0) :
      f ~~ f0 -> subarrow f f' <-> subarrow f0 f' .
    Proof.
      move => Hff0; split; move => [si siP]; exists si; eapply TransV;
                                   eassumption || eapply SymV; eassumption.
    Qed.

    Definition comp_subarrow (V1 V1' V2 : obV log) (f : log.-V(0 V1 |- V2)0)
               (f' : log.-V(0 V1' |- V2)0) (V0 : obV log) (h : log.-V(0 V0 |- V1 )0) :
      subarrow f f' -> subarrow (f <log<o h) f'.
    Proof.
      move => [sm smP]. exists (sm <log<o h).
      eapply TransV; first eapply Cat2V.
      by eapply CongCom_identitary; last eapply ReflV.
    Qed.
    
    Definition comono_revfunctor_polyF :=
      forall (A A' : obA func) (g : log.-V(0 I |- A[0 A ~> A']0 )0),
        subarrow (F|1 A A' <o g) (f_ (F|0 A) A')
        -> forall (B : obB func), subarrow (f_ B A') (f_ B A o>`func` g).

    Definition comono_revfunctor_revF :=
      forall (A A' : obA func) (g : log.-V(0 I |- A[0 A ~> A']0 )0),
        subarrow (revF|1 A' A <o g) (f_ (F|0 A') A)
        -> forall (B : obB func), subarrow (f_ B A) (f_ B A' o>/`func` g).

    Definition comono_revfunctor_unit := forall (A : obA func),
        subarrow ((catB).-uA) (f_ (F|0 A) A).

    Hypothesis (Hf_polyF : comono_revfunctor_polyF).
    Hypothesis (Hf_revF : comono_revfunctor_revF).
    Hypothesis (Hf_unit : comono_revfunctor_unit).

    (* for g = unitA , assumption is same as conclusion 
     move this as nonemptiness axiom *)
    Lemma comono_revfunctor_unit_deduce : forall (A : obA func),
        (exists (A' : obA func) , exists (g : log.-V(0 log.-I |- func.-A[0 A ~> A' ]0 )0),
              subarrow (F|1 A A' <o g ) (f_ (F|0 A) A')) ->
        subarrow ((catB).-uA) (f_ (F|0 A) A).
    Proof.
      move => A [A' [g Hg]]. move: (Hf_polyF Hg (F|0 A)) => [Hf_polyF_Hg Hf_polyF_HgP].
      move: Hg => [Hg HgP].

      exists ((Hf_polyF_Hg <log<o Hg)).

      have H2 : (func).-F|1 A A' <log<o g ~~log`
                ((f_ (F|0 A) A o>`func` g) <log<o Hf_polyF_Hg) <log<o Hg.
      { eapply TransV; [| exact HgP].
        eapply (@CongCom_identitary log); [| eapply ReflV].
        exact: Hf_polyF_HgP. }

      have H3 : ((catB).-uA o>`func` g) ~~log`
                (((f_ (F|0 A) A) <log<o (Hf_polyF_Hg <log<o Hg)) o>`func` g).
      { eapply TransV; [| eapply SymV, DesIdenObRL ].
        eapply TransV; [| eapply DesIdenObR_Input]. 
        eapply TransV; [eapply CongDesIdenObL, CongCom_identitary; [| eapply ReflV];
                        eapply SymV, FUNCTORTOCAT.polyF_arrow |].
        eapply TransV; [eapply CongDesIdenObL, SymV, Cat2V |]. 
        eapply TransV; [eapply SymV, DesIdenObL_input |].
        eapply TransV; [eapply Cat2V |].
        exact: H2. }

      eapply TransV; [ eapply (@revF_polyF log func _ _ g _ _) |].
      eapply TransV; [| eapply SymV,  (@revF_polyF log func _ _ g _ _) ].
      eapply (@Cong_dual_revF log func _ _ g _ _).
      exact H3.
    Qed.

    Lemma comono_revfunctor_revF_unitB_deduce : forall (A A' : obA func),
        forall (g : log.-V(0 log.-I |- func.-A[0 A ~> A' ]0 )0),
          subarrow (F|1 A A' <o g ) (f_ (F|0 A) A') ->
          subarrow (revF|1 A' A <o g ) (f_ (F|0 A') A).
    Proof.
      move => A A' g Hg. move: (Hf_polyF Hg (F|0 A')) => Hg'.
      move : Hg => [Hg HgP].
      
      have Hg'' : subarrow ((catB).-uA) (f_ (F|0 A') A o>`func` g).
      { move : (Hf_unit A') => [Hf_unitA' Hf_unitA'P].
        eapply subarrow_congL; first apply (Hf_unitA'P).
        apply comp_subarrow. apply Hg'. }

      move : Hg'' => [Hg'' Hg''P]. exists Hg''.
      eapply (TransV (dat:=log)) in Hg''P; [| eapply SymV, (DesIdenObL_input (log:=log))].
      eapply (TransV (dat:=log)) in Hg''P; [| eapply CongDesIdenObL, SymV, Cat2V].
      eapply (TransV (dat:=log)) in Hg''P;
        [| eapply CongDesIdenObL, CongCom_identitary; [|eapply ReflV];
           eapply SymV, (@polyF_arrow log func (*(class_of _)*)func)].
      eapply (@Cong_dual_revF log func _ _ g _ _) in Hg''P.
      eapply (TransV (dat:=log)) in Hg''P; [| eapply (@revF_polyF log func)].

      rewrite /revF_unitB.
      eapply (TransV (dat:=log)); [| eapply SymV, DesIdenObR_Input].
      eapply (TransV (dat:=log)); [| eapply DesIdenObRL].
      exact Hg''P. (* AHH YES HOHO *)
    Qed.

    Lemma comono_revfunctor_dual_polyF_deduce :
      forall (W_ : obB func -> obA func -> obV log)
        (k_ : forall (B : obB func) (A : obA func), log.-V(0 W_ B A |- func.-F[0 B ~> A ]0)0),
      (forall (B : obB func) (A : obA func), subarrow (k_ B A) (f_ B A)) ->
      forall (A A' : obA func)
        (g : log.-V(0 log.-I |- func.-A[0 A ~> A' ]0 )0),
      subarrow (F|1 A A' <o g ) (f_ (F|0 A) A') ->
      forall B : obB func, subarrow ((k_ B A) o>`func` g) (f_ B A').
    Proof.
      move => W_ k_ k_P A A' g Hg.
      move : (comono_revfunctor_revF_unitB_deduce Hg) => Hg'.
      move : (Hf_revF Hg') => Hg''.
      
      have k_P' : forall B, subarrow (k_ B A) (f_ B A' o>/`func` g).
      { move => B. move : {k_P}(k_P B A) => [k_P k_PP].
        eapply subarrow_congL; first eapply k_PP.
        apply comp_subarrow. apply Hg''. }

      move => B. move : {k_P'}(k_P' B) => [k_P' k_P'P].
      exists k_P'. eapply (TransV (dat:=log)) in k_P'P;
                 [| eapply SymV, (DesIdenObL_input (log:=log))].
      eapply (TransV (dat:=log)) in k_P'P;
        [| eapply CongDesIdenObL, SymV, Cat2V  ].
      eapply (TransV (dat:=log)) in k_P'P;
        [| eapply CongDesIdenObL, CongCom_identitary;
           [|eapply ReflV];
           eapply SymV, (@revF_arrow log func (*(class_of _)*)func) ].
      eapply (@Cong_dual_polyF log func _ _ g _ _ ) in k_P'P.
      eapply (TransV (dat:=log)) in k_P'P;
        [| eapply (@polyF_revF log func)].
      exact k_P'P. (* AHH YES HOHO *)
    Qed.

    (** TODO: Lemma comono_revfunctor_dual_revF_deduce. **)

  End Section3.

  Section Section4.

    (** by revF_comp_polyF below, the definitions above hold the same after the
        revfunctor is precomposed by some isomorphism .

        by dual_polyF_monomorphism below, also the definitions above hold sense when
        the domain of subarrow is erased to only monomorphisms .

        these sayings could continue in full generality, but by focusing on the
        instance of the finite logic and the monotone functions, these will be quicker
        and make clear the motivations **)
    
    Context {log : logic}.

    Definition monomorphism (W V : obV log) (v : log.-V(0 W |- V)0) :=
      forall W' (w1 w2 : log.-V(0 W' |- W)0) of v <log<o w1 ~~ v <log<o w2,
        w1 ~~ w2 .

    Variable func : @functor log.
    Variables (A A' : obA func) (g :  log.-V(0 log.-I |- func.-A[0 A ~> A' ]0 )0) .
    Variables (V : obV log) (B : obB func).
    Variables (f : log.-V(0 V |- func.-F[0 B ~> A ]0 )0).

    Lemma revF_comp_polyF (V' : obV log) (v : log.-V(0 V' |- V )0) :
      ((f o>`func` g) <log<o v) ~~log` (f <log<o v) o>`func` g .
    Proof.
      eapply TransV; first (eapply CongDesIdenObL, CongCom_identitary;
                           last eapply ReflV; eapply SymV, polyF_arrow).
      eapply TransV; first eapply CongDesIdenObL, SymV, Cat2V.
      eapply TransV; first eapply SymV, DesIdenObL_input.
      exact: ReflV.
    Qed.
      
    Lemma dual_polyF_monomorphism :
      monomorphism f -> monomorphism ( f o>`func` g ).
    Proof.
      move => f_mon W' w1 w2 Hw1w2.
      apply: f_mon.
      eapply TransV; last eapply SymV, revF_polyF.
      eapply TransV; first eapply revF_polyF.
      eapply Cong_dual_revF.

      eapply TransV; last (eapply CongDesIdenObL, CongCom_identitary;
                           last eapply ReflV; eapply polyF_arrow).
      eapply TransV; last eapply CongDesIdenObL, Cat2V.
      eapply TransV; last eapply DesIdenObL_input.

      eapply TransV; first (eapply CongDesIdenObL, CongCom_identitary;
                            last eapply ReflV; eapply SymV, polyF_arrow).
      eapply TransV; first eapply CongDesIdenObL, SymV, Cat2V.
      eapply TransV; first eapply SymV, DesIdenObL_input.
      exact: Hw1w2.
    Qed.

  End Section4.

End REVFUNCTOR.

Module FINLOGIC.

  Import METALOGIC.
  Export LOGIC.
  Import LOGIC.Ex_Notations3.
  
  Definition finType_obV := finType.

  Definition finType_polyV_relT00 (V1 V2 : finType_obV) : Type
    := V1 -> V2.

  Definition finType_convV V1 V2 (f g : finType_polyV_relT00 V1 V2)
    := f =1 g.
  
  
  Definition finType_polyV_relT : forall (T : obT), forall B : finType_obV,  forall (A : finType_obV),
          T(0 T |- (finType_polyV_relT00 B A) )0 -> forall (X : finType_obV)
          , T(0 (finType_polyV_relT00 A X) |-  T(0 T |- (finType_polyV_relT00 B X) )0 )0
    :=  fun T B A t_ X => fun f => fun u => t_ u o>> f.
  
  Definition finType_IdenV : forall {V : finType_obV}, (finType_polyV_relT00 V V)
    := fun V => id.
  
  Definition finType_consV00 : finType_obV -> finType_obV -> finType_obV
    := fun V1 V2 => [finType of {ffun V1 -> V2}].
  
  Definition finType_consV01 : forall V1 : finType_obV, forall {V2 V2'}
      , (finType_polyV_relT00 V2 V2')
        -> (finType_polyV_relT00 (finType_consV00 V1 V2)  (finType_consV00 V1 V2'))
    := fun V1 V2 V2' f22' => fun f12 => [ffun x => f22' (f12 x)].
  
  Definition finType_consV10 :
    forall {V1' V1}, (finType_polyV_relT00 V1' V1) -> forall V2 : finType_obV
      , (finType_polyV_relT00 (finType_consV00 V1 V2) (finType_consV00 V1' V2))
    := fun V1' V1 f1'1 V2 => fun f12 => [ffun x => f12 (f1'1 x)].
  
  Definition finType_desV00 : forall V2 : finType_obV, forall V1 : finType_obV, finType_obV
    := fun V2 V1 => [finType of (V1 * V2)].
  
  Definition finType_desV10 : forall V2 : finType_obV, forall {V1 V1'}
      , (finType_polyV_relT00 V1 V1')
        -> (finType_polyV_relT00 (finType_desV00 V2 V1) (finType_desV00 V2 V1'))
    := fun V2 V1 V2' f11' => fun v1v2 => (f11' v1v2.1 , v1v2.2).
  
  Definition finType_Cons : forall {V : finType_obV}, forall {U W : finType_obV}
      , (finType_polyV_relT00 (finType_desV00 V U) W)
        -> (finType_polyV_relT00 U (finType_consV00 V W))
    := fun V U W f => fun u => [ffun v => f (u, v) ].
  
  Definition finType_Des : forall {V : finType_obV}, forall {U W : finType_obV}
      , (finType_polyV_relT00 U (finType_consV00 V W))
        -> (finType_polyV_relT00 (finType_desV00 V U) W)
    := fun V U W f => fun uv => f uv.1 uv.2.
  
  Definition finType_IdenObV : finType_obV
    := [finType of 'I_0.+1].

  Definition finType_unitV : forall {A : finType_obV}
    , (finType_polyV_relT00 finType_IdenObV (finType_consV00 A A))
    := fun A => fun _ => [ffun a => a].
  
  Definition finType_Assoc : forall {V W : finType_obV}, forall {U: finType_obV}
      , (finType_polyV_relT00 (finType_desV00 (finType_desV00 W V) U)
                              ((finType_desV00 W (finType_desV00  V U ))))
    := fun V W U => fun uvw => let (u, vw) := uvw in let (v, w) := vw in (u, v, w).

  Definition finType_DesIdenObR : forall {U W : finType_obV}
    , (finType_polyV_relT00 U (finType_consV00 finType_IdenObV W))
      -> (finType_polyV_relT00 U W)
    := fun U W f => fun u => f u ord0.

  Definition finType_DesIdenObL : forall {V : finType_obV}, forall {W : finType_obV}
      , (finType_polyV_relT00 finType_IdenObV (finType_consV00 V W))
        -> (finType_polyV_relT00 V W)
    := fun V W f => fun v => f ord0 v.

  Definition finType_Data : LOGIC.data
    := (@LOGIC.Data finType_obV finType_polyV_relT00 finType_convV finType_polyV_relT 
                    (@finType_IdenV)
                    finType_consV00 (@finType_consV01) (@finType_consV10)
                    finType_desV00 finType_desV10 (@finType_Cons) (@finType_Des)
                    finType_IdenObV (@finType_unitV) (@finType_Assoc)
                    (@finType_DesIdenObR) (@finType_DesIdenObL)).

  (** now: partial proof for LOGIC.class **)
  
  Lemma finType_Des_Cons : forall V : obV finType_Data, forall (U W : obV finType_Data)
      , forall (f : finType_Data.-V(0 (0 U & V )0 |-  W )0),
          Des (Cons f) ~~ f.
  Proof.
      by move => *; move; move => *; rewrite /= /finType_Des /finType_Cons /= ffunE -
                                   surjective_pairing.
  Qed.

  Lemma finType_Cons_Des : forall V : obV finType_Data, forall (U W : obV finType_Data)
      , forall (f : V(0 U |-  [0 V ~> W ]0 )0),
          Cons (Des f) ~~ f.
  Proof.
      by move => *; move; move => *; rewrite /= /finType_Cons /finType_Des; apply/ffunP;
                                  move => *; rewrite /= ffunE.
  Qed.
  
  Lemma finType_CongDes : forall V : obV finType_Data, forall (U W : obV finType_Data)
      , forall (f f' : V(0 U |- [0 V ~> W ]0 )0),
          f' ~~ f -> Des f' ~~ Des f.
  Proof.
      by move => V U W f f' H;
                  move; move => x; rewrite /= /finType_Des; move/(_ x.1): H => ->.
  Qed.

  Lemma finType_CongCons : forall V : obV finType_Data, forall (U W : obV finType_Data)
      , forall (v v' : V(0 (0 U & V )0 |- W )0 ),
          v' ~~ v -> Cons v' ~~ Cons v.
  Proof.
      by move => V U W v v' H x; rewrite /= /finType_Cons; apply/ffunP;
                  move => x0; rewrite !ffunE; move/(_ (x, x0)): H => -> .
  Qed.

  Lemma finType_Class : @LOGIC.class finType_Data.
  Admitted.
  
  Canonical Structure logfT := LOGIC.Logic finType_Class.

End FINLOGIC.

Module FINMONO.

  Section Section1.

    Variables (aT : finType) (rT : finType).
    
    Structure finInjType : Type := FinInjType { 
                                       finj_val :> {ffun aT -> rT} ; 
                                       finj_valP : injectiveb finj_val }.
    
    Canonical finInjType_subType := Eval hnf in [subType for finj_val].
    Definition finInjType_eqMixin := Eval hnf in [eqMixin of finInjType by <:].
    Canonical finInjType_eqType := Eval hnf in EqType finInjType finInjType_eqMixin.
    Definition finInjType_choiceMixin := [choiceMixin of finInjType by <:].
    Canonical finInjType_choiceType := Eval hnf
        in ChoiceType finInjType finInjType_choiceMixin.
    Definition finInjType_countMixin := [countMixin of finInjType by <:].
    Canonical finInjType_countType := Eval hnf
        in CountType finInjType finInjType_countMixin.
    Canonical finInjType_subCountType := Eval hnf in [subCountType of finInjType].
    Definition finInjType_finMixin := [finMixin of finInjType by <:].
    Canonical finInjType_finType := Eval hnf
        in FinType finInjType finInjType_finMixin.
    Canonical finInjType_subFinType := Eval hnf in [subFinType of finInjType].
    
    Definition finInjType_of of phant (aT -> rT) := finInjType.
    Identity Coercion finInjType_of_finInjType : finInjType_of >-> finInjType.
    Definition finInjType_clone f fiT c of phant_id (finj_valP fiT) c
      := @FinInjType f c.

  End Section1.

  Notation "{ 'finj' fT }" := (finInjType_of (Phant fT) : predArgType).
  Notation "[ 'finInjType' 'of' f ]" := (@finInjType_clone _ _ f _ _ id).
  
  Section Section2.

    Variables (aT rT : finType).

    Canonical finInjType_of_subType := Eval hnf in [subType of {finj aT -> rT}].
    Canonical finInjType_of_eqType := Eval hnf in [eqType of {finj aT -> rT}].
    Canonical finInjType_of_choiceType := Eval hnf in [choiceType of {finj aT -> rT}].
    Canonical finInjType_of_countType := Eval hnf in [countType of {finj aT -> rT}].
    Canonical finInjType_of_subCountType := Eval hnf
        in [subCountType of {finj aT -> rT}].
    Canonical finInjType_of_finType := Eval hnf in [finType of {finj aT -> rT}].
    Canonical finInjType_of_subFinType := Eval hnf in [subFinType of {finj aT -> rT}].

  End Section2.
    
  Section Section3.

    Variables (aT rT : finType).

    Definition monotoneb (f : aT -> rT ) := enum (mem (codom f)) == codom f.

    (** maybe 2 mixing on top of 1 data {ffun aT -> rT} instead of telescope,
        but telescope is ok for quotient types **) 
    Structure finMonType : Type := FinMonType {
                                       fmon_val :> {finj aT -> rT} ;
                                       fmon_valP : monotoneb fmon_val }.

    Canonical finMonType_subType := Eval hnf in [subType for fmon_val].
    Definition finMonType_eqMixin := Eval hnf in [eqMixin of finMonType by <:].
    Canonical finMonType_eqType := Eval hnf in EqType finMonType finMonType_eqMixin.
    Definition finMonType_choiceMixin := [choiceMixin of finMonType by <:].
    Canonical finMonType_choiceType := Eval hnf
        in ChoiceType finMonType finMonType_choiceMixin.
    Definition finMonType_countMixin := [countMixin of finMonType by <:].
    Canonical finMonType_countType := Eval hnf
        in CountType finMonType finMonType_countMixin.
    Canonical finMonType_subCountType := Eval hnf in [subCountType of finMonType].
    Definition finMonType_finMixin := [finMixin of finMonType by <:].
    Canonical finMonType_finType := Eval hnf
        in FinType finMonType finMonType_finMixin.
    Canonical finMonType_subFinType := Eval hnf in [subFinType of finMonType].

    Definition finMonType_of of phant (aT -> rT) := finMonType.
    Identity Coercion finMonType_of_finMonType : finMonType_of >-> finMonType.
    Definition finMonType_clone f fiT c of phant_id (fmon_valP fiT) c := @FinMonType f c.

  End Section3.
  
  Notation "{ 'fmon' fT }" := (finMonType_of (Phant fT) : predArgType) .
  Notation "[ 'finMonType' 'of' f ]" := (@finMonType_clone _ _ f _ _ id).

  Section Section4.

    Variables (aT rT : finType).

    Canonical finMonType_of_subType := Eval hnf in [subType of {fmon aT -> rT}].
    Canonical finMonType_of_eqType := Eval hnf in [eqType of {fmon aT -> rT}].
    Canonical finMonType_of_choiceType := Eval hnf in [choiceType of {fmon aT -> rT}].
    Canonical finMonType_of_countType := Eval hnf in [countType of {fmon aT -> rT}].
    Canonical finMonType_of_subCountType := Eval hnf
        in [subCountType of {fmon aT -> rT}].
    Canonical finMonType_of_finType := Eval hnf in [finType of {fmon aT -> rT}].
    Canonical finMonType_of_subFinType := Eval hnf in [subFinType of {fmon aT -> rT}].

  End Section4.

  Section Section5.

    Variables (aT rT : finType).

    Lemma mkMonotone_base_subproof (f : aT -> rT) (fP : injectiveb f) : #|aT| = #|codom f|.
    Proof. exact: esym (card_codom (injectiveP f fP)). Qed.

    Definition mkMonotone_base (f : {finj aT -> rT}) : {ffun aT -> rT} :=
      let: FinInjType f fP := f in
      [ffun x => @enum_val rT (mem (codom f)) (cast_ord (mkMonotone_base_subproof fP) (enum_rank x))] .

    Definition monotone (f : aT -> rT) (fP : injectiveb f) :=
      forall (j : 'I_#| mem (codom f) |), @enum_val _ (mem (codom f)) j =
            f (enum_val (cast_ord ((card_codom (injectiveP f fP))) j)) .

    Lemma nth_inj (T : Type) (x0 : T) : forall (s1 s2 : seq T) (Hsize: size s1 = size s2)
      , forall (Hnth: forall (i : nat), i < size s1 -> i < size s2 -> (nth x0 s1 i = nth x0 s2 i)),
          s1 = s2.
    Proof.
      move => s1 s2 Hsize Hnth. apply: (eq_from_nth (x0:=x0)) => // *.
      by apply: Hnth; rewrite // -Hsize.
    Qed.
    
    Lemma map_enum_val : forall (T : finType) (A : pred T), map (@enum_val T A) (enum 'I_#|A|) = enum A.
    Proof.
      move => T A. case : (card_gt0P A).
      - move => [x0 Hx0]. apply (nth_inj (x0:=x0)).
        rewrite size_map -cardE -cardE card_ord; reflexivity.
        
        move => i Hil Hir.
        rewrite (nth_map (enum_rank_in Hx0 x0)); last by move: Hil;
                            rewrite size_map //.
        rewrite -[nth _ _ _ in LHS](valKd (enum_rank_in Hx0 x0)).
        rewrite /val /=. rewrite nth_enum_ord; last rewrite cardE //. 
        rewrite /enum_val.
        rewrite (set_nth_default x0); last by rewrite insubdK; first assumption;
          rewrite -topredE cardE //.
        rewrite insubdK; last by rewrite -topredE cardE //. reflexivity.
      - move/(introF (card_gt0P A)) . case : posnP => // HA.
        move: {-}HA. move => /card0_eq /eq_enum -> _ .
        rewrite enum0. apply size0nil. rewrite size_map -cardE card_ord //. 
    Qed.

    Lemma map_enum_valT : forall (T : finType),
        map (@enum_val T T) (enum 'I_#|T|) = enum T.
    Proof. move => *. apply: map_enum_val. Qed.

    Lemma codom_comp_enum_val : forall (T : finType) (T' : Type) (f : T -> T'),
        codom (f \o @enum_val T T) = codom f .
    Proof. by move => T T' f; rewrite /codom /image_mem map_comp map_enum_val. Qed.

    Lemma map_enum_rank_in : forall (T : finType) (A : pred T) (x0 : T) (Ax0 : x0 \in A),
        map (@enum_rank_in T x0 A Ax0) (enum A) = enum 'I_#|A|.
    Proof.
      move => T A x0 Ax0.
      apply/(inj_map (f:= @enum_val T A)); first by exact: enum_val_inj.
      rewrite [RHS]map_enum_val.
      rewrite -[LHS]map_comp. 
      rewrite [LHS](eq_map (f2:= (fun x => if x \in A then x else
                                          enum_val (Ordinal (@enum_rank_subproof
                                                               T x0 [eta A] Ax0))) )).
      - rewrite (iffLR (eq_in_map _ id _)); first by rewrite map_id.
          by move => x Ax; rewrite -mem_enum Ax.
      - move => x. case Ax: (x \in A); first by apply: enum_rankK_in.
        rewrite /enum_rank_in. congr enum_val. apply/val_inj. rewrite val_insubd.
          by rewrite {1}cardE index_mem mem_enum Ax.
    Qed.

    Lemma map_cast_ord : forall n m : nat, forall (eq_n_m : n = m),
          map (cast_ord eq_n_m) (enum 'I_n) = enum 'I_m.
    Proof.
      move => n m eq_n_m. case : m / eq_n_m.
      rewrite (eq_map (f2:= id)); first by rewrite map_id. exact: cast_ord_id.
    Qed.

    Lemma inj_can_eq_in :
     forall (A B : Type) (f g : B -> A) (D : pred B) (f' : A -> B),
       {in D , cancel f f'} -> {on D, injective f'}
       -> {in D , cancel g f'} -> {in D , f =1 g}.
    Proof.
      move => A B f g D f' Hf Hf' Hg => d Hd.
      apply Hf'; first rewrite Hf //. rewrite Hf ?Hg //.
    Qed.

    Lemma enum_rank_default :
      forall (T : finType) (x1 : T) (x0 : T) (A : pred T) (Ax1 : x1 \in A) (Ax0 : x0 \in A)
      , {in A, (enum_rank_in Ax0) =1 (enum_rank_in Ax1)}.
    Proof.
      move => *; apply: inj_can_eq_in; do [apply: enum_rankK_in |
                                          hnf; intros; apply: enum_val_inj => //].
    Qed.

    Lemma enum_rank_congr : forall (T : finType) (x1 : T) (x0 : T) (A1 A0 : pred T)
      , (A0 =i A1) -> forall (Ax1 : x1 \in A1)  (Ax0 : x0 \in A0),
          {in A0, forall x,  ( (enum_rank_in Ax0) x) = ( ((enum_rank_in Ax1) x)) :> nat }.
    Proof.
      move => T x1 x0 A1 A0 H * => x A0x; rewrite /enum_rank_in.
      rewrite insubdK. rewrite insubdK.
      rewrite (eq_enum H). reflexivity.
      rewrite -topredE. simpl. rewrite cardE. rewrite -(eq_enum H). rewrite index_mem.
      rewrite mem_enum. assumption.
      rewrite -topredE. simpl. rewrite cardE. rewrite index_mem.  rewrite mem_enum. assumption.
    Qed.

    Lemma enum_val_congr :
      forall (T : finType) (A B : pred T) (eqmem : A =i B) (i : 'I_#| A|),
        enum_val i = enum_val (cast_ord (eq_card (eqmem)) i).
    Proof.
      move => T A B eqmem i.
      rewrite [LHS](enum_val_nth (enum_val i)).
      rewrite [RHS](enum_val_nth (enum_val i)).
      move: (eq_enum eqmem) => H.
      rewrite H. apply/eqP.
      erewrite nth_uniq.
        by [].
          by rewrite -H -cardE ltn_ord.
            by rewrite /= -H -cardE ltn_ord.
              by apply enum_uniq.
    Qed.

    Lemma map_enum_rank : forall (T : finType),
        map (@enum_rank T) (enum T) = enum 'I_#|T|.
    Proof.
      move => T. case: (card_gt0P T).
      - move => [x0 Tx0]. rewrite /enum_rank.
        rewrite (eq_map (f2:=fun x => @enum_rank_in T x0 T Tx0 x ));
          last by move => x; apply: enum_rank_default.
          by rewrite map_enum_rank_in.
      - move/(introN (card_gt0P T)). case: posnP => // H_eq_cardT_nat0 _.
        move: (H_eq_cardT_nat0) => /card0_eq  H_eq_mem_T_pred0.
        apply/(inj_map (f:= val)); first by exact: val_inj.
        
        rewrite (eq_enum H_eq_mem_T_pred0) -map_comp enum0 /=.
          by rewrite val_enum_ord [in RHS]H_eq_cardT_nat0.
    Qed.
    
   Lemma monotoneP (f : aT -> rT) (fP : injectiveb f)
     : reflect (monotone fP) (monotoneb f).
   Proof.
     case: (monotoneb f) / idP => [HmonbT | HmonbF]; constructor.
     - move => j. 
       rewrite -(nth_codom (enum_default j)). rewrite /enum_val.
       congr nth. by apply/eqP. 
     - move => Hmon. move: HmonbF. apply/negP.
       rewrite /monotoneb. apply/eqP.
       rewrite [in RHS]/codom [in RHS]/image_mem.
       rewrite -[in RHS]map_enum_val -[in RHS]map_comp.
       rewrite -[in LHS]map_enum_val.  
       case: (card_gt0P aT); last first.
       + move/(introF (card_gt0P aT)). case : (posnP #|aT|) => // card_aT _.
         rewrite [RHS]size0nil; last by rewrite size_map -cardE card_ord.
         rewrite [LHS]size0nil; first done.
         by rewrite size_map -cardE card_ord;
           apply/eqP; rewrite -leqn0 -card_aT leq_image_card.
       + move => [i0 Hi0]. apply: (nth_inj (x0:= f i0)).
         by do 2 rewrite size_map /=; rewrite card_codom //; apply/injectiveP => //.
         do 2 rewrite size_map /=. do 2 rewrite -cardE card_ord.
         move => i H_i_lt_codom H_i_lt_aT .
         rewrite [in LHS](nth_map (Ordinal H_i_lt_codom));
           last by rewrite -cardE card_ord.
         rewrite [in RHS](nth_map (Ordinal H_i_lt_aT));
           last by rewrite -cardE card_ord.
         rewrite Hmon. congr f. congr enum_val. apply/val_inj.
           by rewrite /= ?nth_enum_ord.
   Qed.

   Lemma mkMonotone_base_monoP : forall f : {finj aT -> rT}, monotoneb (mkMonotone_base f).
   Proof.
     move => [f fP] /=. apply/monotoneP.
     - apply/injectiveP. move => x x'. rewrite !ffunE. move => Heq.
         by apply /enum_rank_inj /(cast_ord_inj (eq_n:=(mkMonotone_base_subproof fP)))                 
                  /enum_val_inj.
     - rewrite /monotone. set mkMon_f := [ffun x => _]. move => mkMon_f_inj j.
       rewrite ffunE.
       rewrite [RHS](enum_val_congr (B:=(mem (codom mkMon_f)))); last first.
       + move => H_eq_mem. congr enum_val. rewrite enum_valK. by apply/val_inj.
       + rewrite {2}/codom /image_mem.
         rewrite (eq_map (f2 := (fun x => (enum_val
                                           \o ((cast_ord (mkMonotone_base_subproof fP)
                                               ) \o enum_rank)) x)));
           last by apply ffunE.
         rewrite (map_comp (enum_val)).
         rewrite (map_comp (cast_ord _)).
         rewrite map_enum_rank map_cast_ord map_enum_val.
           by move => y; rewrite mem_enum.
   Qed.

   Lemma monotoneb_injectiveb : forall f : aT -> rT, monotoneb f -> injectiveb f.
   Proof.
     move => f /eqP Hf.
     rewrite /injectiveb /dinjectiveb. rewrite [RHS]/codom [RHS]/image_mem in Hf.
       by rewrite -Hf enum_uniq.
   Qed.
   
   Lemma mkMonotone_base_injP (f : {finj aT -> rT}) : injectiveb (mkMonotone_base f).
   Proof.  by apply/monotoneb_injectiveb/mkMonotone_base_monoP. Qed.

   Canonical mkMonotone (f : {finj aT -> rT}) : {finj aT -> rT} :=
     @FinInjType _ _ (mkMonotone_base f) (mkMonotone_base_injP f).
   Canonical mkMonotone_finMonType (f : {finj aT -> rT}) : {fmon aT -> rT} :=
     @FinMonType _ _ (mkMonotone f) (mkMonotone_base_monoP f).

   Lemma fmon_valK : cancel (@fmon_val aT rT) mkMonotone_finMonType.
   Proof.
     move => f. rewrite /mkMonotone_finMonType. apply/val_inj/val_inj => /=.
     move: f => [[f f_injP] f_monP] /=. apply/ffunP => x. rewrite ffunE.
     move/(monotoneP f_injP) : f_monP => -> .
       by congr (fun_of_fin f); rewrite cast_ord_comp cast_ord_id enum_rankK.
   Qed.

   Definition finMonType_quotMixin
     := @QuotClass {finj aT -> rT} (finMonType aT rT) (@fmon_val aT rT)
                   mkMonotone_finMonType fmon_valK.
   Canonical finMonType_quotType := QuotType (finMonType aT rT) finMonType_quotMixin.
   Canonical finMonType_of_quotType := Eval hnf in [quotType of ({fmon aT -> rT})].

  End Section5.

  Section Section6.

    Variables (aT rT : finType).

    Lemma mkMonotone_base_subinj (f : {finj aT -> rT}) :
      exists si : aT -> aT, f =1 (mkMonotone_base f) \o si
                      /\ bijective si.
    Proof.
      move : f => [f f_inj].
      eexists. split.
      (* (fun x : aT =>
         enum_val (cast_ord (esym (mkMonotone_base_subproof f_inj)
                            ) (enum_rank_in (codom_f f x) (f x)))) *)
      - move => x. rewrite /mkMonotone_base /= ffunE.
        rewrite -[LHS](enum_rankK_in (codom_f f x));
          last by apply: codom_f.
        congr enum_val. About cast_ordK.
        rewrite -[LHS](cast_ordK (esym (mkMonotone_base_subproof f_inj))).
        congr cast_ord; first by apply: esymK.
        rewrite -[LHS](enum_valK).
        congr enum_rank.
      - apply: injF_bij.
        apply: (inj_comp (f:=enum_val) );
          first by exact: enum_val_inj.
        apply: (inj_comp (f:=cast_ord _));
          first by exact: cast_ord_inj.
        move/injectiveP : f_inj => f_inj x x'/(f_equal enum_val);
                                    rewrite ?enum_rankK_in; first (by exact: f_inj);
                                      apply: codom_f.
    Qed.

    Lemma mkMonotone_base_subinj_uniq (f : {finj aT -> rT}) :
     forall si1 si2 : aT -> aT, f =1 (mkMonotone_base f) \o si1
                          -> f =1 (mkMonotone_base f) \o si2
                          -> si1 =1 si2 .
    Proof.
      move => si1 si2 Hsi1 Hsi2 x.
        by move/injectiveP: (mkMonotone_base_injP f);
          apply; rewrite -[LHS]Hsi1 -[RHS]Hsi2.
    Qed.

    Lemma codom_mono_injective (f1 f2 : aT -> rT) :
      monotoneb f1 -> monotoneb f2 ->
      (codom f1 =i codom f2) -> f1 =1 f2 . 
    Proof.
      move => Hf1 Hf2 Hf1f2. About ffunP.  move => x.
      rewrite -[x]enum_rankK. move/monotoneb_injectiveb : (Hf1) => Hf1_inj .
      move/(monotoneP Hf1_inj): (Hf1) => Hf1_mon.
      rewrite /monotone in Hf1_mon.
      rewrite -[enum_rank x in
                   LHS](cast_ordK (esym (card_codom ((injectiveP f1) Hf1_inj)))).
      rewrite esymK. rewrite -Hf1_mon.
      rewrite (enum_val_congr Hf1f2).  
      move/monotoneb_injectiveb : (Hf2) => Hf2_inj .
      move/(monotoneP Hf2_inj): (Hf2) => Hf2_mon.
      rewrite /monotone in Hf2_mon.
      rewrite -[enum_rank x in
                   RHS](cast_ordK (esym (card_codom ((injectiveP f2) Hf2_inj)))).
      rewrite esymK. rewrite -Hf2_mon.
      congr enum_val.
        by apply/val_inj.
    Qed.

  End Section6.
  
  Section Section7.

    Variables (aT rT : finType).

    Definition monotone0 (f : aT -> rT) :=
      {mono f : x y / enum_rank x < enum_rank y >-> enum_rank x < enum_rank y}.

    Definition monotone0_in (f : aT -> rT)
      := forall x y , ( enum_rank x < enum_rank y )
                 = ( enum_rank_in (codom_f f x) (f x)
                     < enum_rank_in (codom_f f y) (f y) ).

    Definition monotone0_in_ord (f : aT -> rT)
      := forall (i j : 'I_#| aT |),
        ( i < j ) = ( enum_rank_in (codom_f f (enum_val i)) (f (enum_val i)) <
                      enum_rank_in (codom_f f (enum_val j)) (f (enum_val j)) ).

    Lemma nat_monotoneRL (T : eqType) (f : nat -> nat) :
      (forall x y, x < y -> f x < f y) -> forall x y, f x < f y -> x < y.
    Proof.
      move => H x y.
      case: (ltngtP (x) (y)) => //; first
        by move/H => Hlt1 Hlt2; move: (ltn_trans Hlt1 Hlt2); rewrite ltnn.
        by move => ->; rewrite ltnn.
    Qed.

    Lemma index_monotone_filterR :
      forall (T : eqType) (a : T -> bool) (x y : T) (ax : a x) (ay : a y),
      forall s, index x s < index y s -> index x (filter a s) < index y (filter a s).
    Proof.
      move => T a x y ax ay. elim => //= s0 s' IH.
      case : (@idP (a s0)) => [ _ | ].
      - case : (s0 =P x) => [ <- | ] ; case (s0 =P y) => [ <- | ] /= ; rewrite ?eqxx.
        trivial.
        move => /(introF (s0 =P y)) -> // .
        trivial.
        move => /(introF (s0 =P y)) -> /(introF (s0 =P x)) -> /= . exact IH.
      - case : (s0 =P x) => [ -> // | _ ]. case : (s0 =P y) => [ -> // | _ _ ] . exact IH.
    Qed.

    Lemma index_monotone_filterL : forall (T : eqType) (a : T -> bool) (x y : T) (ax : a x) (ay : a y),
        forall s, index x (filter a s) < index y (filter a s) -> index x s < index y s.
    Proof.
      move => T a x y ax ay. elim => //= s0 s' IH.
      case : (@idP (a s0)) => [ _ | ].
      - case : (s0 =P x) => [ <- | ] ; case (s0 =P y) => [ <- | ] /= ; rewrite ?eqxx.
        trivial.
        trivial.
        move => /(introF (s0 =P x)) -> //.
        move => /(introF (s0 =P y)) -> /(introF (s0 =P x)) -> /= . exact IH.
      - case : (s0 =P x) => [ -> // | _ ]. case : (s0 =P y) => [ -> // | _ _ ] . exact IH.
    Qed.

    Lemma rank_monotone :
      forall (T : finType) (A : pred T) (x y : T) (Ax : (x \in A)) (Ay : (y \in A)),
        ( enum_rank_in Ax x  < enum_rank_in Ay y ) = (enum_rank x < enum_rank y).
    Proof.
      move => T A x y Ax Ay.
      rewrite /enum_rank /enum_rank_in ?val_insubd.
      have H_i_A: index x (enum A) < #|A| by
          rewrite cardE index_mem mem_enum; exact Ax.
      have H_j_A : index y (enum A) < #|A| by
          rewrite cardE index_mem mem_enum; exact Ay.
      have H_i_T : index x (enum T) < #|T| by
          rewrite cardE index_mem mem_enum -topredE //.
      have H_j_T : index y (enum T) < #|T| by
          rewrite cardE index_mem mem_enum -topredE //.
      rewrite H_i_A H_j_A H_i_T H_j_T.

      rewrite ?/(enum _) ?filter_predT.
      apply/Bool.eq_true_iff_eq; split;
        apply index_monotone_filterR || apply index_monotone_filterL;
        exact Ax || exact Ay.
    Qed.

    Lemma rank_val_monotone : forall (T : finType) (A : pred T) (i j : 'I_#|A|),
        (i < j) = (enum_rank (enum_val (A:=A) i) < enum_rank (enum_val (A:=A) j)).
    Proof.
      move => T A i j.
      rewrite -{1}[i](enum_valK_in (x0 := (enum_val (A:=A) i)) (enum_valP i)) ;
        rewrite -{1}[j](enum_valK_in (x0 := (enum_val (A:=A) j)) (enum_valP j)) .
      apply rank_monotone.
    Qed.

    (** ?lacked? **)
    Lemma rank_val_inj : forall (T : finType) (A : pred T),
        injective (enum_rank \o (enum_val (A:=A))) .
    Proof.
      move => T A => i j.
      move/eqP => Hij. apply/eqP.
      move : Hij. apply/contraLR.   
      rewrite ?neq_ltn /= .
      move/orP => [ H_i_lt_j | H_j_lt_i ]; apply/orP; [left | right];
                   rewrite -(rank_val_monotone _ _); assumption.
    Qed.

    Lemma monotone0_monotone0_in (f : aT -> rT) : monotone0 f <-> monotone0_in f.
    Proof.
        by split; move => Hf x y;
                           do [rewrite rank_monotone; rewrite Hf |
                               rewrite Hf; rewrite rank_monotone ].
    Qed.

    Lemma monotone0_in_monotone0_in_ord (f : aT -> rT) :
      monotone0_in f <-> monotone0_in_ord f.
    Proof.
      split.
      - move => Hf i j; rewrite -{1}[i]enum_valK -{1}[j]enum_valK.
                  by rewrite Hf.
      - move => Hf x y. by rewrite Hf ?enum_rankK.
    Qed.

    Lemma monotone0_injective (f : aT -> rT) : monotone0 f -> injective f.
    Proof.
      move => Hf x y.
      move/(f_equal enum_rank)/eqP => Hxy. apply/enum_rank_inj/eqP.
      move : Hxy. apply/contraLR.   
      rewrite ?neq_ltn /= .
      move/orP => [ H_x_lt_y | H_y_lt_x ]; apply/orP; [left | right];
                   rewrite Hf; assumption.
    Qed.

    Lemma monotone_endo_is_id_gte n (f : 'I_n -> 'I_n)
          (H: forall (i j : 'I_n), i < j -> f i < f j) :
      forall m : nat , forall (k : 'I_n), k = m :> nat -> m <= f k.
    Proof.
      elim; first (move => *; apply: leq0n).

      move => m' IH k Hk_eq.
      have Hm' : m' < n .
      move: Hk_eq (ltn_ord k) => -> Hk_lt.
      apply: (leq_trans (n := m'.+1.+1)); [ apply: leqnSn | exact: Hk_lt].
      
      eapply (leq_ltn_trans (n:= f (Ordinal Hm'))).
         apply IH; reflexivity.
      apply: H => /=. rewrite Hk_eq ltnSn //.
    Qed.

    Lemma monotone_endo_is_id_lte n (f : 'I_n -> 'I_n)
          (H: forall (i j : 'I_n), i < j -> f i < f j) :
      forall m : nat , 0 < n - m -> forall (k : 'I_n), k = ((n - m).-1) :> nat -> f k <= ((n - m).-1).
    Proof.
      elim. rewrite subn0.  move => J k Hk_eq. move: (ltn_ord (f k)). move => Hfk_lt.
      have Hn : 0 < n.
      eapply leq_ltn_trans; last exact: Hfk_lt; exact: leq0n.

      rewrite -ltnS prednK; first exact: Hfk_lt; exact: Hn.

      move => m' IH J  k Hk_eq.
      move: (ltn_ord (f k)). move => Hfk_lt.
      rewrite -ltnS.
      have Hn : 0 < n.
      eapply leq_trans; last exact: Hfk_lt; exact: leq0n.
      have Hm' : (n - m'.+1) < n .
      clear -Hn. trivial. rewrite -{2}[n]subn0. apply: ltn_sub2l; first exact Hn;
                                                  rewrite ltnS leq0n //.

      eapply (leq_trans (n:= f (Ordinal Hm'))).
      apply: H => /=. rewrite Hk_eq . rewrite prednK. exact: leqnn. assumption.

      rewrite prednK; last assumption.
      rewrite [in X in _ <= X]subnS.
      apply IH. 2: rewrite -subnS; reflexivity.
      eapply (leq_trans (n:= (n - m').-1)). rewrite -subnS. assumption.
      exact: leq_pred.
    Qed.
    
    Lemma monotone_endo_is_id n (f : 'I_n -> 'I_n)
          (H: forall (i j : 'I_n), i < j -> f i < f j) :
      forall (k : 'I_n), f k = k.
    Proof.
      move => k. apply/esym/val_inj/eqP. rewrite eqn_leq. apply/andP.
      split; first by apply: monotone_endo_is_id_gte.

      pose (mm:= val(rev_ord k)). (*evar (mm:nat).*)
      move: (@monotone_endo_is_id_lte _ _ H mm).
      have djdj: ((n - mm).-1 = val k).
      { rewrite -subnS. move: (rev_ordK k). simpl. move/(f_equal val).
        simpl. by trivial. }
      rewrite djdj. apply; last by reflexivity.
      move: (ltn_ord (rev_ord k)) => L. move: (ltn_sub2l (p:=n)(m:=mm) (n:=n)).
      rewrite subnn. apply; done.
    Qed.

    Lemma monotone_eqendo_is_id n m (eqnm: n = m) (f : 'I_n -> 'I_m) :
      (forall (i j : 'I_n), i < j -> f i < f j) ->
      forall i, f i = (cast_ord eqnm i ).
    Proof. 
      move : f. case :  m / eqnm => * .  rewrite cast_ord_id.
      apply monotone_endo_is_id. assumption.
    Qed.

    Lemma monotone_injendo_is_id n (T : finType) (f : 'I_n -> T)
          (f_injP : injectiveb f) :
      (forall (i j : 'I_n), i < j -> enum_rank_in (codom_f f i) (f i)
                               < enum_rank_in (codom_f f j) (f j)) ->
      forall i, forall y (By : y \in codom f),
          enum_rank_in By (f i) =
          (cast_ord (esym (card_codom ((injectiveP f) f_injP))))
            (cast_ord (esym (card_ord _)) i).
    Proof.
      move => f_mono i y By.
      rewrite [in LHS](@monotone_eqendo_is_id _ _ _ (fun i =>  enum_rank_in By (f i))).
      rewrite card_codom; last by apply/injectiveP; assumption. rewrite card_ord //.
      move => Heq . rewrite cast_ord_comp. apply val_inj. reflexivity.

      move => i0 j0 Hi0j0.
      rewrite [in X in X < _](enum_rank_default  (codom_f f i0)); last apply: codom_f.
      rewrite [in X in _ < X](enum_rank_default (codom_f f j0)); last apply: codom_f.
      apply f_mono. assumption.
    Qed.

    (* non-lacked extra lemma *)
    Lemma monotone_injendos_is_id n (T : finType) (f : 'I_n -> T)
          (f_injP : injectiveb f) (g : 'I_n -> T) (g_injP : injectiveb g) :
      (forall (i j : 'I_n), i < j ->
                       enum_rank_in (codom_f f i) (f i)
                       < enum_rank_in (codom_f f j) (f j)) ->
      (forall (i j : 'I_n), i < j ->
                       enum_rank_in (codom_f g i) (g i)
                       < enum_rank_in (codom_f g j) (g j)) ->
      (codom f =i codom g) -> f =1 g .
    Proof.
      move => Hf Hg Hfg i.
      rewrite -[f i](enum_rankK_in (codom_f f i)); last apply (codom_f f i).
      rewrite -[g i](enum_rankK_in (codom_f g i)); last apply (codom_f g i).
      rewrite !monotone_injendo_is_id; last assumption; last assumption.
      rewrite (enum_val_congr Hfg). congr 1 enum_val. apply val_inj. reflexivity.
    Qed.

    Lemma monotone0P (f : aT -> rT)
      : reflect (monotone0 f) (monotoneb f).
    Proof.
      case: (monotoneb f) / idP => [HmonbT | HmonbF]; constructor.
      - move: (monotoneb_injectiveb HmonbT) => Hinj.
        move/(monotoneP Hinj) : HmonbT => Hmon.
        apply/monotone0_monotone0_in/monotone0_in_monotone0_in_ord => i j.
        rewrite -[i in X in _ = ( enum_rank_in _ X < _)
                 ](cast_ordKV ((card_codom ((injectiveP f) Hinj))));
        rewrite -Hmon enum_valK_in.
        rewrite -[j in X in _ = ( _ < enum_rank_in _ X )
                 ](cast_ordKV ((card_codom ((injectiveP f) Hinj))));
        rewrite -Hmon enum_valK_in. by [].
      - move => Hmon0. apply: HmonbF.
        move/monotone0_injective/injectiveP : (Hmon0) => Hinj.        
        apply/(monotoneP Hinj) => j.
        move /monotone0_monotone0_in /monotone0_in_monotone0_in_ord : (Hmon0) =>
        Hmon0_in_ord. 
        
        rewrite /monotone0_in_ord in Hmon0_in_ord.
        rewrite
        -[LHS](enum_rankK_in (codom_f f (enum_val (cast_ord (card_codom ((injectiveP f
                                                                       ) Hinj)) j))));
          
           last by apply: enum_valP.
        rewrite
        -[RHS](enum_rankK_in (codom_f f (enum_val (cast_ord (card_codom ((injectiveP f
                                                                         ) Hinj)) j))));
           last by apply: codom_f.
         congr enum_val. rewrite [LHS]enum_valK_in. apply/val_inj => /=.
         rewrite [RHS](enum_rank_congr
                         _ (codom_f (f \o enum_val
                                    ) ((cast_ord (card_codom ((injectiveP f) Hinj)) j)
                      )));
           last (by apply: codom_f);
           last (by rewrite codom_comp_enum_val /eq_mem).

         rewrite (@monotone_injendo_is_id _ _ (f \o enum_val));
           first (by apply/injectiveP/inj_comp;
           [apply/injectiveP : Hinj | apply: enum_val_inj]);
           first by [].
         move => i' j' Hi'j' .
         rewrite [in X in X < _](enum_rank_congr _ (codom_f f (enum_val i')));
           last (by apply: codom_f);
           last (by rewrite codom_comp_enum_val /eq_mem).
         rewrite [in X in _ < X](enum_rank_congr _ (codom_f f (enum_val j')));
           last (by apply: codom_f);
           last (by rewrite codom_comp_enum_val /eq_mem).
           by rewrite -Hmon0_in_ord Hi'j'.
    Qed.
    
  End Section7.

  Section Section8.

    Lemma comp_monoP (aT mT rT : finType) (f1 : aT -> mT) (f2 : mT -> rT) :
      monotoneb f1 -> monotoneb f2 -> monotoneb (f2 \o f1). 
    Proof.
      move => /monotone0P Hf1 /monotone0P Hf2. apply /monotone0P.
      move => x x'. rewrite /funcomp Hf2 Hf1 //.
    Qed.

  End Section8.
  
  Section Section9.

    Import LOGIC.
    Import LOGIC.Ex_Notations3.

    Definition subarrow (V1 V1' V2 : finType) (f : V1 -> V2)
               (f' : V1' -> V2) :=
      exists si : V1 -> V1', f =1 f' \o si .

    Definition submonob (V1 V1' V2 : finType) (f : V1 -> V2)
               (f' : V1' -> V2) :=
      subseq (codom f) (codom f').

    Lemma subset_congrL (T : finType) (A A' B : mem_pred T )
      : A' =i A -> {subset A' <= B} -> {subset A <= B}.
    Proof. by move => HA'A HA'B x; move: HA'A => <- ; apply: HA'B. Qed.

    Lemma subset_congrR (T : finType) (A B B' : mem_pred T )
      : B' =i B -> {subset A <= B'} -> {subset A <= B}.
    Proof. by move => HB'B HAB' x; move: HB'B => <- ; apply: HAB'. Qed.

    Lemma subset_subseq (T : finType) (A B : mem_pred T) :
      {subset A <= B} <-> subseq (enum (mem A)) (enum (mem B)).
    Proof.
      split.
      - move => HAB. apply/subseq_uniqP; first by apply: enum_uniq. 
        erewrite (eq_filter (mem_enum A)).
        rewrite [enum B]/enum_mem. rewrite -filter_predI.
        rewrite (eq_filter (a2:= mem A)); first by reflexivity.
        move => x /=; apply: andb_idr; apply: HAB.
      - move => HAB. eapply subset_congrL; first by apply: mem_enum.
        eapply subset_congrR; first by apply: mem_enum.
        by apply: mem_subseq.
    Qed.

    Lemma submonoP1 (V1 V1' V2 : finType) (f : V1 -> V2)
          (f' : V1' -> V2) :
      monotoneb f -> monotoneb f' ->
      ({subset ((codom f)) <= ((codom f'))}) <-> (submonob f f').
    Proof.
      move =>  /eqP Hf /eqP Hf'.
      rewrite /submonob. rewrite -[in X in _ <-> X]Hf -[in X in _ <-> X]Hf'.
      apply: (subset_subseq (mem(codom f)) (mem (codom f'))) .
    Qed.

    Lemma map_eq_mem_eq_mem (T T' : finType) (f : T -> T') s1 s2 :
      ((mem s1) =i (mem s2)) ->
      mem (map f s1) =i mem (map f s2).
    Proof.
      move => Hs1s2 y. by apply/mapP/mapP; move
                      => [x sx yx]; exists x; rewrite // ?Hs1s2 // -?Hs1s2.
    Qed.

    Lemma submonoP2 (V1 V1' V2 : finType) (f : V1 -> V2)
          (f' : V1' -> V2) :
      (subarrow f f') -> ({subset (codom f) <= (codom f')}).
    Proof.
      move => [Hff' Hff'P].
      rewrite (eq_codom Hff'P).
      rewrite {1}/codom /image_mem map_comp.
      set s1' := (map _ (enum V1)).
      eapply subset_congrL;
        first by apply: (map_eq_mem_eq_mem f' (s1:=enum (mem s1'))); apply: mem_enum.
      apply: image_codom.
    Qed.

    Lemma submonoP3 (V1 V1' V2 : finType) (f : V1 -> V2)
          (f' : V1' -> V2) :
      injectiveb f (* not necessary, use (undup (codom f)) *)->
      ({subset (codom f) <= (codom f')}) -> (subarrow f f').
    Proof.
      move => f_inj Hff'. move/map_preim : (Hff').
      case: (card_gt0P V1'); last first.
      - move/card_gt0P. case: posnP => // HV1' _ _. move/subsetP/subset_leq_card : Hff'.
        move/leq_trans. move/(_ _ (leq_image_card _ V1')). rewrite HV1'.
        rewrite leqn0. move/eqP.
        rewrite card_codom; last by apply/injectiveP. move => /card0_eq => HV1.
        have g : V1 -> V1'.
        { move => x1. move/(predT_subset (subxx_hint _)) : (x1). rewrite HV1 //. }
        exists g. move => x1. move/(predT_subset (subxx_hint _)) : (x1). rewrite HV1 //.
      - move => [x1' _].
        move => H. About size_map. move/(f_equal size) : (H); rewrite size_map.
        move => Hsize.
        move: (map_of_seq ( codom f) ( preim_seq f' (codom f)) x1')  .
        move => [g gP]. move/(_ f_inj Hsize) : gP => gP'.
        exists (g \o f). move => x1.
        rewrite -[x1]enum_rankK. rewrite -?(nth_image (f x1)). congr nth.
        move: (map_preim Hff'). move => J; rewrite -[LHS]J .
        rewrite [RHS]/image_mem [RHS]map_comp. congr map.
        rewrite [RHS]map_comp. symmetry. apply: gP'.
    Qed.
    
    Lemma submonoP (V1 V1' V2 : finType) (f : V1 -> V2)
          (f' : V1' -> V2) :
      monotoneb f -> monotoneb f' ->
      reflect (subarrow f f') (submonob f f').
    Proof.
      move => Hf Hf'.  apply/(equivP (idP)). rewrite -submonoP1 //.
      move/monotoneb_injectiveb : Hf => Hf. by split; [apply: submonoP3 | apply: submonoP2].
    Qed.

  End Section9.
  
End FINMONO.

Module EXAMPLE1.

  Import REVFUNCTOR.
  Import FINLOGIC.
  Import FINMONO.

  Import LOGIC.Ex_Notations3.
 
  Section Section1.

    Open Scope quotient_scope.

    Context {catA : @form logfT} {catB : category logfT}.
    Variable (func : functorToCat catA catB).

    (* coin .. coinjection  .. comono .. *)
    Hypothesis V_ : forall (B : obB func) (A : obA func), obV logfT.
    Variable f_ : forall (B : obB func) (A : obA func), {finj V_ B A -> F[0 B ~> A ]0 }.
    Arguments f_ : clear implicits.

    Lemma pi_comono_revfunctor_polyF :
      comono_revfunctor_polyF f_ <->
      forall (A A' : obA func) (g : logfT.-V(0 I |- A[0 A ~> A']0 )0),
        subarrow (F|1 A A' <o g) (\pi_{fmon _} (f_ (F|0 A) A')) -> forall (B : obB func),
          subarrow (\pi_{fmon _} (f_ B A') : logfT.-V(0 _ |- _ )0)
                   ((\pi_{fmon _} (f_ B A)) o>`func` g).
      (* by mkMonotone_base_subinj *)
    Admitted.

  End Section1.

End EXAMPLE1.
