(*** SECTION 3: Inverse Semigroups ***)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import Ensembles.
Require Import Relations_1.
Require Import Partial_Order.

(* Preliminary definitions, take 2 *)
Section Definitions.
  Variable U : Type.
  Variable op : U -> U -> U.
  Variable s : U -> U.
  Definition associative := forall x y z : U, op (op x y) z = op x (op y z).
  Definition pseudo1 := forall x : U, op (op x (s x)) x = x.
  Definition pseudo2 := forall x : U, op (op (s x) x) (s x) = s x.
  Definition ispseudo op (x y : U) := (x = op (op x y) x) /\ (y = op (op y x) y).
  Definition pseudounique op s := forall x y : U, (ispseudo op x y) -> (y = s x).
  Definition commute (x y : U) := (op x y = op y x).
  Definition idempotent op (x : U) := op x x = x.
  Definition idems_commute := forall x y : U, (idempotent op x) -> (idempotent op y) -> (commute x y).
  Variable X : Ensemble U.
  Definition endo_fn (f : U -> U) := forall x : U, In U X x -> In U X (f x).
  Definition endo_op (o : U -> U -> U) := forall x y : U, (In U X x /\ In U X y) -> In U X (o x y).
End Definitions.

(* Now we define inverse semigroups.  Rather than repeat the work of TwoEquivalentAxiomatizations, we simply define, in the language of Ensembles, 
   an inverse semigroup to be a regular semigroup satisfying both equivalent conditions in the main theorem of Section 1. *)

Section Inv_Semigroup.
  Record inv_semigroup (U : Type) := mkinv_semigroup
    {EX : Ensemble U;
     oh : U -> U -> U;
     oh_endo : endo_op EX oh;
     oh_assoc : associative oh;
     es : U -> U;
     es_endo : endo_fn EX es;
     oh_pseudo1 : pseudo1 oh es; 
     oh_pseudo2 : pseudo2 oh es;
     pseudo_law1 : pseudounique oh es;
     pseudo_law2 : idems_commute oh
    }.
    (* Now the binary operation and pseudoinversion are technically acting on -all- possible elements in our universe U, not just those that are in the
       set we care about.  Thus, we now do need to specify that the binary operation and pseudoinversion don't take us out of our inverse semigroup (ie, are
       respectively an endo operation and endo function.) *)
End Inv_Semigroup.

(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)

(*** SECTION 3.1: Properties of pseudoinverses and idempotents ***)

Section Properties_pseudo_idem.
  Variable U : Type.
  Variable S : inv_semigroup U.
  Let X := EX S.
  Let o := oh S.
  Let s := es S.
  Let a := oh_assoc S.
  Let end_o := oh_endo.
  Let end_s := es_endo.
  Let ps1 := oh_pseudo1 S.
  Let ps2 := oh_pseudo2 S.
  Let pl1 := pseudo_law1.
  Let pl2 := pseudo_law2.
  Infix "+" := o.
  Hint Unfold X o s a.
  Hint Resolve end_o end_s ps1 ps2 pl1 pl2.

  (* Next to discovering "congruence", "Infix" is the next most amazing thing that I discovered.  Looking back at TwoEquivalentAxiomatizations, there are
     lines of code that look like
           "transitivity (o (o (o y (e (o x y))) x) (o (o y (e (o x y))) x))".
     This also required many bleary-eyed hours in the basement of 585KED to figure out how to write - not to mention it's also not very human readable either.  Using infix, we can just 
     write "x + y" for "o x y", and moreover this automatically associates to the left.  This makes equations look much more like what we as humans are used to, and greatly sped up 
     progress on proofs. *)

  (* Also new to this section is the habit of adding hints after every definition or lemma/theorem as appropriate.  There are several places where we are able to use auto
     and Coq is able to use these hints to automate some of the tedious steps.  The most frequently used case of this is to use the fact that the binary operation and pseudoinversion
     are endo operations, so that, for instance, if x,y are in X, then x+(y^{-1}) is in X as well.  Any proof where this is used begins with the line
           "unfold endo_op in end_o; unfold endo_fn in end_s."
     because Coq is smart enough to try -one- hint at a time, but won't try arbitrary combinations of hints on its own. *)
 
  (* Lemma 1a : the product of an element with its pseudoinverse is idempotent *)
    Lemma prod_with_pseudo_is_idem : forall x : U, In U X x -> (idempotent o (x + (s x)) /\ idempotent o ((s x) + x)).
      intro y; intro H.
      unfold idempotent; split.
      transitivity (y + (s y + y + s y)).
      unfold o, s; congruence.
      rewrite ps2; auto.
      transitivity (s y + y + s y + y).
      unfold o, s; congruence.
      rewrite ps2; auto.
    Save.
    Hint Resolve prod_with_pseudo_is_idem.
  (* Lemma 1b : pseudoinversion is an involution *)
    Lemma pseudo_is_involn : forall x : U, In U X x -> s (s x) = x.
      intro y; intro H.
        assert ((s y = s y + y + s y) /\ (y = y + s y + y)).
          split.
          unfold s; rewrite ps2; auto.
          unfold s; rewrite ps1; auto.
      fold (ispseudo o (s y) y) in H0.
      generalize (pl1 H0); intro H1.
      auto.
    Save.
    Hint Resolve pseudo_is_involn.
  (* Lemma 1c : for any x, any idempotent e, (x^{-1} e x) is idempotent *)
    Lemma sxex_is_idem : forall x e : U, (In U X x) -> (In U X e) -> (idempotent o e) -> (idempotent o (s x + e + x)).
      intros y i; intro H; intros.
      decompose [and] H.
      unfold idempotent.
      generalize (prod_with_pseudo_is_idem H); intro H4.
      decompose [and] H4; clear H4.
      generalize (pl2 H1 H2); intro H7.
      transitivity (s y + (i + i) + (y + s y + y)).
      Focus 2.
      rewrite H1; rewrite ps1; auto.
      transitivity (s y + i + (i + (y + s y)) + y).
      Focus 2.
      unfold o, s; congruence.
      fold o in H7.
      rewrite H7; auto.
      unfold o, s; congruence.
    Save.
    Hint Resolve sxex_is_idem.
  (* Lemma 1d : idempotents are self-pseudoinverse *)
    Lemma idem_is_selfpseudo : forall e : U, (In U X e) -> (idempotent o e) -> (e = (s e)).
      intro i; intro H; intros.
      decompose [and] H.
        assert (ispseudo o i i).
          unfold ispseudo; split.
          rewrite H0; auto.
          rewrite H0; auto.
      generalize (pl1 H1); intro H3.
      auto.
    Save.
    Hint Resolve idem_is_selfpseudo.
  (* Lemma 1e : (xy)^{-1} = y^{-1}x^{-1} *)
    Lemma inversion_symmetry : forall x y : U, (In U X x) -> (In U X y) -> (s (x + y) = s y + s x).
      intros x1 x2; intro H; decompose [and] H; intros.
      symmetry.
      generalize (prod_with_pseudo_is_idem H); intro H2; generalize (prod_with_pseudo_is_idem H0); intro H3.
      decompose [and] H2; decompose [and] H3.
      generalize (pl2 H4 H5); intro H9.
      fold o in H9.
        assert (ispseudo o (x1 + x2) (s x2 + s x1)).
          unfold ispseudo; split.
          transitivity ((x1 + s x1 + x1) + (x2 + s x2 + x2)).
          rewrite ps1; rewrite ps1; auto.
          transitivity (x1 + ((x2 + s x2) + (s x1 + x1)) + x2).
          Focus 2.
          unfold o, s; congruence.
          rewrite <- H9.
          unfold o, s; congruence.
          transitivity ((s x2 + x2 + s x2) + (s x1 + x1 + s x1)).
          rewrite ps2; rewrite ps2; auto.
          transitivity (s x2 + ((s x1 + x1) + (x2 + s x2)) + s x1).
          Focus 2.
          unfold o, s; congruence.
          rewrite H9.
          unfold o, s; congruence.
      generalize (pl1 H7); intro H8.
      fold s in H8; auto.
    Save.
    Hint Resolve inversion_symmetry.
  (* Lemma 1f : the product of idempotents is idempotent *)
    Lemma prod_of_idem_is_idem : forall x y : U, (In U X x) -> (In U X y) -> (idempotent o x) -> (idempotent o y) -> (idempotent o (x + y)).
      intros xo yo; intros.
      unfold idempotent.
      transitivity (xo + (yo + xo) + yo).
      unfold o; congruence.
      generalize (pl2 H1 H2); intro H3.
      fold o in H3; rewrite <- H3.
      transitivity (xo + xo + (yo + yo)).
      unfold o; congruence.
      rewrite H1; rewrite H2; auto.
    Save.
    Hint Resolve prod_of_idem_is_idem.

  (* In this proof, we use for the first time the "pattern" command.  This is done immediately before a rewrite command to tell Coq to only rewrite some occurrences
     of the string in question. *)
  (* Lemma 2 : for every idempotent e and element x, there are idempotents f,g such that ex = xf and xe = gx *)
    Lemma idempotent_wire : forall x e : U, (In U X x) -> (In U X e) -> (idempotent o e) -> 
        (exists f : U, (In U X f) /\ (idempotent o f) /\ (e + x) = (x + f)) /\ (exists g : U, (In U X g) /\ (idempotent o g) /\ (x + e) = (g + x)).
      intros y i; intro H; decompose [and] H.
      unfold endo_op in end_o; unfold endo_fn in end_s.
      split.
      (* part a *)
        exists (s y + i + y); split.
          assert (In U X (s y + i)).
            unfold o, s, X; auto.
        unfold o, s, X; auto.
        split.
        auto.
        transitivity (i + (y + s y + y)).
        rewrite ps1; auto.
        transitivity (i + (y + s y) + y).
        unfold o, s; congruence.
        generalize (prod_with_pseudo_is_idem H); intro H4; decompose [and] H4.
        generalize (pl2 H2 H1); intro H6.
        fold o in H6; rewrite <- H6.
        unfold o, s; congruence.      
      (* part b *)
        exists (y + i + s y); split.
          assert (In U X (y + i)).
            unfold o, s, X; auto.
        unfold o, s, X; auto.
        split.
        auto.
        generalize (pseudo_is_involn H); intro H4.
        pattern y at 1; rewrite <- H4.
        generalize (end_s H); intro Ha; fold X s in Ha.
        generalize (end_s Ha); intro Hb; fold X s in Hb.
        auto.
        transitivity (y + s y + y + i).
        rewrite ps1; auto.
        transitivity (y + (s y + y + i)).
        unfold o, s; congruence.
        generalize (prod_with_pseudo_is_idem H); intro H4; decompose [and] H4.
        generalize (pl2 H3 H1); intro H6.
        fold o in H6; rewrite H6.
        unfold o, s; congruence.
    Save.
    Hint Resolve idempotent_wire.
End Properties_pseudo_idem.

(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)

(*** SECTION 3.2: Ideals and generators ***)

(* Definitions of (left/right) ideals *)
Section Ideals.
  Variable U : Type.
  Inductive l_ideal (I : Ensemble U) (S : inv_semigroup U) : Prop :=
    l_ideal_intro : Included U I (EX S) -> (forall b x : U, ((In U (EX S) x) -> (In U I b) -> (In U I (oh S x b)))) -> l_ideal I S.
  Inductive r_ideal (I : Ensemble U) (S : inv_semigroup U) : Prop :=
    r_ideal_intro : Included U I (EX S) -> (forall b x : U, ((In U (EX S) x) -> (In U I b) -> (In U I (oh S b x)))) -> r_ideal I S.
  Hint Resolve l_ideal_intro r_ideal_intro.
End Ideals.

(* Definitions of (left/right) principal ideals *)
Section PrincipalIdeals.
  Variable U : Type.
  Inductive lp_ideal (S : inv_semigroup U) (a : U) : Ensemble U :=
    lp_ideal_intro : forall y : U, In U (EX S) a -> In U (EX S) y -> (exists r : U, (In U (EX S) r /\ y = (oh S r a))) -> In U (lp_ideal S a) y.
  Inductive rp_ideal (a : U) (S : inv_semigroup U) : Ensemble U :=
    rp_ideal_intro : forall y : U, In U (EX S) a -> In U (EX S) y -> (exists r : U, (In U (EX S) r /\ y = (oh S a r))) -> In U (rp_ideal a S) y.
  Hint Resolve lp_ideal_intro rp_ideal_intro.
End PrincipalIdeals.

(* Ideals and principal ideals are defined inductively.  Each has only one introduction rule.  If we have the last thing in the chain of implications, we can conclude that
   the rest hold.  If we have all but the last, we can conclude the last. *)

(* Structural properties of principal ideals - we only prove them for right principal ideals; analogous statements for left principal ideals have analogous proofs *)
Section PI_structure.
  Variable U : Type.
  Variable S : inv_semigroup U.
  Let X := EX S.
  Let o := oh S.
  Let s := es S.
  Let a := oh_assoc S.
  Let end_o := oh_endo.
  Let end_s := es_endo.
  Let ps1 := oh_pseudo1 S.
  Let ps2 := oh_pseudo2 S.
  Let pl1 := pseudo_law1.
  Let pl2 := pseudo_law2.
  Infix "+" := o.
  Hint Unfold X o s a.
  Hint Resolve end_o end_s ps1 ps2 pl1 pl2.

  (* Technically these are more remarks than lemmas; all this stuff is "too obvious" to even write down on paper, but we need to prove it here anyway.
     1a we will actually need to use, so doing it once saves some work later on. *)
  (* Remark 1a : if x is in the (right) principal ideal aS, then we can write x = ar for some r in S *)
    Lemma instantiate_rp_ideal : forall a x : U, In U (rp_ideal a S) x -> (exists r : U, (In U (EX S) r /\ x = (a + r))).
      intros a0 x0.
      intro H.
      elim H; intros.
      fold o in H2; auto.
    Save.
      (* Notice something strange during this proof.  When we elim H, it replaces our variable with a new variable and also changes the goal of the proof.
         While this doesn't affect the proof here, having to do this in the middle of a bigger proof unneccesarily clutters the screen with extra variables and hypotheses.
         Thus, it's nice to just every time we have someting like this to prove an "instantiation lemma" and be able to use it in future proofs as a one-liner instead of a four-liner. *)

  (* Remark 1b : (right) principal ideals are (right) ideals *)
    Lemma rpideal_is_rideal : forall r : U, In U (EX S) r -> r_ideal (rp_ideal r S) S.
        intros r0 J.
        unfold endo_op in end_o; unfold endo_fn in end_s.
        assert (Included U (rp_ideal r0 S) (EX S)).
          unfold Included.
          intros xo H.
          elim H; intros.
          elim H2; intros.
          decompose [and] H3.
          rewrite H5.
          auto.
        assert (forall b x : U, ((In U (EX S) x) -> (In U (rp_ideal r0 S) b) -> (In U (rp_ideal r0 S) (oh S b x)))).
          intros bo xo; intros.
          elim H1; intros.
          elim H4; intros.
          decompose [and] H5.
          rewrite H7.
          apply rp_ideal_intro.
          assumption.
          auto.
          fold o; fold o.
          exists (x + xo).
          split.
          unfold o, X; auto.
          unfold o; congruence.
      generalize (r_ideal_intro H H0); auto.
    Save.

  (* Remark 1c : every element is in the (right) principal ideal it generates *)
    Lemma r_in_rX : forall r : U, In U (EX S) r -> In U (rp_ideal r S) r.
      intro r0; intro H.
      unfold endo_op in end_o; unfold endo_fn in end_s.
      generalize (ps1 r0); intro H1.
      fold o s X in H1; fold o in H1; fold o in H1.
      pattern r0 at 2; rewrite <- H1.
        assert (In U (EX S) (r0 + s r0 + r0)).
          assert (In U (EX S) (r0 + s r0)).
            unfold o, s; auto.
          unfold o, s; auto.
        assert (exists x : U, (In U (EX S) x /\ r0 + s r0 + r0 = r0 + x )).
          exists (s r0 + r0).
          split.
          unfold o, s; auto.
          unfold o, s; congruence.
      generalize (rp_ideal_intro H H0 H2); auto.
     Save.
     Hint Resolve instantiate_rp_ideal rpideal_is_rideal r_in_rX.

  (* Theorem : (Right) principal ideals have a unique idempotent generator *)
    (* Part a (existence) : for any r in X, rX = (rr^{-1})X *)
    Theorem rpideals_have_unique_idemgenerator_1 : forall r : U, In U (EX S) r -> (Same_set U (rp_ideal r S) (rp_ideal (r + s r) S)).
      intros r0 H.
      unfold endo_op in end_o; unfold endo_fn in end_s.
      unfold Same_set.
      unfold Included.
      split.
      (* Part a.I : rX is contained in rr^{-1}X *)
        intros x0 H0.
        elim H0; intros.
        elim H3; intro x1; intros; clear H3.
        decompose [and] H4; clear H4.
          assert (y = (r0 + s r0) + (r0 + x1)).
            fold o in H5; rewrite H5.
            generalize (ps1 r0); intro H6.
            fold o s in H6; fold o in H6.
            pattern r0 at 1; rewrite <- H6.
            unfold o, s; congruence.
        rewrite H4.
          assert (In U (EX S) (r0 + s r0)).
            unfold o, s; auto.
          assert (In U (EX S) (r0 + s r0 + (r0 + x1))).
            unfold o, s; auto.
          assert (exists r : U, (In U (EX S) r /\ (r0 + s r0 + (r0 + x1)) = (r0 + s r0) + r)).
            exists (r0 + x1).
            split.
            unfold o; auto.
            auto.
        generalize (rp_ideal_intro H6 H7 H8); intro H9.
        auto.
      (* Part a.II : rr^{-1}X is contained in rX *)
        intros x0 H0.
        elim H0; intros.
        elim H3; intro x1; intros; clear H3.
        decompose [and] H4; clear H4.
        fold o in H5; rewrite H5.
          assert (In U (EX S) (r0 + s r0 + x1)).
            unfold o, s; auto.
          assert (exists r : U, (In U (EX S) r /\ r0 + s r0 + x1 = (r0 + r))).
            exists (s r0 + x1).
            split.
            unfold o, s; auto.
            unfold o, s; congruence.
          assert (In U (EX S) (r0 + s r0 + x1)).
            unfold o, s; auto.
        generalize (rp_ideal_intro H H7 H6); intro H8.
        auto.  
    Save.        
    Hint Resolve rpideals_have_unique_idemgenerator_1.
    (* Part b (uniqueness) : rr^{-1} is the unique idempotent generator of rX *)
    Theorem rp_ideals_have_unique_idemgenerator_2 : forall r : U, In U (EX S) r -> forall e : U, (In U (EX S) e -> idempotent o e -> 
        Same_set U (rp_ideal e S) (rp_ideal r S) -> e = r + s r).
      intros r0 H i; intros.
      unfold endo_op in end_o; unfold endo_fn in end_s.
      unfold Same_set in H2.
      decompose [and] H2; clear H2.
      unfold Included in H3; unfold Included in H4.
        assert (In U (EX S) (r0 + s r0)).
        unfold o, s; auto.
      generalize (rpideals_have_unique_idemgenerator_1 H); intro J.
      unfold Same_set in J; unfold Included in J.
      decompose [and] J; clear J.
        assert (K1 : (In U (rp_ideal i S) (r0 + s r0))).
          generalize (r_in_rX H2); intro H7.
          generalize (H6 (r0 + s r0) H7); intro H8.
          generalize (H4 (r0 + s r0) H8); intro H9.
          auto. 
        assert (K2 : (In U (rp_ideal (r0 + s r0) S) i)).
          generalize (r_in_rX H0); intro H7.
          generalize (H3 i H7); intro H8.
          generalize (H5 i H8); intro H9.
          auto.
      clear H3 H4 H5 H6.
        assert (In U (EX S) (r0 + s r0)).
          unfold o, s; auto.
      generalize (instantiate_rp_ideal K1); intro J1; clear K1.
      generalize (instantiate_rp_ideal K2); intro J2; clear K2.
      elim J1; intro p; intro K3; clear J1.
      elim J2; intro t; intro K4; clear J2.
      decompose [and] K3; clear K3; decompose [and] K4; clear K4.
      generalize (prod_with_pseudo_is_idem H); intro K5.
      fold o in K5; decompose [and] K5; clear K5.
      fold o s in H8; clear H9.
        assert (r0 + s r0 + i = i).
          transitivity (r0 + s r0 + (r0 + s r0 + t)).
          rewrite <- H7; auto.
          transitivity (r0 + s r0 + (r0 + s r0) + t).
          unfold o, s; congruence.
          rewrite H8.
          rewrite H7; auto.
        assert (i + (r0 + s r0) = r0 + s r0).
          pattern (r0 + s r0) at 1; rewrite <- H8.
          pattern (r0 + s r0) at 1; rewrite H5.
          transitivity (i + i + p + r0 + s r0).
          unfold o, s; congruence.
          rewrite H1.
          rewrite <- H5.
          transitivity (r0 + s r0 + (r0 + s r0)).
          unfold o, s; congruence.
          auto.
      rewrite <- H9.
      generalize (pl2 H1 H8); intro.
      transitivity (i + (r0 + s r0)).
      unfold commute in H11; fold o in H11.
      auto.
      auto.
    Save.
    Hint Resolve rp_ideals_have_unique_idemgenerator_2.
  
  (* "Lemma" to instantiate intersections *)
    Lemma instantiate_intersection : forall A B : Ensemble U, forall x : U, In U (Intersection U A B) x -> (In U A x /\ In U B x).
      intros A B xo; intros.
      elim H; intros.
      auto.
    Save.
    Hint Resolve instantiate_intersection.

  (* Theorem: if e, f are idempotents, then the intersection of eX and fX is efX *)
    Theorem idem_rpideal_intersection : forall e f : U, In U (EX S) e /\ idempotent o e /\ In U (EX S) f /\ idempotent o f ->
        Same_set U (Intersection U (rp_ideal e S) (rp_ideal f S)) (rp_ideal (e + f) S).
      unfold endo_op in end_o; unfold endo_fn in end_s.
      intros e f; intros.
      decompose [and] H; clear H. 
      unfold Same_set; unfold Included.
      split.
      (* (1): eX \cap fX \subseteq efX *)
        intro xo; intro K.
        generalize (instantiate_intersection K); intro K1; clear K.
        decompose [and] K1; clear K1.
        generalize (instantiate_rp_ideal H); intro K2.
          assert (In U (EX S) xo).
            elim H; intros.
            auto.
        generalize (instantiate_rp_ideal H3); intro K3; clear H3.
        elim K2; intro x1; intros; clear K2.
        elim K3; intro x2; intros; clear K3.
        decompose [and] H3; clear H3; decompose [and] H6; clear H6; clear H.
          assert (J1 : e + xo = xo).
            pattern xo at 1; rewrite H8.
            transitivity (e + e + x1).
            unfold o; congruence.
            rewrite H2.
            auto.
          assert (J2 : f + xo = xo).
            pattern xo at 1; rewrite H9.
            transitivity (f + f + x2).
            unfold o; congruence.
            rewrite H4.
            auto.
          assert (J3 : xo = e + f + xo).
            pattern xo at 1; rewrite <- J1.
            pattern xo at 1; rewrite <- J2.
            unfold o; congruence.
          assert (In U (EX S) (e + f)).
            unfold o; auto.
          assert (exists r : U, (In U (EX S) r /\ xo = e + f + r)).
            exists xo.
            split; auto; auto.
         generalize (rp_ideal_intro H H5 H6); intro L.
         auto.
      (* (2) efX \subseteq eX \cap fX *)
        intro xo; intro K.
        generalize (instantiate_rp_ideal K); intros.
        elim H; intro x1; intros; clear H.
        decompose [and] H3; clear H3.
          assert (In U (EX S) xo).
            elim K; intros.
            auto.
          assert (J1 : In U (rp_ideal e S) xo).
            assert (xo = e + (f + x1)).
              rewrite H5; unfold o; congruence.
            assert (exists r : U, (In U (EX S) r /\ xo = e + r)).
              exists (f + x1).
              split.
              unfold o; auto.
              auto.
            generalize (rp_ideal_intro H0 H3 H7); intro L1.
            auto.
          assert (J2 : In U (rp_ideal f S) xo).
            assert (xo = f + (e + x1)).
              pattern xo at 1; rewrite H5.
              transitivity (f + e + x1).
              generalize (pl2 H2 H4); intro.
              unfold commute in H6; fold o in H6.
              rewrite H6; auto.
              unfold o; congruence; auto.
            assert (exists r : U, (In U (EX S) r /\ xo = f + r)).
              exists (e + x1).
              split.
              unfold o; auto.
              auto.
            generalize (rp_ideal_intro H1 H3 H7); intro L2.
            auto.
        generalize (Intersection_intro U (rp_ideal e S) (rp_ideal f S) xo J1 J2); intro J3.
        auto.
    Save.
    Hint Resolve idem_rpideal_intersection.
End PI_structure.

(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)

(*** SECTION 3.3: The natural partial order ***)

Section defining_the_relation.
  Variable U : Type.
  Inductive leq (S : inv_semigroup U) : U -> U -> Prop :=
    leq_intro : forall s t : U, In U (EX S) s -> In U (EX S) t -> (exists e : U, (In U (EX S) e) /\ idempotent (oh S) e /\ s = (oh S t e)) -> leq S s t.
End defining_the_relation.

Section partial_order.
  Variable U : Type.
  Variable S : inv_semigroup U.
  Let X := EX S.
  Let o := oh S.
  Let s := es S.
  Let a := oh_assoc S.
  Let end_o := oh_endo.
  Let end_s := es_endo.
  Let ps1 := oh_pseudo1 S.
  Let ps2 := oh_pseudo2 S.
  Let pl1 := pseudo_law1.
  Let pl2 := pseudo_law2.
  Infix "+" := o.
  Infix "<" := (leq S).
  Hint Unfold X o s a.
  Hint Resolve end_o end_s ps1 ps2 pl1 pl2.
  
  (* When s<t, we can write s=te for an idempotent e *)
    Lemma instantiate_order : forall x y : U, (In U X x) -> (In U X y) -> (x < y) -> (exists i : U, (In U X i) /\ idempotent o i /\ x=(y + i)).
      intros xo yo; intros.
      decompose [and] H.
      elim H1; intros.
      elim H4; intro eo; intros.
      exists eo.
      unfold o, X; auto.
      Save.
      Hint Resolve instantiate_order.

  (* Lemma: the following are equivalent.
     (1) s < t
     (2) s = ft for some idempotent f
     (3) s^{-1} < t^{-1}
     (4) s = ss^{-1}t
     (5) s = ts^{-1}s. 
     The proof proceeds with cyclic implication (1) -> (2) -> (3) -> (4) -> (5) -> (1) *)
    (* (1) implies (2) *)
      Lemma tfae_1_2 : forall x y : U, (In U X x) -> (In U X y) -> ((x < y) -> (exists f : U, (In U X f) /\ idempotent o f /\ x = (f + y))).
        intros xo yo; intros.
        generalize (instantiate_order H H0 H1); intro J.
        elim J; intro e; intros.
        decompose [and] H2; clear H2.
        generalize (idempotent_wire H0 H3 H5); intro K.
        decompose [and] K; clear K.
        clear H2; fold o in H4.
        elim H4; intro fo; intros.
        exists fo.
        split.
        fold X in H2.
        decompose [and] H2; auto.
        split.
        decompose [and] H2; auto.
        transitivity (yo + e).
        auto.
        decompose [and] H2; auto.
        Save.
    (* (2) implies (3) *)
      Lemma tfae_2_3 : forall x y : U, (In U X x) -> (In U X y) -> ((exists f : U, (In U X f) /\ idempotent o f /\ x = (f + y)) -> (s x) < (s y)).
        unfold endo_op in end_o; unfold endo_fn in end_s.
        intros xo yo; intros.
        elim H1; intro fo; intros; clear H1.
        decompose [and] H2; intros; clear H2.
        apply leq_intro.
        unfold o, s, X; auto.
        unfold o, s, X; auto.
        exists fo.
        fold o s X; split.
        auto.
        split.
        auto.
        rewrite H5.
        generalize (inversion_symmetry H1 H0); intro J1.
        fold o s in J1.
        rewrite J1.
        generalize (idem_is_selfpseudo H1 H4); intro J2.
        fold s in J2; pattern fo at 2; rewrite <- J2.
        auto.
        Save.
    (* (3) implies (4) *)
       Lemma tfae_3_4 : forall x y : U, (In U X x) -> (In U X y) -> ((s x) < (s y) -> x = (x + (s x) + y)).
         intros xo yo; intros.
         unfold endo_op in end_o; unfold endo_fn in end_s.
           assert (In U X (s xo)).
             unfold s, X; auto.
           assert (In U X (s yo)).
             unfold s, X; auto.
         generalize (instantiate_order H2 H3 H1); intros; clear H1.
         elim H4; intro e; intros.
         decompose [and] H1; clear H1.
           assert (J1 : xo = e + yo).
             transitivity (s (s xo)).
             generalize (pseudo_is_involn H); intro H9.
             auto.
             transitivity (s (s yo + e)).
             rewrite H8; auto.
             generalize (inversion_symmetry H3 H5); intro H9.
             fold o s in H9.
             rewrite H9.
             generalize (idem_is_selfpseudo H5 H7); intro H10.
             generalize (pseudo_is_involn H0); intro H11.
             fold o s in H10; rewrite <- H10.
             fold o s in H11; fold s in H11; rewrite H11.
             auto.
           assert (J2 : e + xo = xo).
             pattern xo at 1; rewrite J1.
             transitivity (e + e + yo).
             unfold o; congruence.
             rewrite H7.
             auto.
           assert (J3 : e + xo + (s xo) = xo + (s xo)).
             rewrite J2; auto.
         symmetry.
         rewrite <- J3.
         transitivity (e + (xo + s xo) + yo).
         unfold o; congruence.
         generalize (prod_with_pseudo_is_idem H); intro K1.
         inversion K1 as [K2 K3]; clear K1.
         fold o s in K2; clear K3.
         generalize (pl2 H7 K2); intro K3.
         fold o in K3; rewrite K3.
         transitivity (xo + s xo + (e + yo)).
         unfold o, s; congruence.
         rewrite <- J1.
         unfold o, s; auto.
         Save.
    (* (4) implies (5) *)
       Lemma tfae_4_5 : forall x y : U, (In U X x) -> (In U X y) -> (x = (x + (s x) + y) -> x = (y + (s x) + x)).
         intros xo yo; intros.
         unfold endo_op in end_o; unfold endo_fn in end_s.
         generalize (prod_with_pseudo_is_idem H); intro J1.
         fold o s in J1; inversion J1 as [J2 J3]; clear J1.
           assert (In U X (xo + s xo)).
             unfold o, s, X; auto.
         generalize (idempotent_wire H0 H2 J2); intro J4.
         decompose [and] J4; clear J4.
         elim H3; intro eo; intros; clear H3; clear H4.
         fold o s X in H5; decompose [and] H5; clear H5.
           assert (J4 : s xo + xo + eo = s xo + xo).
             pattern xo at 2; rewrite H1; rewrite H7.
             transitivity (s xo + yo + (eo + eo)).
             unfold o, s; congruence.
             rewrite H6.
             transitivity (s xo + (yo + eo)).
             unfold o, s; congruence.
             rewrite <- H7; rewrite <- H1.
             auto.
         symmetry.
         transitivity (yo + (s xo + xo)).
         unfold o, s; congruence.
         rewrite <- J4.
         transitivity (yo + (eo + (s xo + xo))).
           assert (In U X (s xo + xo)).
             unfold o, s, X; auto.
         generalize (pl2 J3 H6); intro J5.
         fold o in J5; rewrite J5.
         auto.
         transitivity (yo + eo + s xo + xo).
         unfold o, s; congruence.
         rewrite <- H7; rewrite <- H1.
         unfold o, s; auto.
         Save.
    (* (5) implies (1) *)
       Lemma tfae_5_1 : forall x y : U, (In U X x) -> (In U X y) -> (x = (y + (s x) + x) -> x < y).
         intros xo yo; intros.
         unfold endo_op in end_o; unfold endo_fn in end_s.
         apply leq_intro.
         auto.
         auto.
         exists (s xo + xo).
         split.
         unfold o, s; auto.
         split.
         generalize (prod_with_pseudo_is_idem H); intro H2.
         decompose [and] H2; clear H2; auto. 
         pattern xo at 1; rewrite H1.
         unfold o, s; congruence.
         Save.
       Hint Resolve tfae_1_2 tfae_2_3 tfae_3_4 tfae_4_5 tfae_5_1.

  (* Defining what a partial order is in the context of Ensembles. *)
     Definition reflexive (R : U -> U -> Prop) (Y : Ensemble U) : Prop := 
       forall x : U, In U Y x -> R x x.
     Definition antisymmetric (R : U -> U -> Prop) (Y : Ensemble U) : Prop := 
       forall x y : U, In U Y x -> In U Y y -> R x y -> R y x -> x = y.
     Definition transitive (R : U -> U -> Prop) (Y : Ensemble U) : Prop := 
       forall x y z : U, In U Y x -> In U Y y -> In U Y z -> R x y -> R y z -> R x z.
     Inductive partial_order (R : U -> U -> Prop) (Y : Ensemble U) : Prop := 
       po_intro : reflexive R Y -> antisymmetric R Y -> transitive R Y -> partial_order R Y.

  (* Theorem: < is a partial order. *)
  (* In the Ideals section, we often applied the intro rule for inductive definition forwards by first asserting all the necessary pieces were true and 
     then using "generalize" to conclude the result.  In this section, we instead used "apply".  While we end up proving all the same things, the latter 
     method is a bit nicer because Coq will then tell us the subgoals we need to prove one by one, and saves a bit of work. *)
    Theorem leq_is_partialorder : partial_order (leq S) X.
      unfold endo_op in end_o; unfold endo_fn in end_s.
      apply po_intro.
      (* reflexivity *)
        unfold reflexive.
        intro xo; intro.
        apply leq_intro.
        auto.
        auto.
        exists (s xo + xo).
        split.
        unfold o, s, X; auto.
        fold o; split.
        generalize (prod_with_pseudo_is_idem H); intro H1.
        decompose [and] H1; clear H1.
        auto.
        transitivity (xo + s xo + xo).
        auto.
        unfold o, s; congruence.
      (* antisymmetry *)
        unfold antisymmetric.
        intros xo yo; intros.
          assert (xo = yo + s xo + xo).
            auto.
          assert (yo = xo + s yo + yo).
            auto.
          assert (commute o (s yo + yo) (s xo + xo)).
            unfold commute.
              assert (idempotent o (s yo + yo)).
                generalize (prod_with_pseudo_is_idem H0); intros.
                decompose [and] H5; auto.
              assert (idempotent o (s xo + xo)).
                generalize (prod_with_pseudo_is_idem H); intros.
                decompose [and] H6; auto.
            generalize (pl2 H5 H6); intro.
            auto.
        rewrite H3.
        pattern yo at 1; rewrite H4.
        transitivity (xo + ((s yo + yo) + (s xo + xo))).
        unfold o, s; congruence.
        transitivity (xo + ((s xo + xo) + (s yo + yo))).
        rewrite <- H5; auto.
        transitivity (xo + s yo + yo).
        unfold o, s; congruence.
        auto.
      (* transitivity *)
        unfold transitive.
        intros xo yo zo; intros.
        apply leq_intro.
        auto.
        auto.
        generalize (instantiate_order H H0 H2); intro J1.
        generalize (instantiate_order H0 H1 H3); intro J2.
        elim J1; intro eo; intros; clear J1.
        elim J2; intro fo; intros; clear J2.
        decompose [and] H4; decompose [and] H5; clear H4; clear H5.
        exists (fo + eo).
        fold o s X; split.
        unfold o, X; auto.
        split.
        apply prod_of_idem_is_idem.
        auto.
        auto.
        auto.
        auto.
        symmetry; transitivity (zo + fo + eo).
        unfold o, s; congruence.
        rewrite <- H12.
        auto.
       Save.
       Hint Resolve leq_is_partialorder.

  (* Proposition: The following hold.
       (1) If e, f are idempotent, then e<f iff e=ef=fe
       (2) If s<t and u<v then su<tv
       (3) If s<t then s^{-1}s<t^{-1}t and ss^{-1}<tt^{-1} *)
    Lemma order1 : forall e f : U, In U X e -> In U X f -> idempotent o e -> idempotent o f -> (e < f <-> e = e + f /\ e = f + e).
      intros eo fo; intros.
      split.
      intro J1.
      generalize (instantiate_order H H0 J1); intro J2.
      elim J2; intro io; intros; clear J2.
      decompose [and] H3; clear H3.
        assert (K : eo = fo + eo).
          pattern eo at 1; rewrite H7.
          pattern fo at 1; rewrite <- H2.
          transitivity (fo + (fo + io)).
          unfold o; congruence.
          rewrite <- H7; auto.
          auto.
      split.
      generalize (pl2 H1 H2); intro K1.
      fold o in K1; rewrite K1.
      auto.
      auto.
      intro J1.
      decompose [and] J1.
      clear J1; clear H3.
      apply leq_intro.
      auto.
      auto.
      exists eo.
      split.
      auto.
      split.
      auto.
      auto.
      Save.
    Lemma order2 : forall x y z w : U, In U X x -> In U X y -> In U X z -> In U X w -> x < y -> z < w -> (x + z) < (y + w).
      unfold endo_op in end_o; unfold endo_fn in end_s.
      intros xo yo zo wo; intros.
      generalize (instantiate_order H H0 H3); intro J1; generalize (instantiate_order H1 H2 H4); intro J2; clear H3; clear H4.
      elim J1; intro eo; intros; elim J2; intro fo; intros; clear J1; clear J2.
      decompose [and] H3; decompose [and] H4; clear H3; clear H4.
      generalize (idempotent_wire H2 H5 H7); intro K1.
      decompose [and] K1; clear K1.
      elim H3; intro io; intros; clear H3; clear H4.
      decompose [and] H9; clear H9.
      apply leq_intro.
      unfold o, X; auto.
      unfold o, X; auto.
      exists (io + fo).
      split.
      unfold o, X; auto.
      split.
      apply prod_of_idem_is_idem.
      auto.
      auto.
      auto.
      auto.
      fold o.
      rewrite H8; rewrite H11.
      transitivity (yo + (eo + wo) + fo).
      unfold o, s; congruence.
      transitivity (yo + (wo + io) + fo).
      fold o in H13; rewrite H13; auto.
      unfold o, s; congruence.
      Save.
      Hint Resolve order1 order2.
    Lemma order3 : forall x y : U, In U X x -> In U X y -> x < y -> (x + s x) < (y + s y).
      unfold endo_op in end_o; unfold endo_fn in end_s.
      intros xo yo; intros.
      apply order2.
      auto.
      auto.
      unfold o, s, X; auto.
      unfold o, s, X; auto.
      auto.
      auto.
      Save.
      Hint Resolve order3.
End partial_order.

Section MSL_definitions.
(* Definition of a meet *)
  Variable U : Type.
  Variable X : Ensemble U.
  Definition meet (R : U -> U -> Prop) (z x y : U) :=
    In U X x -> In U X y -> In U X z -> R z x /\ R z y /\ forall w : U, In U X w -> R w x -> R w y -> R w z.
End MSL_definitions.

Section MSL_definitions2.
(* Definition of a meet semilattice *)
  Record MeetSL (U : Type) (X : Ensemble U) := mkmeet_sl
    {R : U -> U -> Prop;
     g : U -> U -> U;
     R_order : partial_order R X;
     g_endo : endo_op X g;
     g_glb : forall x y : U, meet X R (g x y) x y
    }.

(* Definition of the subset of idempotents of an inverse semigroup *)  
  Variable U : Type.
  Variable X : Ensemble U.
  Inductive Idems (S : inv_semigroup U) : Ensemble U :=
    idems_intro : forall x : U, In U (EX S) x -> idempotent (oh S) x -> In U (Idems S) x.

(* Definition of the relation *)
  Inductive leq2 (S : inv_semigroup U) : U -> U -> Prop :=
    leq2_intro : forall e f : U, In U (Idems S) e -> In U (Idems S) f -> e = (oh S e f) -> leq2 S e f.
End MSL_definitions2.

Section MSL_ideminvsemi_equivalence.
  Variable U : Type.
  Variable S : inv_semigroup U.
  Let X := EX S.
  Let o := oh S.
  Let s := es S.
  Let a := oh_assoc S.
  Let end_o := oh_endo.
  Let end_s := es_endo.
  Let ps1 := oh_pseudo1 S.
  Let ps2 := oh_pseudo2 S.
  Let pl1 := pseudo_law1.
  Let pl2 := pseudo_law2.
  Infix "+" := o.
  Infix "<" := (leq2 S).
  Hint Unfold o s a.
  Hint Resolve end_o end_s ps1 ps2 pl2.

  (* Instatiation rule for being in Idems (S) *)
  Lemma instantiate_idems : forall x : U, In U (Idems S) x -> (In U X x /\ idempotent o x).
    intro xo; intros.
    elim H; intros; clear H.
    auto.
    Save.
    Hint Resolve instantiate_idems.
  
  (* Instantiation rule for the relation *)
  Lemma instantiate_order2 : forall x y : U, In U (Idems S) x -> In U (Idems S) y -> x < y -> x = x + y.
    intros xo yo; intros.
    elim H1; intros; clear H1.
    auto.
    Save.
    Hint Resolve instantiate_order2.

  (* Now the construction : start with inverse semigroup S and turn Idems(S) into a meet semilattice.
     The relation is the one defined above and the operation of taking meets is the same as the operation from the semigroup. *)  
  Theorem IdemsS_is_a_MeetSL : MeetSL (Idems S).
    unfold endo_op in end_o; unfold endo_fn in end_s.
    apply mkmeet_sl with (leq2 S) (oh S).
    apply po_intro.
    unfold reflexive.
    intro xo; intro H.
    generalize (instantiate_idems H); intro.
    apply leq2_intro.
    auto.
    auto.
    decompose [and] H0; intros.
    auto.
    unfold antisymmetric.
    intros xo yo; intros.
    generalize (instantiate_order2 H H0 H1); generalize (instantiate_order2  H0 H H2); intros; clear H1; clear H2.
    generalize (instantiate_idems H); generalize (instantiate_idems H0); intros.
    decompose [and] H1; decompose [and] H2; clear H1; clear H2.
    generalize (pl2 H8 H6); intro.
    rewrite H4.
    pattern yo at 2; rewrite H3.
    auto.
    unfold transitive.
    intros xo yo zo; intros.
    generalize (instantiate_idems H); generalize (instantiate_idems H0); generalize (instantiate_idems H1); intros.
    decompose [and] H4; decompose [and] H5; decompose [and] H6; clear H4; clear H5; clear H6.
    generalize (instantiate_order2 H H0 H2); generalize (instantiate_order2 H0 H1 H3); intros; clear H2; clear H3.
    apply leq2_intro.
    auto.
    auto.
    fold o.
    pattern xo at 1; rewrite H5.
    rewrite H4.
    transitivity (xo + yo + zo).
    unfold o; congruence.
    rewrite <- H5.
    auto.
    unfold endo_op.
    intros xo yo; intros.
    decompose [and] H; clear H.
    generalize (instantiate_idems H0); generalize (instantiate_idems H1); intros.
    decompose [and] H; decompose [and] H2; clear H; clear H2.
    apply idems_intro.
    unfold o; auto.
    fold o.
    generalize (prod_of_idem_is_idem H5 H3 H6 H4); intro J.
    auto.
    unfold meet.
    intros xo yo; intros.
    fold o; fold o in H1.
    generalize (instantiate_idems H); generalize (instantiate_idems H0); intros.
    decompose [and] H2; decompose [and] H3; clear H2; clear H3.
    generalize (pl2 H7 H5); intro J; fold o in J.
    split.
    apply leq2_intro.
    auto.
    auto.
    fold o.
    pattern xo at 1; rewrite <- H7.
    transitivity (xo + (xo + yo)).
    unfold o; congruence.
    pattern (xo + yo) at 1; rewrite J.
    unfold o; congruence.
    split.
    apply leq2_intro.
    auto.
    auto.
    fold o.
    pattern yo at 1; rewrite <- H5.
    unfold o; congruence.
    intro wo; intros.
    generalize (instantiate_order2 H2 H H3); intro J1; generalize (instantiate_order2 H2 H0 H8); intro J2; clear H3; clear H8.
    apply leq2_intro.
    auto.
    auto.
    fold o.
    symmetry.
    transitivity (wo + xo + yo).
    unfold o; congruence.
    rewrite <- J1.
    rewrite <- J2.
    auto.
    Save.
    Hint Resolve IdemsS_is_a_MeetSL.
End MSL_ideminvsemi_equivalence.

(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)

(*** SECTION 3.4: Homomorphisms ***)

Section homo_definition.
  Variable U : Type.
  Record homo (S : inv_semigroup U) (T : inv_semigroup U) := mk_homomorphism
    {
      f : U -> U;
      dom_cod : forall x : U, In U (EX S) x -> In U (EX T) (f x);
      preservation : forall x y : U, In U (EX S) x -> In U (EX S) y -> f (oh S x y) = oh T (f x) (f y)
    }.
    (* Again due to the weirdness of functions acting on the whole universe U, we have to specify the domain and codomain of the homomorphism
       to be the respective underlying sets of the two inverse semigroups in question. *)
End homo_definition.

Section homo_properties.
  Variable U : Type.
  Variables S T : inv_semigroup U.
  Let X := EX S.
  Let o := oh S.
  Let s := es S.
  Let a := oh_assoc S.
  Let end_o := oh_endo.
  Let end_s := es_endo.
  Let ps1 := oh_pseudo1 S.
  Let ps2 := oh_pseudo2 S.
  Let pl1 := pseudo_law1.
  Let pl2 := pseudo_law2.
  Infix "+" := o.
  Infix "<" := (leq S).
  Hint Unfold X o s a.
  Hint Resolve end_o end_s ps1 ps2 pl1 pl2.
  Let Y := EX T.
  Let o' := oh T.
  Let s' := es T.
  Let a' := oh_assoc T.
  Let ps1' := oh_pseudo1 T.
  Let ps2' := oh_pseudo2 T.
  Infix "*" := o'.
  Infix "/" := (leq T).
  Hint Unfold Y o' s' a'.
  Hint Resolve ps1' ps2.
  Variable phi : homo S T.
  Let F := f phi.
  Let dc := dom_cod phi.
  Let pres := preservation phi.
  Hint Resolve dc pres.

  (* Proposition: If f: X -> Y is a homomorphism, then:
     (1) f preserves pseudoinverses
     (2) f preserves idempotents
     (3) f preserves the order relation *)
    Lemma homo_pres_inv : forall x : U, In U X x -> F (s x) = s' (F x).
      unfold endo_op in end_o; unfold endo_fn in end_s.
      intro xo; intros.
      apply pl1.
      fold o'; unfold ispseudo.
      split.
      transitivity (F (xo + s xo + xo)).
        assert (xo = xo + s xo + xo).
          auto.
      rewrite <- H0.
      auto.
      transitivity (F (xo + s xo) * F xo).
      apply pres.
      unfold o, s, X; auto.
      auto.
        assert (F (xo + s xo) = F xo * F (s xo)).
          apply pres.
          auto.
          unfold s, X; auto.
      rewrite H0; auto.
      transitivity (F (s xo + xo + s xo)).
        assert (s xo + xo + s xo = s xo).
          auto.
      rewrite H0.
      auto.
      transitivity (F (s xo + xo) * F (s xo)).
      apply pres.
      unfold o, s, X; auto.
      unfold s, X; auto.
        assert (F (s xo + xo) = F (s xo) * F (xo)).
          apply pres.
          unfold s, X; auto.
          auto.
      rewrite H0; auto.
      Save.
    Lemma homo_pres_idem : forall x : U, In U X x -> idempotent o x -> idempotent o' (F x).
      intro xo; intros.
      unfold idempotent.
      transitivity (F (xo + xo)).
      symmetry.
      apply pres.
      auto.
      auto.
      rewrite H0.
      auto.
      Save.
      Hint Resolve homo_pres_inv homo_pres_idem.
    Lemma homo_pres_order : forall x y : U, In U X x -> In U X y -> x < y -> (F x) / (F y).
      intros xo yo; intros.
      generalize (instantiate_order H H0 H1); intro; clear H1.
      elim H2; intro eo; intros.
      decompose [and] H1; clear H1.
      apply leq_intro.
      auto.
      auto.
      exists (F eo).
      split.
      auto.
      split.
      auto.
      fold o'; symmetry.
      transitivity (F (yo + eo)).
      symmetry; apply pres.
      auto.
      auto.
      fold o in H6; rewrite H6; auto.
      Save.
      Hint Resolve homo_pres_order.

  (* Proposition: if f: X -> Y is a homomorphism and f(x) is idempotent, then there is an idempotent e in X such that f(e)=f(x) *)
    Lemma homo_reflect_idem : forall x : U, In U X x -> idempotent o' (F x) -> (exists y : U, In U X y /\ idempotent o y /\ F y = F x).
      unfold endo_op in end_o; unfold endo_fn in end_s.
      intro xo; intros.
      exists (xo + s xo).
      split.
      unfold o, s, X; auto.
      split.
      generalize (prod_with_pseudo_is_idem H); intro H1.
      decompose [and] H1; clear H1.
      auto; clear H2; clear H3.
      transitivity (F xo * F (s xo)).
      apply pres.
      auto.
      unfold s; auto.
        assert (F (s xo) = s' (F xo)).
          auto.
      rewrite H1; clear H1.
        assert (F xo = s' (F xo)).
          apply idem_is_selfpseudo.
          auto.
          auto.
      rewrite <- H1; clear H1.
      auto.
      Save.
      Hint Resolve homo_reflect_idem.

  (* Proposition: if f(x1)<f(x2) then there is x0 in X such that x0<x2 and f(x0)=f(x1) *)
    Lemma homo_reflect_order : forall x y : U, In U X x -> In U X y -> F x / F y -> (exists z : U, z < y /\ F z = F x).
      unfold endo_op in end_o; unfold endo_fn in end_s.
      intros x1 x2; intros.
        assert (In U Y (F x1)).
          unfold Y; auto.
        assert (In U Y (F x2)).
          unfold Y; auto.
      generalize (instantiate_order H2 H3 H1); clear H1; intro J.
      elim J; intro f; intros; clear J.
      decompose [and] H1; clear H1.
      exists (x2 + s x1 + x1).
      split.
      apply leq_intro.
        assert (In U X (x2 + s x1)).
          unfold o, s, X; auto. 
      unfold o, s, X; auto.
      auto.
      exists (s x1 + x1).
      split.
      unfold o, s, X; auto.
      split.
      generalize (prod_with_pseudo_is_idem H); intro J; decompose [and] J; clear J.
      auto; clear H1; clear H5.
      unfold o, s; congruence.
        assert (x2 + s x1 + x1 = x2 + (s x1 + x1)).
          unfold o, s; congruence.
      rewrite H1.
      transitivity (F x2 * F(s x1 + x1)).
      apply pres.
      auto.
      unfold o, s; auto.
      transitivity (F x2 * F (s x1) * F x1).
        assert (F (s x1 + x1) = F (s x1) * F x1).
          apply pres.
          unfold s; auto.
          auto.
      rewrite H5.
      unfold o', s; congruence.
        assert (F (s x1) = s' (F x1)).
          auto.
      rewrite H5.
      fold o in H7; pattern (F x1) at 1; rewrite H7.
      pattern (F x1) at 1; rewrite H7; fold o'.
      generalize (inversion_symmetry H3 H4); intro K.
      fold o' s' in K; rewrite K.
      generalize (idem_is_selfpseudo H4 H6); intro K1.
      fold s' in K1; rewrite <- K1.
      transitivity (F x2 * (f * (s' (F x2) * F x2)) * f).
      unfold o', s'; congruence.
      generalize (prod_with_pseudo_is_idem H3); intro K2.
      decompose [and] K2; clear K2.
      fold o' s' in H9; clear H8.
      generalize (pl2 H6 H9); intro K2.
      fold o' in K2; rewrite K2.
      transitivity ((F x2 * s' (F x2) * F x2) * (f * f)).
      unfold o', s'; congruence.
      transitivity (F x2 * f).
        assert (F x2 * s' (F x2) * F x2 = F x2).
          auto.
      rewrite H8.
      fold o' in H6; rewrite H6.
      auto.
      auto.
      Save.
      Hint Resolve homo_reflect_order.
End homo_properties.