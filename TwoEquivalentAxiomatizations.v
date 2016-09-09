(*** SECTION 1: Two Equivalent Axiomatizations ***)

Set Implicit Arguments.
Unset Strict Implicit.

(* Preliminary definitions *)
Section Definitions.
  Variable X : Set.
  Variable op : X -> X -> X.
  Variable s : X -> X.
  Definition associative := forall x y z : X, op (op x y) z = op x (op y z).
  Definition pseudo1 := forall x : X, op (op x (s x)) x = x.
  Definition pseudo2 := forall x : X, op (op (s x) x) (s x) = s x.
  Definition ispseudo op (x y : X) := (x = op (op x y) x) /\ (y = op (op y x) y).
   (* The pseudoinversion is defined as a function s: X -> X, so this guarantees a "canonical" pseudoinverse for any element x.
      Thus, for pseudoinverses to be unique means that if any element y satisfies the property that it is pseudoinverse to x, then
      it must be this canonical pseudoinverse s(x). *)
  Definition pseudounique op s := forall x y : X, (ispseudo op x y) -> (y = s x).
  Definition commute (x y : X) := (op x y = op y x).
  Definition idempotent op (x : X) := op x x = x.
   (* Something strange here: the set implicit arguments / unset strict implicit commands at the beginning allow Coq to automatically infer
      some variables from context.  But for some reason, "commute" only works when the operation is not specified and "idempotent" only works
      when the operation -is- specified.  I'm not sure why this is so.  It was bothering me for a while, but then I remembered something Rick
      Blute told me - "if you worry about every little detail, you'll never get anywhere."  So let's not question it and just move on! *)
  Definition idems_commute := forall x y : X, (idempotent op x) /\ (idempotent op y) -> (commute x y).
End Definitions.

(* Defining a regular semigroup with Record; it depends on a set X, and comes equipped with a bunch of "stuff" - operations, axioms *)
Section Reg_Semigroup.
  Record reg_semigroup (X : Set) := mkreg_semigroup
    {oh: X -> X -> X;
     oh_assoc: associative oh;
     eh: X -> X;
     oh_pseudo1: pseudo1 oh eh; 
     oh_pseudo2: pseudo2 oh eh
    }.
    (* It is not necessary to specify the closure axiom; by construction, the operation takes two elements in X to an element in X. *)
End Reg_Semigroup.

(* Lemmas *)
Section Lemmas.
  Variable X : Set.
  Variable S : reg_semigroup X.
  Let o := oh S.
  Let e := eh S.
  Let a := oh_assoc.
  Let ps1 := oh_pseudo1.
  Let ps2 := oh_pseudo2.
  (* Giving shorter names to these things makes the proof take more steps in the sense that we need to fold/unfold definitions sometimes, 
     but makes it far more readable. *)

  (* Lemma 1: Every idempotent is pseudoinverse to itself *)
  Lemma idem_pseudoinv_itself : forall x : X, (idempotent o x) -> (ispseudo o x x).
    intros x H.
    unfold idempotent in H; unfold ispseudo.
    split.
    rewrite H; symmetry; assumption.
    rewrite H; symmetry; assumption.
    Save.

  (* Lemma 2: If e is a pseudoinverse of xy, then yex is idempotent *)
  Lemma yex_is_idem : forall x y : X, (idempotent o (o (o y (e (o x y))) x)).
    intros x y.
    unfold idempotent.
    transitivity (o (o y (o (o (e (o x y)) (o x y)) (e (o x y)))) x).
    Focus 2.
    unfold o, e; rewrite ps2; auto.
    unfold o, e; congruence.
    Save.
    (* The strategy for proving chains of equalities is to use "transitivity" to break the task up so that each step can be solved by a particular
       rewrite or application of lemma/axiom/hypothesis.  The "congruence" tactic lets Coq automatically try rewrites as necessary to solve the goal.
       Our use of "congruence" is mostly for (multiple) associativity rewrites.  Before discovering this tactic, these lines of proof looked something like
            "unfold o, e; rewrite a; rewrite a; rewrite a; rewrite a; rewrite a; auto",
       where I had to manually or by trial-and-error figure out how many times to move brackets and rewrite associativity.  This led to many hours of bleary-eyed 
       staring at my laptop screen in the basement of 585KED to prove essentially trivial steps! *)

  (* Lemma 3: If x, y are idempotent, then xy has an idempotent inverse *)
  Lemma product_of_idems_has_ideminv : forall x y : X, (idempotent o x) /\ (idempotent o y) -> {z : X | (idempotent o z) /\ (ispseudo o (o x y) z)}.
    intros x y H.
    unfold idempotent in H.
    decompose [and] H.
    exists (o (o y (e (o x y))) x); split.
    apply yex_is_idem.
    unfold ispseudo; split.
    transitivity (o (o (o x y) (e (o x y))) (o x y)).
    unfold o, e; rewrite ps1; auto.
    transitivity (o (o (o x (o y y)) (e (o x y))) (o (o x x) y)).
    rewrite H0; rewrite H1; auto.
    unfold o, e; congruence.
    transitivity (o (o (o y (e (o x y))) x) (o (o y (e (o x y))) x)).
    symmetry.
    fold (idempotent o ((o (o y (e (o x y))) x))); apply yex_is_idem; auto.
    transitivity (o (o (o y (e (o x y))) (o x x)) (o (o (o y y) (e (o x y))) x)).
    rewrite H0; rewrite H1; auto.
    unfold o, e; congruence.
    Save.
End Lemmas.

(* The theorem: in a regular semigroup S, the following are equivalent:
   (1) idempotents commute
   (2) pseudoinverses are unique
   When these conditions are satisfied, S is called an inverse semigroup. *)
Section Theorem_Inv_Semigroup.
  Variable X : Set.
  Variable S : reg_semigroup X.
  Let o := oh S.
  Let e := eh S.
  Let a := oh_assoc.
  Let ps1 := oh_pseudo1.
  Let ps2 := oh_pseudo2.
  (* Obvious fact that we need to prove explictly anyway: if x, y are pseudoinverse to each other, then y, x are pseudoinverse to each other.
     This is because "ispseudo o x y" is a conjunct of two propositions and is not technically the same thing as "ispseudo o y x". *)
  Goal forall x y : X, (ispseudo o x y) -> (ispseudo o y x).
    unfold ispseudo; intros x y H.
    inversion H as [H1 H2]; split; assumption; assumption.
    Save pseudo_sym.
  (* The main theorem *)
  (* We begin using the "assert" command here.  This allows us to prove a subgoal within a proof that we will need for the main goal.
     This is nice because sometimes the subgoals aren't important enough to be their own lemma, or they depend on the hypothesis of the main goal. *)
  Theorem Inv_Semigroup_Equiv_Formulations : idems_commute o <-> pseudounique o e.
    split.
    (* (1) implies (2) *)
        assert (x_invx_is_idem_1 : forall x y : X, (ispseudo o x y) -> (idempotent o (o x y)) /\ (idempotent o (o y x))).
          intros x y H.
          split.
          unfold ispseudo in H; unfold idempotent.
          decompose [and] H.
          transitivity (o (o (o x y) x) y).
          unfold o, e; congruence.
          rewrite <- H0; auto.
          unfold ispseudo in H; unfold idempotent.
          decompose [and] H.
          transitivity (o (o (o y x) y) x).
          unfold o, e; congruence.
          rewrite <- H1; auto.
        assert (pseudo_is_pseudo : forall x : X, (ispseudo o x (e x))).
          intro x.
          unfold ispseudo; split.
          unfold o, e; rewrite ps1; auto.
          unfold o, e; rewrite ps2; auto.
        assert (x_invx_is_idem_2 : forall x : X, (idempotent o (o x (e x))) /\ (idempotent o (o (e x) x))).
        intro x.
        apply x_invx_is_idem_1.
        apply pseudo_is_pseudo.
      intros H x y H1.
      unfold idems_commute in H; unfold ispseudo in H1; inversion H1 as [J1 J2].
      generalize (x_invx_is_idem_1 x y H1); intro idems1.
      generalize (x_invx_is_idem_2 x); intro idems2.
      inversion idems1 as [idems1a idems1b]; inversion idems2 as [idems2a idems2b].
      generalize (conj idems1a idems2a); intro idemz1.
      generalize (conj idems1b idems2b); intro idemz2.
      generalize (H (o x y) (o x (e x)) idemz1); intro comm1.
      generalize (H (o y x) (o (e x) x) idemz2); intro comm2.
      unfold commute in comm1; unfold commute in comm2.
      transitivity (o (o y x) y).
      rewrite <- J2; auto.
      transitivity (o y (o x y)).
      unfold o; rewrite <- a; auto.
      transitivity (o y (o (o x y) (o x y))).
      unfold idempotent in idems1a; rewrite idems1a; auto.
      transitivity (o (o y (o (o x y) x)) y).
      unfold o; congruence.
      transitivity (o (o y (o (o x (e x)) x)) y).
      rewrite <- J1; unfold o; rewrite ps1; auto.
      transitivity (o y (o (o x (e x)) (o x y))).
      unfold o; congruence.
      transitivity (o y (o (o x y) (o x (e x)))).
      rewrite comm1; auto.
      transitivity (o (o y (o (o x y) x)) (e x)).
      unfold o; congruence.
      transitivity (o (o y (o (o x (e x)) x)) (e x)).
      rewrite <- J1; unfold o; rewrite ps1; auto.
      transitivity (o (o (o y x) (o (e x) x)) (e x)).
      unfold o, e; congruence.
      transitivity (o (o (o (e x) x) (o y x)) (e x)).
      rewrite comm2; auto.
      transitivity (o (o (e x) (o (o x y) x)) (e x)).
      unfold o, e; congruence.
      transitivity (o (o (e x) (o (o x (e x)) x)) (e x)).
      rewrite <- J1; unfold o; rewrite ps1; auto.
      transitivity (o (o (o (o (e x) x) (e x)) x) (e x)).
      unfold o, e; congruence.
      unfold o, e; rewrite ps2; rewrite ps2; auto.
    (* (2) implies (1) *)
      unfold pseudounique; unfold idems_commute; intros H x y H1.
      generalize (product_of_idems_has_ideminv H1); intro z.
      destruct z as [w H2]; inversion H2 as [H2a H2b].
      fold o in H2; fold o in H2a; fold o in H2b.
      generalize (idem_pseudoinv_itself H2a); intro H3; fold o in H3.
      generalize (pseudo_sym H2b); intro H2c.
      generalize (H w (o x y) H2c); intro H4.
      generalize (H w w H3); intro H5.
      unfold commute; transitivity (e w).
      exact H4.
      transitivity w.
      symmetry; exact H5.
        assert (idem_xy : idempotent o (o x y)).
          rewrite H4; rewrite <- H5.
          assumption.
      inversion H1 as [H1a H1b]; generalize (conj H1b H1a); intro H1s.
      generalize (product_of_idems_has_ideminv H1s); intro z1.
      destruct z1 as [w1 H2s]; inversion H2s as [H2sa H2sb].
      fold o in H2s; fold o in H2sa; fold o in H2sb.
      generalize (idem_pseudoinv_itself H2sa); intro H3s; fold o in H3s.
      generalize (pseudo_sym H2sb); intro H2sc.
      generalize (H w1 (o y x) H2sc); intro H4s.
      generalize (H w1 w1 H3s); intro H5s.
        assert (idem_yx : idempotent o (o y x)).
          rewrite H4s; rewrite <- H5s.
          assumption.
        assert (xy_pseudoinv_self : ispseudo o (o x y) (o x y)).
          rewrite H5 in H2b; rewrite <- H4 in H2b; assumption.
        assert (yx_pseudoinv_self : ispseudo o (o y x) (o y x)).
          rewrite H5s in H2sb; rewrite <- H4s in H2sb; assumption.
        assert (tridempotent_xy : o(o(o x y)(o x y))(o x y) = o x y).
          unfold ispseudo in xy_pseudoinv_self; inversion xy_pseudoinv_self as [xy_pseudoinv_self1 xypseudoinv_self2].
          symmetry; assumption.
        assert (tridempotent_yx : o(o(o y x)(o y x))(o y x) = o y x).
          unfold ispseudo in yx_pseudoinv_self; inversion yx_pseudoinv_self as [yx_pseudoinv_self1 yxpseudoinv_self2].
          symmetry; assumption.
        assert (yx_inv_xy : ispseudo o (o y x) (o x y)).
          unfold ispseudo; split; symmetry.
          transitivity (o (o (o y x) (o (o x y)(o x y))) (o y x)).
          unfold idempotent in idem_xy; rewrite idem_xy; auto.
          transitivity (o (o (o y (o x x)) (o y x)) (o (o y y) x)).
          unfold o; congruence.
          transitivity (o (o (o y x) (o y x)) (o y x)).
          unfold idempotent in H1a; unfold idempotent in H1b; rewrite H1a; rewrite H1b; auto.
          rewrite tridempotent_yx; auto.
          transitivity (o (o (o x y) (o (o y x)(o y x))) (o x y)).
          unfold idempotent in idem_yx; rewrite idem_yx; auto.
          transitivity (o (o (o x (o y y )) (o x y)) (o (o x x) y)).
          unfold o; congruence. 
          transitivity (o (o (o x y) (o x y)) (o x y)).
          rewrite H1a; rewrite H1b; auto.
          rewrite tridempotent_xy; auto.
      generalize (pseudo_sym yx_inv_xy); intro xy_inv_yx.
      generalize (H (o x y) (o y x) xy_inv_yx); intro H6.
      rewrite H6.
      rewrite H4.
      rewrite <- H5; rewrite <- H5; auto.
    Save.
End Theorem_Inv_Semigroup.