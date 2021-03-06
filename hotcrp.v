Require Import Bool Arith List Omega String.
Require Import Recdef.
Require Import Program.Tactics.
Import ListNotations.


(*  Overall architecture:
     *)

Module HotCRP.
  (********************************************************)
  (* The spec *)
  (********************************************************)

  Inductive user : Set :=
  | User: forall (id:nat) (email:string) (team: nat), user.
  Hint Constructors user.

  Inductive paper : Set :=
  | Paper: forall (id:nat) (title:string)
            (team:nat) (decision:nat), paper.
  Hint Constructors paper.

  (*(* Currently not needed *)
  Lemma paper_dec : forall p1 p2 : paper, {p1 = p2} + {p1 <> p2}.
  Proof.
    intros; induction p1, p2.
    destruct (eq_nat_dec id id0), (eq_nat_dec team team0),
      (eq_nat_dec  decision decision0).
    1: admit.
    all: right; subst. (* Don't know what to do here... *)
  Admitted.*)

  Notation database := (list paper).

  Section SQL.
    (*  Queries are of the form SELECT * FROM PAPERS WHERE e
        Here, we define the possible options for e
        e = [True | False | Paper.Field = x | e /\ e | e \/ e | -e]
        For Paper.Field = x, for now, we just list out the properties
        of a paper.

        To use this, we will generate a filter function from a query,
        and apply it to a list of papers. *)

    Inductive paper_field : Set:=
    | Paper_id: nat -> paper_field
    | Paper_title: string -> paper_field
    | Paper_team: nat -> paper_field
    | Paper_decision: nat -> paper_field.


    Inductive sql_query : Set :=
    | Sql_true: sql_query
    | Sql_false: sql_query
    | Field_eq: paper_field -> sql_query
    | Field_neq: paper_field -> sql_query
    | And: sql_query -> sql_query -> sql_query
    | Or: sql_query -> sql_query -> sql_query.

    Fixpoint beq_field (field : paper_field) (p : paper) :=
      match p with
      | Paper p_id p_title p_team p_decision =>
         match field with
          | Paper_id i => beq_nat p_id i
          | Paper_title t => if string_dec p_title t then true else false
          | Paper_team t => beq_nat p_team t
          | Paper_decision d => beq_nat p_decision d
        end
      end.

    (*  Now define a computational version. *)
    Fixpoint sql_query_func (q:sql_query) (p:paper) : bool :=
      match q with
        | Sql_true => true
        | Sql_false => false
        | Field_eq field => beq_field field p
        | Field_neq field => negb (beq_field field p)
        | And q1 q2 => andb (sql_query_func q1 p) (sql_query_func q2 p)
        | Or q1 q2 => orb (sql_query_func q1 p) (sql_query_func q2 p)
      end.

    (* Some baby test cases. *)
    Definition empty_paper := (Paper 0 "" 0 0).
    Eval compute in sql_query_func (Sql_true) empty_paper.
    Eval compute in sql_query_func (Sql_false) empty_paper.
    Eval compute in sql_query_func (Field_eq (Paper_id 10)) empty_paper.
    Definition paper10 := (Paper 10 "paper_10" 10 0).
    Eval compute in sql_query_func (Field_eq (Paper_id 10)) paper10.
    Eval compute in sql_query_func (Field_eq (Paper_title "paper_10")) paper10.
    Definition paper10query := (And (Field_eq (Paper_id 10)) (Field_eq (Paper_team 10))).
    Eval compute in sql_query_func paper10query empty_paper.
    Eval compute in sql_query_func paper10query paper10.

    Definition sql_query_filter (q:sql_query) db : database :=
      filter (fun p => sql_query_func q p) db.

    (* Some test cases. *)
    Definition testdb := [(Paper 0 "0" 0 0);(Paper 1 "hi" 0 0);(Paper 2 "yo" 0 1);
                          (Paper 3 "naw" 2 0);(Paper 4 "P=NP" 2 1);
                          (Paper 6 "hotcrp" 3 2)].
    Definition team0query := (Field_eq (Paper_team 0)).
    Definition team2query := (Field_eq (Paper_team 2)).
    Definition decision1queryeq := (Field_eq (Paper_decision 1)).
    Definition decision1queryneq := (Field_neq (Paper_decision 1)).
    Eval compute in sql_query_filter team0query testdb.
    Eval compute in sql_query_filter team2query testdb.
    Eval compute in sql_query_filter decision1queryeq testdb.
    Eval compute in sql_query_filter (And (decision1queryneq) team2query) testdb.
    Eval compute in sql_query_filter (Or (decision1queryneq) team0query) testdb.
  End SQL.

  Notation user_query := sql_query.


  (********************************************************)
  (* Policies *)
  (********************************************************)
  Section SimplePolicy.
    (* Scrub out the decision and put 0 in *)
    Fixpoint simple_policy_map (p:paper) (u:user) : paper :=
    match u with
    | User _ _ u_team => 
      match p with
      | Paper p_id p_title p_team p_decision =>
        if Nat.eqb p_team u_team then Paper p_id p_title p_team 0 else p
      end
    end.

    Definition simple_policy_scrub u db : database :=
      map (fun p => simple_policy_map p u) db.

    Definition team0user := (User 0 "dan@dan" 0).
    Definition team2user := (User 1 "richard@richard" 2).
    Eval compute in simple_policy_scrub team0user testdb.
    Eval compute in simple_policy_scrub team2user testdb.
  End SimplePolicy.


  (********************************************************)
  (* Optimizations *)
  (********************************************************)
  Section SimpleOptimization.
    (* A simple optimization for simple_policy_map:
    Move the entire user query into SQL, and replace any instance of
    (paper.decision = x) with
    if x = 0 then (paper.team = u.team) || (paper.decision = x)
    else (paper.decision = x) && (Team != u.team),
    and replace any instance of
    (paper.decision != x) with
    if x = 0 then (paper.decision != x) && (paper.team != u.team)
    else (paper.team = u.team) || (paper.decision != x) *)
    Fixpoint simple_optimization (uq:user_query) (u:user) :
      (user_query * sql_query) :=
      match u with
      | User _ _ team =>
        match uq with
        | Field_eq (Paper_decision x) =>
            (Sql_true,
            if (Nat.eqb x 0) then
            Or (Field_eq (Paper_team team)) uq else
            And uq (Field_neq (Paper_team team)))
        | Field_neq (Paper_decision x) =>
            (Sql_true,
            if (Nat.eqb x 0) then
            And uq (Field_neq (Paper_team team)) else
            Or (Field_eq (Paper_team team)) uq)
        | And q1 q2 =>
            (Sql_true,
            And (snd (simple_optimization q1 u)) (snd (simple_optimization q2 u)))
        | Or q1 q2 =>
            (Sql_true,
            Or (snd (simple_optimization q1 u)) (snd (simple_optimization q2 u)))
        | _ => (Sql_true, uq)
        end
      end.

    Definition decision0 := (Field_eq (Paper_decision 0)).
    Definition testuser := (User 1 "dan@dan" 1).
    Definition complexquery := (Or Sql_false
      (And decision0 (Field_eq (Paper_team 1)))).
    Eval compute in simple_optimization decision0 testuser.
    Eval compute in simple_optimization complexquery testuser.

    Lemma true_filter :
      forall db, (filter (fun _ : paper => true) db) = db.
    Proof.
      intros; induction db; auto.
      unfold filter in *; rewrite IHdb; auto.
    Qed.

    Lemma false_filter :
      forall db, (filter (fun _ : paper => false) db) = [].
    Proof.
      intros; induction db; auto.
    Qed.

    Lemma beq_nat_sym (x y : nat):
      (x =? y) = (y =? x).
    Proof.
      destruct (Sumbool.sumbool_of_bool (x =? y)).
      rewrite beq_nat_true_iff in e.
      rewrite e.
      auto.
      apply beq_nat_false in e.
      assert (y <> x) by auto.
      rewrite <- beq_nat_false_iff in *.
      rewrite e, H.
      auto.
    Qed.

    Lemma help (uq:user_query) (u:user) (p:paper):
      sql_query_func uq (simple_policy_map p u) = true ->
        sql_query_func (snd (simple_optimization uq u)) p = true.
    Proof.
      intros.
      unfold simple_policy_map in H.
      destruct p, u.
      induction uq;
      simpl in *;auto.
      (* Field_eq cases *)
      destruct p.
      (* paper id *)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (team =? team0 = false) by (now apply Nat.eqb_neq).
      rewrite H0 in *.
      auto.
      (* Paper title*)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (team =? team0 = false) by (now apply Nat.eqb_neq).
      rewrite H0 in *.
      auto.
      (* Paper team *)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (team =? team0 = false) by (now apply Nat.eqb_neq).
      rewrite H0 in *.
      auto.
      (* Paper decision *)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      pose (beq_nat_sym 0 n).
      rewrite <- e0.
      rewrite H.
      simpl.
      rewrite orb_true_iff.
      rewrite <- beq_nat_refl.
      auto.
      rewrite <- beq_nat_false_iff in n0.
      destruct (Nat.eq_dec n 0).
      rewrite n0 in H.
      rewrite e in *.
      simpl.
      rewrite orb_true_iff.
      auto.
      rewrite <- beq_nat_false_iff in n1.
      rewrite n0 in *.
      rewrite n1.
      simpl.
      rewrite andb_true_iff.
      rewrite negb_true_iff.
      auto.
      (* Field_neq cases *)
      destruct p.
      (* paper id *)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      now auto.
      assert (team =? team0 = false) by (now apply Nat.eqb_neq).
      rewrite H0 in *.
      now auto.
      (* Paper title*)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      now auto.
      assert (team =? team0 = false) by (now apply Nat.eqb_neq).
      rewrite H0 in *.
      now auto.
      (* Paper team *)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (team =? team0 = false) by (now apply Nat.eqb_neq).
      rewrite H0 in *.
      now auto.
      (* Paper decision *)
      simpl in *.
      destruct (Nat.eq_dec team team0).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      pose (beq_nat_sym 0 n).
      rewrite <- e0.
      rewrite negb_true_iff in H.
      rewrite H.
      simpl.
      rewrite orb_true_iff.
      rewrite <- beq_nat_refl.
      now auto.
      rewrite <- beq_nat_false_iff in n0.
      destruct (Nat.eq_dec n 0).
      rewrite n0 in H.
      rewrite e in *.
      simpl.
      rewrite andb_true_iff.
      rewrite <- negb_true_iff in n0.
      now auto.
      rewrite <- beq_nat_false_iff in n1.
      rewrite n0 in *.
      rewrite n1.
      simpl.
      rewrite <- negb_true_iff in n0.
      rewrite orb_true_iff.
      now auto.
      rewrite andb_true_iff in *.
      destruct_pairs.
      firstorder.
      rewrite orb_true_iff in *.
      destruct H.
      firstorder.
      firstorder.
    Qed.

    Lemma simple_optimization_and (uq1:user_query) (uq2:user_query)
      (u:user) (db:database) (p:paper):
      In p (simple_policy_scrub u db) ->
      sql_query_func (And uq1 uq2) p = true ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq1 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq2 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization (And uq1 uq2) u)) db)).
    Proof.
      intros; destruct p, u.
      cbn.
      unfold sql_query_filter in *; cbn in *.
      unfold simple_policy_scrub in *; cbn in *.
      apply in_map_iff.
      apply in_map_iff in H1; destruct H1; destruct_conjs.
      exists x; split; auto.
      apply filter_In in H3; destruct_conjs.
      apply filter_In; split; auto.
      apply andb_true_iff; split; auto.
      apply andb_true_iff in H0; destruct_conjs.
      induction uq2; cbn; auto.
      - destruct x; cbn in *.
        destruct (Nat.eq_dec team1 team0).
      --  rewrite e in *; rewrite <- beq_nat_refl in *.
          inversion H1; subst; induction p; cbn in *; auto.
      --- destruct (Nat.eq_dec n 0).
          rewrite e in *; cbn in *; rewrite <- beq_nat_refl in *; auto.
          induction n; try omega; discriminate.
      --  rewrite <- Nat.eqb_neq in n; rewrite n in H1; inversion H1; subst.
          induction p; cbn in *; auto.
          apply in_map_iff in H2; destruct H2; destruct_conjs; destruct x.
          unfold simple_policy_map in H2.
          destruct (Nat.eq_dec team1 team0).
      --- subst. rewrite <- beq_nat_refl in H2. inversion H2; subst.
          rewrite <- beq_nat_refl in n. discriminate.
      --- rewrite <- Nat.eqb_neq in n1; rewrite n1 in H2; inversion H2;
          subst; apply filter_In in H6; destruct_conjs; auto.
      - destruct x; cbn in *.
        destruct (Nat.eq_dec team1 team0).
      --  rewrite e in *; rewrite <- beq_nat_refl in *.
          inversion H1; subst; induction p; cbn in *; auto.
      --- destruct (Nat.eq_dec n 0).
          rewrite e in *; cbn in *; rewrite <- beq_nat_refl in *; auto.
          induction n; try omega; discriminate.
          rewrite <- Nat.eqb_neq in n0; rewrite n0.
          unfold sql_query_func; cbn. rewrite <- beq_nat_refl; auto.
      --  rewrite <- Nat.eqb_neq in n; rewrite n in H1; inversion H1; subst.
          induction p; cbn in *; auto.
          apply in_map_iff in H2; destruct H2; destruct_conjs; destruct x.
          unfold simple_policy_map in H2.
          destruct (Nat.eq_dec team1 team0).
      --- subst. rewrite <- beq_nat_refl in H2. inversion H2; subst.
          rewrite <- beq_nat_refl in n. discriminate.
      --- rewrite <- Nat.eqb_neq in n1; rewrite n1 in H2; inversion H2;
          subst; apply filter_In in H6; destruct_conjs; auto.
      - unfold sql_query_func in H5; apply andb_true_iff in H5;
        destruct_conjs. fold sql_query_func in H5; fold sql_query_func in H6.
        apply andb_true_iff; split; [ apply IHuq2_1 | apply IHuq2_2 ]; auto.
      --
          clear IHuq2_1 IHuq2_2.
          rewrite in_map_iff in *.
          destruct H2.
          exists x0.
          firstorder.
          rewrite filter_In in *.
          firstorder.
          simpl in H9.
          rewrite andb_true_iff in H9.
          firstorder.
      --
          clear IHuq2_1 IHuq2_2.
          rewrite in_map_iff in *.
          destruct H2.
          exists x0.
          firstorder.
          rewrite filter_In in *.
          firstorder.
          simpl in H9.
          rewrite andb_true_iff in H9.
          firstorder.
      -
        simpl in *.
        rewrite orb_true_iff in *.
        rewrite in_map_iff in *.
        destruct H2.
        destruct_pairs.
        destruct H5.
        pose (IHuq2_1 H5).
        firstorder.
        simpl in *.
        specialize (H8 x1).
        assert (In x1
       (filter
          (fun p : paper =>
           sql_query_func
             (snd (simple_optimization uq2_1 (User id0 email team0))) p) db)).
        rewrite filter_In.
        split;auto.
        rewrite <- H in H5.
        pose (help _ _ _ H5).
        (* Induction? *)
        now auto.
        auto.
        pose (IHuq2_2 H5).
        firstorder.
        simpl in *.
        specialize (H8 x1).
        assert (In x1
       (filter
          (fun p : paper =>
           sql_query_func
             (snd (simple_optimization uq2_2 (User id0 email team0))) p) db)).
        rewrite filter_In.
        split;auto.
        rewrite <- H in H5.
        (* Induction? *)
        pose (help _ _ _ H5).
        now auto.
        auto.
    Qed.

    Lemma simple_optimization_or_left (uq1:user_query) (uq2:user_query)
      (u:user) (db:database) (p:paper):
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq1 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization (Or uq1 uq2) u)) db)).
    Proof.
      intros. unfold simple_policy_scrub in *; unfold simple_policy_map in *;
      apply in_map_iff in H; destruct_conjs.
      apply in_map_iff; exists H; split; auto; clear H0;
      unfold sql_query_filter in *; unfold sql_query_func in *.
      apply filter_In in H1; destruct_conjs.
      apply filter_In; split; auto; destruct u;
      unfold simple_optimization in *; unfold snd in *.
      apply orb_true_iff; left; auto.
    Qed.

    Lemma simple_optimization_or_right (uq1:user_query) (uq2:user_query)
      (u:user) (db:database) (p:paper):
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq2 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization (Or uq1 uq2) u)) db)).
    Proof.
      intros. unfold simple_policy_scrub in *; unfold simple_policy_map in *;
      apply in_map_iff in H; destruct_conjs.
      apply in_map_iff; exists H; split; auto; clear H0;
      unfold sql_query_filter in *; unfold sql_query_func in *.
      apply filter_In in H1; destruct_conjs.
      apply filter_In; split; auto; destruct u;
      unfold simple_optimization in *; unfold snd in *.
      apply orb_true_iff; right; auto.
    Qed.

    (* One direction of our proof: nothing is lost by our optimization. *)
    Lemma simple_optimization_no_loss :
      forall uq u db p,
      In p (sql_query_filter uq (simple_policy_scrub u db)) ->
      In p (sql_query_filter (fst (simple_optimization uq u))
        (simple_policy_scrub u (sql_query_filter (snd (simple_optimization uq u)) db)
      )).
    Proof.
      unfold sql_query_filter; intros; rewrite filter_In in *; destruct u;
      split; destruct_conjs.
      - induction uq.
      --  unfold simple_optimization; simpl; try rewrite true_filter; auto.
      --  unfold sql_query_func in H0; discriminate.
      --  (* Field_eq case *)
          unfold simple_policy_scrub in *; unfold simple_policy_map in *.
          rewrite in_map_iff in H; destruct_conjs. destruct H.
          destruct (Nat.eq_dec team0 team).
      --- rewrite e in *. rewrite <- beq_nat_refl in H1;
          destruct p0; unfold simple_optimization; unfold snd; auto;
          apply in_map_iff.
          1, 2, 3: exists (Paper id0 title team decision);
          rewrite <- beq_nat_refl; split; auto; apply filter_In; split;
          auto; rewrite <- H1 in H0;
          unfold sql_query_func in *; unfold beq_field in *; auto.
          destruct (Nat.eq_dec n 0).
      ----  exists (Paper id0 title team decision);
            rewrite <- beq_nat_refl; split; auto; apply filter_In; split;
            auto; rewrite <- e; auto;
            rewrite e0; rewrite <- beq_nat_refl;
            unfold sql_query_func in *; unfold beq_field in *;
            rewrite e; rewrite <- beq_nat_refl; auto.
      ----  unfold sql_query_func in H0; unfold beq_field in H0;
            rewrite <- H1 in H0; apply beq_nat_true in H0; rewrite H0 in *;
            omega.
      --- assert (team0 =? team = false) by now apply Nat.eqb_neq.
          rewrite H in H1; apply in_map_iff; exists p; split.
          rewrite <- H1; rewrite H; auto.
          apply filter_In; split; rewrite <- H1; auto;
          destruct p0; rewrite H1; unfold simple_optimization;
          unfold snd; auto;
          unfold sql_query_func in H0; unfold beq_field in H0;
          rewrite <- H1 in H0.
          destruct (Nat.eq_dec n0 0).
      ----  rewrite e; simpl; rewrite <- H1; rewrite e in *;
            rewrite H0; rewrite H; auto.
      ----  rewrite <- Nat.eqb_neq in n1; rewrite n1;
            unfold sql_query_func in *; unfold beq_field in *;
            rewrite <- H1 in *; rewrite H0; rewrite H; auto.
      --  (* Field_neq case *)
          unfold simple_policy_scrub in *; unfold simple_policy_map in *.
          rewrite in_map_iff in H; destruct_conjs. destruct H.
          destruct (Nat.eq_dec team0 team).
      --- rewrite e in *. rewrite <- beq_nat_refl in H1;
          destruct p0; unfold simple_optimization; unfold snd; auto;
          apply in_map_iff.
          1, 2, 3: exists (Paper id0 title team decision);
          rewrite <- beq_nat_refl; split; auto; apply filter_In; split;
          auto; rewrite <- H1 in H0;
          unfold sql_query_func in *; unfold beq_field in *; auto.
          destruct (Nat.eq_dec n 0).
      ----  unfold sql_query_func in *; unfold beq_field in *;
            rewrite <- H1 in *; rewrite e0 in *; rewrite <- beq_nat_refl in *;
            simpl in *; discriminate.
      ----  exists (Paper id0 title team decision);
            rewrite <- beq_nat_refl; split; auto; apply filter_In; split;
            auto; rewrite <- Nat.eqb_neq in n0; rewrite n0;
            unfold sql_query_func in *; unfold beq_field in *;
            rewrite <- beq_nat_refl; auto.
      --- assert (team0 =? team = false) by now apply Nat.eqb_neq.
          rewrite H in H1; apply in_map_iff; exists p; split.
          rewrite <- H1; rewrite H; auto.
          apply filter_In; split; rewrite <- H1; auto;
          destruct p0; rewrite H1; unfold simple_optimization;
          unfold snd; auto;
          unfold sql_query_func in H0; unfold beq_field in H0;
          rewrite <- H1 in H0.
          destruct (Nat.eq_dec n0 0).
      ----  rewrite e; simpl; rewrite <- H1; rewrite e in *;
            rewrite H0; rewrite H; auto.
      ----  rewrite <- Nat.eqb_neq in n1; rewrite n1;
            unfold sql_query_func in *; unfold beq_field in *;
            rewrite <- H1 in *; rewrite H0; rewrite H; auto.
      --  apply simple_optimization_and with (uq1:=uq1) (uq2:=uq2)
          (u:=(User id email team)) (db:=db) (p:=p); auto.
          assert (sql_query_func uq1 p = true). unfold sql_query_func in *.
          apply andb_true_iff in H0; destruct_conjs; auto.
          apply IHuq1; auto.
          assert (sql_query_func uq2 p = true). unfold sql_query_func in *.
          apply andb_true_iff in H0; destruct_conjs; auto.
          apply IHuq2; auto.
      --  unfold sql_query_func in H0. apply orb_true_iff in H0.
          induction H0.
      --- assert (sql_query_func uq1 p = true); auto.
          apply simple_optimization_or_left with (uq1:=uq1) (uq2:=uq2)
          (u:=(User id email team)) (db:=db) (p:=p).
          apply IHuq1; auto.
      --- assert (sql_query_func uq2 p = true); auto.
          apply simple_optimization_or_right with (uq1:=uq1) (uq2:=uq2)
          (u:=(User id email team)) (db:=db) (p:=p).
          apply IHuq2; auto.
      - destruct uq; auto; destruct p0; simpl; auto.
    Qed.

    Lemma fst_opt_always_true (q : user_query) (u : user) (p : paper):
    (sql_query_func (fst (simple_optimization q u)) p) = true.
    Proof.
      destruct p.
      destruct u.
      induction q;simpl;auto.
      destruct p;simpl;auto.
      destruct p;simpl;auto.
    Qed.

    (* Other direction of our proof: the optimization doesn't give us
    anything extra *)
    Lemma simple_optimization_no_extra :
      forall uq u db p,
      In p (sql_query_filter (fst (simple_optimization uq u))
        (simple_policy_scrub u (sql_query_filter (snd (simple_optimization uq u)) db)
      )) ->
      In p (sql_query_filter uq (simple_policy_scrub u db)).
    Proof.
      Proof.
      intros.
      destruct u.
      induction uq;
      unfold sql_query_filter in *;
      rewrite filter_In in *;
      destruct_pairs;
      simpl in *.
      rewrite true_filter in H.
      auto.
      rewrite false_filter in H.
      firstorder.
      (* handle the Field_eq cases *)
      destruct p0; unfold simple_optimization; simpl in *;
      unfold simple_policy_scrub in *;
      rewrite in_map_iff in *.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      subst.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
      subst.
      rewrite <- beq_nat_false_iff in n0.
      rewrite n0.
      auto.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      subst.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
      subst.
      rewrite <- beq_nat_false_iff in n.
      rewrite n.
      auto.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      subst.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
      subst.
      rewrite <- beq_nat_false_iff in n0.
      rewrite n0.
      auto.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec n 0).
      subst.
      rewrite <- beq_nat_refl in *.
      simpl in H2.
      rewrite orb_true_iff in H2.
      destruct H2.
      assert (team0 = team) by (now apply Nat.eqb_eq).
      rewrite H2.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (decision = 0) by (now apply Nat.eqb_eq).
      rewrite H2.
      destruct (Nat.eq_dec team0 team).
      rewrite e.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (team0 =? team = false) by now apply Nat.eqb_neq.
      rewrite H3.
      rewrite <- beq_nat_refl in *.
      auto.
      assert (n =? 0 = false) by now apply Nat.eqb_neq.
      rewrite H3 in *.
      subst.
      simpl in H2.
      rewrite andb_true_iff in H2.
      destruct_pairs.
      rewrite negb_true_iff in H2.
      rewrite H2.
      auto.
      (* neq cases *)
      destruct p0; unfold simple_optimization; simpl in *;
      unfold simple_policy_scrub in *;
      rewrite in_map_iff in *.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      subst.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
      subst.
      rewrite <- beq_nat_false_iff in n0.
      rewrite n0.
      auto.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      subst.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
      subst.
      rewrite <- beq_nat_false_iff in n.
      rewrite n.
      auto.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      subst.
      simpl.
      rewrite <- beq_nat_refl.
      auto.
      subst.
      rewrite <- beq_nat_false_iff in n0.
      rewrite n0.
      auto.
      destruct H.
      destruct_pairs.
      rewrite filter_In in H1.
      destruct_pairs.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec n 0).
      subst.
      rewrite <- beq_nat_refl in *.
      simpl in H2.
      rewrite andb_true_iff in H2.
      destruct H2.
      rewrite negb_true_iff in *.
      rewrite H2.
      auto.
      assert (n =? 0 = false) by now apply Nat.eqb_neq.
      rewrite H3 in *.
      subst.
      simpl in *.
      rewrite orb_true_iff in H2.
      destruct H2.
      rewrite H.
      rewrite negb_true_iff.
      rewrite beq_nat_false_iff in *.
      auto.
      rewrite negb_true_iff in H.
      destruct (Nat.eq_dec team0 team).
      rewrite e.
      rewrite <- beq_nat_refl.
      rewrite negb_true_iff.
      rewrite beq_nat_false_iff in *.
      auto.
      rewrite <- Nat.eqb_neq in n1.
      rewrite n1.
      rewrite negb_true_iff.
      auto.
      (* and case *)
      unfold simple_policy_scrub in *.
      rewrite in_map_iff in *.
      firstorder.
      rewrite filter_In in H3.
      destruct_pairs.
      rewrite andb_true_iff in H4.
      destruct_pairs.
      firstorder.
      rewrite filter_In in H3.
      destruct_pairs.
      rewrite andb_true_iff in H4.
      destruct_pairs.
      specialize (H2 x).
      specialize (H1 x).
      simpl in *.
      firstorder.
      rewrite filter_In in *.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      rewrite <- H in *.
      pose (fst_opt_always_true uq1 (User id email team) p).
      pose (fst_opt_always_true uq2 (User id email team) p).
      subst.
      apply H1 in e1.
      apply H2 in e0.
      rewrite filter_In in *.
      firstorder.
      rewrite <- beq_nat_false_iff in n.
      rewrite n in H.
      rewrite H in *.
      pose (fst_opt_always_true uq1 (User id email team) p).
      pose (fst_opt_always_true uq2 (User id email team) p).
      apply H1 in e0.
      apply H2 in e.
      rewrite filter_In in *.
      firstorder.
      (* or case *)
      unfold simple_policy_scrub in *.
      rewrite in_map_iff in *.
      firstorder.
      rewrite filter_In in H3.
      destruct_pairs.
      rewrite orb_true_iff in H4.
      firstorder.
      specialize (H2 x).
      specialize (H1 x).
      simpl in *.
      firstorder.
      rewrite filter_In in *.
      firstorder.
      unfold simple_policy_map in H.
      destruct x.
      destruct (Nat.eq_dec team0 team).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      rewrite orb_true_iff in H4.
      pose (fst_opt_always_true uq1 (User id email team) p).
      pose (fst_opt_always_true uq2 (User id email team) p).
      subst.
      destruct H4.
      firstorder.
      rewrite filter_In in *.
      firstorder.
      firstorder.
      rewrite filter_In in *.
      firstorder.
      rewrite <- beq_nat_false_iff in n.
      rewrite n in H.
      rewrite H in *.
      rewrite orb_true_iff in H4.
      pose (fst_opt_always_true uq1 (User id email team) p).
      pose (fst_opt_always_true uq2 (User id email team) p).
      rewrite filter_In in *.
      firstorder.
    Qed.
  End SimpleOptimization.

  (********************************************************)
  (* Generalized Boolean Policies *)
  (********************************************************)
  Section GeneralizedBooleanPolicy.
    Inductive user_field : Set :=
    | User_id: nat -> user_field
    | User_email: string -> user_field
    | User_team: nat -> user_field.

    Fixpoint beq_user_field (field : user_field) (u : user) :=
      match u with
      | User u_id u_email u_team =>
         match field with
          | User_id i => beq_nat u_id i
          | User_email e => if string_dec u_email e then true else false
          | User_team t => beq_nat u_team t
        end
      end.

    Fixpoint get_paper_field_nat (field : paper_field) (p : paper) :=
      match p with
      | Paper p_id _ p_team p_decision =>
         match field with
          | Paper_id _ => p_id
          | Paper_title _ => 0
          | Paper_team _ => p_team
          | Paper_decision _ => p_decision
        end
      end.

    Fixpoint get_user_field_nat (field : user_field) (u : user) :=
      match u with
      | User u_id _ u_team =>
         match field with
          | User_id _ => u_id
          | User_email e => 0
          | User_team _ => u_team
        end
      end.

    (* Returns true if p.paper_field = u.user_field, and paper_field and
    user_field have the same type *)
    Fixpoint beq_paper_user_field (p_field: paper_field) (u_field:user_field)
                                  (p: paper) (u: user) :=
      match p with
      | Paper p_id p_title p_team p_decision =>
        match u with
        | User u_id u_email u_team =>
          match p_field, u_field with
          | Paper_title t, User_email e => if string_dec p_title u_email
                                            then true else false
          | Paper_title _, _ => false
          | _, User_email _ => false
          | _, _ => beq_nat (get_paper_field_nat p_field p)
                              (get_user_field_nat u_field u)
          end
        end
      end.

    Inductive boolean_exp : Set :=
    | B_true: boolean_exp
    | B_false: boolean_exp
    | Paper_field_eq: paper_field -> boolean_exp
    | Paper_field_neq: paper_field -> boolean_exp
    | User_field_eq: user_field -> boolean_exp
    | User_field_neq: user_field -> boolean_exp
    | Paper_user_field_eq: paper_field -> user_field -> boolean_exp
    | Paper_user_field_neq: paper_field -> user_field -> boolean_exp
    | B_and: boolean_exp -> boolean_exp -> boolean_exp
    | B_or: boolean_exp -> boolean_exp -> boolean_exp.

    Fixpoint boolean_eval (b:boolean_exp) (p:paper) (u:user) : bool :=
      match b with
        | B_true => true
        | B_false => false
        | Paper_field_eq field => beq_field field p
        | Paper_field_neq field => negb (beq_field field p)
        | User_field_eq field => beq_user_field field u
        | User_field_neq field => negb (beq_user_field field u)
        | Paper_user_field_eq p_field u_field =>
            beq_paper_user_field p_field u_field p u
        | Paper_user_field_neq p_field u_field =>
            negb (beq_paper_user_field p_field u_field p u)
        | B_and b1 b2 => andb (boolean_eval b1 p u) (boolean_eval b2 p u)
        | B_or b1 b2 => orb (boolean_eval b1 p u) (boolean_eval b2 p u)
      end.

    (* Boolean blacklist policy *)
    Inductive bb_policy : Set :=
    | BB_policy: forall (id_exp:boolean_exp) (title_exp:boolean_exp)
                (team_exp:boolean_exp) (decision_exp:boolean_exp), bb_policy.
    Hint Constructors bb_policy.

    Fixpoint bb_policy_map (b:bb_policy) (p:paper) (u:user) : paper :=
    match b with
    | BB_policy id_exp title_exp team_exp decision_exp =>
      match p with
      | Paper p_id p_title p_team p_decision =>
        let id_val := if boolean_eval id_exp p u then 0 else p_id in
        let title_val := if boolean_eval title_exp p u
                          then EmptyString else p_title in
        let team_val := if boolean_eval team_exp p u then 0 else p_team in
        let decision_val := if boolean_eval decision_exp p u
                            then 0 else p_decision in
        Paper id_val title_val team_val decision_val
      end
    end.

    (* A definition of simple_policy as a bb_policy *)
    Definition simple_bb_policy :=
      BB_policy B_false B_false B_false
        (Paper_user_field_eq (Paper_team 0) (User_team 0)). 

    Lemma simple_bb_policy_is_simple_policy :
      forall p u,
      bb_policy_map simple_bb_policy p u = simple_policy_map p u.
    Proof.
      intros; destruct p, u. cbn.
      destruct (Nat.eq_dec team team0).
      - rewrite <- Nat.eqb_eq in e; rewrite e; auto.
      - rewrite <- Nat.eqb_neq in n; rewrite n; auto.
    Qed.
  End GeneralizedBooleanPolicy.

  (********************************************************)
  (* Generalized Boolean Optimizations *)
  (********************************************************)
  Section GeneralizedBooleanOptimization.
    Fixpoint nothing_boolean_optimization
      (policy:bb_policy) (uq:user_query) (u:user) :
      (user_query * sql_query) :=
      (uq, Sql_true).

    Lemma nothing_boolean_optimization_correct :
      forall u uq p bb_policy,
      sql_query_func uq (bb_policy_map bb_policy p u) = 
      andb (sql_query_func (fst (nothing_boolean_optimization bb_policy uq u))
            (bb_policy_map bb_policy p u))
      (sql_query_func (snd (nothing_boolean_optimization bb_policy uq u)) p).
    Proof.
      intros.
      destruct uq, bb_policy0, u; cbn; auto; rewrite andb_true_r; auto.
    Qed.

    Fixpoint exp_is_false (exp : boolean_exp) : bool :=
      match exp with
      | B_false => true
      | _ => false
      end.

    (* simple opt that says if we will overwrite a field with a policy, 
      it is unsafe to filter on that as an inner query *)
    Fixpoint simple_opt_inner (b : bb_policy) (q : user_query) : user_query :=
      match b with
      | BB_policy id_exp title_exp team_exp decision_exp => 
        match q with
        | Sql_true => Sql_true
        | Sql_false => Sql_false
        | Field_eq field => 
          match field with
            | Paper_id _ => if exp_is_false id_exp then q else Sql_true
            | Paper_title _ => if exp_is_false title_exp then q else Sql_true
            | Paper_team _ => if exp_is_false team_exp then q else Sql_true
            | Paper_decision _ => if exp_is_false decision_exp then q else Sql_true
          end
        | Field_neq field => 
          match field with
            | Paper_id _ => if exp_is_false id_exp then q else Sql_true
            | Paper_title _ => if exp_is_false title_exp then q else Sql_true
            | Paper_team _ => if exp_is_false team_exp then q else Sql_true
            | Paper_decision _ => if exp_is_false decision_exp then q else Sql_true
          end
        | And q1 q2 => And (simple_opt_inner b q1) (simple_opt_inner b q2)
        | Or q1 q2 => Or (simple_opt_inner b q1) (simple_opt_inner b q2)
        end
      end.

    (* This is proof that our simple opt doesnt eat anything. *)
    Lemma simple_opt_inner_doesnt_lose:
      forall b uq p u,
        sql_query_func uq (bb_policy_map b p u) = true -> sql_query_func (simple_opt_inner b uq) p = true.
    Proof.
      intros.
      destruct b, p, u.
      induction uq;
      simpl in *;
      auto.
      (* Field eq case *)
      destruct p;
      simpl in *.
      destruct (Sumbool.sumbool_of_bool (exp_is_false id_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval id_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct id_exp;
      simpl in *;
      firstorder.
      destruct (Sumbool.sumbool_of_bool (exp_is_false title_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval title_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct title_exp;
      simpl in *;
      firstorder.
      destruct (Sumbool.sumbool_of_bool (exp_is_false team_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval team_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct team_exp;
      simpl in *;
      firstorder.
      destruct (Sumbool.sumbool_of_bool (exp_is_false decision_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval decision_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct decision_exp;
      simpl in *;
      firstorder.
      (* Field neq case, exact copy of eq_case - todo make smaller *)
      destruct p;
      simpl in *.
      destruct (Sumbool.sumbool_of_bool (exp_is_false id_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval id_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct id_exp;
      simpl in *;
      firstorder.
      destruct (Sumbool.sumbool_of_bool (exp_is_false title_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval title_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct title_exp;
      simpl in *;
      firstorder.
      destruct (Sumbool.sumbool_of_bool (exp_is_false team_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval team_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct team_exp;
      simpl in *;
      firstorder.
      destruct (Sumbool.sumbool_of_bool (exp_is_false decision_exp));
      destruct (Sumbool.sumbool_of_bool (boolean_eval decision_exp (Paper id title team decision)
         (User id0 email team0)));
      rewrite e in *;
      rewrite e0 in *;
      destruct decision_exp;
      simpl in *;
      firstorder.
      (* And case *)
      rewrite andb_true_iff in *.
      destruct_pairs.
      firstorder.
      (* Or case *)
      rewrite orb_true_iff in *.
      firstorder.
    Qed.

    Lemma neg_bool_iff:
      forall x y, (x = true <-> y = true) <-> (x = false <-> y = false).
    Proof.
      split;intros;split;
      destruct (Sumbool.sumbool_of_bool x);
      destruct (Sumbool.sumbool_of_bool y);
      inversion H;
      subst;
      firstorder.
    Qed.

    Fixpoint negate_query (q : user_query) : user_query :=
        match q with
        | Sql_true => Sql_false
        | Sql_false => Sql_true
        | Field_eq field => Field_neq field
        | Field_neq field => Field_eq field
        | And q1 q2 => Or (negate_query q1) (negate_query q2)
        | Or q1 q2 => And (negate_query q1) (negate_query q2)
        end.

    Lemma negate_correct_true:
      forall q p,
        sql_query_func q p = true <-> sql_query_func (negate_query q) p = false.
    Proof.
      split;intros.
      induction q; simpl in *; auto.
      rewrite negb_false_iff; now auto.
      rewrite negb_true_iff in H; now auto.
      rewrite andb_true_iff in H.
      now firstorder.
      rewrite orb_true_iff in H.
      rewrite andb_false_iff.
      now firstorder.
      induction q; simpl in *; auto.
      rewrite negb_false_iff in H; now auto.
      rewrite negb_true_iff; now auto.
      rewrite orb_false_iff in H.
      rewrite andb_true_iff.
      now firstorder.
      rewrite andb_false_iff in H.
      now firstorder.
    Qed.

    Lemma negate_correct_false:
      forall q p,
        sql_query_func q p = false <-> sql_query_func (negate_query q) p = true.
    Proof.
      split;intros.
      induction q; simpl in *; auto.
      rewrite negb_true_iff; now auto.
      rewrite negb_false_iff in H; now auto.
      rewrite andb_false_iff in H.
      now firstorder.
      rewrite orb_false_iff in H.
      rewrite andb_true_iff.
      now firstorder.
      induction q; simpl in *; auto.
      rewrite negb_true_iff in H; now auto.
      rewrite negb_false_iff; now auto.
      rewrite orb_true_iff in H.
      rewrite andb_false_iff.
      now firstorder.
      rewrite andb_true_iff in H.
      now firstorder.
    Qed.

    Fixpoint paper_user_field_eq_to_query (pfield : paper_field) (ufield : user_field) (u : user) :=
      match u with
      | User uid uemail uteam =>
         match pfield with
          | Paper_id pid =>
            match ufield with
            | User_id _ => Field_eq (Paper_id uid)
            | User_email _ => Sql_false (* never reached *)
            | User_team _ => Field_eq (Paper_id uteam)
            end
          | Paper_title ptitle =>
            match ufield with
            | User_id _ => Sql_false(* never reached *)
            | User_email _ => Field_eq (Paper_title uemail)
            | User_team _ => Sql_false (* never reached *)
            end
          | Paper_team pteam =>
            match ufield with
            | User_id _ => Field_eq (Paper_team uid)
            | User_email _ => Sql_false (* never reached *)
            | User_team _ => Field_eq (Paper_team uteam)
            end
          | Paper_decision pdecision =>
            match ufield with
            | User_id _ => Field_eq (Paper_decision uid)
            | User_email _ => Sql_false (* never reached *)
            | User_team _ => Field_eq (Paper_decision uteam)
            end
          end
      end.

    (* Now start writing something that can move the entire query inside. This seems like pain. *)
    Fixpoint bexp_to_query (exp : boolean_exp) (u : user) : user_query :=
      match u with
      | User uid uemail uteam =>
        match exp with
        | B_true => Sql_true
        | B_false => Sql_false
        | Paper_field_eq field => Field_eq field
        | Paper_field_neq field => Field_neq field
        | User_field_eq ufield => if beq_user_field ufield u then Sql_true else Sql_false
        | User_field_neq ufield => if beq_user_field ufield u then Sql_false else Sql_true
        | Paper_user_field_eq pfield ufield => paper_user_field_eq_to_query pfield ufield u
        | Paper_user_field_neq pfield ufield => negate_query (paper_user_field_eq_to_query pfield ufield u)
        | B_and exp1 exp2 => And (bexp_to_query exp1 u) (bexp_to_query exp2 u)
        | B_or exp1 exp2 => Or (bexp_to_query exp1 u) (bexp_to_query exp2 u)
        end
      end.

    Lemma beq_paper_user_field_opt_correct (pf : paper_field) (uf : user_field) (p: paper) (u: user):
      beq_paper_user_field pf uf p u = true <-> sql_query_func (bexp_to_query (Paper_user_field_eq pf uf) u) p = true.
    Proof.
      split;intros;destruct p, u;
      destruct uf;
      destruct pf;
      simpl in *;
      auto.
    Qed.

    Lemma negb_beq_paper_user_field_opt_correct (pf : paper_field) (uf : user_field) (p: paper) (u: user):
      negb (beq_paper_user_field pf uf p u) = true <-> sql_query_func (bexp_to_query (Paper_user_field_neq pf uf) u) p = true.
    Proof.
     split;intros;destruct p, u;
    destruct uf;
    destruct pf;
    simpl in *;
    auto.
    Qed.

    Lemma bexp_to_query_correct:
      forall exp p u,
        boolean_eval exp p u = true <-> sql_query_func (bexp_to_query exp u) p = true.
    Proof.
      split;intros.
      destruct p, u.
      induction exp;
      simpl in *; auto.
      (* user field eq *)
      rewrite H.
      unfold sql_query_func; now auto.
      (* user field neq *)
      rewrite negb_true_iff in H.
      rewrite H.
      unfold sql_query_func; now auto.
      (* eq paper user field case *)
      pose (beq_paper_user_field_opt_correct p u (Paper id title team decision)
      (User id0 email team0)).
      now firstorder.
      (* neq paper user field case *)
      pose (negb_beq_paper_user_field_opt_correct p u (Paper id title team decision)
      (User id0 email team0)).
      now firstorder.
      (* and *)
      rewrite andb_true_iff in *.
      now firstorder.
      (* or *)
      rewrite orb_true_iff in *.
      firstorder.
      (* other direction *)
      destruct p, u.
      induction exp;
      simpl in *; auto.
      (* user field eq *)
      destruct u;
      simpl in *.
      (* id field *)
      destruct (Nat.eq_dec id0 n).
      rewrite e in *.
      rewrite <- beq_nat_refl; now auto.
      apply Nat.eqb_neq in n0.
      rewrite n0 in H.
      simpl in H.
      inversion H.
      (* string field *)
      destruct (string_dec email s).
      auto.
      simpl in H.
      auto.
      (* team field *)
      destruct (Nat.eq_dec team0 n).
      rewrite e in *.
      rewrite <- beq_nat_refl; now auto.
      apply Nat.eqb_neq in n0.
      rewrite n0 in H.
      simpl in H.
      now inversion H.
      (* neq user fields *)
      destruct u;
      simpl in *.
      (* id field *)
      destruct (Nat.eq_dec id0 n).
      rewrite e in *.
      rewrite <- beq_nat_refl in *.
      simpl in *.
      now auto.
      apply Nat.eqb_neq in n0.
      rewrite negb_true_iff.
      now auto.
      (* string field *)
      destruct (string_dec email s);
      simpl in *;
      auto.
      (* team field *)
      destruct (Nat.eq_dec team0 n).
      rewrite e in *.
      rewrite <- beq_nat_refl in *; now auto.
      apply Nat.eqb_neq in n0.
      rewrite negb_true_iff.
      now auto.
      (* eq paper user field case *)
      pose (beq_paper_user_field_opt_correct p u (Paper id title team decision)
      (User id0 email team0)).
      now firstorder.
      (* neq paper user field case *)
      pose (negb_beq_paper_user_field_opt_correct p u (Paper id title team decision)
      (User id0 email team0)).
      now firstorder.
      (* and case *)
      rewrite andb_true_iff in *.
      now firstorder.
      rewrite orb_true_iff in *.
      now firstorder.
    Qed.

    Lemma bexp_to_query_correct_false:
      forall exp p u,
        boolean_eval exp p u = false <-> sql_query_func (bexp_to_query exp u) p = false.
    Proof.
      intros.
      pose (bexp_to_query_correct exp p u).
      rewrite neg_bool_iff in i.
      auto.
    Qed.

    (* Pair of functions that implements our final optimization *)
    Fixpoint bb_opt_outer (policy:bb_policy) (uq:user_query) (u:user) :
      (sql_query) := Sql_true.
    (* A bb_policy is a blacklist that blacklists certain fields based on boolean expressions
    We convert these boolean expressions to SQL expressions - the SQL expression admits a
    paper if and only if the boolean expression returns true for this user and paper

    This optimization moves the entire user query into SQL space
    Suppose our policy blacklists every field with a field_b boolean expression, which we convert to
    a field_sql SQL expression as above

    This optimization replaces every instance of Paper.field = x with
    if x = 0/EmptyString
    then (field_sql || Paper.field = x)
    else (!field_sql && Paper.field = x)

    It replaces every instance of Paper.field != x with
    if x = 0/EmptyString
    then (!field_sql && Paper.field != x)
    else (field_sql || Paper.field != x) *)
    Fixpoint bb_opt_inner (policy:bb_policy) (uq:user_query) (u:user) :
      (user_query) :=
      match policy with
      | BB_policy id_exp title_exp team_exp decision_exp =>
        let id_sql := bexp_to_query id_exp u in
        let title_sql := bexp_to_query title_exp u in
        let team_sql := bexp_to_query team_exp u in
        let decision_sql := bexp_to_query decision_exp u in
        match uq with
        | Field_eq field =>
          match field with
          | Paper_title x =>  if (string_dec x EmptyString)
                              then Or title_sql uq
                              else And (negate_query title_sql) uq
          | Paper_id x => if (Nat.eqb x 0)
                          then Or id_sql uq
                          else And (negate_query id_sql) uq
          | Paper_team x => if (Nat.eqb x 0)
                            then Or team_sql uq
                            else And (negate_query team_sql) uq
          | Paper_decision x => if (Nat.eqb x 0)
                                then Or decision_sql uq
                                else And (negate_query decision_sql) uq
          end
        | Field_neq field =>
          match field with
          | Paper_title x =>  if (string_dec x EmptyString)
                              then And (negate_query title_sql) uq
                              else Or title_sql uq
          | Paper_id x => if (Nat.eqb x 0)
                          then And (negate_query id_sql) uq
                          else Or id_sql uq
          | Paper_team x => if (Nat.eqb x 0)
                            then And (negate_query team_sql) uq
                            else Or team_sql uq
          | Paper_decision x => if (Nat.eqb x 0)
                                then And (negate_query decision_sql) uq
                                else Or decision_sql uq
          end
        | And q1 q2 =>  And (bb_opt_inner policy q1 u) (bb_opt_inner policy q2 u)
        | Or q1 q2 => Or (bb_opt_inner policy q1 u) (bb_opt_inner policy q2 u)
        | _ => uq
        end
      end.

    Lemma bb_opt_true_first :
    forall u uq p policy,
      sql_query_func uq (bb_policy_map policy p u) = true ->
      andb (sql_query_func (bb_opt_outer policy uq u) (bb_policy_map policy p u))
        (sql_query_func (bb_opt_inner policy uq u) p) = true.
    Proof.
      intros.
      rewrite andb_true_iff.
      split.
      destruct policy.
      unfold bb_opt_outer.
      simpl.
      auto.
      destruct policy.
      unfold bb_opt_inner.
      induction uq.
      (* True case *)
      simpl in *.
      auto.
      (* False case *)
      simpl in *.
      auto.
      (* Field_eq case *)
      simpl in *.
      destruct p.
      destruct p0;
      simpl in *.
      (* id *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval id_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite Nat.eqb_eq in H.
      rewrite H.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      rewrite Nat.eqb_eq in H.
      destruct (Nat.eq_dec n 0).
      rewrite e0 in *.
      rewrite H.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite orb_true_iff.
      now auto.
      apply beq_nat_false_iff in n0.
      rewrite n0.
      simpl.
      rewrite andb_true_iff.
      rewrite H in *.
      rewrite <- beq_nat_refl.
      rewrite <- negate_correct_false.
      apply bexp_to_query_correct_false in e.
      now auto.
      (* email - fml *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval title_exp (Paper id title team decision) u)).
      rewrite e in *.
      destruct (string_dec "" s).
      destruct (string_dec s ""). (* WHY do I have to do thi????? *)
      simpl in *.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      subst.
      now auto.
      now auto.
      rewrite e in *.
      destruct (string_dec s "").
      simpl in *.
      rewrite orb_true_iff.
      now auto.
      simpl in *.
      rewrite andb_true_iff.
      rewrite <- negate_correct_false.
      apply bexp_to_query_correct_false in e.
      now auto.
      (* team *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval team_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite beq_nat_true_iff in H.
      rewrite H in *.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      destruct n.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite orb_true_iff.
      now auto.
      simpl.
      rewrite andb_true_iff.
      apply bexp_to_query_correct_false in e.
      rewrite <- negate_correct_false.
      now auto.
      (* decision *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval decision_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite beq_nat_true_iff in H.
      rewrite H in *.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      destruct n.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite orb_true_iff.
      now auto.
      simpl.
      rewrite andb_true_iff.
      apply bexp_to_query_correct_false in e.
      rewrite <- negate_correct_false.
      now auto.
      (* field neq cases *)
      simpl in *.
      destruct p.
      destruct p0;
      simpl in *.
      (* id *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval id_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite negb_true_iff in H.
      rewrite beq_nat_sym in H.
      rewrite H.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      rewrite negb_true_iff in H.
      destruct (Nat.eq_dec n 0).
      rewrite e0 in *.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite andb_true_iff.
      rewrite <- negate_correct_false.
      rewrite negb_true_iff.
      apply bexp_to_query_correct_false in e.
      now auto.
      apply beq_nat_false_iff in n0.
      rewrite n0.
      simpl.
      rewrite orb_true_iff.
      rewrite H in *.
      rewrite negb_true_iff.
      apply bexp_to_query_correct_false in e.
      now auto.
      (* title - fml *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval title_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite negb_true_iff in H.
      destruct (string_dec "" s);
      destruct (string_dec s ""). (* WHY do I have to do thi????? *)
      simpl in *.
      rewrite andb_true_iff.
      rewrite negb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      subst.
      now auto.
      now auto.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      destruct (string_dec s "").
      simpl in *.
      rewrite andb_true_iff.
      rewrite <- negate_correct_false.
      apply bexp_to_query_correct_false in e.
      now auto.
      simpl in *.
      rewrite orb_true_iff.
      apply bexp_to_query_correct_false in e.
      now auto.
      (* team *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval team_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite negb_true_iff in H.
      rewrite beq_nat_sym in H.
      rewrite H in *.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      destruct n.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite andb_true_iff.
      rewrite <- negate_correct_false.
      apply bexp_to_query_correct_false in e.
      now auto.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct_false in e.
      now auto.
      (* decision *)
      destruct (Sumbool.sumbool_of_bool (boolean_eval decision_exp (Paper id title team decision) u)).
      rewrite e in *.
      rewrite negb_true_iff in H.
      rewrite beq_nat_sym in H.
      rewrite H in *.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct in e.
      now auto.
      rewrite e in *.
      destruct n.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite andb_true_iff.
      rewrite <- negate_correct_false.
      apply bexp_to_query_correct_false in e.
      now auto.
      simpl.
      rewrite orb_true_iff.
      apply bexp_to_query_correct_false in e.
      now auto.
      (* and case*)
      simpl in *.
      rewrite andb_true_iff in *.
      now firstorder.
      (* or case*)
      simpl in *.
      rewrite orb_true_iff in *.
      now firstorder.
    Qed.

    Lemma bb_opt_true_second :
    forall u uq p policy,
      andb (sql_query_func (bb_opt_outer policy uq u) (bb_policy_map policy p u))
        (sql_query_func (bb_opt_inner policy uq u) p) = true ->
      sql_query_func uq (bb_policy_map policy p u) = true.
    Proof.
      intros.
      rewrite andb_true_iff in H.
      destruct policy, p.
      destruct_pairs.
      clear H.
      induction uq.
      simpl.
      auto.
      simpl in *.
      auto.
      (* Field_eq case*)
      unfold bb_opt_inner in H0;
      unfold bb_policy_map;
      destruct p;
      simpl in *.
      (* id *)
      destruct (Nat.eq_dec n 0).
      rewrite e in *.
      rewrite <- beq_nat_refl in H0.
      simpl in *.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      now auto.
      destruct (boolean_eval id_exp (Paper id title team decision) u);auto.
      apply beq_nat_false_iff in n0.
      rewrite n0 in H0.
      simpl in H0.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      (* title *)
      destruct (string_dec s "").
      simpl in H0.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      rewrite e.
      now auto.
      destruct (boolean_eval title_exp (Paper id title team decision) u).
      rewrite e; now auto.
      now auto.
      simpl in *.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      (* team *)
      destruct (Nat.eq_dec n 0).
      rewrite e in *.
      rewrite <- beq_nat_refl in H0.
      simpl in *.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      now auto.
      destruct (boolean_eval team_exp (Paper id title team decision) u);auto.
      apply beq_nat_false_iff in n0.
      rewrite n0 in H0.
      simpl in H0.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      (* decision *)
      destruct (Nat.eq_dec n 0).
      rewrite e in *.
      rewrite <- beq_nat_refl in H0.
      simpl in *.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      now auto.
      destruct (boolean_eval decision_exp (Paper id title team decision) u);auto.
      apply beq_nat_false_iff in n0.
      rewrite n0 in H0.
      simpl in H0.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      (* Field neq *)
      unfold bb_opt_inner in H0;
      unfold bb_policy_map;
      destruct p;
      simpl in *.
      (* id *)
      destruct (Nat.eq_dec n 0).
      rewrite e in *.
      rewrite <- beq_nat_refl in H0.
      simpl in *.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      apply beq_nat_false_iff in n0.
      rewrite n0 in H0.
      simpl in H0.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      rewrite negb_true_iff.
      rewrite beq_nat_sym.
      now auto.
      destruct (boolean_eval id_exp (Paper id title team decision) u);auto.
      rewrite negb_true_iff.
      rewrite beq_nat_sym.
      now auto.
      (* title *)
      destruct (string_dec s "").
      simpl in H0.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      simpl in *.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      destruct (string_dec "" s); now auto.
      destruct (boolean_eval title_exp (Paper id title team decision) u).
      destruct (string_dec "" s); now auto.
      now auto.
      (* team *)
      destruct (Nat.eq_dec n 0).
      rewrite e in *.
      rewrite <- beq_nat_refl in H0.
      simpl in *.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      apply beq_nat_false_iff in n0.
      rewrite n0 in H0.
      simpl in H0.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      rewrite negb_true_iff.
      rewrite beq_nat_sym.
      now auto.
      destruct (boolean_eval team_exp (Paper id title team decision) u).
      rewrite negb_true_iff.
      rewrite beq_nat_sym.
      now auto.
      now auto.
      (* decision *)
      destruct (Nat.eq_dec n 0).
      rewrite e in *.
      rewrite <- beq_nat_refl in H0.
      simpl in *.
      rewrite andb_true_iff in H0.
      destruct_pairs.
      rewrite <- negate_correct_false in H.
      rewrite <- bexp_to_query_correct_false in H.
      rewrite H.
      now auto.
      apply beq_nat_false_iff in n0.
      rewrite n0 in H0.
      simpl in H0.
      rewrite orb_true_iff in H0.
      destruct H0.
      rewrite <- bexp_to_query_correct in H.
      rewrite H.
      rewrite negb_true_iff.
      rewrite beq_nat_sym.
      now auto.
      destruct (boolean_eval decision_exp (Paper id title team decision) u).
      rewrite negb_true_iff.
      rewrite beq_nat_sym.
      now auto.
      now auto.
      (* and case *)
      simpl in *.
      rewrite andb_true_iff in *.
      now firstorder.
      (* or case *)
      simpl in *.
      rewrite orb_true_iff in *.
      now firstorder.
    Qed.

    Lemma bb_opt_true_correct :
      forall u uq p policy,
      sql_query_func uq (bb_policy_map policy p u) = true <->
      andb (sql_query_func (bb_opt_outer policy uq u) (bb_policy_map policy p u))
        (sql_query_func (bb_opt_inner policy uq u) p) = true.
    Proof.
      split;intros.
      apply bb_opt_true_first; now auto.
      apply bb_opt_true_second; now auto.
    Qed.

    Lemma bb_opt_false_correct :
    forall u uq p policy,
      sql_query_func uq (bb_policy_map policy p u) = false <->
      andb (sql_query_func (bb_opt_outer policy uq u) (bb_policy_map policy p u))
        (sql_query_func (bb_opt_inner policy uq u) p) = false.
    Proof.
      intros.
      pose (bb_opt_true_correct u uq p policy).
      rewrite neg_bool_iff in i.
      now auto.
    Qed.

    Lemma bb_opt_correct :
      forall u uq p policy,
      sql_query_func uq (bb_policy_map policy p u) =
      andb (sql_query_func (bb_opt_outer policy uq u) (bb_policy_map policy p u))
        (sql_query_func (bb_opt_inner policy uq u) p).
    Proof.
      intros; destruct (bool_dec (sql_query_func uq (bb_policy_map policy p u)) true);
      [ rewrite e | apply not_true_is_false in n; rewrite n ];
      symmetry; [ apply bb_opt_true_first | apply bb_opt_false_correct ]; auto.
    Qed.
  End GeneralizedBooleanOptimization.

  (********************************************************)
  (* Generalized User Queries *)
  (********************************************************)

  Section GeneralizedUserQueries.
    (* Bring not back into the user queries *)
    Inductive gen_sql_query : Set :=
      | Gen_true: gen_sql_query
      | Gen_false: gen_sql_query
      | Gen_field_eq: paper_field -> gen_sql_query
      | Gen_and: gen_sql_query -> gen_sql_query -> gen_sql_query
      | Gen_or: gen_sql_query -> gen_sql_query -> gen_sql_query
      | Gen_not: gen_sql_query -> gen_sql_query.

    Fixpoint gen_sql_query_func (q:gen_sql_query) (p:paper) : bool :=
      match q with
        | Gen_true => true
        | Gen_false => false
        | Gen_field_eq field => beq_field field p
        | Gen_and q1 q2 => andb (gen_sql_query_func q1 p) (gen_sql_query_func q2 p)
        | Gen_or q1 q2 => orb (gen_sql_query_func q1 p) (gen_sql_query_func q2 p)
        | Gen_not q1 => negb (gen_sql_query_func q1 p)
      end.

    Fixpoint gen_to_sql (q:gen_sql_query) : sql_query :=
      match q with
        | Gen_true => Sql_true
        | Gen_false => Sql_false
        | Gen_field_eq field => Field_eq field
        | Gen_and q1 q2 => And (gen_to_sql q1) (gen_to_sql q2)
        | Gen_or q1 q2 => Or (gen_to_sql q1) (gen_to_sql q2)
        | Gen_not q1 => negate_query (gen_to_sql q1)
      end.

    Lemma gen_to_sql_correct :
      forall p q, sql_query_func (gen_to_sql q) p = gen_sql_query_func q p.
    Proof.
      intros; induction q; cbn; auto.
      1, 2: rewrite IHq1; rewrite IHq2; auto.
      destruct (bool_dec (sql_query_func (gen_to_sql q) p) true).
      - rewrite e in IHq; rewrite negate_correct_true in e;
        rewrite e; rewrite <- IHq; now cbn.
      - apply not_true_is_false in n;
        rewrite n in IHq; rewrite negate_correct_false in n;
        rewrite n; rewrite <- IHq; now cbn.
    Qed.
  End GeneralizedUserQueries.

  Notation gen_user_query := gen_sql_query.

  Section GeneralizedUserQueriesOpt.
    (* bb_opt for general user queries *)
    Fixpoint bb_opt_inner_gen_uq (policy:bb_policy) (uq:gen_user_query) (u:user) :
      (sql_query) := bb_opt_inner policy (gen_to_sql uq) u.
    Fixpoint bb_opt_outer_gen_uq (policy:bb_policy) (uq:gen_user_query) (u:user) :
      (sql_query) := bb_opt_outer policy (gen_to_sql uq) u.

    (* Proof that the bb_opt for general user queries is correct *)
    Lemma bb_opt_gen_uq_correct :
      forall u uq p policy,
      gen_sql_query_func uq (bb_policy_map policy p u) =
      andb (sql_query_func (bb_opt_outer_gen_uq policy uq u) (bb_policy_map policy p u))
        (sql_query_func (bb_opt_inner_gen_uq policy uq u) p).
    Proof.
      intros. unfold bb_opt_outer_gen_uq, bb_opt_inner_gen_uq; destruct policy.
      rewrite <- gen_to_sql_correct.
      rewrite bb_opt_correct; auto.
    Qed.
  End GeneralizedUserQueriesOpt.

  (********************************************************)
  (* General white/blacklists *)
  (********************************************************)

  (* First, we introduce Not to our boolean expressions *)
  Section GeneralizedBooleanExpressions.
    Inductive gen_boolean_exp : Set :=
    | Gen_b_true: gen_boolean_exp
    | Gen_b_false: gen_boolean_exp
    | Gen_paper_field_eq: paper_field -> gen_boolean_exp
    | Gen_user_field_eq: user_field -> gen_boolean_exp
    | Gen_paper_user_field_eq: paper_field -> user_field -> gen_boolean_exp
    | Gen_b_and: gen_boolean_exp -> gen_boolean_exp -> gen_boolean_exp
    | Gen_b_or: gen_boolean_exp -> gen_boolean_exp -> gen_boolean_exp
    | Gen_b_not: gen_boolean_exp -> gen_boolean_exp.

    Fixpoint gen_boolean_eval (b:gen_boolean_exp) (p:paper) (u:user) : bool :=
      match b with
        | Gen_b_true => true
        | Gen_b_false => false
        | Gen_paper_field_eq field => beq_field field p
        | Gen_user_field_eq field => beq_user_field field u
        | Gen_paper_user_field_eq p_field u_field =>
            beq_paper_user_field p_field u_field p u
        | Gen_b_and b1 b2 => andb (gen_boolean_eval b1 p u) (gen_boolean_eval b2 p u)
        | Gen_b_or b1 b2 => orb (gen_boolean_eval b1 p u) (gen_boolean_eval b2 p u)
        | Gen_b_not b1 => negb (gen_boolean_eval b1 p u)
      end.

    Fixpoint negate_bexp (b:boolean_exp) : boolean_exp :=
      match b with
        | B_true => B_false
        | B_false => B_true
        | Paper_field_eq field => Paper_field_neq field
        | Paper_field_neq field => Paper_field_eq field
        | User_field_eq field => User_field_neq field
        | User_field_neq field => User_field_eq field
        | Paper_user_field_eq p_field u_field =>
            Paper_user_field_neq p_field u_field
        | Paper_user_field_neq p_field u_field =>
            Paper_user_field_eq p_field u_field
        | B_and b1 b2 => B_or (negate_bexp b1) (negate_bexp b2)
        | B_or b1 b2 => B_and (negate_bexp b1) (negate_bexp b2)
      end.

    Lemma negate_bexp_correct_true :
      forall b p u, boolean_eval (negate_bexp b) p u = true <->
        boolean_eval b p u = false.
    Proof.
      split; intros; induction b; cbn in *; auto;
      try rewrite negb_true_iff in *;
      try rewrite negb_false_iff in *; auto;
      [ apply orb_true_iff in H; apply andb_false_iff |
        apply andb_true_iff in H | apply andb_false_iff in H |
        apply orb_false_iff in H ]; now firstorder.
    Qed.

    Lemma negate_bexp_correct_false :
      forall b p u, boolean_eval (negate_bexp b) p u = false <->
        boolean_eval b p u = true.
    Proof.
      split; intros; induction b; cbn in *; auto;
      try rewrite negb_true_iff in *;
      try rewrite negb_false_iff in *; auto;
      [ apply orb_false_iff in H |
        apply andb_false_iff in H | apply andb_true_iff in H |
        apply orb_true_iff in H; apply andb_false_iff ]; now firstorder.
    Qed.

    Fixpoint gen_bexp_to_bexp (b:gen_boolean_exp) : boolean_exp :=
      match b with
        | Gen_b_true => B_true
        | Gen_b_false => B_false
        | Gen_paper_field_eq field => Paper_field_eq field
        | Gen_user_field_eq field => User_field_eq field
        | Gen_paper_user_field_eq p_field u_field =>
            Paper_user_field_eq p_field u_field
        | Gen_b_and b1 b2 => B_and (gen_bexp_to_bexp b1) (gen_bexp_to_bexp b2)
        | Gen_b_or b1 b2 => B_or (gen_bexp_to_bexp b1) (gen_bexp_to_bexp b2)
        | Gen_b_not b1 => negate_bexp (gen_bexp_to_bexp b1)
      end.

    Lemma gen_b_correct :
      forall b p u, gen_boolean_eval b p u= boolean_eval (gen_bexp_to_bexp b) p u.
    Proof.
      intros; induction b; cbn; auto; try rewrite IHb1, IHb2; auto.
      rewrite IHb;
      destruct (bool_dec (boolean_eval (gen_bexp_to_bexp b) p u) true).
      - rewrite e in *; rewrite <- negate_bexp_correct_false in e; rewrite e;
        cbn; auto.
      - apply not_true_is_false in n; rewrite n in *;
        rewrite <- negate_bexp_correct_true in n; rewrite n;
        cbn; auto.
    Qed.
  End GeneralizedBooleanExpressions.

  Section GeneralizedWhiteList.
    (* Generalized blacklist *)
    Inductive gbb_policy : Set :=
    | GBB_policy: forall (id_exp:gen_boolean_exp) (title_exp:gen_boolean_exp)
                (team_exp:gen_boolean_exp) (decision_exp:gen_boolean_exp), gbb_policy.
    Hint Constructors gbb_policy.

    Fixpoint gbb_policy_map (b:gbb_policy) (p:paper) (u:user) : paper :=
    match b with
    | GBB_policy id_exp title_exp team_exp decision_exp =>
      match p with
      | Paper p_id p_title p_team p_decision =>
        let id_val := if gen_boolean_eval id_exp p u then 0 else p_id in
        let title_val := if gen_boolean_eval title_exp p u
                          then EmptyString else p_title in
        let team_val := if gen_boolean_eval team_exp p u then 0 else p_team in
        let decision_val := if gen_boolean_eval decision_exp p u
                            then 0 else p_decision in
        Paper id_val title_val team_val decision_val
      end
    end.

    Fixpoint gbb_to_bb (gbb:gbb_policy) : bb_policy :=
    match gbb with
    | GBB_policy id_exp title_exp team_exp decision_exp =>
      BB_policy (gen_bexp_to_bexp id_exp) (gen_bexp_to_bexp title_exp)
        (gen_bexp_to_bexp team_exp) (gen_bexp_to_bexp decision_exp)
    end.

    Lemma gbb_to_bb_correct :
    forall gbb p u, gbb_policy_map gbb p u = bb_policy_map (gbb_to_bb gbb) p u.
    Proof.
      intros; destruct gbb; unfold gbb_policy_map, gbb_to_bb, bb_policy_map; cbn;
      repeat rewrite gen_b_correct; auto.
    Qed.

    (* Generalized white list *)
    Inductive gw_policy : Set :=
    | GW_policy: forall (id_exp:gen_boolean_exp) (title_exp:gen_boolean_exp)
                (team_exp:gen_boolean_exp) (decision_exp:gen_boolean_exp), gw_policy.
    Hint Constructors gw_policy.

    Fixpoint gw_policy_map (b:gw_policy) (p:paper) (u:user) : paper :=
    match b with
    | GW_policy id_exp title_exp team_exp decision_exp =>
      match p with
      | Paper p_id p_title p_team p_decision =>
        let id_val := if gen_boolean_eval id_exp p u then p_id else 0 in
        let title_val := if gen_boolean_eval title_exp p u
                          then p_title else EmptyString in
        let team_val := if gen_boolean_eval team_exp p u then p_team else 0 in
        let decision_val := if gen_boolean_eval decision_exp p u
                            then p_decision else 0 in
        Paper id_val title_val team_val decision_val
      end
    end.

    Fixpoint gw_to_gbb (gw:gw_policy) : gbb_policy :=
    match gw with
    | GW_policy id_exp title_exp team_exp decision_exp =>
      GBB_policy (Gen_b_not id_exp) (Gen_b_not title_exp) (Gen_b_not team_exp)
        (Gen_b_not decision_exp)
    end.

    Lemma gw_to_gbb_correct :
    forall gw p u, gw_policy_map gw p u = gbb_policy_map (gw_to_gbb gw) p u.
    Proof.
      intros; destruct gw; unfold gw_policy_map, gw_to_gbb, gbb_policy_map; cbn.
      destruct (bool_dec (gen_boolean_eval id_exp p u) true);
      destruct (bool_dec (gen_boolean_eval title_exp p u) true);
      destruct (bool_dec (gen_boolean_eval team_exp p u) true);
      destruct (bool_dec (gen_boolean_eval decision_exp p u) true);
      try apply not_true_is_false in n;
      try apply not_true_is_false in n0;
      try apply not_true_is_false in n1;
      try apply not_true_is_false in n2;
      try rewrite n;
      try rewrite n0;
      try rewrite n1;
      try rewrite n2;
      try rewrite e;
      try rewrite e0;
      try rewrite e1;
      try rewrite e2; cbn; auto.
    Qed.
  End GeneralizedWhiteList.

  Section GeneralizedBlackWhiteListOpts.
    (* Pair of functions that implements the optimization for generalized black lists *)
    Fixpoint gbb_opt_outer (policy:gbb_policy) (uq:gen_user_query) (u:user) :
      (sql_query) := bb_opt_outer_gen_uq (gbb_to_bb policy) uq u.
    Fixpoint gbb_opt_inner (policy:gbb_policy) (uq:gen_user_query) (u:user) :
      (sql_query) := bb_opt_inner_gen_uq (gbb_to_bb  policy) uq u.

    Lemma gbb_opt_correct :
      forall u uq p gbb_policy,
      gen_sql_query_func uq (gbb_policy_map gbb_policy p u) =
      andb (sql_query_func (gbb_opt_outer gbb_policy uq u) (gbb_policy_map gbb_policy p u))
        (sql_query_func (gbb_opt_inner gbb_policy uq u) p).
    Proof.
      intros; destruct gbb_policy0.
      unfold gbb_opt_inner, gbb_opt_outer.
      rewrite gbb_to_bb_correct.
      rewrite bb_opt_gen_uq_correct; auto.
    Qed.

    (* Pair of functions that implements the optimization for white lists *)
    Fixpoint gw_opt_outer (policy:gw_policy) (uq:gen_user_query) (u:user) :
      (sql_query) := bb_opt_outer_gen_uq (gbb_to_bb (gw_to_gbb policy)) uq u.
    Fixpoint gw_opt_inner (policy:gw_policy) (uq:gen_user_query) (u:user) :
      (sql_query) := bb_opt_inner_gen_uq (gbb_to_bb (gw_to_gbb policy)) uq u.

    Lemma gw_opt_correct :
      forall u uq p gw_policy,
      gen_sql_query_func uq (gw_policy_map gw_policy p u) =
      andb (sql_query_func (gw_opt_outer gw_policy uq u) (gw_policy_map gw_policy p u))
        (sql_query_func (gw_opt_inner gw_policy uq u) p).
    Proof.
      intros; destruct gw_policy0.
      unfold gw_opt_inner, gw_opt_outer.
      rewrite gw_to_gbb_correct, gbb_to_bb_correct.
      rewrite bb_opt_gen_uq_correct; auto.
    Qed.
  End GeneralizedBlackWhiteListOpts.

  (********************************************************)
  (* General list membership *)
  (********************************************************)
  Section GeneralizedListMembership.
    Fixpoint gbb_policy_scrub policy u db : database :=
      map (fun p => gbb_policy_map policy p u) db.

    Lemma gbb_opt_list_correct :
    forall uq u db policy p,
      In p (sql_query_filter (gbb_opt_outer policy uq u)
        (gbb_policy_scrub policy u (sql_query_filter (gbb_opt_inner policy uq u) db)
      )) <->
      In p (sql_query_filter (gen_to_sql uq) (gbb_policy_scrub policy u db)).
    Proof.
      split; intros; destruct policy; unfold sql_query_filter, gbb_policy_scrub in *;
      apply filter_In in H; apply filter_In; destruct_conjs;
      apply in_map_iff in H; destruct_conjs;
      [ apply filter_In in H2; destruct_conjs | ]; split.
      - apply in_map_iff; exists H; now firstorder.
      - rewrite <- H1 in *. rewrite gen_to_sql_correct.
        rewrite gbb_opt_correct; now firstorder.
      - apply in_map_iff; exists H; split; auto.
        apply filter_In; split; auto.
        rewrite gen_to_sql_correct in H0; rewrite <- H1 in H0.
        rewrite gbb_opt_correct in H0; now firstorder.
      - rewrite gen_to_sql_correct in H0; rewrite <- H1 in H0.
        rewrite gbb_opt_correct in H0; now firstorder.
    Qed.

    Fixpoint gw_policy_scrub policy u db : database :=
      map (fun p => gw_policy_map policy p u) db.

    Lemma gw_opt_list_correct :
    forall uq u db policy p,
      In p (sql_query_filter (gw_opt_outer policy uq u)
        (gw_policy_scrub policy u (sql_query_filter (gw_opt_inner policy uq u) db)
      )) <->
      In p (sql_query_filter (gen_to_sql uq) (gw_policy_scrub policy u db)).
    Proof.
      split; intros; destruct policy; unfold sql_query_filter, gw_policy_scrub in *;
      apply filter_In in H; apply filter_In; destruct_conjs;
      apply in_map_iff in H; destruct_conjs;
      [ apply filter_In in H2; destruct_conjs | ]; split.
      - apply in_map_iff; exists H; now firstorder.
      - rewrite <- H1 in *. rewrite gen_to_sql_correct.
        rewrite gw_opt_correct; now firstorder.
      - apply in_map_iff; exists H; split; auto.
        apply filter_In; split; auto.
        rewrite gen_to_sql_correct in H0; rewrite <- H1 in H0.
        rewrite gw_opt_correct in H0; now firstorder.
      - rewrite gen_to_sql_correct in H0; rewrite <- H1 in H0.
        rewrite gw_opt_correct in H0; now firstorder.
    Qed.
  End GeneralizedListMembership.

End HotCRP.