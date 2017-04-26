Require Import Bool Arith List Omega String.
Require Import Recdef.
Require Import Program.Tactics.
Import ListNotations.

(*  Overall architecture:
     *)

Module HotCRP.
  Inductive user : Set :=
  | User: forall (id:nat) (email:string) (team: nat), user.
  Hint Constructors user.

  Inductive paper : Set :=
  | Paper: forall (id:nat) (title:string)
            (team:nat) (decision:nat), paper.
  Hint Constructors paper.

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

  Section Policy.
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
  End Policy.

  Notation user_query := sql_query.

  Section Optimization.
    (* A simple optimization for simple_policy_map:
    Move the entire user query into SQL, and replace any instance of
    (Decision = x) with
    (Team = u.team && 0 = x) || (Decision = x && !(Team = u.team)) *)
    Fixpoint simple_optimization (uq:user_query) (u:user) :
      (user_query * sql_query) :=
      match u with
      | User _ _ team =>
        match uq with
        | Field_eq (Paper_decision x) =>
            (Sql_true,
            Or (And (Field_eq (Paper_team team)) (Field_eq (Paper_decision 0)))
              (And uq (Field_neq (Paper_team team))))
        | Field_neq (Paper_decision x) =>
            (Sql_true,
            Or (And (Field_eq (Paper_team team)) (Field_neq (Paper_decision 0)))
               (And uq (Field_neq (Paper_team team))))
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

    Lemma simple_optimization_and (uq1:user_query) (uq2:user_query)
      (u:user) (db:database) (p:paper):
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq1 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq2 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization (And uq1 uq2) u)) db)).
    Admitted.

    Lemma simple_optimization_or_left (uq1:user_query) (uq2:user_query)
      (u:user) (db:database) (p:paper):
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq1 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization (Or uq1 uq2) u)) db)).
    Admitted.

    Lemma simple_optimization_or_right (uq1:user_query) (uq2:user_query)
      (u:user) (db:database) (p:paper):
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization uq2 u)) db)) ->
      In p (simple_policy_scrub u
        (sql_query_filter (snd (simple_optimization (Or uq1 uq2) u)) db)).
    Admitted.

    Lemma simple_optimization_no_loss :
      forall uq u db p,
      In p (sql_query_filter uq (simple_policy_scrub u db)) ->
      In p (sql_query_filter (fst (simple_optimization uq u))
        (simple_policy_scrub u (sql_query_filter (snd (simple_optimization uq u)) db)
      )).
    Proof.
      unfold sql_query_filter; split; intros; rewrite filter_In in *; destruct u.
      - (* First direction *)
        split; destruct_conjs.
      --  induction uq.
      --- unfold simple_optimization; simpl; try rewrite true_filter; auto.
      --- unfold sql_query_func in H0; discriminate.
      --- (* Field_eq case *)
          unfold simple_policy_scrub in *; unfold simple_policy_map in *.
          rewrite in_map_iff in H; destruct_conjs. destruct H.
          destruct (Nat.eq_dec team0 team).
      ----  rewrite e in *. rewrite <- beq_nat_refl in H1;
            destruct p0; unfold simple_optimization; unfold snd; auto;
            apply in_map_iff; exists (Paper id0 title team decision);
            rewrite <- beq_nat_refl; split; auto; apply filter_In; split;
            auto; rewrite <- H1 in H0;
            unfold sql_query_func in *; unfold beq_field in *; auto;
            rewrite <- beq_nat_refl; auto.
      ----  assert (team0 =? team = false). apply Nat.eqb_neq; auto.
            rewrite H in H1.
            apply in_map_iff. exists p; split.
            rewrite <- H1. rewrite H; auto.
            apply filter_In; split. rewrite <- H1; auto.
            destruct p0.
            1, 2, 3: unfold simple_optimization; unfold snd; auto.
            1: unfold simple_optimization; unfold snd;
            unfold sql_query_func in *; unfold beq_field in *; rewrite <- H1 in *;
            rewrite H0; rewrite H; auto.
      --- (* Field_neq case - EXACT SAME, but I don't know how to use semicolons *)
          unfold simple_policy_scrub in *; unfold simple_policy_map in *.
          rewrite in_map_iff in H; destruct_conjs. destruct H.
          destruct (Nat.eq_dec team0 team).
      ----  rewrite e in *. rewrite <- beq_nat_refl in H1;
            destruct p0; unfold simple_optimization; unfold snd; auto;
            apply in_map_iff; exists (Paper id0 title team decision);
            rewrite <- beq_nat_refl; split; auto; apply filter_In; split;
            auto; rewrite <- H1 in H0;
            unfold sql_query_func in *; unfold beq_field in *; auto;
            rewrite <- beq_nat_refl; auto.
      ----  assert (team0 =? team = false). apply Nat.eqb_neq; auto.
            rewrite H in H1.
            apply in_map_iff. exists p; split.
            rewrite <- H1. rewrite H; auto.
            apply filter_In; split. rewrite <- H1; auto.
            destruct p0.
            1, 2, 3: unfold simple_optimization; unfold snd; auto.
            1: unfold simple_optimization; unfold snd;
            unfold sql_query_func in *; unfold beq_field in *; rewrite <- H1 in *;
            rewrite H0; rewrite H; auto.
      --- assert (sql_query_func uq1 p = true). unfold sql_query_func in *.
          apply andb_true_iff in H0; destruct_conjs; auto.
          assert (sql_query_func uq2 p = true). unfold sql_query_func in *.
          apply andb_true_iff in H0; destruct_conjs; auto.
          destruct H1. destruct H2.
          apply simple_optimization_and with (uq1:=uq1) (uq2:=uq2)
          (u:=(User id email team)) (db:=db) (p:=p);
          unfold sql_query_filter.
          apply IHuq1; auto.
          apply IHuq2; auto.
      --- unfold sql_query_func in H0. apply orb_true_iff in H0.
          induction H0.
      ----  assert (sql_query_func uq1 p = true); auto.
            apply simple_optimization_or_left with (uq1:=uq1) (uq2:=uq2)
            (u:=(User id email team)) (db:=db) (p:=p).
            apply IHuq1; auto.
      ----  assert (sql_query_func uq2 p = true); auto.
            apply simple_optimization_or_right with (uq1:=uq1) (uq2:=uq2)
            (u:=(User id email team)) (db:=db) (p:=p).
            apply IHuq2; auto.
      --  destruct uq; auto; destruct p0; simpl; auto.
    Admitted.

    Lemma simple_optimization_no_extra :
      forall uq u db p,
      In p (sql_query_filter (fst (simple_optimization uq u))
        (simple_policy_scrub u (sql_query_filter (snd (simple_optimization uq u)) db)
      )) ->
      In p (sql_query_filter uq (simple_policy_scrub u db)).
    Proof.
      - (* Second direction *)
        split; destruct_conjs.
      --  admit.
      --  destruct uq; auto; unfold simple_optimization in H0; simpl in H0.
      --- unfold simple_optimization in H; simpl in H; rewrite false_filter in H;
          unfold simple_policy_scrub in H; simpl in H; contradiction.
      --- admit.
      --- admit.
      --- admit.
      --- admit.
    Admitted.
  End Optimization.

  (* TODO: generalize policies *)
  (* TODO: define a generalized optimization function *)

End HotCRP.