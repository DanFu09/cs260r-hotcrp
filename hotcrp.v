Require Import Bool Arith List Omega String.
Require Import Recdef.
Require Import Program.Tactics.
Import ListNotations.

(*  Overall architecture:
     *)

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

  Definition sql_query_filter db q : database :=
    filter (fun p => sql_query_func q p) db.

  (* Some test cases. *)
  Definition testdb := [(Paper 0 "0" 0 0);(Paper 1 "hi" 0 0);(Paper 2 "yo" 0 1);
                        (Paper 3 "naw" 2 0);(Paper 4 "P=NP" 2 1);
                        (Paper 6 "hotcrp" 3 2)].
  Definition team0query := (Field_eq (Paper_team 0)).
  Definition team2query := (Field_eq (Paper_team 2)).
  Definition decision1queryeq := (Field_eq (Paper_decision 1)).
  Definition decision1queryneq := (Field_neq (Paper_decision 1)).
  Eval compute in sql_query_filter testdb team0query.
  Eval compute in sql_query_filter testdb team2query.
  Eval compute in sql_query_filter testdb decision1queryeq.
  Eval compute in sql_query_filter testdb (And (decision1queryneq) team2query).
  Eval compute in sql_query_filter testdb (Or (decision1queryneq) team0query).
End SQL.

Section Policy.
  (* Scrub out the decision and put 0 in *)
  Fixpoint policy_map (p:paper) (u:user) : paper :=
  match u with
  | User _ _ u_team => 
    match p with
    | Paper p_id p_title p_team p_decision =>
      if Nat.eqb p_team u_team then Paper p_id p_title p_team 0 else p
    end
  end.

  Definition policy_scrub u db : database :=
    map (fun p => policy_map p u) db.

  Definition team0user := (User 0 "dan@dan" 0).
  Definition team2user := (User 1 "richard@richard" 2).
  Eval compute in policy_scrub team0user testdb.
  Eval compute in policy_scrub team2user testdb.
End Policy.

(* TODO: define user queries - let's just say that they are sql queries *)
(* TODO: define optimizations moving user queries across optimization *)

(* dump opt. wipe out decision from queries *)
Fixpoint dumb_opt_inner (q : sql_query) : sql_query :=
match q with
  | Sql_true => Sql_true
  | Sql_false => Sql_false
  | Field_eq field => 
    match field with
      | Paper_decision d => Sql_true
      | _ => Field_eq field
    end
  | Field_neq field => 
    match field with
      | Paper_decision d => Sql_true
      | _ => Field_neq field
    end
  | And q1 q2 => And (dumb_opt_inner q1) (dumb_opt_inner q2)
  | Or q1 q2 => Or (dumb_opt_inner q1) (dumb_opt_inner q2)
end.

Lemma true_removes_nothing (db : database) (p : paper) : 
  In p db <-> In p (sql_query_filter db Sql_true).
Proof.
  split;
  intros.
  unfold sql_query_filter.
  rewrite filter_In.
  simpl.
  destruct p.
  auto.
  unfold sql_query_filter in H.
  rewrite filter_In in H.
  destruct_pairs.
  auto.
Qed.

Lemma dumb_opt_inner_doesnt_eat (usql : sql_query) (db : database) (p : paper):
  In p (sql_query_filter db usql) -> In p (sql_query_filter db (dumb_opt_inner usql)).
Proof.
  intros.
  induction usql; auto;
  simpl.
  unfold sql_query_filter in *.
  rewrite filter_In in *.
  destruct_pairs.
  simpl in *.
  destruct p0; auto.
  unfold sql_query_filter in *.
  simpl in *.
  rewrite filter_In in *.
  destruct_pairs.
  destruct p0; auto.
  unfold sql_query_filter in *.
  rewrite filter_In in *.
  destruct_pairs.
  simpl in *.
  rewrite andb_true_iff in H0.
  destruct_pairs.
  firstorder.
  rewrite filter_In in *.
  destruct_pairs.
  rewrite andb_true_iff.
  auto.
  unfold sql_query_filter in *.
  simpl in *.
  rewrite filter_In in *.
  destruct p.
  rewrite orb_true_iff in H.
  destruct_pairs.
  firstorder.
  rewrite filter_In in *.
  destruct_pairs.
  rewrite orb_true_iff.
  auto.
  unfold sql_query_filter in *.
  simpl in *.
  rewrite filter_In in *.
  firstorder.
Qed.

Fixpoint dumb_opt_outer (q : sql_query) : sql_query :=
match q with
  | Sql_true => Sql_true
  | Sql_false => Sql_false
  | Field_eq field => 
    match field with
      | Paper_decision d => Field_eq field
      | _ => Sql_true
    end
  | Field_neq field => 
    match field with
      | Paper_decision d => Field_neq field
      | _ => Sql_true
    end
  | And q1 q2 => And (dumb_opt_inner q1) (dumb_opt_inner q2)
  | Or q1 q2 => Or q1 q2
end.

Lemma obvious1 (db : database) :
  (filter (fun _ : paper => true) db) = db.
Proof.
  induction db.
  auto.
  unfold filter in *.
  rewrite IHdb.
  auto.
Qed.

Lemma opt_correct (usql : sql_query) (db : database) (p : paper) (u : user) :
  In p (sql_query_filter (policy_scrub u (sql_query_filter db (dumb_opt_inner usql))) (dumb_opt_outer usql)) <-> 
    In p (sql_query_filter (policy_scrub u db) usql).
Proof.
  split; intros.
  induction usql; simpl.
  unfold sql_query_filter in *.
  rewrite filter_In in *.
  destruct_pairs.
  simpl in *.
  pose (obvious1 db).
  rewrite e in *.
  auto.
  unfold sql_query_filter in *.
  rewrite filter_In in *.
  destruct_pairs.
  simpl in *.
  inversion H0.
  destruct p0.
  unfold sql_query_filter in *.
  rewrite filter_In in H.
  destruct_pairs.
  simpl in *.
  remember (fun p0 : paper => match p0 with
                        | Paper p_id _ _ _ => p_id =? n
                        end).
  unfold policy_scrub in *.
  rewrite in_map_iff in H.
  destruct H.
  destruct_pairs.
  rewrite filter_In.
  rewrite in_map_iff.
  rewrite filter_In in H1.
  destruct_pairs.
  split.
  exists x.
  auto.
  rewrite <- H.
  unfold policy_map.
  destruct x.
  destruct u.
  pose (Sumbool.sumbool_of_bool (Nat.eqb team team0)).
  destruct s.
  rewrite e.
  rewrite Heqb in *.
  auto.
  rewrite e.
  rewrite Heqb in *.
  auto.

  (* redo above with some changes *)
  unfold sql_query_filter in *.
  rewrite filter_In in H.
  destruct_pairs.
  simpl in *.
  remember (fun p0 : paper => match p0 with
                        | Paper _ p_title _ _ => if string_dec p_title s then true else false
                        end).
  unfold policy_scrub in *.
  rewrite in_map_iff in H.
  destruct H.
  destruct_pairs.
  rewrite filter_In.
  rewrite in_map_iff.
  rewrite filter_In in H1.
  destruct_pairs.
  split.
  exists x.
  auto.
  rewrite <- H.
  unfold policy_map.
  destruct x.
  destruct u.
  pose (Sumbool.sumbool_of_bool (Nat.eqb team team0)).
  destruct s0.
  rewrite e.
  rewrite Heqb in *.
  auto.
  rewrite e.
  rewrite Heqb in *.
  auto.
  
  (* ditto *)
  unfold sql_query_filter in *.
  rewrite filter_In in H.
  destruct_pairs.
  simpl in *.
  remember (fun p0 : paper => match p0 with
                        | Paper _ _ p_team _ => p_team =? n
                        end).
  unfold policy_scrub in *.
  rewrite in_map_iff in H.
  destruct H.
  destruct_pairs.
  rewrite filter_In.
  rewrite in_map_iff.
  rewrite filter_In in H1.
  destruct_pairs.
  split.
  exists x.
  auto.
  rewrite <- H.
  unfold policy_map.
  destruct x.
  destruct u.
  pose (Sumbool.sumbool_of_bool (Nat.eqb team team0)).
  destruct s.
  rewrite e.
  rewrite Heqb in *.
  auto.
  rewrite e.
  rewrite Heqb in *.
  auto.

  (* ditto, this one more special because this is the decision scrub branch *)
  unfold sql_query_filter in *.
  rewrite filter_In in H.
  destruct_pairs.
  simpl in *.
  remember (fun p0 : paper => match p0 with
                        | Paper _ _ _ p_decision => p_decision =? n
                        end).
  unfold policy_scrub in *.
  rewrite in_map_iff in H.
  destruct H.
  destruct_pairs.
  rewrite filter_In.
  rewrite in_map_iff.
  rewrite filter_In in H1.
  destruct_pairs.
  split.
  exists x.
  auto.
  rewrite <- H.
  unfold policy_map in *.
  destruct x.
  destruct u.
  pose (Sumbool.sumbool_of_bool (Nat.eqb team team0)).
  destruct s.
  rewrite e in *.
  rewrite Heqb in *.
  rewrite <- H in *.
  auto.
  rewrite e in *.
  rewrite Heqb in *.
  rewrite <- H in *.
  auto.

  (* neq cases - what do? *)
Admitted.

(* Instead do optimization where we code in the policy *)

Example sample_queries :
  
(* TODO: generalize policies *)
(* TODO: define a generalized optimization function *)