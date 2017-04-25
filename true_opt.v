Require Import Bool Arith List Omega String.
Require Import Recdef.
Require Import Program.Tactics.
Import ListNotations.

Load hotcrp.

(* An optimization that replaces everything
touched by the policy map with Sql_true *)

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
