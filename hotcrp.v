Require Import Bool Arith List Omega String.
Require Import Recdef.
Require Import Program.Tactics.
Import ListNotations.

(*  Overall architecture:
     *)

Inductive user : Set :=
| User: forall (id:nat) (email:string) (teams:list nat), user.
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
  Inductive sql_query : Set :=
  | Sql_true: sql_query
  | Sql_false: sql_query
  | Paper_id: nat -> sql_query
  | Paper_title: string -> sql_query
  | Paper_team: nat -> sql_query
  | Paper_decision: nat -> sql_query
  | And: sql_query -> sql_query -> sql_query
  | Or: sql_query -> sql_query -> sql_query
  | Not: sql_query -> sql_query.

  (*  Now define a computational version. *)
  Fixpoint sql_query_func (q:sql_query) (p:paper) : bool :=
  match p with
  | Paper p_id p_title p_team p_decision =>
    match q with
    | Sql_true => true
    | Sql_false => false
    | Paper_id id => beq_nat p_id id
    | Paper_title title => if string_dec p_title title then true else false
    | Paper_team team => beq_nat p_team team
    | Paper_decision decision => beq_nat p_decision decision
    | And q1 q2 => andb (sql_query_func q1 p) (sql_query_func q2 p)
    | Or q1 q2 => orb (sql_query_func q1 p) (sql_query_func q2 p)
    | Not q1 => negb (sql_query_func q1 p)
    end
  end.

  (* Some baby test cases. *)
  Definition empty_paper := (Paper 0 "" 0 0).
  Eval compute in sql_query_func (Sql_true) empty_paper.
  Eval compute in sql_query_func (Sql_false) empty_paper.
  Eval compute in sql_query_func (Paper_id 10) empty_paper.
  Definition paper10 := (Paper 10 "paper_10" 10 0).
  Eval compute in sql_query_func (Paper_id 10) paper10.
  Eval compute in sql_query_func (Paper_title "paper_10") paper10.
  Definition paper10query := (And (Paper_id 10) (Paper_team 10)).
  Eval compute in sql_query_func paper10query empty_paper.
  Eval compute in sql_query_func paper10query paper10.

  Definition sql_query_filter db q : database :=
    filter (fun p => sql_query_func q p) db.

  (* Some test cases. *)
  Definition testdb := [(Paper 0 "0" 0 0);(Paper 1 "hi" 0 0);(Paper 2 "yo" 0 1);
                        (Paper 3 "naw" 2 0);(Paper 4 "P=NP" 2 1);
                        (Paper 6 "hotcrp" 3 2)].
  Definition team0query := (Paper_team 0).
  Definition team2query := (Paper_team 2).
  Definition decision1query := (Paper_decision 1).
  Eval compute in sql_query_filter testdb team0query.
  Eval compute in sql_query_filter testdb team2query.
  Eval compute in sql_query_filter testdb decision1query.
  Eval compute in sql_query_filter testdb (And (Not decision1query) team2query).
  Eval compute in sql_query_filter testdb (Or (Not decision1query) team0query).
End SQL.

Section Policy.
  (* Scrub out the decision and put 0 in *)
  Fixpoint policy_map (p:paper) (u:user) : paper :=
  match u with
  | User _ _ u_teams => 
    match p with
    | Paper p_id p_title p_team p_decision =>
      if in_dec eq_nat_dec p_team u_teams then Paper p_id p_title p_team 0 else p
    end
  end.

  Definition policy_scrub u db : database :=
    map (fun p => policy_map p u) db.

  Definition team0user := (User 0 "dan@dan" [0;3]).
  Definition team2user := (User 1 "richard@richard" [2;3]).
  Eval compute in policy_scrub team0user testdb.
  Eval compute in policy_scrub team2user testdb.
End Policy.

(* TODO: define user queries *)
(* TODO: define optimizations moving user queries across optimization *)
(* TODO: generalize policies *)
(* TODO: define a generalized optimization function *)