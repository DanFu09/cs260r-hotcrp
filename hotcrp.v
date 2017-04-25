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

  Section UserQueries.
    Notation user_query := sql_query.
  End UserQueries.

  (* TODO: define optimizations moving user queries across optimization *)

  (* TODO: generalize policies *)
  (* TODO: define a generalized optimization function *)

End HotCRP.