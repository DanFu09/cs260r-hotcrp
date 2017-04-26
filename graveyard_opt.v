Require Import Bool Arith List Omega String.
Require Import Recdef.
Require Import Program.Tactics.
Import ListNotations.

(* Graveyard of bad optimizations *)

(* For simple_policy_map:
Move the entire user query into SQL, and replace any instance of
(Decision = x) with
(Team = u.team) || (Decision = x && !(Team = u.team)) *)
Fixpoint simple_optimization (uq:user_query) (u:user) :
  (user_query * sql_query) :=
  match u with
  | User _ _ team =>
    match uq with
    | Field_eq (Paper_decision x) =>
        (Sql_true,
        Or (Field_eq (Paper_team team))
          (And uq (Field_neq (Paper_team team))))
    | Field_neq (Paper_decision x) =>
        (Sql_true,
        Or (Field_eq (Paper_team team))
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

(* For simple_policy_map:
Move the entire user query into SQL, and replace any instance of
(Decision = x) with
(Team = u.team && Decision = 0) || (Decision = x && !(Team = u.team)) *)
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

(* A simple optimization for simple_policy_map:
Move the entire user query into SQL, and replace any instance of
(Decision = x) with
(Team = u.team && 0 = x) || (Decision = x && !(Team = u.team)) and
(Decision != x) with
(Team = u.team && 0 = x) || (Decision != x && !(Team = u.team))*)
Fixpoint simple_optimization (uq:user_query) (u:user) :
  (user_query * sql_query) :=
  match u with
  | User _ _ team =>
    match uq with
    | Field_eq (Paper_decision x) =>
        (Sql_true,
        if (Nat.eqb x 0) then
        Or (Field_eq (Paper_team team))
          (And uq (Field_neq (Paper_team team))) else
        And uq (Field_neq (Paper_team team)))
    | Field_neq (Paper_decision x) =>
        (Sql_true,
        if (Nat.eqb x 0) then
        Or (Field_eq (Paper_team team))
          (And uq (Field_neq (Paper_team team))) else
        And uq (Field_neq (Paper_team team)))
    | And q1 q2 =>
        (Sql_true,
        And (snd (simple_optimization q1 u)) (snd (simple_optimization q2 u)))
    | Or q1 q2 =>
        (Sql_true,
        Or (snd (simple_optimization q1 u)) (snd (simple_optimization q2 u)))
    | _ => (Sql_true, uq)
    end
  end.