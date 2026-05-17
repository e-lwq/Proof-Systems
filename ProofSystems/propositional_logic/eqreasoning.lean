import ProofSystems.propositional_logic.definitions
import ProofSystems.propositional_logic.boolaxioms
import ProofSystems.propositional_logic.SATsolver
set_option linter.style.longLine false

open Formula
open List


axiom correctAxioms {Var : Type} [DecidableEq Var] : (∀ (rule : Rule (Var := Var)), logicEquiv (genPair rule).1 (genPair rule).2)

theorem correctness_of_1step {Var : Type} [DecidableEq Var] (step : dstep (Var := Var)) : logicEquiv step.LHS step.RHS := by
  rw [logicEquiv]
  have cd := step.correct_deriv
  unfold correct_deriv_type at cd
  intro val
  rw [← cd]
  have hrule := correctAxioms step.rule
  apply substitution_thm
  exact hrule

theorem forall_lemma {α : Type} (p : α → Prop) (ss : List α)
  : Forall p ss → Forall p ss.tail := by
  intro hp
  match ss with
  | [] => simp
  | x :: xs => simp? at *; exact hp.right

theorem zip_lemma {α : Type} (s : α) (ss : List α) (notnull : ss ≠ [])
  : tail (myZip (s::ss) ss) = myZip ss (tail ss) := by
    cases ss with
    | nil => contradiction
    | cons x xs =>
      rw [myZip]
      simp

theorem tmp_lemma {Var : Type} [DecidableEq Var] (step : dstep (Var := Var)) (ss : List (dstep)) (hchain : Forall pairfun (myZip (step :: ss) ss))
  : Forall pairfun (myZip (step :: ss) ss).tail
  := forall_lemma pairfun (myZip (step :: ss) ss) hchain

theorem step1RHS_eq_step2LHS_lemma {Var : Type} [DecidableEq Var] (step1 : dstep (Var := Var)) (step2 : dstep (Var := Var)) (ss : List dstep) (hchain : Forall pairfun (myZip (step1 :: step2 :: ss) (step2 :: ss)))
  : step1.RHS = step2.LHS := by
  unfold Forall at *
  unfold myZip at *
  cases hzip : (myZip (step2 :: ss) ss) with
  | nil =>
    simp? [hzip] at hchain
    unfold pairfun at hchain
    simp? at hchain
    exact hchain
  | cons y ys =>
    simp [hzip] at hchain
    have hl := hchain.left
    unfold pairfun at hl
    simp? at hl
    exact hl

theorem EqReasoning_Soundness {Var : Type} [DecidableEq Var] (deriv : derivation (Var := Var))
  : logicEquiv (deriv.steps.head deriv.notnull).LHS (deriv.steps.getLast deriv.notnull).RHS := by
  cases deriv with
  | mk steps hchain notnull =>
    revert hchain notnull
    induction steps with
    | nil =>
      intro hchain notnull
      contradiction
    | cons step ss ih' =>
      intro hchain notnull
      -- break hchain
      unfold hchain_type at *
      simp?
      have hchain' : Forall pairfun ((myZip (step :: ss) ss).tail) := tmp_lemma step ss hchain
      cases ss with
      | nil =>
        simp?
        exact correctness_of_1step step
      | cons step2 ss2 =>
        have notnull_ss : (step2 :: ss2) ≠ [] := by simp
        rw [zip_lemma step (step2 :: ss2) notnull_ss] at hchain'
        have ih := ih' hchain' notnull_ss
        simp?
        have hstep := correctness_of_1step step
        have := step1RHS_eq_step2LHS_lemma step step2 ss2 hchain
        rw [this] at hstep
        exact logicEquiv.transitive hstep ih

axiom logicEquiv_sameDNF {Var : Type} [DecidableEq Var] (F G : Formula Var) : logicEquiv F G ↔ findDNF F = findDNF G
