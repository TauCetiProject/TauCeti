/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Abstract variational equations

This file packages Mathlib's Lax-Milgram theorem in the form used by weak formulations of
elliptic PDEs: a coercive bounded bilinear form `B` on a real Hilbert space has a unique
solution `u` to

`B u v = ℓ v`

for every continuous linear functional `ℓ` and every test vector `v`.

Mathlib's `IsCoercive.continuousLinearEquivOfBilin` gives the operator associated to `B`,
while `InnerProductSpace.toDual` supplies the Fréchet-Riesz representative of `ℓ`. The lemmas
below only connect those two existing pieces.
-/

namespace TauCeti

noncomputable section

namespace Variational

open InnerProductSpace

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A vector whose coercive bilinear form vanishes on the diagonal is zero. -/
lemma eq_zero_of_apply_self_eq_zero (hB : IsCoercive B) {u : V} (hu : B u u = 0) :
    u = 0 := by
  rcases hB with ⟨C, C_pos, hcoercive⟩
  rw [← norm_eq_zero, ← mul_self_eq_zero, ← mul_right_inj' C_pos.ne', mul_zero,
    ← mul_assoc]
  refine le_antisymm ?_ ?_
  · calc
      C * ‖u‖ * ‖u‖ ≤ B u u := hcoercive u
      _ = 0 := hu
  · positivity

/-- A coercive bilinear variational equation with zero right-hand side has only the zero
solution. -/
lemma eq_zero_of_forall_apply_eq_zero (hB : IsCoercive B) {u : V}
    (hu : ∀ v, B u v = 0) :
    u = 0 :=
  eq_zero_of_apply_self_eq_zero hB (hu u)

/-- Two vectors satisfying the same variational equation are equal. -/
lemma eq_of_forall_apply_eq_of_forall_apply_eq (hB : IsCoercive B) {f : V → ℝ}
    {u₁ u₂ : V} (hu₁ : ∀ v, B u₁ v = f v) (hu₂ : ∀ v, B u₂ v = f v) :
    u₁ = u₂ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_apply_self_eq_zero hB ?_
  simp [hu₁ (u₁ - u₂), hu₂ (u₁ - u₂)]

end Uniqueness

section Solution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}
variable [CompleteSpace V]

/-- The weak solution of the abstract variational equation associated to a coercive bilinear
form and a continuous linear functional.

It is the inverse image, under the Lax-Milgram operator associated to `B`, of the
Fréchet-Riesz representative of `ℓ`. -/
def solution (hB : IsCoercive B) (ℓ : StrongDual ℝ V) : V :=
  hB.continuousLinearEquivOfBilin.symm ((toDual ℝ V).symm ℓ)

/-- Applying the Lax-Milgram operator to the variational solution gives the Riesz
representative of the right-hand side. -/
@[simp]
lemma continuousLinearEquivOfBilin_solution (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    hB.continuousLinearEquivOfBilin (solution hB ℓ) = (toDual ℝ V).symm ℓ := by
  simp [solution]

/-- The variational solution solves `B u v = ℓ v` for every test vector `v`. -/
@[simp]
lemma solution_spec (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (solution hB ℓ) v = ℓ v := by
  rw [← toDual_symm_apply (𝕜 := ℝ) (E := V) (x := v) (y := ℓ),
    ← continuousLinearEquivOfBilin_solution hB ℓ]
  exact (hB.continuousLinearEquivOfBilin_apply (solution hB ℓ) v).symm

/-- A vector satisfying the variational equation is the Lax-Milgram solution. -/
lemma eq_solution_of_forall_apply_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) {u : V}
    (hu : ∀ v, B u v = ℓ v) :
    u = solution hB ℓ := by
  let r := (toDual ℝ V).symm ℓ
  have hr : r = hB.continuousLinearEquivOfBilin u := by
    refine hB.unique_continuousLinearEquivOfBilin ?_
    intro v
    rw [toDual_symm_apply (𝕜 := ℝ) (E := V), hu]
  calc
    u = hB.continuousLinearEquivOfBilin.symm (hB.continuousLinearEquivOfBilin u) := by
      exact (hB.continuousLinearEquivOfBilin.symm_apply_apply u).symm
    _ = hB.continuousLinearEquivOfBilin.symm r := by rw [← hr]
    _ = solution hB ℓ := rfl

/-- Existence and uniqueness of the solution to the abstract variational equation. -/
theorem existsUnique_forall_apply_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v, B u v = ℓ v := by
  refine ⟨solution hB ℓ, ?_, ?_⟩
  · intro v
    exact solution_spec hB ℓ v
  · intro u hu
    exact eq_solution_of_forall_apply_eq hB ℓ hu

/-- The solution for the zero functional is zero. -/
@[simp]
lemma solution_zero (hB : IsCoercive B) :
    solution hB (0 : StrongDual ℝ V) = 0 := by
  exact eq_zero_of_forall_apply_eq_zero hB (u := solution hB 0) (by simp [solution_spec hB])

/-- The solution operator taking a continuous linear functional to the corresponding
variational solution. -/
def solutionCLM (hB : IsCoercive B) : StrongDual ℝ V →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
lemma solutionCLM_apply (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    solutionCLM hB ℓ = solution hB ℓ :=
  rfl

/-- The solution depends linearly on the continuous functional. -/
lemma solution_add (hB : IsCoercive B) (ℓ₁ ℓ₂ : StrongDual ℝ V) :
    solution hB (ℓ₁ + ℓ₂) = solution hB ℓ₁ + solution hB ℓ₂ := by
  exact (solutionCLM hB).map_add ℓ₁ ℓ₂

/-- The solution commutes with scalar multiplication of the continuous functional. -/
lemma solution_smul (hB : IsCoercive B) (c : ℝ) (ℓ : StrongDual ℝ V) :
    solution hB (c • ℓ) = c • solution hB ℓ := by
  exact (solutionCLM hB).map_smul c ℓ

/-- The solution for the negated right-hand side is the negated solution. -/
lemma solution_neg (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    solution hB (-ℓ) = -solution hB ℓ := by
  exact (solutionCLM hB).map_neg ℓ

/-- The solution of the difference of right-hand sides is the difference of the solutions. -/
lemma solution_sub (hB : IsCoercive B) (ℓ₁ ℓ₂ : StrongDual ℝ V) :
    solution hB (ℓ₁ - ℓ₂) = solution hB ℓ₁ - solution hB ℓ₂ := by
  exact (solutionCLM hB).map_sub ℓ₁ ℓ₂

end Solution

end Variational

end

end TauCeti
