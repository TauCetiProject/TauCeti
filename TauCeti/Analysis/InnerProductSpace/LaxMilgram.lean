/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Existence and uniqueness form of Lax--Milgram

Mathlib's Lax--Milgram theorem is packaged as
`IsCoercive.continuousLinearEquivOfBilin`: a coercive continuous bilinear form
`B : V →L[ℝ] V →L[ℝ] ℝ` induces a continuous linear equivalence `V ≃L[ℝ] V` sending
`u` to the Riesz representative of the functional `v ↦ B u v`.

The variational formulation of coercive equations uses the corresponding solution API:
given a forcing functional `ℓ`, there is a unique `u` satisfying `B u v = ℓ v` for every test
vector `v`. This file records that existence/uniqueness form, both for forcing represented by a
vector `F` (`ℓ = ⟪F, ·⟫`) and for an arbitrary continuous linear functional.

The same equation restricted to a subspace `S` has a Galerkin solution `w ∈ S`, characterised by
`B (u - w) y = 0` for every `y ∈ S`. Céa's lemma bounds its error by the best approximation error
in `S`, up to the factor `M / C`, where `M` bounds `B` and `C` is its coercivity constant; this is
how solutions of the equation on an increasing family of subspaces with dense union are shown to
converge.

## Main declarations

* `IsCoercive.apply_self_nonneg`: coercive forms have nonnegative diagonal.
* `IsCoercive.solutionOfInner`: the solution of the variational equation with forcing
  represented by `F`.
* `IsCoercive.apply_solutionOfInner_eq_inner`: the defining variational identity.
* `IsCoercive.eq_solutionOfInner`: uniqueness of a vector satisfying the variational
  identity.
* `IsCoercive.existsUnique_forall_eq_inner`: the combined existence-and-uniqueness theorem.
* `IsCoercive.solutionOfFunctional`: the solution map on the strong dual, as a continuous
  linear map, obtained through the Fréchet--Riesz representation.
* `IsCoercive.apply_solutionOfFunctional_eq`, `IsCoercive.eq_solutionOfFunctional` and
  `IsCoercive.existsUnique_forall_eq`: the same API for an arbitrary continuous linear
  functional.
* `LinearMap.norm_sub_le_div_mul_norm_sub`: Céa's lemma, `‖u - w‖ ≤ M / C * ‖u - v‖` for the
  Galerkin solution `w` and every `v` in the subspace, where `M` bounds `B`.

## References

* J. Céa, *Approximation variationnelle des problèmes aux limites*, Ann. Inst. Fourier 14 (1964),
  345–444.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace IsCoercive

section Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- A coercive form has nonnegative diagonal. -/
theorem apply_self_nonneg (hB : IsCoercive B) (v : V) : 0 ≤ B v v :=
  let ⟨C, hC, hle⟩ := hB
  (by positivity : 0 ≤ C * ‖v‖ * ‖v‖).trans (hle v)

end Seminormed

end IsCoercive

namespace LinearMap

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Céa's lemma.** Let `B` be a bilinear form with `B x y ≤ M ‖x‖ ‖y‖` and `C ‖x‖² ≤ B x x`
for some `C > 0`, and let `w` be a Galerkin approximation of `u` in a subspace `S`: `w ∈ S` and
`B (u - w) y = 0` for every `y ∈ S`. Then `w` is within the factor `M / C` of the best
approximation of `u` in `S`: `‖u - w‖ ≤ M / C * ‖u - v‖` for every `v ∈ S`. -/
theorem norm_sub_le_div_mul_norm_sub (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {C M : ℝ} (hC : 0 < C)
    (hle : ∀ x, C * ‖x‖ * ‖x‖ ≤ B x x) (hM : ∀ x y, B x y ≤ M * ‖x‖ * ‖y‖)
    {S : Submodule ℝ V} {u w v : V} (hw : w ∈ S) (hv : v ∈ S)
    (horth : ∀ y ∈ S, B (u - w) y = 0) : ‖u - w‖ ≤ M / C * ‖u - v‖ := by
  -- Galerkin orthogonality: `B (u - w) (u - w) = B (u - w) (u - v)`, since `v - w ∈ S`.
  have hsplit : B (u - w) (u - w) = B (u - w) (u - v) := by
    conv_lhs => rw [← sub_add_sub_cancel u v w, map_add]
    rw [sub_add_sub_cancel, horth _ (S.sub_mem hv hw), add_zero]
  have key : C * ‖u - w‖ * ‖u - w‖ ≤ M * ‖u - w‖ * ‖u - v‖ :=
    (hle _).trans (hsplit ▸ hM _ _)
  -- Coercivity and the bound at `u - v` give `C ≤ M` unless `‖u - v‖ = 0`.
  have hd : C * ‖u - v‖ * ‖u - v‖ ≤ M * ‖u - v‖ * ‖u - v‖ := (hle _).trans (hM _ _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hC]
  rcases (norm_nonneg (u - w)).eq_or_lt with h | h
  · rw [← h, zero_mul]
    rcases (norm_nonneg (u - v)).eq_or_lt with h' | h'
    · rw [← h', mul_zero]
    · have hCM : C ≤ M := le_of_mul_le_mul_right (by simpa only [mul_assoc] using hd)
        (mul_pos h' h')
      exact mul_nonneg (hC.le.trans hCM) h'.le
  · nlinarith

end LinearMap

namespace IsCoercive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The solution supplied by Lax--Milgram for a represented forcing functional.

For `F : V`, `solutionOfInner hB F` is the unique vector `u` satisfying
`B u v = ⟪F, v⟫` for every `v`. -/
def solutionOfInner (hB : IsCoercive B) (F : V) : V :=
  hB.continuousLinearEquivOfBilin.symm F

/-- The represented-forcing solution is the inverse Lax--Milgram operator. -/
theorem solutionOfInner_def (hB : IsCoercive B) (F : V) :
    solutionOfInner hB F = hB.continuousLinearEquivOfBilin.symm F :=
  (rfl)

/-- Applying the Lax--Milgram equivalence to the represented-forcing solution returns the
forcing vector. -/
@[simp]
theorem continuousLinearEquivOfBilin_solutionOfInner (hB : IsCoercive B) (F : V) :
    hB.continuousLinearEquivOfBilin (solutionOfInner hB F) = F := by
  simp [solutionOfInner_def]

/-- Solving against the forcing represented by a Lax--Milgram image recovers the original
vector. -/
@[simp]
theorem solutionOfInner_continuousLinearEquivOfBilin (hB : IsCoercive B) (u : V) :
    solutionOfInner hB (hB.continuousLinearEquivOfBilin u) = u := by
  simp [solutionOfInner_def]

/-- The Lax--Milgram solution satisfies the variational equation. -/
@[simp]
theorem apply_solutionOfInner_eq_inner (hB : IsCoercive B) (F v : V) :
    B (solutionOfInner hB F) v = ⟪F, v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply, continuousLinearEquivOfBilin_solutionOfInner]

/-- A vector satisfying the represented variational equation is the Lax--Milgram solution. -/
theorem eq_solutionOfInner (hB : IsCoercive B) {F u : V} (hu : ∀ v : V, B u v = ⟪F, v⟫_ℝ) :
    u = solutionOfInner hB F := by
  rw [solutionOfInner_def, ContinuousLinearEquiv.eq_symm_apply]
  exact (hB.unique_continuousLinearEquivOfBilin fun v => (hu v).symm).symm

/-- Lax--Milgram as an existence-and-uniqueness theorem for represented functionals.

If `B` is coercive, then for every `F : V` there is a unique `u` such that
`B u v = ⟪F, v⟫` for all test vectors `v`. -/
theorem existsUnique_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃! u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  ⟨solutionOfInner hB F, apply_solutionOfInner_eq_inner hB F,
    fun _ hu => eq_solutionOfInner hB hu⟩

/-- Lax--Milgram as an existence theorem for represented functionals. -/
theorem exists_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃ u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  (existsUnique_forall_eq_inner hB F).exists

/-- The Lax--Milgram solution map on continuous linear functionals, as a continuous linear map.

It sends `ℓ` to the unique vector `u` satisfying `B u v = ℓ v` for every `v`: this is
`solutionOfInner` applied to the Fréchet--Riesz representative of `ℓ`. -/
def solutionOfFunctional (hB : IsCoercive B) : StrongDual ℝ V →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The functional solution is obtained by solving against the Fréchet--Riesz representative. -/
theorem solutionOfFunctional_apply (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    solutionOfFunctional hB ℓ =
      solutionOfInner hB ((InnerProductSpace.toDual ℝ V).symm ℓ) :=
  (rfl)

/-- For represented functionals, the functional solution agrees with `solutionOfInner`. -/
@[simp]
theorem solutionOfFunctional_toDual (hB : IsCoercive B) (F : V) :
    solutionOfFunctional hB ((InnerProductSpace.toDual ℝ V) F) = solutionOfInner hB F := by
  simp [solutionOfFunctional_apply]

/-- The Lax--Milgram solution for a continuous linear functional satisfies the variational
equation. -/
@[simp]
theorem apply_solutionOfFunctional_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (solutionOfFunctional hB ℓ) v = ℓ v := by
  rw [solutionOfFunctional_apply, apply_solutionOfInner_eq_inner,
    InnerProductSpace.toDual_symm_apply]

/-- A vector satisfying the variational equation for a continuous linear functional is the
Lax--Milgram solution for that functional. -/
theorem eq_solutionOfFunctional (hB : IsCoercive B) {ℓ : StrongDual ℝ V} {u : V}
    (hu : ∀ v : V, B u v = ℓ v) :
    u = solutionOfFunctional hB ℓ := by
  rw [solutionOfFunctional_apply]
  exact eq_solutionOfInner hB fun v => by rw [hu, InnerProductSpace.toDual_symm_apply]

/-- Lax--Milgram as an existence-and-uniqueness theorem for arbitrary continuous linear
functionals. -/
theorem existsUnique_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨solutionOfFunctional hB ℓ, apply_solutionOfFunctional_eq hB ℓ,
    fun _ hu => eq_solutionOfFunctional hB hu⟩

/-- Lax--Milgram as an existence theorem for arbitrary continuous linear functionals. -/
theorem exists_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V, B u v = ℓ v :=
  (existsUnique_forall_eq hB ℓ).exists

end IsCoercive
