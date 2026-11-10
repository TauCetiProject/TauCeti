/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Algebra.Exponential.Polynomial
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Exponentials of bounded operators

This file records facts about the exponential of a continuous linear endomorphism of a normed
space. The norm bounds for exponentials in a general normed algebra live in
`TauCeti/Analysis/Normed/Algebra/Exponential.lean`.

## Main results

* `ContinuousLinearMap.exp_add_smul`, `ContinuousLinearMap.exp_add_smul_apply`: exponentials of
  scalar multiples of a bounded operator compose additively.
* `ContinuousLinearMap.expEquiv`: the exponential of a bounded operator as a continuous linear
  automorphism with inverse `exp (-B)`, with `ContinuousLinearMap.coe_expEquiv` and
  `ContinuousLinearMap.coe_expEquiv_symm` identifying it and its inverse with `exp B` and
  `exp (-B)`.
* `ContinuousLinearMap.exp_apply_of_apply_eq_smul`: the exponential of an operator acts on an
  eigenvector by the scalar exponential of the eigenvalue.
* `ContinuousLinearMap.spectrum_exp`: in finite dimension, the spectrum of `exp N` is the image of
  the spectrum of `N` under the exponential.
* `ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral`: the Duhamel identity
  `exp (t • B) x - x = ∫₀ᵗ exp (u • B) (B x) du` for the orbits of a real bounded operator.
* `ContinuousLinearMap.eq_exp_smul_apply_of_hasDerivWithinAt`: a continuous function on `[0, ∞)`
  with right derivative `A (z t)` is the linear flow `t ↦ exp (t • A) (z 0)` of its initial value.
-/

public section

open NormedSpace

namespace TauCeti

section Operator

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- Exponentials of scalar multiples of the same bounded operator split over addition. -/
theorem _root_.ContinuousLinearMap.exp_add_smul (A : X →L[𝕜] X) (s t : 𝕜) :
    exp ((s + t) • A) = (exp (s • A)).comp (exp (t • A)) := by
  exact (NormedSpace.exp_add_smul A s t).trans (ContinuousLinearMap.mul_def _ _)

/-- Pointwise form of `ContinuousLinearMap.exp_add_smul`:
`exp ((s + t) • A) x = exp (s • A) (exp (t • A) x)`. -/
theorem _root_.ContinuousLinearMap.exp_add_smul_apply (A : X →L[𝕜] X) (s t : 𝕜) (x : X) :
    exp ((s + t) • A) x = exp (s • A) (exp (t • A) x) := by
  rw [ContinuousLinearMap.exp_add_smul, ContinuousLinearMap.comp_apply]

/-- The exponential `exp B` of a continuous endomorphism of a Banach space, as a continuous linear
automorphism with inverse `exp (-B)`. -/
noncomputable def _root_.ContinuousLinearMap.expEquiv (B : X →L[𝕜] X) : X ≃L[𝕜] X :=
  .equivOfInverse' (exp B) (exp (-B))
    (by
      let +nondep : NormedAlgebra ℚ (X →L[𝕜] X) := .restrictScalars ℚ 𝕜 _
      rw [← ContinuousLinearMap.mul_def, ← exp_add_of_commute (Commute.refl B).neg_right,
        add_neg_cancel, exp_zero, ContinuousLinearMap.one_def])
    (by
      let +nondep : NormedAlgebra ℚ (X →L[𝕜] X) := .restrictScalars ℚ 𝕜 _
      rw [← ContinuousLinearMap.mul_def, ← exp_add_of_commute (Commute.refl B).neg_left,
        neg_add_cancel, exp_zero, ContinuousLinearMap.one_def])

@[simp]
theorem _root_.ContinuousLinearMap.expEquiv_apply (B : X →L[𝕜] X) (x : X) :
    B.expEquiv x = exp B x :=
  (rfl)

@[simp]
theorem _root_.ContinuousLinearMap.expEquiv_symm_apply (B : X →L[𝕜] X) (x : X) :
    B.expEquiv.symm x = exp (-B) x :=
  (rfl)

@[simp]
theorem _root_.ContinuousLinearMap.coe_expEquiv (B : X →L[𝕜] X) :
    (B.expEquiv : X →L[𝕜] X) = exp B :=
  ContinuousLinearMap.ext B.expEquiv_apply

@[simp]
theorem _root_.ContinuousLinearMap.coe_expEquiv_symm (B : X →L[𝕜] X) :
    (B.expEquiv.symm : X →L[𝕜] X) = exp (-B) :=
  ContinuousLinearMap.ext B.expEquiv_symm_apply

/-- **The exponential of an operator acts exponentially on an eigenvector.** If `B x = μ • x`,
then `exp B x = exp μ • x`. The statement also covers `x = 0`, without requiring a bundled
`Module.End.HasEigenvector` witness. -/
theorem _root_.ContinuousLinearMap.exp_apply_of_apply_eq_smul (B : X →L[𝕜] X) {x : X} {μ : 𝕜}
    (hx : B x = μ • x) : exp B x = exp μ • x := by
  have hpow (n : ℕ) : (B ^ n) x = μ ^ n • x := by
    induction n with
    | zero => simp
    | succ n hn => rw [pow_succ, mul_apply_eq_comp, hx, map_smul, hn, smul_smul, ← pow_succ']
  have hop := (exp_series_hasSum_exp' (𝕂 := 𝕜) B).mapL (ContinuousLinearMap.apply 𝕜 X x)
  simp only [ContinuousLinearMap.apply_apply, smul_apply, hpow, smul_smul] at hop
  have hscalar := (exp_series_hasSum_exp' (𝕂 := 𝕜) μ).smul_const x
  simp only [smul_eq_mul] at hscalar
  exact hop.unique hscalar

end Operator

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

open Polynomial in
/-- **Spectral mapping for the exponential in finite dimension.** For an operator `N` on a
finite-dimensional complex normed space, the spectrum of `exp N` is the image of the spectrum of
`N` under the exponential. -/
theorem _root_.ContinuousLinearMap.spectrum_exp (N : V →L[ℂ] V) :
    spectrum ℂ (exp N) = exp '' spectrum ℂ N := by
  have := FiniteDimensional.complete ℂ V
  -- The inclusion `⊇` is `spectrum.exp_mem_exp`. For `⊆`, `exp N` is a polynomial `P (N)`, so its
  -- spectrum consists of the values `P (μ)` at the eigenvalues `μ` of `N`, and an eigenvector for
  -- `μ` shows `P (μ) = exp μ`.
  refine subset_antisymm (fun z hz ↦ ?_)
    (Set.image_subset_iff.mpr fun μ hμ ↦ spectrum.exp_mem_exp N hμ)
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [spectrum.of_subsingleton] at hz
  obtain ⟨P, hP⟩ := exists_aeval_eq_exp (𝕜 := ℂ) N
  rw [← hP, spectrum.map_polynomial_aeval_of_nonempty _ _ (spectrum.nonempty N)] at hz
  obtain ⟨μ, hμ, rfl⟩ := hz
  refine ⟨μ, hμ, ?_⟩
  rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  -- `P (N)` acts on the eigenvector `v` by `P (μ)`, and `exp N` by `exp μ`.
  have h := Module.End.aeval_apply_of_hasEigenvector (p := P) hv
  rw [← ContinuousLinearMap.toLinearMap_aeval, ContinuousLinearMap.coe_coe, hP,
    ContinuousLinearMap.exp_apply_of_apply_eq_smul N (Module.End.mem_eigenspace_iff.mp hv.1)] at h
  exact smul_left_injective ℂ hv.2 h

end FiniteDimensional

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **The Duhamel identity for the exponential of a bounded operator.** For `B : X →L[ℝ] X`,
`exp (t B) x - x = ∫₀ᵗ exp (u B) (B x) du`.

This is the fundamental theorem of calculus applied to the differentiable orbit
`u ↦ exp (u B) x`, whose derivative is the continuous function `u ↦ exp (u B) (B x)`. -/
theorem _root_.ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral
    (B : X →L[ℝ] X) (t : ℝ) (x : X) :
    exp (t • B) x - x = ∫ u in (0 : ℝ)..t, exp (u • B) (B x) := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun v : ℝ => exp (v • B) x) (exp (u • B) (B x)) u := by
    intro u
    simpa [mul_apply_eq_comp] using
      (hasDerivAt_exp_smul_const B u).clm_apply (hasDerivAt_const u x)
  have hcont : Continuous fun u : ℝ => exp (u • B) (B x) :=
    (differentiable_exp_smul_const ℝ B).continuous.clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 t)]
  simp

/-- A continuous function on `[0, ∞)` with right derivative `A (z t)` at every `t ≥ 0` is the linear
flow `t ↦ exp (t • A) (z 0)` of its initial value, by uniqueness for the linear equation. -/
theorem _root_.ContinuousLinearMap.eq_exp_smul_apply_of_hasDerivWithinAt {A : X →L[ℝ] X}
    {z : ℝ → X} (hz_cont : ContinuousOn z (Set.Ici 0))
    (hz : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt z (A (z t)) (Set.Ici t) t)
    {t : ℝ} (ht : 0 ≤ t) :
    z t = exp (t • A) (z 0) :=
  ODE_solution_unique_of_mem_Icc_right (v := fun _ x ↦ A x) (s := fun _ ↦ Set.univ)
    (K := ‖A‖₊) (fun _ _ ↦ A.lipschitzWith.lipschitzOnWith)
    (hz_cont.mono Set.Icc_subset_Ici_self) (fun t ht ↦ hz t ht.1) (fun _ _ ↦ Set.mem_univ _)
    (((differentiable_exp_smul_const ℝ A).continuous.clm_apply continuous_const).continuousOn)
    (fun t _ ↦ ((hasDerivAt_exp_smul_const' A t).clm_apply
      (hasDerivAt_const t (z 0))).hasDerivWithinAt.congr_deriv (by simp [mul_apply_eq_comp]))
    (fun _ _ ↦ Set.mem_univ _) (by simp) ⟨ht, le_rfl⟩

end Real

end TauCeti

end
