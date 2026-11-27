/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Analysis.Calculus.ContDiff.BoundedDerivatives
import TauCeti.Analysis.Sobolev.Leibniz

/-!
# Multiplication and division by functions with bounded derivatives in `W^{k,p}(Ω)`

Let `Ω` be an open set, possibly unbounded, and let `ψ` be `Cᵏ` on `Ω` with derivatives of order
at most `k` bounded on `Ω`. Multiplication by `ψ` preserves `W^{k,p}(Ω)`
(`TauCeti.Wkp.exists_value_ae_eq_mul_of_bddDerivOn`): by the Leibniz rule
`∂ᵥ(ψ u) = ψ ∂ᵥu + (∂ᵥψ) u`, and `∂ᵥψ` again has bounded derivatives, one order fewer. This is
the form in which variable coefficients act on Sobolev functions on a half-space or on the whole
space, where `closure Ω` is not compact and
`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn` does not apply.

Conversely, a function `ρ` of this kind bounded below by `λ > 0` can be divided out: if
`v ∈ Lᵖ(Ω)` and `ρ v ∈ W^{k,p}(Ω)`, then `v ∈ W^{k,p}(Ω)`
(`TauCeti.Wkp.exists_value_eq_of_value_ae_eq_mul`). The derivatives of `v` are found one at a
time: `ρ ∂ᵥv = ∂ᵥ(ρ v) - (∂ᵥρ) v`, so a gain of regularity for `v` passes to its derivatives.
Only `ρ⁻¹` itself, never a derivative of `ρ⁻¹` of order above one, enters the argument. This is
how an elliptic equation, solved for one second derivative of the solution, yields the regularity
of that derivative.

## Main declarations

* `TauCeti.Wkp.exists_value_ae_eq_mul_of_bddDerivOn`: multiplication by a `Cᵏ`
  function with bounded derivatives preserves `W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_value_eq_of_value_ae_eq_mul`: division by such a function bounded below by
  a positive constant preserves `W^{k,p}(Ω)`.
-/

public section

namespace TauCeti

namespace Wkp

open MeasureTheory TopologicalSpace
open scoped ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] [Fact (1 ≤ p)] in
/-- Multiplication by a function continuous and bounded on `Ω` preserves `Lᵖ(Ω)`. -/
private theorem exists_coeFn_ae_eq_mul_of_continuousOn {phi : E → ℝ} {M : ℝ}
    (hphi : ContinuousOn phi Omega) (hM : ∀ x ∈ (Omega : Set E), ‖phi x‖ ≤ M)
    (f : Lp ℝ p (mu.restrict Omega)) :
    ∃ g : Lp ℝ p (mu.restrict Omega), (g : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => phi x * f x := by
  have h : MemLp (fun x => phi x * f x) p (mu.restrict Omega) :=
    (memLp_top_of_bound (hphi.aestronglyMeasurable Omega.isOpen.measurableSet) M
      ((ae_restrict_mem Omega.isOpen.measurableSet).mono hM)).fun_mul (Lp.memLp f)
  exact ⟨h.toLp _, h.coeFn_toLp⟩

/-- **Multiplication by a function with bounded derivatives in `W^{k,p}`.** Let `ψ` be `Cᵏ` on
the open set `Ω`, with every derivative of order at most `k` bounded on `Ω`. If
`u ∈ W^{k,p}(Ω)`, then `ψ u` lies in `W^{k,p}(Ω)`: some element of `W^{k,p}(Ω)` has value `ψ u`
almost everywhere on `Ω`.

Neither `Ω` nor `closure Ω` need be bounded, unlike in
`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn`, where compactness of `closure Ω` bounds the
derivatives of `ψ`. -/
theorem exists_value_ae_eq_mul_of_bddDerivOn {k : ℕ} {psi : E → ℝ}
    (hpsi : BddDerivOn ℝ k psi Omega) (u : Wkp mu Omega p k) :
    ∃ w : Wkp mu Omega p k, (value k w : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x := by
  induction k generalizing psi with
  | zero =>
    -- `ψ` is continuous and bounded on `Ω`, so multiplication by `ψ` preserves `Lᵖ(Ω)`.
    obtain ⟨M, hM⟩ := hpsi.exists_norm_le
    simpa only [value_zero] using
      exists_coeFn_ae_eq_mul_of_continuousOn hpsi.contDiffOn.continuousOn hM (value 0 u)
  | succ k ih =>
    obtain ⟨M, hM⟩ := hpsi.exists_norm_le
    obtain ⟨g, hg⟩ := exists_coeFn_ae_eq_mul_of_continuousOn hpsi.contDiffOn.continuousOn hM
      (value (k + 1) u)
    set b := stdOrthonormalBasis ℝ E
    refine (exists_value_eq_of_forall_hasWeakLineDerivOn b g k fun i => ?_).imp
      fun w (hw : value (k + 1) w = g) => hw ▸ hg
    -- `∂ᵢ(ψ u) = ψ ∂ᵢu + (∂ᵢψ) u`, and both summands lie in `W^{k,p}(Ω)` by induction.
    obtain ⟨d, hd⟩ := exists_hasWeakLineDerivOn_value k u (b i)
    obtain ⟨w₁, hw₁⟩ := ih (hpsi.of_le (Nat.le_succ k)) d
    obtain ⟨w₂, hw₂⟩ := ih (hpsi.fderiv_apply Omega.isOpen (b i)) (lowerOrder k u)
    refine ⟨w₁ + w₂, ((hd.contDiffOn_smul_of_ne_zero hpsi.contDiffOn (by simp)).congr_ae
      ?_).congr_ae_deriv ?_⟩
    · filter_upwards [hg] with x hx
      rw [hx, smul_eq_mul]
    · filter_upwards [value_add_ae k w₁ w₂, hw₁, hw₂]
        with x hx h₁ h₂
      rw [hx, Pi.add_apply, h₁, h₂, ← value_succ, smul_eq_mul, smul_eq_mul]

/-- **Dividing out a function bounded below in `W^{k,p}`.** Let `ρ` be `Cᵏ` on the open set `Ω`,
with every derivative of order at most `k` bounded on `Ω`, and with `λ ≤ ρ` on `Ω` for some
`λ > 0`. If `v ∈ Lᵖ(Ω)` and `ρ v` is the value of an element of `W^{k,p}(Ω)`, then so is `v`. -/
theorem exists_value_eq_of_value_ae_eq_mul {k : ℕ} {rho : E → ℝ}
    (hrho : BddDerivOn ℝ k rho Omega) {lam : ℝ} (hlam : 0 < lam)
    (hrl : ∀ x ∈ (Omega : Set E), lam ≤ rho x) (v : Lp ℝ p (mu.restrict Omega))
    (w : Wkp mu Omega p k)
    (hw : (value k w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => rho x * v x) :
    ∃ W : Wkp mu Omega p k, value k W = v := by
  induction k generalizing rho v with
  | zero => exact ⟨v, value_zero v⟩
  | succ k ih =>
    have hne : ∀ x ∈ (Omega : Set E), rho x ≠ 0 := fun x hx => (hlam.trans_le (hrl x hx)).ne'
    -- `v ∈ W^{k,p}(Ω)` by induction, from `ρ v ∈ W^{k,p}(Ω)`.
    obtain ⟨V, hV⟩ := ih (hrho.of_le (Nat.le_succ k)) hrl v (lowerOrder k w)
      (by rwa [← value_succ])
    set b := stdOrthonormalBasis ℝ E
    refine exists_value_eq_of_forall_hasWeakLineDerivOn b v k fun i => ?_
    -- The derivative `g = ∂ᵢ(ρ v)` and the product `(∂ᵢρ) v` lie in `W^{k,p}(Ω)`.
    obtain ⟨g, hg⟩ := exists_hasWeakLineDerivOn_value k w (b i)
    obtain ⟨z, hz⟩ := exists_value_ae_eq_mul_of_bddDerivOn (hrho.fderiv_apply Omega.isOpen (b i)) V
    rw [hV] at hz
    -- The candidate derivative `q = ρ⁻¹ (∂ᵢ(ρ v) - (∂ᵢρ) v)` lies in `Lᵖ(Ω)`.
    have hinv : ContDiffOn ℝ (k + 1) (fun x => (rho x)⁻¹) Omega := hrho.contDiffOn.inv hne
    obtain ⟨q, hq⟩ := exists_coeFn_ae_eq_mul_of_continuousOn hinv.continuousOn
      (M := lam⁻¹) (fun x hx => by
        rw [norm_inv, Real.norm_of_nonneg (hlam.le.trans (hrl x hx))]
        exact inv_anti₀ hlam (hrl x hx)) (value k (g - z))
    -- `ρ q = ∂ᵢ(ρ v) - (∂ᵢρ) v` lies in `W^{k,p}(Ω)`, so by induction so does `q`.
    obtain ⟨d, hdq⟩ := ih (hrho.of_le (Nat.le_succ k)) hrl q (g - z) (by
        filter_upwards [hq, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
        rw [hx, ← mul_assoc, mul_inv_cancel₀ (hne x hxΩ), one_mul])
    refine ⟨d, ?_⟩
    rw [hdq]
    -- By the Leibniz rule for `ρ⁻¹ (ρ v) = v`, the function `q` is a weak derivative of `v`.
    refine (((hg.contDiffOn_smul_of_ne_zero hinv (by simp)).congr_ae ?_).congr_ae_deriv ?_)
    · filter_upwards [hw, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
      rw [smul_eq_mul, hx, ← mul_assoc, inv_mul_cancel₀ (hne x hxΩ), one_mul]
    · filter_upwards [hq, hw, hz, value_sub_ae k g z,
        ae_restrict_mem Omega.isOpen.measurableSet] with x hx hwx hzx hsub hxΩ
      have hdx : DifferentiableAt ℝ rho x :=
        ((hrho.contDiffOn x hxΩ).differentiableWithinAt (by simp)).differentiableAt
          (Omega.isOpen.mem_nhds hxΩ)
      -- The derivative of `ρ⁻¹` is `-(ρ²)⁻¹ ∂ᵢρ`.
      have hinvd : fderiv ℝ (fun y => (rho y)⁻¹) x (b i) =
          -((rho x ^ 2)⁻¹ * fderiv ℝ rho x (b i)) := by
        rw [show (fun y => (rho y)⁻¹) = (fun t : ℝ => t⁻¹) ∘ rho from rfl,
          fderiv_comp x (differentiableAt_inv (hne x hxΩ)) hdx, ContinuousLinearMap.comp_apply,
          fderiv_inv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
        ring
      rw [hx, hsub, Pi.sub_apply, hzx, smul_eq_mul, smul_eq_mul, hwx, hinvd]
      field_simp [hne x hxΩ]
      ring

end Wkp

end TauCeti
