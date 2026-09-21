/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
public import TauCeti.Analysis.Sobolev.W1p.ChainRule

/-!
# The Caccioppoli inequality for truncations of weak subsolutions

Let `u ∈ H¹(Ω)` be a weak subsolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≤ f` in `Ω`.

Thus the weak energy inequality holds against every nonnegative test function in `H¹₀(Ω)`.
For a nonnegative level `k`, put `w = (u - k)⁺`. If `a` is measurable and uniformly elliptic
with constants `0 < λ ≤ Λ`, then every smooth cutoff `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2/λ) ∫_Ω ψ² f w`.

The test function is `ψ²w`. It is nonnegative and belongs to `H¹₀(Ω)` because the cutoff is
compactly supported. On `{u > k}`, the weak gradient of `w` equals that of `u`; off this set,
both the value and weak gradient of `w` vanish. This reduces the pointwise energy estimate to
the same absorption inequality as for weak solutions.

This truncation estimate is the energy input to De Giorgi iteration and to the corresponding
weak maximum-principle argument.

## Main declaration

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le`:
  Caccioppoli's inequality for `(u - k)⁺` when `u` is a weak subsolution.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- **The Caccioppoli inequality for a positive truncation of a weak subsolution.**
Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` satisfy

`a(u, v) ≤ ∫_Ω f v`

for every nonnegative `v ∈ H¹₀(Ω)`. For `k ≥ 0`, write `w = (u - k)⁺`. Then every
smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2/λ) ∫_Ω ψ² f w`.

No boundary regularity or coefficient regularity beyond measurability is assumed. The
restriction `k ≥ 0` ensures `(u - k)⁺ ∈ L²(Ω)` even when `Ω` has infinite measure. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAbove (by norm_num) hk u
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + 2 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value w x ∂mu := by
  dsimp only
  have hlam := h.pos
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- Build the nonnegative test function `v = ψ² (u - k)⁺` in `H¹₀(Ω)`.
  set w := W1p.posPartAbove (by norm_num) hk u
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' z
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM'
      hgradM' hcpt hts z
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_posPartAbove_ae (by norm_num) hk u] with x hvx hzx hwx
    rw [hvx, hzx, hwx, smul_eq_mul, smul_eq_mul]
    rw [← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (le_max_right _ _)
  have hsub := hu ⟨v, hv⟩ hnonneg
  simp only at hsub
  -- Record integrability before integrating the pointwise absorption estimate.
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hgrad2 : AEStronglyMeasurable (fun x => ‖∇ ψ x‖ ^ 2) (mu.restrict Omega) :=
    ((ContDiff.continuous_gradient hψ).norm.pow 2).aestronglyMeasurable
  have hI1 : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_sq w).bdd_mul hψ2 (c := M ^ 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2)
  have hI2 : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_value_sq w).bdd_mul hgrad2 (c := M ^ 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgradM x) 2)
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0) (gamma := 0)
    ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u v
  -- On the active set the truncation gradient is `∇u`; off it, the test jet vanishes.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ≤
        energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x)
          + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2) := by
    filter_upwards [hmem, W1p.gradient_posPartAbove_ae (by norm_num) hk u,
      W1p.value_posPartAbove_ae (by norm_num) hk u,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w] with
        x hx hwg hwv hgv hgz hzv
    by_cases hxu : k < W1p.value u x
    · have hwg_active : W1p.gradient w x = W1p.gradient u x := by
        rw [hwg]
        have hxmem : x ∈ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
        exact Set.indicator_of_mem hxmem (⇑(W1p.gradient u))
      have hkey := mul_sq_mul_norm_sq_le_matrixBilinearForm hlam (h.lower_bound hx)
        (h.upper_bound hx) (ψ x) (W1p.value w x) (W1p.gradient u x) (∇ ψ x)
      rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgz, hzv, hwg_active]
      simpa [driftForm_apply, massForm_apply, smul_eq_mul] using hkey
    · have hwg_zero : W1p.gradient w x = 0 := by
        rw [hwg]
        have hxmem : x ∉ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
        exact Set.indicator_of_notMem hxmem (⇑(W1p.gradient u))
      have hwv_zero : W1p.value w x = 0 := by
        rw [hwv, max_eq_right (sub_nonpos.mpr (le_of_not_gt hxu))]
      rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgz, hzv, hwg_zero,
        hwv_zero]
      simp [driftForm_apply, massForm_apply]
  -- Integrate the pointwise estimate, using the integrability facts above to split the sum.
  have hint : ∫ x in Omega, lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ∂mu ≤
      ∫ x in Omega, (energyIntegrand (a x)
            ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x)
          + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2)) ∂mu :=
    integral_mono_ae (hI1.const_mul lam) ((hE.add (hI1.const_mul _)).add (hI2.const_mul _)) hpt
  rw [integral_const_mul, integral_add, integral_add, integral_const_mul,
    integral_const_mul] at hint
  rotate_left
  · exact hE
  · exact hI1.const_mul _
  · exact hE.add (hI1.const_mul _)
  · exact hI2.const_mul _
  -- Apply the weak subsolution inequality to the nonnegative test function.
  have hforce : ∫ x in Omega,
        energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
          ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x) ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * f x * W1p.value w x ∂mu := by
    rw [← energyFormH1_def]
    refine hsub.trans_eq (integral_congr_ae ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w] with x hvx hzx
    rw [hvx, hzx, smul_eq_mul, smul_eq_mul]
    ring
  -- Absorb half of the gradient term and simplify the explicit constants.
  set X := ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
  set F := ∫ x in Omega, ψ x ^ 2 * f x * W1p.value w x ∂mu
  have hmain : lam * X ≤ F + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
    calc
      lam * X ≤
          (∫ x in Omega, energyIntegrand (a x)
              ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
              ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x) ∂mu)
            + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
        simpa [X, Y] using hint
      _ ≤ F + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
        gcongr
  have hX : X = 2 / lam * (lam / 2 * X) := by field_simp
  rw [hX]
  calc
    2 / lam * (lam / 2 * X) ≤ 2 / lam * (F + 2 * Lam ^ 2 / lam * Y) := by
      gcongr
      linarith
    _ = (2 * Lam / lam) ^ 2 * Y + 2 / lam * F := by
      field_simp
      ring

end PDE

end TauCeti
