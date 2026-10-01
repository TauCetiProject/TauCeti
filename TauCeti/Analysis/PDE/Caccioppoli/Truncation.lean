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
For a level `k`, put `w = (u - k)⁺` and assume `w ∈ L²(Ω)`. If `a` is measurable and uniformly
elliptic with constants `0 < λ ≤ Λ`, then every smooth cutoff `ψ` compactly supported in `Ω`
satisfies

`∫_Ω ψ² ‖∇w‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2/λ) ∫_Ω ψ² f w`.

The test function is `ψ²w`. It is nonnegative and belongs to `H¹₀(Ω)` because the cutoff is
compactly supported. On `{u > k}`, the weak gradient of `w` equals that of `u`; off this set,
both the value and weak gradient of `w` vanish. This reduces the pointwise energy estimate to
the same absorption inequality as for weak solutions.

This truncation estimate is the energy input to De Giorgi iteration and to the corresponding
weak maximum-principle argument.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp`:
  Caccioppoli's inequality for `(u - k)⁺` at an arbitrary level with an `L²` hypothesis.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le`:
  the nonnegative-level specialization, whose `L²` hypothesis is automatic.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le`: the form on concentric
  balls `B(x₀, r) ⊆ B(x₀, R)`, `∫_{B(x₀, r)} ‖∇w‖² ≤ (2Λ/λ)² (c/(R - r))² ∫_{B(x₀, R)} w²`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
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

for every nonnegative `v ∈ H¹₀(Ω)`. At any level `k` for which `w = (u - k)⁺` belongs to
`L²(Ω)`, every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2/λ) ∫_Ω ψ² f w`.

No boundary regularity or coefficient regularity beyond measurability is assumed. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ}
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + 2 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value w x ∂mu := by
  dsimp only
  have hlam := h.pos
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- Build the nonnegative test function `v = ψ² (u - k)⁺` in `H¹₀(Ω)`.
  set w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' z
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM'
      hgradM' hcpt hts z
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp] with x hvx hzx hwx
    rw [hvx, hzx, hwx, smul_eq_mul, smul_eq_mul]
    rw [← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (le_max_right _ _)
  have hsub := hu ⟨v, hv⟩ hnonneg
  simp only at hsub
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
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
    filter_upwards [hmem, W1p.gradient_posPartAboveOfMemLp_ae (by norm_num) k u hwLp,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w] with
        x hx hwg hwv hgv hgz hzv
    by_cases hxu : k < W1p.value u x
    · have hwg_active : W1p.gradient w x = W1p.gradient u x := by
        rw [hwg]
        have hxmem : x ∈ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
        exact Set.indicator_of_mem hxmem (⇑(W1p.gradient u))
      have hkey := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam (ψ x)
        (W1p.value w x) (W1p.gradient u x) (∇ ψ x)
        (h.lower_bound hx (W1p.gradient u x))
        (h.upper_bound hx (∇ ψ x) (W1p.gradient u x))
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
  exact W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise hlam w hψ hψM hgradM hE hpt
    hforce

/-- **The Caccioppoli inequality for a nonnegative-level truncation of a weak subsolution.**
This specializes
`UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp`; the
condition `k ≥ 0` makes `(u - k)⁺ ∈ L²(Ω)` automatic even when `Ω` has infinite measure. -/
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
  have hgeneral := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp ha hu
    (W1p.memLp_posPartAbove hk u) hψ hcpt hts
  rw [W1p.posPartAboveOfMemLp_eq_posPartAbove (by norm_num) hk u
    (W1p.memLp_posPartAbove hk u)] at hgeneral
  exact hgeneral

/-- **The Caccioppoli inequality on concentric balls.** There is a constant `c > 0`, depending
only on the dimension, such that the following holds for every additive Haar measure `μ`.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≤ 0`. At any level `k` with
`w = (u - k)⁺ ∈ L²(Ω)`, and for every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with
`0 < r < R`,

`∫_{B(x₀, r)} ‖∇w‖² ≤ (2Λ/λ)² (c / (R - r))² ∫_{B(x₀, R)} w²`. -/
theorem exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {k : ℝ}
      (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < r → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r,
          ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) k u hwLp) x‖ ^ 2 ∂mu ≤
        (2 * Lam / lam) ^ 2 * (c / (R - r)) ^ 2 *
          ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
  obtain ⟨c, hc0, hc⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨2 * (c + 1), by positivity, ?_⟩
  intro mu _ Omega a lam Lam u k hwLp x₀ r R h ha hu hr hrR hball
  -- A cutoff equal to one on `B(x₀, r)` and supported in `B̄(x₀, (r + R)/2) ⊆ B(x₀, R)`.
  obtain ⟨ψ, hψ, hrange, hone, hts, hgrad⟩ := hc x₀ hr (by linarith : r < (r + R) / 2)
  have htsR : tsupport ψ ⊆ ball x₀ R :=
    hts.trans (closedBall_subset_ball (by linarith))
  have htsΩ : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := htsR.trans hball
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ((r + R) / 2)).of_isClosed_subset (isClosed_tsupport ψ) hts
  set G : ℝ := 2 * (c + 1) / (R - r)
  have hG : ∀ x, ‖∇ ψ x‖ ≤ G := fun x => (hgrad x).trans (by
    rw [(by ring : (r + R) / 2 - r = (R - r) / 2), div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith))
  set w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
  -- Caccioppoli's inequality for `w`, with zero forcing.
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp ha
    (f := 0) (fun v hv => (hu v hv).trans_eq (integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx
      rw [hx, Pi.zero_apply, zero_mul])).symm) hwLp hψ hcpt htsΩ
  have hzero : ∫ x in Omega, ψ x ^ 2 * (0 : Lp ℝ 2 (mu.restrict Omega)) x *
      W1p.value w x ∂mu = 0 := integral_eq_zero_of_ae (by
    filter_upwards [Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx
    rw [hx, Pi.zero_apply, mul_zero, zero_mul])
  dsimp only at hcacc
  rw [hzero, mul_zero, add_zero] at hcacc
  -- On `B(x₀, r)` the cutoff is one.
  have hleft : ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu := by
    have hψ1 : ∀ x, |ψ x| ≤ 1 := fun x => by
      obtain ⟨h0, h1⟩ := hrange (mem_range_self x)
      rw [abs_of_nonneg h0]
      exact h1
    have hint : IntegrableOn (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) Omega mu :=
      (W1p.integrable_norm_gradient_sq w).bdd_mul (hψ.continuous.pow 2).aestronglyMeasurable
        (c := 1) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (hψ1 x))
    calc ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu
        = ∫ x in ball x₀ r, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu :=
          setIntegral_congr_fun measurableSet_ball fun x hx => by
            rw [hone (ball_subset_closedBall hx), Pi.one_apply, one_pow, one_mul]
      _ ≤ ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu :=
          setIntegral_mono_set hint (Eventually.of_forall fun x => by positivity)
            ((ball_subset_ball hrR.le).trans hball).eventuallyLE
  -- `∇ψ` vanishes off `B(x₀, R)`, where it is bounded by `G`.
  have hright : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu ≤
      G ^ 2 * ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
    have hI2 : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
      (W1p.integrable_value_sq w).bdd_mul
        ((ContDiff.continuous_gradient hψ).norm.pow 2).aestronglyMeasurable (c := G ^ 2)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_pow, abs_norm]
          exact pow_le_pow_left₀ (norm_nonneg _) (hG x) 2)
    have hind : Integrable ((ball x₀ R).indicator fun x => max (W1p.value u x - k) 0 ^ 2)
        (mu.restrict Omega) := hwLp.integrable_sq.indicator measurableSet_ball
    calc ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        ≤ ∫ x in Omega, G ^ 2 *
            (ball x₀ R).indicator (fun x => max (W1p.value u x - k) 0 ^ 2) x ∂mu :=
          integral_mono_ae hI2 (hind.const_mul _) (by
            filter_upwards [W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp] with x hx
            by_cases hxR : x ∈ ball x₀ R
            · rw [indicator_of_mem hxR, hx]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hG x) 2)
                (by positivity)
            · have hfd : fderiv ℝ ψ x = 0 := Function.notMem_support.1 fun hx' =>
                hxR (htsR (support_fderiv_subset ℝ hx'))
              simp [indicator_of_notMem hxR, _root_.gradient, hfd])
      _ = G ^ 2 * ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
          rw [integral_const_mul, setIntegral_indicator measurableSet_ball,
            inter_eq_right.2 hball]
  calc ∫ x in ball x₀ r, ‖W1p.gradient w x‖ ^ 2 ∂mu
      ≤ (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu :=
        hleft.trans hcacc
    _ ≤ (2 * Lam / lam) ^ 2 * (G ^ 2 * ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) :=
        mul_le_mul_of_nonneg_left hright (sq_nonneg _)
    _ = _ := by rw [div_pow, mul_assoc]

end PDE

end TauCeti
