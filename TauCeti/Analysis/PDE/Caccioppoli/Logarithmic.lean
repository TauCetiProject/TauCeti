/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.ChainRule

/-!
# The logarithmic Caccioppoli inequality for positive supersolutions

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`. If `u` is bounded below by a positive
constant on the support of a smooth cutoff `ψ` compactly supported in `Ω`, then

`∫_Ω ψ² ‖∇u‖² / u² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖²`.

This is the **logarithmic Caccioppoli inequality**: `‖∇u‖ / u = ‖∇ log u‖`, so the gradient of
`log u` is controlled by the cutoff alone, independently of the size of `u`. Combined with the
Poincaré–Wirtinger inequality on balls it shows that `log u` has bounded mean oscillation: on
every ball `B(x₀, R)` with `B(x₀, 2R) ⊆ Ω`, if `u ≥ m` almost everywhere on the doubled ball
`B(x₀, 2R)` for some constant `m > 0`, then

`∫_{B(x₀, R)} (log u - (log u)_{B(x₀, R)})² ≤ C (Λ/λ)² |B(x₀, R)|`,

with `C` depending only on the dimension. This estimate is the bridge between the bounds for
subsolutions and for supersolutions in Moser's proof of the Harnack inequality: through the
John–Nirenberg inequality, or the Bombieri–Giusti lemma, it is what allows the averages of a
small positive power of `u` and of its reciprocal to be compared.

The proof tests the supersolution inequality against `ψ²/u`, which lies in `H¹₀(Ω)`, with weak
gradient `2ψ ∇ψ / u - ψ² ∇u / u²`. Since `u` is only bounded below on the support of `ψ`, the
reciprocal is realised as a composition `F ∘ u` with a `C¹` function `F` that has bounded
derivative, vanishes near `0` and agrees with `t ↦ 1/t` for `t ≥ m/2`; the logarithm is handled
in the same way for the mean-oscillation bound.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_div_sq_le`: the
  logarithmic Caccioppoli inequality.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_div_sq_le`: its form on concentric balls,
  `∫_{B(x₀, r)} ‖∇u‖² / u² ≤ (2Λ/λ)² (c / (R - r))² |B(x₀, R)|`.
* `TauCeti.PDE.exists_setIntegral_ball_log_sub_setAverage_sq_le`: the `L²` mean oscillation of
  `log u` on a ball is bounded by a dimensional constant times `(Λ/λ)²`.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  14 (1961).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6 (the estimate for `log u` in the proof of Theorem 8.18).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- If `|ψ| ≤ M` and `u ≥ m > 0` on the support of `ψ`, then `ψ² ‖∇u‖² / u²` is integrable on
`Ω`, being dominated by `(M/m)² ‖∇u‖²`. -/
private theorem integrable_sq_mul_norm_gradient_sq_div_sq {u : W1p mu Omega 2}
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : Continuous ψ) {M : ℝ} (hψM : ∀ x, |ψ x| ≤ M) {m : ℝ}
    (hm : 0 < m) (hum : ∀ᵐ x ∂mu.restrict Omega, x ∈ tsupport ψ → m ≤ W1p.value u x) :
    Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2)
      (mu.restrict Omega) := by
  refine Integrable.mono' ((W1p.integrable_norm_gradient_sq u).const_mul ((M / m) ^ 2)) ?_ ?_
  · exact ((((hψ.pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (W1p.gradient u)).norm.pow 2)).aemeasurable).div
      ((Lp.aestronglyMeasurable (W1p.value u)).pow 2).aemeasurable).aestronglyMeasurable
  filter_upwards [hum] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hxs : x ∈ tsupport ψ
  · have hux := hx hxs
    have hu0 : 0 < W1p.value u x := hm.trans_le hux
    have hψ2 : ψ x ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
    have hum2 : 1 ≤ W1p.value u x ^ 2 / m ^ 2 := by
      rw [one_le_div (by positivity)]
      exact pow_le_pow_left₀ hm.le hux 2
    rw [div_le_iff₀ (by positivity)]
    calc ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2
        ≤ M ^ 2 * ‖W1p.gradient u x‖ ^ 2 := by gcongr
      _ ≤ M ^ 2 * ‖W1p.gradient u x‖ ^ 2 * (W1p.value u x ^ 2 / m ^ 2) :=
          le_mul_of_one_le_right (by positivity) hum2
      _ = (M / m) ^ 2 * ‖W1p.gradient u x‖ ^ 2 * W1p.value u x ^ 2 := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxs]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div]
    positivity

/-- The pointwise form of the logarithmic Caccioppoli inequality. Let `A` satisfy the ellipticity
bounds with constants `λ, Λ`. At a point where `u = c > 0`, `∇u = g`, `ψ = z` and `∇ψ = q`, the
gradient of the test function `ψ²/u` is `z (z (-g/c²) + q/c) + (z/c) q`, and

`λ z² ‖g‖²/c² ≤ -⟨A g, ∇(ψ²/u)⟩ + (λ/2) z² ‖g‖²/c² + (2Λ²/λ) ‖q‖²`.

This is `TauCeti.PDE.mul_sq_mul_norm_sq_le_matrixBilinearForm_add` at `g/c`, with the sign of
the cross term reversed. -/
private theorem mul_sq_mul_norm_sq_div_sq_le_neg_matrixBilinearForm_add {A : Matrix ι ι ℝ}
    (hlam : 0 < lam) (hlower : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hupper : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) {c : ℝ}
    (hc : 0 < c) (z : ℝ) (g q : EuclideanSpace ℝ ι) :
    lam * (z ^ 2 * ‖g‖ ^ 2 / c ^ 2) ≤
      -matrixBilinearForm A (z • (z • (-(c ^ 2)⁻¹ • g) + c⁻¹ • q) + (z • c⁻¹) • q) g
        + lam / 2 * (z ^ 2 * ‖g‖ ^ 2 / c ^ 2) + 2 * Lam ^ 2 / lam * ‖q‖ ^ 2 := by
  set G := c⁻¹ • g
  have hkey := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam z (-1) G q (hlower G)
    (hupper q G)
  have hg : g = c • G := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hGnorm : z ^ 2 * ‖G‖ ^ 2 = z ^ 2 * ‖g‖ ^ 2 / c ^ 2 := by
    simp only [G, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    ring
  have hB : matrixBilinearForm A (z • (z • (-(c ^ 2)⁻¹ • g) + c⁻¹ • q) + (z • c⁻¹) • q) g =
      -matrixBilinearForm A (z • (z • G + (-1 : ℝ) • q) + (z * -1) • q) G := by
    rw [hg]
    simp only [map_add, map_smul, _root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    field_simp
    ring
  rw [hGnorm, neg_one_sq, mul_one] at hkey
  rw [hB, neg_neg]
  exact hkey

/-- **The logarithmic Caccioppoli inequality.** Let `a` be measurable and uniformly elliptic on
`Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Let `ψ` be smooth
and compactly supported in `Ω`, and suppose that `u ≥ m` almost everywhere on the support of `ψ`
for some `m > 0`. Then

`∫_Ω ψ² ‖∇u‖² / u² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖²`.

The left side is `∫_Ω ψ² ‖∇ log u‖²`; the bound does not depend on `m`, on the size of `u`, or
on any regularity of the coefficients beyond measurability. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_div_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {m : ℝ} (hm : 0 < m)
    (hum : ∀ᵐ x ∂mu.restrict (tsupport ψ), m ≤ W1p.value u x) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu := by
  have hlam := h.pos
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- The reciprocal `1/u` on the support of `ψ`, as an element `z = F ∘ u` of `H¹(Ω)`.
  set F := positiveCutoff m fun t : ℝ => t⁻¹
  have hgC : ∀ t : ℝ, 0 < t → ContDiffAt ℝ 1 (fun t : ℝ => t⁻¹) t :=
    fun t ht => contDiffAt_inv ℝ ht.ne'
  have hFC : ContDiff ℝ 1 F := contDiff_positiveCutoff hm hgC
  obtain ⟨MF, hMF⟩ := exists_nnnorm_deriv_positiveCutoff_le hm hgC (K := (m ^ 2)⁻¹)
    fun t ht => by
      rw [deriv_inv, abs_neg, abs_inv, abs_pow, abs_of_pos (hm.trans_le ht)]
      gcongr
  have hF0 : F 0 = 0 := positiveCutoff_of_le hm _ (by linarith)
  set z := W1p.contDiffComp (by norm_num) hFC hMF hF0 u
  -- The test function `v = ψ (ψ z) = ψ² / u`, nonnegative and in `H¹₀(Ω)`.
  set y := W1p.contDiffSMul ψ hψ hM hψM' hgradM' z
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' y
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM' hgradM'
      hcpt hts y
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value v x := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' y,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffComp_ae (by norm_num) hFC hMF hF0 u] with x hvx hyx hzx
    rw [hvx, hyx, hzx, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _)
      (positiveCutoff_nonneg hm (fun t ht => (inv_pos.2 ht).le) _)
  have hsup := hu ⟨v, hv⟩ hnonneg
  simp only at hsup
  -- The lower bound `u ≥ m` on the support of `ψ`, almost everywhere on `Ω`.
  have hum' : ∀ᵐ x ∂mu.restrict Omega, x ∈ tsupport ψ → m ≤ W1p.value u x :=
    ae_restrict_of_ae ((ae_restrict_iff' (isClosed_tsupport ψ).measurableSet).1 hum)
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0) (gamma := 0)
    ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u v
  set X : EuclideanSpace ℝ ι → ℝ := fun x => ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2
  -- Off the support of `ψ` both `ψ` and `∇ψ` vanish.
  have hψ0 : ∀ x, x ∉ tsupport ψ → ψ x = 0 ∧ ∇ ψ x = 0 := fun x hx => by
    refine ⟨image_eq_zero_of_notMem_tsupport hx, ?_⟩
    have hfd : fderiv ℝ ψ x = 0 := Function.notMem_support.1 fun hx' =>
      hx (support_fderiv_subset ℝ hx')
    simp [_root_.gradient, hfd]
  have hXint : Integrable X (mu.restrict Omega) :=
    integrable_sq_mul_norm_gradient_sq_div_sq hψ.continuous hψM hm hum'
  have hYint : Integrable (fun x => ‖∇ ψ x‖ ^ 2) (mu.restrict Omega) := by
    have hcs : HasCompactSupport fun x => ‖∇ ψ x‖ ^ 2 := by
      refine hcpt.mono' fun x hx => ?_
      by_contra hxs
      exact hx (by simp [(hψ0 x hxs).2])
    exact (((ContDiff.continuous_gradient hψ).norm.pow 2).integrable_of_hasCompactSupport
      hcs).restrict
  -- The pointwise estimate: with `G = ∇u / u` and `q = ∇ψ`, the energy density of the test
  -- function is `-ψ² aG·G + 2ψ aG·q`, and Young's inequality absorbs the cross term.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      lam * X x ≤
        -energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x)
          + lam / 2 * X x + 2 * Lam ^ 2 / lam * ‖∇ ψ x‖ ^ 2 := by
    filter_upwards [hmem, hum', W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' y,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' z,
      W1p.value_contDiffComp_ae (by norm_num) hFC hMF hF0 u,
      W1p.gradient_contDiffComp_ae (by norm_num) hFC hMF hF0 u] with
        x hx hux hgv hgy hyv hzv hzg
    rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgy, hyv, hzv, hzg]
    simp only [driftForm_apply, massForm_apply, Pi.zero_apply, inner_zero_left, zero_mul,
      add_zero]
    by_cases hxs : x ∈ tsupport ψ
    · have hu0 : 0 < W1p.value u x := hm.trans_le (hux hxs)
      have hhalf : m / 2 < W1p.value u x := by linarith [hux hxs]
      have hFu : F (W1p.value u x) = (W1p.value u x)⁻¹ := positiveCutoff_of_ge hm _ hhalf.le
      have hdFu : deriv F (W1p.value u x) = -(W1p.value u x ^ 2)⁻¹ := by
        rw [deriv_positiveCutoff hm _ hhalf, deriv_inv]
      rw [hFu, hdFu]
      exact mul_sq_mul_norm_sq_div_sq_le_neg_matrixBilinearForm_add hlam (h.lower_bound hx)
        (h.upper_bound hx) hu0 _ _ _
    · obtain ⟨hψx, hqx⟩ := hψ0 x hxs
      simp [X, hψx, hqx]
  -- Integrate, and absorb half of the left side.
  have hint : ∫ x in Omega, lam * X x ∂mu ≤ ∫ x in Omega, (-energyIntegrand (a x)
        ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)
          (jetField u x) (jetField v x) + lam / 2 * X x + 2 * Lam ^ 2 / lam * ‖∇ ψ x‖ ^ 2) ∂mu :=
    integral_mono_ae (hXint.const_mul lam)
      (by exact (hE.neg.add (hXint.const_mul _)).add (hYint.const_mul _)) hpt
  have hsplit : ∫ x in Omega, (-energyIntegrand (a x)
        ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)
          (jetField u x) (jetField v x) + lam / 2 * X x + 2 * Lam ^ 2 / lam * ‖∇ ψ x‖ ^ 2) ∂mu =
      -energyFormH1 a 0 0 u v + lam / 2 * ∫ x in Omega, X x ∂mu
        + 2 * Lam ^ 2 / lam * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu := by
    rw [integral_add, integral_add, integral_neg, integral_const_mul, integral_const_mul,
      energyFormH1_def]
    all_goals first
      | exact hE.neg
      | exact hXint.const_mul _
      | exact hYint.const_mul _
      | exact hE.neg.add (hXint.const_mul _)
  rw [integral_const_mul, hsplit] at hint
  set I := ∫ x in Omega, X x ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu
  have h2 : lam / 2 * I ≤ 2 * Lam ^ 2 / lam * Y := by linarith
  calc I = 2 / lam * (lam / 2 * I) := by field_simp
    _ ≤ 2 / lam * (2 * Lam ^ 2 / lam * Y) := by gcongr
    _ = (2 * Lam / lam) ^ 2 * Y := by field_simp

/-- **The logarithmic Caccioppoli inequality on concentric balls.** There is a constant `c > 0`,
depending only on the dimension, such that the following holds for every additive Haar measure
`μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`. If `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with
`0 < r < R`, and `u ≥ m` almost everywhere on `B(x₀, R)` for some `m > 0`, then

`∫_{B(x₀, r)} ‖∇u‖² / u² ≤ (2Λ/λ)² (c / (R - r))² |B(x₀, R)|`. -/
theorem exists_setIntegral_ball_norm_gradient_sq_div_sq_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {r R m : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < r → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → 0 < m →
      (∀ᵐ x ∂mu.restrict (ball x₀ R), m ≤ W1p.value u x) →
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu ≤
        (2 * Lam / lam) ^ 2 * (c / (R - r)) ^ 2 * mu.real (ball x₀ R) := by
  obtain ⟨c, hc0, hc⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨2 * (c + 1), by positivity, ?_⟩
  intro mu _ Omega a lam Lam u x₀ r R m h ha hu hr hrR hball hm hum
  -- A cutoff equal to one on `B(x₀, r)`, supported in `closedBall x₀ ((r + R)/2) ⊆ B(x₀, R)`.
  obtain ⟨ψ, hψ, hrange, hone, hts, hgrad⟩ := hc x₀ hr (by linarith : r < (r + R) / 2)
  have hsubR : closedBall x₀ ((r + R) / 2) ⊆ ball x₀ R := closedBall_subset_ball (by linarith)
  have htsR : tsupport ψ ⊆ ball x₀ R := hts.trans hsubR
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ((r + R) / 2)).of_isClosed_subset (isClosed_tsupport ψ) hts
  set G : ℝ := 2 * (c + 1) / (R - r)
  have hG : ∀ x, ‖∇ ψ x‖ ≤ G := fun x => (hgrad x).trans (by
    rw [(by ring : (r + R) / 2 - r = (R - r) / 2), div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith))
  have hcacc := h.setIntegral_sq_mul_norm_gradient_sq_div_sq_le ha hu hψ hcpt
    (htsR.trans hball) hm (ae_restrict_of_ae_restrict_of_subset htsR hum)
  -- On `B(x₀, r)` the cutoff is one.
  have hleft : ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu := by
    have hXint := integrable_sq_mul_norm_gradient_sq_div_sq (u := u) hψ.continuous
      (M := 1) (fun x => by
        obtain ⟨h0, h1⟩ := hrange (mem_range_self x)
        rwa [abs_of_nonneg h0]) hm
      (ae_restrict_of_ae (((ae_restrict_iff' measurableSet_ball).1 hum).mono
        fun x hx hxs => hx (htsR hxs)))
    calc ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu
        = ∫ x in ball x₀ r, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu :=
          setIntegral_congr_fun measurableSet_ball fun x hx => by
            rw [hone (ball_subset_closedBall hx), Pi.one_apply, one_pow, one_mul]
      _ ≤ _ := setIntegral_mono_set hXint (Eventually.of_forall fun x => by positivity)
          (Eventually.of_forall ((ball_subset_ball hrR.le).trans hball))
  -- `∇ψ` vanishes off `closedBall x₀ ((r + R)/2)`, where it is bounded by `G`.
  have hright : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu ≤ G ^ 2 * mu.real (ball x₀ R) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Omega.isOpen.measurableSet
      (hsubR.trans hball) fun x hx => by
        have hfd : fderiv ℝ ψ x = 0 := Function.notMem_support.1 fun hx' =>
          hx.2 (hts (support_fderiv_subset ℝ hx'))
        simp [_root_.gradient, hfd]]
    calc ∫ x in closedBall x₀ ((r + R) / 2), ‖∇ ψ x‖ ^ 2 ∂mu
        ≤ ‖∫ x in closedBall x₀ ((r + R) / 2), ‖∇ ψ x‖ ^ 2 ∂mu‖ := Real.le_norm_self _
      _ ≤ G ^ 2 * mu.real (closedBall x₀ ((r + R) / 2)) :=
          norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun x _ => by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hG x) 2
      _ ≤ G ^ 2 * mu.real (ball x₀ R) := by
          gcongr
          exact measure_ball_lt_top.ne
  calc ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu
      ≤ (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu := hleft.trans hcacc
    _ ≤ (2 * Lam / lam) ^ 2 * (G ^ 2 * mu.real (ball x₀ R)) := by gcongr
    _ = _ := by ring

/-- **Bounded mean oscillation of the logarithm of a positive supersolution (Moser).** There is
a constant `C > 0`, depending only on the dimension, such that the following holds for every
additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`. If
`B(x₀, 2R) ⊆ Ω` and `u ≥ m` almost everywhere on `B(x₀, 2R)` for some `m > 0`, then

`∫_{B(x₀, R)} (log u - (log u)_{B(x₀, R)})² ≤ C (Λ/λ)² |B(x₀, R)|`,

where `(log u)_{B(x₀, R)}` is the mean of `log u` over the ball. The bound does not depend on
`m`, on `R`, or on the size of `u`. -/
theorem exists_setIntegral_ball_log_sub_setAverage_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R m : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < R → ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → 0 < m →
      (∀ᵐ x ∂mu.restrict (ball x₀ (2 * R)), m ≤ W1p.value u x) →
      ∫ x in ball x₀ R,
          (Real.log (W1p.value u x) - ⨍ y in ball x₀ R, Real.log (W1p.value u y) ∂mu) ^ 2 ∂mu ≤
        C * (Lam / lam) ^ 2 * mu.real (ball x₀ R) := by
  obtain ⟨c, hc0, hc⟩ := exists_setIntegral_ball_norm_gradient_sq_div_sq_le (ι := ι)
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  refine ⟨(2 ^ (n + 1)) ^ 2 * 4 * c ^ 2 * 2 ^ n, by positivity, ?_⟩
  intro mu _ Omega a lam Lam u x₀ R m h ha hu hR hball hm hum
  have hlam := h.pos
  -- `log u` as an element `w` of `H¹(B(x₀, R))`, with weak gradient `∇u / u`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ R, isOpen_ball⟩
  have hU : U ≤ Omega := (ball_subset_ball (by linarith)).trans hball
  set F := positiveCutoff m Real.log
  have hgC : ∀ t : ℝ, 0 < t → ContDiffAt ℝ 1 Real.log t :=
    fun t ht => Real.contDiffAt_log.2 ht.ne'
  have hFC : ContDiff ℝ 1 F := contDiff_positiveCutoff hm hgC
  obtain ⟨MF, hMF⟩ := exists_nnnorm_deriv_positiveCutoff_le hm hgC (K := m⁻¹) fun t ht => by
    rw [Real.deriv_log, abs_inv, abs_of_pos (hm.trans_le ht)]
    gcongr
  have hF0 : F 0 = 0 := positiveCutoff_of_le hm _ (by linarith)
  set w := W1p.contDiffComp (by norm_num) hFC hMF hF0 (W1p.restrictL hU u)
  have humR : ∀ᵐ x ∂mu.restrict (ball x₀ R), m ≤ W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hum
  have hwv : ⇑(W1p.value w) =ᵐ[mu.restrict (ball x₀ R)] fun x => Real.log (W1p.value u x) := by
    filter_upwards [W1p.value_contDiffComp_ae (by norm_num) hFC hMF hF0 (W1p.restrictL hU u),
      W1p.value_restrictL_ae hU u, humR] with x hx hux hmx
    rw [hx, hux]
    exact positiveCutoff_of_ge hm _ (by linarith)
  have hwg : ∀ᵐ x ∂mu.restrict (ball x₀ R),
      ‖W1p.gradient w x‖ ^ 2 = ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 := by
    filter_upwards [W1p.gradient_contDiffComp_ae (by norm_num) hFC hMF hF0 (W1p.restrictL hU u),
      W1p.value_restrictL_ae hU u, W1p.gradient_restrictL_ae hU u, humR] with x hx hux hgx hmx
    rw [hx, hux, hgx, deriv_positiveCutoff hm _ (by linarith), Real.deriv_log, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos (hm.trans_le hmx)]
    ring
  -- The Poincaré–Wirtinger inequality for `w` on `B(x₀, R)`, then the logarithmic Caccioppoli
  -- inequality on the balls `B(x₀, R) ⊆ B(x₀, 2R)`, whose volume is `2ⁿ |B(x₀, R)|`.
  have hP := W1p.setIntegral_value_sub_setAverage_sq_le_of_ball_subset (Omega := U) hR subset_rfl w
  have hcacc := hc h ha hu hR (by linarith : R < 2 * R) hball hm hum
  have hvol : mu.real (ball x₀ (2 * R)) = 2 ^ n * mu.real (ball x₀ R) := by
    have hb : ∀ ρ : ℝ, 0 < ρ → mu.real (ball x₀ ρ) = ρ ^ n * mu.real (ball 0 1) := fun ρ hρ => by
      rw [measureReal_def, Measure.addHaar_ball_of_pos mu x₀ hρ, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
    rw [hb _ (by linarith), hb _ hR]
    ring
  calc ∫ x in ball x₀ R,
        (Real.log (W1p.value u x) - ⨍ y in ball x₀ R, Real.log (W1p.value u y) ∂mu) ^ 2 ∂mu
      = ∫ x in ball x₀ R, (W1p.value w x - ⨍ y in ball x₀ R, W1p.value w y ∂mu) ^ 2 ∂mu := by
        rw [average_congr hwv]
        exact integral_congr_ae (by filter_upwards [hwv] with x hx; rw [hx])
    _ ≤ (2 ^ (n + 1) * R) ^ 2 * ∫ x in ball x₀ R, ‖W1p.gradient w x‖ ^ 2 ∂mu := hP
    _ = (2 ^ (n + 1) * R) ^ 2 *
          ∫ x in ball x₀ R, ‖W1p.gradient u x‖ ^ 2 / W1p.value u x ^ 2 ∂mu := by
        rw [integral_congr_ae hwg]
    _ ≤ (2 ^ (n + 1) * R) ^ 2 *
          ((2 * Lam / lam) ^ 2 * (c / (2 * R - R)) ^ 2 * mu.real (ball x₀ (2 * R))) := by
        gcongr
    _ = (2 ^ (n + 1)) ^ 2 * 4 * c ^ 2 * 2 ^ n * (Lam / lam) ^ 2 * mu.real (ball x₀ R) := by
        rw [hvol, (by ring : 2 * R - R = R)]
        field_simp
        ring

end PDE

end TauCeti
