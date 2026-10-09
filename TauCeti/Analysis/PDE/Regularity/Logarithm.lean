/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
public import TauCeti.Analysis.Sobolev.W1p.ChainRule
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The logarithm of a positive weak supersolution

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, which is bounded below by a constant
`ε > 0`. Then `log u` is a Sobolev function with weak gradient `∇u / u`
(`TauCeti.W1p.exists_value_gradient_ae_eq_comp_of_le`), and this file shows that this gradient is
controlled by the ellipticity constants alone:

* the **logarithmic Caccioppoli inequality**: for every smooth `ψ` compactly supported in `Ω`,

  `∫_Ω ψ² ‖∇u‖² / u² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖²`.

  Unlike the Caccioppoli inequality for `u` itself, the right side does not involve `u` at all;
* on every ball with `B(x₀, 2r) ⊆ Ω`, the scale-invariant bound
  `∫_{B(x₀, r)} ‖∇u‖² / u² ≤ C (Λ/λ)² |B(x₀, r)| / r²`;
* consequently, by the Poincaré–Wirtinger inequality on balls, **`log u` has bounded mean
  oscillation**: `⨍_{B(x₀, r)} |log u - (log u)_{B(x₀, r)}| ≤ C Λ/λ` on every such ball.

The constants `C` depend only on the dimension; nothing depends on `u` or on the lower bound `ε`,
which serves only to make `u⁻¹` and `log u` Sobolev functions. No regularity of the coefficients
beyond measurability is used.

The mean oscillation bound is the hypothesis of the John–Nirenberg inequality. In Moser's proof of
the weak Harnack inequality, John–Nirenberg turns it into the crossover estimate
`⨍_B u^p · ⨍_B u^{-p} ≤ C` for a small `p > 0`, which links bounds on negative powers of a
supersolution to bounds on positive ones.

The inequalities are proved by testing the supersolution inequality against `ψ² u⁻¹`, whose
gradient is `-ψ² u⁻² ∇u + 2ψ u⁻¹ ∇ψ`: ellipticity bounds `ψ² ⟨a ∇u, ∇u⟩ / u²` below by
`λ ψ² ‖∇ log u‖²`, and Young's inequality absorbs the cross term.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le`: the
  logarithmic Caccioppoli inequality.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_div_value_sq_le`: the bound for
  `∫ ‖∇ log u‖²` on balls.
* `TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le`: `log u` has bounded mean
  oscillation.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6 (the proof of Theorem 8.18).
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- The squared norm `(‖∇u‖ / u)²` of the gradient of `log u` is integrable on `Ω` when `u` is
bounded below by a positive constant. -/
private theorem integrable_norm_gradient_div_value_sq {u : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε)
    (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) :
    Integrable (fun x => (‖W1p.gradient u x‖ / W1p.value u x) ^ 2) (mu.restrict Omega) := by
  refine ((W1p.integrable_norm_gradient_sq u).const_mul (ε ^ 2)⁻¹).mono' ?_ ?_
  · exact (((Lp.aestronglyMeasurable (W1p.gradient u)).aemeasurable.norm.div
      (Lp.aestronglyMeasurable (W1p.value u)).aemeasurable).pow_const 2).aestronglyMeasurable
  · filter_upwards [hεu] with x hx
    have hU : 0 < W1p.value u x := hε.trans_le hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow, div_eq_inv_mul]
    gcongr

/-- The pointwise form of the logarithmic Caccioppoli inequality. At a point where `u` has value
`U > 0` and gradient `G`, and the cutoff has value `z` and gradient `q`, the test function `ψ² u⁻¹`
has gradient `-z² U⁻² G + 2 z U⁻¹ q`. Pairing it with `G` through a matrix `A` that is
elliptic and bounded with constants `λ, Λ` controls `z² ‖G / U‖²`, the integrand of
`∫ ψ² ‖∇ log u‖²`, up to the error `‖q‖²`. -/
private theorem mul_sq_mul_div_sq_le_neg_matrixBilinearForm_add {A : Matrix ι ι ℝ}
    (hlam : 0 < lam) (hlower : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hupper : ∀ η ξ : EuclideanSpace ℝ ι, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    {U : ℝ} (hU : 0 < U) (z : ℝ) (G q : EuclideanSpace ℝ ι) :
    lam * (z ^ 2 * (‖G‖ / U) ^ 2) ≤
      -matrixBilinearForm A ((-(z ^ 2 * (U ^ 2)⁻¹)) • G + (2 * z * U⁻¹) • q) G
        + lam / 2 * (z ^ 2 * (‖G‖ / U) ^ 2) + 2 * Lam ^ 2 / lam * ‖q‖ ^ 2 := by
  -- In terms of `g = U⁻¹ G`, the gradient of `log u`, this is the absorption estimate
  -- `mul_sq_mul_norm_sq_le_matrixBilinearForm_add` with the weight `-1`.
  set g : EuclideanSpace ℝ ι := U⁻¹ • G
  have hg : ‖g‖ = ‖G‖ / U := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hU, inv_mul_eq_div]
  have key := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam z (-1) g q (hlower g)
    (hupper q g)
  set X := z • (z • g + (-1 : ℝ) • q) + (z * -1) • q
  have hη : (-(z ^ 2 * (U ^ 2)⁻¹)) • G + (2 * z * U⁻¹) • q = (-U⁻¹) • X := by
    simp only [X, g]
    module
  have hGU : G = U • g := by
    simp only [g, smul_smul, mul_inv_cancel₀ hU.ne', one_smul]
  have hB : matrixBilinearForm A ((-U⁻¹) • X) (U • g) = -matrixBilinearForm A X g := by
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
  rw [hη, ← hg, hGU, hB, neg_neg]
  rw [neg_one_sq, mul_one] at key
  linarith

omit [DecidableEq ι] in
/-- The test function `ψ² u⁻¹` of the logarithmic Caccioppoli inequality. If `u ∈ H¹(Ω)` is
bounded below by a positive constant and `ψ` is smooth and compactly supported in `Ω`, then
`ψ² u⁻¹ ∈ H¹₀(Ω)`, with weak gradient `-ψ² u⁻² ∇u + 2 ψ u⁻¹ ∇ψ`. -/
private theorem exists_w1p0_value_gradient_ae_eq_sq_mul_inv {u : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega,
        W1p.value (v : W1p mu Omega 2) x = ψ x ^ 2 * (W1p.value u x)⁻¹) ∧
      ∀ᵐ x ∂mu.restrict Omega, W1p.gradient (v : W1p mu Omega 2) x =
        (-(ψ x ^ 2 * (W1p.value u x ^ 2)⁻¹)) • W1p.gradient u x +
          (2 * ψ x * (W1p.value u x)⁻¹) • ∇ ψ x := by
  -- The Sobolev function `u⁻¹`, with weak gradient `-u⁻² ∇u`.
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_comp_of_le (φ := fun t : ℝ => t⁻¹)
    (by simp) (contDiffOn_inv ℝ |>.mono fun t ht => ne_of_gt ht) hε (M := (ε ^ 2)⁻¹)
    (fun t ht => by
      have ht0 : 0 < t := hε.trans_le ht
      rw [deriv_inv, abs_neg, abs_of_pos (by positivity)]
      gcongr) hεu
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- `ψ² u⁻¹ = ψ (ψ u⁻¹)`, by the Leibniz rule twice.
  set w₁ := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w₁
  refine ⟨⟨v, W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM'
    hgradM' hcpt hts w₁⟩, ?_, ?_⟩
  · filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w₁,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w, hwv] with x h1 h2 h3
    rw [h1, h2, h3, smul_eq_mul, smul_eq_mul]
    ring
  · filter_upwards [hwv, hwg, W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w₁,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w] with x hwvx hwgx hg1 hg2 hv2
    rw [hg1, hg2, hv2, hwgx, hwvx, deriv_inv]
    simp only [smul_eq_mul]
    module

/-- **The logarithmic Caccioppoli inequality.** Let `a` be measurable and uniformly elliptic on
`Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ ε`
almost everywhere for some `ε > 0`. Then for every smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² (‖∇u‖ / u)² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖²`.

The integrand on the left is `ψ² ‖∇ log u‖²`, and the right side depends on neither `u` nor
`ε`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_div_value_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {ε : ℝ} (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu := by
  have hlam := h.pos
  -- Test the inequality against `v = ψ² u⁻¹ ≥ 0`.
  obtain ⟨v, hvv, hvg⟩ := exists_w1p0_value_gradient_ae_eq_sq_mul_inv hε hεu hψ hcpt hts
  have hpos := hu v (by
    filter_upwards [hvv, hεu] with x h1 h2
    rw [h1]
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hε.le.trans h2)))
  rw [energyFormH1_def] at hpos
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0) (gamma := 0)
    ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u (v : W1p mu Omega 2)
  -- The pointwise estimate.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2) ≤
        -energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField (v : W1p mu Omega 2) x)
          + lam / 2 * (ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2)
          + 2 * Lam ^ 2 / lam * ‖∇ ψ x‖ ^ 2 := by
    filter_upwards [hmem, hεu, hvg] with x hx hux hgx
    rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgx]
    simp only [Pi.zero_apply, driftForm_apply, massForm_apply, inner_zero_left, zero_mul,
      add_zero]
    exact mul_sq_mul_div_sq_le_neg_matrixBilinearForm_add hlam (h.lower_bound hx)
      (h.upper_bound hx) (hε.trans_le hux) (ψ x) (W1p.gradient u x) (∇ ψ x)
  -- Integrability of the three terms.
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hF : Integrable (fun x => ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2)
      (mu.restrict Omega) :=
    (integrable_norm_gradient_div_value_sq hε hεu).bdd_mul
      (hψ.continuous.pow 2).aestronglyMeasurable (c := M ^ 2) (Filter.Eventually.of_forall
        fun x => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2)
  have hY : Integrable (fun x => ‖∇ ψ x‖ ^ 2) (mu.restrict Omega) := by
    have hs : HasCompactSupport (fun x => ‖∇ ψ x‖ ^ 2) := hcpt.mono' fun x hx => by
      by_contra hxt
      have hfd : fderiv ℝ ψ x = 0 :=
        Function.notMem_support.1 fun h' => hxt (support_fderiv_subset ℝ h')
      simp [_root_.gradient, hfd] at hx
    exact (((ContDiff.continuous_gradient hψ).norm.pow 2).integrable_of_hasCompactSupport
      hs).restrict
  -- Integrate the pointwise estimate and absorb half of the left side.
  have hI : ∫ x in Omega, lam * (ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2) ∂mu ≤
      ∫ x in Omega, (-energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField (v : W1p mu Omega 2) x)
          + lam / 2 * (ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2)
          + 2 * Lam ^ 2 / lam * ‖∇ ψ x‖ ^ 2) ∂mu :=
    integral_mono_ae (hF.const_mul lam) ((hE.neg.add (hF.const_mul _)).add (hY.const_mul _)) hpt
  rw [integral_const_mul, integral_add, integral_add, integral_neg, integral_const_mul,
    integral_const_mul] at hI
  rotate_left
  · exact hE.neg
  · exact hF.const_mul _
  · exact hE.neg.add (hF.const_mul _)
  · exact hY.const_mul _
  set X := ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu
  have hhalf : lam / 2 * X ≤ 2 * Lam ^ 2 / lam * Y := by linarith
  calc X = 2 / lam * (lam / 2 * X) := by field_simp
    _ ≤ 2 / lam * (2 * Lam ^ 2 / lam * Y) := by gcongr
    _ = (2 * Lam / lam) ^ 2 * Y := by field_simp

/-- **The gradient of `log u` on balls.** There is a constant `C ≥ 0`, depending only on the
dimension, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` with
`u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball with `B(x₀, 2r) ⊆ Ω`,

`∫_{B(x₀, r)} (‖∇u‖ / u)² ≤ C (Λ/λ)² |B(x₀, r)| / r²`.

So the average of `‖∇ log u‖²` over `B(x₀, r)` is at most `C (Λ/λ)² r⁻²`, the power of `r`
dictated by scaling. -/
theorem exists_setIntegral_ball_norm_gradient_div_value_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < r → Metric.ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
        C * (Lam / lam) ^ 2 * mu.real (Metric.ball x₀ r) / r ^ 2 := by
  obtain ⟨c, hc0, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨16 * c ^ 2 * (3 / 2) ^ Fintype.card ι, by positivity, ?_⟩
  intro mu _ Omega a lam Lam u ε x₀ r h ha hu hε hεu hr hball
  have hlam := h.pos
  -- A cutoff equal to `1` on `B(x₀, r)`, supported in `closedBall x₀ (3r/2)`, with `‖∇ψ‖ ≤ 2c/r`.
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg⟩ := hcut x₀ hr (by linarith : r < 3 * r / 2)
  have hR : 3 * r / 2 - r = r / 2 := by ring
  rw [hR] at hψg
  have hclosed : Metric.closedBall x₀ (3 * r / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hcpt : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ (3 * r / 2))
      (subset_tsupport ψ |>.trans hψts)
  have hcacc := h.setIntegral_sq_mul_norm_gradient_div_value_sq_le ha hu hε hεu hψ hcpt
    (hψts.trans hclosed)
  have hmeasB : MeasurableSet (Metric.closedBall x₀ (3 * r / 2)) := measurableSet_closedBall
  -- The gradient of the cutoff is supported in `closedBall x₀ (3r/2)`, where it is at most `2c/r`.
  have hgrad : ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu ≤
      (2 * c / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2)) := by
    calc ∫ x in Omega, ‖∇ ψ x‖ ^ 2 ∂mu
        ≤ ∫ x in Omega, (Metric.closedBall x₀ (3 * r / 2)).indicator
            (fun _ => (2 * c / r) ^ 2) x ∂mu := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
              hmeasB).restrict
            (Filter.Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ Metric.closedBall x₀ (3 * r / 2)
          · rw [indicator_of_mem hx]
            have := hψg x
            rw [div_div_eq_mul_div, mul_comm c 2] at this
            exact pow_le_pow_left₀ (norm_nonneg _) this 2
          · have hfd : fderiv ℝ ψ x = 0 := Function.notMem_support.1 fun hx' =>
              hx (hψts (support_fderiv_subset ℝ hx'))
            simp [indicator_of_notMem hx, _root_.gradient, hfd]
      _ ≤ (2 * c / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2)) := by
          rw [integral_indicator_const _ hmeasB, smul_eq_mul, mul_comm]
          gcongr
          rw [measureReal_restrict_apply hmeasB]
          exact measureReal_mono inter_subset_left measure_closedBall_lt_top.ne
  -- On `B(x₀, r)` the cutoff is `1`, so the integral there is dominated by the weighted one.
  have hweighted : Integrable (fun x => ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2)
      (mu.restrict Omega) :=
    (integrable_norm_gradient_div_value_sq hε hεu).bdd_mul
      (hψ.continuous.pow 2).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall
        fun x => by
          obtain ⟨h0, h1⟩ := hψr (mem_range_self x)
          rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
          exact pow_le_one₀ h0 h1)
  have hleft : ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu := by
    calc ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu
        = ∫ x in Metric.ball x₀ r, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu :=
          setIntegral_congr_fun measurableSet_ball fun x hx => by
            rw [hψ1 (Metric.ball_subset_closedBall hx)]
            simp
      _ ≤ ∫ x in Omega, ψ x ^ 2 * (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu :=
          setIntegral_mono_set hweighted (Filter.Eventually.of_forall fun x => by positivity)
            ((Metric.ball_subset_ball (by linarith)).trans hball).eventuallyLE
  -- Both balls have measure proportional to the `n`-th power of the radius.
  have hvol : mu.real (Metric.closedBall x₀ (3 * r / 2)) =
      (3 / 2) ^ Fintype.card ι * mu.real (Metric.ball x₀ r) := by
    have hb : mu.real (Metric.ball x₀ r) = r ^ Fintype.card ι * mu.real (Metric.ball 0 1) := by
      rw [measureReal_def, Measure.addHaar_ball_of_pos mu x₀ hr, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), measureReal_def, finrank_euclideanSpace]
    rw [Measure.addHaar_real_closedBall mu x₀ (by positivity), hb, finrank_euclideanSpace]
    ring
  calc ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu
      ≤ (2 * Lam / lam) ^ 2 * ((2 * c / r) ^ 2 * mu.real (Metric.closedBall x₀ (3 * r / 2))) :=
        hleft.trans (hcacc.trans (by gcongr))
    _ = 16 * c ^ 2 * (3 / 2) ^ Fintype.card ι * (Lam / lam) ^ 2 * mu.real (Metric.ball x₀ r) /
          r ^ 2 := by
        rw [hvol]
        field_simp
        ring

omit [DecidableEq ι] in
/-- The logarithm of a Sobolev function bounded below by a positive constant is a Sobolev
function, with weak gradient `u⁻¹ ∇u`. -/
private theorem exists_value_gradient_ae_eq_log {u : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε)
    (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) :
    ∃ w : W1p mu Omega 2,
      W1p.value w =ᵐ[mu.restrict Omega] (fun x => Real.log (W1p.value u x)) ∧
        W1p.gradient w =ᵐ[mu.restrict Omega] fun x => (W1p.value u x)⁻¹ • W1p.gradient u x := by
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_comp_of_le (φ := Real.log) (by simp)
    (Real.contDiffOn_log.mono fun t ht => ne_of_gt ht) hε (M := ε⁻¹) (fun t ht => by
      rw [Real.deriv_log, abs_inv, abs_of_pos (hε.trans_le ht)]
      exact inv_anti₀ hε ht) hεu
  exact ⟨w, hwv, hwg.mono fun x hx => by simp only [hx, Real.deriv_log]⟩

omit [DecidableEq ι] in
/-- **The Poincaré–Wirtinger inequality for `log u` on a ball.** If `u ∈ H¹(Ω)` is bounded below
by a positive constant and `B(x₀, r) ⊆ Ω`, then `log u` deviates in `L²(B(x₀, r))` from its mean
over the ball by at most `2ⁿ⁺¹ r` times the `L²` norm of `∇ log u = ‖∇u‖ / u` there. -/
private theorem setIntegral_ball_log_sub_setAverage_sq_le {u : W1p mu Omega 2} {ε : ℝ}
    (hε : 0 < ε) (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) {x₀ : EuclideanSpace ℝ ι}
    {r : ℝ} (hr : 0 < r) (hBsub : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Metric.ball x₀ r, (Real.log (W1p.value u x) -
        ⨍ y in Metric.ball x₀ r, Real.log (W1p.value u y) ∂mu) ^ 2 ∂mu ≤
      (2 ^ (Fintype.card ι + 1) * r) ^ 2 *
        ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu := by
  obtain ⟨w, hwv, hwg⟩ := exists_value_gradient_ae_eq_log hε hεu
  -- Restrict `log u` to the ball `B = B(x₀, r)`, viewed as a domain of its own.
  set B : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩
  have hB : B ≤ Omega := hBsub
  set wB := W1p.restrictL hB w
  set f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (W1p.value u x)
  set m := ⨍ y in Metric.ball x₀ r, f y ∂mu
  have hval : W1p.value wB =ᵐ[mu.restrict (Metric.ball x₀ r)] f :=
    (W1p.value_restrictL_ae hB w).trans (ae_restrict_of_ae_restrict_of_subset hBsub hwv)
  have hgradB : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ r),
      ‖W1p.gradient wB x‖ ^ 2 = (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 := by
    filter_upwards [W1p.gradient_restrictL_ae hB w,
      ae_restrict_of_ae_restrict_of_subset hBsub hwg,
      ae_restrict_of_ae_restrict_of_subset hBsub hεu] with x h1 h2 h3
    rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le h3),
      inv_mul_eq_div]
  -- The Poincaré–Wirtinger inequality on `B`, in `L²`.
  have hP := W1p.eLpNorm_value_sub_setAverage_le_of_eq_ball (p := 2) (by simp) hr
    (rfl : (B : Set (EuclideanSpace ℝ ι)) = Metric.ball x₀ r) wB
  have havg : ⨍ y in (B : Set (EuclideanSpace ℝ ι)), W1p.value wB y ∂mu = m :=
    average_congr hval
  rw [havg, finrank_euclideanSpace] at hP
  have hcongr : (fun x => W1p.value wB x - m) =ᵐ[mu.restrict (Metric.ball x₀ r)]
      fun x => f x - m := hval.mono fun x hx => congrArg (· - m) hx
  replace hP : eLpNorm (fun x => f x - m) 2 (mu.restrict (Metric.ball x₀ r)) ≤
      ENNReal.ofReal (2 ^ (Fintype.card ι + 1) * r) * ‖W1p.gradient wB‖ₑ :=
    (eLpNorm_congr_ae hcongr).symm.trans_le hP
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ r)) :=
    isFiniteMeasure_restrict.2 (measure_ball_lt_top (μ := mu)).ne
  have hmem : MemLp (fun x => f x - m) 2 (mu.restrict (Metric.ball x₀ r)) :=
    ((Lp.memLp (W1p.value wB)).sub (memLp_const m)).ae_eq hcongr
  -- Convert the `eLpNorm` bound into a bound on integrals of squares.
  have hnorm : ‖hmem.toLp _‖ ≤ 2 ^ (Fintype.card ι + 1) * r * ‖W1p.gradient wB‖ := by
    rw [Lp.norm_toLp, ← toReal_enorm (W1p.gradient wB),
      ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ (Fintype.card ι + 1) * r),
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (by finiteness) hP
  have hsq : ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu = ‖hmem.toLp _‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs]
  have hgrad : ‖W1p.gradient wB‖ ^ 2 =
      ∫ x in Metric.ball x₀ r, (‖W1p.gradient u x‖ / W1p.value u x) ^ 2 ∂mu := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    exact integral_congr_ae hgradB
  rw [hsq, ← hgrad, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **The logarithm of a positive supersolution has bounded mean oscillation.** There is a
constant `C ≥ 0`, depending only on the dimension, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a
weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` with `u ≥ ε` almost everywhere for some `ε > 0`. Then on
every ball with `B(x₀, 2r) ⊆ Ω`,

`⨍_{B(x₀, r)} |log u - ⨍_{B(x₀, r)} log u| ≤ C Λ/λ`.

The bound is uniform over all such balls, and independent of `u` and `ε`: this is the hypothesis
of the John–Nirenberg inequality for `log u`. -/
theorem exists_setAverage_abs_log_sub_setAverage_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      0 < r → Metric.ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍ x in Metric.ball x₀ r, |Real.log (W1p.value u x) -
          ⨍ y in Metric.ball x₀ r, Real.log (W1p.value u y) ∂mu| ∂mu ≤ C * (Lam / lam) := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_div_value_sq_le (ι := ι)
  refine ⟨2 ^ (Fintype.card ι + 1) * √C, by positivity, ?_⟩
  intro mu _ Omega a lam Lam u ε x₀ r h ha hu hε hεu hr hball
  have hBsub : Metric.ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  set f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (W1p.value u x)
  set m := ⨍ y in Metric.ball x₀ r, f y ∂mu
  have hB0 : mu (Metric.ball x₀ r) ≠ 0 := (Metric.measure_ball_pos mu x₀ hr).ne'
  have hBtop : mu (Metric.ball x₀ r) ≠ (⊤ : ℝ≥0∞) := (measure_ball_lt_top (μ := mu)).ne
  have hBpos : 0 < mu.real (Metric.ball x₀ r) := ENNReal.toReal_pos hB0 hBtop
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ r)) := isFiniteMeasure_restrict.2 hBtop
  obtain ⟨w, hwv, -⟩ := exists_value_gradient_ae_eq_log hε hεu
  have hmem : MemLp (fun x => f x - m) 2 (mu.restrict (Metric.ball x₀ r)) :=
    (((Lp.memLp (W1p.value w)).ae_eq hwv).mono_measure
      (Measure.restrict_mono hBsub le_rfl)).sub (memLp_const m)
  -- Jensen's inequality bounds the `L¹` mean oscillation by the `L²` one.
  have hgi : Integrable (fun x => |f x - m| ^ 2) (mu.restrict (Metric.ball x₀ r)) := by
    simpa only [sq_abs] using hmem.integrable_sq
  have hJ : (⨍ x in Metric.ball x₀ r, |f x - m| ∂mu) ^ 2 ≤
      ⨍ x in Metric.ball x₀ r, |f x - m| ^ 2 ∂mu :=
    ConvexOn.map_set_average_le (convexOn_pow 2) (continuous_pow 2).continuousOn isClosed_Ici
      hB0 hBtop (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (hmem.integrable one_le_two).abs hgi
  have hJ' : ⨍ x in Metric.ball x₀ r, |f x - m| ^ 2 ∂mu =
      (mu.real (Metric.ball x₀ r))⁻¹ * ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu := by
    simp [setAverage_eq, sq_abs]
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (by positivity) (div_nonneg h.upper_nonneg h.pos.le)) (hJ.trans ?_)
  rw [hJ']
  -- Poincaré–Wirtinger for `log u`, then the gradient bound for `log u` on the ball.
  calc (mu.real (Metric.ball x₀ r))⁻¹ * ∫ x in Metric.ball x₀ r, (f x - m) ^ 2 ∂mu
      ≤ (mu.real (Metric.ball x₀ r))⁻¹ * ((2 ^ (Fintype.card ι + 1) * r) ^ 2 *
          (C * (Lam / lam) ^ 2 * mu.real (Metric.ball x₀ r) / r ^ 2)) := by
        gcongr
        exact (setIntegral_ball_log_sub_setAverage_sq_le hε hεu hr hBsub).trans
          (by gcongr; exact hC mu h ha hu hε hεu hr hball)
    _ = (2 ^ (Fintype.card ι + 1) * √C * (Lam / lam)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC0]
        field_simp

end PDE

end TauCeti
