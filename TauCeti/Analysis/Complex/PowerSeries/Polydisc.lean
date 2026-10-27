/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Multivariate Cauchy expansions on polydiscs

The Cauchy integral on a polydisc expands into an unconditionally convergent series indexed
by exponent vectors. For a function continuous on the closed polydisc and holomorphic separately
in each open coordinate disc, the coefficients are its Cauchy integrals and the series recovers
the function throughout the open polydisc. A common boundary bound gives uniform convergence
in both parameters and evaluation points on every smaller closed polydisc. The codomain may be
any complex Banach space, and dimension zero is included.

The kernel expansion and interchange of integration and summation require only torus
integrability of the boundary values. The identification with the original function then
uses `ContinuousOn.torusIntegral_prod_sub_inv_smul`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter MeasureTheory Metric Real Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

/-- Expanding the product Cauchy kernel and integrating term by term is valid for every
torus-integrable function. The sum is unconditional over all multi-indices. -/
theorem hasSum_torusIntegral_prod_geometric {f : (Fin n → ℂ) → E}
    {c w : Fin n → ℂ} {R : Fin n → ℝ} (hf : TorusIntegrable f c R)
    (hw : ∀ i, ‖w i‖ < R i) :
    HasSum (fun α : Fin n → ℕ ↦ ∯ z in T(c, R),
      (∏ i, (w i / (z i - c i)) ^ α i / (z i - c i)) • f z)
      (∯ z in T(c, R), (∏ i, (z i - (c i + w i))⁻¹) • f z) := by
  have hR (i) : 0 < R i := (norm_nonneg _).trans_lt (hw i)
  have hnorm (θ : Fin n → ℝ) (i : Fin n) :=
    norm_torusMap_apply_sub_center (c := c) θ i (hR i).le
  have hne (θ : Fin n → ℝ) (i : Fin n) : torusMap c R θ i - c i ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnorm]; exact (hR i).ne')
  let q : Fin n → ℝ := fun i ↦ ‖w i‖ / R i
  have hq₀ (i) : 0 ≤ q i := div_nonneg (norm_nonneg _) (hR i).le
  have hq₁ (i) : q i < 1 := (div_lt_one (hR i)).mpr (hw i)
  have hs : Summable (fun α : Fin n → ℕ ↦ ∏ i, q i ^ α i) :=
    (hasSum_prod_geometric_of_norm_lt_one (fun i ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hq₀ i)] using hq₁ i)).summable
  -- The Jacobian cancels the reciprocal factors in the kernel, leaving a geometric majorant.
  have hb (α : Fin n → ℕ) (θ : Fin n → ℝ) :
      ‖(∏ i, (R i : ℂ) * exp (θ i * I) * I) •
        ((∏ i, (w i / (torusMap c R θ i - c i)) ^ α i /
          (torusMap c R θ i - c i)) • f (torusMap c R θ))‖ =
        ‖f (torusMap c R θ)‖ * ∏ i, q i ^ α i := by
    simp only [norm_smul, norm_prod, norm_mul, norm_I, mul_one, norm_real,
      norm_exp_ofReal_mul_I, norm_div, norm_pow, hnorm]
    rw [← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    dsimp [q]
    rw [abs_of_pos (hR i), ← mul_div_assoc, mul_div_cancel_left₀ _ (hR i).ne']
  -- Integrate the absolutely summable kernel expansion using the integrable boundary norm.
  unfold torusIntegral
  apply hasSum_integral_of_dominated_convergence
    (fun α θ ↦ ‖f (torusMap c R θ)‖ * ∏ i, q i ^ α i)
  · intro α
    apply AEStronglyMeasurable.smul
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · apply AEStronglyMeasurable.smul
      · exact Continuous.aestronglyMeasurable (by fun_prop (disch := intro θ; exact hne θ _))
      · exact hf.1
  · intro α
    exact ae_of_all _ fun θ ↦ (hb α θ).le
  · exact ae_of_all _ fun θ ↦ hs.mul_left _
  · simpa only [tsum_mul_left] using hf.norm.mul_const (∑' α : Fin n → ℕ, ∏ i, q i ^ α i)
  · apply ae_of_all
    intro θ
    have hg := hasSum_prod_geometric_div (z := fun i ↦ torusMap c R θ i - c i)
      (w := w) (fun i ↦ by simpa only [hnorm] using hw i)
    simpa only [sub_sub] using (hg.smul_const (f (torusMap c R θ))).const_smul
      (∏ i, (R i : ℂ) * exp (θ i * I) * I)

/-- A uniform bound on the distinguished boundary gives the geometric bound on every
multivariate Cauchy coefficient. No regularity of the boundary values is needed. -/
theorem norm_torusIntegral_cauchyCoeff_le {f : (Fin n → ℂ) → E}
    {c : Fin n → ℂ} {R : Fin n → ℝ} {M : ℝ} (hR : ∀ i, 0 < R i)
    (hf : ∀ z ∈ univ.pi (fun i ↦ sphere (c i) (R i)), ‖f z‖ ≤ M)
    (α : Fin n → ℕ) :
    ‖(2 * π * I : ℂ)⁻¹ ^ n •
      ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z‖ ≤
      M * ∏ i, (R i)⁻¹ ^ α i := by
  have hk (θ : Fin n → ℝ) :
      ‖(∏ i, (torusMap c R θ i - c i) ^ (α i + 1))⁻¹ • f (torusMap c R θ)‖ ≤
        (∏ i, (R i ^ (α i + 1))⁻¹) * M := by
    simp only [norm_smul, norm_inv, norm_prod, norm_pow,
      norm_torusMap_apply_sub_center θ _ (hR _).le, ← Finset.prod_inv_distrib]
    exact mul_le_mul_of_nonneg_left
      (hf _ (torusMap_mem_pi_sphere (fun i ↦ (hR i).le) θ))
      (Finset.prod_nonneg fun i _ ↦ inv_nonneg.mpr (pow_nonneg (hR i).le _))
  have hb := norm_torusIntegral_le_of_norm_le_const
    (f := fun z ↦ (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z) hk
  calc
    _ ≤ ‖(2 * π * I : ℂ)⁻¹ ^ n‖ *
        (((2 * π) ^ n * ∏ i, |R i|) * ((∏ i, (R i ^ (α i + 1))⁻¹) * M)) :=
      (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _ = M * ((∏ i, R i) * (∏ i, (R i ^ (α i + 1))⁻¹)) := by
      simp only [norm_pow, norm_inv, norm_mul, norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos pi_pos, abs_of_pos (hR _), Complex.norm_ofNat]
      rw [inv_pow]
      field_simp
    _ = M * ∏ i, (R i)⁻¹ ^ α i := by
      rw [← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [pow_succ, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ (hR i).ne', mul_one,
        inv_pow]

variable [CompleteSpace E]

/-- **The multivariate Cauchy expansion.** A function continuous on the closed polydisc and
holomorphic separately in each open coordinate disc is represented throughout the open polydisc
by its Cauchy coefficients. The exponent vector indexes an unconditionally convergent series,
so no choice of an enumeration is required. -/
theorem _root_.ContinuousOn.hasSum_torusIntegral_cauchyCoeff
    {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : ContinuousOn f (univ.pi fun i ↦ closedBall (c i) (R i)))
    (hd : ∀ z ∈ univ.pi (fun i ↦ closedBall (c i) (R i)), ∀ i, z i ∈ ball (c i) (R i) →
      DifferentiableAt ℂ (fun x ↦ f (Function.update z i x)) (z i))
    (hw : ∀ i, ‖w i‖ < R i) :
    HasSum (fun α : Fin n → ℕ ↦ (∏ i, w i ^ α i) •
      ((2 * π * I : ℂ)⁻¹ ^ n •
        ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z))
      (f (c + w)) := by
  have hR (i) : 0 < R i := (norm_nonneg _).trans_lt (hw i)
  have ht : TorusIntegrable f c R :=
    (hf.comp_continuous (continuous_torusMap c R) fun θ i _ ↦
      sphere_subset_closedBall (torusMap_mem_pi_sphere (fun i ↦ (hR i).le) θ i trivial))
      |>.integrableOn_Icc
  have h := (hasSum_torusIntegral_prod_geometric ht hw).const_smul
    ((2 * π * I : ℂ)⁻¹ ^ n)
  have hterm (α : Fin n → ℕ) :
      (∯ z in T(c, R), (∏ i, (w i / (z i - c i)) ^ α i / (z i - c i)) • f z) =
        (∏ i, w i ^ α i) •
          ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z := by
    rw [← torusIntegral_smul]
    congr 1
    funext z
    rw [smul_smul, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [pow_succ, div_eq_mul_inv, mul_pow, mul_comm, mul_left_comm]
  simp only [hterm, smul_comm ((2 * π * I : ℂ)⁻¹ ^ n)] at h
  have hc : c + w ∈ univ.pi (fun i ↦ ball (c i) (R i)) := by
    intro i _
    simpa only [mem_ball, dist_eq_norm, Pi.add_apply, add_sub_cancel_left] using hw i
  have hi := hf.torusIntegral_prod_sub_inv_smul hd hc
  simp only [Pi.add_apply] at hi
  simp only [Finset.prod_inv_distrib] at h
  rw [hi] at h
  simpa only [inv_pow, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ two_pi_I_ne_zero), one_smul] using h

/-- Multivariate Cauchy expansions converge uniformly in the parameter and the evaluation
point on every smaller closed polydisc, if each function is continuous on the closed polydisc
and holomorphic separately in each open coordinate disc, with a common bound on the distinguished
boundary. No topology on the parameter set is needed. -/
theorem tendstoUniformlyOn_torusIntegral_cauchyCoeff {P : Type*} {S : Set P}
    {f : P → (Fin n → ℂ) → E} {c : Fin n → ℂ} {R r : Fin n → ℝ} {M : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hrR : ∀ i, r i < R i)
    (hf : ∀ x ∈ S, ContinuousOn (f x) (univ.pi fun i ↦ closedBall (c i) (R i)))
    (hd : ∀ x ∈ S, ∀ z ∈ univ.pi (fun i ↦ closedBall (c i) (R i)), ∀ i,
      z i ∈ ball (c i) (R i) →
        DifferentiableAt ℂ (fun t ↦ f x (Function.update z i t)) (z i))
    (hb : ∀ x ∈ S, ∀ z ∈ univ.pi (fun i ↦ sphere (c i) (R i)), ‖f x z‖ ≤ M) :
    TendstoUniformlyOn
      (fun A : Finset (Fin n → ℕ) ↦ fun b : P × (Fin n → ℂ) ↦
        ∑ α ∈ A, (∏ i, b.2 i ^ α i) • ((2 * π * I : ℂ)⁻¹ ^ n •
          ∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f b.1 z))
      (fun b ↦ f b.1 (c + b.2)) atTop
      (S ×ˢ univ.pi fun i ↦ closedBall 0 (r i)) := by
  have hR (i) : 0 < R i := (hr i).trans_lt (hrR i)
  have hs : Summable (fun α : Fin n → ℕ ↦ ∏ i, (r i / R i) ^ α i) :=
    (hasSum_prod_geometric_of_norm_lt_one (r := fun i ↦ r i / R i) (fun i ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hr i) (hR i).le)]
      exact (div_lt_one (hR i)).mpr (hrR i))).summable
  apply (tendstoUniformlyOn_tsum (hs.mul_left M) ?_).congr_right
  · intro b hb'
    have hw (i : Fin n) : ‖b.2 i‖ < R i := by
      have hi : ‖b.2 i‖ ≤ r i := by
        simpa only [mem_closedBall, dist_zero_right] using hb'.2 i trivial
      exact hi.trans_lt (hrR i)
    exact ((hf b.1 hb'.1).hasSum_torusIntegral_cauchyCoeff (hd b.1 hb'.1) hw).tsum_eq
  · intro α b hb'
    rw [norm_smul, norm_prod]
    calc
      _ ≤ (∏ i, r i ^ α i) * (M * ∏ i, (R i)⁻¹ ^ α i) :=
        mul_le_mul
          (Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _)
            (fun i _ ↦ by
              rw [norm_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) (by
                simpa only [mem_closedBall, dist_zero_right] using hb'.2 i trivial) _))
          (norm_torusIntegral_cauchyCoeff_le hR (hb b.1 hb'.1) α)
          (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr i) _)
      _ = M * ∏ i, (r i / R i) ^ α i := by
        rw [mul_left_comm, ← Finset.prod_mul_distrib]
        simp only [← mul_pow, div_eq_mul_inv]

end TauCeti
