/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import TauCeti.Analysis.InnerProductSpace.LyapunovForm
public import TauCeti.Analysis.Normed.Operator.HurwitzStable
public import TauCeti.Analysis.Polynomial.HalfPlane

/-!
# Exponential dichotomy of hyperbolic linear flows

A linear operator `A` on a finite-dimensional real space is *hyperbolic* when its
complexification has no eigenvalue on the imaginary axis. Over `ℝ` this says that there are no
`ω : ℝ` and vectors `v, w`, not both zero, with `A v = -ω • w` and `A w = ω • v`: such a pair
spans the real and imaginary parts of an eigenvector `v + i w` with eigenvalue `i ω`.

This file proves that the flow of a hyperbolic operator has an *exponential dichotomy*
(`ContinuousLinearMap.exists_projection_exponential_bounds`): there is an idempotent `P`
commuting with `A` such that `exp (t • A)` contracts the range of `P` exponentially in forward
time and the kernel of `P` exponentially in backward time, with a common rate. These are exactly
the hypotheses of the Lyapunov--Perron construction of local stable and unstable manifolds in
`TauCeti.Analysis.ODE.LyapunovPerron.VectorField`, so that construction applies at every
hyperbolic zero of a `C^n` vector field. In particular an operator with a Lyapunov form has an
exponential dichotomy (`ContinuousLinearMap.HasLyapunovForm.exists_projection_exponential_bounds`).
The symmetric case, with orthogonal spectral subspaces, is in
`TauCeti.Analysis.ODE.ExponentialDichotomy`.

## The construction

Hyperbolicity means that no complex root of the minimal polynomial `μ` of `A` lies on the
imaginary axis (`ContinuousLinearMap.re_ne_zero_of_aeval_minpoly_eq_zero`). Then `μ = p * q` with
the complex roots of `p` in the left half-plane and those of `q` in the right half-plane
(`Polynomial.exists_eq_mul_forall_re_neg_forall_re_pos`). These factors are coprime, say
`u * p + v * q = 1`, and `P = (v * q)(A)` is the projection onto `ker p(A)` along `ker q(A)`.
The operator `B = A P - (1 - P)`, again a polynomial in `A`, is annihilated by `p * (X + 1)`, whose
roots all have negative real part, so its flow decays exponentially
(`ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`); and `exp (t • B)` agrees with
`exp (t • A)` on the range of `P`. The backward estimate is the forward one for `-A`.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, third edition, Academic Press, 2013, Chapter 7.
* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer, 1978.
-/

public section

open NormedSpace Polynomial
open scoped NNReal

namespace ContinuousLinearMap

/-- A factor of positive degree of the minimal polynomial of an operator on a finite-dimensional
space has a nonzero vector in the kernel of its evaluation at the operator. -/
theorem exists_ne_zero_aeval_apply_eq_zero_of_dvd_minpoly {𝕜 V : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] {A : V →L[𝕜] V} {q : 𝕜[X]} (hq : q ∣ minpoly 𝕜 A)
    (hdeg : 0 < q.natDegree) : ∃ v : V, v ≠ 0 ∧ aeval A q v = 0 := by
  obtain ⟨r, hr⟩ := hq
  by_contra! hinj
  have hint : IsIntegral 𝕜 A := .of_finite 𝕜 A
  -- If `q(A)` were injective, then `r(A) = 0`, but `r` has smaller degree than `μ`.
  have hrA : aeval A r = 0 := by
    ext x
    by_contra hx
    refine hinj _ hx ?_
    rw [← mul_apply_eq_comp, ← map_mul, ← hr, minpoly.aeval, zero_apply]
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact minpoly.ne_zero hint (by rw [hr, mul_zero])
  have hle := natDegree_le_of_dvd (minpoly.dvd 𝕜 A hrA) hr0
  rw [hr, natDegree_mul (by rintro rfl; simp at hdeg) hr0] at hle
  lia

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **No root of the minimal polynomial of a hyperbolic operator is purely imaginary.** If there
are no `ω` and `v, w`, not both zero, with `A v = -ω • w` and `A w = ω • v`, then every complex
root of the minimal polynomial of `A` has nonzero real part. -/
theorem re_ne_zero_of_aeval_minpoly_eq_zero {A : E →L[ℝ] E}
    (hA : ∀ (ω : ℝ) (v w : E), A v = -ω • w → A w = ω • v → v = 0 ∧ w = 0) {z : ℂ}
    (hz : aeval z (minpoly ℝ A) = 0) : z.re ≠ 0 := by
  intro hre
  by_cases him : z.im = 0
  · -- `z = 0` is a root, so `A` has a nonzero kernel vector.
    have hz0 : z = algebraMap ℝ ℂ 0 := Complex.ext (by simpa using hre) (by simpa using him)
    rw [hz0, aeval_algebraMap_apply_eq_algebraMap_eval, map_eq_zero, ← IsRoot,
      ← dvd_iff_isRoot] at hz
    obtain ⟨v, hv, hAv⟩ := exists_ne_zero_aeval_apply_eq_zero_of_dvd_minpoly hz (by simp)
    simp only [aeval_X, map_zero, sub_zero] at hAv
    exact hv (hA 0 v 0 (by simp [hAv]) (by simp)).1
  · -- `z = ± i ‖z‖`, so `A ^ 2 + ‖z‖ ^ 2` has a nonzero kernel vector `v`, and
    -- `(v, -‖z‖⁻¹ • A v)` rotates under `A` with angular speed `‖z‖`.
    have hdvd := quadratic_dvd_of_aeval_eq_zero_im_ne_zero _ hz him
    have hdeg : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)).natDegree = 2 := by compute_degree!
    obtain ⟨v, hv, hAv⟩ := exists_ne_zero_aeval_apply_eq_zero_of_dvd_minpoly hdvd (by lia)
    have hc : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr fun h ↦ him (by simp [h])
    simp only [hre, mul_zero, map_zero, zero_mul, sub_zero, map_add, aeval_X_pow, aeval_C,
      add_apply, algebraMap_apply] at hAv
    have hAAv : A (A v) = -(‖z‖ ^ 2) • v := by
      rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, ← hAv, pow_two A, mul_apply_eq_comp]
    refine hv (hA ‖z‖ v (-‖z‖⁻¹ • A v) ?_ ?_).1
    · rw [smul_smul, neg_mul_neg, mul_inv_cancel₀ hc, one_smul]
    · rw [map_smul, hAAv, smul_smul, neg_mul_neg, pow_two, ← mul_assoc, inv_mul_cancel₀ hc,
        one_mul]

/-- The forward half of the dichotomy. If `p(A) q(A) = 0` with `u * p + v * q = 1` and the complex
roots of `p` have negative real part, then the flow of `A` decays exponentially on the range of
`(v * q)(A)`, the projection onto `ker p(A)` along `ker q(A)`. -/
private theorem exists_norm_exp_smul_mul_aeval_le {A : E →L[ℝ] E} {p q u v : ℝ[X]}
    (hpq : aeval A (p * q) = 0) (huv : u * p + v * q = 1)
    (hp : ∀ z : ℂ, aeval z p = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t →
      ‖exp (t • A) * aeval A (v * q)‖ ≤ K * Real.exp (-α * t) := by
  -- `B = s(A)` acts as `A` on `ker p(A)` and as `-1` on `ker q(A)`.
  set s : ℝ[X] := X * (v * q) - u * p
  have hsX : s - X = -((X + 1) * u * p) := by linear_combination X * huv
  have hs1 : s + 1 = (X + 1) * (v * q) := by linear_combination -huv
  have hps : p ∣ p.comp s := by
    have h := sub_dvd_eval_sub s X (p.map C)
    rw [eval_map, eval_map, eval₂_C_X, ← algebraMap_eq, ← aeval_def, ← comp_eq_aeval] at h
    have hp' : p ∣ s - X := ⟨-((X + 1) * u), by rw [hsX]; ring⟩
    simpa using (hp'.trans h).add (dvd_refl p)
  have hB : aeval (aeval A s) (p * (X + 1)) = 0 := by
    rw [← aeval_comp, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.one_comp, hs1]
    refine aeval_eq_zero_of_dvd_aeval_eq_zero ?_ hpq
    exact mul_dvd_mul hps ⟨(X + 1) * v, by ring⟩
  obtain ⟨K, α, hα, hK⟩ := exists_norm_exp_smul_le_of_aeval_eq_zero (aeval A s) hB
    fun z hz ↦ by
      rw [map_mul, mul_eq_zero] at hz
      rcases hz with hz | hz
      · exact hp z hz
      · simp only [map_add, aeval_X, map_one, add_eq_zero_iff_eq_neg] at hz
        simp [hz]
  refine ⟨K * ‖aeval A (v * q)‖, α, hα, fun t ht ↦ ?_⟩
  -- `s(A) = A + D` with `D` commuting with `A` and killing the range of `(v * q)(A)`.
  set D := aeval A (s - X)
  have hDP : t • D * aeval A (v * q) = 0 := by
    rw [smul_mul_assoc, ← map_mul, aeval_eq_zero_of_dvd_aeval_eq_zero _ hpq, smul_zero]
    exact ⟨-((X + 1) * u * v), by rw [hsX]; ring⟩
  have hsD : aeval A s = A + D := by
    simp only [D, map_sub, aeval_X]
    abel
  have hAD : Commute A D := by simpa using (Commute.all (X : ℝ[X]) (s - X)).map (aeval A)
  have hsplit : exp (t • aeval A s) = exp (t • A) * exp (t • D) := by
    let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
    rw [hsD, smul_add, exp_add_of_commute ((hAD.smul_left t).smul_right t)]
  have hexp : exp (t • A) * aeval A (v * q) = exp (t • aeval A s) * aeval A (v * q) := by
    let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
    rw [hsplit, mul_assoc, exp_mul_of_mul_eq_zero hDP]
  rw [hexp]
  calc ‖exp (t • aeval A s) * aeval A (v * q)‖
      ≤ ‖exp (t • aeval A s)‖ * ‖aeval A (v * q)‖ := norm_mul_le _ _
    _ ≤ K * Real.exp (-α * t) * ‖aeval A (v * q)‖ := by gcongr; exact hK t ht
    _ = K * ‖aeval A (v * q)‖ * Real.exp (-α * t) := by ring

/-- **Exponential dichotomy of a hyperbolic operator.** If an operator `A` on a finite-dimensional
real space has no eigenvalue on the imaginary axis, in the sense that there are no `ω` and `v, w`,
not both zero, with `A v = -ω • w` and `A w = ω • v`, then there are an idempotent `P` commuting
with `A` and constants `K, α > 0` such that `exp (t • A)` contracts the range of `P` at rate `α`
for `t ≥ 0` and the kernel of `P` at rate `α` for `t ≤ 0`. -/
theorem exists_projection_exponential_bounds (A : E →L[ℝ] E)
    (hA : ∀ (ω : ℝ) (v w : E), A v = -ω • w → A w = ω • v → v = 0 ∧ w = 0) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧
      ∃ (K α : ℝ≥0), 0 < K ∧ 0 < α ∧
        (∀ t : ℝ, 0 ≤ t → ∀ z : E, ‖exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ z : E,
          ‖exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖) := by
  -- Split the minimal polynomial `μ = p * q` along the imaginary axis; `P = (v * q)(A)`.
  obtain ⟨p, q, hpq, hp, hq⟩ :=
    exists_eq_mul_forall_re_neg_forall_re_pos fun z ↦ re_ne_zero_of_aeval_minpoly_eq_zero hA
  obtain ⟨u, v, huv⟩ : IsCoprime p q :=
    (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K := ℂ) (p := p) (q := q)).mpr fun z ↦ by
      by_contra! h
      exact lt_asymm (hp z h.1) (hq z h.2)
  have hA0 : aeval A (p * q) = 0 := by rw [← hpq, minpoly.aeval]
  have hP : IsIdempotentElem (aeval A (v * q)) := by
    rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub]
    exact aeval_eq_zero_of_dvd_aeval_eq_zero ⟨-(u * v), by linear_combination (v * q) * huv⟩ hA0
  have hAP : Commute A (aeval A (v * q)) := by
    simpa using (Commute.all (X : ℝ[X]) (v * q)).map (aeval A)
  obtain ⟨Ks, αs, hαs, hs⟩ := exists_norm_exp_smul_mul_aeval_le hA0 huv hp
  -- The backward estimate is the forward estimate for `-A`, with the roles of `p` and `q`
  -- exchanged by the substitution `X ↦ -X`.
  have hcomp (r : ℝ[X]) : aeval (-A) (r.comp (-X)) = aeval A r := by
    rw [aeval_comp, map_neg, aeval_X, neg_neg]
  have hA0' : aeval (-A) (q.comp (-X) * p.comp (-X)) = 0 := by
    rw [← Polynomial.mul_comp, hcomp, mul_comm, hA0]
  have huv' : v.comp (-X) * q.comp (-X) + u.comp (-X) * p.comp (-X) = 1 := by
    rw [← Polynomial.mul_comp, ← Polynomial.mul_comp, ← Polynomial.add_comp, add_comm, huv,
      Polynomial.one_comp]
  have hq' (z : ℂ) (hz : aeval z (q.comp (-X)) = 0) : z.re < 0 := by
    rw [aeval_comp, map_neg, aeval_X] at hz
    simpa using hq (-z) hz
  obtain ⟨Ku, αu, hαu, hu⟩ := exists_norm_exp_smul_mul_aeval_le hA0' huv' hq'
  have hQ : aeval (-A) (u.comp (-X) * p.comp (-X)) = 1 - aeval A (v * q) := by
    rw [← Polynomial.mul_comp, hcomp, eq_sub_iff_add_eq, ← map_add, huv, map_one]
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, (K : ℝ) = max (max Ks Ku) 1 := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ≥0, (α : ℝ) = min αs αu := ⟨⟨_, le_min hαs.le hαu.le⟩, rfl⟩
  refine ⟨aeval A (v * q), hP, hAP, K, α, ?_, ?_, fun t ht z ↦ ?_, fun t ht z ↦ ?_⟩
  · rw [← NNReal.coe_pos, hK]
    exact one_pos.trans_le (le_max_right _ _)
  · rw [← NNReal.coe_pos, hα]
    exact lt_min hαs hαu
  · refine ((exp (t • A) * aeval A (v * q)).le_opNorm z).trans ?_
    gcongr
    refine (hs t ht).trans (mul_le_mul ?_ ?_ (Real.exp_nonneg _) K.coe_nonneg)
    · exact hK ▸ (le_max_left _ _).trans (le_max_left _ _)
    · exact Real.exp_le_exp.mpr (by nlinarith [min_le_left αs αu])
  · have hz : exp (t • A) (z - aeval A (v * q) z) =
        (exp ((-t) • -A) * aeval (-A) (u.comp (-X) * p.comp (-X))) z := by
      rw [hQ, neg_smul_neg, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
    rw [hz]
    refine (ContinuousLinearMap.le_opNorm _ z).trans ?_
    gcongr
    refine (hu (-t) (neg_nonneg.mpr ht)).trans
      (mul_le_mul ?_ ?_ (Real.exp_nonneg _) K.coe_nonneg)
    · exact hK ▸ (le_max_right _ _).trans (le_max_left _ _)
    · exact Real.exp_le_exp.mpr (by nlinarith [min_le_right αs αu])

end ContinuousLinearMap

namespace ContinuousLinearMap.HasLyapunovForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →L[ℝ] E}

/-- **An operator with a Lyapunov form has an exponential dichotomy.** Such an operator has no
eigenvalue on the imaginary axis, so the hyperbolic dichotomy applies to it. -/
theorem exists_projection_exponential_bounds (h : A.HasLyapunovForm) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧
      ∃ (K α : ℝ≥0), 0 < K ∧ 0 < α ∧
        (∀ t : ℝ, 0 ≤ t → ∀ z : E, ‖exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ z : E,
          ‖exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖) :=
  A.exists_projection_exponential_bounds fun _ _ _ hv hw ↦
    h.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul hv hw

end ContinuousLinearMap.HasLyapunovForm
