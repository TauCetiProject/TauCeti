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
public import TauCeti.LinearAlgebra.Eigenspace.Minpoly

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
imaginary axis (`Module.End.re_ne_zero_of_aeval_minpoly_eq_zero`). Then `μ = p * q` with
the complex roots of `p` in the left half-plane and those of `q` in the right half-plane
(`Polynomial.exists_eq_mul_forall_re_neg_forall_re_pos`). These factors are coprime, say
`u * p + v * q = 1`, and `P = (v * q)(A)` is the projection onto `ker p(A)` along `ker q(A)`.
The operator `B = A P - (1 - P)`, again a polynomial in `A`, is annihilated by `p * (X + 1)`, whose
roots all have negative real part, so its flow decays exponentially
(`ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`); and `exp (t • B)` agrees with
`exp (t • A)` on the range of `P` (`ContinuousLinearMap.exists_norm_exp_smul_mul_aeval_le`). The
backward estimate is the forward one for `-A`.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, third edition, Academic Press, 2013, Chapter 7.
* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer, 1978.
-/

public section

open NormedSpace Polynomial
open scoped NNReal

namespace Module.End

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- **No root of the minimal polynomial of a hyperbolic operator is purely imaginary.** If there
are no `ω` and `v, w`, not both zero, with `f v = -ω • w` and `f w = ω • v`, then every complex
root of the minimal polynomial of `f` has nonzero real part. -/
theorem re_ne_zero_of_aeval_minpoly_eq_zero {f : End ℝ E}
    (hf : ∀ (ω : ℝ) (v w : E), f v = -ω • w → f w = ω • v → v = 0 ∧ w = 0) {z : ℂ}
    (hz : aeval z (minpoly ℝ f) = 0) : z.re ≠ 0 := by
  intro hre
  by_cases him : z.im = 0
  · -- `z = 0` is a root, so `f` has a nonzero kernel vector.
    have hz0 : z = algebraMap ℝ ℂ 0 := Complex.ext (by simpa using hre) (by simpa using him)
    rw [hz0, aeval_algebraMap_apply_eq_algebraMap_eval, map_eq_zero, ← IsRoot,
      ← dvd_iff_isRoot] at hz
    obtain ⟨v, hv, hfv⟩ := exists_ne_zero_aeval_apply_eq_zero_of_dvd_minpoly hz (by simp)
    simp only [aeval_X, map_zero, sub_zero] at hfv
    exact hv (hf 0 v 0 (by simp [hfv]) (by simp)).1
  · -- `z = ± i ‖z‖`, so `f ^ 2 + ‖z‖ ^ 2` has a nonzero kernel vector `v`, and
    -- `(v, -‖z‖⁻¹ • f v)` rotates under `f` with angular speed `‖z‖`.
    have hdvd := quadratic_dvd_of_aeval_eq_zero_im_ne_zero _ hz him
    have hdeg : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)).natDegree = 2 := by compute_degree!
    obtain ⟨v, hv, hfv⟩ := exists_ne_zero_aeval_apply_eq_zero_of_dvd_minpoly hdvd (by lia)
    have hc : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr fun h ↦ him (by simp [h])
    simp only [hre, mul_zero, map_zero, zero_mul, sub_zero, map_add, aeval_X_pow, aeval_C,
      LinearMap.add_apply, algebraMap_end_apply] at hfv
    have hffv : f (f v) = -(‖z‖ ^ 2) • v := by
      rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, ← hfv, pow_two f, _root_.mul_apply_eq_comp]
    refine hv (hf ‖z‖ v (-‖z‖⁻¹ • f v) ?_ ?_).1
    · rw [smul_smul, neg_mul_neg, mul_inv_cancel₀ hc, one_smul]
    · rw [map_smul, hffv, smul_smul, neg_mul_neg, pow_two, ← mul_assoc, inv_mul_cancel₀ hc,
        one_mul]

end Module.End

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

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
  have hmin : minpoly ℝ (A : E →ₗ[ℝ] E) = minpoly ℝ A := by
    have h : Module.End.toContinuousLinearMap E (A : E →ₗ[ℝ] E) = A := by ext; rfl
    rw [← minpoly.algEquiv_eq (Module.End.toContinuousLinearMap E), h]
  obtain ⟨p, q, hpq, hp, hq⟩ := exists_eq_mul_forall_re_neg_forall_re_pos fun z ↦
    hmin ▸ Module.End.re_ne_zero_of_aeval_minpoly_eq_zero (f := (A : E →ₗ[ℝ] E)) hA
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

/-- **An operator with a Lyapunov form has an exponential dichotomy.** If `A` has a Lyapunov
form, then there are an idempotent `P` commuting with `A` and constants `K, α > 0` such that
`exp (t • A)` contracts the range of `P` at rate `α` for `t ≥ 0` and the kernel of `P` at rate `α`
for `t ≤ 0`. -/
theorem exists_projection_exponential_bounds (h : A.HasLyapunovForm) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧
      ∃ (K α : ℝ≥0), 0 < K ∧ 0 < α ∧
        (∀ t : ℝ, 0 ≤ t → ∀ z : E, ‖exp (t • A) (P z)‖ ≤ K * Real.exp (-α * t) * ‖z‖) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ z : E,
          ‖exp (t • A) (z - P z)‖ ≤ K * Real.exp (α * t) * ‖z‖) :=
  A.exists_projection_exponential_bounds fun _ _ _ hv hw ↦
    h.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul hv hw

end ContinuousLinearMap.HasLyapunovForm
