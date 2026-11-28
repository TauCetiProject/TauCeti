/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Probability.Moments.SubGaussian.IsotropicRows
public import TauCeti.Probability.Moments.SubGaussian.Vector

/-!
# Operator-norm concentration of sample second moments

For independent isotropic sub-Gaussian observations `x₁, …, xₙ` in `ℝ^p` with variance proxy
`c = K²`, the sample second moment `n⁻¹ ∑ xᵢ xᵢᵀ` is close to the identity in the Euclidean
operator norm: the error is of order `c (ε + ε²)` with `ε = (√p + t) / √n`, except on an event
of probability at most `2 exp (-t²)`. The observations need not have independent coordinates
or a common distribution.

## Main results

* `ProbabilityTheory.iIndepFun.measureReal_norm_sampleSecondMoment_sub_one_gt_le`: the tail
  bound `P(12288 c (ε + ε²) < ‖n⁻¹ ∑ xᵢ xᵢᵀ - 1‖) ≤ 2 exp (-t²)`, with explicit constants.
* `TauCeti.norm_sampleCovariance_sub_le`: the high-probability form
  `‖n⁻¹ ∑ wᵢ wᵢᵀ - 1‖ ≤ 3 max (CK²(√p + t)/√n, (CK²(√p + t)/√n)²)` for independent isotropic
  sub-Gaussian vectors `wᵢ` of `EuclideanSpace ℝ (Fin p)`.

Both are the normalized form of the Gram-matrix bound
`ProbabilityTheory.iIndepFun.measureReal_gram_sub_smul_one_gt_le`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), Theorem 4.6.1 and Exercise 4.7.3.
-/

public section

open MeasureTheory Real Matrix
open scoped NNReal Matrix.Norms.L2Operator RealInnerProductSpace

namespace ProbabilityTheory.iIndepFun

variable {Ω ι n : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [Fintype n]
  [DecidableEq n] {μ : Measure Ω} {x : ι → Ω → n → ℝ} {c : ℝ≥0}

/-- Operator-norm concentration of the sample second moment of independent isotropic
sub-Gaussian observations indexed by a nonempty `ι`, with coordinates indexed by `n`. The proxy
`c` bounds every unit linear form. For `t ≥ 0` and `ε = (√(card n) + t) / √(card ι)`, the
operator norm of `sampleSecondMoment x - 1` exceeds `12288 c (ε + ε²)` with probability at most
`2 exp (-t²)`. -/
theorem measureReal_norm_sampleSecondMoment_sub_one_gt_le (hindep : iIndepFun x μ)
    (hsub : ∀ i (u : EuclideanSpace ℝ n), ‖u‖ = 1 →
      HasSubgaussianMGF (fun ω ↦ x i ω ⬝ᵥ u) c μ)
    (hiso : ∀ i (u : EuclideanSpace ℝ n), ‖u‖ = 1 → ∫ ω, (x i ω ⬝ᵥ u) ^ 2 ∂μ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | 12288 * c * ((√(Fintype.card n) + t) / √(Fintype.card ι) +
        ((√(Fintype.card n) + t) / √(Fintype.card ι)) ^ 2) <
      ‖TauCeti.sampleSecondMoment (fun i ↦ x i ω) - 1‖} ≤ 2 * exp (-(t ^ 2)) := by
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  let A : Ω → Matrix ι n ℝ := fun ω ↦ Matrix.of fun i ↦ x i ω
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
    (measureReal_gram_sub_smul_one_gt_le (A := A) hindep hsub hiso ht)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  set N : ℝ := (Fintype.card ι : ℝ)
  set s : ℝ := √(Fintype.card n : ℝ) + t
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have hsqrt : √N ^ 2 = N := Real.sq_sqrt hN.le
  have hsqrt0 : 0 < √N := Real.sqrt_pos.mpr hN
  -- The sample second moment of the rows of `A` is the normalized Gram matrix of `A`.
  have hS : TauCeti.sampleSecondMoment (fun i ↦ x i ω) - 1 =
      N⁻¹ • ((A ω)ᵀ * A ω - N • 1) := by
    have hmap : (Matrix.of fun i ↦ x i ω).map star = Matrix.of fun i ↦ x i ω := by ext; simp
    rw [TauCeti.sampleSecondMoment_eq_inv_smul_transpose_mul, hmap, smul_sub, smul_smul,
      inv_mul_cancel₀ hN.ne', one_smul]
  rw [hS, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hN.le), lt_inv_mul_iff₀ hN] at hω
  have hthr : N * (12288 * c * (s / √N + (s / √N) ^ 2)) = 12288 * c * (√N * s + s ^ 2) := by
    field_simp
    rw [hsqrt]
    ring
  linarith

end ProbabilityTheory.iIndepFun

namespace TauCeti

open ProbabilityTheory

/-- Operator-norm concentration of the sample second moment of independent isotropic
sub-Gaussian vectors with proxy `K²`: with probability at least `1 - 2 exp (-c t²)`,
`‖n⁻¹ ∑ wᵢ wᵢᵀ - 1‖ ≤ 3 max (ε, ε²)` with `ε = C K² (√p + t) / √n`, for universal constants
`C, c > 0` and all `n ≥ 1`, `t ≥ 0`. -/
theorem norm_sampleCovariance_sub_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n p : ℕ)
        (w : Fin n → Ω → EuclideanSpace ℝ (Fin p)) (K : ℝ≥0) (t : ℝ), 0 < n → 0 ≤ t →
        iIndepFun w μ → (∀ i, IsSubgaussianVector (w i) (K ^ 2) μ) →
        (∀ i u v, ∫ ω, ⟪u, w i ω⟫ * ⟪v, w i ω⟫ ∂μ = ⟪u, v⟫) →
        1 - 2 * exp (-c * t ^ 2) ≤ μ.real {ω |
          ‖sampleSecondMoment (fun i ↦ WithLp.ofLp (w i ω)) - 1‖ ≤
            3 * max (C * K ^ 2 * (√(p : ℝ) + t) / √(n : ℝ))
              ((C * K ^ 2 * (√(p : ℝ) + t) / √(n : ℝ)) ^ 2)} := by
  -- The constants are those of `measureReal_norm_sampleSecondMoment_sub_one_gt_le`.
  refine ⟨12288, 1, by norm_num, one_pos, fun {Ω} _ μ n p w K t hn ht hindep hsub hiso ↦ ?_⟩
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdot (i : Fin n) (u : EuclideanSpace ℝ (Fin p)) (ω : Ω) :
      WithLp.ofLp (w i ω) ⬝ᵥ u = ⟪u, w i ω⟫ := by
    simp [dotProduct, PiLp.inner_apply, mul_comm]
  have hsub' (i : Fin n) (u : EuclideanSpace ℝ (Fin p)) (hu : ‖u‖ = 1) :
      HasSubgaussianMGF (fun ω ↦ WithLp.ofLp (w i ω) ⬝ᵥ u) (K ^ 2) μ := by
    have hu' : ‖u‖₊ = 1 := by ext; simpa using hu
    simpa [hdot, hu'] using (hsub i).hasSubgaussianMGF_inner u
  have hiso' (i : Fin n) (u : EuclideanSpace ℝ (Fin p)) (hu : ‖u‖ = 1) :
      ∫ ω, (WithLp.ofLp (w i ω) ⬝ᵥ u) ^ 2 ∂μ = 1 := by
    simpa [hdot, sq, real_inner_self_eq_norm_sq, hu] using hiso i u u
  have hbad := (hindep.comp (fun _ ↦ WithLp.ofLp) (fun _ ↦ by fun_prop)
    ).measureReal_norm_sampleSecondMoment_sub_one_gt_le hsub' hiso' ht
  simp only [Function.comp_def, Fintype.card_fin, NNReal.coe_pow] at hbad
  set ε : ℝ := (√(p : ℝ) + t) / √(n : ℝ)
  set bad := {ω | 12288 * (K : ℝ) ^ 2 * (ε + ε ^ 2) <
    ‖sampleSecondMoment (fun i ↦ WithLp.ofLp (w i ω)) - 1‖}
  set good := {ω | ‖sampleSecondMoment (fun i ↦ WithLp.ofLp (w i ω)) - 1‖ ≤
    3 * max (12288 * K ^ 2 * (√(p : ℝ) + t) / √(n : ℝ))
      ((12288 * K ^ 2 * (√(p : ℝ) + t) / √(n : ℝ)) ^ 2)}
  have hε : 0 ≤ ε := by positivity
  have hcover : Set.univ ⊆ good ∪ bad := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · intro ω _
      left
      simp only [good, Set.mem_ofPred_eq]
      rw [Subsingleton.elim (_ - 1) 0, norm_zero]
      positivity
    -- Isotropy forces the proxy to be at least one.
    have hK : 1 ≤ (K : ℝ) ^ 2 := by
      have hu : ‖EuclideanSpace.single (⟨0, hp⟩ : Fin p) (1 : ℝ)‖ = 1 := by simp
      have := (hsub' ⟨0, hn⟩ _ hu).integral_sq_le
      rw [hiso' _ _ hu] at this
      exact_mod_cast this
    intro ω _
    by_contra h
    simp only [Set.mem_union, not_or, good, bad, Set.mem_ofPred_eq, not_le, not_lt] at h
    have hscale : 12288 * (K : ℝ) ^ 2 * (√(p : ℝ) + t) / √(n : ℝ) = 12288 * (K : ℝ) ^ 2 * ε := by
      simp [ε, mul_div_assoc]
    rw [hscale] at h
    have h1 := le_max_left (12288 * (K : ℝ) ^ 2 * ε) ((12288 * (K : ℝ) ^ 2 * ε) ^ 2)
    have h2 := le_max_right (12288 * (K : ℝ) ^ 2 * ε) ((12288 * (K : ℝ) ^ 2 * ε) ^ 2)
    nlinarith [mul_nonneg (mul_nonneg hε hε) (sub_nonneg.mpr hK)]
  have hunion := (measureReal_mono (μ := μ) hcover (measure_ne_top _ _)).trans
    (measureReal_union_le good bad)
  rw [probReal_univ] at hunion
  simp only [neg_mul, one_mul]
  linarith

end TauCeti
