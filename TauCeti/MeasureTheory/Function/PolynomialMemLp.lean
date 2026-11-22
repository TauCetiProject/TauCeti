/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Integrability and `L²` membership of polynomials against a finite-moment measure

This file proves that a polynomial, evaluated pointwise, is integrable against any measure on a
normed ring whose polynomial moments are finite (up to the relevant degree), and that a real
polynomial is moreover square-integrable:

* `integrable_eval_of_forall_le_natDegree` — a polynomial is integrable, being a finite linear
  combination of monomials, as soon as its monomials up to its degree are integrable, and
  `integral_eval_eq_sum_range` — under the same hypothesis, its integral is the corresponding
  combination of moments;
* `integrable_eval_of_forall_integrable_pow` — the all-moments corollary: every polynomial is
  integrable when every monomial is;
* `integrable_pow_of_ae_norm_le` — every monomial is integrable against a finite measure
  concentrated on a bounded set, so such measures satisfy the moment hypothesis;
* `abs_integral_eval_sub_le` — a real polynomial that approximates a bounded continuous function
  within `δ` on `[-M, M]` has integral within `δ` of that of the function, against a probability
  measure concentrated on `[-R, R]` with `R ≤ M`;
* `memLp_two_eval_of_forall_integrable_pow` — a real polynomial is in `L²`, since the square of a
  polynomial is again a polynomial (hence integrable), and `memLp_two_iff_integrable_sq`.

The all-moments results consume only the moment hypothesis `∀ k, Integrable (x ↦ xᵏ) μ`, and the
degree-bounded ones only its restriction to `k ≤ q.natDegree`, with no dependence on the
particular measure, so they apply verbatim to the Gaussian measure (all moments finite by Fernique)
and to the compactly supported Chebyshev measure alike.

Building on the `L²` membership, `polynomialEvalLp` bundles real polynomial evaluation, cast into
any `[RCLike 𝕜]` scalar field, as an `ℝ`-linear map `ℝ[X] →ₗ[ℝ] Lp 𝕜 2 μ`.  Being measure- and
scalar-generic, it is the shared construction underlying the Gaussian and Chebyshev orthogonal-basis
targets.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial

section NormedRing

variable {A : Type*} [NormedRing A] [MeasurableSpace A] {μ : Measure A}

/-- A polynomial over a normed ring is integrable against any measure against which its monomials
up to its degree are integrable, being a finite linear combination of them. -/
theorem integrable_eval_of_forall_le_natDegree {q : A[X]}
    (hmom : ∀ k ≤ q.natDegree, Integrable (fun x : A => x ^ k) μ) :
    Integrable (fun x : A => q.eval x) μ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ fun k hk => (hmom k (Finset.mem_range_succ_iff.1 hk)).const_mul _

/-- The integral of a polynomial over a normed `ℝ`-algebra, against a measure against which its
monomials up to its degree are integrable, is the corresponding linear combination of the moments
`∫ xᵏ dμ`. -/
theorem integral_eval_eq_sum_range [NormedAlgebra ℝ A] {q : A[X]}
    (hmom : ∀ k ≤ q.natDegree, Integrable (fun x : A => x ^ k) μ) :
    ∫ x, q.eval x ∂μ = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * ∫ x, x ^ k ∂μ := by
  -- The moment hypothesis, indexed by the summation range of `eval_eq_sum_range`.
  have hmom' (k) (hk : k ∈ Finset.range (q.natDegree + 1)) :=
    hmom k (Finset.mem_range_succ_iff.1 hk)
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ fun k hk => (hmom' k hk).const_mul _]
  exact Finset.sum_congr rfl fun k hk => integral_const_mul_of_integrable (hmom' k hk)

/-- A polynomial over a normed ring is integrable against any measure all of whose polynomial
moments are finite. -/
theorem integrable_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun x : A => x ^ k) μ) (q : A[X]) :
    Integrable (fun x : A => q.eval x) μ :=
  integrable_eval_of_forall_le_natDegree fun k _ => hmom k

/-- Every monomial is integrable against a finite measure on a separable normed ring that is almost
everywhere concentrated on the closed ball of radius `R`, so such a measure satisfies the moment
hypothesis of the results above. -/
theorem integrable_pow_of_ae_norm_le [OpensMeasurableSpace A] [SecondCountableTopology A]
    [IsFiniteMeasure μ] {R : ℝ} (h : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (n : ℕ) :
    Integrable (fun x : A => x ^ n) μ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [pow_zero] using integrable_const (1 : A)
  refine .of_bound (continuous_pow n).aestronglyMeasurable (R ^ n) ?_
  filter_upwards [h] with x hx
  exact (norm_pow_le' x hn).trans (pow_le_pow_left₀ (norm_nonneg x) hx n)

end NormedRing

variable {μ : Measure ℝ}

/-- A real polynomial is in `L²` against any measure all of whose polynomial moments are finite.
The square of a polynomial is again a polynomial, hence integrable by
`integrable_eval_of_forall_integrable_pow`, and `L²` membership is integrability of the square. -/
theorem memLp_two_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    MemLp (fun x : ℝ => q.eval x) 2 μ := by
  rw [memLp_two_iff_integrable_sq (Polynomial.continuous q).aestronglyMeasurable]
  exact (integrable_eval_of_forall_integrable_pow hmom (q ^ 2)).congr
    (.of_forall fun x => Polynomial.eval_pow 2)

/-- A real polynomial evaluation, cast into any `RCLike` scalar field, lies in `L²` against any
measure all of whose polynomial moments are finite. -/
theorem memLp_two_algebraMap_eval_of_forall_integrable_pow {𝕜 : Type*} [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x)) 2 μ := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_two_eval_of_forall_integrable_pow hmom q).ofReal (K := 𝕜)

/-- Polynomial evaluation, cast into any `RCLike` scalar field, bundled as an `ℝ`-linear map into
`L²` against any measure all of whose polynomial moments are finite. -/
noncomputable def polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) :
    ℝ[X] →ₗ[ℝ] Lp 𝕜 2 μ where
  toFun q := (memLp_two_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hmom q).toLp _
  map_add' q r := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_forall fun x => by simp)
  map_smul' a q := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x => by simp [Algebra.smul_def])

/-- The `L²` representative of `polynomialEvalLp` is the expected scalar-cast pointwise
evaluation. -/
lemma coeFn_polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    ⇑(polynomialEvalLp 𝕜 hmom q) =ᵐ[μ] fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x) :=
  MemLp.coeFn_toLp (memLp_two_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hmom q)

open scoped BoundedContinuousFunction in
/-- If `|f - p| ≤ δ` on `[-M, M]` and `μ` is a probability measure concentrated on `[-R, R]` with
`R ≤ M`, then `|∫ p dμ - ∫ f dμ| ≤ δ`. -/
theorem abs_integral_eval_sub_le [IsProbabilityMeasure μ]
    {f : ℝ →ᵇ ℝ} {p : ℝ[X]} {R M δ : ℝ} (hRM : R ≤ M) (hae : ∀ᵐ x ∂μ, |x| ≤ R)
    (hp : ∀ x ∈ Set.Icc (-M) M, |p.eval x - f x| ≤ δ) :
    |∫ x, p.eval x ∂μ - ∫ x, f x ∂μ| ≤ δ := by
  have hμ := integrable_pow_of_ae_norm_le (hae.mono fun x hx => (Real.norm_eq_abs x).trans_le hx)
  rw [← integral_sub (integrable_eval_of_forall_integrable_pow hμ p) (f.integrable _)]
  have hb : ∀ᵐ x ∂μ, ‖p.eval x - f x‖ ≤ δ := by
    filter_upwards [hae] with x hx
    exact (Real.norm_eq_abs _).trans_le (hp x (abs_le.1 (hx.trans hRM)))
  have := norm_integral_le_of_norm_le_const hb
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

end TauCeti
