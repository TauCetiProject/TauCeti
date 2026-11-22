/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Integrability and `L²` membership of polynomials against a finite-moment measure

This file proves that a polynomial over a normed ring, evaluated along a function `g`, is
integrable as soon as the powers of `g` occurring in it are, and that a real polynomial is
square-integrable against a measure on `ℝ` all of whose moments are finite:

* `integrable_eval_of_forall_mem_support` — `ω ↦ q(g ω)` is integrable, being a finite linear
  combination of powers of `g`, as soon as `gᵏ` is integrable for every `k` in the support of `q`,
  and `integral_eval_eq_sum_range` — under the same hypothesis, over a normed `ℝ`-algebra, its
  integral is the corresponding combination of the moments `∫ gᵏ dμ` (if the algebra is not
  complete, every Bochner integral is `0` by convention and both sides vanish);
* `integrable_eval_of_forall_integrable_pow` — the all-moments corollary: every polynomial is
  integrable along `g` when every power of `g` is;
* `memLp_two_eval_of_forall_integrable_pow` — a real polynomial is in `L²` against a measure on
  `ℝ` against which every monomial `x ↦ xᵏ` is integrable. Unlike the `L¹` results, this assumes
  all moments, not only those occurring in the polynomial: the square of a polynomial involves
  powers up to twice its degree, and `L²` membership is integrability of the square
  (`memLp_two_iff_integrable_sq`).

These results consume only the moment hypothesis, with no dependence on the particular measure,
so they apply verbatim to the Gaussian measure (all moments finite by Fernique) and to the
compactly supported Chebyshev measure alike. For a finite measure concentrated on a bounded set,
`integrable_pow_of_ae_norm_le` supplies the hypothesis.

Building on the `L²` membership, `polynomialEvalLp` sends a real polynomial to the `L²` class of
its evaluation, cast into any `[RCLike 𝕜]` scalar field, as an `ℝ`-linear map
`ℝ[X] →ₗ[ℝ] Lp 𝕜 2 μ`. Its range is the space of polynomial functions inside `L²(μ)`, in which
the orthogonality and the closed span of a family of real polynomials can be studied.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial

section NormedRing

variable {Ω A : Type*} [NormedRing A] [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → A}

/-- A polynomial over a normed ring, evaluated along `g`, is integrable as soon as `gᵏ` is
integrable for every `k` in its support, being a finite linear combination of these powers. -/
theorem integrable_eval_of_forall_mem_support {q : A[X]}
    (hmom : ∀ k ∈ q.support, Integrable (fun ω => g ω ^ k) μ) :
    Integrable (fun ω => q.eval (g ω)) μ := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact integrable_finsetSum _ fun k hk => (hmom k hk).const_mul _

/-- The integral of a polynomial over a normed `ℝ`-algebra, evaluated along `g`, is the
corresponding linear combination of the moments `∫ gᵏ dμ`, as soon as `gᵏ` is integrable for
every `k` in its support. If `A` is not complete, every Bochner integral into `A` is `0` by
convention, so both sides vanish and the identity carries no information; it is meaningful for
complete `A`, such as `ℝ` or `ℂ`. -/
theorem integral_eval_eq_sum_range [NormedAlgebra ℝ A] {q : A[X]}
    (hmom : ∀ k ∈ q.support, Integrable (fun ω => g ω ^ k) μ) :
    ∫ ω, q.eval (g ω) ∂μ = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * ∫ ω, g ω ^ k ∂μ := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [integral_finsetSum _ fun k hk => (hmom k hk).const_mul _,
    Finset.sum_congr rfl fun k hk => integral_const_mul_of_integrable (hmom k hk)]
  exact q.sum_over_range (f := fun k a => a * ∫ ω, g ω ^ k ∂μ) fun _ => zero_mul _

/-- A polynomial over a normed ring, evaluated along `g`, is integrable as soon as every power of
`g` is. -/
theorem integrable_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) μ) (q : A[X]) :
    Integrable (fun ω => q.eval (g ω)) μ :=
  integrable_eval_of_forall_mem_support fun k _ => hmom k

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

/-- `polynomialEvalLp` sends a polynomial to the `L²` class of its scalar-cast evaluation, given
by `MemLp.toLp`. -/
lemma polynomialEvalLp_apply (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    polynomialEvalLp 𝕜 hmom q =
      (memLp_two_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hmom q).toLp _ := by
  simp only [polynomialEvalLp, LinearMap.coe_mk, AddHom.coe_mk]

end TauCeti
