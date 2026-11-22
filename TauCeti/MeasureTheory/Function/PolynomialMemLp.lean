/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Integrability and `Lᵖ` membership of polynomials against a finite-moment measure

This file proves that a polynomial over a normed ring, evaluated along a function `g`, is
integrable as soon as the powers of `g` occurring in it are, and that it lies in every `Lᵖ` with
`p ≠ ∞` as soon as every power of `g` is integrable:

* `integrable_eval_of_forall_mem_support` — `ω ↦ q(g ω)` is integrable, being a finite linear
  combination of powers of `g`, as soon as `gᵏ` is integrable for every `k` in the support of `q`,
  and `integral_eval_eq_sum_range` — under the same hypothesis, over a normed `ℝ`-algebra, its
  integral is the corresponding combination of the moments `∫ gᵏ dμ` (if the algebra is not
  complete, every Bochner integral is `0` by convention and both sides vanish);
* `integrable_eval_of_forall_integrable_pow` — the all-moments corollary: every polynomial is
  integrable along `g` when every power of `g` is;
* `memLp_eval_of_forall_mem_support` — likewise, `ω ↦ q(g ω)` lies in `Lᵖ` as soon as `gᵏ` does
  for every `k` in the support of `q`;
* `memLp_eval_of_forall_integrable_pow` — over a normed ring with power-multiplicative norm,
  `ω ↦ q(g ω)` lies in `Lᵖ` for every `p ≠ ∞` when every power of `g` is integrable. Unlike the
  support-indexed results, this assumes all moments, not only those occurring in `q`: they make the
  measure finite (`g⁰ = 1` is integrable), and `‖gᵏ‖ⁿ = ‖gᵏⁿ‖` puts every power of `g` in every
  `Lⁿ`.

These results consume only the moment hypothesis, with no dependence on the particular measure,
so they apply verbatim to the Gaussian measure (all moments finite by Fernique) and to the
compactly supported Chebyshev measure alike. For a finite measure concentrated on a bounded set,
`integrable_pow_of_ae_norm_le` supplies the hypothesis.

Building on the `Lᵖ` membership, `polynomialEvalLp` sends a real polynomial to the `Lᵖ` class,
for any `p ≠ ∞`, of its evaluation on `ℝ`, cast into any `[RCLike 𝕜]` scalar field, as an
`ℝ`-linear map `ℝ[X] →ₗ[ℝ] Lp 𝕜 p μ`. Its range consists of the `Lᵖ` classes of the scalar-cast
evaluations of real polynomials; for `p = 2` this is where the orthogonality and the closed span
of a family of real polynomials can be studied.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial
open scoped ENNReal

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

/-- A polynomial over a normed ring, evaluated along `g`, lies in `Lᵖ` as soon as `gᵏ` does for
every `k` in its support, being a finite linear combination of these powers. -/
theorem memLp_eval_of_forall_mem_support {p : ℝ≥0∞} {q : A[X]}
    (hmom : ∀ k ∈ q.support, MemLp (fun ω => g ω ^ k) p μ) :
    MemLp (fun ω => q.eval (g ω)) p μ := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact memLp_finsetSum _ fun k hk => (hmom k hk).const_mul _

/-- A polynomial over a normed ring with power-multiplicative norm (`‖aⁿ‖ = ‖a‖ⁿ` for `n ≥ 1`, as
for `ℝ`, `ℂ`, or a sup-normed product or function algebra), evaluated along `g`, lies in every `Lᵖ`
with `p ≠ ∞` as soon as every power of `g` is integrable. The measure is then finite, since
`g⁰ = 1` is integrable, and `‖gᵏ‖ⁿ = ‖gᵏⁿ‖` puts every `gᵏ` in `Lⁿ` for a natural number `n > p`,
hence in `Lᵖ`; `memLp_eval_of_forall_mem_support` concludes. Some condition on the norm is
needed: for a square-zero real `2 × 2` matrix `e` and a real function `h`, every power of
`g = h • e` is integrable against a finite measure as soon as `h` is, since `gᵏ = 0` for `k ≥ 2`,
even if `h`, hence `g`, is not in `L²`. -/
theorem memLp_eval_of_forall_integrable_pow (hA : IsPowMul (‖·‖ : A → ℝ)) {p : ℝ≥0∞}
    (hp : p ≠ ∞) (hmom : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) μ) (q : A[X]) :
    MemLp (fun ω => q.eval (g ω)) p μ := by
  rcases subsingleton_or_nontrivial A with _ | _
  · convert MemLp.zero' (p := p) (μ := μ)
  have : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure one_ne_zero).1 (by simpa using hmom 0)
  obtain ⟨n, hpn⟩ := ENNReal.exists_nat_gt hp
  have hn : 0 < n := by exact_mod_cast pos_of_gt hpn
  refine memLp_eval_of_forall_mem_support fun k _ => MemLp.mono_exponent ?_ hpn.le
  rw [← integrable_norm_rpow_iff (hmom k).aestronglyMeasurable (pos_of_gt hpn).ne'
    (ENNReal.natCast_ne_top n)]
  refine (hmom (k * n)).norm.congr (.of_forall fun ω => ?_)
  simp only [pow_mul, hA _ hn, ENNReal.toReal_natCast, Real.rpow_natCast]

end NormedRing

/-- A real polynomial evaluated along `g`, cast into any `RCLike` scalar field, lies in every `Lᵖ`
with `p ≠ ∞` as soon as every power of `g` is integrable. -/
theorem memLp_algebraMap_eval_of_forall_integrable_pow {Ω 𝕜 : Type*} [RCLike 𝕜]
    [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ} {p : ℝ≥0∞} (hp : p ≠ ∞)
    (hmom : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) μ) (q : ℝ[X]) :
    MemLp (fun ω => (algebraMap ℝ 𝕜) (q.eval (g ω))) p μ := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_eval_of_forall_integrable_pow (fun x _ _ => norm_pow x _) hp hmom q).ofReal (K := 𝕜)

variable {μ : Measure ℝ} {p : ℝ≥0∞}

/-- Polynomial evaluation on `ℝ`, cast into any `RCLike` scalar field, bundled as an `ℝ`-linear
map into `Lᵖ`, for `p ≠ ∞`, against any measure all of whose polynomial moments are finite. -/
noncomputable def polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜] (hp : p ≠ ∞)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) :
    ℝ[X] →ₗ[ℝ] Lp 𝕜 p μ where
  toFun q := (memLp_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hp hmom q).toLp _
  map_add' q r := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_forall fun x => by simp)
  map_smul' a q := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x => by simp [Algebra.smul_def])

/-- The `Lᵖ` representative of `polynomialEvalLp` is the expected scalar-cast pointwise
evaluation. -/
lemma coeFn_polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜] (hp : p ≠ ∞)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    ⇑(polynomialEvalLp 𝕜 hp hmom q) =ᵐ[μ] fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x) :=
  MemLp.coeFn_toLp (memLp_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hp hmom q)

/-- `polynomialEvalLp` sends a polynomial to the `Lᵖ` class of its scalar-cast evaluation, given
by `MemLp.toLp`. -/
lemma polynomialEvalLp_apply (𝕜 : Type*) [RCLike 𝕜] (hp : p ≠ ∞)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    polynomialEvalLp 𝕜 hp hmom q =
      (memLp_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hp hmom q).toLp _ := by
  simp only [polynomialEvalLp, LinearMap.coe_mk, AddHom.coe_mk]

end TauCeti
