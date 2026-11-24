/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability and `Lᵖ` membership of polynomials against a finite-moment measure

This file proves that a polynomial over a normed ring, evaluated along a function `g`, is
integrable as soon as the powers of `g` occurring in it are, and that, when the norm is
power-multiplicative, it lies in every `Lᵖ` with `p ≠ ∞` as soon as every power of `g` is
integrable:

* `integrable_eval_of_forall_mem_support` — `ω ↦ q(g ω)` is integrable, being a finite linear
  combination of powers of `g`, as soon as `gᵏ` is integrable for every `k` in the support of `q`;
* `integral_eval_eq_sum_support` — under the same hypothesis, over a normed `ℝ`-algebra, the
  integral of `ω ↦ q(g ω)` is the sum over the support of `q` of the coefficients times the
  moments `∫ gᵏ dμ`, and `integral_eval_eq_sum_range` is the same sum over all `k ≤ natDegree q`
  (if the algebra is not complete, every Bochner integral is `0` by convention and both sides
  vanish);
* `tendsto_integral_eval_of_tendsto_integral_pow` — if the moments `∫ gᵏ dμᵢ` converge to
  `∫ gᵏ dμ` for every `k` in the support of `q`, and each such `gᵏ` is integrable against `μ`
  and, eventually, against `μᵢ`, then `∫ q(g) dμᵢ` converges to `∫ q(g) dμ`;
* `integrable_eval_of_forall_integrable_pow` — the all-moments corollary: every polynomial is
  integrable along `g` when every power of `g` is;
* `memLp_eval_of_forall_mem_support` — likewise, `ω ↦ q(g ω)` lies in `Lᵖ` as soon as `gᵏ` does
  for every `k` in the support of `q`;
* `memLp_pow_of_forall_integrable_pow` and `memLp_eval_of_forall_integrable_pow` — over a normed
  ring with power-multiplicative norm, every power of `g`, and hence `ω ↦ q(g ω)`, lies in `Lᵖ`
  for every `p ≠ ∞` when every power of `g` is integrable. Unlike the support-indexed results,
  this assumes every moment, not only those occurring in `q`: for `p > 1` and `k ≥ 1`, the `Lᵖ`
  membership of `gᵏ` concerns the moment of `‖g‖` of order `kp > k`.
* `integrable_pow_of_integrable_pow_two_mul` — on `ℝ`, against a finite measure, a finite moment
  of order `2k` makes every moment of order at most `2k` finite, so finiteness of the even moments
  gives the all-moments hypothesis.

These results assume nothing about the measure beyond the moment hypotheses, so they apply
verbatim to the Gaussian measure (all moments finite by Fernique) and to the compactly supported
Chebyshev measure alike. For an almost everywhere strongly measurable `g` that is almost
everywhere bounded against a finite measure, `integrable_pow_of_ae_norm_le` supplies the
integrability hypotheses.

Building on the `Lᵖ` membership, `polynomialEvalLp` sends a real polynomial to the `Lᵖ` class of
its evaluation on `ℝ`, cast into any `[RCLike 𝕜]` scalar field, as an `ℝ`-linear map
`ℝ[X] →ₗ[ℝ] Lp 𝕜 p μ`, for any `p` and any measure `μ` against which every monomial lies in `Lᵖ`.
Its range consists of the `Lᵖ` classes of the scalar-cast evaluations of real polynomials; for
`p = 2` this is where the orthogonality and the closed span of a family of real polynomials can be
studied.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Filter
open scoped ENNReal Topology

section NormedRing

variable {Ω A : Type*} [NormedRing A] [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → A}

/-- A polynomial over a normed ring, evaluated along `g`, is integrable as soon as `gᵏ` is
integrable for every `k` in its support, being a finite linear combination of these powers. -/
theorem integrable_eval_of_forall_mem_support {q : A[X]}
    (hmom : ∀ k ∈ q.support, Integrable (fun ω => g ω ^ k) μ) :
    Integrable (fun ω => q.eval (g ω)) μ := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact integrable_finsetSum _ fun k hk => (hmom k hk).const_mul _

/-- The integral of a polynomial over a normed `ℝ`-algebra, evaluated along `g`, is the sum over
its support of the coefficients times the moments `∫ gᵏ dμ`, as soon as `gᵏ` is integrable for
every `k` in its support. If `A` is not complete, every Bochner integral into `A` is `0` by
convention, so both sides vanish and the identity carries no information; it is meaningful for
complete `A`, such as `ℝ` or `ℂ`. -/
theorem integral_eval_eq_sum_support [NormedAlgebra ℝ A] {q : A[X]}
    (hmom : ∀ k ∈ q.support, Integrable (fun ω => g ω ^ k) μ) :
    ∫ ω, q.eval (g ω) ∂μ = ∑ k ∈ q.support, q.coeff k * ∫ ω, g ω ^ k ∂μ := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [integral_finsetSum _ fun k hk => (hmom k hk).const_mul _]
  exact Finset.sum_congr rfl fun k hk => integral_const_mul_of_integrable (hmom k hk)

/-- The integral of a polynomial over a normed `ℝ`-algebra, evaluated along `g`, is the
corresponding linear combination of the moments `∫ gᵏ dμ` for `k ≤ natDegree q`, as soon as `gᵏ`
is integrable for every `k` in its support. As for `integral_eval_eq_sum_support`, the identity is
meaningful for complete `A`, such as `ℝ` or `ℂ`. -/
theorem integral_eval_eq_sum_range [NormedAlgebra ℝ A] {q : A[X]}
    (hmom : ∀ k ∈ q.support, Integrable (fun ω => g ω ^ k) μ) :
    ∫ ω, q.eval (g ω) ∂μ = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * ∫ ω, g ω ^ k ∂μ :=
  (integral_eval_eq_sum_support hmom).trans
    (q.sum_over_range (f := fun k a => a * ∫ ω, g ω ^ k ∂μ) fun _ => zero_mul _)

/-- If the moment `∫ gᵏ dμᵢ` converges to `∫ gᵏ dμ` for every `k` in the support of a polynomial
over a normed `ℝ`-algebra, then so does the integral of the polynomial evaluated along `g`. The
moments must be genuine: each such `gᵏ` is assumed integrable against `μ` and, eventually, against
`μᵢ`. -/
theorem tendsto_integral_eval_of_tendsto_integral_pow [NormedAlgebra ℝ A] {ι : Type*}
    {l : Filter ι} {μs : ι → Measure Ω} (q : A[X])
    (hμs : ∀ k ∈ q.support, ∀ᶠ i in l, Integrable (fun ω => g ω ^ k) (μs i))
    (hμ : ∀ k ∈ q.support, Integrable (fun ω => g ω ^ k) μ)
    (h : ∀ k ∈ q.support, Tendsto (fun i => ∫ ω, g ω ^ k ∂μs i) l (𝓝 (∫ ω, g ω ^ k ∂μ))) :
    Tendsto (fun i => ∫ ω, q.eval (g ω) ∂μs i) l (𝓝 (∫ ω, q.eval (g ω) ∂μ)) := by
  rw [integral_eval_eq_sum_support hμ]
  refine (tendsto_finsetSum _ fun k hk => (h k hk).const_mul (q.coeff k)).congr' ?_
  filter_upwards [(eventually_all_finset q.support).2 hμs] with i hi
  exact (integral_eval_eq_sum_support hi).symm

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

/-- Over a normed ring with power-multiplicative norm (`‖aⁿ‖ = ‖a‖ⁿ` for `n ≥ 1`, as for `ℝ`, `ℂ`,
or finite products and bounded function algebras of real or complex scalars with the sup norm),
every power of `g` lies in every `Lᵖ` with `p ≠ ∞` as soon as every power of `g` is integrable.
Some condition on the norm is needed: for a square-zero real `2 × 2` matrix `e` and a real function
`h`, every power of `g = h • e` is integrable against a finite measure as soon as `h` is, since
`gᵏ = 0` for `k ≥ 2`, even if `h`, hence `g`, is not in `L²`. -/
theorem memLp_pow_of_forall_integrable_pow (hA : IsPowMul (‖·‖ : A → ℝ)) {p : ℝ≥0∞}
    (hp : p ≠ ∞) (hmom : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) μ) (k : ℕ) :
    MemLp (fun ω => g ω ^ k) p μ := by
  rcases subsingleton_or_nontrivial A with _ | _
  · convert MemLp.zero' (p := p) (μ := μ)
  have : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure one_ne_zero).1 (by simpa using hmom 0)
  obtain ⟨n, hpn⟩ := ENNReal.exists_nat_gt hp
  have hn : 0 < n := by exact_mod_cast pos_of_gt hpn
  refine MemLp.mono_exponent ?_ hpn.le
  rw [← integrable_norm_rpow_iff (hmom k).aestronglyMeasurable (pos_of_gt hpn).ne'
    (ENNReal.natCast_ne_top n)]
  refine (hmom (k * n)).norm.congr (.of_forall fun ω => ?_)
  simp only [pow_mul, hA _ hn, ENNReal.toReal_natCast, Real.rpow_natCast]

/-- A polynomial over a normed ring with power-multiplicative norm, evaluated along `g`, lies in
every `Lᵖ` with `p ≠ ∞` as soon as every power of `g` is integrable. See
`memLp_pow_of_forall_integrable_pow` for why a condition on the norm is needed. -/
theorem memLp_eval_of_forall_integrable_pow (hA : IsPowMul (‖·‖ : A → ℝ)) {p : ℝ≥0∞}
    (hp : p ≠ ∞) (hmom : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) μ) (q : A[X]) :
    MemLp (fun ω => q.eval (g ω)) p μ :=
  memLp_eval_of_forall_mem_support fun k _ => memLp_pow_of_forall_integrable_pow hA hp hmom k

end NormedRing

/-- On a finite measure, a finite moment of order `2k` makes every moment of order `n ≤ 2k`
finite: the real-monomial case of Mathlib's `integrable_norm_pow_of_le`. Finiteness of the even
moments alone therefore gives the all-moments hypothesis of the results above. -/
theorem integrable_pow_of_integrable_pow_two_mul {μ : Measure ℝ} [IsFiniteMeasure μ] {k n : ℕ}
    (hn : n ≤ 2 * k) (h : Integrable (fun x : ℝ ↦ x ^ (2 * k)) μ) :
    Integrable (fun x : ℝ ↦ x ^ n) μ :=
  (integrable_norm_iff (by fun_prop)).1 <| by
    simpa only [norm_pow, id] using integrable_norm_pow_of_le (f := id) aestronglyMeasurable_id hn
      (by simpa only [id, Real.norm_eq_abs, (even_two_mul k).pow_abs] using h)

section Real

variable {Ω 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ} {p : ℝ≥0∞}

/-- A real polynomial evaluated along `g`, cast into any `RCLike` scalar field, lies in `Lᵖ` as
soon as `gᵏ` does for every `k` in its support. -/
theorem memLp_algebraMap_eval_of_forall_mem_support {q : ℝ[X]}
    (hmom : ∀ k ∈ q.support, MemLp (fun ω => g ω ^ k) p μ) :
    MemLp (fun ω => (algebraMap ℝ 𝕜) (q.eval (g ω))) p μ := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_eval_of_forall_mem_support hmom).ofReal (K := 𝕜)

/-- A real polynomial evaluated along `g`, cast into any `RCLike` scalar field, lies in every `Lᵖ`
with `p ≠ ∞` as soon as every power of `g` is integrable. -/
theorem memLp_algebraMap_eval_of_forall_integrable_pow (hp : p ≠ ∞)
    (hmom : ∀ k : ℕ, Integrable (fun ω => g ω ^ k) μ) (q : ℝ[X]) :
    MemLp (fun ω => (algebraMap ℝ 𝕜) (q.eval (g ω))) p μ :=
  memLp_algebraMap_eval_of_forall_mem_support fun k _ =>
    memLp_pow_of_forall_integrable_pow (fun x _ _ => norm_pow x _) hp hmom k

end Real

variable {μ : Measure ℝ} {p : ℝ≥0∞}

/-- Polynomial evaluation on `ℝ`, cast into any `RCLike` scalar field, bundled as an `ℝ`-linear
map into `Lᵖ`, against any measure for which every monomial lies in `Lᵖ`. -/
noncomputable def polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, MemLp (fun x : ℝ => x ^ k) p μ) :
    ℝ[X] →ₗ[ℝ] Lp 𝕜 p μ where
  toFun q := (memLp_algebraMap_eval_of_forall_mem_support (𝕜 := 𝕜)
    (g := fun x : ℝ => x) (q := q) fun k _ => hmom k).toLp _
  map_add' q r := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (.of_forall fun x => by simp)
  map_smul' a q := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x => by simp [Algebra.smul_def])

/-- `polynomialEvalLp` sends a polynomial to the `Lᵖ` class of its scalar-cast evaluation, given
by `MemLp.toLp`. -/
lemma polynomialEvalLp_apply (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, MemLp (fun x : ℝ => x ^ k) p μ) (q : ℝ[X]) :
    polynomialEvalLp 𝕜 hmom q =
      (memLp_algebraMap_eval_of_forall_mem_support (𝕜 := 𝕜) (g := fun x : ℝ => x) (q := q)
        fun k _ => hmom k).toLp _ := by
  simp only [polynomialEvalLp, LinearMap.coe_mk, AddHom.coe_mk]

/-- The `Lᵖ` representative of `polynomialEvalLp 𝕜 hmom q` agrees `μ`-almost everywhere with the
scalar-cast pointwise evaluation of `q`. -/
lemma coeFn_polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, MemLp (fun x : ℝ => x ^ k) p μ) (q : ℝ[X]) :
    ⇑(polynomialEvalLp 𝕜 hmom q) =ᵐ[μ] fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x) := by
  rw [polynomialEvalLp_apply]
  exact MemLp.coeFn_toLp _

end TauCeti
