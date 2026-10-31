/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Weierstrass
import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Weak convergence from convergence of moments

The *method of moments* on the real line: if probability measures `μᵢ` on `ℝ` have finite moments
of every order and `∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`, where the limit `μ` is concentrated on a
compact set, then `μᵢ → μ` weakly. The approximating measures need not be compactly supported,
let alone supported in one common compact set. This is how a limit theorem proved by computing
moments, such as the free central limit theorem or the moment convergence of a random-matrix
ensemble, is turned into weak convergence of the corresponding laws.

## Main results

* `TauCeti.tendsto_integral_eval_of_tendsto_integral_pow` — convergence of all moments gives
  convergence of the integral of every real polynomial.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow` — the method of moments:
  moment convergence to a compactly supported limit implies weak convergence.

## Implementation notes

The proof does not go through Prokhorov's theorem. Let `|x| ≤ R` on the support of `μ`, put
`M = R + 1`, and fix a bounded continuous `f` with `|f| ≤ C`. By the Weierstrass approximation
theorem there is a polynomial `p` with `|f - p| < δ` on `[-M, M]`. Outside `[-M, M]` the Markov-type
bound `1 ≤ x²ⁿ / M²ⁿ` and the inequality `|p| ≤ t p² + 1 / (4t)` give, for every `x`,
`|f x - p x| ≤ q x := δ + t p(x)² + (C + 1 / (4t)) x²ⁿ / M²ⁿ`, with the polynomial `q` of the
same shape for all `i`. Since `∫ q dμᵢ → ∫ q dμ ≤ δ + t (C + δ)² + (C + 1 / (4t)) (R / M)²ⁿ`, the
choice of a small `t` and then a large `n` makes `∫ |f - p| dμᵢ` eventually small. The higher
moments thus provide both the tightness and the uniform integrability of `p` that the standard
argument through subsequential limits requires.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 30.2.
-/

public section

open MeasureTheory Filter Polynomial Set Finset
open scoped Topology

namespace TauCeti

variable {ι : Type*} {l : Filter ι}

/-- If every monomial is eventually integrable against `μᵢ`, then eventually all the monomials up
to the degree of a given polynomial are. -/
private theorem eventually_forall_le_natDegree_integrable {μs : ι → Measure ℝ}
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ n) (μs i)) (p : ℝ[X]) :
    ∀ᶠ i in l, ∀ k ≤ p.natDegree, Integrable (fun x : ℝ => x ^ k) (μs i) :=
  (eventually_all_finite (Set.finite_Iic p.natDegree)).2 fun n _ => hμs n

/-- If every moment `∫ xⁿ dμᵢ` converges to `∫ xⁿ dμ`, then so does the integral of every real
polynomial. The moments must be genuine: each monomial is assumed integrable against `μ` and,
eventually, against `μᵢ`. -/
theorem tendsto_integral_eval_of_tendsto_integral_pow {μs : ι → Measure ℝ} {μ : Measure ℝ}
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ n) (μs i))
    (hμ : ∀ n, Integrable (fun x : ℝ => x ^ n) μ)
    (h : ∀ n, Tendsto (fun i => ∫ x, x ^ n ∂μs i) l (𝓝 (∫ x, x ^ n ∂μ))) (p : ℝ[X]) :
    Tendsto (fun i => ∫ x, p.eval x ∂μs i) l (𝓝 (∫ x, p.eval x ∂μ)) := by
  rw [integral_eval_eq_sum_range fun n _ => hμ n]
  refine (tendsto_finsetSum _ fun n _ => (h n).const_mul (p.coeff n)).congr' ?_
  filter_upwards [eventually_forall_le_natDegree_integrable hμs p] with i hi
  exact (integral_eval_eq_sum_range hi).symm

/-- The pointwise domination behind the method of moments: if `|f| ≤ C` and `|p - f| < δ` on
`[-M, M]`, then for all `t > 0` and `n`, everywhere on `ℝ`,
`|f x - p x| ≤ δ + t p(x)² + (C + 1 / (4t)) x²ⁿ / M²ⁿ`. -/
private theorem abs_sub_eval_le {f : ℝ → ℝ} {p : ℝ[X]} {C δ M t : ℝ} (hM : 0 < M) (ht : 0 < t)
    (hfC : ∀ x, |f x| ≤ C) (hp : ∀ x ∈ Icc (-M) M, |p.eval x - f x| < δ) (n : ℕ) (x : ℝ) :
    |f x - p.eval x| ≤
      δ + t * p.eval x ^ 2 + (C + 1 / (4 * t)) / M ^ (2 * n) * x ^ (2 * n) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hfC 0)
  have hδ : 0 < δ := (abs_nonneg _).trans_lt (hp 0 ⟨by linarith, hM.le⟩)
  have h₁ : 0 ≤ t * p.eval x ^ 2 := by positivity
  have h₂ : 0 ≤ (C + 1 / (4 * t)) / M ^ (2 * n) * x ^ (2 * n) :=
    mul_nonneg (by positivity) ((even_two_mul n).pow_nonneg x)
  by_cases hx : x ∈ Icc (-M) M
  · linarith [abs_sub_comm (f x) (p.eval x), hp x hx]
  -- Off `[-M, M]`, bound `|f - p|` by `C + |p|`, and use `1 ≤ x²ⁿ / M²ⁿ` and
  -- `|p| ≤ t p² + 1 / (4t)`.
  have hMx : M ≤ |x| := (not_le.1 fun h => hx (abs_le.1 h)).le
  have hpow : M ^ (2 * n) ≤ x ^ (2 * n) := by
    rw [← (even_two_mul n).pow_abs x]
    exact pow_le_pow_left₀ hM.le hMx _
  have htail : C + 1 / (4 * t) ≤ (C + 1 / (4 * t)) / M ^ (2 * n) * x ^ (2 * n) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hamgm : |p.eval x| ≤ t * p.eval x ^ 2 + 1 / (4 * t) := by
    rw [← sq_abs (p.eval x), ← sub_nonneg]
    have : t * |p.eval x| ^ 2 + 1 / (4 * t) - |p.eval x| =
        (2 * t * |p.eval x| - 1) ^ 2 / (4 * t) := by
      field_simp
      ring
    rw [this]
    positivity
  linarith [abs_sub (f x) (p.eval x), hfC x]

/-- On the support `[-R, R]` of the limit measure, the dominating function of `abs_sub_eval_le` is
at most `3δ` once `t` and `n` are chosen so that `t (C + δ)² ≤ δ` and `c (R / M)²ⁿ ≤ δ`. -/
private theorem dominator_le {f : ℝ → ℝ} {p : ℝ[X]} {C δ R M t c : ℝ} (hR : 0 ≤ R) (hRM : R < M)
    (ht : 0 < t) (hc : 0 ≤ c) (hfC : ∀ x, |f x| ≤ C) (hp : ∀ x ∈ Icc (-M) M, |p.eval x - f x| < δ)
    (htδ : t * (C + δ) ^ 2 ≤ δ) {n : ℕ} (hn : c * ((R / M) ^ 2) ^ n ≤ δ) {x : ℝ} (hx : |x| ≤ R) :
    δ + t * p.eval x ^ 2 + c / M ^ (2 * n) * x ^ (2 * n) ≤ 3 * δ := by
  have hM : 0 < M := hR.trans_lt hRM
  have hpx : |p.eval x| ≤ C + δ := by
    have := hp x (abs_le.1 (hx.trans hRM.le))
    linarith [abs_sub_abs_le_abs_sub (p.eval x) (f x), hfC x]
  have h₁ : t * p.eval x ^ 2 ≤ t * (C + δ) ^ 2 := by
    rw [← sq_abs (p.eval x)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hpx 2) ht.le
  have h₂ : c / M ^ (2 * n) * x ^ (2 * n) ≤ c * ((R / M) ^ 2) ^ n :=
    calc c / M ^ (2 * n) * x ^ (2 * n) = c * ((|x| / M) ^ 2) ^ n := by
          rw [← (even_two_mul n).pow_abs x]
          ring
      _ ≤ c * ((R / M) ^ 2) ^ n := by gcongr
  linarith

end TauCeti

namespace MeasureTheory.ProbabilityMeasure

open TauCeti

variable {ι : Type*} {l : Filter ι}

/-- **The method of moments.** Let `μᵢ` and `μ` be probability measures on `ℝ` such that `μ` is
concentrated on a compact set, every moment of `μᵢ` is eventually finite, and
`∫ xⁿ dμᵢ → ∫ xⁿ dμ` for every `n`. Then `μᵢ → μ` weakly. -/
theorem tendsto_of_tendsto_integral_pow {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} {K : Set ℝ} (hK : IsCompact K) (hμK : (μ : Measure ℝ) Kᶜ = 0)
    (hμs : ∀ n, ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ n) (μs i : Measure ℝ))
    (h : ∀ n, Tendsto (fun i => ∫ x, x ^ n ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ n ∂(μ : Measure ℝ)))) :
    Tendsto μs l (𝓝 μ) := by
  -- `μ` is concentrated on `[-R, R]`, and `M = R + 1`.
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  set M := R + 1
  have hM : 0 < M := by positivity
  have hae : ∀ᵐ x ∂(μ : Measure ℝ), |x| ≤ R := by
    filter_upwards [ae_iff.mpr hμK] with x hx
    exact (hR₀ x hx).trans (le_max_left _ _)
  have hμ := integrable_pow_of_ae_abs_le hae
  have hpoly := tendsto_integral_eval_of_tendsto_integral_pow hμs hμ h
  have hpolyμs (p : ℝ[X]) : ∀ᶠ i in l, Integrable (fun x => p.eval x) (μs i : Measure ℝ) := by
    filter_upwards [eventually_forall_le_natDegree_integrable hμs p] with i hi
    exact integrable_eval_of_forall_le_natDegree hi
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Approximate `f` by a polynomial `p` on `[-M, M]`.
  set δ := ε / 6 with hδε
  have hδ : 0 < δ := by positivity
  set C := ‖f‖
  have hfC (x : ℝ) : |f x| ≤ C := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-M) M f f.continuous.continuousOn δ hδ
  -- The polynomial `q` dominating `|f - p|` everywhere.
  set t := δ / ((C + δ) ^ 2 + 1)
  have ht : 0 < t := by positivity
  set c := C + 1 / (4 * t)
  have hc : 0 < c := by positivity
  have hRM : (R / M) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    exact pow_lt_pow_left₀ (by linarith) hR two_ne_zero
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hc) hRM
  set q : ℝ[X] := Polynomial.C δ + Polynomial.C t * p ^ 2 +
    Polynomial.C (c / M ^ (2 * n)) * X ^ (2 * n)
  have hq (x : ℝ) : q.eval x = δ + t * p.eval x ^ 2 + c / M ^ (2 * n) * x ^ (2 * n) := by
    simp [q]
  have hfpq (x : ℝ) : |f x - p.eval x| ≤ q.eval x := by
    rw [hq]
    exact abs_sub_eval_le hM ht hfC hp n x
  -- The limit of `∫ q dμᵢ` is at most `3δ`.
  have hqμ : ∫ x, q.eval x ∂(μ : Measure ℝ) ≤ 3 * δ := by
    have htδ : t * (C + δ) ^ 2 ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hb : ∀ᵐ x ∂(μ : Measure ℝ), q.eval x ≤ 3 * δ := by
      filter_upwards [hae] with x hx
      rw [hq]
      exact dominator_le hR (by linarith) ht hc.le hfC hp htδ ((lt_div_iff₀' hc).1 hn).le hx
    calc ∫ x, q.eval x ∂(μ : Measure ℝ) ≤ ∫ _, 3 * δ ∂(μ : Measure ℝ) :=
          integral_mono_ae (integrable_eval_of_forall_integrable_pow hμ q) (integrable_const _) hb
      _ = 3 * δ := by simp
  -- On the limit side, `|f - p| < δ` on the support of `μ`, so `|∫ f dμ - ∫ p dμ| ≤ δ`.
  have hfpμ : |∫ x, f x ∂(μ : Measure ℝ) - ∫ x, p.eval x ∂(μ : Measure ℝ)| ≤ δ := by
    rw [← integral_sub (f.integrable _) (integrable_eval_of_forall_integrable_pow hμ p)]
    have hb : ∀ᵐ x ∂(μ : Measure ℝ), ‖f x - p.eval x‖ ≤ δ := by
      filter_upwards [hae] with x hx
      have := hp x (abs_le.1 (hx.trans (by linarith)))
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact this.le
    have := norm_integral_le_of_norm_le_const hb
    rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this
  -- Eventually `∫ q dμᵢ < 4δ` and `|∫ p dμᵢ - ∫ p dμ| < δ`. Since `|f - p| ≤ q`, the triangle
  -- inequality bounds `|∫ f dμᵢ - ∫ f dμ|` by
  -- `|∫ f dμᵢ - ∫ p dμᵢ| + |∫ p dμᵢ - ∫ p dμ| + |∫ p dμ - ∫ f dμ| < 4δ + δ + δ = ε`.
  filter_upwards [(hpoly q).eventually_lt_const (show _ < 4 * δ by linarith),
    Metric.tendsto_nhds.1 (hpoly p) δ hδ, hpolyμs p, hpolyμs q] with i hqi hpi hpint hqint
  have hfpi : |∫ x, f x ∂(μs i : Measure ℝ) - ∫ x, p.eval x ∂(μs i : Measure ℝ)| ≤
      ∫ x, q.eval x ∂(μs i : Measure ℝ) := by
    rw [← integral_sub (f.integrable _) hpint]
    exact norm_integral_le_of_norm_le hqint
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hfpq x))
  rw [Real.dist_eq] at hpi ⊢
  rw [abs_sub_comm] at hfpμ
  linarith [hδε, abs_sub_le (∫ x, f x ∂(μs i : Measure ℝ)) (∫ x, p.eval x ∂(μs i : Measure ℝ))
      (∫ x, f x ∂(μ : Measure ℝ)),
    abs_sub_le (∫ x, p.eval x ∂(μs i : Measure ℝ)) (∫ x, p.eval x ∂(μ : Measure ℝ))
      (∫ x, f x ∂(μ : Measure ℝ))]

end MeasureTheory.ProbabilityMeasure
