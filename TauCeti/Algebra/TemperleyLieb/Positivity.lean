/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.QuantumDimension
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.QuantumGroups.QuantumInteger.Real
public import TauCeti.RingTheory.TraceFunctional.Positive
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

import TauCeti.Algebra.TemperleyLieb.PathModel
import TauCeti.Algebra.TemperleyLieb.SpinPositivity
import TauCeti.Algebra.TemperleyLieb.TypeA
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos
import TauCeti.Analysis.StarAlgebra.CauchySchwarz

/-!
# Jones's positivity theorem and the first bad level

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. Across all real `δ`, positivity
on every number of strands holds if and only if `δ = 0` or `δ ∈ jonesLoopParameters`. At an
inadmissible `δ > 0`, the form on `n` strands is positive semidefinite if and only if
`n < ⌊π / arccos (δ / 2)⌋`. This file proves both equivalences together with their positive-trace
and pullback consequences.

Necessity: write `δ = 2 cos θ` with `θ = arccos (δ / 2)` and put `k = ⌊π / θ⌋`. When `0 < δ` is
not admissible, `π / θ` is not an integer, so the quantum integers `[1], …, [k]` are positive and
`[k + 1]` is negative. Hence the Jones–Wenzl projection `f_k` exists; it is a self-adjoint
idempotent, so its norm `tr k (f_k⋆ * f_k) = tr k f_k = [k + 1]` is negative. Adding `n - k`
straight strands multiplies the trace by `δ ^ (n - k) > 0`, so the form on `n` strands is
indefinite for every `n ≥ k`. Consequently, if a family of star-multiplicative maps pulls back
functionals nonnegative on squares `b⋆ * b` to positive multiples of `tr n` (for instance the
normalized Markov trace `δ⁻ⁿ tr n` in a subfactor tower) and `δ > 0`, then
`δ ∈ jonesLoopParameters`.

Sufficiency: for `δ ≥ 2` this is the spin model of
`TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_two_le`. For `δ = 2 cos (π / m)`
it is the path model of `TauCeti.Algebra.TemperleyLieb.PathModel` on the Dynkin graph `A_(m-1)`,
the path graph on `m - 1` vertices, with the vertex `t` weighted by `√[t + 1]`: the quantum
integers `[1], …, [m - 1]` are positive, `[m] = 0`, and the recurrence
`[t] + [t + 2] = δ [t + 1]` says that they form a global eigenvector of the adjacency matrix with
eigenvalue `δ` (`TauCeti.TemperleyLieb.isPathEigenvectorUpTo_pathGraph_two_mul_cos`). Below the
first bad level `k` of an inadmissible `δ > 0`, `[2], …, [k] > 0` and `[k + 1] < 0`, so no
positive-weight truncation `pathGraph m` (`1 ≤ m ≤ k`) satisfies the top-vertex equation; however,
on `n < k` strands the quantum integers `[1], …, [n + 1]` are still positive, and walks of fewer
than `n` steps from vertex `0` on `pathGraph (n + 1)` stay at non-top vertices `t < n`, where the
adjacency recurrence `[t] + [t + 2] = δ [t + 1]` holds for every `δ`
(`TauCeti.TemperleyLieb.isPathEigenvectorUpTo_pathGraph_sqrt_qInt`). Bounded-depth path-model
positivity (`TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo`)
then proves positivity on `n` strands.

At any admissible loop parameter `δ ∈ jonesLoopParameters`, `tr n` packages as a
`TauCeti.StarPositiveFunctional` (`TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctional`) and
descends directly to a faithful `TauCeti.StarPositiveFunctional` on the canonical trace-radical
quotient (`TauCeti.TemperleyLieb.IsMarkovTrace.quotientStarPositiveFunctional`), yielding
Cauchy–Schwarz and identifying the trace radical with the quadratic null space
`{x | tr n (x⋆ * x) = 0}`.

The results are stated for an arbitrary Markov trace, so they apply to the spin-model trace
`TauCeti.TemperleyLieb.markovTrace` through `TauCeti.TemperleyLieb.isMarkovTrace_markovTrace`.
Over `ℂ` the analytic adjoint is the instance `TauCeti.TemperleyLieb.instStarRing`, whose
hypothesis `Fact (IsSelfAdjoint (δ : ℂ))` holds for every real `δ` by `Complex.conj_ofReal`.

## Main definitions

* `TauCeti.TemperleyLieb.jonesLoopParameters`: the admissible loop parameters
  `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctional`: `tr n` packaged as a
  `TauCeti.StarPositiveFunctional` at admissible parameters.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientStarPositiveFunctional`: the faithful
  `TauCeti.StarPositiveFunctional` induced by `tr n` directly on the canonical trace-radical
  quotient `TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)`.

## Main results

* `TauCeti.TemperleyLieb.one_le_of_mem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.lt_two_of_notMem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.notMem_jonesLoopParameters_of_two_mul_cos_lt`,
  `TauCeti.TemperleyLieb.floor_pi_div_arccos_eq`: bounds `1 ≤ δ` and `δ < 2`, inadmissibility in
  the open gaps `(2 cos (π / m), 2 cos (π / (m + 1)))`, and evaluation of
  `⌊π / arccos (δ / 2)⌋ = m` on `[2 cos (π / m), 2 cos (π / (m + 1)))`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem** for `δ > 0` (and
  `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem` for all
  real `δ`).
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_lt_floor`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`: positivity below `⌊π / arccos (δ / 2)⌋`
  for every real `δ`, and **the first bad level** characterizing positivity on `n` strands at an
  inadmissible `δ > 0`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_eq_zero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.neg_one_pow_mul_map_star_mul_self_nonneg_of_eq_zero`:
  nonnegativity of `tr n (x⋆ * x)` and of the signed form `(-1) ^ n * tr n (x⋆ * x)` at `δ = 0`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_traceRadical_iff_map_star_mul_self_eq_zero`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.norm_map_star_mul_sq_le`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.nullSubmodule_quotientStarPositiveFunctional`: trace-radical
  null-space characterization, Cauchy–Schwarz, and faithfulness of the positive quotient trace at
  admissible parameters.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_pullback`: **pullback
  admissibility criterion** for `δ > 0`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Lemma 4.3.8,
  Theorem 4.3.17 and §§4.4–4.5.
-/

public section

namespace TauCeti.TemperleyLieb

open Real

/-- The **admissible loop parameters** `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`. By Jones's positivity
theorem these are the positive reals `δ` for which the Hermitian forms of the Temperley–Lieb Markov
trace with loop value `δ` are positive semidefinite on every number of strands; the squares `δ ^ 2`
of its members are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. -/
def jonesLoopParameters : Set ℝ :=
  {δ | (∃ m : ℕ, 3 ≤ m ∧ δ = 2 * cos (π / m)) ∨ 2 ≤ δ}

/-- Membership in the admissible loop parameters, unfolded. -/
theorem mem_jonesLoopParameters {δ : ℝ} :
    δ ∈ jonesLoopParameters ↔ (∃ m : ℕ, 3 ≤ m ∧ δ = 2 * cos (π / m)) ∨ 2 ≤ δ :=
  Iff.rfl

/-- Every discrete cosine value `2 cos (π / m)` with `m ≥ 3` is an admissible loop parameter. -/
theorem two_mul_cos_pi_div_mem_jonesLoopParameters {m : ℕ} (hm : 3 ≤ m) :
    2 * cos (π / m) ∈ jonesLoopParameters :=
  Or.inl ⟨m, hm, rfl⟩

/-- Every real number `δ ≥ 2` is an admissible loop parameter. -/
theorem mem_jonesLoopParameters_of_two_le {δ : ℝ} (hδ : 2 ≤ δ) : δ ∈ jonesLoopParameters :=
  Or.inr hδ

/-- Every inadmissible loop parameter is strictly less than `2`. -/
theorem lt_two_of_notMem_jonesLoopParameters {δ : ℝ} (h : δ ∉ jonesLoopParameters) : δ < 2 :=
  lt_of_not_ge fun h2 ↦ h (mem_jonesLoopParameters_of_two_le h2)

/-- Every admissible loop parameter is at least `1`, its smallest element `2 cos (π / 3) = 1`. -/
theorem one_le_of_mem_jonesLoopParameters {δ : ℝ} (h : δ ∈ jonesLoopParameters) : 1 ≤ δ := by
  obtain ⟨m, hm, rfl⟩ | h2 := h
  · have hdiv : π / (m : ℝ) ≤ π / 3 :=
      div_le_div_of_nonneg_left pi_pos.le (by positivity) (by exact_mod_cast hm)
    have hcos : cos (π / 3) ≤ cos (π / (m : ℝ)) :=
      cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hdiv
    rw [cos_pi_div_three] at hcos
    linarith
  · linarith

/-- Every admissible loop parameter is strictly positive. -/
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (h : δ ∈ jonesLoopParameters) : 0 < δ :=
  lt_of_lt_of_le zero_lt_one (one_le_of_mem_jonesLoopParameters h)

/-- Every admissible loop parameter is a unit in `ℂ`. -/
theorem isUnit_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) :
    IsUnit (δ : ℂ) :=
  (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne').isUnit

/-- No real number strictly below `1` is an admissible loop parameter. -/
theorem notMem_jonesLoopParameters_of_lt_one {δ : ℝ} (h : δ < 1) : δ ∉ jonesLoopParameters :=
  fun hJ ↦ h.not_ge (one_le_of_mem_jonesLoopParameters hJ)

/-- `0` is not an admissible loop parameter (`0 < 1 = 2 cos (π / 3)`). -/
@[simp]
theorem zero_notMem_jonesLoopParameters : (0 : ℝ) ∉ jonesLoopParameters :=
  notMem_jonesLoopParameters_of_lt_one zero_lt_one

/-- `1 = 2 cos (π / 3)` is an admissible loop parameter. -/
@[simp]
theorem one_mem_jonesLoopParameters : (1 : ℝ) ∈ jonesLoopParameters := by
  simpa [cos_pi_div_three] using two_mul_cos_pi_div_mem_jonesLoopParameters (m := 3) le_rfl

/-- `√2 = 2 cos (π / 4)` is an admissible loop parameter. -/
@[simp]
theorem sqrt_two_mem_jonesLoopParameters : √2 ∈ jonesLoopParameters := by
  convert two_mul_cos_pi_div_mem_jonesLoopParameters (m := 4) (by omega) using 1
  rw [Nat.cast_ofNat, cos_pi_div_four]
  ring

/-- `2` is an admissible loop parameter. -/
@[simp]
theorem two_mem_jonesLoopParameters : (2 : ℝ) ∈ jonesLoopParameters :=
  mem_jonesLoopParameters_of_two_le le_rfl

/-- For `δ ∈ [2 cos (π / m), 2 cos (π / (m + 1)))` (`m ≥ 1`), the floor `⌊π / arccos (δ / 2)⌋`
equals `m`, including at the left endpoint `δ = 2 cos (π / m)`. When `m ≥ 2` and `δ` lies in the
positive open gap `(2 cos (π / m), 2 cos (π / (m + 1)))`, this `m` is the first bad level
(`IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`); at the left endpoints
`δ = 2 cos (π / m)` (`m ≥ 2`), positivity holds on every number of strands. -/
theorem floor_pi_div_arccos_eq {m : ℕ} {δ : ℝ} (hm : 1 ≤ m)
    (hlo : 2 * cos (π / m) ≤ δ) (hhi : δ < 2 * cos (π / (m + 1 : ℕ))) :
    ⌊π / arccos (δ / 2)⌋₊ = m := by
  have hm1 : (1 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ hm
  have hx₀ : -1 ≤ δ / 2 := by linarith [neg_one_le_cos (π / m)]
  have hx₁ : δ / 2 < 1 := by linarith [cos_le_one (π / (m + 1 : ℕ))]
  have h1 : (m : ℝ) ≤ π / arccos (δ / 2) :=
    (le_pi_div_arccos_iff hx₀ hx₁ (by exact_mod_cast hm)).2 (by linarith)
  have h2 : π / arccos (δ / 2) < (m : ℝ) + 1 := by
    simpa [Nat.cast_add_one] using (pi_div_arccos_lt_iff hx₁ hm1).2 (by linarith)
  exact (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg m) h1)).2 ⟨h1, h2⟩

/-- No element of `jonesLoopParameters` lies strictly between consecutive cosine parameters
`2 cos (π / m)` and `2 cos (π / (m + 1))` (`m ≥ 1`). -/
theorem notMem_jonesLoopParameters_of_two_mul_cos_lt {m : ℕ} {δ : ℝ} (hm : 1 ≤ m)
    (hlo : 2 * cos (π / m) < δ) (hhi : δ < 2 * cos (π / (m + 1 : ℕ))) :
    δ ∉ jonesLoopParameters := by
  have hm1 : (1 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ hm
  have hx₁ : δ / 2 < 1 := by linarith [cos_le_one (π / (m + 1 : ℕ))]
  have h1 : (m : ℝ) < π / arccos (δ / 2) :=
    (lt_pi_div_arccos_iff (by exact_mod_cast hm)).2 ⟨by linarith, hx₁⟩
  have h2 : π / arccos (δ / 2) < (m : ℝ) + 1 := by
    simpa [Nat.cast_add_one] using (pi_div_arccos_lt_iff hx₁ hm1).2 (by linarith)
  rintro (⟨k, hk, rfl⟩ | h2le)
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have harc : arccos (2 * cos (π / k) / 2) = π / k := by
      rw [mul_div_cancel_left₀ _ two_ne_zero,
        arccos_cos (by positivity) (div_le_self pi_pos.le hk1)]
    rw [harc, div_div_cancel₀ pi_ne_zero] at h1 h2
    have hmk : m < k := by exact_mod_cast h1
    have hkm : k < m + 1 := by exact_mod_cast h2
    omega
  · linarith

section QuantumInteger

variable {δ : ℝ}

/-- An inadmissible positive loop parameter is `2 cos θ` for `θ = arccos (δ / 2)` with
`0 < θ < π / 2`, and `π / θ` is not an integer. -/
private theorem arccos_spec_of_notMem_jonesLoopParameters (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) :
    0 < arccos (δ / 2) ∧ arccos (δ / 2) < π / 2 ∧ 2 * cos (arccos (δ / 2)) = δ ∧
      (⌊π / arccos (δ / 2)⌋₊ : ℝ) < π / arccos (δ / 2) := by
  have hδ₂ : δ < 2 := lt_two_of_notMem_jonesLoopParameters hδJ
  have hθ₀ : 0 < arccos (δ / 2) := arccos_pos.2 (by linarith)
  have hθ₂ : arccos (δ / 2) < π / 2 := arccos_lt_pi_div_two.2 (by linarith)
  have hcos : 2 * cos (arccos (δ / 2)) = δ := by
    rw [cos_arccos (by linarith) (by linarith)]
    ring
  refine ⟨hθ₀, hθ₂, hcos, (Nat.floor_le (by positivity)).lt_of_ne fun hfloor ↦ hδJ ?_⟩
  -- If `π / θ` were an integer `m`, then `θ = π / m` with `m ≥ 3`, so `δ` would be admissible.
  have h2 : (2 : ℝ) < ⌊π / arccos (δ / 2)⌋₊ := by
    rw [hfloor, lt_div_iff₀ hθ₀]
    linarith
  convert two_mul_cos_pi_div_mem_jonesLoopParameters (m := ⌊π / arccos (δ / 2)⌋₊)
    (by exact_mod_cast h2) using 1
  rw [hfloor, div_div_cancel₀ pi_ne_zero, hcos]

/-- At an inadmissible positive loop parameter `δ`, the quantum integers `[1], …, [k]` are
positive, where `k = ⌊π / arccos (δ / 2)⌋`. -/
theorem qInt_pos_of_notMem_jonesLoopParameters (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ ⌊π / arccos (δ / 2)⌋₊) : 0 < qInt ℝ δ j := by
  obtain ⟨hθ₀, -, hcos, hfloor⟩ := arccos_spec_of_notMem_jonesLoopParameters hδ hδJ
  rw [← hcos]
  exact qInt_two_mul_cos_pos_of_le_floor hθ₀ hfloor hj hjk

/-- At an inadmissible positive loop parameter `δ`, the quantum integer `[k + 1]` is negative,
where `k = ⌊π / arccos (δ / 2)⌋`. -/
theorem qInt_floor_add_one_neg_of_notMem_jonesLoopParameters (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) : qInt ℝ δ (⌊π / arccos (δ / 2)⌋₊ + 1) < 0 := by
  obtain ⟨hθ₀, hθ₂, hcos, -⟩ := arccos_spec_of_notMem_jonesLoopParameters hδ hδJ
  have h := qInt_two_mul_cos_floor_add_one_neg hθ₀ (by linarith [pi_pos])
  rwa [hcos] at h

end QuantumInteger

namespace IsMarkovTrace

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} [Fact (IsSelfAdjoint δ)]
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- The norm of the Jones–Wenzl projection for the Hermitian form of a Markov trace is its quantum
dimension `[n + 1]`, provided `[1], …, [n]` are units. -/
theorem map_star_jonesWenzl_mul_jonesWenzl (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    tr n (star (jonesWenzl δ n) * jonesWenzl δ n) = qInt R δ (n + 1) := by
  rw [star_jonesWenzl, (isIdempotentElem_jonesWenzl h).eq, htr.map_jonesWenzl n h]

/-- If `[1], …, [k]` are units, then on every number `n ≥ k` of strands some element has norm
`δ ^ (n - k) * [k + 1]` for the Hermitian form of a Markov trace: the Jones–Wenzl projection on
`k` strands, with `n - k` straight strands added. -/
theorem exists_map_star_mul_self_eq (htr : IsMarkovTrace R δ tr) {k : ℕ}
    (h : ∀ j ∈ Finset.Icc 1 k, IsUnit (qInt R δ j)) {n : ℕ} (hkn : k ≤ n) :
    ∃ x : TemperleyLieb R δ n, tr n (star x * x) = δ ^ (n - k) * qInt R δ (k + 1) := by
  obtain rfl | hk := k.eq_zero_or_pos
  · exact ⟨1, by simp [htr.map_one]⟩
  induction n, hkn using Nat.le_induction with
  | base => exact ⟨jonesWenzl δ k, by
    rw [htr.map_star_jonesWenzl_mul_jonesWenzl h, Nat.sub_self, pow_zero, one_mul]⟩
  | succ n hkn ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨strandIncl x, ?_⟩
    rw [← strandIncl_star, ← map_mul, htr.map_strandIncl, hx,
      show m + 1 + 1 - k = m + 1 - k + 1 by omega, pow_succ]
    ring

end StarRing

section StarOrderedRing

variable {R : Type*} [CommSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  {δ : R} [Fact (IsSelfAdjoint δ)] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- At loop parameter `0`, every Markov trace over a star-ordered commutative semiring is
nonnegative on elements `x⋆ * x`: it is the augmentation on zero strands and vanishes on one or
more strands. -/
theorem map_star_mul_self_nonneg_of_eq_zero (htr : IsMarkovTrace R δ tr) (hδ : δ = 0) (n : ℕ)
    (x : TemperleyLieb R δ n) : 0 ≤ tr n (star x * x) := by
  subst hδ
  obtain _ | n := n
  · rw [htr.apply_zero, map_mul, aug_star]
    exact star_mul_self_nonneg (aug x)
  · simp [htr.apply_succ_eq_zero]

end StarOrderedRing

section StarOrderedCommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  {δ : R} [Fact (IsSelfAdjoint δ)] {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- At loop parameter `0`, the signed form `(-1) ^ n * tr n (x⋆ * x)` of a Markov trace over a
star-ordered commutative ring is nonnegative on every number of strands, since the trace vanishes
on one or more strands. -/
theorem neg_one_pow_mul_map_star_mul_self_nonneg_of_eq_zero (htr : IsMarkovTrace R δ tr)
    (hδ : δ = 0) (n : ℕ) (x : TemperleyLieb R δ n) : 0 ≤ (-1 : R) ^ n * tr n (star x * x) := by
  obtain _ | n := n
  · simpa using htr.map_star_mul_self_nonneg_of_eq_zero hδ 0 x
  · subst hδ
    simp [htr.apply_succ_eq_zero]

end StarOrderedCommRing

open scoped ComplexOrder

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **Failure of positivity from level `k` on.** Let `0 < δ` be an inadmissible loop parameter and
`k = ⌊π / arccos (δ / 2)⌋`. On every number `n ≥ k` of strands the Hermitian form of a Markov
trace takes a negative value: the witness is the Jones–Wenzl projection `f_k`, of norm
`δ ^ (n - k) * [k + 1] < 0` once `n - k` straight strands are added. -/
theorem exists_map_star_mul_self_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : ⌊π / arccos (δ / 2)⌋₊ ≤ n) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, tr n (star x * x) < 0 := by
  have hq (j : ℕ) : qInt ℂ (δ : ℂ) j = (qInt ℝ δ j : ℂ) :=
    (Complex.ofRealHom.map_qInt δ j).symm
  have hunit : ∀ j ∈ Finset.Icc 1 ⌊π / arccos (δ / 2)⌋₊, IsUnit (qInt ℂ (δ : ℂ) j) := by
    intro j hj
    obtain ⟨hj, hjk⟩ := Finset.mem_Icc.1 hj
    rw [hq]
    exact (Complex.ofReal_ne_zero.2
      (qInt_pos_of_notMem_jonesLoopParameters hδ hδJ hj hjk).ne').isUnit
  obtain ⟨x, hx⟩ := htr.exists_map_star_mul_self_eq hunit hn
  refine ⟨x, ?_⟩
  rw [hx, hq]
  exact_mod_cast mul_neg_of_pos_of_neg (pow_pos hδ _)
    (qInt_floor_add_one_neg_of_notMem_jonesLoopParameters hδ hδJ)

/-- **Jones's restriction on the loop parameter.** If `δ > 0` and the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number of strands,
then `δ` is admissible: `δ = 2 cos (π / m)` for some `m ≥ 3`, or `δ ≥ 2`. -/
theorem mem_jonesLoopParameters_of_forall_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (h : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) :
    δ ∈ jonesLoopParameters := by
  by_contra hδJ
  obtain ⟨x, hx⟩ := htr.exists_map_star_mul_self_neg hδ hδJ le_rfl
  exact (h _ x).not_gt hx

/-- At an inadmissible loop parameter `δ > 0`, the Hermitian form of a Markov trace on `n` strands
can be positive semidefinite only below level `⌊π / arccos (δ / 2)⌋`. -/
theorem lt_floor_of_forall_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ}
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) :
    n < ⌊π / arccos (δ / 2)⌋₊ := by
  by_contra hn
  obtain ⟨x, hx⟩ := htr.exists_map_star_mul_self_neg hδ hδJ (not_lt.1 hn)
  exact (h x).not_gt hx

/-- **Positivity at the discrete loop parameters.** For `δ = 2 cos (π / m)` with `m ≥ 2`, the
Hermitian forms `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every
number of strands. The trace is that of the path model on the Dynkin graph `A_(m-1)`, with the
vertex `t` weighted by `√[t + 1]`, the square root of the quantum integer `[t + 1]`, all of which
are positive. -/
theorem map_star_mul_self_nonneg_of_eq_two_mul_cos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {m : ℕ}
    (hm : 2 ≤ m) (hδ : δ = 2 * cos (π / m)) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  subst hδ
  have hpos (t : Fin (k + 1)) : 0 < qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1) :=
    qInt_two_mul_cos_pi_div_pos (by omega) (by omega)
  exact htr.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos t)).ne')
    (fun t ↦ Complex.conj_ofReal _)
    ((isPathEigenvectorUpTo_pathGraph_two_mul_cos 0 n).map Complex.ofRealHom) x

/-- **Positivity on `n` strands from positive quantum integers.** Whenever `[1], …, [n + 1]` are
positive, the Hermitian form `(x, y) ↦ tr n (x⋆ * y)` of any Markov trace is positive semidefinite
on `n` strands: walks of fewer than `n` steps from `0` on `SimpleGraph.pathGraph (n + 1)` never
reach the top vertex `n`, so the weights `√[t + 1]` satisfy the bounded-depth eigenvector equation
up to `n`. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hq : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) := by
  have hpos (t : Fin (n + 1)) : 0 < qInt ℝ δ (t + 1) :=
    hq (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  exact htr.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos t)).ne')
    (fun t ↦ Complex.conj_ofReal _)
    ((isPathEigenvectorUpTo_pathGraph_sqrt_qInt le_rfl (fun t ↦ (hpos t).le)).map
      Complex.ofRealHom) x

/-- **Jones's positivity theorem.** For `δ > 0`, the Hermitian forms `(x, y) ↦ tr n (x⋆ * y)` of a
Markov trace are positive semidefinite on every number of strands exactly when `δ` is an admissible
loop parameter, `δ = 2 cos (π / m)` for some `m ≥ 3` or `δ ≥ 2`. -/
theorem forall_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters := by
  refine ⟨htr.mem_jonesLoopParameters_of_forall_nonneg hδ, fun h n x ↦ ?_⟩
  obtain ⟨m, hm, hδm⟩ | h2 := h
  · exact htr.map_star_mul_self_nonneg_of_eq_two_mul_cos (by omega) hδm x
  · exact htr.map_star_mul_self_nonneg_of_two_le h2 x

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Hermitian forms of a Markov
trace are positive semidefinite on every number of strands. -/
theorem map_star_mul_self_nonneg_of_mem_jonesLoopParameters
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) :=
  (htr.forall_map_star_mul_self_nonneg_iff (pos_of_mem_jonesLoopParameters hδ)).2 hδ n x

/-- Across all real loop parameters `δ : ℝ`, the Hermitian forms of a Markov trace are positive
semidefinite on every number of strands if and only if `δ = 0` or `δ ∈ jonesLoopParameters`. -/
theorem forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ = 0 ∨ δ ∈ jonesLoopParameters := by
  rcases lt_trichotomy δ 0 with hneg | rfl | hpos
  · refine iff_of_false (fun h ↦ ?_) (fun h ↦ ?_)
    · have h1 := h 1 1
      rw [star_one, mul_one, htr.map_one, pow_one] at h1
      have hlt : ((δ : ℂ)) < 0 := by exact_mod_cast hneg
      exact h1.not_gt hlt
    · rcases h with rfl | hJ
      · exact hneg.false
      · linarith [pos_of_mem_jonesLoopParameters hJ]
  · simp only [true_or, iff_true]
    intro n x
    exact htr.map_star_mul_self_nonneg_of_eq_zero Complex.ofReal_zero n x
  · rw [htr.forall_map_star_mul_self_nonneg_iff hpos]
    exact ⟨Or.inr, fun h ↦ h.resolve_left hpos.ne'⟩

/-- **Positivity below `⌊π / arccos (δ / 2)⌋`.** For every real loop parameter `δ`, the Hermitian
form `(x, y) ↦ tr n (x⋆ * y)` of any Markov trace is positive semidefinite on `n` strands whenever
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hn : n < ⌊π / arccos (δ / 2)⌋₊) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) := by
  obtain _ | m := n
  · rw [htr.apply_zero, map_mul, aug_star]
    exact star_mul_self_nonneg (aug x)
  have hfl : 2 ≤ ⌊π / arccos (δ / 2)⌋₊ := by omega
  have h2 : (2 : ℝ) ≤ π / arccos (δ / 2) := by
    exact_mod_cast (Nat.le_floor_iff (div_nonneg pi_pos.le (arccos_nonneg _))).1 hfl
  have h0 : 0 ≤ δ := by
    have hcos := ((le_pi_div_arccos_iff' one_lt_two).1 h2).1
    rw [cos_pi_div_two] at hcos
    linarith
  obtain rfl | hδ := h0.eq_or_lt
  · exact htr.map_star_mul_self_nonneg_of_eq_zero Complex.ofReal_zero (m + 1) x
  by_cases hδJ : δ ∈ jonesLoopParameters
  · exact htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδJ (m + 1) x
  · exact htr.map_star_mul_self_nonneg_of_qInt_pos
      (fun _ hj ↦ qInt_pos_of_notMem_jonesLoopParameters hδ hδJ
        (Finset.mem_Icc.1 hj).1 ((Finset.mem_Icc.1 hj).2.trans hn)) x

/-- **The first bad level.** At an inadmissible loop parameter `δ > 0`, the Hermitian form
`(x, y) ↦ tr n (x⋆ * y)` of a Markov trace on `n` strands is positive semidefinite if and only if
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  ⟨htr.lt_floor_of_forall_nonneg hδ hδJ, fun hn x ↦ htr.map_star_mul_self_nonneg_of_lt_floor hn x⟩

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Markov trace on `n` strands
packaged as a `TauCeti.StarPositiveFunctional`. -/
def starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg := htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδ n

/-- Forgetting positivity of `starPositiveFunctional` recovers `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.starPositiveFunctional hδ n).toLinearMap = tr n := (rfl)

/-- Evaluating `starPositiveFunctional` computes `tr n`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctional hδ n x = tr n x := (rfl)

/-- `starPositiveFunctional` is tracial. -/
theorem starPositiveFunctional_mul_comm (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctional hδ n (x * y) = htr.starPositiveFunctional hδ n (y * x) :=
  htr.map_mul_comm n x y

/-- The trace radical of `starPositiveFunctional` coincides with the trace radical of `tr n`. -/
theorem traceRadical_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.starPositiveFunctional hδ n).toLinearMap.traceRadical
        (htr.starPositiveFunctional_mul_comm hδ n) =
      (tr n).traceRadical (htr.map_mul_comm n) := by
  simp

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Markov trace on the canonical
trace-radical quotient `TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)`,
packaged as a faithful `TauCeti.StarPositiveFunctional` whose underlying linear map is
`LinearMap.quotientTrace`. Supply the star-stable radical instance via `htr.isStar_traceRadical n`.
-/
def quotientStarPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n ⧸
      (tr n).traceRadical (htr.map_mul_comm n)) :=
  (htr.starPositiveFunctional hδ n).quotientTrace (htr.map_mul_comm n)

/-- Forgetting positivity of `quotientStarPositiveFunctional` recovers the algebraic quotient trace
`LinearMap.quotientTrace`. -/
@[simp]
theorem toLinearMap_quotientStarPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.quotientStarPositiveFunctional hδ n).toLinearMap =
      (tr n).quotientTrace (htr.map_mul_comm n) :=
  (htr.starPositiveFunctional hδ n).toLinearMap_quotientTrace (htr.map_mul_comm n)

/-- Evaluating `quotientStarPositiveFunctional` computes `LinearMap.quotientTrace`. -/
theorem quotientStarPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientStarPositiveFunctional hδ n x =
      (tr n).quotientTrace (htr.map_mul_comm n) x :=
  LinearMap.congr_fun (htr.toLinearMap_quotientStarPositiveFunctional hδ n) x

/-- On a quotient class `mk x`, `quotientStarPositiveFunctional` evaluates to `tr n x`. -/
@[simp]
theorem quotientStarPositiveFunctional_mk (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.quotientStarPositiveFunctional hδ n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) = tr n x :=
  (htr.starPositiveFunctional hδ n).quotientTrace_mk (htr.map_mul_comm n) x

/-- Evaluating `quotientStarPositiveFunctional` at `1` gives `δ ^ n`. -/
@[simp]
theorem quotientStarPositiveFunctional_one (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    htr.quotientStarPositiveFunctional hδ n 1 = (δ : ℂ) ^ n := by
  rw [htr.quotientStarPositiveFunctional_apply, LinearMap.quotientTrace_one, htr.map_one]

/-- The positive quotient trace is tracial. -/
theorem quotientStarPositiveFunctional_mul_comm (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x y : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientStarPositiveFunctional hδ n (x * y) =
      htr.quotientStarPositiveFunctional hδ n (y * x) :=
  (htr.starPositiveFunctional hδ n).quotientTrace_mul_comm (htr.map_mul_comm n) x y

/-- Faithfulness of the positive quotient trace: a square `x⋆ * x` has zero quotient trace
exactly when `x = 0`. -/
@[simp]
theorem quotientStarPositiveFunctional_star_mul_self_eq_zero_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientStarPositiveFunctional hδ n (star x * x) = 0 ↔ x = 0 :=
  (htr.starPositiveFunctional hδ n).quotientTrace_star_mul_self_eq_zero_iff
    (htr.map_mul_comm n) x

/-- The positive quotient trace has trivial GNS null space. -/
theorem nullSubmodule_quotientStarPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.quotientStarPositiveFunctional hδ n).nullSubmodule = ⊥ :=
  (htr.starPositiveFunctional hδ n).nullSubmodule_quotientTrace (htr.map_mul_comm n)

/-- **Cauchy–Schwarz inequality** for a Markov trace at an admissible loop parameter. -/
theorem norm_map_star_mul_sq_le (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖tr n (star x * y)‖ ^ 2 ≤ ‖tr n (star x * x)‖ * ‖tr n (star y * y)‖ :=
  (tr n).norm_map_star_mul_sq_le
    (htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδ n) x y

/-- At an admissible loop parameter, the trace radical on `n` strands is the quadratic null space
`{x | tr n (x⋆ * x) = 0}`. -/
theorem mem_traceRadical_iff_map_star_mul_self_eq_zero (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ tr n (star x * x) = 0 :=
  (htr.starPositiveFunctional hδ n).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n) x

/-- **Pullback admissibility criterion.** Suppose `δ > 0` and at each strand count `n` a
star-multiplicative map `ρ n` into a type `B n` with multiplication and star pulls back a map
`φ n : B n → ℂ` satisfying `0 ≤ φ n (b⋆ * b)` to a positive real multiple `c n * tr n` of a Markov
trace (for instance `c n = δ⁻¹ ^ n` for the normalized Markov trace in a subfactor tower, or
`c n = 1` for the unnormalized trace). Then `δ ∈ jonesLoopParameters`. -/
theorem mem_jonesLoopParameters_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    {B : ℕ → Type*} [∀ n, Mul (B n)] [∀ n, Star (B n)]
    (φ : ∀ n, B n → ℂ) (hφ : ∀ (n : ℕ) (b : B n), 0 ≤ φ n (star b * b))
    {F : ℕ → Type*} [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, MulHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    (ρ : ∀ n, F n) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hpull : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), φ n (ρ n x) = c n * tr n x) :
    δ ∈ jonesLoopParameters := by
  refine htr.mem_jonesLoopParameters_of_forall_nonneg hδ fun n x ↦ ?_
  have h0 : 0 ≤ (c n : ℂ) * tr n (star x * x) := by
    rw [← hpull, map_mul, StarHomClass.map_star]
    exact hφ n (ρ n x)
  have hinv : (0 : ℂ) ≤ ((c n)⁻¹ : ℝ) := Complex.zero_le_real.2 (inv_nonneg.2 (hc n).le)
  have hmul := mul_nonneg hinv h0
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hc n).ne', Complex.ofReal_one,
    one_mul] at hmul

end IsMarkovTrace

open scoped ComplexOrder in
/-- **Jones's positivity theorem** for the spin-model trace. Let `δ > 0` and let `q` be a unit with
`δ = -(q + q⁻¹)`. Then `TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` is real and nonnegative
for every number of strands and every `x` exactly when `δ` is an admissible loop parameter. -/
theorem markovTrace_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ markovTrace q hq (star x * x)) ↔
      δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff hδ

open scoped ComplexOrder in
/-- **The first bad level** for the spin-model trace. Let `δ > 0` be an inadmissible loop parameter
and let `q` be a unit with `δ = -(q + q⁻¹)`. Then `TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)`
is real and nonnegative for every `x` on `n` strands if and only if `n < ⌊π / arccos (δ / 2)⌋`. -/
theorem markovTrace_nonneg_iff_lt_floor {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) (n : ℕ) :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ markovTrace q hq (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

end TauCeti.TemperleyLieb
