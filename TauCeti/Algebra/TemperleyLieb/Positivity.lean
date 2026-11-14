/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.QuantumGroups.QuantumInteger.Real
public import TauCeti.RingTheory.TraceFunctional.Positive
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

import TauCeti.Algebra.TemperleyLieb.PathModel
import TauCeti.Algebra.TemperleyLieb.SpinPositivity
import TauCeti.Combinatorics.SimpleGraph.PathGraph

/-!
# Jones's positivity theorem

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. At an inadmissible loop value
`0 < δ` with `θ = arccos (δ / 2)`, the form on `n` strands is positive semidefinite exactly below
the first bad level `k = ⌊π / θ⌋` (`TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`). This
file proves both characterizations together with their sesquilinear-form and pullback consequences.

Necessity: write `δ = 2 cos θ` with `θ = arccos (δ / 2)` and put `k = ⌊π / θ⌋`. When `0 < δ` is
not admissible, `π / θ` is not an integer, so the quantum integers `[1], …, [k]` are positive and
`[k + 1]` is negative. Hence the Jones–Wenzl projection `f_k` exists; it is a self-adjoint
idempotent, so its norm `tr k (f_k⋆ * f_k) = tr k f_k = [k + 1]` is negative. Adding `n - k`
straight strands multiplies the trace by `δ ^ (n - k) > 0`, so the form on `n` strands is
indefinite for every `n ≥ k`.

Sufficiency: for `δ ≥ 2` this is the spin model of
`TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_two_le`. For `δ = 2 cos (π / m)`
it is the path model of `TauCeti.Algebra.TemperleyLieb.PathModel` on the Dynkin graph `A_(m-1)`,
the path graph on `m - 1` vertices, with the vertex `t` weighted by `√[t + 1]`: the quantum
integers `[1], …, [m - 1]` are positive, `[m] = 0`, and the recurrence
`[t] + [t + 2] = δ [t + 1]` says that they form an eigenvector of the adjacency matrix with
eigenvalue `δ`. Below the first bad level (`n < k`), `[1], …, [n + 1]` are positive and satisfy
the same adjacency recurrence at every vertex of distance `< n` from `0` on `pathGraph (n + 1)`, so
bounded-level Markov uniqueness identifies `tr n` with the truncated path trace and proves
positivity on `n` strands.

Whenever the form on `n` strands is positive semidefinite, `tr n` is a
`TauCeti.StarPositiveFunctional`, so its sesquilinear form `(tr n).traceSesqForm` satisfies the
Cauchy–Schwarz inequality and its trace radical coincides with the null cone
`{x | (tr n).traceSesqForm x x = 0}`. Conversely, pulling positive functionals back along
`⋆`-homomorphisms into star algebras forces `δ ∈ jonesLoopParameters`, without any injectivity or
traciality assumption on the target algebras.

The results are stated for an arbitrary Markov trace, so they apply to the spin-model trace
`TauCeti.TemperleyLieb.markovTrace` through `TauCeti.TemperleyLieb.isMarkovTrace_markovTrace`.
Over `ℂ` the analytic adjoint is the instance `TauCeti.TemperleyLieb.instStarRing`, whose
hypothesis `Fact (IsSelfAdjoint (δ : ℂ))` holds for every real `δ` by `Complex.conj_ofReal`.

## Main definitions

* `TauCeti.TemperleyLieb.jonesLoopParameters`: the admissible loop parameters
  `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctional`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctionalOfLtFloor`: `tr n` bundled as a
  `TauCeti.StarPositiveFunctional` at admissible parameters and below the first bad level.

## Main results

* `TauCeti.TemperleyLieb.qInt_pos_of_notMem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.qInt_floor_add_one_neg_of_notMem_jonesLoopParameters`: the signs of the
  quantum integers at an inadmissible positive loop parameter.
* `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_eq`: over a commutative star ring,
  every level `n ≥ k` contains an element of norm `δ ^ (n - k) * [k + 1]`, when `[1], …, [k]` are
  units.
* `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_neg`: at an inadmissible positive
  loop parameter, the form on `n` strands takes a negative value for every `n ≥ ⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_forall_nonneg`: **Jones's
  restriction**, the necessity half of Jones's positivity theorem.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_qInt_pos`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_lt_floor`: positivity on `n`
  strands from positive quantum integers `[1], …, [n + 1]`, and below level `⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`: **the first bad level**, characterizing
  positivity on `n` strands at an inadmissible positive loop parameter by `n < ⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.norm_traceSesqForm_le`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.mem_traceRadical_iff_traceSesqForm_self_eq_zero`:
  Cauchy–Schwarz and the null-cone characterization of the trace radical.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_starPositiveFunctional`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_inv_pow_mul`: the pullback
  admissibility criteria for `δ`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
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

/-- `1 = 2 cos (π / 3)` is the smallest admissible loop parameter. -/
theorem one_mem_jonesLoopParameters : (1 : ℝ) ∈ jonesLoopParameters :=
  Or.inl ⟨3, le_rfl, by rw [Nat.cast_ofNat, cos_pi_div_three]; norm_num⟩

/-- Every admissible loop parameter is at least `1`. -/
theorem one_le_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 1 ≤ δ := by
  obtain ⟨m, hm, rfl⟩ | h2 := hδ
  · have hm3 : π / (m : ℝ) ≤ π / 3 :=
      div_le_div_of_nonneg_left pi_pos.le (by positivity) (by exact_mod_cast hm)
    have hcos : cos (π / 3) ≤ cos (π / (m : ℝ)) :=
      cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hm3
    rw [cos_pi_div_three] at hcos
    linarith
  · linarith

/-- Reals strictly less than `1` are not admissible loop parameters. -/
theorem notMem_jonesLoopParameters_of_lt_one {δ : ℝ} (hδ : δ < 1) :
    δ ∉ jonesLoopParameters :=
  fun h ↦ (one_le_of_mem_jonesLoopParameters h).not_gt hδ

/-- Every admissible loop parameter is strictly positive. -/
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 0 < δ :=
  lt_of_lt_of_le zero_lt_one (one_le_of_mem_jonesLoopParameters hδ)

/-- Nonpositive reals are not admissible loop parameters. -/
theorem notMem_jonesLoopParameters_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) :
    δ ∉ jonesLoopParameters :=
  notMem_jonesLoopParameters_of_lt_one (hδ.trans_lt zero_lt_one)

section QuantumInteger

section CommRing

open SimpleGraph

/-- At any vertex `v < k` of `pathGraph (k + 1)`, the quantum integers `[t + 1]` satisfy the
adjacency eigenvector identity `∑ u ∈ neighborFinset v, [u + 1] = δ * [v + 1]`. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_lt {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    {v : Fin (k + 1)} (hv : v.val < k) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [neighborFinset_eq_filter, Finset.sum_filter]
  simp only [pathGraph_adj]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0)]
  have h (j : ℕ) : (if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0) =
      (if v.val + 1 = j then qInt R δ (j + 1) else 0) +
        (if j + 1 = v.val then qInt R δ (j + 1) else 0) := by
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq,
    ite_eq_left (Finset.mem_range.2 (by omega))]
  have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = v.val then qInt R δ (j + 1) else 0) =
      qInt R δ v := by
    obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  rw [h2, Nat.add_assoc, qInt_add_two]
  ring

/-- When `[k + 2] = 0`, the quantum integers `[t + 1]` on `pathGraph (k + 1)` form a global
`δ`-eigenvector of its adjacency matrix. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_eq_zero {R : Type*} [CommRing R] {δ : R}
    {k : ℕ} (hz : qInt R δ (k + 2) = 0) (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  obtain hv | hvk := lt_or_eq_of_le (Nat.lt_succ_iff.1 v.isLt)
  · exact sum_neighborFinset_pathGraph_qInt_of_lt δ hv
  · rw [neighborFinset_eq_filter, Finset.sum_filter]
    simp only [pathGraph_adj]
    rw [Fin.sum_univ_eq_sum_range
      (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0)]
    have h (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
        (if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0) =
          if j + 1 = k then qInt R δ (j + 1) else 0 := by
      rw [Finset.mem_range] at hj
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [Finset.sum_congr rfl h]
    have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = k then qInt R δ (j + 1) else 0) =
        qInt R δ k := by
      obtain _ | w := k
      · simp
      · simp only [Nat.add_right_cancel_iff]
        rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
    rw [h2, hvk, ← add_zero (qInt R δ k), ← hz, qInt_add_two]
    ring

end CommRing

variable {δ : ℝ}

/-- An inadmissible positive loop parameter is `2 cos θ` for `θ = arccos (δ / 2)` with
`0 < θ < π / 2`, and `π / θ` is not an integer. -/
private theorem arccos_spec_of_notMem_jonesLoopParameters (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) :
    0 < arccos (δ / 2) ∧ arccos (δ / 2) < π / 2 ∧ 2 * cos (arccos (δ / 2)) = δ ∧
      (⌊π / arccos (δ / 2)⌋₊ : ℝ) < π / arccos (δ / 2) := by
  rw [mem_jonesLoopParameters, not_or, not_le] at hδJ
  obtain ⟨hm, hδ₂⟩ := hδJ
  have hθ₀ : 0 < arccos (δ / 2) := arccos_pos.2 (by linarith)
  have hθ₂ : arccos (δ / 2) < π / 2 := arccos_lt_pi_div_two.2 (by linarith)
  have hcos : 2 * cos (arccos (δ / 2)) = δ := by
    rw [cos_arccos (by linarith) (by linarith)]
    ring
  refine ⟨hθ₀, hθ₂, hcos, (Nat.floor_le (by positivity)).lt_of_ne fun hfloor ↦ hm ?_⟩
  -- If `π / θ` were an integer `m`, then `θ = π / m` with `m ≥ 3`, so `δ` would be admissible.
  have h2 : (2 : ℝ) < ⌊π / arccos (δ / 2)⌋₊ := by
    rw [hfloor, lt_div_iff₀ hθ₀]
    linarith
  refine ⟨⌊π / arccos (δ / 2)⌋₊, by exact_mod_cast h2, ?_⟩
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

/-- At loop parameter `0`, the Hermitian forms `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace are
positive semidefinite on every number of strands. In particular, `0 < δ` cannot be omitted in
`forall_map_star_mul_self_nonneg_iff`. -/
theorem map_star_mul_self_nonneg_zero {R : Type*} [CommSemiring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Fact (IsSelfAdjoint (0 : R))]
    {tr : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R} (htr : IsMarkovTrace R 0 tr) (n : ℕ)
    (x : TemperleyLieb R 0 n) : 0 ≤ tr n (star x * x) := by
  -- `tr 0` is the augmentation, whereas `tr n = 0` for `n > 0`.
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [htr.eq_aug_zero, AlgHom.toLinearMap_apply, map_mul, aug_star]
    exact star_mul_self_nonneg (aug x)
  · simp [htr.eq_zero_of_pos hn]

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

/-- **Positivity on `n` strands from positive quantum integers.** If the quantum integers
`[1], …, [n + 1]` at the real loop value `δ` are positive, then the Hermitian form
`(x, y) ↦ tr n (x⋆ * y)` of a Markov trace is positive semidefinite on `n` strands. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hq : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) := by
  -- On `pathGraph (n + 1)` from `0`, the weights `√[t + 1]` satisfy the `δ`-eigenvector equation
  -- on `ball 0 n` (`v < n`), so bounded-level Markov uniqueness identifies `tr n` with `pathTrace`.
  have hpos (t : Fin (n + 1)) : 0 < qInt ℝ δ (t + 1) :=
    hq (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  refine htr.map_star_mul_self_nonneg_of_ball (G := SimpleGraph.pathGraph (n + 1))
    (v₀ := 0) (r := fun t ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ))
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos t)).ne')
    (fun t ↦ Complex.conj_ofReal _) (fun v hv ↦ ?_) x
  rw [SimpleGraph.mem_ball_pathGraph, Fin.val_zero, Nat.dist_zero_right, Nat.cast_lt] at hv
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (hpos _).le]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_lt δ hv

/-- **Positivity below the first bad level.** At an inadmissible loop parameter `δ > 0`, the
Hermitian form `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace is positive semidefinite for every
`n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : n < ⌊π / arccos (δ / 2)⌋₊) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_qInt_pos
    (fun _ hj ↦ qInt_pos_of_notMem_jonesLoopParameters hδ hδJ (Finset.mem_Icc.1 hj).1
      ((Finset.mem_Icc.1 hj).2.trans hn))
    x

/-- **The first bad level** for an arbitrary Markov trace. At an inadmissible loop parameter
`δ > 0`, the Hermitian form `(x, y) ↦ tr n (x⋆ * y)` on `n` strands is positive semidefinite
exactly when `n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  ⟨htr.lt_floor_of_forall_nonneg hδ hδJ, htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ⟩

/-- **Positivity at the discrete loop parameters.** For `δ = 2 cos (π / m)` with `m ≥ 2`, the
Hermitian forms `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every
number of strands. -/
theorem map_star_mul_self_nonneg_of_eq_two_mul_cos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {m : ℕ}
    (hm : 2 ≤ m) (hδ : δ = 2 * cos (π / m)) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) := by
  -- On the Dynkin graph `A_(m-1)` (`pathGraph (m - 1)`), `[1], …, [m - 1] > 0` and `[m] = 0`.
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  subst hδ
  have hpos (t : Fin (k + 1)) : 0 < qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1) :=
    qInt_two_mul_cos_pi_div_pos (by omega) (by omega)
  refine htr.map_star_mul_self_nonneg_of_graph (G := SimpleGraph.pathGraph (k + 1))
    (r := fun t ↦ ((√(qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1)) : ℝ) : ℂ))
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos t)).ne')
    (fun t ↦ Complex.conj_ofReal _) (fun v ↦ ?_) x
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (hpos _).le]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_eq_zero
    (qInt_two_mul_cos_pi_div_eq_zero (by omega)) v

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number of
strands. -/
theorem map_star_mul_self_nonneg_of_mem_jonesLoopParameters (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) := by
  obtain ⟨m, hm, hδm⟩ | h2 := hδ
  · exact htr.map_star_mul_self_nonneg_of_eq_two_mul_cos (by omega) hδm x
  · exact htr.map_star_mul_self_nonneg_of_two_le h2 x

/-- **Jones's positivity theorem.** For `δ > 0`, the Hermitian forms `(x, y) ↦ tr n (x⋆ * y)` of a
Markov trace are positive semidefinite on every number of strands exactly when `δ` is an admissible
loop parameter, `δ = 2 cos (π / m)` for some `m ≥ 3` or `δ ≥ 2`. -/
theorem forall_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters :=
  ⟨htr.mem_jonesLoopParameters_of_forall_nonneg hδ,
    fun h _ x ↦ htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters h x⟩

/-- For any `δ > 0` and any number `n` of strands, the Hermitian form of a Markov trace on `n`
strands is positive semidefinite exactly when `δ` is admissible or
`n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem forall_map_star_mul_self_nonneg_iff_mem_or_lt_floor
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters ∨ n < ⌊π / arccos (δ / 2)⌋₊ := by
  by_cases hδJ : δ ∈ jonesLoopParameters
  · simp [hδJ, htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδJ]
  · simp [hδJ, htr.forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ]

section Consequences

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, `tr n` bundled as a
`TauCeti.StarPositiveFunctional` on `TemperleyLieb ℂ (δ : ℂ) n`. -/
def starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg := htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδ

/-- Forgetting positivity recovers `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.starPositiveFunctional hδ n).toLinearMap = tr n :=
  (rfl)

/-- Evaluating `starPositiveFunctional` evaluates `tr n`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctional hδ n x = tr n x :=
  (rfl)

/-- Below the first bad level at an inadmissible loop parameter `δ > 0`, `tr n` bundled as a
`TauCeti.StarPositiveFunctional` on `TemperleyLieb ℂ (δ : ℂ) n`. -/
def starPositiveFunctionalOfLtFloor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊) :
    StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg := htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ hn

/-- Forgetting positivity recovers `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctionalOfLtFloor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊) :
    (htr.starPositiveFunctionalOfLtFloor hδ hδJ hn).toLinearMap = tr n :=
  (rfl)

/-- Evaluating `starPositiveFunctionalOfLtFloor` evaluates `tr n`. -/
@[simp]
theorem starPositiveFunctionalOfLtFloor_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctionalOfLtFloor hδ hδJ hn x = tr n x :=
  (rfl)

/-- **Cauchy–Schwarz inequality** for the Hermitian Markov trace form at an admissible loop
parameter. -/
theorem norm_traceSesqForm_le (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖(tr n).traceSesqForm x y‖ ≤
      √‖(tr n).traceSesqForm x x‖ * √‖(tr n).traceSesqForm y y‖ := by
  simpa using (htr.starPositiveFunctional hδ n).norm_map_star_mul_le x y

/-- At an admissible loop parameter, the trace radical on `n` strands is the null cone
`{x | (tr n).traceSesqForm x x = 0}` of the Hermitian Markov trace form. -/
theorem mem_traceRadical_iff_traceSesqForm_self_eq_zero (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} {x : TemperleyLieb ℂ (δ : ℂ) n} :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ (tr n).traceSesqForm x x = 0 := by
  simpa using (htr.starPositiveFunctional hδ n).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n) x

/-- **Cauchy–Schwarz inequality** for the Hermitian Markov trace form below the first bad level. -/
theorem norm_traceSesqForm_le_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖(tr n).traceSesqForm x y‖ ≤
      √‖(tr n).traceSesqForm x x‖ * √‖(tr n).traceSesqForm y y‖ := by
  simpa using (htr.starPositiveFunctionalOfLtFloor hδ hδJ hn).norm_map_star_mul_le x y

/-- Below the first bad level, the trace radical on `n` strands is the null cone
`{x | (tr n).traceSesqForm x x = 0}` of the Hermitian Markov trace form. -/
theorem mem_traceRadical_iff_traceSesqForm_self_eq_zero_of_lt_floor
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : n < ⌊π / arccos (δ / 2)⌋₊) {x : TemperleyLieb ℂ (δ : ℂ) n} :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ (tr n).traceSesqForm x x = 0 := by
  simpa using
    (htr.starPositiveFunctionalOfLtFloor hδ hδJ hn).mem_traceRadical_iff_apply_star_mul_self_eq_zero
      (htr.map_mul_comm n) x

/-- **Pullback criterion for admissibility.** Let `δ > 0`, and suppose for each `n` there is a
`⋆`-multiplicative map `ρ n` from `TemperleyLieb ℂ (δ : ℂ) n` into a complex star ring `B n`
carrying a `TauCeti.StarPositiveFunctional` `σ n` such that `σ n (ρ n x) = c n * tr n x` for some
positive real `c n > 0`. Then `δ ∈ jonesLoopParameters`. Neither injectivity of `ρ n` nor
traciality of `σ n` is needed. -/
theorem mem_jonesLoopParameters_of_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) {B : ℕ → Type*} [∀ n, NonUnitalRing (B n)] [∀ n, Module ℂ (B n)]
    [∀ n, StarRing (B n)] (σ : ∀ n, StarPositiveFunctional (B n)) {F : ℕ → Type*}
    [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, MulHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)] (ρ : ∀ n, F n)
    {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hρ : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x) = (c n : ℂ) * tr n x) :
    δ ∈ jonesLoopParameters := by
  refine htr.mem_jonesLoopParameters_of_forall_nonneg hδ fun n x ↦ ?_
  have hsq : 0 ≤ (c n : ℂ) * tr n (star x * x) := by
    rw [← hρ, map_mul, StarHomClass.map_star]
    exact (σ n).apply_star_mul_self_nonneg (ρ n x)
  rw [Complex.nonneg_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul] at hsq
  exact Complex.nonneg_iff.2 ⟨nonneg_of_mul_nonneg_right hsq.1 (hc n),
    (mul_eq_zero.1 hsq.2.symm).resolve_left (hc n).ne' |>.symm⟩

/-- **Pullback criterion for normalized traces.** Let `δ > 0`, and suppose for each `n` there is a
`⋆`-multiplicative map `ρ n` from `TemperleyLieb ℂ (δ : ℂ) n` into a complex star ring `B n`
carrying a `TauCeti.StarPositiveFunctional` `σ n` with `σ n (ρ n x) = δ⁻¹ ^ n * tr n x`. Then
`δ ∈ jonesLoopParameters`. -/
theorem mem_jonesLoopParameters_of_inv_pow_mul (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) {B : ℕ → Type*} [∀ n, NonUnitalRing (B n)] [∀ n, Module ℂ (B n)]
    [∀ n, StarRing (B n)] (σ : ∀ n, StarPositiveFunctional (B n)) {F : ℕ → Type*}
    [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, MulHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)] (ρ : ∀ n, F n)
    (hρ : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x) = (δ : ℂ)⁻¹ ^ n * tr n x) :
    δ ∈ jonesLoopParameters :=
  htr.mem_jonesLoopParameters_of_starPositiveFunctional hδ σ ρ
    (c := fun n ↦ δ⁻¹ ^ n) (fun _ ↦ by positivity) fun n x ↦ by
      push_cast
      exact hρ n x

end Consequences

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
and let `q` be a unit with `δ = -(q + q⁻¹)`. Then
`TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` is real and nonnegative for every `x` on `n`
strands exactly when `n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem markovTrace_nonneg_iff_lt_floor {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) (n : ℕ) :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ markovTrace q hq (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

end TauCeti.TemperleyLieb
