/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.QuantumDimension
public import TauCeti.QuantumGroups.QuantumInteger.Real
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

import TauCeti.Algebra.TemperleyLieb.PathModel
import TauCeti.Algebra.TemperleyLieb.SpinPositivity
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Jones's positivity theorem

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. This file proves both
directions.

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
eigenvalue `δ`.

Below the first bad level: at an inadmissible `δ > 0`, the quantum integers `[1], …, [n + 1]` are
positive whenever `n < k = ⌊π / arccos (δ / 2)⌋`. On the truncated half-line `pathGraph (n + 1)`
from `0`, every walk of fewer than `n` steps ends strictly below the top vertex `n`, where the
adjacency recurrence `[t] + [t + 2] = δ [t + 1]` holds without needing `[n + 2] = 0`. Bounded-level
Markov uniqueness identifies the resulting path-model trace with `tr n`, proving that the form on
`n` strands is positive semidefinite if and only if `n < k`
(`TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
`TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`). At `δ = 0 = 2 cos (π / 2)` the forms are
positive semidefinite on all strands even though `0 ∉ jonesLoopParameters`, whereas for `δ < 0`
positivity fails already on one strand (`tr 1 1 = δ < 0`), giving the unrestricted real
characterization
`TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem`.

The results are stated for an arbitrary Markov trace, so they apply to the spin-model trace
`TauCeti.TemperleyLieb.markovTrace` through `TauCeti.TemperleyLieb.isMarkovTrace_markovTrace`.
Over `ℂ` the analytic adjoint is the instance `TauCeti.TemperleyLieb.instStarRing`, whose
hypothesis `Fact (IsSelfAdjoint (δ : ℂ))` holds for every real `δ` by `Complex.conj_ofReal`.

## Main definitions

* `TauCeti.TemperleyLieb.jonesLoopParameters`: the admissible loop parameters
  `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`.

## Main results

* `TauCeti.TemperleyLieb.pos_of_mem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.mem_jonesLoopParameters_iff_sq`: positivity of admissible loop parameters
  and the characterization of their squares `{4 cos² (π / m) : m ≥ 3} ∪ [4, ∞)`.
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
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_qInt_pos`: positivity on `n`
  strands whenever `[1], …, [n + 1]` are positive.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`: **the first bad level** at an
  inadmissible positive loop parameter.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem`:
  all-level positivity for arbitrary real loop parameters `δ`.

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

/-- Every admissible loop parameter is strictly positive. -/
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (h : δ ∈ jonesLoopParameters) : 0 < δ := by
  obtain ⟨m, hm, rfl⟩ | h2 := h
  · simpa using qInt_two_mul_cos_pi_div_pos (m := m) (n := 2) zero_lt_two hm
  · linarith

/-- Nonpositive real numbers are not admissible loop parameters. -/
theorem notMem_jonesLoopParameters_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) :
    δ ∉ jonesLoopParameters :=
  fun h ↦ (pos_of_mem_jonesLoopParameters h).not_ge hδ

/-- Zero is not in `jonesLoopParameters`, even though at `δ = 0` the Markov trace forms are
positive semidefinite (`0` on positive strand counts and the norm square on `0` strands). -/
@[simp]
theorem zero_notMem_jonesLoopParameters : (0 : ℝ) ∉ jonesLoopParameters :=
  notMem_jonesLoopParameters_of_nonpos le_rfl

/-- A positive real `δ` is an admissible loop parameter if and only if `δ ^ 2` lies in the Jones
index set `{4 cos² (π / m) : m ≥ 3} ∪ [4, ∞)`. -/
theorem mem_jonesLoopParameters_iff_sq {δ : ℝ} (hδ : 0 < δ) :
    δ ∈ jonesLoopParameters ↔ (∃ m : ℕ, 3 ≤ m ∧ δ ^ 2 = 4 * cos (π / m) ^ 2) ∨ 4 ≤ δ ^ 2 := by
  constructor
  · rintro (⟨m, hm, rfl⟩ | h2)
    · exact Or.inl ⟨m, hm, by ring⟩
    · exact Or.inr (by nlinarith)
  · rintro (⟨m, hm, hsq⟩ | h4)
    · have hpos : 0 < 2 * cos (π / m) := by
        simpa using qInt_two_mul_cos_pi_div_pos (m := m) (n := 2) zero_lt_two hm
      exact Or.inl ⟨m, hm, by nlinarith⟩
    · exact Or.inr (by nlinarith)

section QuantumInteger

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

open SimpleGraph in
/-- On the path graph `pathGraph (k + 1)` with vertices `0, …, k`, the sum of the quantum integers
`[u + 1]` over the neighbours `u` of `v` equals `δ * [v + 1]` minus the missing top term `[k + 2]`
when `v = k`, over any commutative ring. -/
private theorem sum_neighborFinset_pathGraph_qInt_eq {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) =
      δ * qInt R δ (v + 1) - if v.val = k then qInt R δ (k + 2) else 0 := by
  rw [neighborFinset_eq_filter, Finset.sum_filter]
  simp only [pathGraph_adj]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0)]
  have h (j : ℕ) : (if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0) =
      (if v.val + 1 = j then qInt R δ (j + 1) else 0) +
        (if j + 1 = v.val then qInt R δ (j + 1) else 0) := by
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  have h1 : (if v.val + 1 ∈ Finset.range (k + 1) then qInt R δ (v + 1 + 1) else 0) =
      qInt R δ (v + 2) - if v.val = k then qInt R δ (k + 2) else 0 := by
    split_ifs with hv hvk hvk
    · exfalso; simp at hv; omega
    · exact (sub_zero _).symm
    · rw [hvk, sub_self]
    · exfalso; simp at hv; omega
  have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = v.val then qInt R δ (j + 1) else 0) =
      qInt R δ v := by
    obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  rw [h1, h2, qInt_add_two]
  ring

open SimpleGraph in
/-- At every interior vertex `v < k` of `pathGraph (k + 1)`, the quantum integers `[t + 1]` satisfy
the adjacency recurrence `[v] + [v + 2] = δ * [v + 1]` over any commutative ring. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_lt {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    {v : Fin (k + 1)} (hv : v.val < k) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, ite_eq_right hv.ne, sub_zero]

open SimpleGraph in
/-- At `δ = 2 cos (π / (k + 2))`, the quantum integers `[t + 1]` on the vertices `t` of the path
graph on `k + 1` vertices, the Dynkin graph `A_(k+1)`, form an eigenvector of its adjacency
matrix with eigenvalue `δ`: this is the recurrence `[t] + [t + 2] = δ [t + 1]`, with `[0] = 0` at
one end of the graph and `[k + 2] = 0` at the other. -/
private theorem sum_neighborFinset_pathGraph_qInt {k : ℕ} (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (u + 1) =
      2 * cos (π / (k + 2 : ℕ)) * qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, qInt_two_mul_cos_pi_div_eq_zero (by omega),
    ite_self, sub_zero]

/-- When the quantum integers `[1], …, [n + 1]` are nonnegative, the weights `√[t + 1]` on
`pathGraph (n + 1)` satisfy the walk-endpoint eigenvector equation from `0` up to `n` steps: every
walk of `k < n` steps from `0` ends at a vertex `< n`, away from the boundary vertex `n`. -/
private theorem isWalkEigenvectorUpTo_pathGraph_sqrt_qInt {n : ℕ}
    (hnonneg : ∀ j ∈ Finset.Icc 1 (n + 1), 0 ≤ qInt ℝ δ j) :
    IsWalkEigenvectorUpTo (SimpleGraph.pathGraph (n + 1)) 0
      (fun t : Fin (n + 1) ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)) (δ : ℂ) n := by
  rw [isWalkEigenvectorUpTo_iff]
  intro k hk s hs
  have hv : (s (Fin.last k)).val < n := by
    have hle := hs.apply_le_add (f := Fin.val)
      (fun _ _ huv ↦ by rw [SimpleGraph.pathGraph_adj] at huv; omega) (Fin.last k)
    simp only [Fin.val_zero, zero_add, Fin.val_last] at hle
    omega
  have hsq (t : Fin (n + 1)) :
      (((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)) ^ 2 = (qInt ℝ δ (t + 1) : ℂ) := by
    rw [← Complex.ofReal_pow,
      Real.sq_sqrt (hnonneg (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))]
  simp only [hsq]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_lt δ hv

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

/-- **Positivity from positive quantum integers.** If the quantum integers `[1], …, [n + 1]` at a
real loop parameter `δ` are positive, then the Hermitian form `(x, y) ↦ tr n (x⋆ * y)` of a Markov
trace on `n` strands is positive semidefinite. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hpos : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) := by
  have ht (t : Fin (n + 1)) : 0 < qInt ℝ δ (t + 1) :=
    hpos (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  exact htr.map_star_mul_self_nonneg_of_isWalkEigenvectorUpTo
    (G := SimpleGraph.pathGraph (n + 1))
    (r := fun t ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ))
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (ht t)).ne')
    (fun _ ↦ Complex.conj_ofReal _) 0
    (isWalkEigenvectorUpTo_pathGraph_sqrt_qInt fun j hj ↦ (hpos j hj).le) le_rfl x

/-- **Positivity below the first bad level.** At an inadmissible loop parameter `δ > 0`, the
Hermitian form of a Markov trace on `n` strands is positive semidefinite for every
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_qInt_pos (fun _ hj ↦ by
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hj
    exact qInt_pos_of_notMem_jonesLoopParameters hδ hδJ hj1 (by omega)) x

/-- **The first bad level** for an abstract Markov trace. Let `0 < δ` be an inadmissible loop
parameter and write `k = ⌊π / arccos (δ / 2)⌋`. Then the Hermitian form `(x, y) ↦ tr n (x⋆ * y)`
on `n` strands is positive semidefinite exactly when `n < k`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  ⟨htr.lt_floor_of_forall_nonneg hδ hδJ,
    fun hn ↦ htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ hn⟩

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
  refine htr.map_star_mul_self_nonneg_of_graph (G := SimpleGraph.pathGraph (k + 1))
    (r := fun t ↦ ((√(qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1)) : ℝ) : ℂ))
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos t)).ne')
    (fun _ ↦ Complex.conj_ofReal _) (fun v ↦ ?_) x
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (hpos _).le]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt v

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

/-- For `δ > 0`, the Hermitian form of a Markov trace on `n` strands is positive semidefinite
if and only if `δ` is admissible or `n < ⌊π / arccos (δ / 2)⌋`. -/
theorem forall_map_star_mul_self_nonneg_iff_mem_or_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters ∨ n < ⌊π / arccos (δ / 2)⌋₊ := by
  by_cases hδJ : δ ∈ jonesLoopParameters
  · simp [(htr.forall_map_star_mul_self_nonneg_iff hδ).2 hδJ n, hδJ]
  · simp [hδJ, htr.forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ]

/-- For an arbitrary real loop parameter `δ`, the Hermitian forms of a Markov trace are positive
semidefinite on every number of strands if and only if `δ = 0` or `δ ∈ jonesLoopParameters`: at
`δ = 0 = 2 cos (π / 2)` the forms remain positive semidefinite, whereas for `δ < 0` positivity
already fails on `1` strand since `tr 1 1 = δ < 0`. -/
theorem forall_map_star_mul_self_nonneg_iff_eq_zero_or_mem
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ tr n (star x * x)) ↔
      δ = 0 ∨ δ ∈ jonesLoopParameters := by
  rcases lt_trichotomy δ 0 with hneg | rfl | hpos
  · refine iff_of_false (fun h ↦ ?_) ?_
    · have h1 := h 1 1
      rw [star_one, one_mul, htr.map_one, pow_one] at h1
      exact h1.not_gt (by exact_mod_cast hneg)
    · rintro (rfl | hJ)
      · exact hneg.ne rfl
      · exact hneg.not_gt (pos_of_mem_jonesLoopParameters hJ)
  · refine iff_of_true (fun n x ↦ ?_) (Or.inl rfl)
    exact htr.map_star_mul_self_nonneg_of_eq_two_mul_cos (m := 2) le_rfl (by simp) x
  · simp [hpos.ne', htr.forall_map_star_mul_self_nonneg_iff hpos]

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
/-- **The first bad level** for the spin-model trace. Let `0 < δ` be an inadmissible loop
parameter, write `k = ⌊π / arccos (δ / 2)⌋`, and let `q` be a unit with `δ = -(q + q⁻¹)`. Then
`TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` is real and nonnegative for every `x` on `n`
strands exactly when `n < k`. -/
theorem markovTrace_nonneg_iff_lt_floor {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) (n : ℕ) :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ markovTrace q hq (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

end TauCeti.TemperleyLieb
