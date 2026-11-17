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
# Jones's positivity theorem and the first bad level

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. For an inadmissible positive loop
value `δ = 2 cos θ` with `θ = arccos (δ / 2)`, positivity holds on `n` strands precisely below the
first bad level `k = ⌊π / θ⌋`. This file proves both theorems and the pullback criterion for
star-representations carrying positive functionals.

Necessity: write `δ = 2 cos θ` with `θ = arccos (δ / 2)` and put `k = ⌊π / θ⌋`. When `0 < δ` is
not admissible, `π / θ` is not an integer, so the quantum integers `[1], …, [k]` are positive and
`[k + 1]` is negative. Hence the Jones–Wenzl projection `f_k` exists; it is a self-adjoint
idempotent, so its norm `tr k (f_k⋆ * f_k) = tr k f_k = [k + 1]` is negative. Adding `n - k`
straight strands multiplies the trace by `δ ^ (n - k) > 0`, so the form on `n` strands is
indefinite for every `n ≥ k`.

Sufficiency: for `δ ≥ 2` this is the spin model of
`TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_two_le` (and also follows from the
truncated path model below). For `δ = 2 cos (π / m)` it is the path model of
`TauCeti.Algebra.TemperleyLieb.PathModel` on the Dynkin graph `A_(m-1)`, the path graph on `m - 1`
vertices, with the vertex `t` weighted by `√[t + 1]`: the quantum integers `[1], …, [m - 1]` are
positive, `[m] = 0`, and the recurrence `[t] + [t + 2] = δ [t + 1]` says that they form an
eigenvector of the adjacency matrix with eigenvalue `δ`. Below the first bad level, whenever
`[1], …, [n + 1]` are positive (in particular for `n < ⌊π / θ⌋` at an inadmissible `δ > 0`), the
truncated path model on `pathGraph (n + 1)` from vertex `0` with weights `√[t + 1]` satisfies the
eigenvector equation at every vertex reached in fewer than `n` steps; truncated Markov uniqueness
identifies its positive trace with `tr` up to level `n`.

The results are stated for truncated Markov traces (`IsMarkovTraceUpTo`) and full Markov traces
(`IsMarkovTrace`), so they apply to the spin-model trace `TauCeti.TemperleyLieb.markovTrace`
through `TauCeti.TemperleyLieb.isMarkovTrace_markovTrace`, as well as to star-representations into
algebras carrying positive functionals (the pullback criterion). Over `ℂ` the analytic adjoint is
the instance `TauCeti.TemperleyLieb.instStarRing`, whose hypothesis `Fact (IsSelfAdjoint (δ : ℂ))`
holds for every real `δ` by `Complex.conj_ofReal`.

## Main definitions

* `TauCeti.TemperleyLieb.jonesLoopParameters`: the admissible loop parameters
  `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`.

## Main results

* `TauCeti.TemperleyLieb.one_le_of_mem_jonesLoopParameters`: every admissible loop parameter is at
  least `1`.
* `TauCeti.TemperleyLieb.qInt_pos_of_notMem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.qInt_floor_add_one_neg_of_notMem_jonesLoopParameters`: the signs of the
  quantum integers at an inadmissible positive loop parameter.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.exists_map_star_mul_self_eq`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_eq`: over a commutative star ring,
  every level `n ≥ k` contains an element of norm `δ ^ (n - k) * [k + 1]`, when `[1], …, [k]` are
  units.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.exists_map_star_mul_self_neg`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_neg`: at an inadmissible positive
  loop parameter, the form on `n` strands takes a negative value for every `n ≥ ⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.map_star_mul_self_nonneg_of_qInt_pos`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_qInt_pos`: positivity on `n`
  strands whenever `[1], …, [n + 1]` are positive, via the truncated path model on
  `pathGraph (n + 1)`.
* `TauCeti.TemperleyLieb.IsMarkovTraceUpTo.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`: **the first bad level**; at an
  inadmissible `δ > 0`, the Hermitian form on `n` strands is positive semidefinite exactly when
  `n < ⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_forall_nonneg`: **Jones's
  restriction**, the necessity half of Jones's positivity theorem.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_eq_two_mul_cos`: positivity
  at the loop values `2 cos (π / m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_pullback`,
  `TauCeti.TemperleyLieb.mem_jonesLoopParameters_of_markov_pullback`,
  `TauCeti.TemperleyLieb.lt_floor_of_markov_pullback`: **pullback criteria** deriving admissibility
  (and the first-bad-level bound) from star-homomorphisms into algebras carrying positive
  functionals.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones and V. S. Sunder, *Introduction to Subfactors*, London Math. Soc. Lecture Note
  Ser. 234, Cambridge Univ. Press, 1997, Theorem 2.3.8.
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

/-- Every admissible loop parameter is at least `1` (corresponding to Jones indices at least
`1`). -/
theorem one_le_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 1 ≤ δ := by
  obtain ⟨m, hm, rfl⟩ | h2 := hδ
  · have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hle : π / m ≤ π / 3 := div_le_div_of_nonneg_left pi_pos.le (by positivity) hm'
    have hcos : cos (π / 3) ≤ cos (π / m) :=
      strictAntiOn_cos.antitoneOn ⟨by positivity, by linarith [pi_pos]⟩
        ⟨by positivity, by linarith [pi_pos]⟩ hle
    rw [cos_pi_div_three] at hcos
    linarith
  · linarith

/-- Every admissible loop parameter is positive. -/
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 0 < δ :=
  lt_of_lt_of_le zero_lt_one (one_le_of_mem_jonesLoopParameters hδ)

/-- Zero is not an admissible loop parameter. -/
theorem zero_notMem_jonesLoopParameters : (0 : ℝ) ∉ jonesLoopParameters :=
  fun h ↦ (pos_of_mem_jonesLoopParameters h).ne' rfl

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
/-- Neighbour sum of the quantum integers `[u + 1]` on the path graph `pathGraph (k + 1)`: the
neighbour below `v` contributes `[v]` (vanishing at `v = 0`), and the neighbour above `v`
contributes `[v + 2]` when `v < k` and `0` at the top vertex `v = k`. -/
private theorem sum_neighborFinset_pathGraph_qInt_eq {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) =
      (if v.val + 1 < k + 1 then qInt R δ (v + 2) else 0) + qInt R δ v := by
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
  congr 1
  · simp [Finset.mem_range]
  · obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]

open SimpleGraph in
/-- At any loop parameter `δ` and any vertex `v` strictly below the top of `pathGraph (k + 1)`,
the quantum integers `[u + 1]` satisfy the adjacency eigenvector equation at `v`. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_lt {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    {v : Fin (k + 1)} (hv : v.val < k) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, ite_eq_left (by omega), qInt_add_two]
  ring

open SimpleGraph in
/-- When `[k + 2] = 0`, the quantum integers `[u + 1]` form a global eigenvector of the adjacency
matrix of `pathGraph (k + 1)` with eigenvalue `δ`. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_eq_zero {R : Type*} [CommRing R] {δ : R}
    {k : ℕ} (h0 : qInt R δ (k + 2) = 0) (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq]
  have h1 : (if v.val + 1 < k + 1 then qInt R δ (v + 2) else 0) = qInt R δ (v + 2) := by
    split_ifs with hv
    · rfl
    · rw [show v.val + 2 = k + 2 by omega, h0]
  rw [h1, qInt_add_two]
  ring

end QuantumInteger

namespace IsMarkovTraceUpTo

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} [Fact (IsSelfAdjoint δ)] {N : ℕ}
  {tr : ∀ n : ℕ, n ≤ N → TemperleyLieb R δ n →ₗ[R] R}

/-- The norm of the Jones–Wenzl projection for the Hermitian form of a truncated Markov trace is
its quantum dimension `[n + 1]`, provided `[1], …, [n]` are units. -/
theorem map_star_jonesWenzl_mul_jonesWenzl (htr : IsMarkovTraceUpTo R δ N tr) {n : ℕ}
    (hn : n ≤ N) (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    tr n hn (star (jonesWenzl δ n) * jonesWenzl δ n) = qInt R δ (n + 1) := by
  rw [star_jonesWenzl, (isIdempotentElem_jonesWenzl h).eq, htr.map_jonesWenzl n hn h]

/-- If `[1], …, [k]` are units, then on every number `n` of strands with `k ≤ n ≤ N` some element
has norm `δ ^ (n - k) * [k + 1]` for the Hermitian form of a truncated Markov trace: the
Jones–Wenzl projection on `k` strands, with `n - k` straight strands added. -/
theorem exists_map_star_mul_self_eq (htr : IsMarkovTraceUpTo R δ N tr) {k : ℕ}
    (h : ∀ j ∈ Finset.Icc 1 k, IsUnit (qInt R δ j)) {n : ℕ} (hkn : k ≤ n) (hn : n ≤ N) :
    ∃ x : TemperleyLieb R δ n, tr n hn (star x * x) = δ ^ (n - k) * qInt R δ (k + 1) := by
  obtain rfl | hk := k.eq_zero_or_pos
  · exact ⟨1, by simp [htr.map_one]⟩
  induction n, hkn using Nat.le_induction with
  | base => exact ⟨jonesWenzl δ k, by
    rw [htr.map_star_jonesWenzl_mul_jonesWenzl hn h, Nat.sub_self, pow_zero, one_mul]⟩
  | succ n hkn ih =>
    obtain ⟨x, hx⟩ := ih (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨strandIncl x, ?_⟩
    rw [← strandIncl_star, ← map_mul, htr.map_strandIncl, hx,
      show m + 1 + 1 - k = m + 1 - k + 1 by omega, pow_succ]
    ring

end StarRing

open scoped ComplexOrder

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] {N : ℕ}
  {tr : ∀ n : ℕ, n ≤ N → TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **Failure of positivity from level `k` on** for a truncated Markov trace. Let `0 < δ` be an
inadmissible loop parameter and `k = ⌊π / arccos (δ / 2)⌋`. On every number `n` of strands with
`k ≤ n ≤ N` the Hermitian form takes a negative value. -/
theorem exists_map_star_mul_self_neg (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hkn : ⌊π / arccos (δ / 2)⌋₊ ≤ n) (hn : n ≤ N) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, tr n hn (star x * x) < 0 := by
  have hq (j : ℕ) : qInt ℂ (δ : ℂ) j = (qInt ℝ δ j : ℂ) :=
    (Complex.ofRealHom.map_qInt δ j).symm
  have hunit : ∀ j ∈ Finset.Icc 1 ⌊π / arccos (δ / 2)⌋₊, IsUnit (qInt ℂ (δ : ℂ) j) := by
    intro j hj
    obtain ⟨hj, hjk⟩ := Finset.mem_Icc.1 hj
    rw [hq]
    exact (Complex.ofReal_ne_zero.2
      (qInt_pos_of_notMem_jonesLoopParameters hδ hδJ hj hjk).ne').isUnit
  obtain ⟨x, hx⟩ := htr.exists_map_star_mul_self_eq hunit hkn hn
  refine ⟨x, ?_⟩
  rw [hx, hq]
  exact_mod_cast mul_neg_of_pos_of_neg (pow_pos hδ _)
    (qInt_floor_add_one_neg_of_notMem_jonesLoopParameters hδ hδJ)

/-- At an inadmissible loop parameter `δ > 0`, the Hermitian form of a truncated Markov trace on
`n ≤ N` strands can be positive semidefinite only below level `⌊π / arccos (δ / 2)⌋`. -/
theorem lt_floor_of_forall_nonneg (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n ≤ N)
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n hn (star x * x)) :
    n < ⌊π / arccos (δ / 2)⌋₊ := by
  by_contra hkn
  obtain ⟨x, hx⟩ := htr.exists_map_star_mul_self_neg hδ hδJ (not_lt.1 hkn) hn
  exact (h x).not_gt hx

/-- **Positivity from positive quantum integers.** If `[1], …, [n + 1]` are positive at a real
loop parameter `δ`, then the Hermitian form `(x, y) ↦ tr n hn (x⋆ * y)` of a truncated Markov
trace on `n ≤ N` strands is positive semidefinite: it is realized by the truncated path model on
`pathGraph (n + 1)` from vertex `0` with vertex weights `√[t + 1]`. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr) {n : ℕ}
    (hn : n ≤ N) (hpos : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n hn (star x * x) := by
  have hpos' (t : Fin (n + 1)) : 0 < qInt ℝ δ (t + 1) :=
    hpos (t + 1) (Finset.mem_Icc.2 ⟨Nat.succ_pos _, Nat.succ_le_succ (Nat.le_of_lt_succ t.isLt)⟩)
  refine htr.map_star_mul_self_nonneg_of_graph (G := SimpleGraph.pathGraph (n + 1))
    (v₀ := (0 : Fin (n + 1))) (r := fun t ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ))
    (fun t ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos' t)).ne')
    (fun t ↦ Complex.conj_ofReal _) (fun k hk s hs ↦ ?_) hn x
  have hlt : (s (Fin.last k)).val < n := by
    have hle := hs.apply_le_add (f := Fin.val)
      (fun _ _ h ↦ by rw [SimpleGraph.pathGraph_adj] at h; omega) (Fin.last k)
    simp only [Fin.val_zero, Fin.val_last, zero_add] at hle
    omega
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (hpos' _).le]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_lt δ hlt

/-- **Positivity below the first bad level** for a truncated Markov trace. At an inadmissible loop
parameter `δ > 0`, the Hermitian form on `n ≤ N` strands is positive semidefinite whenever
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n ≤ N) (hkn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n hn (star x * x) :=
  htr.map_star_mul_self_nonneg_of_qInt_pos hn (fun j hj ↦ by
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.1 hj
    exact qInt_pos_of_notMem_jonesLoopParameters hδ hδJ hj₁ (by omega)) x

/-- **The first bad level** for a truncated Markov trace. At an inadmissible loop parameter
`δ > 0`, the Hermitian form `(x, y) ↦ tr n hn (x⋆ * y)` on `n ≤ N` strands is positive
semidefinite exactly when `n < ⌊π / arccos (δ / 2)⌋`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n ≤ N) :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n hn (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  ⟨htr.lt_floor_of_forall_nonneg hδ hδJ hn, htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ hn⟩

/-- At loop parameter `0`, the Hermitian form of a truncated Markov trace is positive semidefinite
on every number of strands: on `0` strands `[1] = 1 > 0`, and on `n > 0` strands the trace
vanishes identically. This is why Jones's restriction requires `δ > 0`. -/
theorem map_star_mul_self_nonneg_of_loop_eq_zero (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr)
    (hδ : δ = 0) {n : ℕ} (hn : n ≤ N) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n hn (star x * x) := by
  obtain rfl | hn₀ := n.eq_zero_or_pos
  · exact htr.map_star_mul_self_nonneg_of_qInt_pos hn (fun j hj ↦ by
      have hj1 : j = 1 := by simp only [Finset.mem_Icc] at hj; omega
      simp [hj1]) x
  · rw [htr.eq_zero_of_loop_eq_zero (by exact_mod_cast hδ) hn₀ hn, LinearMap.zero_apply]

/-- At a negative loop parameter `δ < 0`, positivity already fails on one strand, since
`tr 1 (1⋆ * 1) = δ < 0`. -/
theorem exists_map_star_mul_self_neg_of_neg (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr)
    (hδ : δ < 0) (hN : 1 ≤ N) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) 1, tr 1 hN (star x * x) < 0 := by
  refine ⟨1, ?_⟩
  simpa [htr.map_one] using Complex.real_lt_real.2 hδ

/-- **Single-level pullback bound.** At an inadmissible loop parameter `δ > 0`, if a
star-multiplicative map `ρ` pulls back a functional `σ` nonnegative on squares `b⋆ * b` to a
positive real multiple `c * tr n hn`, then `n < ⌊π / arccos (δ / 2)⌋`. Injectivity of `ρ` and
traciality of `σ` are not required. -/
theorem lt_floor_of_pullback (htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n ≤ N) {B F : Type*} [Mul B] [Star B]
    [FunLike F (TemperleyLieb ℂ (δ : ℂ) n) B] [MulHomClass F (TemperleyLieb ℂ (δ : ℂ) n) B]
    [StarHomClass F (TemperleyLieb ℂ (δ : ℂ) n) B] (ρ : F) {σ : B → ℂ}
    (hσ : ∀ b, 0 ≤ σ (star b * b)) {c : ℝ} (hc : 0 < c)
    (hpull : ∀ x, σ (ρ x) = (c : ℂ) * tr n hn x) :
    n < ⌊π / arccos (δ / 2)⌋₊ := by
  refine htr.lt_floor_of_forall_nonneg hδ hδJ hn fun x ↦ ?_
  have h1 : 0 ≤ (c : ℂ) * tr n hn (star x * x) := by
    rw [← hpull, map_mul, map_star]
    exact hσ (ρ x)
  have h2 : 0 ≤ ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * tr n hn (star x * x)) :=
    mul_nonneg (Complex.zero_le_real.2 (inv_nonneg.2 hc.le)) h1
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one,
    one_mul] at h2

end IsMarkovTraceUpTo

namespace IsMarkovTrace

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} [Fact (IsSelfAdjoint δ)]
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

/-- The norm of the Jones–Wenzl projection for the Hermitian form of a Markov trace is its quantum
dimension `[n + 1]`, provided `[1], …, [n]` are units. -/
theorem map_star_jonesWenzl_mul_jonesWenzl (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    tr n (star (jonesWenzl δ n) * jonesWenzl δ n) = qInt R δ (n + 1) :=
  (htr.isMarkovTraceUpTo n).map_star_jonesWenzl_mul_jonesWenzl le_rfl h

/-- If `[1], …, [k]` are units, then on every number `n ≥ k` of strands some element has norm
`δ ^ (n - k) * [k + 1]` for the Hermitian form of a Markov trace: the Jones–Wenzl projection on
`k` strands, with `n - k` straight strands added. -/
theorem exists_map_star_mul_self_eq (htr : IsMarkovTrace R δ tr) {k : ℕ}
    (h : ∀ j ∈ Finset.Icc 1 k, IsUnit (qInt R δ j)) {n : ℕ} (hkn : k ≤ n) :
    ∃ x : TemperleyLieb R δ n, tr n (star x * x) = δ ^ (n - k) * qInt R δ (k + 1) :=
  (htr.isMarkovTraceUpTo n).exists_map_star_mul_self_eq h hkn le_rfl

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
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, tr n (star x * x) < 0 :=
  (htr.isMarkovTraceUpTo n).exists_map_star_mul_self_neg hδ hδJ hn le_rfl

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
    n < ⌊π / arccos (δ / 2)⌋₊ :=
  (htr.isMarkovTraceUpTo n).lt_floor_of_forall_nonneg hδ hδJ le_rfl h

/-- **Positivity from positive quantum integers.** If `[1], …, [n + 1]` are positive at a real
loop parameter `δ`, then the Hermitian form `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace on `n`
strands is positive semidefinite. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hpos : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) :=
  (htr.isMarkovTraceUpTo n).map_star_mul_self_nonneg_of_qInt_pos le_rfl hpos x

/-- **Positivity below the first bad level.** At an inadmissible loop parameter `δ > 0`, the
Hermitian form `(x, y) ↦ tr n (x⋆ * y)` of a Markov trace on `n` strands is positive semidefinite
for every `n < ⌊π / arccos (δ / 2)⌋`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) :=
  (htr.isMarkovTraceUpTo n).map_star_mul_self_nonneg_of_lt_floor hδ hδJ le_rfl hn x

/-- **The first bad level.** At an inadmissible loop parameter `δ > 0`, the Hermitian form
`(x, y) ↦ tr n (x⋆ * y)` of a Markov trace on `n` strands is positive semidefinite exactly when
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (htr.isMarkovTraceUpTo n).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ le_rfl

/-- At loop parameter `0`, the Hermitian form of a Markov trace is positive semidefinite on every
number of strands. -/
theorem map_star_mul_self_nonneg_of_loop_eq_zero (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ = 0)
    {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) :=
  (htr.isMarkovTraceUpTo n).map_star_mul_self_nonneg_of_loop_eq_zero hδ le_rfl x

/-- At a negative loop parameter `δ < 0`, positivity already fails on one strand. -/
theorem exists_map_star_mul_self_neg_of_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) 1, tr 1 (star x * x) < 0 :=
  (htr.isMarkovTraceUpTo 1).exists_map_star_mul_self_neg_of_neg hδ le_rfl

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
    (fun t ↦ Complex.conj_ofReal _) (fun v ↦ ?_) x
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (hpos _).le]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_eq_zero
    (qInt_two_mul_cos_pi_div_eq_zero (by omega)) v

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

/-- **Single-level pullback bound** for a Markov trace. -/
theorem lt_floor_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} {B F : Type*} [Mul B] [Star B]
    [FunLike F (TemperleyLieb ℂ (δ : ℂ) n) B] [MulHomClass F (TemperleyLieb ℂ (δ : ℂ) n) B]
    [StarHomClass F (TemperleyLieb ℂ (δ : ℂ) n) B] (ρ : F) {σ : B → ℂ}
    (hσ : ∀ b, 0 ≤ σ (star b * b)) {c : ℝ} (hc : 0 < c)
    (hpull : ∀ x, σ (ρ x) = (c : ℂ) * tr n x) :
    n < ⌊π / arccos (δ / 2)⌋₊ :=
  (htr.isMarkovTraceUpTo n).lt_floor_of_pullback hδ hδJ le_rfl ρ hσ hc hpull

/-- **Pullback criterion for Jones's restriction.** Let `δ > 0` and let `tr` be a Markov trace. If
for every number of strands `n` there exist a star-multiplicative map `ρ n` into a type `B n`
carrying a functional `σ n` nonnegative on squares `b⋆ * b` such that `σ n (ρ n x) = c n * tr n x`
for some real `c n > 0` (in particular `c n = (δ ^ n)⁻¹`), then `δ` is an admissible loop
parameter. Neither injectivity of `ρ n` nor traciality of `σ n` is required. -/
theorem mem_jonesLoopParameters_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    {B F : ℕ → Type*} [∀ n, Mul (B n)] [∀ n, Star (B n)]
    [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, MulHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    (ρ : ∀ n, F n) {σ : ∀ n, B n → ℂ} (hσ : ∀ n b, 0 ≤ σ n (star b * b))
    {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hpull : ∀ n x, σ n (ρ n x) = (c n : ℂ) * tr n x) :
    δ ∈ jonesLoopParameters := by
  by_contra hδJ
  exact (htr.lt_floor_of_pullback hδ hδJ (ρ ⌊π / arccos (δ / 2)⌋₊) (hσ _) (hc _) (hpull _)).ne rfl

end IsMarkovTrace

section Pullback

open scoped ComplexOrder

/-- **First bad level for a finite normalized Markov pullback.** Let `δ > 0` be an inadmissible
loop parameter. If star-algebra homomorphisms `ρ n hn : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B n`
(for `n ≤ N`) pull back normalized linear functionals `σ n hn` that are tracial on the image of
`ρ`, compatible with `strandIncl`, satisfy the Markov relation
`δ * σ (n + 2) (ρ (strandIncl x * e (Fin.last n))) = σ (n + 1) (ρ x)`, and `σ N le_rfl` is
positive, then `N < ⌊π / arccos (δ / 2)⌋`. Injectivity of `ρ` is not required. -/
theorem lt_floor_of_markov_pullback {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {N : ℕ} {B : ℕ → Type*}
    [∀ n, Semiring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, Star (B n)]
    (ρ : ∀ n, n ≤ N → TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B n)
    (σ : ∀ n, n ≤ N → B n →ₗ[ℂ] ℂ)
    (hpos : ∀ b : B N, 0 ≤ σ N le_rfl (star b * b))
    (h1 : ∀ n (hn : n ≤ N), σ n hn 1 = 1)
    (hcomm : ∀ n (hn : n ≤ N) (x y : TemperleyLieb ℂ (δ : ℂ) n),
      σ n hn (ρ n hn x * ρ n hn y) = σ n hn (ρ n hn y * ρ n hn x))
    (hincl : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      σ (n + 2) hn (ρ (n + 2) hn (strandIncl x)) =
        σ (n + 1) (by omega) (ρ (n + 1) (by omega) x))
    (hmarkov : ∀ n (hn : n + 2 ≤ N) (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      (δ : ℂ) * σ (n + 2) hn (ρ (n + 2) hn (strandIncl x * e (δ : ℂ) (Fin.last n))) =
        σ (n + 1) (by omega) (ρ (n + 1) (by omega) x)) :
    N < ⌊π / arccos (δ / 2)⌋₊ := by
  have htr : IsMarkovTraceUpTo ℂ (δ : ℂ) N
      fun n hn ↦ (δ : ℂ) ^ n • (σ n hn ∘ₗ (ρ n hn).toAlgHom.toLinearMap) :=
    isMarkovTraceUpTo_smul_pow
      (fun n hn ↦ by simp [h1 n hn])
      (fun n hn x y ↦ by simpa [map_mul] using hcomm n hn x y)
      (fun n hn x ↦ by simpa using hincl n hn x)
      (fun n hn x ↦ by simpa using hmarkov n hn x)
  exact htr.lt_floor_of_forall_nonneg hδ hδJ le_rfl fun x ↦ by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      StarAlgHom.coe_toAlgHom, smul_eq_mul, map_mul, map_star]
    exact mul_nonneg (by exact_mod_cast (pow_pos hδ N).le) (hpos (ρ N le_rfl x))

/-- **Normalized Markov pullback criterion for Jones's restriction.** Let `δ > 0`. If star-algebra
homomorphisms `ρ n : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B n` pull back normalized, positive linear
functionals `σ n` that are tracial on the image of `ρ`, compatible with `strandIncl`, and satisfy
the Markov relation `δ * σ (n + 2) (ρ (strandIncl x * e (Fin.last n))) = σ (n + 1) (ρ x)`, then
`δ` is an admissible loop parameter. Injectivity of `ρ` is not required. -/
theorem mem_jonesLoopParameters_of_markov_pullback {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
    (hδ : 0 < δ) {B : ℕ → Type*}
    [∀ n, Semiring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, Star (B n)]
    (ρ : ∀ n, TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B n)
    (σ : ∀ n, B n →ₗ[ℂ] ℂ)
    (hpos : ∀ n (b : B n), 0 ≤ σ n (star b * b))
    (h1 : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb ℂ (δ : ℂ) n),
      σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hincl : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      (δ : ℂ) * σ (n + 2) (ρ (n + 2) (strandIncl x * e (δ : ℂ) (Fin.last n))) =
        σ (n + 1) (ρ (n + 1) x)) :
    δ ∈ jonesLoopParameters := by
  by_contra hδJ
  exact (lt_floor_of_markov_pullback (N := ⌊π / arccos (δ / 2)⌋₊) hδ hδJ
    (fun n _ ↦ ρ n) (fun n _ ↦ σ n) (hpos _) (fun n _ ↦ h1 n)
    (fun n _ ↦ hcomm n) (fun n _ ↦ hincl n) (fun n _ ↦ hmarkov n)).ne rfl

end Pullback

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
strands exactly when `n < ⌊π / arccos (δ / 2)⌋`. -/
theorem markovTrace_nonneg_iff_lt_floor {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ markovTrace q hq (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

end TauCeti.TemperleyLieb
