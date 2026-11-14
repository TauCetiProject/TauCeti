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
import TauCeti.Algebra.TemperleyLieb.Sign
import TauCeti.Algebra.TemperleyLieb.SpinPositivity
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Jones's positivity theorem

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. This file proves both
directions, and transports the classification to negative loop values `δ < 0` via the sign
isomorphism `TauCeti.TemperleyLieb.signEquiv`.

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

Negative loop parameters: for `δ < 0`, the sign isomorphism `e δ i ↦ -e (-δ) i` commutes with the
analytic adjoint and multiplies the Markov trace on `n` strands by `(-1) ^ n`, so the signed
Hermitian forms `(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` are positive semidefinite at every level
exactly when `-δ ∈ jonesLoopParameters`. Equivalently, for every `δ ≠ 0`, the normalized forms
`(x, y) ↦ (δ ^ n)⁻¹ * tr n (x⋆ * y)` are positive semidefinite at every level exactly when
`|δ| ∈ jonesLoopParameters`.

The results are stated for an arbitrary Markov trace, so they apply to the spin-model trace
`TauCeti.TemperleyLieb.markovTrace` through `TauCeti.TemperleyLieb.isMarkovTrace_markovTrace`.
Over `ℂ` the analytic adjoint is the instance `TauCeti.TemperleyLieb.instStarRing`, whose
hypothesis `Fact (IsSelfAdjoint (δ : ℂ))` holds for every real `δ` by `Complex.conj_ofReal`.

## Main definitions

* `TauCeti.TemperleyLieb.jonesLoopParameters`: the admissible loop parameters
  `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`.

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
* `TauCeti.TemperleyLieb.IsMarkovTrace.lt_floor_of_forall_nonneg`: the form on `n` strands can
  only be positive semidefinite below level `⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_eq_two_mul_cos`: positivity
  at the loop values `2 cos (π / m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem** for `δ > 0`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: **positivity at negative loop
  parameters** (`δ < 0`).
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_inv_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_inv_pow_nonneg_iff`: **positivity of the normalized Markov
  trace** for `δ ≠ 0`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Lemma 4.3.8,
  Theorem 4.3.17, Facts 4.4.14 (TB6), and §4.5.
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

/-- Every admissible Jones loop parameter satisfies `1 ≤ δ`, with equality at `m = 3`
(`2 * cos (π / 3) = 1`). -/
theorem one_le_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 1 ≤ δ := by
  obtain ⟨m, hm, rfl⟩ | h2 := hδ
  · have hm0 : (0 : ℝ) < m := by positivity
    have hle : π / m ≤ π / 3 := by
      rw [div_le_div_iff_of_pos_left pi_pos hm0 (by norm_num)]
      exact_mod_cast hm
    have hcos := cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hle
    rw [cos_pi_div_three] at hcos
    linarith
  · linarith

/-- Every admissible Jones loop parameter is strictly positive. -/
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (hδ : δ ∈ jonesLoopParameters) : 0 < δ :=
  one_pos.trans_le (one_le_of_mem_jonesLoopParameters hδ)

/-- Zero is not an admissible Jones loop parameter. -/
@[simp]
theorem zero_notMem_jonesLoopParameters : (0 : ℝ) ∉ jonesLoopParameters :=
  fun h ↦ (pos_of_mem_jonesLoopParameters h).false

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
/-- At `δ = 2 cos (π / (k + 2))`, the quantum integers `[t + 1]` on the vertices `t` of the path
graph on `k + 1` vertices, the Dynkin graph `A_(k+1)`, form an eigenvector of its adjacency
matrix with eigenvalue `δ`: this is the recurrence `[t] + [t + 2] = δ [t + 1]`, with `[0] = 0` at
one end of the graph and `[k + 2] = 0` at the other. -/
private theorem sum_neighborFinset_pathGraph_qInt {k : ℕ} (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (u + 1) =
      2 * cos (π / (k + 2 : ℕ)) * qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (v + 1) := by
  set δ := 2 * cos (π / (k + 2 : ℕ))
  rw [neighborFinset_eq_filter, Finset.sum_filter]
  simp only [pathGraph_adj]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then qInt ℝ δ (j + 1) else 0)]
  have h (j : ℕ) : (if v.val + 1 = j ∨ j + 1 = v.val then qInt ℝ δ (j + 1) else 0) =
      (if v.val + 1 = j then qInt ℝ δ (j + 1) else 0) +
        (if j + 1 = v.val then qInt ℝ δ (j + 1) else 0) := by
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  -- The neighbour above `v` contributes `[v + 2]`, which vanishes when `v` is the top vertex.
  have h1 : (if v.val + 1 ∈ Finset.range (k + 1) then qInt ℝ δ (v + 1 + 1) else 0) =
      qInt ℝ δ (v + 2) := by
    split_ifs with hv
    · rfl
    · rw [show v.val + 2 = k + 2 by simp at hv; omega]
      exact (qInt_two_mul_cos_pi_div_eq_zero (by omega)).symm
  -- The neighbour below `v` contributes `[v]`, which vanishes when `v` is the bottom vertex.
  have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = v.val then qInt ℝ δ (j + 1) else 0) =
      qInt ℝ δ v := by
    obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  rw [h1, h2, qInt_add_two]
  ring

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

private theorem exists_map_star_mul_self_neg_of_eq {z : ℂ} [Fact (IsSelfAdjoint z)]
    {tr' : ∀ n : ℕ, TemperleyLieb ℂ z n →ₗ[ℂ] ℂ}
    (htr' : IsMarkovTrace ℂ z tr') {μ : ℝ} (hz : z = (μ : ℂ)) (hμ : 0 < μ)
    (hμJ : μ ∉ jonesLoopParameters) {n : ℕ} (hn : ⌊π / arccos (μ / 2)⌋₊ ≤ n) :
    ∃ y : TemperleyLieb ℂ z n, tr' n (star y * y) < 0 := by
  subst hz
  exact htr'.exists_map_star_mul_self_neg hμ hμJ hn

private theorem forall_map_star_mul_self_nonneg_iff_of_eq {z : ℂ} [Fact (IsSelfAdjoint z)]
    {tr' : ∀ n : ℕ, TemperleyLieb ℂ z n →ₗ[ℂ] ℂ}
    (htr' : IsMarkovTrace ℂ z tr') {μ : ℝ} (hz : z = (μ : ℂ)) (hμ : 0 < μ) :
    (∀ (n : ℕ) (y : TemperleyLieb ℂ z n), 0 ≤ tr' n (star y * y)) ↔
      μ ∈ jonesLoopParameters := by
  subst hz
  exact htr'.forall_map_star_mul_self_nonneg_iff hμ

/-- **Failure of signed positivity from level `k` on.** Let `δ < 0` with `-δ ∉ jonesLoopParameters`
and `k = ⌊π / arccos (-δ / 2)⌋`. On every number `n ≥ k` of strands the signed Hermitian form
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` takes a negative value. -/
theorem exists_neg_one_pow_mul_map_star_mul_self_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : ⌊π / arccos (-δ / 2)⌋₊ ≤ n) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, (-1 : ℂ) ^ n * tr n (star x * x) < 0 := by
  let : Fact (IsSelfAdjoint (-(δ : ℂ))) := ⟨(Fact.out : IsSelfAdjoint (δ : ℂ)).neg⟩
  obtain ⟨y, hy⟩ := exists_map_star_mul_self_neg_of_eq htr.signPushforward
    (Complex.ofReal_neg δ).symm (neg_pos.2 hδ) hδJ hn
  refine ⟨(signEquiv (δ : ℂ) n).symm y, ?_⟩
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
    signEquiv_symm_star, smul_eq_mul] using hy

/-- **Jones's restriction at negative loop parameters.** If `δ < 0` and the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number of
strands, then `-δ` is an admissible Jones loop parameter. -/
theorem mem_jonesLoopParameters_neg_of_forall_neg_one_pow_mul_nonneg
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0)
    (h : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
      0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    -δ ∈ jonesLoopParameters := by
  by_contra hδJ
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ le_rfl
  exact (h _ x).not_gt hx

/-- For `δ < 0` with `-δ ∉ jonesLoopParameters`, the signed Hermitian form of a Markov trace on
`n` strands can be positive semidefinite only below level `⌊π / arccos (-δ / 2)⌋`. -/
theorem lt_floor_of_forall_neg_one_pow_mul_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    n < ⌊π / arccos (-δ / 2)⌋₊ := by
  by_contra hn
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ (not_lt.1 hn)
  exact (h x).not_gt hx

/-- **Positivity at negative loop parameters.** For `δ < 0`, the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number of
strands exactly when `-δ` is an admissible loop parameter, `-δ = 2 cos (π / m)` for some `m ≥ 3`
or `-δ ≥ 2`. -/
theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters := by
  let : Fact (IsSelfAdjoint (-(δ : ℂ))) := ⟨(Fact.out : IsSelfAdjoint (δ : ℂ)).neg⟩
  rw [← forall_map_star_mul_self_nonneg_iff_of_eq htr.signPushforward
    (Complex.ofReal_neg δ).symm (neg_pos.2 hδ)]
  refine forall_congr' fun n ↦ ?_
  rw [← (signEquiv (δ : ℂ) n).toEquiv.forall_congr_right]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply,
    ← signEquiv_star, ← map_mul, smul_eq_mul]

/-- **Positivity of the normalized Markov trace.** For any nonzero real loop parameter `δ ≠ 0`,
the normalized Hermitian forms `(x, y) ↦ (δ ^ n)⁻¹ * tr n (x⋆ * y)` of a Markov trace are positive
semidefinite on every number of strands exactly when `|δ|` is an admissible loop parameter. -/
theorem forall_inv_pow_mul_map_star_mul_self_nonneg_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ≠ 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ ((δ : ℂ) ^ n)⁻¹ * tr n (star x * x)) ↔
      |δ| ∈ jonesLoopParameters := by
  have hreal {r : ℝ} (hr : 0 < r) {z : ℂ} : 0 ≤ (r : ℂ) * z ↔ 0 ≤ z := by
    rw [Complex.nonneg_iff, Complex.nonneg_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      mul_nonneg_iff_of_pos_left hr, eq_comm, mul_eq_zero_iff_left hr.ne', eq_comm]
  rcases hδ.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg, ← htr.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hneg]
    refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
    have hpow : ((δ : ℂ) ^ n)⁻¹ = ((((-δ) ^ n)⁻¹ : ℝ) : ℂ) * (-1 : ℂ) ^ n := by
      have hsplit : (δ : ℂ) = (-1 : ℂ) * ((-δ : ℝ) : ℂ) := by push_cast; ring
      rw [hsplit, mul_pow, mul_inv, ← inv_pow, inv_neg, inv_one, ← Complex.ofReal_pow,
        ← Complex.ofReal_inv, mul_comm]
    rw [hpow, mul_assoc]
    exact hreal (inv_pos.2 (pow_pos (neg_pos.2 hneg) n))
  · rw [abs_of_pos hpos, ← htr.forall_map_star_mul_self_nonneg_iff hpos]
    refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
    exact hreal (inv_pos.2 (pow_pos hpos n))

end IsMarkovTrace

section SpinMarkovTrace

open scoped ComplexOrder

/-- **Jones's positivity theorem** for the spin-model trace. Let `δ > 0` and let `q` be a unit with
`δ = -(q + q⁻¹)`. Then `TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` is real and nonnegative
for every number of strands and every `x` exactly when `δ` is an admissible loop parameter. -/
theorem markovTrace_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ markovTrace q hq (star x * x)) ↔
      δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff hδ

/-- **Positivity at negative loop parameters** for the spin-model trace. Let `δ < 0` and let `q`
be a unit with `δ = -(q + q⁻¹)`. Then the signed closure forms
`(-1) ^ n * TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` are real and nonnegative for every
number of strands `n` and every `x` exactly when `-δ` is an admissible loop parameter
(`-δ = 2 cos (π / m)` for some `m ≥ 3` or `-δ ≥ 2`). -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ < 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1 : ℂ) ^ n * markovTrace q hq (star x * x)) ↔
      -δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hδ

/-- **Positivity of the normalized spin-model trace.** For any nonzero real loop parameter `δ ≠ 0`
and unit `q` with `δ = -(q + q⁻¹)`, the normalized Hermitian forms
`(δ ^ n)⁻¹ * TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` are real and nonnegative at every
level `n` exactly when `|δ|` is an admissible loop parameter. -/
theorem markovTrace_inv_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ ≠ 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ ((δ : ℂ) ^ n)⁻¹ * markovTrace q hq (star x * x)) ↔
      |δ| ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_inv_pow_mul_map_star_mul_self_nonneg_iff hδ

end SpinMarkovTrace

end TauCeti.TemperleyLieb
