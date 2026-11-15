/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.PathModel.Positive
public import TauCeti.Algebra.TemperleyLieb.QuantumDimension
public import TauCeti.QuantumGroups.QuantumInteger.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Combinatorics.SimpleGraph.Hasse

import TauCeti.Algebra.TemperleyLieb.SpinPositivity
import TauCeti.Algebra.TemperleyLieb.Trace.Positive

/-!
# Jones's positivity theorem and the first bad level

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. At an inadmissible loop
parameter `0 < δ ∉ jonesLoopParameters`, write `δ = 2 cos θ` with `θ = arccos (δ / 2)` and put
`k = ⌊π / θ⌋₊`; this file also proves the sharp single-level refinement that `tr n` is positive
semidefinite if and only if `n < k`.

Necessity: when `0 < δ` is not admissible, `π / θ` is not an integer, so the quantum integers
`[1], …, [k]` are positive and `[k + 1]` is negative. Hence the Jones–Wenzl projection `f_k`
exists; it is a self-adjoint idempotent, so its norm `tr k (f_k⋆ * f_k) = tr k f_k = [k + 1]` is
negative. Adding `n - k` straight strands multiplies the trace by `δ ^ (n - k) > 0`, so the form on
`n` strands is indefinite for every `n ≥ k`.

Sufficiency and bounded-horizon positivity:
* For `δ ≥ 2`, all-level positivity holds both via the spin model of
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_two_le` and via the truncated
  half-line path model on `SimpleGraph.pathGraph (n + 1)` with weights `√[t + 1]`.
* For `δ = 2 cos (π / m)`, all-level positivity comes from the path model of
  `TauCeti.Algebra.TemperleyLieb.PathModel.Basic` on the Dynkin graph `A_(m-1)`
  (`pathGraph (m - 1)`) with vertex `t` weighted by `√[t + 1]`: `[1], …, [m - 1]` are positive,
  `[m] = 0`, and `[t] + [t + 2] = δ [t + 1]` gives a global adjacency eigenvector with eigenvalue
  `δ`.
* Whenever `[1], …, [n + 1]` are positive (in particular for `n < ⌊π / θ⌋₊` at an inadmissible
  `δ > 0`, or at any `n` for `δ ≥ 2`), walks of fewer than `n` steps from `0` in
  `pathGraph (n + 1)` never reach the boundary vertex `n`, so `√[t + 1]` satisfies
  `IsAdjEigenvectorUpTo` up to horizon `n`. Bounded-level Markov trace uniqueness then identifies
  `tr n` with `pathTrace`, proving positivity below level `k` and identifying `(tr n).traceRadical`
  with `RingHom.ker walkRep`.

Finally, pulling positive functionals back along star-preserving representations of the
Temperley–Lieb tower forces `δ ∈ jonesLoopParameters` without requiring injectivity of the
representations (`IsMarkovTrace.mem_jonesLoopParameters_of_pullback` and
`mem_jonesLoopParameters_of_tower_pullback`).

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
* `TauCeti.TemperleyLieb.isAdjEigenvectorUpTo_pathGraph_sqrt_qInt`: bounded-horizon adjacency
  eigenvector property of `√[t + 1]` on `SimpleGraph.pathGraph (n + 1)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_eq`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_neg`: negative-norm witnesses from
  level `⌊π / θ⌋₊` onward.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`: **the first bad level** at an
  inadmissible loop parameter `δ > 0`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_walkRep_pathGraph_of_qInt_pos`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_walkRep_pathGraph_of_two_le`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_walkRep_pathGraph_of_eq_two_mul_cos`:
  identification of the trace radical with `ker walkRep` on path graphs.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_pullback`,
  `TauCeti.TemperleyLieb.mem_jonesLoopParameters_of_tower_pullback`: **pullback criteria** for
  admissibility of `δ`.

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
/-- On `pathGraph (k + 1)`, the sum of `qInt ℝ δ (u + 1)` over the neighbours `u` of `v` is
`(if v.val < k then [v + 2] else 0) + [v]`. -/
private theorem sum_neighborFinset_pathGraph_qInt_eq (δ : ℝ) {k : ℕ} (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ δ (u + 1) =
      (if v.val < k then qInt ℝ δ (v + 2) else 0) + qInt ℝ δ v := by
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
  have h1 : (if v.val + 1 ∈ Finset.range (k + 1) then qInt ℝ δ (v + 1 + 1) else 0) =
      if v.val < k then qInt ℝ δ (v + 2) else 0 := by
    split_ifs <;> first | rfl | simp_all
  have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = v.val then qInt ℝ δ (j + 1) else 0) =
      qInt ℝ δ v := by
    obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  rw [h1, h2]

open SimpleGraph in
/-- At every non-top vertex `v` (`v.val < k`) of `pathGraph (k + 1)`, the quantum integers
`[t + 1]` satisfy the adjacency recurrence `∑_{u ~ v} [u + 1] = δ [v + 1]` for any `δ : ℝ`. -/
theorem sum_neighborFinset_pathGraph_qInt_of_lt {k : ℕ} {v : Fin (k + 1)} (hv : v.val < k) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ δ (u + 1) = δ * qInt ℝ δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, ite_eq_left hv, qInt_add_two]
  ring

open SimpleGraph in
/-- When `[k + 2] = 0`, the quantum integers `[t + 1]` on all vertices of `pathGraph (k + 1)`
form an eigenvector of its adjacency matrix with eigenvalue `δ`. -/
theorem sum_neighborFinset_pathGraph_qInt_of_eq_zero {k : ℕ} (hz : qInt ℝ δ (k + 2) = 0)
    (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ δ (u + 1) = δ * qInt ℝ δ (v + 1) := by
  by_cases hv : v.val < k
  · exact sum_neighborFinset_pathGraph_qInt_of_lt hv
  · have hvk : v.val + 2 = k + 2 := by omega
    rw [sum_neighborFinset_pathGraph_qInt_eq, ite_eq_right hv, zero_add,
      ← add_zero (qInt ℝ δ v), ← hz, ← hvk, qInt_add_two]
    ring

open SimpleGraph in
/-- At `δ = 2 cos (π / (k + 2))`, the quantum integers `[t + 1]` on the vertices `t` of the path
graph on `k + 1` vertices, the Dynkin graph `A_(k+1)`, form an eigenvector of its adjacency
matrix with eigenvalue `δ`: this is the recurrence `[t] + [t + 2] = δ [t + 1]`, with `[0] = 0` at
one end of the graph and `[k + 2] = 0` at the other. -/
theorem sum_neighborFinset_pathGraph_qInt {k : ℕ} (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (u + 1) =
      2 * cos (π / (k + 2 : ℕ)) * qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (v + 1) :=
  sum_neighborFinset_pathGraph_qInt_of_eq_zero (qInt_two_mul_cos_pi_div_eq_zero (by omega)) v

/-- When `[1], …, [k + 1]` are strictly positive, the complex square-root weights `√[t + 1]` on
`Fin (k + 1)` are nonzero. -/
theorem ofReal_sqrt_qInt_ne_zero {k : ℕ} (hq : ∀ j ∈ Finset.Icc 1 (k + 1), 0 < qInt ℝ δ j)
    (t : Fin (k + 1)) : (((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)) ≠ 0 :=
  Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (hq (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))).ne'

/-- When `[1], …, [n + 1]` are nonnegative, the weights `t ↦ √[t + 1]` on
`SimpleGraph.pathGraph (n + 1)` satisfy `IsAdjEigenvectorUpTo` from base vertex `0` up to horizon
`n`: a walk of fewer than `n` steps from `0` never reaches the top vertex `n`. -/
theorem isAdjEigenvectorUpTo_pathGraph_sqrt_qInt {n : ℕ}
    (hq : ∀ j ∈ Finset.Icc 1 (n + 1), 0 ≤ qInt ℝ δ j) :
    IsAdjEigenvectorUpTo (SimpleGraph.pathGraph (n + 1)) 0
      (fun t : Fin (n + 1) ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)) (δ : ℂ) n := by
  rw [isAdjEigenvectorUpTo_iff]
  intro k hk s hs
  have hle : (s (Fin.last k)).val ≤ (0 : Fin (n + 1)).val + (Fin.last k).val :=
    hs.apply_le_add Fin.val (fun _ _ h ↦ by rw [SimpleGraph.pathGraph_adj] at h; omega)
      (Fin.last k)
  have hlt : (s (Fin.last k)).val < n := by
    simp only [Fin.val_zero, zero_add, Fin.val_last] at hle
    omega
  have hsq (t : Fin (n + 1)) :
      (((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)) ^ 2 = (qInt ℝ δ (t + 1) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (hq (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))]
  simp only [hsq]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_lt hlt

/-- At `δ = 2 cos (π / (k + 2))`, the weights `t ↦ √[t + 1]` on `SimpleGraph.pathGraph (k + 1)`
satisfy `IsAdjEigenvectorUpTo` at every horizon `n`. -/
theorem isAdjEigenvectorUpTo_pathGraph_of_eq_two_mul_cos {k : ℕ}
    (hδ : δ = 2 * cos (π / (k + 2 : ℕ))) (n : ℕ) :
    IsAdjEigenvectorUpTo (SimpleGraph.pathGraph (k + 1)) 0
      (fun t : Fin (k + 1) ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ)) (δ : ℂ) n := by
  refine IsAdjEigenvectorUpTo.of_forall (fun v ↦ ?_) n
  subst hδ
  have hsq (t : Fin (k + 1)) :
      (((√(qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1)) : ℝ) : ℂ)) ^ 2 =
        (qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (t + 1) : ℂ) := by
    rw [← Complex.ofReal_pow,
      Real.sq_sqrt (qInt_two_mul_cos_pi_div_pos (by omega) (by omega)).le]
  simp only [hsq]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt v

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
    have hsub : m + 1 + 1 - k = m + 1 - k + 1 := by omega
    rw [← strandIncl_star, ← map_mul, htr.map_strandIncl, hx, hsub, pow_succ]
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

/-- **Single-level positivity from positive quantum integers.** Whenever `[1], …, [n + 1]` are
strictly positive at `δ`, the Hermitian form of any Markov trace on `n` strands is positive
semidefinite, realized by the truncated half-line path model on `SimpleGraph.pathGraph (n + 1)`
with vertex weights `√[t + 1]`. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hq : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_isAdjEigenvectorUpTo
    (ofReal_sqrt_qInt_ne_zero hq) (fun _ ↦ Complex.conj_ofReal _)
    (isAdjEigenvectorUpTo_pathGraph_sqrt_qInt fun j hj ↦ (hq j hj).le) x

/-- Whenever `[1], …, [n + 1]` are strictly positive at `δ`, the trace radical `(tr n).traceRadical`
equals the kernel of `walkRep` on `SimpleGraph.pathGraph (n + 1)` with weights `√[t + 1]`. -/
theorem traceRadical_eq_ker_walkRep_pathGraph_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    {n : ℕ} (hq : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j) :
    (tr n).traceRadical (htr.map_mul_comm n) =
      RingHom.ker (walkRep (SimpleGraph.pathGraph (n + 1)) 0 (ofReal_sqrt_qInt_ne_zero hq)
        (isAdjEigenvectorUpTo_pathGraph_sqrt_qInt fun j hj ↦ (hq j hj).le)) :=
  htr.traceRadical_eq_ker_walkRep (ofReal_sqrt_qInt_ne_zero hq)
    (fun _ ↦ Complex.conj_ofReal _)
    (isAdjEigenvectorUpTo_pathGraph_sqrt_qInt fun j hj ↦ (hq j hj).le)

/-- For `δ ≥ 2`, the trace radical `(tr n).traceRadical` equals the kernel of `walkRep` on the
truncated half-line `SimpleGraph.pathGraph (n + 1)` with weights `√[t + 1]`. -/
theorem traceRadical_eq_ker_walkRep_pathGraph_of_two_le (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 2 ≤ δ) (n : ℕ) :
    (tr n).traceRadical (htr.map_mul_comm n) =
      RingHom.ker (walkRep (SimpleGraph.pathGraph (n + 1)) 0
        (ofReal_sqrt_qInt_ne_zero fun _ hj ↦ qInt_pos_of_two_le hδ (Finset.mem_Icc.1 hj).1)
        (isAdjEigenvectorUpTo_pathGraph_sqrt_qInt fun _ hj ↦
          (qInt_pos_of_two_le hδ (Finset.mem_Icc.1 hj).1).le)) :=
  htr.traceRadical_eq_ker_walkRep_pathGraph_of_qInt_pos
    fun _ hj ↦ qInt_pos_of_two_le hδ (Finset.mem_Icc.1 hj).1

/-- At the discrete loop parameter `δ = 2 cos (π / (k + 2))`, the trace radical
`(tr n).traceRadical` on any number `n` of strands equals the kernel of `walkRep` on the Dynkin
graph `A_(k+1)` (`SimpleGraph.pathGraph (k + 1)`) with weights `√[t + 1]`. -/
theorem traceRadical_eq_ker_walkRep_pathGraph_of_eq_two_mul_cos (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    {k : ℕ} (hδ : δ = 2 * cos (π / (k + 2 : ℕ))) (n : ℕ) :
    (tr n).traceRadical (htr.map_mul_comm n) =
      RingHom.ker (walkRep (SimpleGraph.pathGraph (k + 1)) 0
        (ofReal_sqrt_qInt_ne_zero fun j hj ↦ by
          obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.1 hj
          exact hδ ▸ qInt_two_mul_cos_pi_div_pos hj₁ (by omega))
        (isAdjEigenvectorUpTo_pathGraph_of_eq_two_mul_cos hδ n)) :=
  htr.traceRadical_eq_ker_walkRep _ (fun _ ↦ Complex.conj_ofReal _)
    (isAdjEigenvectorUpTo_pathGraph_of_eq_two_mul_cos hδ n)

/-- **Positivity below the first bad level.** At an inadmissible loop parameter `δ > 0`, the
Hermitian form of a Markov trace on `n` strands is positive semidefinite for every
`n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_qInt_pos
    (fun _ hj ↦ qInt_pos_of_notMem_jonesLoopParameters hδ hδJ (Finset.mem_Icc.1 hj).1
      ((Finset.mem_Icc.1 hj).2.trans hn)) x

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

/-- **The first bad level** for an arbitrary Markov trace. At an inadmissible loop parameter
`δ > 0`, the Hermitian form `(x, y) ↦ tr n (x⋆ * y)` on `n` strands is positive semidefinite
if and only if `n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  ⟨htr.lt_floor_of_forall_nonneg hδ hδJ, htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ⟩

/-- **Single-level positivity criterion.** For any `δ > 0` and any strand count `n`, the Hermitian
form of a Markov trace on `n` strands is positive semidefinite if and only if either `δ` is
admissible or `n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem forall_map_star_mul_self_nonneg_iff_mem_or_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      δ ∈ jonesLoopParameters ∨ n < ⌊π / arccos (δ / 2)⌋₊ := by
  by_cases hδJ : δ ∈ jonesLoopParameters
  · exact ⟨fun _ ↦ Or.inl hδJ, fun _ ↦ (htr.forall_map_star_mul_self_nonneg_iff hδ).2 hδJ n⟩
  · simpa [hδJ] using htr.forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

/-- For `δ > 0`, whenever `δ` is admissible or `n < ⌊π / arccos (δ / 2)⌋₊`, the null vectors of
`x ↦ tr n (star x * x)` are precisely the two-sided trace radical `(tr n).traceRadical`. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_of_mem_or_lt_floor
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) {n : ℕ}
    (h : δ ∈ jonesLoopParameters ∨ n < ⌊π / arccos (δ / 2)⌋₊)
    {x : TemperleyLieb ℂ (δ : ℂ) n} :
    tr n (star x * x) = 0 ↔ x ∈ (tr n).traceRadical (htr.map_mul_comm n) :=
  htr.map_star_mul_self_eq_zero_iff_mem_traceRadical
    ((htr.forall_map_star_mul_self_nonneg_iff_mem_or_lt_floor hδ).2 h)

/-- **Pullback criterion for admissibility.** Let `δ > 0` and suppose that at each strand count `n`
there is a star-preserving algebra homomorphism `ρ n : TemperleyLieb ℂ (δ : ℂ) n →ₐ[ℂ] B n` into a
complex star algebra carrying a positive functional `σ n` such that
`σ n (ρ n x) = ((δ : ℂ)⁻¹) ^ n * tr n x`. Then `δ ∈ jonesLoopParameters`; injectivity of `ρ n` is
not required. -/
theorem mem_jonesLoopParameters_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    {B : ℕ → Type*} [∀ n, Ring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, StarRing (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n))
    (ρ : ∀ n, TemperleyLieb ℂ (δ : ℂ) n →ₐ[ℂ] B n)
    (hρ : ∀ n x, ρ n (star x) = star (ρ n x))
    (hpull : ∀ n x, σ n (ρ n x) = ((δ : ℂ)⁻¹) ^ n * tr n x) :
    δ ∈ jonesLoopParameters := by
  refine htr.mem_jonesLoopParameters_of_forall_nonneg hδ fun n x ↦ ?_
  have hσ : 0 ≤ ((δ : ℂ)⁻¹) ^ n * tr n (star x * x) := by
    rw [← hpull, map_mul, hρ]
    exact (σ n).square_nonneg (ρ n x)
  have hd_pos : 0 ≤ ((δ : ℂ) ^ n) := by exact_mod_cast pow_nonneg hδ.le n
  have hd_ne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  have hmul := mul_nonneg hd_pos hσ
  rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hd_ne, one_pow, one_mul] at hmul

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
/-- **The first bad level** for the spin-model trace. Let `0 < δ ∉ jonesLoopParameters` and let `q`
be a unit with `δ = -(q + q⁻¹)`. Then `TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` is real and
nonnegative for every `x : TemperleyLieb ℂ (δ : ℂ) n` if and only if
`n < ⌊π / arccos (δ / 2)⌋₊`. -/
theorem markovTrace_nonneg_iff_lt_floor {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) (n : ℕ) :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ markovTrace q hq (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

/-- **Tower pullback criterion for admissibility.** Let `δ > 0` and suppose `ρ n` are
star-preserving algebra homomorphisms from `TemperleyLieb ℂ (δ : ℂ) n` into complex star algebras
`B n` carrying normalized positive functionals `σ n` that are tracial on the image of `ρ n`,
compatible with `strandIncl`, and satisfy the normalized Markov relation with factor `(δ : ℂ)⁻¹`.
Then `δ ∈ jonesLoopParameters`. -/
theorem mem_jonesLoopParameters_of_tower_pullback {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
    (hδ : 0 < δ) {B : ℕ → Type*} [∀ n, Ring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, StarRing (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n))
    (ρ : ∀ n, TemperleyLieb ℂ (δ : ℂ) n →ₐ[ℂ] B n)
    (hρ : ∀ n x, ρ n (star x) = star (ρ n x))
    (hone : ∀ n, n ≤ 1 → σ n 1 = 1)
    (hmul : ∀ n (x y : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hstrand : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x * e (δ : ℂ) (Fin.last n))) =
        (δ : ℂ)⁻¹ * σ (n + 1) (ρ (n + 1) x)) :
    δ ∈ jonesLoopParameters := by
  have hd_ne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  have htr := isMarkovTrace_of_pullback ρ (fun n ↦ (σ n).toLinearMap) (mul_inv_cancel₀ hd_ne)
    hone hmul hstrand hmarkov
  exact htr.mem_jonesLoopParameters_of_pullback hδ σ ρ hρ
    (htr.pullback_eq ρ (fun n ↦ (σ n).toLinearMap) (mul_inv_cancel₀ hd_ne)
      hone hmul hstrand hmarkov)

end TauCeti.TemperleyLieb
