/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.QuantumDimension
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.QuantumGroups.QuantumInteger.Real
public import TauCeti.RingTheory.TraceFunctional.Positive
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

import TauCeti.Algebra.TemperleyLieb.PathModel
import TauCeti.Algebra.TemperleyLieb.SpinPositivity
import TauCeti.Analysis.StarAlgebra.CauchySchwarz
import TauCeti.Combinatorics.SimpleGraph.PathGraph

/-!
# Jones's positivity theorem and the first bad level

For a real loop value `δ`, the analytic adjoint and a Markov trace `tr` give the Hermitian forms
`(x, y) ↦ tr n (x⋆ * y)` on the Temperley–Lieb algebras. Jones's positivity theorem says that for
`δ > 0` all of these forms are positive semidefinite exactly when `δ` lies in
`{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`, the set `TauCeti.TemperleyLieb.jonesLoopParameters`; its
squares are the Jones index values `4 cos² (π / m)` and `[4, ∞)`. At an inadmissible positive loop
value `δ`, write `δ = 2 cos θ` with `θ = arccos (δ / 2)` and put `k = ⌊π / θ⌋`: then the form on
`n` strands is positive semidefinite if and only if `n < k`. This file proves both theorems and
their immediate consequences for the trace radical and for representations with positive traces.

Necessity: when `0 < δ` is not admissible, `π / θ` is not an integer, so the quantum integers
`[1], …, [k]` are positive and `[k + 1]` is negative. Hence the Jones–Wenzl projection `f_k`
exists; it is a self-adjoint idempotent, so its norm `tr k (f_k⋆ * f_k) = tr k f_k = [k + 1]` is
negative. Adding `n - k` straight strands multiplies the trace by `δ ^ (n - k) > 0`, so the form
on `n` strands is indefinite for every `n ≥ k`.

Sufficiency and levels below `k`: for `δ ≥ 2` positivity at every level is given by the spin model
of `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_two_le`, and for
`δ = 2 cos (π / m)` by the path model of `TauCeti.Algebra.TemperleyLieb.PathModel` on the Dynkin
graph `A_(m-1)` with weights `√[t + 1]`. Below the first bad level (`n < k`), the quantum integers
`[1], …, [n + 1]` are all positive; on the truncated path graph `pathGraph (n + 1)` with base
vertex `0`, walks of length `n` only invoke the eigenvector equation `[t] + [t + 2] = δ [t + 1]` at
vertices `t < n`, where it holds identically, and bounded Markov uniqueness up to `n` strands
identifies the path-model trace with `tr n`.

Whenever the form at level `n` is positive semidefinite (at admissible `δ` for all `n`, or at
inadmissible `δ > 0` for `n < k`), `tr n` bundles into a `TauCeti.StarPositiveFunctional`: Cauchy–
Schwarz holds, and the zero set `{x | tr n (x⋆ * x) = 0}` coincides with the trace radical.
Conversely, pulling `((δ : ℂ) ^ n)⁻¹ * tr n` back along star-multiplicative maps from positive
functionals forces `δ ∈ jonesLoopParameters` without any injectivity assumption.

The results are stated for an arbitrary Markov trace, so they apply to the spin-model trace
`TauCeti.TemperleyLieb.markovTrace` through `TauCeti.TemperleyLieb.isMarkovTrace_markovTrace`.
Over `ℂ` the analytic adjoint is the instance `TauCeti.TemperleyLieb.instStarRing`, whose
hypothesis `Fact (IsSelfAdjoint (δ : ℂ))` holds for every real `δ` by `Complex.conj_ofReal`.

## Main definitions

* `TauCeti.TemperleyLieb.jonesLoopParameters`: the admissible loop parameters
  `{2 cos (π / m) : m ≥ 3} ∪ [2, ∞)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctional`: `tr n` bundled as a
  `TauCeti.StarPositiveFunctional` at an admissible loop parameter.

## Main results

* `TauCeti.TemperleyLieb.pos_of_mem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.floor_pi_div_arccos_eq_of_Ioo`,
  `TauCeti.TemperleyLieb.notMem_jonesLoopParameters_of_Ioo`: positivity of admissible parameters
  and location of the first bad level on each open interval `(2 cos (π / k), 2 cos (π / (k + 1)))`.
* `TauCeti.TemperleyLieb.qInt_pos_of_notMem_jonesLoopParameters`,
  `TauCeti.TemperleyLieb.qInt_floor_add_one_neg_of_notMem_jonesLoopParameters`: the signs of the
  quantum integers at an inadmissible positive loop parameter.
* `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_eq`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.exists_map_star_mul_self_neg`: negative-norm elements at and
  above the first bad level `⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_qInt_pos`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_lt_floor`: positivity on `n`
  strands when `[1], …, [n + 1]` are positive, and in particular below `⌊π / θ⌋`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff`: **Jones's positivity theorem**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_map_star_mul_self_nonneg_iff_lt_floor`,
  `TauCeti.TemperleyLieb.markovTrace_nonneg_iff_lt_floor`: **the first bad level**.
* `TauCeti.TemperleyLieb.IsMarkovTrace.norm_map_star_mul_sq_le`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.mem_traceRadical_iff_map_star_mul_self_eq_zero`: Cauchy–
  Schwarz and the quadratic characterization of the trace radical.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_pullback`: **pullback criterion**
  for admissibility.

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

/-- Every admissible loop parameter is at least `1`, the value at `m = 3`. -/
theorem one_le_of_mem_jonesLoopParameters {δ : ℝ} (h : δ ∈ jonesLoopParameters) : 1 ≤ δ := by
  obtain ⟨m, hm, rfl⟩ | h2 := h
  · have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hle : π / m ≤ π / 3 := div_le_div_of_nonneg_left pi_pos.le (by positivity) hm'
    have hc := cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hle
    rw [cos_pi_div_three] at hc
    linarith
  · linarith

/-- Every admissible loop parameter is strictly positive. -/
theorem pos_of_mem_jonesLoopParameters {δ : ℝ} (h : δ ∈ jonesLoopParameters) : 0 < δ :=
  lt_of_lt_of_le zero_lt_one (one_le_of_mem_jonesLoopParameters h)

/-- No nonpositive real number is an admissible loop parameter. -/
theorem notMem_jonesLoopParameters_of_nonpos {δ : ℝ} (h : δ ≤ 0) : δ ∉ jonesLoopParameters :=
  fun hJ ↦ (pos_of_mem_jonesLoopParameters hJ).not_ge h

/-- An inadmissible loop parameter is strictly less than `2`. -/
theorem lt_two_of_notMem_jonesLoopParameters {δ : ℝ} (h : δ ∉ jonesLoopParameters) : δ < 2 :=
  lt_of_not_ge fun h2 ↦ h (Or.inr h2)

section QuantumInteger

variable {δ : ℝ}

/-- When `δ` lies strictly between `2 cos (π / k)` and `2 cos (π / (k + 1))` with `k ≥ 1`, the
ratio `π / arccos (δ / 2)` lies strictly between `k` and `k + 1`. -/
private theorem pi_div_arccos_mem_Ioo {k : ℕ} (hk : 1 ≤ k) (hlo : 2 * cos (π / k) < δ)
    (hhi : δ < 2 * cos (π / (k + 1 : ℕ))) :
    (k : ℝ) < π / arccos (δ / 2) ∧ π / arccos (δ / 2) < (k + 1 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hπk : π / k ≤ π := div_le_self pi_pos.le (by exact_mod_cast hk)
  have hπk1 : π / (k + 1 : ℕ) ≤ π :=
    div_le_self pi_pos.le (by exact_mod_cast Nat.le_add_right_of_le hk)
  have harc_hi : arccos (δ / 2) < π / k := by
    rw [← arccos_cos (by positivity) hπk]
    exact arccos_lt_arccos (neg_one_le_cos _) (by linarith)
      ((by linarith : δ / 2 < cos (π / (k + 1 : ℕ))).le.trans (cos_le_one _))
  have harc_lo : π / (k + 1 : ℕ) < arccos (δ / 2) := by
    rw [← arccos_cos (by positivity) hπk1]
    exact arccos_lt_arccos ((neg_one_le_cos _).trans (by linarith : cos (π / k) < δ / 2).le)
      (by linarith) (cos_le_one _)
  have harc_pos : 0 < arccos (δ / 2) := lt_trans (div_pos pi_pos hk1) harc_lo
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ harc_pos]
    linarith [(lt_div_iff₀ hk0).1 harc_hi]
  · rw [div_lt_iff₀ harc_pos]
    have harc_lo' := (div_lt_iff₀ hk1).1 harc_lo
    push_cast at harc_lo'
    linarith

/-- On the open interval `(2 cos (π / k), 2 cos (π / (k + 1)))` (`k ≥ 1`), the floor
`⌊π / arccos (δ / 2)⌋` is constantly `k`. -/
theorem floor_pi_div_arccos_eq_of_Ioo {k : ℕ} (hk : 1 ≤ k) (hlo : 2 * cos (π / k) < δ)
    (hhi : δ < 2 * cos (π / (k + 1 : ℕ))) :
    ⌊π / arccos (δ / 2)⌋₊ = k := by
  obtain ⟨h1, h2⟩ := pi_div_arccos_mem_Ioo hk hlo hhi
  exact Nat.floor_eq_iff ((Nat.cast_nonneg k).trans h1.le) |>.2 ⟨h1.le, h2⟩

/-- No point strictly between `2 cos (π / k)` and `2 cos (π / (k + 1))` (`k ≥ 1`) is an admissible
loop parameter. -/
theorem notMem_jonesLoopParameters_of_Ioo {k : ℕ} (hk : 1 ≤ k) (hlo : 2 * cos (π / k) < δ)
    (hhi : δ < 2 * cos (π / (k + 1 : ℕ))) :
    δ ∉ jonesLoopParameters := by
  obtain ⟨h1, h2⟩ := pi_div_arccos_mem_Ioo hk hlo hhi
  rintro (⟨m, hm, rfl⟩ | h2le)
  · have hm0 : (0 : ℝ) < m := by positivity
    have hπm : π / m ≤ π := div_le_self pi_pos.le (by exact_mod_cast (by omega : 1 ≤ m))
    have harc : π / arccos (2 * cos (π / m) / 2) = m := by
      rw [mul_div_cancel_left₀ _ two_ne_zero, arccos_cos (by positivity) hπm,
        div_div_cancel₀ pi_ne_zero]
    rw [harc] at h1 h2
    have hkm : k < m := by exact_mod_cast h1
    have hmk : m < k + 1 := by exact_mod_cast h2
    omega
  · linarith [cos_le_one (π / (k + 1 : ℕ))]

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
/-- On `pathGraph (N + 1)`, the sum of the quantum integers `[u + 1]` over the neighbours `u` of
`v` equals `δ * [v + 1]` at every vertex `v < N`, and equals `[N]` at the top vertex `v = N`:
this is the recurrence `[v] + [v + 2] = δ [v + 1]`, with `[0] = 0` at `v = 0`. -/
private theorem sum_neighborFinset_pathGraph_qInt_aux {R : Type*} [CommRing R] (δ : R) {N : ℕ}
    (v : Fin (N + 1)) :
    ∑ u ∈ (pathGraph (N + 1)).neighborFinset v, qInt R δ (u + 1) =
      (if v.val < N then qInt R δ (v + 2) else 0) + qInt R δ v := by
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
  · simp only [Finset.mem_range]
    split_ifs <;> first | rfl | omega
  · obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]

open SimpleGraph in
/-- At every vertex `v < N` of `pathGraph (N + 1)`, the quantum integers `[t + 1]` satisfy the
adjacency-eigenvector equation with eigenvalue `δ`, over any commutative ring. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_lt {R : Type*} [CommRing R] (δ : R) {N : ℕ}
    {v : Fin (N + 1)} (hv : v.val < N) :
    ∑ u ∈ (pathGraph (N + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_aux, ite_eq_left hv, qInt_add_two]
  ring

open SimpleGraph in
/-- When `[k + 2] = 0`, the quantum integers `[t + 1]` on `pathGraph (k + 1)` form a global
eigenvector of its adjacency matrix with eigenvalue `δ`. -/
private theorem sum_neighborFinset_pathGraph_qInt_of_eq_zero {R : Type*} [CommRing R] {δ : R}
    {k : ℕ} (hzero : qInt R δ (k + 2) = 0) (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  by_cases hv : v.val < k
  · exact sum_neighborFinset_pathGraph_qInt_of_lt δ hv
  · have hvk : v.val = k := by omega
    rw [sum_neighborFinset_pathGraph_qInt_aux, ite_eq_right hv, zero_add]
    have hrec := qInt_add_two (R := R) δ k
    rw [hzero] at hrec
    rw [hvk]
    linear_combination hrec

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

/-- **Positivity at level `n` from positive quantum integers.** For any real `δ`, if the quantum
integers `[1], …, [n + 1]` are positive, then the Hermitian form of a Markov trace on `n` strands
is positive semidefinite: it agrees with the trace of the path model on `pathGraph (n + 1)` with
base vertex `0` and weights `√[t + 1]`, where `n`-step walks only invoke the eigenvector equation
at vertices `t < n`. -/
theorem map_star_mul_self_nonneg_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hpos : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) := by
  have hpos_fin (t : Fin (n + 1)) : 0 < qInt ℝ δ (t + 1) :=
    hpos (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  refine htr.map_star_mul_self_nonneg_of_edist_lt (G := SimpleGraph.pathGraph (n + 1)) (v₀ := 0)
    (r := fun t ↦ ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ))
    (fun t _ ↦ Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos_fin t)).ne')
    (fun t _ ↦ Complex.conj_ofReal _) (fun v hv ↦ ?_) x
  have hvn : v.val < n := by simpa using hv
  simp only [← Complex.ofReal_pow, Real.sq_sqrt (hpos_fin _).le]
  exact_mod_cast sum_neighborFinset_pathGraph_qInt_of_lt δ hvn

/-- **Positivity below the first bad level.** At an inadmissible positive loop parameter `δ`, the
Hermitian form of a Markov trace on `n` strands is positive semidefinite for every
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem map_star_mul_self_nonneg_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x : TemperleyLieb ℂ (δ : ℂ) n) : 0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_qInt_pos (fun j hj ↦ by
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hj
    exact qInt_pos_of_notMem_jonesLoopParameters hδ hδJ hj1 (by omega)) x

/-- **The first bad level** for an abstract Markov trace. At an inadmissible loop parameter `δ > 0`,
the Hermitian form `(x, y) ↦ tr n (x⋆ * y)` on `n` strands is positive semidefinite if and only if
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem forall_map_star_mul_self_nonneg_iff_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  ⟨htr.lt_floor_of_forall_nonneg hδ hδJ, htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ⟩

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

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Hermitian forms of a Markov
trace are positive semidefinite on every number of strands. -/
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

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Markov trace on `n` strands
bundled as a `TauCeti.StarPositiveFunctional`. -/
def starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters)
    (n : ℕ) : StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg := htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδ

/-- Evaluating `htr.starPositiveFunctional` computes the Markov trace `tr n`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctional hδ n x = tr n x :=
  (rfl)

/-- Forgetting positivity from `htr.starPositiveFunctional` recovers the linear form `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.starPositiveFunctional hδ n).toLinearMap = tr n :=
  (rfl)

/-- **Cauchy–Schwarz inequality** for the Hermitian form of a Markov trace at an admissible loop
parameter. -/
theorem norm_map_star_mul_sq_le (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖tr n (star x * y)‖ ^ 2 ≤ ‖tr n (star x * x)‖ * ‖tr n (star y * y)‖ :=
  (tr n).norm_map_star_mul_sq_le
    (htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hδ) x y

/-- **Cauchy–Schwarz inequality** for the Hermitian form of a Markov trace below the first bad
level. -/
theorem norm_map_star_mul_sq_le_of_lt_floor (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) {n : ℕ} (hn : n < ⌊π / arccos (δ / 2)⌋₊)
    (x y : TemperleyLieb ℂ (δ : ℂ) n) :
    ‖tr n (star x * y)‖ ^ 2 ≤ ‖tr n (star x * x)‖ * ‖tr n (star y * y)‖ :=
  (tr n).norm_map_star_mul_sq_le (htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ hn) x y

/-- At an admissible loop parameter, the trace radical on `n` strands is precisely the null space
`{x | tr n (x⋆ * x) = 0}` of the Hermitian form. -/
theorem mem_traceRadical_iff_map_star_mul_self_eq_zero (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) {n : ℕ} (x : TemperleyLieb ℂ (δ : ℂ) n) :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ tr n (star x * x) = 0 :=
  (htr.starPositiveFunctional hδ n).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n) x

/-- Below the first bad level at an inadmissible positive loop parameter, the trace radical on `n`
strands is precisely the null space `{x | tr n (x⋆ * x) = 0}` of the Hermitian form. -/
theorem mem_traceRadical_iff_map_star_mul_self_eq_zero_of_lt_floor
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ) (hδJ : δ ∉ jonesLoopParameters) {n : ℕ}
    (hn : n < ⌊π / arccos (δ / 2)⌋₊) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔ tr n (star x * x) = 0 :=
  StarPositiveFunctional.mem_traceRadical_iff_apply_star_mul_self_eq_zero
    ⟨tr n, htr.map_star_mul_self_nonneg_of_lt_floor hδ hδJ hn⟩ (htr.map_mul_comm n) x

/-- **Pullback criterion for admissibility.** Let `δ > 0` and let `ρ n` be star-multiplicative
maps from `TemperleyLieb ℂ (δ : ℂ) n` into star-equipped multiplicative types `B n` carrying
maps `σ n : B n → ℂ` nonnegative on squares `b⋆ * b` such that
`σ n (ρ n x) = ((δ : ℂ) ^ n)⁻¹ * tr n x` for every `n` and `x`. Then `δ` is an admissible loop
parameter. Injectivity of `ρ n` is not required. -/
theorem mem_jonesLoopParameters_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    {B : ℕ → Type*} {F : ℕ → Type*} [∀ n, Mul (B n)] [∀ n, Star (B n)]
    [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, MulHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    (ρ : ∀ n, F n) (σ : ∀ n, B n → ℂ)
    (hσ : ∀ n (b : B n), 0 ≤ σ n (star b * b))
    (hpull : ∀ n x, σ n (ρ n x) = ((δ : ℂ) ^ n)⁻¹ * tr n x) :
    δ ∈ jonesLoopParameters := by
  refine htr.mem_jonesLoopParameters_of_forall_nonneg hδ fun n x ↦ ?_
  have hsq : 0 ≤ σ n (ρ n (star x * x)) := by
    rw [map_mul, StarHomClass.map_star]
    exact hσ n (ρ n x)
  have heq : tr n (star x * x) = ((δ ^ n : ℝ) : ℂ) * σ n (ρ n (star x * x)) := by
    rw [hpull, Complex.ofReal_pow, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n (Complex.ofReal_ne_zero.2 hδ.ne')), one_mul]
  rw [heq]
  exact mul_nonneg (by exact_mod_cast pow_nonneg hδ.le n) hsq

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
is real and nonnegative for every `x : TemperleyLieb ℂ (δ : ℂ) n` if and only if
`n < ⌊π / arccos (δ / 2)⌋`. -/
theorem markovTrace_nonneg_iff_lt_floor {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : 0 < δ)
    (hδJ : δ ∉ jonesLoopParameters) (q : ℂˣ)
    (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) (n : ℕ) :
    (∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ markovTrace q hq (star x * x)) ↔
      n < ⌊π / arccos (δ / 2)⌋₊ :=
  (isMarkovTrace_markovTrace q hq).forall_map_star_mul_self_nonneg_iff_lt_floor hδ hδJ

end TauCeti.TemperleyLieb
