/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Classification
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounding multiplicities along `(-2)`-configurations

In a minimal numerical type of genus `g ≥ 2`, every multiplicity-weighted intersection number
`mᵢ|aᵢⱼ|` is at most `768g` ([Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W)),
and in fact at most `768g - 768`.
The components that are not `(-2)`-indices already satisfy `mⱼ|aⱼⱼ| ≤ 6g - 6`
(`TauCeti.NumericalType.IsMinimal.multiplicity_mul_abs_intersection_self_le`). The work is to
propagate a bound into the configurations of `(-2)`-indices, which the classification of
[Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L) shows to be of Dynkin shape.
This file supplies the two propagation mechanisms of the Stacks proof, and combines them with the
classification of connected proper sets of `(-2)`-indices into the bound itself.

* **Doubling along a walk.** If a component `i` with `aᵢᵢ = -2wᵢ` meets `k`, then
  `mᵢ|aᵢᵢ| = 2mᵢwᵢ ≤ 2mₖ|aₖₖ|`. Along a walk of such components starting at a component that is
  not a `(-2)`-index, the weighted self-intersection at most doubles at each step. This handles
  the small configurations, where every component is close to a component outside them.
* **A weighted maximum principle.** Let `S` be a nonempty proper set of components and `v` a vector,
  positive on `S`, with `∑_{k ∈ S} aᵢₖvₖ ≤ 0` for every `i ∈ S`. Then the ratio `mᵢ/vᵢ` attains
  its maximum over `S` at a component meeting a component outside `S`. This is the concavity
  argument of the Stacks proof, and it handles the long configurations. For a chain of the
  shape of [Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89) and a fork of the
  shape of [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8D) there is such a
  `v` with values `1` and `2`. When every component meeting the configuration from outside is
  not a `(-2)`-index, this gives `mᵢ|aᵢᵢ| ≤ 24g - 24` along the whole configuration, however
  long it is.

## Main results

* `TauCeti.NumericalType.exists_adj_notMem_forall_multiplicity_mul_le`: the weighted maximum
  principle.
* `TauCeti.NumericalType.IsMinimal.exists_forall_multiplicity_mul_weight_mul_le`: its form in a
  minimal numerical type, when every component meeting `S` from outside is not a `(-2)`-index.
* `TauCeti.NumericalType.multiplicity_mul_abs_intersection_self_le_two_pow_mul` and
  `TauCeti.NumericalType.IsMinimal.multiplicity_mul_abs_intersection_self_le_two_pow_mul`: the
  doubling bound along a walk of components of self-intersection `-2w`.
* `IsSelfIntersectionMinusTwoChain.multiplicity_mul_abs_intersection_self_le`:
  `mᵢ|aᵢᵢ| ≤ 24g - 24` along a chain of at least five components of self-intersection `-2w`
  that meets no `(-2)`-index outside itself.
* `IsSelfIntersectionMinusTwoFork.multiplicity_mul_abs_intersection_self_le` and
  `IsSelfIntersectionMinusTwoFork.multiplicity_mul_abs_intersection_self_le_branch`:
  the same bound on a fork.
* `TauCeti.NumericalType.IsMinimal.multiplicity_mul_abs_intersection_le`:
  `mᵢ|aᵢⱼ| ≤ 768g - 768` for all components `i`, `j` of a minimal numerical type of genus
  `g ≥ 2`.

## References

The doubling argument is the second paragraph and the concavity argument the last three
paragraphs of the proof of [Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W).
The Stacks Project writes out the concavity argument for a simply laced chain only and leaves the
chains with a double edge and the forks to the reader. Here the three cases are treated uniformly
through the weighted maximum principle, and the constant `24g - 24` covers all of them.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-! ### The weighted maximum principle -/

/-- The equality case of the weighted maximum principle: if `i ∈ S` maximizes `mⱼ/vⱼ` over `S`
and meets no component outside `S`, then every component of `S` meeting `i` maximizes it too. -/
private lemma multiplicity_mul_eq_of_forall_le {S : Finset T.Component} {v : T.Component → ℤ}
    (hrow : ∀ i ∈ S, ∑ k ∈ S, T.intersection i k * v k ≤ 0) {i : T.Component} (hi : i ∈ S)
    (hmax : ∀ j ∈ S, (T.multiplicity j : ℤ) * v i ≤ T.multiplicity i * v j)
    (hout : ∀ k ∉ S, ¬ 0 < T.intersection i k) {k : T.Component} (hk : k ∈ S) (hik : i ≠ k)
    (hpos : 0 < T.intersection i k) :
    (T.multiplicity k : ℤ) * v i = T.multiplicity i * v k := by
  have hmi : (0 : ℤ) ≤ T.multiplicity i := Int.natCast_nonneg _
  -- the fibre relation at `i` only involves components of `S`
  have hfib : (T.multiplicity i : ℤ) * T.intersection i i =
      -∑ j ∈ S.erase i, (T.multiplicity j : ℤ) * T.intersection i j := by
    rw [T.multiplicity_mul_intersection_self i]
    congr 1
    refine (Finset.sum_subset (Finset.erase_subset_erase i (Finset.subset_univ S)) ?_).symm
    intro j hj hjS
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hjS' : j ∉ S := fun h ↦ hjS (Finset.mem_erase.mpr ⟨hji, h⟩)
    have hzero : T.intersection i j = 0 :=
      le_antisymm (not_lt.mp (hout j hjS')) (T.offDiagonal_nonneg i j hji.symm)
    rw [hzero, mul_zero]
  have hrow' := hrow i hi
  rw [← Finset.add_sum_erase S _ hi] at hrow'
  -- the defects `aᵢⱼ (mᵢvⱼ - mⱼvᵢ)` are nonnegative and sum to a nonpositive number
  have hnonneg : ∀ j ∈ S.erase i,
      0 ≤ T.intersection i j * ((T.multiplicity i : ℤ) * v j - T.multiplicity j * v i) :=
    fun j hj ↦ mul_nonneg (T.offDiagonal_nonneg i j (Finset.ne_of_mem_erase hj).symm)
      (sub_nonneg.mpr (hmax j (Finset.mem_of_mem_erase hj)))
  have hsum : ∑ j ∈ S.erase i,
      T.intersection i j * ((T.multiplicity i : ℤ) * v j - T.multiplicity j * v i) =
        T.multiplicity i * ∑ j ∈ S.erase i, T.intersection i j * v j -
          v i * ∑ j ∈ S.erase i, (T.multiplicity j : ℤ) * T.intersection i j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hle : ∑ j ∈ S.erase i,
      T.intersection i j * ((T.multiplicity i : ℤ) * v j - T.multiplicity j * v i) ≤ 0 := by
    rw [hsum]
    have h₁ := mul_le_mul_of_nonneg_left hrow' hmi
    have h₂ : v i * ((T.multiplicity i : ℤ) * T.intersection i i) =
        -(v i * ∑ j ∈ S.erase i, (T.multiplicity j : ℤ) * T.intersection i j) := by
      rw [hfib]; ring
    nlinarith [h₁, h₂]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
    (le_antisymm hle (Finset.sum_nonneg hnonneg)) k (Finset.mem_erase.mpr ⟨hik.symm, hk⟩)
  have := (mul_eq_zero.mp hterm).resolve_left hpos.ne'
  linarith

/-- **The weighted maximum principle for multiplicities.** Let `S` be a nonempty proper set of
components of a numerical type and `v` an integer vector, positive on `S`, with
`∑_{k ∈ S} aᵢₖvₖ ≤ 0` for every `i ∈ S`. Then the ratio `mᵢ/vᵢ` attains its maximum over `S` at a
component `i ∈ S` meeting a component outside `S`. The conclusion is stated without division:
`mⱼvᵢ ≤ mᵢvⱼ` for every `j ∈ S`.

For a proper chain of components of a common weight `w`, each of self-intersection `-2w`, in
which consecutive components meet with intersection number `w` and no other two components meet,
the constant vector `v = 1` satisfies the hypothesis, and the statement says that the
multiplicities along the chain are largest at a component meeting something outside the chain:
this is the concavity argument in the proof of [Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W). -/
theorem exists_adj_notMem_forall_multiplicity_mul_le {S : Finset T.Component} (hS : S.Nonempty)
    (hSu : ∃ k, k ∉ S) {v : T.Component → ℤ} (hv : ∀ i ∈ S, 0 < v i)
    (hrow : ∀ i ∈ S, ∑ k ∈ S, T.intersection i k * v k ≤ 0) :
    ∃ i ∈ S, (∃ k ∉ S, T.Adj i k) ∧
      ∀ j ∈ S, (T.multiplicity j : ℤ) * v i ≤ T.multiplicity i * v j := by
  obtain ⟨i₀, hi₀, hmax₀⟩ :=
    S.exists_max_image (fun j ↦ (T.multiplicity j : ℚ) / (v j : ℚ)) hS
  -- the set of maximizers of `mⱼ/vⱼ` on `S`
  let P : Set T.Component :=
    {i | i ∈ S ∧ ∀ j ∈ S, (T.multiplicity j : ℤ) * v i ≤ T.multiplicity i * v j}
  have hi₀P : i₀ ∈ P := by
    refine ⟨hi₀, fun j hj ↦ ?_⟩
    have h := hmax₀ j hj
    rw [div_le_div_iff₀ (by exact_mod_cast hv j hj) (by exact_mod_cast hv i₀ hi₀)] at h
    exact_mod_cast h
  have hPu : P ≠ Set.univ := by
    obtain ⟨k₀, hk₀⟩ := hSu
    intro h
    have hk : k₀ ∈ P := h ▸ Set.mem_univ k₀
    exact hk₀ hk.1
  obtain ⟨i, hiP, k, hkP, hik⟩ := T.exists_mem_notMem_adj P ⟨i₀, hi₀P⟩ hPu
  refine ⟨i, hiP.1, ?_, hiP.2⟩
  by_contra hno
  have hout : ∀ l ∉ S, ¬ 0 < T.intersection i l := fun l hl hpos ↦
    hno ⟨l, hl, T.adj_iff.mpr ⟨fun h ↦ hl (h ▸ hiP.1), hpos⟩⟩
  have hkS : k ∈ S := by
    by_contra hkS
    exact hno ⟨k, hkS, hik⟩
  have heq := T.multiplicity_mul_eq_of_forall_le hrow hiP.1 hiP.2 hout hkS
    (T.adj_iff.mp hik).1 (T.adj_iff.mp hik).2
  refine hkP ⟨hkS, fun j hj ↦ ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left (hiP.2 j hj) (hv k hkS).le
  have h₂ : (T.multiplicity k : ℤ) * v i * v j = T.multiplicity i * v k * v j := by rw [heq]
  have h₃ : (T.multiplicity j : ℤ) * v k * v i ≤ T.multiplicity k * v j * v i := by
    linarith [h₁, h₂]
  exact le_of_mul_le_mul_right h₃ (hv i hiP.1)

namespace IsMinimal

variable {T}

/-- The weighted maximum principle in a minimal numerical type `T` of genus `g` with more than one
component. Let `S` and `v` be as in
`TauCeti.NumericalType.exists_adj_notMem_forall_multiplicity_mul_le`, and suppose that every
component meeting `S` from outside is not a `(-2)`-index. Then some `i ∈ S` satisfies
`mⱼwᵢvᵢ ≤ (6g - 6)vⱼ` for every `j ∈ S`. -/
theorem exists_forall_multiplicity_mul_weight_mul_le (hT : T.IsMinimal)
    {S : Finset T.Component} (hS : S.Nonempty) (hSu : ∃ k, k ∉ S)
    {v : T.Component → ℤ} (hv : ∀ i ∈ S, 0 < v i)
    (hrow : ∀ i ∈ S, ∑ k ∈ S, T.intersection i k * v k ≤ 0)
    (hclosed : ∀ i ∈ S, ∀ k ∉ S, 0 < T.intersection i k → ¬ T.IsMinusTwoIndex k) :
    ∃ i ∈ S, ∀ j ∈ S, (T.multiplicity j : ℤ) * T.weight i * v i ≤
      (6 * T.arithmeticGenus - 6) * v j := by
  have h : 1 < Fintype.card T.Component := Fintype.one_lt_card_iff.mpr <| by
    obtain ⟨i, hi⟩ := hS
    obtain ⟨k, hk⟩ := hSu
    exact ⟨i, k, fun hik ↦ hk (hik ▸ hi)⟩
  obtain ⟨i, hi, ⟨k, hk, hik⟩, hmax⟩ :=
    T.exists_adj_notMem_forall_multiplicity_mul_le hS hSu hv hrow
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  have hpos := (T.adj_iff.mp hik).2
  have hbound : (T.multiplicity i : ℤ) * T.weight i ≤ 6 * T.arithmeticGenus - 6 :=
    (T.multiplicity_mul_weight_le_of_pos hpos).trans
      (hT.multiplicity_mul_abs_intersection_self_le h (hclosed i hi k hk hpos))
  have hw : (0 : ℤ) ≤ T.weight i := Int.natCast_nonneg _
  have h₁ := mul_le_mul_of_nonneg_left (hmax j hj) hw
  have h₂ := mul_le_mul_of_nonneg_right hbound (hv j hj).le
  linarith [h₁, h₂]

end IsMinimal

/-! ### Doubling along a walk -/

/-- A component with self-intersection `aᵢᵢ = -2wᵢ` meeting a component `k` has weighted
self-intersection `mᵢ|aᵢᵢ|` at most twice that of `k`. -/
lemma multiplicity_mul_abs_intersection_self_le_two_mul {i k : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ))) (hik : 0 < T.intersection i k) :
    (T.multiplicity i : ℤ) * |T.intersection i i| ≤
      2 * ((T.multiplicity k : ℤ) * |T.intersection k k|) := by
  have h := T.multiplicity_mul_weight_le_of_pos hik
  rw [hi, abs_neg, abs_of_nonneg (by positivity)]
  linarith

/-- Along a walk `c 0, c 1, …, c n` of consecutively meeting components in which every component
after the first has self-intersection `-2w`, the weighted self-intersection `mᵢ|aᵢᵢ|` at most
doubles at each step. -/
theorem multiplicity_mul_abs_intersection_self_le_two_pow_mul (c : ℕ → T.Component) (n : ℕ)
    (hself : ∀ r, 0 < r → r ≤ n → T.intersection (c r) (c r) = -(2 * (T.weight (c r) : ℤ)))
    (hsucc : ∀ r < n, 0 < T.intersection (c r) (c (r + 1))) :
    (T.multiplicity (c n) : ℤ) * |T.intersection (c n) (c n)| ≤
      2 ^ n * ((T.multiplicity (c 0) : ℤ) * |T.intersection (c 0) (c 0)|) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ := T.multiplicity_mul_abs_intersection_self_le_two_mul
      (hself (n + 1) (by omega) le_rfl)
      (by rw [T.intersection_comm]; exact hsucc n (by omega))
    have h₂ := ih (fun r hr hrn ↦ hself r hr (by omega)) (fun r hr ↦ hsucc r (by omega))
    rw [pow_succ]
    linarith

/-- In a minimal numerical type `T` of genus `g` with more than one component, along a walk
`c 0, c 1, …, c n` of consecutively meeting components starting at a component that is not a
`(-2)`-index, in which every later component has self-intersection `-2w`, the weighted
self-intersection at the end is `m|a| ≤ 2ⁿ(6g - 6)`. This is the second paragraph of the proof of
[Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W). -/
theorem IsMinimal.multiplicity_mul_abs_intersection_self_le_two_pow_mul {T : NumericalType.{u}}
    (hT : T.IsMinimal) (h : 1 < Fintype.card T.Component) (c : ℕ → T.Component) (n : ℕ)
    (h₀ : ¬ T.IsMinusTwoIndex (c 0))
    (hself : ∀ r, 0 < r → r ≤ n → T.intersection (c r) (c r) = -(2 * (T.weight (c r) : ℤ)))
    (hsucc : ∀ r < n, 0 < T.intersection (c r) (c (r + 1))) :
    (T.multiplicity (c n) : ℤ) * |T.intersection (c n) (c n)| ≤
      2 ^ n * (6 * T.arithmeticGenus - 6) :=
  (T.multiplicity_mul_abs_intersection_self_le_two_pow_mul c n hself hsucc).trans
    (mul_le_mul_of_nonneg_left (hT.multiplicity_mul_abs_intersection_self_le h h₀)
      (by positivity))

/-! ### Chains -/

section Chain

variable {T} {t : ℕ} {c : ℕ → T.Component}

/-- Sums over the components of a chain are sums over its positions. -/
private lemma sum_image_chain (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (f : T.Component → ℤ) : ∑ k ∈ (range t).image c, f k = ∑ s ∈ range t, f (c s) :=
  Finset.sum_image fun p hp q hq hpq ↦
    hc.injOn p (Finset.mem_range.mp hp) q (Finset.mem_range.mp hq) hpq

/-- A set of fewer components than the numerical type has misses some component. -/
private lemma exists_notMem_of_card_lt {S : Finset T.Component}
    (hS : #S < Fintype.card T.Component) : ∃ k, k ∉ S := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := univ) (by simpa using hS)
  exact ⟨k, hk⟩

/-- The test vector for a chain: `1` at a component of twice the common interior weight `W`, and
`2` elsewhere. -/
private def chainTest (W : ℤ) (k : T.Component) : ℤ :=
  if (T.weight k : ℤ) = 2 * W then 1 else 2

/-- Along a chain of at least five components of self-intersection `-2w`, in a numerical type
with more components than the chain has length, the chain test vector satisfies the hypothesis of
the weighted maximum principle. -/
private lemma sum_intersection_mul_chainTest_nonpos (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t < Fintype.card T.Component) {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = W)
    (hall : ∀ i < t, (T.weight (c i) : ℤ) = W ∨ (T.weight (c i) : ℤ) = 2 * W ∨
      2 * (T.weight (c i) : ℤ) = W) (ht : 4 < t) {r : ℕ} (hr : r < t) :
    ∑ s ∈ range t, T.intersection (c r) (c s) * chainTest W (c s) ≤ 0 := by
  have h2 : 2 < Fintype.card T.Component := by omega
  have hedge : ∀ p q, q = p + 1 → q < t → T.intersection (c p) (c q) =
      max (T.weight (c p) : ℤ) (T.weight (c q) : ℤ) := fun p q hpq hq ↦
    intersection_eq_max_weight T h2 (hc.intersection_self p (by omega))
      (hc.intersection_self q hq) (hc.intersection_pos hpq hq)
  have hself := hc.intersection_self r hr
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · -- the first end
    rw [hc.left_sum_eq hcard (by omega), hself, hedge 0 1 rfl (by omega)]
    have h₀ := hall 0 (by omega)
    have h₁ := hint 1 (by omega) (by omega)
    simp only [chainTest, max_def]
    split_ifs <;> omega
  rcases lt_or_ge (r + 1) t with hrt | hrt
  · -- an interior component
    rw [hc.interior_sum_eq hcard _ hr0 hrt, hself, T.intersection_comm (c r) (c (r - 1)),
      hedge (r - 1) r (by omega) hr, hedge r (r + 1) rfl hrt]
    have h₀ := hall (r - 1) (by omega)
    have h₁ := hint r hr0 hrt
    have h₂ := hall (r + 1) hrt
    simp only [chainTest, max_def]
    split_ifs <;> omega
  · -- the last end
    obtain rfl : r = t - 1 := by omega
    rw [hc.right_sum_eq hcard (by omega), hself, T.intersection_comm (c (t - 1)) (c (t - 2)),
      hedge (t - 2) (t - 1) (by omega) (by omega)]
    have h₀ := hint (t - 2) (by omega) (by omega)
    have h₁ := hall (t - 1) (by omega)
    simp only [chainTest, max_def]
    split_ifs <;> omega

/-- In a minimal numerical type `T` of genus `g`, let `c 0, …, c (t - 1)` be a chain of at least
five components of self-intersection `-2w`, with `T` having more components than the chain, and
suppose that every component outside the chain meeting it is not a `(-2)`-index. Then
`mᵢ|aᵢᵢ| ≤ 24g - 24` for every component `i` of the chain.

For chains of length greater than five, see [Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89).
The bound is the chain case of [Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W). -/
theorem IsSelfIntersectionMinusTwoChain.multiplicity_mul_abs_intersection_self_le
    (hT : T.IsMinimal) (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t < Fintype.card T.Component) (ht : 4 < t)
    (hclosed : ∀ r < t, ∀ k, (∀ s < t, k ≠ c s) → 0 < T.intersection (c r) k →
      ¬ T.IsMinusTwoIndex k)
    {r : ℕ} (hr : r < t) :
    (T.multiplicity (c r) : ℤ) * |T.intersection (c r) (c r)| ≤ 24 * T.arithmeticGenus - 24 := by
  -- The `t = 5` classification comes from `exists_intersection_ratio_chain_five_mem` via
  -- `exists_weight_eq_except_one_end`. Use `1` at a double-weight end and `2` elsewhere.
  obtain ⟨W, hW, hint, h₀, hlast, -⟩ := hc.exists_weight_eq_except_one_end hcard ht
  have hall : ∀ i < t, (T.weight (c i) : ℤ) = W ∨ (T.weight (c i) : ℤ) = 2 * W ∨
      2 * (T.weight (c i) : ℤ) = W := fun i hi ↦ by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact h₀
    rcases lt_or_ge (i + 1) t with hit | hit
    · exact Or.inl (hint i hi0 hit)
    · obtain rfl : i = t - 1 := by omega
      exact hlast
  set S := (range t).image c with hS
  have hmemS : ∀ {k}, k ∈ S ↔ ∃ s < t, c s = k := by
    intro k
    simp [hS]
  have hv : ∀ i ∈ S, 0 < chainTest W i := fun i _ ↦ by
    unfold chainTest
    split_ifs <;> omega
  have hrow : ∀ i ∈ S, ∑ k ∈ S, T.intersection i k * chainTest W k ≤ 0 := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := hmemS.mp hi
    rw [sum_image_chain hc]
    exact sum_intersection_mul_chainTest_nonpos hc hcard hW hint hall ht hp
  have hclosed' : ∀ i ∈ S, ∀ k ∉ S, 0 < T.intersection i k → ¬ T.IsMinusTwoIndex k := by
    intro i hi k hk hpos
    obtain ⟨p, hp, rfl⟩ := hmemS.mp hi
    exact hclosed p hp k (fun s hs hks ↦ hk (hmemS.mpr ⟨s, hs, hks.symm⟩)) hpos
  have h1 : 1 < Fintype.card T.Component := by omega
  have hSu : ∃ k, k ∉ S :=
    exists_notMem_of_card_lt ((Finset.card_image_le.trans (card_range t).le).trans_lt hcard)
  obtain ⟨i, hi, hbound⟩ := hT.exists_forall_multiplicity_mul_weight_mul_le
    ⟨c 0, hmemS.mpr ⟨0, by omega, rfl⟩⟩ hSu hv hrow hclosed'
  obtain ⟨p, hp, rfl⟩ := hmemS.mp hi
  have hj := hbound (c r) (hmemS.mpr ⟨r, hr, rfl⟩)
  have hg := hT.one_le_arithmeticGenus h1
  have hm : (0 : ℤ) < T.multiplicity (c r) := Int.natCast_pos.mpr (T.multiplicity (c r)).pos
  rw [hc.intersection_self r hr, abs_neg, abs_of_nonneg (by positivity)]
  -- `wᵢvᵢ ≥ W` at the maximizing component, `wⱼvⱼ ≤ 2W` and `vⱼ ≤ 2` at every component
  have hwi : W ≤ (T.weight (c p) : ℤ) * chainTest W (c p) := by
    unfold chainTest
    rcases hall p hp with h | h | h <;> split_ifs <;> omega
  have hwj : (T.weight (c r) : ℤ) * chainTest W (c r) ≤ 2 * W := by
    unfold chainTest
    rcases hall r hr with h | h | h <;> split_ifs <;> omega
  have hvj : chainTest W (c r) ≤ 2 := by
    unfold chainTest
    split_ifs <;> omega
  have hvj0 := hv (c r) (hmemS.mpr ⟨r, hr, rfl⟩)
  -- `mⱼW ≤ (6g - 6)vⱼ`, hence `mⱼwⱼvⱼ ≤ 2mⱼW ≤ 2(6g - 6)vⱼ`
  have hmW : (T.multiplicity (c r) : ℤ) * W ≤ (6 * T.arithmeticGenus - 6) * chainTest W (c r) :=
    (mul_le_mul_of_nonneg_left hwi hm.le).trans (by linarith [hj])
  have hmw : (T.multiplicity (c r) : ℤ) * T.weight (c r) * chainTest W (c r) ≤
      2 * (6 * T.arithmeticGenus - 6) * chainTest W (c r) := by
    have := mul_le_mul_of_nonneg_left hwj hm.le
    linarith
  have := le_of_mul_le_mul_right hmw hvj0
  linarith

end Chain

/-! ### Forks -/

section Fork

variable {T} {t : ℕ} {c : ℕ → T.Component} {branch : T.Component}

/-- The test vector for a fork: `1` at the two leaves `c (t - 1)` and `branch` at the forked end,
and `2` elsewhere. -/
private def forkTest (c : ℕ → T.Component) (t : ℕ) (branch k : T.Component) : ℤ :=
  if k = c (t - 1) ∨ k = branch then 1 else 2

namespace IsSelfIntersectionMinusTwoFork

/-- Along a fork, in a numerical type with more components than the fork, the fork test vector
satisfies the hypothesis of the weighted maximum principle. -/
private lemma sum_intersection_mul_forkTest_nonpos
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component) {W : ℕ+}
    (hwc : ∀ i < t, (T.weight (c i) : ℤ) = W) (hwb : (T.weight branch : ℤ) = W)
    (hedge : ∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = W)
    (hbranch : T.intersection (c (t - 2)) branch = W) {i : T.Component}
    (hi : i ∈ insert branch ((range t).image c)) :
    ∑ k ∈ insert branch ((range t).image c), T.intersection i k * forkTest c t branch k ≤ 0 := by
  have hc := hf.toIsSelfIntersectionMinusTwoChain
  have ht := hf.two_lt
  have hW : (0 : ℤ) < W := by exact_mod_cast W.pos
  set S := insert branch ((range t).image c) with hS
  have hmemS : ∀ {k}, k ∈ S ↔ k = branch ∨ ∃ s < t, c s = k := by
    intro k
    simp [hS]
  have hbr : branch ∉ (range t).image c := by
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    exact fun s hs h ↦ hf.branch_ne s hs h.symm
  -- the values of the test vector
  have hvc : ∀ s < t, forkTest c t branch (c s) = if s = t - 1 then 1 else 2 := by
    intro s hs
    have hlast : c s = c (t - 1) ↔ s = t - 1 :=
      ⟨fun h ↦ hc.injOn s hs (t - 1) (by omega) h, fun h ↦ h ▸ rfl⟩
    have hb : c s ≠ branch := fun h ↦ hf.branch_ne s hs h.symm
    simp only [forkTest, hlast, hb, or_false]
  have hvb : forkTest c t branch branch = 1 := by simp [forkTest]
  have hsum : ∀ i, ∑ k ∈ S, T.intersection i k * forkTest c t branch k =
      T.intersection i branch + ∑ s ∈ range t,
        T.intersection i (c s) * (if s = t - 1 then 1 else 2) := by
    intro i
    rw [hS, Finset.sum_insert hbr, sum_image_chain hc, hvb, mul_one]
    congr 1
    exact Finset.sum_congr rfl fun s hs ↦ by rw [hvc s (Finset.mem_range.mp hs)]
  have hcardt : t < Fintype.card T.Component := by omega
  have hbself : T.intersection branch branch = -(2 * (W : ℤ)) := by
    rw [hf.branch_intersection_self, hwb]
  rw [hsum]
  rcases hmemS.mp hi with rfl | ⟨r, hr, rfl⟩
  · -- the extra leaf meets the chain only at `c (t - 2)`
    rw [Finset.sum_eq_single (t - 2), hbself, T.intersection_comm, hbranch]
    · have hpenultimate_ne_last : t - 2 ≠ t - 1 := by omega
      simp only [hpenultimate_ne_last, ↓reduceIte]
      linarith
    · intro s hs hst
      rw [T.intersection_comm, hf.branch_intersection_eq_zero (Finset.mem_range.mp hs) hst,
        zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · have hself : T.intersection (c r) (c r) = -(2 * (W : ℤ)) := by
      rw [hc.intersection_self r hr, hwc r hr]
    have hsucc : ∀ p, p + 1 < t → T.intersection (c (p + 1)) (c p) = W := fun p hp ↦ by
      rw [T.intersection_comm, hedge p hp]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · -- the free end of the chain
      have h01 := hedge 0 (by omega)
      have hzero_ne_last : (0 : ℕ) ≠ t - 1 := by omega
      have hone_ne_last : 1 ≠ t - 1 := by omega
      rw [zero_add] at h01
      rw [hf.branch_intersection_eq_zero hr (by omega), hc.left_sum_eq hcardt (by omega),
        hself, h01]
      simp only [hzero_ne_last, hone_ne_last, ↓reduceIte]
      linarith
    rcases lt_or_ge (r + 1) t with hrt | hrt
    · have hprev := hsucc (r - 1) (by omega)
      have hprev_succ : r - 1 + 1 = r := by omega
      have hprev_ne_last : r - 1 ≠ t - 1 := by omega
      have hr_ne_last : r ≠ t - 1 := by omega
      rw [hprev_succ] at hprev
      rw [hc.interior_sum_eq hcardt _ hr0 hrt, hself, hedge r hrt, hprev]
      simp only [hprev_ne_last, hr_ne_last, ↓reduceIte]
      by_cases hrb : r = t - 2
      · -- the forked component meets both leaves
        subst hrb
        rw [hbranch]
        have hpenultimate_succ : t - 2 + 1 = t - 1 := by omega
        simp only [hpenultimate_succ, ↓reduceIte]
        linarith
      · rw [hf.branch_intersection_eq_zero hr hrb]
        have hnext_ne_last : r + 1 ≠ t - 1 := by omega
        simp only [hnext_ne_last, ↓reduceIte]
        linarith
    · -- the leaf `c (t - 1)`
      obtain rfl : r = t - 1 := by omega
      have hprev := hsucc (t - 2) (by omega)
      have hpenultimate_succ : t - 2 + 1 = t - 1 := by omega
      have hpenultimate_ne_last : t - 2 ≠ t - 1 := by omega
      rw [hpenultimate_succ] at hprev
      rw [hf.branch_intersection_eq_zero hr (by omega), hc.right_sum_eq hcardt (by omega),
        hself, hprev]
      simp only [hpenultimate_ne_last, ↓reduceIte]
      linarith

/-- The weighted-maximum-principle bound on a fork, for every component of the fork. -/
private lemma forall_mem_multiplicity_mul_abs_intersection_self_le (hT : T.IsMinimal)
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component)
    (hclosed : ∀ i, (i = branch ∨ ∃ r < t, i = c r) → ∀ k, k ≠ branch → (∀ s < t, k ≠ c s) →
      0 < T.intersection i k → ¬ T.IsMinusTwoIndex k) :
    ∀ j ∈ insert branch ((range t).image c),
      (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 24 * T.arithmeticGenus - 24 := by
  have hc := hf.toIsSelfIntersectionMinusTwoChain
  have ht := hf.two_lt
  -- The shorter fork classifications are supplied by `exists_weight_intersection_eq_three`
  -- and `exists_weight_intersection_eq_four`. Use `1` at both leaves and `2` elsewhere.
  obtain ⟨W, hwc, hwb, hedge, hbranch⟩ := hf.exists_weight_intersection_eq hcard
  have hW : (0 : ℤ) < W := by exact_mod_cast W.pos
  set S := insert branch ((range t).image c) with hS
  have hmemS : ∀ {k}, k ∈ S ↔ k = branch ∨ ∃ s < t, c s = k := by
    intro k
    simp [hS]
  have hbself : T.intersection branch branch = -(2 * (W : ℤ)) := by
    rw [hf.branch_intersection_self, hwb]
  have hv : ∀ i ∈ S, 0 < forkTest c t branch i := fun i _ ↦ by
    unfold forkTest
    split_ifs <;> omega
  have hrow : ∀ i ∈ S, ∑ k ∈ S, T.intersection i k * forkTest c t branch k ≤ 0 :=
    fun i hi ↦ sum_intersection_mul_forkTest_nonpos hf hcard hwc hwb hedge hbranch hi
  have hclosed' : ∀ i ∈ S, ∀ k ∉ S, 0 < T.intersection i k → ¬ T.IsMinusTwoIndex k := by
    intro i hi k hk hpos
    refine hclosed i ?_ k (fun h ↦ hk (hmemS.mpr (Or.inl h)))
      (fun s hs hks ↦ hk (hmemS.mpr (Or.inr ⟨s, hs, hks.symm⟩))) hpos
    rcases hmemS.mp hi with h | ⟨s, hs, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, h.symm⟩
  have h1 : 1 < Fintype.card T.Component := by omega
  have hSu : ∃ k, k ∉ S := by
    refine exists_notMem_of_card_lt ?_
    calc #S ≤ #((range t).image c) + 1 := Finset.card_insert_le _ _
      _ ≤ t + 1 := by
        have := (Finset.card_image_le (s := range t) (f := c)).trans (card_range t).le
        omega
      _ < Fintype.card T.Component := hcard
  obtain ⟨i, hi, hbound⟩ := hT.exists_forall_multiplicity_mul_weight_mul_le
    ⟨branch, hmemS.mpr (Or.inl rfl)⟩ hSu hv hrow hclosed'
  -- every component of the fork has weight `W`
  have hweight : ∀ k ∈ S, (T.weight k : ℤ) = W := by
    intro k hk
    rcases hmemS.mp hk with rfl | ⟨s, hs, rfl⟩
    · exact hwb
    · exact hwc s hs
  have hselfS : ∀ k ∈ S, T.intersection k k = -(2 * W) := by
    intro k hk
    rcases hmemS.mp hk with rfl | ⟨s, hs, rfl⟩
    · exact hbself
    · rw [hc.intersection_self s hs, hwc s hs]
  intro j hj
  have hbj := hbound j hj
  rw [hweight i hi] at hbj
  have hg := hT.one_le_arithmeticGenus h1
  have hm : (0 : ℤ) < T.multiplicity j := Int.natCast_pos.mpr (T.multiplicity j).pos
  rw [hselfS j hj, abs_neg, abs_of_nonneg (by positivity)]
  have hvi : 1 ≤ forkTest c t branch i := by
    unfold forkTest
    split_ifs <;> omega
  have hvj : forkTest c t branch j ≤ 2 := by
    unfold forkTest
    split_ifs <;> omega
  -- `mⱼW ≤ mⱼWvᵢ ≤ (6g - 6)vⱼ ≤ 2(6g - 6)`
  have h₁ : (T.multiplicity j : ℤ) * W ≤ (T.multiplicity j : ℤ) * W * forkTest c t branch i :=
    le_mul_of_one_le_right (by positivity) hvi
  have hgenus : (0 : ℤ) ≤ 6 * T.arithmeticGenus - 6 := by linarith
  have h₂ := mul_le_mul_of_nonneg_left hvj hgenus
  linarith

/-- In a minimal numerical type `T` of genus `g`, let `c 0, …, c (t - 1)` together with `branch`
be a fork of components of self-intersection `-2w`, with `T` having more components than the
fork, and suppose that every component outside the fork meeting it is not a `(-2)`-index. Then
`mᵢ|aᵢᵢ| ≤ 24g - 24` for every component `c r` of the chain of the fork.

For forks with `t > 4`, see [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8D).
The bound is the fork case of [Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W). -/
theorem multiplicity_mul_abs_intersection_self_le (hT : T.IsMinimal)
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component)
    (hclosed : ∀ i, (i = branch ∨ ∃ r < t, i = c r) → ∀ k, k ≠ branch → (∀ s < t, k ≠ c s) →
      0 < T.intersection i k → ¬ T.IsMinusTwoIndex k)
    {r : ℕ} (hr : r < t) :
    (T.multiplicity (c r) : ℤ) * |T.intersection (c r) (c r)| ≤ 24 * T.arithmeticGenus - 24 :=
  forall_mem_multiplicity_mul_abs_intersection_self_le hT hf hcard hclosed (c r)
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem c (Finset.mem_range.mpr hr)))

/-- The bound `m|a| ≤ 24g - 24` of
`TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.multiplicity_mul_abs_intersection_self_le`
at the extra leaf `branch` of the fork. -/
theorem multiplicity_mul_abs_intersection_self_le_branch (hT : T.IsMinimal)
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component)
    (hclosed : ∀ i, (i = branch ∨ ∃ r < t, i = c r) → ∀ k, k ≠ branch → (∀ s < t, k ≠ c s) →
      0 < T.intersection i k → ¬ T.IsMinusTwoIndex k) :
    (T.multiplicity branch : ℤ) * |T.intersection branch branch| ≤
      24 * T.arithmeticGenus - 24 :=
  forall_mem_multiplicity_mul_abs_intersection_self_le hT hf hcard hclosed branch
    (Finset.mem_insert_self _ _)

end IsSelfIntersectionMinusTwoFork

end Fork

/-! ### The bound on a minimal numerical type -/

section Minimal

variable {T}

/-- One doubling step: a component `y` of self-intersection `-2w` meeting a component `z` with
`m_z|a_zz| ≤ 2ⁿB` has `m_y|a_yy| ≤ 2ⁿ⁺¹B`. -/
private lemma le_two_pow_succ_mul {y z : T.Component} {n : ℕ} {B : ℤ}
    (hy : T.intersection y y = -(2 * (T.weight y : ℤ))) (hyz : 0 < T.intersection y z)
    (hz : (T.multiplicity z : ℤ) * |T.intersection z z| ≤ 2 ^ n * B) :
    (T.multiplicity y : ℤ) * |T.intersection y y| ≤ 2 ^ (n + 1) * B := by
  have := T.multiplicity_mul_abs_intersection_self_le_two_mul hy hyz
  rw [pow_succ]
  linarith

/-- Along a chain of components of self-intersection `-2w`, a bound `m|a| ≤ 2ⁿB` at position `r`
gives `m|a| ≤ 2ⁿ⁺ᵈB` at every position at distance `d` from `r`. -/
private lemma IsSelfIntersectionMinusTwoChain.le_two_pow_add_mul {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) {n r : ℕ} {B : ℤ} (hrt : r < t)
    (hr : (T.multiplicity (c r) : ℤ) * |T.intersection (c r) (c r)| ≤ 2 ^ n * B) (d : ℕ) :
    ∀ s, (s + d = r ∨ r + d = s) → s < t →
      (T.multiplicity (c s) : ℤ) * |T.intersection (c s) (c s)| ≤ 2 ^ (n + d) * B := by
  induction d with
  | zero =>
    intro s hs _
    obtain rfl : s = r := by omega
    simpa using hr
  | succ d ih =>
    rintro s (hs | hs) hst
    · rw [← add_assoc]
      exact le_two_pow_succ_mul (hc.intersection_self s hst) (hc.intersection_pos rfl (by omega))
        (ih (s + 1) (.inl (by omega)) (by omega))
    · rw [← add_assoc]
      refine le_two_pow_succ_mul (hc.intersection_self s hst) ?_
        (ih (s - 1) (.inr (by omega)) (by omega))
      rw [T.intersection_comm]
      exact hc.intersection_pos (by omega) hst

/-- In a numerical type of genus at least two with more than one component, the
`(-2)`-indices connected to a given `(-2)`-index through `(-2)`-indices form a proper connected set
of `(-2)`-indices that no further `(-2)`-index meets. -/
private lemma exists_finset_of_isMinusTwoIndex (hg : 2 ≤ T.arithmeticGenus)
    (h : 1 < Fintype.card T.Component) {i : T.Component} (hi : T.IsMinusTwoIndex i) :
    ∃ S : Finset T.Component, i ∈ S ∧ (∀ x ∈ S, T.IsMinusTwoIndex x) ∧
      #S < Fintype.card T.Component ∧
      (∀ A ⊆ S, A.Nonempty → A ≠ S → ∃ a ∈ A, ∃ j ∈ S, j ∉ A ∧ 0 < T.intersection a j) ∧
      ∀ x ∈ S, ∀ k ∉ S, 0 < T.intersection x k → ¬ T.IsMinusTwoIndex k := by
  classical
  let R : T.Component → T.Component → Prop := fun x y ↦ T.Adj x y ∧ T.IsMinusTwoIndex y
  let S : Finset T.Component := {x | Relation.ReflTransGen R i x}
  have hmem {x : T.Component} : x ∈ S ↔ Relation.ReflTransGen R i x := by simp [S]
  have hS : ∀ x ∈ S, T.IsMinusTwoIndex x := fun x hx ↦ by
    rcases (hmem.mp hx).cases_tail with rfl | ⟨y, -, -, hx⟩
    exacts [hi, hx]
  -- all contributions to the genus vanish at `(-2)`-indices, so some component is not one
  obtain ⟨k, hk⟩ : ∃ k, ¬ T.IsMinusTwoIndex k := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hq := T.arithmeticGenus_eq_one_add_sum_genusContribution
    rw [Finset.sum_eq_zero fun j _ ↦ (T.genusContribution_eq_zero_iff h j).mpr (hall j)] at hq
    have : (2 : ℚ) ≤ T.arithmeticGenus := by exact_mod_cast hg
    linarith
  refine ⟨S, hmem.mpr .refl, hS, Finset.card_lt_univ_of_notMem fun hkS ↦ hk (hS k hkS), ?_,
    fun x hx k hk hpos hk2 ↦ hk (hmem.mpr ((hmem.mp hx).tail ⟨T.adj_iff.mpr ⟨?_, hpos⟩, hk2⟩))⟩
  · intro A hAS ⟨a, ha⟩ hne
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    -- without an edge leaving `A` inside `S`, membership in `A` is constant along `R`
    have hconst : ∀ x, Relation.ReflTransGen R i x → (x ∈ A ↔ i ∈ A) := by
      intro x hx
      induction hx with
      | refl => rfl
      | tail hy hyz ih =>
        rename_i y z
        rw [← ih]
        have hyS := hmem.mpr hy
        have hzS := hmem.mpr (hy.tail hyz)
        constructor
        · intro hzA
          by_contra hyA
          exact (hno z hzA y hyS hyA).not_gt (T.intersection_comm y z ▸ (T.adj_iff.mp hyz.1).2)
        · intro hyA
          by_contra hzA
          exact (hno y hyA z hzS hzA).not_gt (T.adj_iff.mp hyz.1).2
    obtain ⟨b, hbS, hbA⟩ : ∃ b ∈ S, b ∉ A := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hne (Finset.Subset.antisymm hAS hall)
    exact hbA ((hconst b (hmem.mp hbS)).mpr ((hconst a (hmem.mp (hAS ha))).mp ha))
  · rintro rfl
    exact hk hx

/-- In a minimal numerical type of genus `g ≥ 2`, a `(-2)`-index `i` has `mᵢ|aᵢᵢ| ≤ 768g - 768`.
The `(-2)`-indices connected to `i` form a chain, a fork, or a configuration of type `E₆`, `E₇` or
`E₈`. Long chains and forks are covered by the concavity bound `24g - 24`; in the remaining
configurations every component lies at distance at most six from a component meeting a component
that is not a `(-2)`-index, and the doubling bound applies. -/
private lemma IsMinimal.multiplicity_mul_abs_intersection_self_le_of_isMinusTwoIndex
    (hT : T.IsMinimal) (hg : 2 ≤ T.arithmeticGenus) {i : T.Component}
    (hi : T.IsMinusTwoIndex i) :
    (T.multiplicity i : ℤ) * |T.intersection i i| ≤ 768 * T.arithmeticGenus - 768 := by
  have h : 1 < Fintype.card T.Component := T.one_lt_card_of_intersection_self_ne_zero <| by
    rw [(T.isMinusTwoIndex_iff.mp hi).2]
    have := (T.weight i).pos
    omega
  obtain ⟨S, hiS, hS, hcard, hconn, hclosed⟩ := exists_finset_of_isMinusTwoIndex hg h hi
  have hself : ∀ x ∈ S, T.intersection x x = -(2 * (T.weight x : ℤ)) := fun x hx ↦
    (T.isMinusTwoIndex_iff.mp (hS x hx)).2
  -- the doubling bound starts at a component of `S` meeting a component outside `S`
  obtain ⟨x, hxS, y, hyS, hxy⟩ := T.exists_mem_notMem_adj (S : Set T.Component) ⟨i, hiS⟩
    fun hu ↦ (exists_notMem_of_card_lt hcard).elim fun k hk ↦
      hk (Finset.mem_coe.mp (hu ▸ Set.mem_univ k))
  have hy := hT.multiplicity_mul_abs_intersection_self_le h
    (hclosed x hxS y hyS (T.adj_iff.mp hxy).2)
  have hx : (T.multiplicity x : ℤ) * |T.intersection x x| ≤
      2 ^ (0 + 1) * (6 * T.arithmeticGenus - 6) :=
    le_two_pow_succ_mul (hself x hxS) (T.adj_iff.mp hxy).2 (by simpa using hy)
  have hfin : ∀ {n : ℕ} {z : T.Component}, n ≤ 7 →
      (T.multiplicity z : ℤ) * |T.intersection z z| ≤ 2 ^ n * (6 * T.arithmeticGenus - 6) →
      (T.multiplicity z : ℤ) * |T.intersection z z| ≤ 768 * T.arithmeticGenus - 768 := by
    intro n z hn hz
    have hpow : (2 : ℤ) ^ n ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) hn
    nlinarith
  rcases exists_chain_or_fork_or_exceptional hself hcard hconn with
    ⟨t, c, hc, rfl⟩ | ⟨t, c, b, hf, rfl⟩ | ⟨t, c, b, hc, ht5, ht7, hbne, -, hbpos, -, rfl⟩
  · obtain ⟨s, hs, rfl⟩ := mem_image.mp hiS
    rw [mem_range] at hs
    by_cases ht : 4 < t
    · -- a long chain: the concavity bound
      have := hc.multiplicity_mul_abs_intersection_self_le hT (hc.card_image_range ▸ hcard) ht
        (fun r hr k hk hpos ↦ hclosed _ (mem_image_of_mem c (mem_range.mpr hr)) k
          (fun hkS ↦ by
            obtain ⟨q, hq, rfl⟩ := mem_image.mp hkS
            exact hk q (mem_range.mp hq) rfl) hpos) hs
      linarith
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp hxS
      rw [mem_range] at hr
      exact hfin (by omega) (hc.le_two_pow_add_mul hr hx (r - s + (s - r)) s (by omega) hs)
  · -- a fork: the concavity bound
    have hc := hf.toIsSelfIntersectionMinusTwoChain
    have hbr : b ∉ (range t).image c := fun hb ↦ by
      obtain ⟨q, hq, hbq⟩ := mem_image.mp hb
      exact hf.branch_ne q (mem_range.mp hq) hbq.symm
    have hcard' : t + 1 < Fintype.card T.Component := by
      rwa [card_insert_of_notMem hbr, hc.card_image_range] at hcard
    have hfclosed : ∀ z, (z = b ∨ ∃ r < t, z = c r) → ∀ k, k ≠ b → (∀ s < t, k ≠ c s) →
        0 < T.intersection z k → ¬ T.IsMinusTwoIndex k := by
      intro z hz k hkb hkc hpos
      refine hclosed z ?_ k ?_ hpos
      · rcases hz with rfl | ⟨r, hr, rfl⟩
        exacts [mem_insert_self _ _, mem_insert_of_mem (mem_image_of_mem c (mem_range.mpr hr))]
      · rw [mem_insert, mem_image]
        rintro (rfl | ⟨q, hq, rfl⟩)
        exacts [hkb rfl, hkc q (mem_range.mp hq) rfl]
    rcases mem_insert.mp hiS with rfl | hiS
    · have := hf.multiplicity_mul_abs_intersection_self_le_branch hT hcard' hfclosed
      linarith
    · obtain ⟨s, hs, rfl⟩ := mem_image.mp hiS
      have := hf.multiplicity_mul_abs_intersection_self_le hT hcard' hfclosed (mem_range.mp hs)
      linarith
  · -- an exceptional configuration: walk along the chain, through the leaf `b` if necessary
    have hb : T.intersection b b = -(2 * (T.weight b : ℤ)) := hself b (mem_insert_self _ _)
    have hbpos' : 0 < T.intersection b (c (t - 3)) := T.intersection_comm b _ ▸ hbpos
    rcases mem_insert.mp hxS with rfl | hxS
    · -- the walk starts at the leaf `x = b`
      have hx' := le_two_pow_succ_mul (hc.intersection_self (t - 3) (by omega)) hbpos hx
      rcases mem_insert.mp hiS with rfl | hiS
      · exact hfin (by omega) hx
      · obtain ⟨s, hs, rfl⟩ := mem_image.mp hiS
        rw [mem_range] at hs
        exact hfin (by omega) (hc.le_two_pow_add_mul (by omega) hx'
          (t - 3 - s + (s - (t - 3))) s (by omega) hs)
    · obtain ⟨r, hr, rfl⟩ := mem_image.mp hxS
      rw [mem_range] at hr
      rcases mem_insert.mp hiS with rfl | hiS
      · have h3 := hc.le_two_pow_add_mul hr hx (r - (t - 3) + (t - 3 - r)) (t - 3) (by omega)
          (by omega)
        exact hfin (by omega) (le_two_pow_succ_mul hb hbpos' h3)
      · obtain ⟨s, hs, rfl⟩ := mem_image.mp hiS
        rw [mem_range] at hs
        exact hfin (by omega) (hc.le_two_pow_add_mul hr hx (r - s + (s - r)) s (by omega) hs)

/-- **The multiplicities of a minimal numerical type are bounded.** In a minimal numerical type of
genus `g ≥ 2`, every multiplicity-weighted intersection number satisfies
`mᵢ|aᵢⱼ| ≤ 768g - 768`. In particular `mᵢ|aᵢⱼ| ≤ 768g`, which is
[Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W). -/
theorem IsMinimal.multiplicity_mul_abs_intersection_le (hT : T.IsMinimal)
    (hg : 2 ≤ T.arithmeticGenus) (i j : T.Component) :
    (T.multiplicity i : ℤ) * |T.intersection i j| ≤ 768 * T.arithmeticGenus - 768 := by
  by_cases h : 1 < Fintype.card T.Component
  swap
  · rw [T.intersection_eq_zero_of_card_eq_one (le_antisymm (not_lt.mp h) Fintype.card_pos)]
    simp only [abs_zero, mul_zero]
    linarith
  -- it suffices to bound the weighted self-intersection `mⱼ|aⱼⱼ|`
  have hj : (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 768 * T.arithmeticGenus - 768 := by
    by_cases hj : T.IsMinusTwoIndex j
    · exact hT.multiplicity_mul_abs_intersection_self_le_of_isMinusTwoIndex hg hj
    · have := hT.multiplicity_mul_abs_intersection_self_le h hj
      linarith
  rcases eq_or_ne i j with rfl | hij
  · exact hj
  · rw [abs_of_nonneg (T.offDiagonal_nonneg i j hij)]
    exact (T.multiplicity_mul_intersection_le i j).trans hj

end Minimal

end NumericalType

end TauCeti
