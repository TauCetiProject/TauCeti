/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Minimal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounding multiplicities along `(-2)`-configurations

In a minimal numerical type of genus `g ≥ 2`, every multiplicity-weighted intersection number
`mᵢ|aᵢⱼ|` is at most `768g` ([Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W)).
The components that are not `(-2)`-indices already satisfy `mⱼ|aⱼⱼ| ≤ 6g - 6`
(`TauCeti.NumericalType.IsMinimal.multiplicity_mul_abs_intersection_self_le`). The work is to
propagate a bound into the configurations of `(-2)`-indices, which the classification of
[Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L) shows to be of Dynkin shape.
This file supplies the two propagation mechanisms of the Stacks proof.

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

For `t > 5`, [Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89) says that such a
chain is a path with equal weights, except possibly at one end where the weight may be twice or
half the common one. The `t = 5` case is supplied locally by the five-component classification
`TauCeti.NumericalType.exists_intersection_ratio_chain_five_mem`, through
`IsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end`.
The bound follows from the weighted maximum principle, with the test vector equal to `1` at a
component of twice the common weight and to `2` elsewhere. This is the concavity argument of the
proof of [Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W), for all three weight
patterns of the chain. -/
theorem IsSelfIntersectionMinusTwoChain.multiplicity_mul_abs_intersection_self_le
    (hT : T.IsMinimal) (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t < Fintype.card T.Component) (ht : 4 < t)
    (hclosed : ∀ r < t, ∀ k, (∀ s < t, k ≠ c s) → 0 < T.intersection (c r) k →
      ¬ T.IsMinusTwoIndex k)
    {r : ℕ} (hr : r < t) :
    (T.multiplicity (c r) : ℤ) * |T.intersection (c r) (c r)| ≤ 24 * T.arithmeticGenus - 24 := by
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

For `t > 4`, [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8D) says that the fork
is simply laced. The shorter cases `t = 3` and `t = 4` are supplied locally by
`exists_weight_intersection_eq_three` and `exists_weight_intersection_eq_four`, respectively,
through `IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq`.
The bound follows from the weighted maximum principle, with the test vector equal to `1` at the
two leaves `c (t - 1)` and `branch` and to `2` elsewhere; this is the concavity argument of the
proof of [Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W) for a fork. -/
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

end NumericalType

end TauCeti
