/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.ProperSubgraph
import TauCeti.Algebra.BigOperators.Finset.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Chains of `(-2)`-indices of arbitrary length

A `(-2)`-index of a numerical type is a component `i` with `gᵢ = 0` and `aᵢᵢ = -2wᵢ`. The
configurations that a set of `(-2)`-indices can form inside a numerical type with strictly more
components are of Dynkin-diagram shape, and
`TauCeti/AlgebraicGeometry/Curves/StableReduction/NumericalType/ProperSubgraph.lean` classifies
those on at most six components. This file treats the one infinite family, a chain
`i₁ - i₂ - ⋯ - i_t` of any length, packaged as
`TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain`.

The underlying adjacency graph of such a chain in a numerical type with more components is a
path: no two of its components meet except along the chain, so in particular the chain never
closes up into a cycle.
From five components on, it also has at most one nonsimple edge, and that edge is at an end: all
its weights are equal except possibly at one end, where the weight may be the double or the half
of the common weight, and every edge has intersection number the larger of the weights of its two
endpoints by `TauCeti.NumericalType.intersection_eq_max_weight`. This is
[Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89), whose source statement is
restricted to more than five components because the five-component case is its Lemma 55.5.5.

## Main results

* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain`: the predicate recording a chain of
  components of self-intersection `-2w`.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_eq_zero`: two components of
  such a chain which are not consecutive do not meet, provided the numerical type has more
  components than the chain has length.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end`: the
  weights along such a chain of at least five components are constant except possibly at one
  end.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- `T.IsSelfIntersectionMinusTwoChain t c` says that `c 0, …, c (t - 1)` are `t` distinct
components of the numerical type `T`, each of self-intersection `aᵢᵢ = -2wᵢ`, in which
consecutive components meet.
Positions are indexed by `ℕ`, with only the values below `t` constrained, so that a block of
consecutive positions is again a chain for the shifted index function.

This is weaker than asking each `c i` to be a `TauCeti.NumericalType.IsMinusTwoIndex`, which
also requires `gᵢ = 0`: the genus plays no role in the classification of the configurations that
`(-2)`-indices form, exactly as in the fixed-length classifications of
[Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L) already available. -/
structure IsSelfIntersectionMinusTwoChain (t : ℕ) (c : ℕ → T.Component) : Prop where
  /-- The components of the chain are pairwise distinct. -/
  injOn : ∀ i < t, ∀ j < t, c i = c j → i = j
  /-- Every component of the chain has self-intersection `-2w`. -/
  intersection_self : ∀ i < t, T.intersection (c i) (c i) = -(2 * (T.weight (c i) : ℤ))
  /-- Consecutive components of the chain meet. -/
  intersection_succ_pos : ∀ i, i + 1 < t → 0 < T.intersection (c i) (c (i + 1))

variable {T}

namespace IsSelfIntersectionMinusTwoChain

variable {t : ℕ} {c : ℕ → T.Component}

/-- Distinct positions of a chain carry distinct components. -/
lemma ne (hc : T.IsSelfIntersectionMinusTwoChain t c) {i j : ℕ} (hi : i < t) (hj : j < t)
    (hij : i ≠ j) : c i ≠ c j := fun h ↦ hij (hc.injOn i hi j hj h)

/-- Consecutive components of a chain meet, in the form in which the successor position is
given by an equation rather than syntactically. -/
lemma intersection_pos (hc : T.IsSelfIntersectionMinusTwoChain t c) {i j : ℕ} (hij : j = i + 1)
    (hj : j < t) : 0 < T.intersection (c i) (c j) := by
  subst hij
  exact hc.intersection_succ_pos i hj

/-- An initial block of a chain is again a chain. -/
lemma mono (hc : T.IsSelfIntersectionMinusTwoChain t c) {s : ℕ} (hs : s ≤ t) :
    T.IsSelfIntersectionMinusTwoChain s c where
  injOn i hi j hj h := hc.injOn i (by omega) j (by omega) h
  intersection_self i hi := hc.intersection_self i (by omega)
  intersection_succ_pos i hi := hc.intersection_succ_pos i (by omega)

/-- Any block of consecutive positions of a chain is again a chain. -/
lemma shift (hc : T.IsSelfIntersectionMinusTwoChain t c) {r s : ℕ} (hrs : r + s ≤ t) :
    T.IsSelfIntersectionMinusTwoChain s fun k ↦ c (r + k) where
  injOn i hi j hj h := by
    have := hc.injOn (r + i) (by omega) (r + j) (by omega) h
    omega
  intersection_self i hi := hc.intersection_self (r + i) (by omega)
  intersection_succ_pos i hi := hc.intersection_succ_pos (r + i) (by omega)

/-- A chain followed by a component outside the chain is injective on its first `t + 1` terms. -/
lemma injOn_snoc (hc : T.IsSelfIntersectionMinusTwoChain t c) {branch : T.Component}
    (hbranch_ne : ∀ i < t, branch ≠ c i) :
    ∀ i < t + 1, ∀ j < t + 1,
      (if i = t then branch else c i) = (if j = t then branch else c j) → i = j := by
  intro i hi j hj hij
  by_cases hit : i = t
  · by_cases hjt : j = t
    · exact hit.trans hjt.symm
    · simp only [hit, hjt, ↓reduceIte] at hij
      exact (hbranch_ne j (by omega) hij).elim
  · by_cases hjt : j = t
    · simp only [hit, hjt, ↓reduceIte] at hij
      exact (hbranch_ne i (by omega) hij.symm).elim
    · simp only [hit, hjt, ↓reduceIte] at hij
      exact hc.injOn i (by omega) j (by omega) hij

/-- A chain and a further distinct component contain at least `t + 1` components. -/
lemma le_card_snoc (hc : T.IsSelfIntersectionMinusTwoChain t c) {branch : T.Component}
    (hbranch_ne : ∀ i < t, branch ≠ c i) :
    t + 1 ≤ Fintype.card T.Component := by
  let e : Fin (t + 1) → T.Component := fun j ↦ if (j : ℕ) = t then branch else c j
  simpa using Fintype.card_le_of_injective e (by
    intro p q hpq
    apply Fin.ext
    exact hc.injOn_snoc hbranch_ne p (by omega) q (by omega) hpq)

/-- A chain read backwards is again a chain. -/
lemma reverse (hc : T.IsSelfIntersectionMinusTwoChain t c) :
    T.IsSelfIntersectionMinusTwoChain t fun i ↦ c (t - 1 - i) where
  injOn i hi j hj h := by
    have := hc.injOn (t - 1 - i) (by omega) (t - 1 - j) (by omega) h
    omega
  intersection_self i hi := hc.intersection_self (t - 1 - i) (by omega)
  intersection_succ_pos i hi := by
    rw [T.intersection_comm]
    exact hc.intersection_pos (by omega) (by omega)

/-- Prepending a component of self-intersection `-2w` which is not in a chain and meets its first
component gives a chain one component longer. -/
lemma cons (hc : T.IsSelfIntersectionMinusTwoChain t c) {x : T.Component}
    (hx_ne : ∀ i < t, x ≠ c i) (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hx_pos : 0 < T.intersection x (c 0)) :
    T.IsSelfIntersectionMinusTwoChain (t + 1) fun i ↦ if i = 0 then x else c (i - 1) where
  injOn i hi j hj h := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · simp only [↓reduceIte, hj0.ne'] at h
      exact (hx_ne (j - 1) (by omega) h).elim
    · simp only [↓reduceIte, hi0.ne'] at h
      exact (hx_ne (i - 1) (by omega) h.symm).elim
    · simp only [hi0.ne', hj0.ne', ↓reduceIte] at h
      have := hc.injOn (i - 1) (by omega) (j - 1) (by omega) h
      omega
  intersection_self i hi := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hx_self
    · simpa only [hi0.ne', ↓reduceIte] using hc.intersection_self (i - 1) (by omega)
  intersection_succ_pos i hi := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hx_pos
    · simpa only [hi0.ne', Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] using
        hc.intersection_pos (i := i - 1) (by omega) (by omega)

/-- A property of a component and of the first `t` terms of a sequence holds for the first
`t + 1` terms of the sequence with that component prepended. -/
lemma forall_lt_succ_cons {α : Type*} {P : α → Prop} {x : α} {d : ℕ → α} {t : ℕ}
    (hx : P x) (hd : ∀ i < t, P (d i)) :
    ∀ i < t + 1, P (if i = 0 then x else d (i - 1)) := by
  intro i hi
  split_ifs
  · exact hx
  · exact hd _ (by omega)

/-- The components of a chain of length `t` form a set of `t` components. -/
@[simp]
lemma card_image_range (hc : T.IsSelfIntersectionMinusTwoChain t c) :
    #((range t).image c) = t := by
  rw [card_image_of_injOn fun i hi j hj h ↦
    hc.injOn i (mem_range.mp hi) j (mem_range.mp hj) h, card_range]

end IsSelfIntersectionMinusTwoChain

/-- Every set of components contains a longest chain. -/
lemma exists_chain_forall_le (S : Finset T.Component) :
    ∃ t c, T.IsSelfIntersectionMinusTwoChain t c ∧ (∀ i < t, c i ∈ S) ∧
      ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t := by
  classical
  let P : ℕ → Prop := fun t ↦ ∃ c, T.IsSelfIntersectionMinusTwoChain t c ∧ ∀ i < t, c i ∈ S
  have hle : ∀ t, P t → t ≤ #S := by
    rintro t ⟨c, hc, hcS⟩
    rw [← hc.card_image_range]
    exact card_le_card fun x hx ↦ by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact hcS i (mem_range.mp hi)
  have hP0 : P 0 := by
    obtain ⟨x⟩ := T.componentNonempty
    exact ⟨fun _ ↦ x, ⟨by omega, by omega, by omega⟩, by omega⟩
  obtain ⟨c, hc, hcS⟩ := Nat.findGreatest_spec (Nat.zero_le _) hP0
  exact ⟨_, c, hc, hcS, fun t' c' hc' hc'S ↦
    Nat.le_findGreatest (hle t' ⟨c', hc', hc'S⟩) ⟨c', hc', hc'S⟩⟩

/-- If two meeting components of a numerical type have intersection number `aᵢⱼ = wᵢp = wⱼq`
with `pq = 1`, then they have equal weights. -/
private lemma weight_eq_of_ratio_eq_one {i j : T.Component} {p q : ℤ}
    (hp : T.intersection i j = (T.weight i : ℤ) * p)
    (hq : T.intersection i j = (T.weight j : ℤ) * q) (hij : 0 < T.intersection i j)
    (hpq : p * q = 1) : (T.weight i : ℤ) = (T.weight j : ℤ) := by
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hp0 : 0 < p := pos_of_mul_pos_right (hp ▸ hij) hwi.le
  have hq0 : 0 < q := pos_of_mul_pos_right (hq ▸ hij) hwj.le
  have hple : p ≤ p * q := le_mul_of_one_le_right hp0.le hq0
  have hqle : q ≤ p * q := le_mul_of_one_le_left hq0.le hp0
  have hp1 : p = 1 := by linarith
  have hq1 : q = 1 := by linarith
  rw [hp1, mul_one] at hp
  rw [hq1, mul_one] at hq
  rw [← hp, hq]

/-- If two meeting components of a numerical type have intersection number `aᵢⱼ = wᵢp = wⱼq`
with `pq = 2`, then one of their weights is twice the other. -/
private lemma weight_eq_of_ratio_eq_two {i j : T.Component} {p q : ℤ}
    (hp : T.intersection i j = (T.weight i : ℤ) * p)
    (hq : T.intersection i j = (T.weight j : ℤ) * q) (hij : 0 < T.intersection i j)
    (hpq : p * q = 2) :
    (T.weight i : ℤ) = 2 * (T.weight j : ℤ) ∨ 2 * (T.weight i : ℤ) = (T.weight j : ℤ) := by
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hp0 : 0 < p := pos_of_mul_pos_right (hp ▸ hij) hwi.le
  have hq0 : 0 < q := pos_of_mul_pos_right (hq ▸ hij) hwj.le
  have hple : p ≤ p * q := le_mul_of_one_le_right hp0.le hq0
  have hqle : q ≤ p * q := le_mul_of_one_le_left hq0.le hp0
  have hp2 : p ≤ 2 := by linarith
  have hq2 : q ≤ 2 := by linarith
  interval_cases p <;> interval_cases q
  · exact absurd hpq (by norm_num)
  · rw [mul_one] at hp
    exact Or.inl (by rw [← hp, hq]; ring)
  · rw [mul_one] at hq
    exact Or.inr (by rw [← hq, hp]; ring)
  · exact absurd hpq (by norm_num)

/-- The two ends of a chain of components of self-intersection `-2w` do not meet, as soon as the
numerical type has more components than the chain has length. -/
private lemma intersection_ends_eq_zero (T : NumericalType.{u}) (t : ℕ) :
    ∀ c : ℕ → T.Component, T.IsSelfIntersectionMinusTwoChain t c →
      t < Fintype.card T.Component → 2 < t → T.intersection (c 0) (c (t - 1)) = 0 := by
  induction t using Nat.strong_induction_on with
  | _ t IH =>
  intro c hc hcard ht
  -- Every chord other than the one joining the two ends joins the ends of a shorter subchain.
  have hsub : ∀ p q, p + 1 < q → q < t → (p ≠ 0 ∨ q ≠ t - 1) →
      T.intersection (c p) (c q) = 0 := by
    intro p q hpq hq hne
    have key := IH (q - p + 1) (by omega) (fun k ↦ c (p + k)) (hc.shift (by omega)) (by omega)
      (by omega)
    have hend : p + (q - p + 1 - 1) = q := by omega
    rwa [hend, Nat.add_zero] at key
  rcases lt_or_ge t 7 with h7 | h7
  · -- Up to six components the classification of proper subgraphs applies directly.
    interval_cases t
    · exact T.intersection_eq_zero_of_intersection_pos_of_intersection_pos (by omega)
        (hc.intersection_self 0 (by omega)) (hc.intersection_self 1 (by omega))
        (hc.intersection_self 2 (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
    · exact (T.intersection_eq_zero_of_chain_four (by omega)
        (hc.intersection_self 0 (by omega)) (hc.intersection_self 1 (by omega))
        (hc.intersection_self 2 (by omega)) (hc.intersection_self 3 (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega))).2.2
    · exact (T.intersection_eq_zero_of_chain_five (by omega)
        (hc.intersection_self 0 (by omega)) (hc.intersection_self 1 (by omega))
        (hc.intersection_self 2 (by omega)) (hc.intersection_self 3 (by omega))
        (hc.intersection_self 4 (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega))).2.2.1
    · exact (T.intersection_eq_zero_of_chain_six (by omega)
        (hc.intersection_self 0 (by omega)) (hc.intersection_self 1 (by omega))
        (hc.intersection_self 2 (by omega)) (hc.intersection_self 3 (by omega))
        (hc.intersection_self 4 (by omega)) (hc.intersection_self 5 (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
        (hc.intersection_pos (by omega) (by omega))).2.2.2.1
  · -- From seven components on, a chord between the two ends would close the chain into a cycle.
    by_contra hne
    have hpos : 0 < T.intersection (c 0) (c (t - 1)) :=
      (T.offDiagonal_nonneg _ _ (hc.ne (by omega) (by omega) (by omega))).lt_of_ne (Ne.symm hne)
    have hpos' : 0 < T.intersection (c (t - 1)) (c 0) := by
      rwa [T.intersection_comm]
    -- Five consecutive components of the cycle form a chain, whose two middle edges are simply
    -- laced. The five positions are given as explicit indices, so that the windows wrapping
    -- around the closing edge are covered too.
    have window : ∀ a b d e f : ℕ, a < t → b < t → d < t → e < t → f < t →
        a ≠ d → a ≠ e → a ≠ f → b ≠ e → b ≠ f → d ≠ f →
        0 < T.intersection (c a) (c b) → 0 < T.intersection (c b) (c d) →
        0 < T.intersection (c d) (c e) → 0 < T.intersection (c e) (c f) →
        T.intersection (c b) (c d) = (T.weight (c b) : ℤ) ∧
          T.intersection (c b) (c d) = (T.weight (c d) : ℤ) ∧
          T.intersection (c d) (c e) = (T.weight (c d) : ℤ) ∧
          T.intersection (c d) (c e) = (T.weight (c e) : ℤ) := by
      intro a b d e f ha hb hd he hf had hae haf hbe hbf hdf hab hbd hde hef
      exact T.intersection_eq_weight_of_chain_five (by omega)
        (hc.intersection_self a ha) (hc.intersection_self b hb) (hc.intersection_self d hd)
        (hc.intersection_self e he) (hc.intersection_self f hf)
        (hc.ne ha hd had) (hc.ne ha he hae) (hc.ne ha hf haf) (hc.ne hb he hbe)
        (hc.ne hb hf hbf) (hc.ne hd hf hdf) hab hbd hde hef
    set W : ℤ := (T.weight (c 1) : ℤ) with hWdef
    -- Every edge strictly inside the chain equals the weight of both of its endpoints.
    have hstep : ∀ j, 1 ≤ j → j + 2 < t →
        T.intersection (c j) (c (j + 1)) = (T.weight (c j) : ℤ) ∧
          T.intersection (c j) (c (j + 1)) = (T.weight (c (j + 1)) : ℤ) := by
      intro j h1 h2
      rcases eq_or_lt_of_le h1 with rfl | hj2
      · have key := window 0 1 2 3 4 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
          (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
        exact ⟨key.1, key.2.1⟩
      · have key := window (j - 2) (j - 1) j (j + 1) (j + 2) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
          (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
        exact ⟨key.2.2.1, key.2.2.2⟩
    have hwt : ∀ i, 1 ≤ i → i + 1 < t → (T.weight (c i) : ℤ) = W := by
      intro i
      induction i with
      | zero => intro h; exact absurd h (by omega)
      | succ n ih =>
        intro _ hn
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · rfl
        · have key := hstep n hn0 (by omega)
          rw [← ih hn0 (by omega), ← key.1, key.2]
    -- The two windows wrapping around the closing edge pin down the remaining data.
    have hwrap₁ := window (t - 3) (t - 2) (t - 1) 0 1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
      hpos' (hc.intersection_pos (by omega) (by omega))
    have hwrap₂ := window (t - 2) (t - 1) 0 1 2 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hc.intersection_pos (by omega) (by omega)) hpos'
      (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
    have hwtm2 : (T.weight (c (t - 2)) : ℤ) = W := hwt (t - 2) (by omega) (by omega)
    have hwtm1 : (T.weight (c (t - 1)) : ℤ) = W := by rw [← hwrap₁.2.1, hwrap₁.1, hwtm2]
    have hwt0 : (T.weight (c 0) : ℤ) = W := by rw [← hwrap₂.2.2.1, hwrap₂.2.2.2]
    have hwtall : ∀ i, i < t → (T.weight (c i) : ℤ) = W := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hwt0
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi) with h | h
      · have hi_last : i = t - 1 := by omega
        rw [hi_last]
        exact hwtm1
      · exact hwt i hi0 (by omega)
    have hclose : T.intersection (c (t - 1)) (c 0) = W := by rw [hwrap₁.2.2.1, hwtm1]
    have hedge : ∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = W := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hwrap₂.2.2.1, hwt0]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi) with h | h
      · have hi_penultimate : i = t - 2 := by omega
        have hsucc_penultimate : t - 2 + 1 = t - 1 := by omega
        rw [hi_penultimate, hsucc_penultimate, hwrap₁.1, hwtm2]
      · rw [(hstep i hi0 (by omega)).1, hwtall i (by omega)]
    have hedgeW : ∀ i j, j = i + 1 → j < t → T.intersection (c i) (c j) = W := by
      intro i j hij hj
      subst hij
      exact hedge i hj
    -- The cycle is affine: the all-ones vector makes every row of the intersection form vanish,
    -- which negative definiteness on a proper subset of the components forbids.
    refine T.not_forall_sum_intersection_mul_nonneg_of_pos (c := c) hc.injOn hcard
      (y := fun _ ↦ (1 : ℤ)) (fun _ _ ↦ by norm_num) ⟨0, by omega, one_pos⟩ ?_
    intro i hi
    simp only [mul_one]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Eq.ge (sum_range_eq_of_eq_zero_off_triple (a := 0) (b := 1) (d := t - 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun j hj _ _ hjt ↦ hsub 0 j (by omega) hj (Or.inr hjt))
        (by rw [hc.intersection_self 0 (by omega), hedgeW 0 1 rfl (by omega),
          T.intersection_comm (c 0) (c (t - 1)), hclose, hwt0]; ring))
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi) with h | h
    · obtain rfl : i = t - 1 := by omega
      exact Eq.ge (sum_range_eq_of_eq_zero_off_triple (a := 0) (b := t - 2) (d := t - 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun j hj hj0 _ _ ↦ by
          rw [T.intersection_comm]
          exact hsub j (t - 1) (by omega) (by omega) (Or.inl hj0))
        (by rw [hclose, T.intersection_comm (c (t - 1)) (c (t - 2)),
          hedgeW (t - 2) (t - 1) (by omega) (by omega), hc.intersection_self (t - 1) (by omega),
          hwtm1]; ring))
    · exact Eq.ge (sum_range_eq_of_eq_zero_off_triple (a := i - 1) (b := i) (d := i + 1) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun j hj _ _ _ ↦ by
          rcases lt_or_ge j i with hji | hji
          · rw [T.intersection_comm]
            exact hsub j i (by omega) (by omega) (Or.inr (by omega))
          · exact hsub i j (by omega) hj (Or.inl (by omega)))
        (by rw [T.intersection_comm (c i) (c (i - 1)), hedgeW (i - 1) i (by omega) (by omega),
          hedgeW i (i + 1) rfl (by omega), hc.intersection_self i (by omega),
          hwtall i (by omega)]; ring))

/-- Two components of a chain of components of self-intersection `-2w` which are not consecutive
in the chain do not meet, as soon as the numerical type has more components than the chain has
length. In particular such a chain is never a cycle and has no chords: its underlying adjacency
graph is a path.
This is the graph-shape half of
[Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89). -/
theorem IsSelfIntersectionMinusTwoChain.intersection_eq_zero {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : t < Fintype.card T.Component) {p q : ℕ}
    (hp : p < t) (hq : q < t) (hpq : p ≠ q) (hpq₁ : p + 1 ≠ q) (hqp₁ : q + 1 ≠ p) :
    T.intersection (c p) (c q) = 0 := by
  -- The two ends of the subchain joining the two positions do not meet.
  have ends : ∀ u v : ℕ, u + 1 < v → v < t → T.intersection (c u) (c v) = 0 := by
    intro u v huv hv
    have key := T.intersection_ends_eq_zero (v - u + 1) (fun k ↦ c (u + k)) (hc.shift (by omega))
      (by omega) (by omega)
    have hend : u + (v - u + 1 - 1) = v := by omega
    rwa [hend, Nat.add_zero] at key
  rcases lt_or_gt_of_ne hpq with h | h
  · exact ends p q (by omega) hq
  · rw [T.intersection_comm]
    exact ends q p (by omega) hp

namespace IsSelfIntersectionMinusTwoChain

/-- A component outside a chain meets at most one of its components, provided the numerical type
has a component besides it and those of the chain: otherwise the chain would close up into a
cycle. -/
lemma eq_of_intersection_pos {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : t + 1 < Fintype.card T.Component)
    {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r s : ℕ} (hs : s < t)
    (hr : 0 < T.intersection (c r) x) (hrs : r ≤ s) (hsx : 0 < T.intersection (c s) x) :
    r = s := by
  by_contra hne
  -- `x, c s, c (s - 1), …, c r` is a chain whose two ends meet.
  have hd := ((hc.shift (r := r) (s := s - r + 1) (by omega)).reverse).cons
    (fun i hi ↦ hx_ne _ (by omega)) hx_self (by
      rw [T.intersection_comm]
      -- The last position of the shifted block is position `s` in the original chain.
      simpa [show r + (s - r) = s by omega] using hsx)
  have h := hd.intersection_eq_zero (by omega) (p := 0) (q := s - r + 1) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel, Nat.sub_self,
    Nat.add_zero] at h
  rw [T.intersection_comm] at h
  omega

/-- The intersection entries of a proper simply laced chain with common weight `w`. -/
theorem intersection_eq_ite {t : ℕ} {c : ℕ → T.Component} {w : ℤ}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : t < Fintype.card T.Component)
    (hweight : ∀ i < t, (T.weight (c i) : ℤ) = w)
    (hedge : ∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w)
    {i j : ℕ} (hi : i < t) (hj : j < t) :
    T.intersection (c i) (c j) =
      if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    rw [hc.intersection_self i hi, hweight i hi]
  · simp only [hij, ↓reduceIte]
    by_cases hadj : i + 1 = j ∨ j + 1 = i
    · simp only [hadj, ↓reduceIte]
      rcases hadj with rfl | hji
      · exact hedge i (by omega)
      · rw [T.intersection_comm]
        subst i
        exact hedge j (by omega)
    · simp only [hadj, ↓reduceIte]
      exact hc.intersection_eq_zero hcard hi hj hij (by omega) (by omega)

end IsSelfIntersectionMinusTwoChain

/-- In a proper chain with at least two components, the left-end row of an intersection sum
has only its diagonal and adjacent terms. -/
theorem IsSelfIntersectionMinusTwoChain.left_sum_eq {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : t < Fintype.card T.Component)
    (ht : 1 < t) (y : ℕ → ℤ) :
    ∑ j ∈ range t, T.intersection (c 0) (c j) * y j =
      T.intersection (c 0) (c 0) * y 0 + T.intersection (c 0) (c 1) * y 1 := by
  exact sum_range_eq_of_eq_zero_off_pair (by omega) (by omega) (by omega)
    (fun j hj hj0 hj1 ↦ by
      rw [hc.intersection_eq_zero hcard (by omega) hj (by omega) (by omega) (by omega), zero_mul])
    rfl

/-- In a proper chain, an interior row of an intersection sum has only its two adjacent terms
and its diagonal term. -/
theorem IsSelfIntersectionMinusTwoChain.interior_sum_eq {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : t < Fintype.card T.Component)
    (y : ℕ → ℤ) {i : ℕ} (hi : 0 < i) (hit : i + 1 < t) :
    ∑ j ∈ range t, T.intersection (c i) (c j) * y j =
      T.intersection (c i) (c (i - 1)) * y (i - 1) +
        T.intersection (c i) (c i) * y i + T.intersection (c i) (c (i + 1)) * y (i + 1) := by
  exact sum_range_eq_of_eq_zero_off_triple (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (fun j hj hprev hself hnext ↦ by
      rcases lt_or_gt_of_ne hself with hji | hji
      · rw [T.intersection_comm,
          hc.intersection_eq_zero hcard hj (by omega) (by omega) (by omega) (by omega), zero_mul]
      · rw [hc.intersection_eq_zero hcard (by omega) hj (by omega) (by omega) (by omega), zero_mul])
    rfl

/-- In a proper chain with at least two components, the right-end row of an intersection sum
has only its diagonal and adjacent terms. -/
theorem IsSelfIntersectionMinusTwoChain.right_sum_eq {t : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain t c) (hcard : t < Fintype.card T.Component)
    (ht : 1 < t) (y : ℕ → ℤ) :
    ∑ j ∈ range t, T.intersection (c (t - 1)) (c j) * y j =
      T.intersection (c (t - 1)) (c (t - 2)) * y (t - 2) +
        T.intersection (c (t - 1)) (c (t - 1)) * y (t - 1) := by
  exact sum_range_eq_of_eq_zero_off_pair (by omega) (by omega) (by omega)
    (fun j hj hprev hself ↦ by
      rw [T.intersection_comm,
        hc.intersection_eq_zero hcard hj (by omega) (by omega) (by omega) (by omega), zero_mul])
    rfl


/-- The weight classification of a chain of components of self-intersection `-2w`. -/
private lemma exists_weight_eq_except_one_end_aux (T : NumericalType.{u}) (t : ℕ) :
    ∀ c : ℕ → T.Component, T.IsSelfIntersectionMinusTwoChain t c →
      t < Fintype.card T.Component → 4 < t →
      ∃ W : ℤ, 0 < W ∧ (∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = W) ∧
        ((T.weight (c 0) : ℤ) = W ∨ (T.weight (c 0) : ℤ) = 2 * W ∨
          2 * (T.weight (c 0) : ℤ) = W) ∧
        ((T.weight (c (t - 1)) : ℤ) = W ∨ (T.weight (c (t - 1)) : ℤ) = 2 * W ∨
          2 * (T.weight (c (t - 1)) : ℤ) = W) ∧
        ((T.weight (c 0) : ℤ) = W ∨ (T.weight (c (t - 1)) : ℤ) = W) := by
  induction t using Nat.strong_induction_on with
  | _ t IH =>
  intro c hc hcard ht
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt ht) with rfl | h6
  · -- Five components: the five-component classification already lists the three patterns.
    have hfive_pred : (5 : ℕ) - 1 = 4 := by norm_num
    rw [hfive_pred]
    obtain ⟨p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, e₁p, e₁q, e₂p, e₂q, e₃p, e₃q, e₄p, e₄q, hmem⟩ :=
      T.exists_intersection_ratio_chain_five_mem (by omega)
      (hc.intersection_self 0 (by omega)) (hc.intersection_self 1 (by omega))
      (hc.intersection_self 2 (by omega)) (hc.intersection_self 3 (by omega))
      (hc.intersection_self 4 (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
      (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
      (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hmid : p₂ * q₂ = 1 ∧ p₃ * q₃ = 1 := by
      rcases hmem with h | h | h <;> exact ⟨h.2.1, h.2.2.1⟩
    have hw₁₂ := weight_eq_of_ratio_eq_one e₂p e₂q (hc.intersection_pos (by omega) (by omega))
      hmid.1
    have hw₂₃ := weight_eq_of_ratio_eq_one e₃p e₃q (hc.intersection_pos (by omega) (by omega))
      hmid.2
    refine ⟨(T.weight (c 1) : ℤ), by simp, fun i h1 h2 ↦ by
      have h3 : i < 4 := by omega
      interval_cases i <;> omega, ?_, ?_, ?_⟩
    · -- the left end
      rcases (by rcases hmem with h | h | h <;> [exact Or.inl h.1; exact Or.inl h.1;
          exact Or.inr h.1] : p₁ * q₁ = 1 ∨ p₁ * q₁ = 2) with h | h
      · exact Or.inl (weight_eq_of_ratio_eq_one e₁p e₁q
          (hc.intersection_pos (by omega) (by omega)) h)
      · exact Or.inr (weight_eq_of_ratio_eq_two e₁p e₁q
          (hc.intersection_pos (by omega) (by omega)) h)
    · -- the right end
      rcases (by rcases hmem with h | h | h <;> [exact Or.inl h.2.2.2; exact Or.inr h.2.2.2;
          exact Or.inl h.2.2.2] : p₄ * q₄ = 1 ∨ p₄ * q₄ = 2) with h | h
      · exact Or.inl (by
          have := weight_eq_of_ratio_eq_one e₄p e₄q
            (hc.intersection_pos (by omega) (by omega)) h
          omega)
      · rcases weight_eq_of_ratio_eq_two e₄p e₄q (hc.intersection_pos (by omega) (by omega)) h
          with h' | h'
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl (by omega))
    · -- at most one end is exceptional
      rcases (by rcases hmem with h | h | h <;> [exact Or.inl h.1; exact Or.inl h.1;
          exact Or.inr h.2.2.2] : p₁ * q₁ = 1 ∨ p₄ * q₄ = 1) with h | h
      · exact Or.inl (weight_eq_of_ratio_eq_one e₁p e₁q
          (hc.intersection_pos (by omega) (by omega)) h)
      · exact Or.inr (by
          have := weight_eq_of_ratio_eq_one e₄p e₄q
            (hc.intersection_pos (by omega) (by omega)) h
          omega)
  · -- More components: cut one component off either end and compare the two readings.
    obtain ⟨W, hWpos, hWint, hW0, -, -⟩ :=
      IH (t - 1) (by omega) c (hc.mono (by omega)) (by omega) (by omega)
    obtain ⟨W', -, hW'int, -, hW'end, -⟩ :=
      IH (t - 1) (by omega) (fun k ↦ c (1 + k)) (hc.shift (by omega)) (by omega) (by omega)
    have hW'₂ : (T.weight (c 2) : ℤ) = W' := hW'int 1 (by omega) (by omega)
    have hWW : W = W' := (hWint 2 (by omega) (by omega)).symm.trans hW'₂
    have hint : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = W := by
      intro i h1 h2
      rcases lt_or_ge (i + 1) (t - 1) with h | h
      · exact hWint i h1 h
      · have key := hW'int (i - 1) (by omega) (by omega)
        have hshift : 1 + (i - 1) = i := by omega
        rw [hshift] at key
        rw [key, hWW]
    have hend : (T.weight (c (t - 1)) : ℤ) = W ∨ (T.weight (c (t - 1)) : ℤ) = 2 * W ∨
        2 * (T.weight (c (t - 1)) : ℤ) = W := by
      have hlast : (1 : ℕ) + (t - 1 - 1) = t - 1 := by omega
      rw [hlast] at hW'end
      rw [hWW]
      exact hW'end
    refine ⟨W, hWpos, hint, hW0, hend, ?_⟩
    -- If both ends were exceptional the chain would be an affine diagram.
    by_contra hcon
    have hcase₀ : (T.weight (c 0) : ℤ) = 2 * W ∨ 2 * (T.weight (c 0) : ℤ) = W :=
      hW0.resolve_left fun h ↦ hcon (Or.inl h)
    have hcaseₗ : (T.weight (c (t - 1)) : ℤ) = 2 * W ∨ 2 * (T.weight (c (t - 1)) : ℤ) = W :=
      hend.resolve_left fun h ↦ hcon (Or.inr h)
    -- Inside the chain every weight and every edge equals `W`.
    have hmidedge : ∀ i j, 0 < i → j = i + 1 → i + 2 < t → T.intersection (c i) (c j) = W := by
      intro i j h0 hj h2
      subst hj
      have hw₁ := hint i h0 (by omega)
      have hw₂ := hint (i + 1) (by omega) (by omega)
      rw [T.intersection_eq_max_weight (by omega) (hc.intersection_self i (by omega))
        (hc.intersection_self (i + 1) (by omega)) (hc.intersection_succ_pos i (by omega))]
      omega
    -- At an exceptional end the intersection form has a kernel entry `α ∈ {1, 2}`.
    have hendfactor : ∀ u v : ℕ, u < t → v < t → (T.weight (c v) : ℤ) = W →
        0 < T.intersection (c u) (c v) →
        ((T.weight (c u) : ℤ) = 2 * W ∨ 2 * (T.weight (c u) : ℤ) = W) →
        ∃ α : ℤ, 0 < α ∧ 2 * T.intersection (c u) (c v) = 2 * (T.weight (c u) : ℤ) * α ∧
          T.intersection (c u) (c v) * α = 2 * W := by
      intro u v hu hv hwv hposuv hcase
      rw [T.intersection_eq_max_weight (by omega) (hc.intersection_self u hu)
        (hc.intersection_self v hv) hposuv]
      rcases hcase with h | h
      · exact ⟨1, one_pos, by omega, by omega⟩
      · exact ⟨2, two_pos, by omega, by omega⟩
    obtain ⟨α, hα, hα₁, hα₂⟩ := hendfactor 0 1 (by omega) (by omega)
      (hint 1 (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega)) hcase₀
    obtain ⟨γ, hγ, hγ₁, hγ₂⟩ := hendfactor (t - 1) (t - 2) (by omega) (by omega)
      (hint (t - 2) (by omega) (by omega))
      (by rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega)) hcaseₗ
    set y : ℕ → ℤ := fun j ↦ if j = 0 then α else if j = t - 1 then γ else 2 with hydef
    have hy₀ : y 0 = α := by simp [hydef]
    have hyₗ : y (t - 1) = γ := by
      have h1 : t - 1 ≠ 0 := by omega
      simp [hydef, h1]
    have hy₂ : ∀ j, 0 < j → j < t - 1 → y j = 2 := by
      intro j h1 h2
      have e₁ : j ≠ 0 := by omega
      have e₂ : j ≠ t - 1 := by omega
      simp [hydef, e₁, e₂]
    refine T.not_forall_sum_intersection_mul_nonneg_of_pos (c := c) hc.injOn hcard
      (y := y) ?_ ⟨0, by omega, by rw [hy₀]; exact hα⟩ ?_
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | h1
      · rw [hy₀]; exact hα.le
      rcases lt_or_ge i (t - 1) with h2 | h2
      · rw [hy₂ i h1 h2]; norm_num
      · have hi_last : i = t - 1 := by omega
        rw [hi_last, hyₗ]
        exact hγ.le
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h1
    · rw [hc.left_sum_eq hcard (by omega) y, hy₀, hy₂ 1 (by omega) (by omega),
        hc.intersection_self 0 (by omega)]
      linarith [hα₁]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h1) with rfl | h2
    · rw [hc.interior_sum_eq hcard y (i := 1) (by omega) (by omega),
        T.intersection_comm (c 1) (c 0), hy₀, hy₂ 1 (by omega) (by omega),
        hy₂ 2 (by omega) (by omega), hc.intersection_self 1 (by omega),
        hint 1 (by omega) (by omega), hmidedge 1 2 (by omega) (by omega) (by omega)]
      linarith [hα₂]
    rcases lt_or_ge i (t - 2) with h3 | h3
    · rw [hc.interior_sum_eq hcard y (i := i) (by omega) (by omega),
        T.intersection_comm (c i) (c (i - 1)), hy₂ (i - 1) (by omega) (by omega),
        hy₂ i (by omega) (by omega), hy₂ (i + 1) (by omega) (by omega),
        hmidedge (i - 1) i (by omega) (by omega) (by omega),
        hmidedge i (i + 1) (by omega) (by omega) (by omega),
        hc.intersection_self i (by omega), hint i (by omega) (by omega)]
      ring_nf
      exact le_rfl
    rcases eq_or_lt_of_le h3 with h4 | h4
    · obtain rfl : i = t - 2 := h4.symm
      have hthird_last : t - 2 - 1 = t - 3 := by omega
      have hpenultimate_succ : t - 2 + 1 = t - 1 := by omega
      rw [hc.interior_sum_eq hcard y (i := t - 2) (by omega) (by omega),
        hthird_last, hpenultimate_succ,
        T.intersection_comm (c (t - 2)) (c (t - 3)),
        T.intersection_comm (c (t - 2)) (c (t - 1)),
        hy₂ (t - 3) (by omega) (by omega), hy₂ (t - 2) (by omega) (by omega), hyₗ,
        hmidedge (t - 3) (t - 2) (by omega) (by omega) (by omega),
        hc.intersection_self (t - 2) (by omega), hint (t - 2) (by omega) (by omega)]
      linarith [hγ₂]
    · obtain rfl : i = t - 1 := by omega
      rw [hc.right_sum_eq hcard (by omega) y, hy₂ (t - 2) (by omega) (by omega), hyₗ,
        hc.intersection_self (t - 1) (by omega)]
      linarith [hγ₁]

/-- The weights along a chain of components of self-intersection `-2w` in a numerical type with
more components than the chain has length are constant except possibly at one end, where the
weight may be twice or half the common interior weight. Together with
`TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_eq_zero` and
`TauCeti.NumericalType.intersection_eq_max_weight`, which turn these weights into the
intersection numbers, this is
[Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89). -/
theorem IsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end {t : ℕ}
    {c : ℕ → T.Component} (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t < Fintype.card T.Component) (ht : 4 < t) :
    ∃ W : ℤ, 0 < W ∧ (∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = W) ∧
      ((T.weight (c 0) : ℤ) = W ∨ (T.weight (c 0) : ℤ) = 2 * W ∨
        2 * (T.weight (c 0) : ℤ) = W) ∧
      ((T.weight (c (t - 1)) : ℤ) = W ∨ (T.weight (c (t - 1)) : ℤ) = 2 * W ∨
        2 * (T.weight (c (t - 1)) : ℤ) = W) ∧
      ((T.weight (c 0) : ℤ) = W ∨ (T.weight (c (t - 1)) : ℤ) = W) :=
  T.exists_weight_eq_except_one_end_aux t c hc hcard ht

end NumericalType

end TauCeti
