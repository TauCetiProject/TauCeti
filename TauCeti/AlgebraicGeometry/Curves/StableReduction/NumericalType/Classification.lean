/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.DoubleFork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.E8
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Exceptional

/-!
# Connected proper sets of `(-2)`-indices

Let `S` be a set of components of a numerical type, each of self-intersection `aᵢᵢ = -2wᵢ`, which
is connected, in the sense that no nonempty proper subset of `S` is disjoint from the rest of
`S`, and which is a proper subset of the components. This file proves that the configuration
formed by `S` has Dynkin-diagram shape
([Stacks, Proposition 55.5.17](https://stacks.math.columbia.edu/tag/0C8Q)): one of the following
holds.

* `S` is the set of components of a chain `c 0 - c 1 - ⋯ - c (t - 1)`
  (`TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain`), the types `A`, `B`, `C` and `G₂`.
* `S` is the set of components of a fork, a chain of at least three components together with a
  leaf meeting its penultimate component (`TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork`),
  the type `D`.
* `S` consists of a chain of five, six or seven components together with a leaf meeting the
  component `c 2` and no other component of the chain: the types `E₆`, `E₇` and `E₈`.

Since the exceptional sets have at most eight elements, a connected proper set of at least nine
such components is a chain or a fork. The
weights and intersection numbers of each shape are determined by the classifications already
available: `IsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end` for chains,
`IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq` for forks, and
`exists_weight_intersection_branch_six_eq`, `exists_weight_intersection_branch_seven_eq` and
`IsSelfIntersectionMinusTwoChain.exists_weight_intersection_branch_eight_eq` for the exceptional
types. This is the input for the bound on the multiplicities of a minimal numerical type in
[Stacks, Lemma 55.7.3](https://stacks.math.columbia.edu/tag/0C9W), where a maximal connected set
of `(-2)`-indices is either small or a chain or a fork, the two shapes treated in
`TauCeti/AlgebraicGeometry/Curves/StableReduction/NumericalType/MultiplicityBound.lean`.

## Main results

* `TauCeti.NumericalType.exists_chain_or_fork_or_exceptional`: the classification above.

## Implementation notes

The Stacks Project leaves the proof of Proposition 55.5.17 to the discussion at the start of
[Section 55.5](https://stacks.math.columbia.edu/tag/0C7L). The argument here starts from a longest
chain `c` inside `S`. A component of `S` outside the chain that meets it meets exactly one of its
components, an interior one: otherwise the chain could be lengthened or would close up into a
cycle, which `IsSelfIntersectionMinusTwoChain.intersection_eq_zero` excludes. Two such components
would form either a four-legged star (Stacks, Lemma 55.5.6) or a chain with leaves at both ends
(Stacks, Lemma 55.5.11), and such a component meeting a further component of `S` would, by
maximality of `c`, form an affine `E₆` diagram (Stacks, Lemma 55.5.12). So `S` is the chain
together with at most one leaf. A leaf at the second or penultimate component gives a fork, and
the affine `E₇` and `E₈` diagrams (Stacks, Lemmas 55.5.15 and 55.5.16) confine every other
position of the leaf to the exceptional types.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable {T : NumericalType.{u}}

/-- Every set of components contains a longest chain. -/
private lemma exists_chain_forall_le (S : Finset T.Component) :
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

/-- The components of a chain read backwards are those of the chain. -/
private lemma image_range_reverse (t : ℕ) (c : ℕ → T.Component) :
    (range t).image (fun i ↦ c (t - 1 - i)) = (range t).image c := by
  conv_rhs => rw [← range_image_pred_top_sub t, image_image]
  rfl

/-- A property of a component and of the first `t` terms of a sequence holds for the first
`t + 1` terms of the sequence with that component prepended. -/
private lemma forall_lt_succ_cons {P : T.Component → Prop} {x : T.Component}
    {d : ℕ → T.Component} {t : ℕ} (hx : P x) (hd : ∀ i < t, P (d i)) :
    ∀ i < t + 1, P (if i = 0 then x else d (i - 1)) := by
  intro i hi
  split_ifs
  · exact hx
  · exact hd _ (by omega)

namespace IsSelfIntersectionMinusTwoChain

variable {t : ℕ} {c : ℕ → T.Component}

/-- A component `x` outside a chain meets at most one of its components, provided the numerical
type has a component besides `x` and those of the chain: otherwise the chain would close up into
a cycle. -/
private lemma eq_of_intersection_pos (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 1 < Fintype.card T.Component) {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r s : ℕ} (hs : s < t)
    (hr : 0 < T.intersection (c r) x) (hrs : r ≤ s) (hsx : 0 < T.intersection (c s) x) :
    r = s := by
  by_contra hne
  -- `x, c s, c (s - 1), …, c r` is a chain whose two ends meet.
  have hd := ((hc.shift (r := r) (s := s - r + 1) (by omega)).reverse).cons
    (fun i hi ↦ hx_ne _ (by omega)) hx_self (by
      rw [T.intersection_comm]
      simpa [show r + (s - r) = s by omega] using hsx)
  have h := hd.intersection_eq_zero (by omega) (p := 0) (q := s - r + 1) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel, Nat.sub_self,
    Nat.add_zero] at h
  rw [T.intersection_comm] at h
  omega

/-- Two distinct components outside a chain cannot both meet interior components of the chain,
provided the numerical type has a component besides them and those of the chain: they would form
a four-legged star or a chain with leaves at both ends. -/
private lemma false_of_two_leaves (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 2 < Fintype.card T.Component) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hy_self : T.intersection y y = -(2 * (T.weight y : ℤ))) {r s : ℕ} (hr0 : 0 < r)
    (hrs : r ≤ s) (hst : s + 1 < t) (hx : 0 < T.intersection (c r) x)
    (hy : 0 < T.intersection (c s) y) : False := by
  rcases hrs.eq_or_lt with rfl | hrs
  · -- `c r` would meet `c (r - 1)`, `c (r + 1)`, `x` and `y`: a four-legged star.
    have h := T.intersection_eq_zero_of_star_five (by omega) (hc.intersection_self r (by omega))
      (hc.intersection_self (r - 1) (by omega)) (hc.intersection_self (r + 1) (by omega))
      hx_self hy_self (hy_ne r (by omega)).symm (hc.ne (by omega) (by omega) (by omega))
      (hx_ne (r - 1) (by omega)).symm (hy_ne (r - 1) (by omega)).symm
      (hx_ne (r + 1) (by omega)).symm (hy_ne (r + 1) (by omega)).symm hxy
      (by rw [T.intersection_comm]; exact hc.intersection_pos (by omega) (by omega))
      (hc.intersection_succ_pos r (by omega)) hx
    omega
  · -- The block `c (r - 1), …, c (s + 1)` would carry leaves at both its second and its
    -- penultimate component.
    have hd := hc.shift (r := r - 1) (s := s - r + 3) (by omega)
    refine IsSelfIntersectionMinusTwoFork.not_oppositeFork (t := s - r + 3)
      (c := fun k ↦ c (r - 1 + k)) (right := y) (left := x) ?_ ?_ (by omega) (by omega)
    · exact ⟨hd, by omega, fun i hi ↦ hy_ne _ (by omega), hy_self, by
        simpa [show r - 1 + (s - r + 1) = s by omega] using hy⟩
    · exact ⟨hd.reverse, by omega, fun i hi ↦ hx_ne _ (by omega), hx_self, by
        simpa [show r - 1 + 1 = r by omega] using hx⟩

/-- A leaf meeting a chain at the position `r`, with `2 ≤ r` and at least `r` further
components after position `r`, can only sit at position `2` of a chain of at most seven
components: otherwise the chain and the leaf contain an affine `E₇` or `E₈` diagram. -/
private lemma eq_two_and_le_seven (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 1 < Fintype.card T.Component) {x : T.Component} (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r : ℕ} (hr : 2 ≤ r)
    (hrt : 2 * r + 1 ≤ t) (hx : 0 < T.intersection (c r) x) : r = 2 ∧ t ≤ 7 := by
  by_cases hr3 : 3 ≤ r
  · -- `c (r - 3), …, c (r + 3)` with the leaf `x` at its middle is an affine `E₇` diagram.
    have h := IsSelfIntersectionMinusTwoChain.intersection_branch_eq_zero T
      (hc.shift (r := r - 3) (s := 7) (by omega)) (by omega) (branch := x)
      (fun i hi ↦ hx_ne _ (by omega)) hx_self
    simp only [show r - 3 + 3 = r by omega] at h
    omega
  refine ⟨by omega, not_lt.mp fun ht ↦ ?_⟩
  obtain rfl : r = 2 := by omega
  -- `c 7, c 6, …, c 0` with the leaf `x` at `c 2` is an affine `E₈` diagram.
  exact (hc.mono (s := 8) (by omega)).reverse.not_affineE8 (by omega)
    (fun i hi ↦ hx_ne _ (by omega)) hx_self (by simpa using hx)

/-- A leaf `x` meeting a chain at the position `r`, with at least two components of the chain on
either side, meets no further component `y` outside the chain, provided the numerical type has a
component besides `x`, `y` and those of the chain: `c (r - 2), …, c (r + 2)`, `x`, `y` would be an
affine `E₆` diagram. -/
private lemma intersection_eq_zero_of_leaf (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcard : t + 2 < Fintype.card T.Component) {x y : T.Component} (hxy : x ≠ y)
    (hx_ne : ∀ i < t, x ≠ c i) (hy_ne : ∀ i < t, y ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ)))
    (hy_self : T.intersection y y = -(2 * (T.weight y : ℤ))) {r : ℕ} (hr : 2 ≤ r)
    (hrt : r + 3 ≤ t) (hx : 0 < T.intersection (c r) x) : T.intersection x y = 0 :=
  T.intersection_eq_zero_of_branch_six (by omega)
    (hc.intersection_self (r - 2) (by omega)) (hc.intersection_self (r - 1) (by omega))
    (hc.intersection_self r (by omega)) (hc.intersection_self (r + 1) (by omega))
    (hc.intersection_self (r + 2) (by omega)) hx_self hy_self
    (hc.ne (by omega) (by omega) (by omega)) (hc.ne (by omega) (by omega) (by omega))
    (hc.ne (by omega) (by omega) (by omega)) (hx_ne _ (by omega)).symm
    (hy_ne _ (by omega)).symm (hc.ne (by omega) (by omega) (by omega))
    (hc.ne (by omega) (by omega) (by omega)) (hx_ne _ (by omega)).symm
    (hy_ne _ (by omega)).symm (hc.ne (by omega) (by omega) (by omega))
    (hy_ne _ (by omega)).symm (hx_ne _ (by omega)).symm (hy_ne _ (by omega)).symm
    (hx_ne _ (by omega)).symm (hy_ne _ (by omega)).symm hxy
    (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega))
    (hc.intersection_pos (by omega) (by omega)) (hc.intersection_pos (by omega) (by omega)) hx

variable {S : Finset T.Component}

/-- A component of `S` outside a longest chain in `S` does not meet the first component of the
chain, since prepending it would give a longer chain. -/
private lemma not_intersection_pos_zero (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcS : ∀ i < t, c i ∈ S)
    (hmax : ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t)
    {x : T.Component} (hxS : x ∈ S) (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) :
    ¬ 0 < T.intersection (c 0) x := fun hpos ↦ by
  have := hmax _ _ (hc.cons hx_ne hx_self (by rwa [T.intersection_comm]))
    (forall_lt_succ_cons hxS hcS)
  omega

/-- A component of `S` outside a longest chain in `S` can only meet interior components of the
chain. -/
private lemma pos_and_lt_of_intersection_pos (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hcS : ∀ i < t, c i ∈ S)
    (hmax : ∀ t' c', T.IsSelfIntersectionMinusTwoChain t' c' → (∀ i < t', c' i ∈ S) → t' ≤ t)
    {x : T.Component} (hxS : x ∈ S) (hx_ne : ∀ i < t, x ≠ c i)
    (hx_self : T.intersection x x = -(2 * (T.weight x : ℤ))) {r : ℕ} (hr : r < t)
    (hx : 0 < T.intersection (c r) x) : 0 < r ∧ r + 1 < t := by
  refine ⟨Nat.pos_of_ne_zero fun h ↦
      hc.not_intersection_pos_zero hcS hmax hxS hx_ne hx_self (h ▸ hx),
    not_le.mp fun h ↦ hc.reverse.not_intersection_pos_zero (fun i hi ↦ hcS _ (by omega)) hmax
      hxS (fun i hi ↦ hx_ne _ (by omega)) hx_self ?_⟩
  simpa [show t - 1 = r by omega] using hx

end IsSelfIntersectionMinusTwoChain

/-- **Classification of connected proper sets of `(-2)`-indices.** Let `S` be a proper subset of
the components of a numerical type, each of self-intersection `-2w`, which is connected: every
nonempty proper subset of `S` meets a component of `S` outside it. Then `S` is the set of
components of a chain, or of a fork, or of a chain of five, six or seven components together with
a leaf meeting `c 2` and no other component of the chain. These are the Dynkin diagrams of types
`A` (with `B`, `C` and `G₂`), `D` and `E₆`, `E₇`, `E₈`
([Stacks, Proposition 55.5.17](https://stacks.math.columbia.edu/tag/0C8Q)). -/
theorem exists_chain_or_fork_or_exceptional {S : Finset T.Component}
    (hS : ∀ i ∈ S, T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hcard : #S < Fintype.card T.Component)
    (hconn : ∀ A ⊆ S, A.Nonempty → A ≠ S → ∃ i ∈ A, ∃ j ∈ S, j ∉ A ∧ 0 < T.intersection i j) :
    (∃ t c, T.IsSelfIntersectionMinusTwoChain t c ∧ (range t).image c = S) ∨
    (∃ t c b, T.IsSelfIntersectionMinusTwoFork t c b ∧ insert b ((range t).image c) = S) ∨
    ∃ t c b, T.IsSelfIntersectionMinusTwoChain t c ∧ 5 ≤ t ∧ t ≤ 7 ∧ (∀ i < t, b ≠ c i) ∧
      T.intersection b b = -(2 * (T.weight b : ℤ)) ∧ 0 < T.intersection (c 2) b ∧
      (∀ i < t, i ≠ 2 → T.intersection (c i) b = 0) ∧ insert b ((range t).image c) = S := by
  obtain ⟨t, c, hc, hcS, hmax⟩ := exists_chain_forall_le S
  set A := (range t).image c with hA_def
  by_cases hAS : A = S
  · exact .inl ⟨t, c, hc, hAS⟩
  have hAsub : A ⊆ S := fun x hx ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact hcS i (mem_range.mp hi)
  have mem_A {x : T.Component} : x ∈ A ↔ ∃ i < t, c i = x := by simp [hA_def]
  have ht : 0 < t := by
    by_contra ht
    obtain ⟨x, hx⟩ : S.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      exact hAS (subset_empty.mp hAsub)
    have := hmax 1 (fun _ ↦ x) ⟨by omega, fun _ _ ↦ hS x hx, by omega⟩ fun _ _ ↦ hx
    omega
  -- Some component `x` of `S` outside the chain meets the chain, at a position `r`.
  obtain ⟨b₀, hmem, x, hxS, hxA, hpos⟩ :=
    hconn A hAsub ⟨c 0, mem_A.mpr ⟨0, ht, rfl⟩⟩ hAS
  obtain ⟨r, hr, rfl⟩ := mem_A.mp hmem
  have hx_ne : ∀ i < t, x ≠ c i := fun i hi h ↦ hxA (mem_A.mpr ⟨i, hi, h.symm⟩)
  have hx_self := hS x hxS
  obtain ⟨hr0, hrt⟩ := hc.pos_and_lt_of_intersection_pos hcS hmax hxS hx_ne hx_self hr hpos
  have hAcard : #A = t := hc.card_image_range
  have hcard₁ : t + 1 < Fintype.card T.Component := by
    have := card_le_card (insert_subset hxS hAsub)
    rw [card_insert_of_notMem hxA, hAcard] at this
    omega
  -- `x` meets no other component of the chain.
  have hx_zero : ∀ i < t, i ≠ r → T.intersection (c i) x = 0 := by
    intro i hi hir
    refine le_antisymm (not_lt.mp fun hix ↦ hir ?_) (T.offDiagonal_nonneg _ _ (hx_ne i hi).symm)
    rcases le_total i r with h | h
    · exact hc.eq_of_intersection_pos hcard₁ hx_ne hx_self hr hix h hpos
    · exact (hc.eq_of_intersection_pos hcard₁ hx_ne hx_self hi hpos h hix).symm
  -- The chain and `x` exhaust `S`.
  have hS_eq : insert x A = S := by
    by_contra hne
    obtain ⟨b, hb, y, hyS, hyB, hby⟩ :=
      hconn (insert x A) (insert_subset hxS hAsub) (insert_nonempty _ _) hne
    have hyx : y ≠ x := fun h ↦ hyB (h ▸ mem_insert_self _ _)
    have hyA : y ∉ A := fun h ↦ hyB (mem_insert_of_mem h)
    have hy_ne : ∀ i < t, y ≠ c i := fun i hi h ↦ hyA (mem_A.mpr ⟨i, hi, h.symm⟩)
    have hy_self := hS y hyS
    have hcard₂ : t + 2 < Fintype.card T.Component := by
      have := card_le_card (insert_subset hyS (insert_subset hxS hAsub))
      rw [card_insert_of_notMem hyB, card_insert_of_notMem hxA, hAcard] at this
      omega
    rcases mem_insert.mp hb with hbx | hbA
    · -- `x` has a second neighbour `y` in `S`. By maximality of the chain, `y, x, c r, …` is
      -- no longer than the chain in either direction, so `x` is a leaf of an affine `E₆`
      -- diagram.
      rw [hbx] at hby
      have hright := hmax _ _
        (((hc.shift (r := r) (s := t - r) (by omega)).cons (fun i hi ↦ hx_ne _ (by omega))
          hx_self (by simpa [T.intersection_comm] using hpos)).cons
          (forall_lt_succ_cons (P := (y ≠ ·)) hyx fun i hi ↦ hy_ne (r + i) (by omega))
          hy_self (by simpa [T.intersection_comm] using hby))
        (forall_lt_succ_cons hyS (forall_lt_succ_cons hxS fun i hi ↦ hcS (r + i) (by omega)))
      have hleft := hmax _ _
        (((hc.reverse.shift (r := t - 1 - r) (s := r + 1) (by omega)).cons
          (fun i hi ↦ hx_ne _ (by omega)) hx_self
          (by simpa [T.intersection_comm, show t - 1 - (t - 1 - r) = r by omega] using hpos)).cons
          (forall_lt_succ_cons (P := (y ≠ ·)) hyx fun i hi ↦
            hy_ne (t - 1 - (t - 1 - r + i)) (by omega))
          hy_self (by simpa [T.intersection_comm] using hby))
        (forall_lt_succ_cons hyS (forall_lt_succ_cons hxS fun i hi ↦
          hcS (t - 1 - (t - 1 - r + i)) (by omega)))
      have h := hc.intersection_eq_zero_of_leaf hcard₂ hyx.symm hx_ne hy_ne hx_self hy_self
        (by omega) (by omega) hpos
      omega
    · -- `y` meets the chain at a position `s`; together with `x` this gives two leaves.
      obtain ⟨s, hs, rfl⟩ := mem_A.mp hbA
      obtain ⟨hs0, hst⟩ := hc.pos_and_lt_of_intersection_pos hcS hmax hyS hy_ne hy_self hs hby
      rcases le_total r s with hrs | hsr
      · exact hc.false_of_two_leaves hcard₂ hyx.symm hx_ne hy_ne hx_self hy_self hr0 hrs hst
          hpos hby
      · exact hc.false_of_two_leaves hcard₂ hyx hy_ne hx_ne hy_self hx_self hs0 hsr hrt hby hpos
  -- Read in the appropriate direction, the leaf `x` sits at a fork or an exceptional position.
  right
  by_cases hfork_right : r = t - 2
  · exact .inl ⟨t, c, x, ⟨hc, by omega, hx_ne, hx_self, hfork_right ▸ hpos⟩, hS_eq⟩
  by_cases hfork_left : r = 1
  · refine .inl ⟨t, fun i ↦ c (t - 1 - i), x, ⟨hc.reverse, by omega,
      fun i hi ↦ hx_ne _ (by omega), hx_self, ?_⟩, by rwa [image_range_reverse]⟩
    simpa [show t - 1 - (t - 2) = r by omega] using hpos
  right
  by_cases hdir : 2 * r + 1 ≤ t
  · obtain ⟨rfl, ht7⟩ := hc.eq_two_and_le_seven hcard₁ hx_ne hx_self (by omega) hdir hpos
    exact ⟨t, c, x, hc, by omega, ht7, hx_ne, hx_self, hpos, fun i hi hi2 ↦ hx_zero i hi hi2,
      hS_eq⟩
  · have hpos' : 0 < T.intersection (c (t - 1 - (t - 1 - r))) x := by
      rwa [show t - 1 - (t - 1 - r) = r by omega]
    obtain ⟨h2, ht7⟩ := hc.reverse.eq_two_and_le_seven hcard₁ (fun i hi ↦ hx_ne _ (by omega))
      hx_self (by omega) (by omega) hpos'
    refine ⟨t, fun i ↦ c (t - 1 - i), x, hc.reverse, by omega, ht7,
      fun i hi ↦ hx_ne _ (by omega), hx_self, by rwa [← h2], fun i hi hi2 ↦
        hx_zero _ (by omega) (by omega), by rwa [image_range_reverse]⟩

end NumericalType

end TauCeti
