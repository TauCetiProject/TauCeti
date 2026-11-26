/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Data.Set.Finite.Lemmas
public import TauCeti.Combinatorics.Matroid.SymmExchange

/-!
# Bases of maximum weight

Let `M` be a matroid on `α` and `w : α → R` a weight with values in an ordered commutative
monoid. The weight of a finite set `X` is `∑ᶠ e ∈ X, w e`. A base of maximum weight
is a base whose weight is at least that of every other base.

For a matroid of finite rank, a base `B`, and weights in an ordered cancellative commutative
monoid, the following are equivalent:

1. `B` is a base of maximum weight;
2. *exchange*: whenever `e ∉ B`, `f ∈ B` and `insert e (B \ {f})` is a base, `w e ≤ w f`;
3. *thresholds*: for every `t`, the elements of `B` of weight at least `t` form a basis of the
   elements of `M.E` of weight at least `t`;
4. *domination*: for every base `B'` there is a bijection `φ` from `B'` onto `B` with
   `w e ≤ w (φ e)` for all `e ∈ B'`.

Conditions 2 and 3 are equivalent for every base of every matroid and every weight with values in
a preorder, and 2 implies 4 for every matroid of finite rank. Each of 2, 3 and 4 implies 1
in every ordered commutative monoid; the converse needs cancellation in `R`. With weights
in `WithTop ℕ`, two bases of weight `⊤` are both of maximum weight while only one of them may
satisfy 2.

Consequently, in a matroid of finite rank with weights in a cancellative monoid, two bases of
maximum weight have the same number of elements of each weight, and when the weight is injective
on the ground set the base of maximum weight is unique.

## Main declarations

* `Matroid.IsMaxWeightBase`: `B` is a base of maximum weight.
* `Matroid.exists_isMaxWeightBase`: a matroid with finite ground set has a base of maximum
  weight.
* `Matroid.IsBase.isMaxWeightBase_iff_forall_exchange`,
  `Matroid.IsBase.isMaxWeightBase_iff_forall_isBasis`,
  `Matroid.IsBase.isMaxWeightBase_iff_forall_exists_bijOn`: the three optimality criteria.
* `Matroid.IsMaxWeightBase.isBasis_inter_preimage`: a base of maximum weight meets the preimage
  of every upper set of weights in a basis of that preimage.
* `Matroid.IsMaxWeightBase.encard_inter_preimage_singleton_eq`: two bases of maximum weight have
  the same number of elements of each weight.
* `Matroid.IsMaxWeightBase.eq_of_injOn`: uniqueness for a weight injective on the ground set.

## References

* A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, 2017, Chapter 10.
-/

public section

open Set

namespace Matroid

variable {α R : Type*} {M : Matroid α} {w : α → R} {B B' : Set α} {e f : α}

/-- `M.IsMaxWeightBase w B` says that `B` is a base of `M` whose weight `∑ᶠ e ∈ B, w e` is at
least the weight of every base of `M`. The weight is meaningful for finite bases, so the theory
assumes `M.RankFinite` or a finite ground set. -/
structure IsMaxWeightBase [AddCommMonoid R] [LE R] (M : Matroid α) (w : α → R) (B : Set α) :
    Prop where
  /-- A base of maximum weight is a base. -/
  isBase : M.IsBase B
  /-- Every base weighs at most as much as a base of maximum weight. -/
  finsum_le : ∀ ⦃B'⦄, M.IsBase B' → ∑ᶠ e ∈ B', w e ≤ ∑ᶠ e ∈ B, w e

theorem isMaxWeightBase_iff [AddCommMonoid R] [LE R] :
    M.IsMaxWeightBase w B ↔ M.IsBase B ∧ ∀ ⦃B'⦄, M.IsBase B' → ∑ᶠ e ∈ B', w e ≤ ∑ᶠ e ∈ B, w e :=
  ⟨fun h ↦ ⟨h.isBase, h.finsum_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Two bases of maximum weight have the same weight. -/
theorem IsMaxWeightBase.finsum_eq [AddCommMonoid R] [PartialOrder R] (hB : M.IsMaxWeightBase w B)
    (hB' : M.IsMaxWeightBase w B') : ∑ᶠ e ∈ B, w e = ∑ᶠ e ∈ B', w e :=
  le_antisymm (hB'.finsum_le hB.isBase) (hB.finsum_le hB'.isBase)

/-- A matroid with finite ground set has a base of maximum weight, for weights in a commutative
monoid with a linear order; no compatibility between the order and the addition is needed. -/
theorem exists_isMaxWeightBase [AddCommMonoid R] [LinearOrder R] [M.Finite] (w : α → R) :
    ∃ B, M.IsMaxWeightBase w B := by
  have hfin : {B | M.IsBase B}.Finite :=
    M.ground_finite.finite_subsets.subset fun _ hB ↦ IsBase.subset_ground hB
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  obtain ⟨B, hB, hmax⟩ := Set.exists_max_image _ (fun B ↦ ∑ᶠ e ∈ B, w e) hfin ⟨B₀, hB₀⟩
  exact ⟨B, hB, hmax⟩

/-! ### Exchange and thresholds -/

/-- If no exchange `insert e (B \ {f})` that is again a base replaces `f` by a strictly heavier
element `e`, then for every upper set `U` of weights, the elements of `B` with weight in `U` form a
basis of the elements of `M.E` with weight in `U`. -/
theorem IsBase.isBasis_inter_preimage_of_forall_exchange [LE R] (hB : M.IsBase B)
    (h : ∀ ⦃e f⦄, e ∉ B → f ∈ B → M.IsBase (insert e (B \ {f})) → w e ≤ w f) {U : Set R}
    (hU : IsUpperSet U) : M.IsBasis (B ∩ w ⁻¹' U) (M.E ∩ w ⁻¹' U) := by
  refine (hB.indep.subset inter_subset_left).isBasis_of_forall_insert
    (inter_subset_inter_left _ hB.subset_ground) fun e ⟨⟨heE, heU⟩, heBU⟩ ↦ ?_
  have heB : e ∉ B := fun heB ↦ heBU ⟨heB, heU⟩
  rw [dep_iff, and_iff_left (insert_subset heE (inter_subset_left.trans hB.subset_ground))]
  intro hind
  -- The fundamental circuit of `e` in `B` is not inside the independent set `insert e (B ∩ _)`,
  -- so it contains some `f ∈ B` with weight outside `U`; exchanging `f` for `e` contradicts `h`.
  have hC := hB.fundCircuit_isCircuit heE heB
  obtain ⟨f, hfC, hfI⟩ := not_subset.1 fun hsub ↦ hC.not_indep (hind.subset hsub)
  have hfe : f ≠ e := fun hfe ↦ hfI (hfe ▸ mem_insert _ _)
  have hfB : f ∈ B := ((M.fundCircuit_subset_insert e B) hfC).resolve_left hfe
  rw [hB.mem_fundCircuit_iff_isBase_exchange heE heB hfe] at hfC
  exact hfI <| mem_insert_of_mem _ ⟨hfB, hU (h heB hfB hfC) heU⟩

section Preorder

variable [Preorder R]

/-- The exchange criterion implies the threshold criterion: if no exchange `insert e (B \ {f})`
replaces an element of `B` by a strictly heavier one, then for every `t` the elements of `B` of
weight at least `t` form a basis of the elements of `M.E` of weight at least `t`. -/
theorem IsBase.isBasis_inter_of_forall_exchange (hB : M.IsBase B)
    (h : ∀ ⦃e f⦄, e ∉ B → f ∈ B → M.IsBase (insert e (B \ {f})) → w e ≤ w f) (t : R) :
    M.IsBasis (B ∩ {e | t ≤ w e}) (M.E ∩ {e | t ≤ w e}) := by
  simpa only [preimage, mem_Ici] using
    hB.isBasis_inter_preimage_of_forall_exchange h (IsUpperSet.Ici t)

/-- The exchange criterion implies the domination criterion: for every base `B'` there is a
bijection from `B'` onto `B` that never decreases the weight. -/
theorem IsBase.exists_bijOn_of_forall_exchange [M.RankFinite] (hB : M.IsBase B)
    (h : ∀ ⦃e f⦄, e ∉ B → f ∈ B → M.IsBase (insert e (B \ {f})) → w e ≤ w f)
    (hB' : M.IsBase B') : ∃ φ : α → α, BijOn φ B' B ∧ ∀ e ∈ B', w e ≤ w (φ e) := by
  classical
  -- Induction on the number of elements of `B' \ B`.
  induction hn : (B' \ B).ncard generalizing B' with
  | zero =>
    have hsub : B' ⊆ B := sdiff_eq_empty.1 <|
      (ncard_eq_zero (hB'.finite.subset sdiff_subset)).1 hn
    obtain rfl := hB'.eq_of_subset_isBase hB hsub
    exact ⟨id, bijOn_id _, fun _ _ ↦ le_rfl⟩
  | succ n ih =>
    obtain ⟨e, heB', heB⟩ : (B' \ B).Nonempty := nonempty_of_ncard_ne_zero (by omega)
    -- Exchange `e` for some `f ∈ B \ B'` in both bases; the exchange criterion gives
    -- `w e ≤ w f`, and `insert f (B' \ {e})` has one element fewer outside `B`.
    obtain ⟨f, ⟨hfB, hfB'⟩, hB'', hBe⟩ := hB'.exists_symm_exchange hB ⟨heB', heB⟩
    have hset : insert f (B' \ {e}) \ B = (B' \ B) \ {e} := by
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      grind
    obtain ⟨φ, hφ, hφw⟩ := ih hB'' (by
      rw [hset, ncard_sdiff_singleton_of_mem (show e ∈ B' \ B from ⟨heB', heB⟩), hn]
      omega)
    refine ⟨φ ∘ Equiv.swap e f, hφ.comp (Equiv.swap_bijOn_exchange heB' hfB'), fun x hx ↦ ?_⟩
    by_cases hxe : x = e
    · subst hxe
      simpa using (h heB hfB hBe).trans (hφw f (mem_insert _ _))
    · have hxf : x ≠ f := by rintro rfl; exact hfB' hx
      simpa [Equiv.swap_apply_of_ne_of_ne hxe hxf] using hφw x (mem_insert_of_mem _ ⟨hx, hxe⟩)

/-- The threshold criterion implies the exchange criterion. -/
private theorem le_of_forall_isBasis_inter
    (h : ∀ t, M.IsBasis (B ∩ {e | t ≤ w e}) (M.E ∩ {e | t ≤ w e})) (he : e ∉ B)
    (hB' : M.IsBase (insert e (B \ {f}))) : w e ≤ w f := by
  by_contra hlt
  have heE : e ∈ M.E := hB'.subset_ground (mem_insert _ _)
  -- The elements of `B` at least as heavy as `e` span `e` and avoid `f`.
  have hsub : B ∩ {x | w e ≤ w x} ⊆ B \ {f} :=
    fun x hx ↦ ⟨hx.1, by rintro rfl; exact hlt hx.2⟩
  have hcl : e ∈ M.closure (B \ {f}) :=
    M.closure_subset_closure hsub ((h (w e)).subset_closure ⟨heE, le_rfl⟩)
  have hind := hB'.indep
  rw [(hB'.indep.subset (subset_insert _ _)).insert_indep_iff_of_notMem
    (fun heB ↦ he heB.1)] at hind
  exact hind.2 hcl

/-- For a base, the exchange criterion and the threshold criterion are equivalent. This holds in
every matroid and for weights with values in any preorder. -/
theorem IsBase.forall_exchange_iff_forall_isBasis (hB : M.IsBase B) :
    (∀ ⦃e f⦄, e ∉ B → f ∈ B → M.IsBase (insert e (B \ {f})) → w e ≤ w f) ↔
      ∀ t, M.IsBasis (B ∩ {e | t ≤ w e}) (M.E ∩ {e | t ≤ w e}) :=
  ⟨hB.isBasis_inter_of_forall_exchange, fun h _ _ he _ ↦ le_of_forall_isBasis_inter h he⟩

end Preorder

/-! ### The optimality criteria -/

section OrderedMonoid

variable [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- The domination criterion implies maximality, without cancellation in `R`. -/
theorem IsBase.isMaxWeightBase_of_forall_exists_bijOn [M.RankFinite] (hB : M.IsBase B)
    (h : ∀ ⦃B'⦄, M.IsBase B' → ∃ φ : α → α, BijOn φ B' B ∧ ∀ e ∈ B', w e ≤ w (φ e)) :
    M.IsMaxWeightBase w B := by
  refine ⟨hB, fun B' hB' ↦ ?_⟩
  obtain ⟨φ, hφ, hφw⟩ := h hB'
  have hfin := hB'.finite
  calc ∑ᶠ e ∈ B', w e ≤ ∑ᶠ e ∈ B', w (φ e) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
        exact Finset.sum_le_sum fun e he ↦ hφw e (hfin.mem_toFinset.1 he)
    _ = ∑ᶠ e ∈ B, w e := finsum_mem_eq_of_bijOn φ hφ fun _ _ ↦ rfl

/-- The exchange criterion implies maximality, without cancellation in `R`. -/
theorem IsBase.isMaxWeightBase_of_forall_exchange [M.RankFinite] (hB : M.IsBase B)
    (h : ∀ ⦃e f⦄, e ∉ B → f ∈ B → M.IsBase (insert e (B \ {f})) → w e ≤ w f) :
    M.IsMaxWeightBase w B :=
  hB.isMaxWeightBase_of_forall_exists_bijOn fun _ hB' ↦ hB.exists_bijOn_of_forall_exchange h hB'

/-- The threshold criterion implies maximality, without cancellation in `R`. -/
theorem IsBase.isMaxWeightBase_of_forall_isBasis [M.RankFinite] (hB : M.IsBase B)
    (h : ∀ t, M.IsBasis (B ∩ {e | t ≤ w e}) (M.E ∩ {e | t ≤ w e})) : M.IsMaxWeightBase w B :=
  hB.isMaxWeightBase_of_forall_exchange fun _ _ he _ ↦ le_of_forall_isBasis_inter h he

end OrderedMonoid

section OrderedCancelMonoid

variable [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

/-- In a base of maximum weight, no exchange `insert e (B \ {f})` that is again a base replaces
`f` by a strictly heavier element. This needs cancellation in `R`. -/
theorem IsMaxWeightBase.le_of_isBase_exchange [M.RankFinite] (hB : M.IsMaxWeightBase w B)
    (he : e ∉ B) (hf : f ∈ B) (hB' : M.IsBase (insert e (B \ {f}))) : w e ≤ w f := by
  have hle := hB.finsum_le hB'
  rw [finsum_mem_insert _ (show e ∉ B \ {f} from fun h ↦ he h.1)
      (hB.isBase.finite.subset sdiff_subset),
    ← finsum_mem_add_sdiff (singleton_subset_iff.2 hf) hB.isBase.finite,
    finsum_mem_singleton] at hle
  exact le_of_add_le_add_right hle

/-- **Exchange criterion.** A base `B` of a matroid of finite rank is of maximum weight if and
only if no exchange `insert e (B \ {f})` that is again a base replaces `f` by a strictly heavier
element `e`. -/
theorem IsBase.isMaxWeightBase_iff_forall_exchange [M.RankFinite] (hB : M.IsBase B) :
    M.IsMaxWeightBase w B ↔
      ∀ ⦃e f⦄, e ∉ B → f ∈ B → M.IsBase (insert e (B \ {f})) → w e ≤ w f :=
  ⟨fun h _ _ ↦ h.le_of_isBase_exchange, hB.isMaxWeightBase_of_forall_exchange⟩

/-- **Domination criterion.** A base `B` of a matroid of finite rank is of maximum weight if and
only if every base `B'` maps bijectively onto `B` by a map that never decreases the weight. -/
theorem IsBase.isMaxWeightBase_iff_forall_exists_bijOn [M.RankFinite] (hB : M.IsBase B) :
    M.IsMaxWeightBase w B ↔
      ∀ ⦃B'⦄, M.IsBase B' → ∃ φ : α → α, BijOn φ B' B ∧ ∀ e ∈ B', w e ≤ w (φ e) :=
  ⟨fun h _ hB' ↦ hB.exists_bijOn_of_forall_exchange (fun _ _ ↦ h.le_of_isBase_exchange) hB',
    hB.isMaxWeightBase_of_forall_exists_bijOn⟩

/-- In a base of maximum weight of a matroid of finite rank, for every upper set `U` of weights,
the elements with weight in `U` form a basis of the elements of the ground set with weight in
`U`. -/
theorem IsMaxWeightBase.isBasis_inter_preimage [M.RankFinite] (hB : M.IsMaxWeightBase w B)
    {U : Set R} (hU : IsUpperSet U) : M.IsBasis (B ∩ w ⁻¹' U) (M.E ∩ w ⁻¹' U) :=
  hB.isBase.isBasis_inter_preimage_of_forall_exchange (fun _ _ ↦ hB.le_of_isBase_exchange) hU

/-- **Threshold criterion.** A base `B` of a matroid of finite rank is of maximum weight if and
only if, for every `t`, the elements of `B` of weight at least `t` form a basis of the elements of
the ground set of weight at least `t`. -/
theorem IsBase.isMaxWeightBase_iff_forall_isBasis [M.RankFinite] (hB : M.IsBase B) :
    M.IsMaxWeightBase w B ↔ ∀ t, M.IsBasis (B ∩ {e | t ≤ w e}) (M.E ∩ {e | t ≤ w e}) := by
  rw [hB.isMaxWeightBase_iff_forall_exchange, hB.forall_exchange_iff_forall_isBasis]

/-- Two bases of maximum weight of a matroid of finite rank have, for every weight `r`, the same
number of elements of weight `r`. -/
theorem IsMaxWeightBase.encard_inter_preimage_singleton_eq [M.RankFinite]
    (hB : M.IsMaxWeightBase w B) (hB' : M.IsMaxWeightBase w B') (r : R) :
    (B ∩ w ⁻¹' {r}).encard = (B' ∩ w ⁻¹' {r}).encard := by
  -- Both bases meet `w ⁻¹' Ioi r` and `w ⁻¹' Ici r` in bases of the same sets, so in the same
  -- number of elements, and `w ⁻¹' Ici r` is the disjoint union of `w ⁻¹' Ioi r` and `w ⁻¹' {r}`.
  have hsplit (B : Set α) : (B ∩ w ⁻¹' Ici r).encard =
      (B ∩ w ⁻¹' Ioi r).encard + (B ∩ w ⁻¹' {r}).encard := by
    rw [← Ioi_union_left, preimage_union, inter_union_distrib_left]
    exact encard_union_eq (disjoint_left.2 fun _ hx hx' ↦ hx.2.ne' hx'.2)
  have hIci := (hB.isBasis_inter_preimage (IsUpperSet.Ici r)).encard_eq_eRk.trans
    (hB'.isBasis_inter_preimage (IsUpperSet.Ici r)).encard_eq_eRk.symm
  have hIoi := (hB.isBasis_inter_preimage (IsUpperSet.Ioi r)).encard_eq_eRk.trans
    (hB'.isBasis_inter_preimage (IsUpperSet.Ioi r)).encard_eq_eRk.symm
  rw [hsplit, hsplit, hIoi] at hIci
  exact (WithTop.add_left_inj
    ((hB'.isBase.finite.subset inter_subset_left).encard_lt_top.ne)).1 hIci

/-- If the weight is injective on the ground set, a matroid of finite rank has at most one base
of maximum weight. -/
theorem IsMaxWeightBase.eq_of_injOn [M.RankFinite] (hB : M.IsMaxWeightBase w B)
    (hB' : M.IsMaxWeightBase w B') (hw : InjOn w M.E) : B = B' := by
  by_contra hne
  obtain ⟨e, heB, heB'⟩ : (B \ B').Nonempty :=
    nonempty_of_not_subset fun hsub ↦ hne (hB.isBase.eq_of_subset_isBase hB'.isBase hsub)
  obtain ⟨f, ⟨hfB', hfB⟩, hBf, hB'e⟩ := hB.isBase.exists_symm_exchange hB'.isBase ⟨heB, heB'⟩
  have hfe := hB.le_of_isBase_exchange hfB heB hBf
  have hef := hB'.le_of_isBase_exchange heB' hfB' hB'e
  exact hfB (hw (hB'.isBase.subset_ground hfB') (hB.isBase.subset_ground heB)
    (le_antisymm hfe hef) ▸ heB)

end OrderedCancelMonoid

end Matroid
