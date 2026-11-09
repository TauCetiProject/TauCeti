/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal
import TauCeti.Data.Finset.Basic

/-!
# The matched subalgebra of the strands algebra

A pointed matched circle `Z` has `4k` points on an oriented circle cut open at a basepoint, matched
in pairs. Lipshitz, Ozsváth and Thurston define the algebra `A(Z)` of bordered Heegaard Floer
homology as a subalgebra of the strands algebra `A(4k)`: it is spanned by the sums of strand
diagrams over all ways of placing each horizontal strand at one of the two points of a matched
pair, the diagrams having no two matched starting points and no two matched end points. Its
idempotents are the sums `I(s)` of the idempotents `I(S)` over the sets `S` containing one point
of each matched pair in `s`.

This file describes this subalgebra intrinsically for an arbitrary matching, a map `M : α → β`
whose fibres are the matched sets (`TauCeti.StrandsAlgebra.matchedSubalgebra`): an element belongs
to it when its diagrams have no two matched starting or end points and its coefficients do not
change when a horizontal strand moves to a matched point
(`TauCeti.StrandDiagram.swapHorizontal`). It is closed under the product, and it is closed under
the differential, so that it is a differential subalgebra. Both closure properties come down to the
behaviour of crossings when a horizontal strand moves, developed in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal`: moving a strand identifies the
factorizations of a diagram, and the diagrams resolving to it, with those of the moved diagram.

Two diagrams are related by `TauCeti.StrandDiagram.matchedSetoid M` when they differ only in the
positions of their horizontal strands within matched classes. The coefficients of an element of
the subalgebra are constant on these classes, so the subalgebra is spanned by the matched
completion sums `TauCeti.StrandsAlgebra.matchedSum`, the sums over the classes of diagrams with no
two matched starting points and no two matched end points; these are the generators of `A(Z)` in
Lipshitz, Ozsváth and Thurston.

The subalgebra has its own unit `TauCeti.StrandsAlgebra.matchedOne`, the sum of the idempotents
`I(S)` of the sets `S` with no two matched points, which is the sum of the idempotents `I(s)`. When
`R` is nontrivial and `M` identifies two points it differs from the unit of the strands algebra.
With this unit the subalgebra is an `R`-algebra, and over a ring of characteristic two the
restricted differential makes it an ungraded differential algebra, over which type `D` structures
are defined.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebra R M`: the matched subalgebra, a non-unital subalgebra
  of the strands algebra.
* `TauCeti.StrandsAlgebra.matchedIdem R M s`: the idempotent `I(s)`.
* `TauCeti.StrandDiagram.matchedSetoid M`: diagrams differing by moving horizontal strands within
  matched classes.
* `TauCeti.StrandsAlgebra.matchedSum R M φ`: the matched completion sum of a diagram.
* `TauCeti.StrandsAlgebra.matchedOne R M`: the unit of the matched subalgebra.
* `TauCeti.StrandsAlgebra.matchedDifferential R M`: the differential restricted to the matched
  subalgebra.

## Main results

* `TauCeti.StrandsAlgebra.mem_matchedSubalgebra`: the characterization of the matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_mem_matchedSubalgebra`: the matched subalgebra is closed
  under the differential.
* `TauCeti.StrandsAlgebra.matchedIdem_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`: the `I(s)` are orthogonal idempotents of the
  matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_matchedIdem`: the `I(s)` are cycles.
* `TauCeti.StrandsAlgebra.matchedSum_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.span_matchedSum`: the matched completion sums lie in the matched
  subalgebra and span it.
* `TauCeti.StrandsAlgebra.matchedOne_mul`, `TauCeti.StrandsAlgebra.mul_matchedOne`: the unit.
* `TauCeti.StrandsAlgebra.sum_matchedIdem`: the `I(s)` sum to the unit of the matched subalgebra.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_matchedDifferential`: over a ring of characteristic
  two, the matched subalgebra is an ungraded differential algebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (pointed
  matched circles, the idempotents `I(s)` and the algebra `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α β : Type*} [LinearOrder α] [Fintype α] {M : α → β} {φ ψ : StrandDiagram α} {a b : α}

/-- Moving a horizontal strand to a matched point does not change whether the starting points are
pairwise unmatched. -/
theorem injOn_source_swapHorizontal_iff (hab : M a = M b) :
    Set.InjOn M ((φ.swapHorizontal a b).source : Set α) ↔ Set.InjOn M (φ.source : Set α) := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this hab.symm h'
    · rw [swapHorizontal_of_not h h']
  rw [source_swapHorizontal h]
  exact Finset.injOn_insert_erase_iff (mem_source.2 ⟨a, h.mem⟩) h.notMem_source hab

/-- Moving a horizontal strand to a matched point does not change whether the end points are
pairwise unmatched. -/
theorem injOn_target_swapHorizontal_iff (hab : M a = M b) :
    Set.InjOn M ((φ.swapHorizontal a b).target : Set α) ↔ Set.InjOn M (φ.target : Set α) := by
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this hab.symm h'
    · rw [swapHorizontal_of_not h h']
  rw [target_swapHorizontal h]
  exact Finset.injOn_insert_erase_iff (mem_target.2 ⟨a, h.mem⟩) h.notMem_target hab

variable (M) in
/-- Two strand diagrams are related for a matching `M : α → β` when one is obtained from the other
by moving horizontal strands to points with the same image under `M`, so that they differ only in
the positions of their horizontal strands within matched classes. -/
def matchedSetoid : Setoid (StrandDiagram α) :=
  Relation.EqvGen.setoid fun φ ψ ↦ ∃ a b, M a = M b ∧ φ.swapHorizontal a b = ψ

/-- Two diagrams are related by `TauCeti.StrandDiagram.matchedSetoid M` exactly when they are
related by the equivalence relation generated by moving a horizontal strand to a point with the
same image under `M`. -/
theorem matchedSetoid_iff : matchedSetoid M φ ψ ↔
    Relation.EqvGen (fun φ ψ ↦ ∃ a b, M a = M b ∧ φ.swapHorizontal a b = ψ) φ ψ :=
  Iff.rfl

/-- Moving a horizontal strand to a point with the same image under `M` gives a diagram related by
`TauCeti.StrandDiagram.matchedSetoid M`. -/
theorem matchedSetoid_swapHorizontal (hab : M a = M b) :
    matchedSetoid M φ (φ.swapHorizontal a b) :=
  matchedSetoid_iff.2 (.rel _ _ ⟨a, b, hab, rfl⟩)

/-- Diagrams related by `TauCeti.StrandDiagram.matchedSetoid M` both have, or both fail to have,
pairwise unmatched starting points and pairwise unmatched end points. -/
theorem injOn_source_and_target_iff_of_matchedSetoid (h : matchedSetoid M φ ψ) :
    Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α) ↔
      Set.InjOn M (ψ.source : Set α) ∧ Set.InjOn M (ψ.target : Set α) := by
  rw [matchedSetoid_iff] at h
  induction h with
  | rel φ ψ h =>
    obtain ⟨a, b, hab, rfl⟩ := h
    rw [injOn_source_swapHorizontal_iff hab, injOn_target_swapHorizontal_iff hab]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-! ### The matched subalgebra -/

variable (R) in
/-- The matched subalgebra of the strands algebra of `α` for a matching `M : α → β`, which pairs
the points of `α` with equal images. It consists of the elements `x` such that

* every diagram with a nonzero coefficient in `x` has no two matched starting points and no two
  matched end points, and
* the coefficient of a diagram in `x` does not change when one of its horizontal strands is moved
  to a matched point at which no strand starts or ends.

The second condition says that the coefficients are constant on each family of diagrams obtained
from one another by moving horizontal strands between matched points, so that `x` is a combination
of the sums of these families. For the matching of a pointed matched circle `Z` with `4k` points,
`α = Fin (4 * k)` and `R = ZMod 2`, these sums span the algebra `A(Z)` of Lipshitz, Ozsváth and
Thurston, which is therefore this subalgebra. The definition uses no property of `M` beyond being
a function. -/
def matchedSubalgebra (M : α → β) : NonUnitalSubalgebra R (StrandsAlgebra R α) where
  carrier := {x | (∀ φ, (basis R α).repr x φ ≠ 0 →
      Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α)) ∧
    ∀ φ a b, M a = M b → (basis R α).repr x (φ.swapHorizontal a b) = (basis R α).repr x φ}
  add_mem' {x y} hx hy := by
    refine ⟨fun φ h ↦ ?_, fun φ a b hab ↦ ?_⟩
    · rw [map_add, Finsupp.add_apply] at h
      by_cases hxφ : (basis R α).repr x φ = 0
      · exact hy.1 φ (by simpa [hxφ] using h)
      · exact hx.1 φ hxφ
    · simp only [map_add, Finsupp.add_apply, hx.2 φ a b hab, hy.2 φ a b hab]
  zero_mem' := ⟨fun φ h ↦ absurd (by simp) h, fun φ a b _ ↦ by simp⟩
  smul_mem' r x hx := by
    refine ⟨fun φ h ↦ hx.1 φ fun hxφ ↦ h ?_, fun φ a b hab ↦ ?_⟩
    · simp [hxφ]
    · simp only [map_smul, Finsupp.smul_apply, hx.2 φ a b hab]
  mul_mem' {x y} hx hy := by
    have := Fintype.ofFinite (StrandDiagram α)
    refine ⟨fun χ hχ ↦ ?_, fun χ a b hab ↦ ?_⟩
    · -- A diagram in a product starts where a diagram of `x` starts and ends where one of `y`
      -- ends.
      rw [repr_mul_apply] at hχ
      obtain ⟨φ, -, hφ⟩ := exists_ne_zero_of_sum_ne_zero hχ
      obtain ⟨ψ, -, hψ⟩ := exists_ne_zero_of_sum_ne_zero hφ
      rw [ne_eq, ite_eq_right_iff, not_imp] at hψ
      obtain ⟨⟨hc, rfl⟩, hψ⟩ := hψ
      rw [source_trans_of_target_eq hc.target_eq, target_trans_of_target_eq hc.target_eq]
      exact ⟨(hx.1 φ (left_ne_zero_of_mul hψ)).1, (hy.1 ψ (right_ne_zero_of_mul hψ)).2⟩
    -- Reduce to a diagram `χ` with a horizontal strand at `a` that can move to `b`.
    wlog hχ : χ.CanMoveHorizontal a b generalizing a b
    · by_cases hχ' : χ.CanMoveHorizontal b a
      · rw [swapHorizontal_comm]
        exact this b a hab.symm hχ'
      · rw [swapHorizontal_of_not hχ hχ']
    -- Moving the strand in both factors identifies the factorizations of `χ` with those of `χ`
    -- with the strand moved.
    have key {φ ψ : StrandDiagram α} {χ : StrandDiagram α} {a b : α}
        (hχ : χ.CanMoveHorizontal a b) (hab : M a = M b)
        (hM : Set.InjOn M (φ.target : Set α)) (h : φ.Composable ψ ∧ φ.trans ψ = χ) :
        (φ.swapHorizontal a b).Composable (ψ.swapHorizontal a b) ∧
          (φ.swapHorizontal a b).trans (ψ.swapHorizontal a b) = χ.swapHorizontal a b := by
      obtain ⟨hc, rfl⟩ := h
      have ha : a ∈ (φ.target : Set α) := mem_coe.2 (mem_target.2 ⟨a, hχ.mem_left_of_trans⟩)
      obtain ⟨hφ, hψ⟩ := hχ.of_trans hc.target_eq fun hb ↦ hχ.ne (hM ha hb hab)
      exact ⟨hc.swapHorizontal hφ hψ, swapHorizontal_trans_swapHorizontal hφ hψ⟩
    set e := (swapHorizontal_involutive (α := α) a b).toPerm
    rw [repr_mul_apply, repr_mul_apply, ← Equiv.sum_comp e]
    refine sum_congr rfl fun φ _ ↦ ?_
    rw [← Equiv.sum_comp e]
    refine sum_congr rfl fun ψ _ ↦ ?_
    simp only [e, Function.Involutive.coe_toPerm, hx.2 φ a b hab, hy.2 ψ a b hab]
    by_cases hxy : (basis R α).repr x φ * (basis R α).repr y ψ = 0
    · simp [hxy]
    have hxφ : (basis R α).repr x (φ.swapHorizontal a b) ≠ 0 := by
      rw [hx.2 φ a b hab]
      exact left_ne_zero_of_mul hxy
    refine if_congr ⟨fun h ↦ ?_, key hχ hab (hx.1 φ (left_ne_zero_of_mul hxy)).2⟩ rfl rfl
    simpa [swapHorizontal_comm _ b a] using key hχ.swapHorizontal hab.symm (hx.1 _ hxφ).2 h

/-- An element of the strands algebra lies in the matched subalgebra when every diagram with a
nonzero coefficient has no two matched starting points and no two matched end points, and the
coefficients do not change when a horizontal strand moves to a matched point. -/
theorem mem_matchedSubalgebra {M : α → β} {x : StrandsAlgebra R α} :
    x ∈ matchedSubalgebra R M ↔
      (∀ φ, (basis R α).repr x φ ≠ 0 →
        Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α)) ∧
      ∀ φ a b, M a = M b →
        (basis R α).repr x (φ.swapHorizontal a b) = (basis R α).repr x φ :=
  Iff.rfl

/-- **The matched subalgebra is closed under the differential.** -/
theorem differential_mem_matchedSubalgebra {M : α → β} {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) : differential R α x ∈ matchedSubalgebra R M := by
  have := Fintype.ofFinite (StrandDiagram α)
  rw [mem_matchedSubalgebra] at hx ⊢
  refine ⟨fun χ hχ ↦ ?_, fun χ a b hab ↦ ?_⟩
  · -- Resolving a crossing keeps the starting and end points.
    rw [repr_differential_apply] at hχ
    obtain ⟨φ, -, hφ⟩ := exists_ne_zero_of_sum_ne_zero hχ
    obtain ⟨q, -, hq⟩ := exists_ne_zero_of_sum_ne_zero hφ
    rw [ne_eq, ite_eq_right_iff, not_imp] at hq
    obtain ⟨⟨-, rfl⟩, hq⟩ := hq
    rw [source_resolve, target_resolve]
    exact hx.1 φ hq
  wlog hχ : χ.CanMoveHorizontal a b generalizing a b
  · by_cases hχ' : χ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this b a hab.symm hχ'
    · rw [swapHorizontal_of_not hχ hχ']
  -- Moving the strand identifies the diagrams resolving to `χ` with those resolving to `χ` with
  -- the strand moved.
  have key {φ χ : StrandDiagram α} {q : α × α} {a b : α} (hχ : χ.CanMoveHorizontal a b)
      (h : q ∈ φ.resolvableInversions ∧ φ.resolve q = χ) :
      q ∈ (φ.swapHorizontal a b).resolvableInversions ∧
        (φ.swapHorizontal a b).resolve q = χ.swapHorizontal a b := by
    obtain ⟨hq, rfl⟩ := h
    have hq' := resolvableInversions_subset_inversions φ hq
    exact ⟨(mem_resolvableInversions_swapHorizontal_iff hq' hχ).2 hq, resolve_swapHorizontal hq' hχ⟩
  set e := (swapHorizontal_involutive (α := α) a b).toPerm
  rw [repr_differential_apply, repr_differential_apply, ← Equiv.sum_comp e]
  refine sum_congr rfl fun φ _ ↦ sum_congr rfl fun q _ ↦ ?_
  simp only [e, Function.Involutive.coe_toPerm, hx.2 φ a b hab]
  refine if_congr ⟨fun h ↦ ?_, key hχ⟩ rfl rfl
  simpa [swapHorizontal_comm _ b a] using key hχ.swapHorizontal h

/-! ### The idempotents of the matched subalgebra -/

section Idempotents

variable [DecidableEq β]

variable (R) in
/-- The idempotent `I(s)` of the matched subalgebra for a finite set `s` of values of the
matching `M`: the sum of the idempotents `I(S)` over the sets `S` of points mapped bijectively
onto `s` by `M`, that is, containing exactly one point over each element of `s`. -/
def matchedIdem (M : α → β) (s : Finset β) : StrandsAlgebra R α :=
  ∑ S with S.image M = s ∧ #S = #s, idem S

theorem matchedIdem_def (M : α → β) (s : Finset β) :
    matchedIdem R M s = ∑ S with S.image M = s ∧ #S = #s, idem S :=
  (rfl)

/-- The idempotents `I(s)` are cycles. -/
@[simp]
theorem differential_matchedIdem (M : α → β) (s : Finset β) :
    differential R α (matchedIdem R M s) = 0 := by
  simp [matchedIdem_def]

/-- The coefficient of a diagram in `I(s)` is `1` when it is the identity diagram on a set mapped
bijectively onto `s` by `M`, and `0` otherwise. -/
theorem repr_matchedIdem_apply (M : α → β) (s : Finset β) (φ : StrandDiagram α) :
    (basis R α).repr (matchedIdem R M s) φ =
      if φ = idOn φ.source ∧ φ.source.image M = s ∧ #φ.source = #s then 1 else 0 := by
  have key (S : Finset α) : idOn S = φ ↔ S = φ.source ∧ φ = idOn φ.source := by
    constructor
    · rintro rfl
      simp
    · rintro ⟨rfl, h⟩
      exact h.symm
  simp only [matchedIdem, idem_def, map_sum, ← basis_apply, Module.Basis.repr_self,
    Finset.sum_apply', Finsupp.single_apply, key, ite_and, sum_ite_eq', mem_filter, mem_univ,
    true_and]
  split_ifs <;> tauto

/-- **The idempotents `I(s)` lie in the matched subalgebra.** -/
theorem matchedIdem_mem_matchedSubalgebra (M : α → β) (s : Finset β) :
    matchedIdem R M s ∈ matchedSubalgebra R M := by
  rw [mem_matchedSubalgebra]
  simp only [repr_matchedIdem_apply]
  refine ⟨fun φ hφ ↦ ?_, fun φ a b hab ↦ ?_⟩
  · obtain ⟨hφ, hM, hcard⟩ := (ite_ne_right_iff.1 hφ).1
    have hinj : Set.InjOn M (φ.source : Set α) := card_image_iff.1 (by rw [hM, hcard])
    rw [hφ, source_idOn, target_idOn]
    exact ⟨hinj, hinj⟩
  wlog h : φ.CanMoveHorizontal a b generalizing a b
  · by_cases h' : φ.CanMoveHorizontal b a
    · rw [swapHorizontal_comm]
      exact this b a hab.symm h'
    · rw [swapHorizontal_of_not h h']
  have ha : a ∈ φ.source := mem_source.2 ⟨a, h.mem⟩
  -- Replacing `a` by `b` changes neither the image under `M` nor the size of the source.
  have himage : (insert b (φ.source.erase a)).image M = φ.source.image M := by
    rw [image_insert, ← hab, ← image_insert, insert_erase ha]
  have hcard : #(insert b (φ.source.erase a)) = #φ.source := by
    rw [card_insert_of_notMem fun h' ↦ h.notMem_source (mem_of_mem_erase h'),
      card_erase_of_mem ha]
    have := card_pos.2 ⟨a, ha⟩
    omega
  rw [source_swapHorizontal h, himage, hcard]
  refine if_congr (and_congr_left fun _ ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩) rfl rfl
  · -- Move the strand back: `φ` is the identity diagram with the strand at `a`.
    have hb : b ∈ insert b (φ.source.erase a) := mem_insert_self b _
    have ha' : a ∉ insert b (φ.source.erase a) := by simp [h.ne]
    conv_lhs => rw [← swapHorizontal_swapHorizontal φ a b, h']
    rw [swapHorizontal_comm, swapHorizontal_idOn hb ha',
      erase_insert fun hb' ↦ h.notMem_source (mem_of_mem_erase hb'), insert_erase ha]
  · conv_lhs => rw [h']
    exact swapHorizontal_idOn ha h.notMem_source

/-- The idempotents `I(s)` are orthogonal: `I(s) I(t)` is `I(s)` when `s = t` and zero
otherwise. -/
@[simp]
theorem matchedIdem_mul_matchedIdem (M : α → β) (s t : Finset β) :
    matchedIdem R M s * matchedIdem R M t = if s = t then matchedIdem R M s else 0 := by
  simp only [matchedIdem, sum_mul_sum, idem_mul_idem, sum_ite_eq, mem_filter, mem_univ, true_and]
  split_ifs with hst
  · subst hst
    exact sum_congr rfl fun S hS ↦ ite_eq_left (mem_filter.1 hS).2
  · refine sum_eq_zero fun S hS ↦ ite_eq_right fun h ↦ hst ?_
    rw [← (mem_filter.1 hS).2.1, h.1]

/-- Each `I(s)` is idempotent. -/
theorem isIdempotentElem_matchedIdem (M : α → β) (s : Finset β) :
    IsIdempotentElem (matchedIdem R M s) := by
  simp [IsIdempotentElem, matchedIdem_mul_matchedIdem]

end Idempotents

/-! ### The matched completion sums -/

section MatchedSum

variable {M : α → β}

/-- The coefficients of an element of the matched subalgebra agree on diagrams related by moving
horizontal strands to matched points. -/
theorem repr_eq_of_matchedSetoid {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M)
    {φ ψ : StrandDiagram α} (h : matchedSetoid M φ ψ) :
    (basis R α).repr x φ = (basis R α).repr x ψ := by
  rw [matchedSetoid_iff] at h
  induction h with
  | rel φ ψ h =>
    obtain ⟨a, b, hab, rfl⟩ := h
    exact ((mem_matchedSubalgebra.1 hx).2 φ a b hab).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable (R M) in
/-- The **matched completion sum** of a strand diagram `φ`: the sum of the diagrams obtained from
`φ` by moving horizontal strands to points matched with them. When `φ` has no two matched starting
points and no two matched end points, it is the sum over all ways of placing each horizontal
strand of `φ` at any free point of its matched class, keeping the other strands; these sums span
the matched subalgebra. -/
def matchedSum (φ : StrandDiagram α) : StrandsAlgebra R α :=
  ∑ ψ ∈ (Set.toFinite {ψ | matchedSetoid M φ ψ}).toFinset, of ψ

open scoped Classical in
/-- The coefficients of a matched completion sum: `1` on the diagrams related to `φ` and `0`
elsewhere. -/
theorem repr_matchedSum_apply (φ ψ : StrandDiagram α) :
    (basis R α).repr (matchedSum R M φ) ψ = if matchedSetoid M φ ψ then 1 else 0 := by
  rw [matchedSum, repr_sum_of_apply]
  simp

/-- The matched completion sum of a diagram with no two matched starting points and no two matched
end points lies in the matched subalgebra. -/
theorem matchedSum_mem_matchedSubalgebra {φ : StrandDiagram α}
    (hS : Set.InjOn M (φ.source : Set α)) (hT : Set.InjOn M (φ.target : Set α)) :
    matchedSum R M φ ∈ matchedSubalgebra R M := by
  classical
  refine mem_matchedSubalgebra.2 ⟨fun ψ hψ ↦ ?_, fun ψ a b hab ↦ ?_⟩
  · rw [repr_matchedSum_apply] at hψ
    exact (injOn_source_and_target_iff_of_matchedSetoid (ite_ne_right_iff.1 hψ).1).1 ⟨hS, hT⟩
  · have h : matchedSetoid M ψ (ψ.swapHorizontal a b) := matchedSetoid_swapHorizontal hab
    have h' : matchedSetoid M φ (ψ.swapHorizontal a b) ↔ matchedSetoid M φ ψ :=
      ⟨fun h' ↦ (matchedSetoid M).iseqv.trans h' ((matchedSetoid M).iseqv.symm h),
        fun h' ↦ (matchedSetoid M).iseqv.trans h' h⟩
    simp only [repr_matchedSum_apply, h']

/-- **The matched completion sums span the matched subalgebra.** The sums
`TauCeti.StrandsAlgebra.matchedSum` of the diagrams with no two matched starting points and no two
matched end points span the matched subalgebra as an `R`-module. -/
theorem span_matchedSum :
    Submodule.span R (matchedSum R M ''
      {φ | Set.InjOn M (φ.source : Set α) ∧ Set.InjOn M (φ.target : Set α)}) =
      (matchedSubalgebra R M).toSubmodule := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
  · rintro _ ⟨φ, ⟨hS, hT⟩, rfl⟩
    exact matchedSum_mem_matchedSubalgebra hS hT
  classical
  let := Fintype.ofFinite (StrandDiagram α)
  let := Fintype.ofFinite (Quotient (matchedSetoid M))
  rw [NonUnitalSubalgebra.mem_toSubmodule] at hx
  -- Grouping the basis expansion of `x` by classes of diagrams writes `x` as a combination of
  -- the matched completion sums of class representatives.
  have key : x = ∑ C : Quotient (matchedSetoid M),
      (basis R α).repr x C.out • matchedSum R M C.out := by
    conv_lhs => rw [← (basis R α).sum_repr x]
    rw [← sum_fiberwise univ fun φ ↦ (⟦φ⟧ : Quotient (matchedSetoid M))]
    refine sum_congr rfl fun C _ ↦ ?_
    rw [matchedSum, smul_sum]
    refine sum_congr ?_ fun φ hφ ↦ ?_
    · ext φ
      simp only [mem_filter, mem_univ, true_and, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
        Quotient.mk_eq_iff_out]
      exact ⟨(matchedSetoid M).iseqv.symm, (matchedSetoid M).iseqv.symm⟩
    · rw [Set.Finite.mem_toFinset] at hφ
      rw [basis_apply, repr_eq_of_matchedSetoid hx hφ]
  rw [key]
  refine Submodule.sum_mem _ fun C _ ↦ ?_
  by_cases h : (basis R α).repr x C.out = 0
  · simp [h]
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨C.out, (mem_matchedSubalgebra.1 hx).1 _ h, rfl⟩)

end MatchedSum

/-! ### The unit of the matched subalgebra -/

section Unit

variable {M : α → β}

open scoped Classical in
variable (R M) in
/-- The unit of the matched subalgebra: the sum of the idempotents `I(S)` over the sets `S` with no
two matched points. -/
def matchedOne : StrandsAlgebra R α :=
  ∑ S ∈ univ.filter fun S : Finset α ↦ Set.InjOn M (S : Set α), idem S

open scoped Classical in
theorem matchedOne_def :
    matchedOne R M = ∑ S ∈ univ.filter fun S : Finset α ↦ Set.InjOn M (S : Set α), idem S :=
  (rfl)

/-- The unit of the matched subalgebra is the sum of the idempotents `I(s)` over any family of sets
`s` of values of `M` containing the image of every set of points. -/
theorem matchedOne_eq_sum_matchedIdem [DecidableEq β] {T : Finset (Finset β)}
    (hT : ∀ S : Finset α, S.image M ∈ T) : matchedOne R M = ∑ s ∈ T, matchedIdem R M s := by
  classical
  rw [matchedOne_def, ← sum_fiberwise_of_maps_to fun S _ ↦ hT S]
  refine sum_congr rfl fun s _ ↦ sum_congr ?_ fun _ _ ↦ rfl
  ext S
  simp only [mem_filter, mem_univ, true_and, ← card_image_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨rfl, h.symm⟩
  · rintro ⟨rfl, h⟩
    exact ⟨h.symm, rfl⟩

/-- **The idempotents `I(s)` sum to the unit of the matched subalgebra.** -/
theorem sum_matchedIdem [Fintype β] [DecidableEq β] :
    ∑ s : Finset β, matchedIdem R M s = matchedOne R M :=
  (matchedOne_eq_sum_matchedIdem fun _ ↦ mem_univ _).symm

/-- The unit `TauCeti.StrandsAlgebra.matchedOne R M` lies in the matched subalgebra. -/
theorem matchedOne_mem_matchedSubalgebra : matchedOne R M ∈ matchedSubalgebra R M := by
  classical
  rw [matchedOne_eq_sum_matchedIdem (T := univ.image (image M))
    fun S ↦ mem_image_of_mem _ (mem_univ S)]
  exact sum_mem fun s _ ↦ matchedIdem_mem_matchedSubalgebra M s

/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem differential_matchedOne : differential R α (matchedOne R M) = 0 := by
  simp [matchedOne_def]

/-- The unit of the matched subalgebra fixes a diagram with no two matched starting points. -/
theorem matchedOne_mul_of {φ : StrandDiagram α} (h : Set.InjOn M (φ.source : Set α)) :
    matchedOne R M * of φ = of φ := by
  classical
  simp [matchedOne_def, sum_mul, idem_mul_of, h]

/-- The unit of the matched subalgebra fixes a diagram with no two matched end points. -/
theorem of_mul_matchedOne {φ : StrandDiagram α} (h : Set.InjOn M (φ.target : Set α)) :
    of φ * matchedOne R M = of φ := by
  classical
  simp [matchedOne_def, mul_sum, of_mul_idem, h]

/-- `TauCeti.StrandsAlgebra.matchedOne` is a left identity on the elements of the matched
subalgebra. -/
theorem matchedOne_mul {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M) :
    matchedOne R M * x = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [mul_sum]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [mul_smul_comm, basis_apply, matchedOne_mul_of ((mem_matchedSubalgebra.1 hx).1 φ hφ).1]

/-- `TauCeti.StrandsAlgebra.matchedOne` is a right identity on the elements of the matched
subalgebra. -/
theorem mul_matchedOne {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M) :
    x * matchedOne R M = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [sum_mul]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [smul_mul_assoc, basis_apply, of_mul_matchedOne ((mem_matchedSubalgebra.1 hx).1 φ hφ).2]

instance : One (matchedSubalgebra R M) :=
  ⟨⟨matchedOne R M, matchedOne_mem_matchedSubalgebra⟩⟩

/-- The unit of the matched subalgebra is `TauCeti.StrandsAlgebra.matchedOne`, which differs from
the unit of the strands algebra when `R` is nontrivial and `M` identifies two points. -/
@[simp]
theorem coe_matchedSubalgebra_one :
    ((1 : matchedSubalgebra R M) : StrandsAlgebra R α) = matchedOne R M :=
  (rfl)

/-- The matched subalgebra is a unital algebra, with unit `TauCeti.StrandsAlgebra.matchedOne`. -/
instance : Semiring (matchedSubalgebra R M) where
  __ := (matchedSubalgebra R M).toNonUnitalSemiring
  one_mul x := Subtype.ext (matchedOne_mul x.2)
  mul_one x := Subtype.ext (mul_matchedOne x.2)

instance {R : Type*} [CommRing R] : Ring (matchedSubalgebra R M) where
  __ := (inferInstance : Semiring (matchedSubalgebra R M))
  __ := (matchedSubalgebra R M).toNonUnitalRing

instance : Algebra R (matchedSubalgebra R M) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

end Unit

/-! ### The differential of the matched subalgebra -/

section Differential

variable {M : α → β}

variable (R M) in
/-- The differential of the strands algebra restricted to the matched subalgebra. -/
def matchedDifferential : matchedSubalgebra R M →ₗ[R] matchedSubalgebra R M :=
  (differential R α).restrict (p := (matchedSubalgebra R M).toSubmodule)
    (q := (matchedSubalgebra R M).toSubmodule) fun _ hx ↦ differential_mem_matchedSubalgebra hx

@[simp]
theorem coe_matchedDifferential (x : matchedSubalgebra R M) :
    (matchedDifferential R M x : StrandsAlgebra R α) = differential R α x :=
  (rfl)

/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem matchedDifferential_one : matchedDifferential R M 1 = 0 :=
  Subtype.ext (by simp)

/-- Over a ring of characteristic two, such as `𝔽₂`, the matched subalgebra with the restricted
differential is an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_matchedDifferential {R : Type*} [CommRing R] [CharP R 2] :
    IsUngradedDGAlgebra (matchedDifferential R M) where
  map_mul a b := Subtype.ext (by simp [differential_mul])
  map_map a := Subtype.ext (by simp [differential_differential])

end Differential

end StrandsAlgebra

end TauCeti
