/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal
public import Mathlib.RingTheory.Idempotents

/-!
# The matched subalgebra of the strands algebra and the algebra `A(Z)`

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

The matched subalgebra need not contain the unit of the strands algebra, but it has a unit of its
own, the sum `TauCeti.StrandsAlgebra.matchedUnit` of the idempotents `I(s)`, which need not equal
the unit of the strands algebra. The type
`TauCeti.MatchedAlgebra R M` is the matched subalgebra with this unit and with the restricted
differential: a unital algebra, and over a ring of characteristic two an ungraded differential
algebra, which is what type `D` structures and box tensor products
(`TauCeti.LowDimTopology.Bordered.TypeD`) are built over. Its idempotents `I(s)` form a complete
family of orthogonal idempotents. Grouping them by the number `i` of strands gives the occupancy
idempotents, which are central because products preserve the number of strands, so the algebra
splits as the product of its occupancy summands, the summands `A(Z, j)` of Lipshitz, Ozsváth and
Thurston.

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebra R M`: the matched subalgebra, a non-unital subalgebra
  of the strands algebra.
* `TauCeti.StrandsAlgebra.matchedIdem R M s`: the idempotent `I(s)`.
* `TauCeti.StrandsAlgebra.matchedUnit R M`: the unit of the matched subalgebra, `∑ s, I(s)`.
* `TauCeti.MatchedAlgebra R M`: the matched subalgebra as a unital algebra, with its
  differential `TauCeti.MatchedAlgebra.differential` and idempotents `TauCeti.MatchedAlgebra.idem`.
* `TauCeti.MatchedAlgebra.occupancyIdem R M i`: the idempotent of the summand with `i` strands.
* `TauCeti.MatchedAlgebra.occupancyRingEquiv`: the matched algebra is the product of its
  occupancy summands.

## Main results

* `TauCeti.StrandsAlgebra.mem_matchedSubalgebra`: the characterization of the matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_mem_matchedSubalgebra`: the matched subalgebra is closed
  under the differential.
* `TauCeti.StrandsAlgebra.matchedIdem_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`: the `I(s)` are orthogonal idempotents of the
  matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_matchedIdem`: the `I(s)` are cycles.
* `TauCeti.StrandsAlgebra.matchedUnit_mul_of_mem`, `TauCeti.StrandsAlgebra.mul_matchedUnit_of_mem`:
  `∑ s, I(s)` is a two-sided unit for the matched subalgebra.
* `TauCeti.MatchedAlgebra.isUngradedDGAlgebra_differential`: in characteristic two the matched
  algebra is an ungraded differential algebra.
* `TauCeti.MatchedAlgebra.completeOrthogonalIdempotents_idem`: the `I(s)` are a complete family of
  orthogonal idempotents of the matched algebra.
* `TauCeti.MatchedAlgebra.isMulCentral_occupancyIdem`,
  `TauCeti.MatchedAlgebra.completeOrthogonalIdempotents_occupancyIdem`: the occupancy idempotents
  are central and form a complete family of orthogonal idempotents.
* `TauCeti.MatchedAlgebra.occupancyRingEquiv_apply_coe`,
  `TauCeti.MatchedAlgebra.occupancyRingEquiv_symm_apply`: the components of the occupancy
  decomposition are the corners `e_i x e_i`, and an element is the sum of its components.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (pointed
  matched circles, the idempotents `I(s)`, the algebra `A(Z)` and its summands `A(Z, i)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

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

/-- Multiplying a basis element `φ` on the left by `I(s)` keeps it exactly when `M` maps the
source of `φ` bijectively onto `s`. -/
theorem matchedIdem_mul_of (M : α → β) (s : Finset β) (φ : StrandDiagram α) :
    matchedIdem R M s * of φ = if φ.source.image M = s ∧ #φ.source = #s then of φ else 0 := by
  simp [matchedIdem_def, sum_mul, idem_mul_of]

/-- Multiplying a basis element `φ` on the right by `I(t)` keeps it exactly when `M` maps the
target of `φ` bijectively onto `t`. -/
theorem of_mul_matchedIdem (M : α → β) (φ : StrandDiagram α) (t : Finset β) :
    of φ * matchedIdem R M t = if φ.target.image M = t ∧ #φ.target = #t then of φ else 0 := by
  simp [matchedIdem_def, mul_sum, of_mul_idem]

/-- `I(s) x I(t)` vanishes when `s` and `t` have different sizes: the diagrams of the strands
algebra have as many starting points as end points. -/
theorem matchedIdem_mul_mul_matchedIdem_of_card_ne (M : α → β) {s t : Finset β} (h : #s ≠ #t)
    (x : StrandsAlgebra R α) : matchedIdem R M s * x * matchedIdem R M t = 0 := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp [mul_add, add_mul, hx, hy]
  | smul_of r φ =>
    rw [mul_smul_comm, smul_mul_assoc, matchedIdem_mul_of]
    split_ifs with hs
    · rw [of_mul_matchedIdem,
        ite_eq_right fun ht ↦ h (by rw [← hs.2, ← ht.2, card_target]), smul_zero]
    · simp

/-! ### The unit of the matched subalgebra -/

variable [Fintype β]

variable (R) in
/-- The unit of the matched subalgebra: the sum of its idempotents `I(s)` over all sets `s` of
values of the matching `M`. Equivalently, it is the sum of the idempotents `I(S)` of the strands
algebra over the sets `S` on which `M` is injective. It need not be the unit of the strands
algebra. -/
def matchedUnit (M : α → β) : StrandsAlgebra R α :=
  ∑ s, matchedIdem R M s

theorem matchedUnit_def (M : α → β) : matchedUnit R M = ∑ s, matchedIdem R M s :=
  (rfl)

/-- Multiplying a basis element `φ` on the left by the unit of the matched subalgebra keeps it
exactly when `M` is injective on the source of `φ`. -/
theorem matchedUnit_mul_of (M : α → β) (φ : StrandDiagram α) :
    matchedUnit R M * of φ = if Set.InjOn M (φ.source : Set α) then of φ else 0 := by
  simp only [matchedUnit_def, sum_mul, matchedIdem_mul_of, ite_and, sum_ite_eq, mem_univ,
    ite_true]
  exact if_congr (eq_comm.trans card_image_iff) rfl rfl

/-- Multiplying a basis element `φ` on the right by the unit of the matched subalgebra keeps it
exactly when `M` is injective on the target of `φ`. -/
theorem of_mul_matchedUnit (M : α → β) (φ : StrandDiagram α) :
    of φ * matchedUnit R M = if Set.InjOn M (φ.target : Set α) then of φ else 0 := by
  simp only [matchedUnit_def, mul_sum, of_mul_matchedIdem, ite_and, sum_ite_eq, mem_univ,
    ite_true]
  exact if_congr (eq_comm.trans card_image_iff) rfl rfl

/-- The unit of the matched subalgebra lies in it. -/
theorem matchedUnit_mem_matchedSubalgebra (M : α → β) :
    matchedUnit R M ∈ matchedSubalgebra R M :=
  sum_mem fun s _ ↦ matchedIdem_mem_matchedSubalgebra M s

/-- The unit of the matched subalgebra is a cycle. -/
@[simp]
theorem differential_matchedUnit (M : α → β) : differential R α (matchedUnit R M) = 0 := by
  simp [matchedUnit_def]

/-- **The unit of the matched subalgebra is a left unit for its elements.** -/
theorem matchedUnit_mul_of_mem {M : α → β} {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) : matchedUnit R M * x = x := by
  have := Fintype.ofFinite (StrandDiagram α)
  conv_lhs => rw [← (basis R α).sum_repr x]
  conv_rhs => rw [← (basis R α).sum_repr x]
  simp only [mul_sum, mul_smul_comm, basis_apply, matchedUnit_mul_of]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases h : (basis R α).repr x φ = 0
  · simp [h]
  · rw [ite_eq_left ((mem_matchedSubalgebra.1 hx).1 φ h).1]

/-- **The unit of the matched subalgebra is a right unit for its elements.** -/
theorem mul_matchedUnit_of_mem {M : α → β} {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) : x * matchedUnit R M = x := by
  have := Fintype.ofFinite (StrandDiagram α)
  conv_lhs => rw [← (basis R α).sum_repr x]
  conv_rhs => rw [← (basis R α).sum_repr x]
  simp only [sum_mul, smul_mul_assoc, basis_apply, of_mul_matchedUnit]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases h : (basis R α).repr x φ = 0
  · simp [h]
  · rw [ite_eq_left ((mem_matchedSubalgebra.1 hx).1 φ h).2]

end Idempotents

end StrandsAlgebra

open StrandsAlgebra

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-! ### The matched algebra -/

variable (R) in
/-- The **matched algebra** of a matching `M : α → β`: the matched subalgebra
`TauCeti.StrandsAlgebra.matchedSubalgebra R M` of the strands algebra, as a unital algebra whose
unit is `TauCeti.StrandsAlgebra.matchedUnit R M`, the sum of its idempotents `I(s)`, together with
the restriction of the differential of the strands algebra. For the matching of a pointed matched
circle `Z` and `R = ZMod 2` it is the differential algebra `A(Z)` of Lipshitz, Ozsváth and
Thurston. Its unit need not be that of the strands algebra, so the inclusion
`TauCeti.MatchedAlgebra.toStrandsAlgebra` need not preserve units and is only a homomorphism of
non-unital algebras. As for Mathlib's `IsIdempotentElem.Corner`, on which this construction is
modelled, it is a type synonym for a non-unital subalgebra equipped with an idempotent of the
ambient algebra as its own unit. -/
@[expose]
def MatchedAlgebra (M : α → β) : Type _ :=
  matchedSubalgebra R M

namespace MatchedAlgebra

variable {M : α → β}

instance : NonUnitalSemiring (MatchedAlgebra R M) :=
  inferInstanceAs (NonUnitalSemiring (matchedSubalgebra R M))

instance : Module R (MatchedAlgebra R M) :=
  inferInstanceAs (Module R (matchedSubalgebra R M))

instance : IsScalarTower R (MatchedAlgebra R M) (MatchedAlgebra R M) :=
  inferInstanceAs (IsScalarTower R (matchedSubalgebra R M) (matchedSubalgebra R M))

instance : SMulCommClass R (MatchedAlgebra R M) (MatchedAlgebra R M) :=
  inferInstanceAs (SMulCommClass R (matchedSubalgebra R M) (matchedSubalgebra R M))

variable (R M) in
/-- The inclusion of the matched algebra into the strands algebra, a homomorphism of non-unital
algebras. -/
def toStrandsAlgebra : MatchedAlgebra R M →ₙₐ[R] StrandsAlgebra R α :=
  NonUnitalSubalgebraClass.subtype (matchedSubalgebra R M)

theorem toStrandsAlgebra_injective : Function.Injective (toStrandsAlgebra R M) :=
  Subtype.val_injective

@[ext]
theorem ext {x y : MatchedAlgebra R M} (h : toStrandsAlgebra R M x = toStrandsAlgebra R M y) :
    x = y :=
  toStrandsAlgebra_injective h

/-- The image of the inclusion of the matched algebra is the matched subalgebra. -/
@[simp]
theorem range_toStrandsAlgebra :
    NonUnitalAlgHom.range (toStrandsAlgebra R M) = matchedSubalgebra R M :=
  NonUnitalSubalgebra.range_val (matchedSubalgebra R M)

theorem toStrandsAlgebra_mem (x : MatchedAlgebra R M) :
    toStrandsAlgebra R M x ∈ matchedSubalgebra R M :=
  x.2

variable (R M) in
/-- The element of the matched algebra given by an element of the matched subalgebra. -/
def mk (x : StrandsAlgebra R α) (hx : x ∈ matchedSubalgebra R M) : MatchedAlgebra R M :=
  ⟨x, hx⟩

@[simp]
theorem toStrandsAlgebra_mk (x : StrandsAlgebra R α) (hx : x ∈ matchedSubalgebra R M) :
    toStrandsAlgebra R M (mk R M x hx) = x :=
  (rfl)

instance {R : Type*} [CommRing R] : Neg (MatchedAlgebra R M) :=
  ⟨fun x ↦ mk R M (-toStrandsAlgebra R M x) (neg_mem (toStrandsAlgebra_mem x))⟩

/-! ### The differential of the matched algebra -/

variable (R M) in
/-- The differential of the matched algebra, the restriction of the differential of the strands
algebra, which resolves crossings. -/
def differential : MatchedAlgebra R M →ₗ[R] MatchedAlgebra R M where
  toFun x := mk R M (StrandsAlgebra.differential R α (toStrandsAlgebra R M x))
    (differential_mem_matchedSubalgebra (toStrandsAlgebra_mem x))
  map_add' x y := ext (by simp)
  map_smul' r x := ext (by simp)

@[simp]
theorem toStrandsAlgebra_differential (x : MatchedAlgebra R M) :
    toStrandsAlgebra R M (differential R M x) =
      StrandsAlgebra.differential R α (toStrandsAlgebra R M x) :=
  (rfl)

/-- **The Leibniz rule** for the differential of the matched algebra, over a ring of
characteristic two. -/
theorem differential_mul [CharP R 2] (x y : MatchedAlgebra R M) :
    differential R M (x * y) = differential R M x * y + x * differential R M y :=
  ext (by simp [StrandsAlgebra.differential_mul])

/-- The differential of the matched algebra squares to zero over a ring of characteristic two. -/
@[simp]
theorem differential_differential [CharP R 2] (x : MatchedAlgebra R M) :
    differential R M (differential R M x) = 0 :=
  ext (by simp)

/-! ### The idempotents of the matched algebra -/

section Idempotents

variable [DecidableEq β]

variable (R M) in
/-- The idempotent `I(s)` of the matched algebra, `TauCeti.StrandsAlgebra.matchedIdem R M s`. -/
def idem (s : Finset β) : MatchedAlgebra R M :=
  mk R M (matchedIdem R M s) (matchedIdem_mem_matchedSubalgebra M s)

@[simp]
theorem toStrandsAlgebra_idem (s : Finset β) :
    toStrandsAlgebra R M (idem R M s) = matchedIdem R M s :=
  (rfl)

/-- The idempotents `I(s)` are cycles. -/
@[simp]
theorem differential_idem (s : Finset β) : differential R M (idem R M s) = 0 :=
  ext (by simp)

/-- The idempotents `I(s)` are orthogonal: `I(s) I(t)` is `I(s)` when `s = t` and zero otherwise. -/
@[simp]
theorem idem_mul_idem (s t : Finset β) :
    idem R M s * idem R M t = if s = t then idem R M s else 0 := by
  ext
  split_ifs <;> simp [*]

/-- `I(s) x I(t)` vanishes when `s` and `t` have different sizes. -/
theorem idem_mul_mul_idem_of_card_ne {s t : Finset β} (h : #s ≠ #t) (x : MatchedAlgebra R M) :
    idem R M s * x * idem R M t = 0 :=
  ext (by simp [matchedIdem_mul_mul_matchedIdem_of_card_ne M h])

/-! ### The unit of the matched algebra -/

variable [Fintype β]

instance : Semiring (MatchedAlgebra R M) where
  __ : NonUnitalSemiring (MatchedAlgebra R M) := inferInstance
  one := mk R M (matchedUnit R M) (matchedUnit_mem_matchedSubalgebra M)
  -- `erw`: in these fields `1` is the `one` field just given, which `rw` does not see as an
  -- application of `mk`.
  one_mul x := ext (by
    erw [map_mul, toStrandsAlgebra_mk]
    exact matchedUnit_mul_of_mem (toStrandsAlgebra_mem x))
  mul_one x := ext (by
    erw [map_mul, toStrandsAlgebra_mk]
    exact mul_matchedUnit_of_mem (toStrandsAlgebra_mem x))

instance : Algebra R (MatchedAlgebra R M) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance {R : Type*} [CommRing R] : Ring (MatchedAlgebra R M) where
  __ : Semiring (MatchedAlgebra R M) := inferInstance
  zsmul := zsmulRec
  -- `erw`: `-x` unfolds to an application of `mk` only through the `Neg` instance.
  neg_add_cancel x := ext (by
    erw [map_add, toStrandsAlgebra_mk, neg_add_cancel, map_zero])

/-- The unit of the matched algebra is the sum of the idempotents `I(s)`. -/
@[simp]
theorem toStrandsAlgebra_one : toStrandsAlgebra R M 1 = matchedUnit R M :=
  (rfl)

/-- Over a ring of characteristic two, such as `𝔽₂`, the matched algebra with its differential is
an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_differential {R : Type*} [CommRing R] [CharP R 2] :
    IsUngradedDGAlgebra (differential R M) :=
  ⟨differential_mul, differential_differential⟩

/-- **The idempotents `I(s)` of the matched algebra are a complete family of orthogonal
idempotents**: they are idempotent, pairwise orthogonal, and sum to the unit. -/
theorem completeOrthogonalIdempotents_idem :
    CompleteOrthogonalIdempotents (idem R M) where
  idem s := by simp [IsIdempotentElem]
  ortho s t hst := by simp [hst]
  complete := ext (by simp [matchedUnit_def])

/-! ### The occupancy summands -/

variable (R M) in
/-- The idempotent of the summand of the matched algebra with `i` strands: the sum of the
idempotents `I(s)` over the sets `s` of size `i`. For the matching of a pointed matched circle with
`4k` points, `i = k + j` strands give the summand `A(Z, j)` of Lipshitz, Ozsváth and Thurston. -/
def occupancyIdem (i : Fin (Fintype.card β + 1)) : MatchedAlgebra R M :=
  ∑ s with #s = (i : ℕ), idem R M s

theorem occupancyIdem_def (i : Fin (Fintype.card β + 1)) :
    occupancyIdem R M i = ∑ s with #s = (i : ℕ), idem R M s :=
  (rfl)

/-- The occupancy idempotents are cycles. -/
@[simp]
theorem differential_occupancyIdem (i : Fin (Fintype.card β + 1)) :
    differential R M (occupancyIdem R M i) = 0 := by
  simp [occupancyIdem_def]

/-- `e_i x e_j` vanishes for distinct occupancy idempotents `e_i` and `e_j`. -/
theorem occupancyIdem_mul_mul_occupancyIdem_of_ne {i j : Fin (Fintype.card β + 1)} (h : i ≠ j)
    (x : MatchedAlgebra R M) : occupancyIdem R M i * x * occupancyIdem R M j = 0 := by
  simp only [occupancyIdem_def, sum_mul, mul_sum]
  refine sum_eq_zero fun s hs ↦ sum_eq_zero fun t ht ↦ idem_mul_mul_idem_of_card_ne ?_ x
  rw [(mem_filter.1 hs).2, (mem_filter.1 ht).2]
  exact Fin.val_injective.ne h

/-- **The occupancy idempotents are a complete family of orthogonal idempotents.** -/
theorem completeOrthogonalIdempotents_occupancyIdem :
    CompleteOrthogonalIdempotents (occupancyIdem R M) := by
  refine (CompleteOrthogonalIdempotents.iff_ortho_complete).2 ⟨fun i j hij ↦ ?_, ?_⟩
  · simpa [occupancyIdem_def, ← mul_assoc] using
      occupancyIdem_mul_mul_occupancyIdem_of_ne (R := R) (M := M) hij 1
  · rw [← completeOrthogonalIdempotents_idem.complete]
    have hlt (s : Finset β) : #s < Fintype.card β + 1 := Nat.lt_succ_of_le (card_le_univ s)
    rw [← sum_fiberwise univ (fun s ↦ (⟨#s, hlt s⟩ : Fin (Fintype.card β + 1))) (idem R M)]
    refine sum_congr rfl fun i _ ↦ sum_congr ?_ fun _ _ ↦ rfl
    ext s
    simp [Fin.ext_iff]

/-- **The occupancy idempotents are central**: the products in the matched algebra preserve the
number of strands. -/
theorem isMulCentral_occupancyIdem (i : Fin (Fintype.card β + 1)) :
    IsMulCentral (occupancyIdem R M i) := by
  refine Set.mem_center_iff.1 (Semigroup.mem_center_iff.2 fun x ↦ ?_)
  have he := completeOrthogonalIdempotents_occupancyIdem (R := R) (M := M)
  -- Both products equal `e_i x e_i`, by inserting `1 = ∑ j, e_j` on the other side.
  have h₁ : x * occupancyIdem R M i = occupancyIdem R M i * x * occupancyIdem R M i := by
    conv_lhs => rw [← one_mul x, ← he.complete, sum_mul, sum_mul]
    exact sum_eq_single i (fun j _ hj ↦ occupancyIdem_mul_mul_occupancyIdem_of_ne hj x)
      (by simp)
  have h₂ : occupancyIdem R M i * x = occupancyIdem R M i * x * occupancyIdem R M i := by
    conv_lhs => rw [← mul_one (_ * x), ← he.complete, mul_sum]
    exact sum_eq_single i (fun j _ hj ↦ occupancyIdem_mul_mul_occupancyIdem_of_ne hj.symm x)
      (by simp)
  rw [h₁, h₂, mul_assoc, (he.idem i).eq]

variable (R M) in
/-- **The occupancy decomposition of the matched algebra.** The matched algebra is the product of
its occupancy summands, the corners `e_i A e_i` of its central occupancy idempotents `e_i`. -/
def occupancyRingEquiv :
    MatchedAlgebra R M ≃+*
      Π i, ((completeOrthogonalIdempotents_occupancyIdem (R := R) (M := M)).idem i).Corner :=
  completeOrthogonalIdempotents_occupancyIdem.ringEquivOfIsMulCentral isMulCentral_occupancyIdem

/-- The component of `x` in the summand with `i` strands is `e_i x e_i`. -/
@[simp]
theorem occupancyRingEquiv_apply_coe (x : MatchedAlgebra R M) (i : Fin (Fintype.card β + 1)) :
    (occupancyRingEquiv R M x i).1 =
      occupancyIdem R M i * x * occupancyIdem R M i :=
  (rfl)

/-- An element is recovered from its occupancy components as their sum. -/
@[simp]
theorem occupancyRingEquiv_symm_apply
    (y : Π i, ((completeOrthogonalIdempotents_occupancyIdem (R := R) (M := M)).idem i).Corner) :
    (occupancyRingEquiv R M).symm y = ∑ i, (y i).1 :=
  (rfl)

end Idempotents

end MatchedAlgebra

end TauCeti
