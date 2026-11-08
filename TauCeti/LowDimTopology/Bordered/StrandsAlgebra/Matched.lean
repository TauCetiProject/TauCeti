/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal

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

## Main definitions

* `TauCeti.StrandsAlgebra.matchedSubalgebra R M`: the matched subalgebra, a non-unital subalgebra
  of the strands algebra.
* `TauCeti.StrandsAlgebra.matchedIdem R M s`: the idempotent `I(s)`.

## Main results

* `TauCeti.StrandsAlgebra.mem_matchedSubalgebra`: the characterization of the matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_mem_matchedSubalgebra`: the matched subalgebra is closed
  under the differential.
* `TauCeti.StrandsAlgebra.matchedIdem_mem_matchedSubalgebra`,
  `TauCeti.StrandsAlgebra.matchedIdem_mul_matchedIdem`: the `I(s)` are orthogonal idempotents of the
  matched subalgebra.
* `TauCeti.StrandsAlgebra.differential_matchedIdem`: the `I(s)` are cycles.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (pointed
  matched circles, the idempotents `I(s)` and the algebra `A(Z)`).
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

end Idempotents

end StrandsAlgebra

end TauCeti
