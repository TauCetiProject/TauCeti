/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.Order.Fin.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Differential
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic

/-!
# Orientation reversal of the strands algebra

Reversing the orientation of a pointed matched circle `Z` keeps its points and its matching but
reverses the order of the points, and the algebra of the reversed circle is the opposite algebra,
`A(-Z) ≅ A(Z)ᵒᵖ`; so a left module over `A(-Z)` is the same as a right module over `A(Z)`. At the
level of the strands algebra the isomorphism rotates a strand diagram by half a turn: a strand
from `(0, i)` to `(1, j)` becomes a strand from `(0, j)` to `(1, i)` in the reversed order. It
reverses the order of concatenation and preserves crossings, so it is an algebra isomorphism onto
the opposite algebra, and it sends the idempotent `I(s)` to the idempotent on the same points.

This file constructs the rotation on the strands algebra of an arbitrary finite linear order,
together with the relabelling of a strands algebra along an order isomorphism, which identifies
the reversed order of `{1, …, n}` with `{1, …, n}`. Both commute with the differential: the
rotation carries the crossing of the strands from `x` to `a` and from `y` to `b` to the crossing of
the rotated strands from `a` to `x` and from `b` to `y`, and resolving one crossing and rotating is
resolving the other (`TauCeti.StrandDiagram.reverse_resolve`). The corresponding statements for the
algebra `A(Z)` of a pointed matched circle are in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Opposite`.

Both maps respect the grading of `TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Basic`,
through maps of grading groups. Relabelling transports the boundary of a class and keeps the Maslov
component. Rotation keeps the Maslov component and negates the boundary, since the strands of the
rotated diagram run from the old end points to the old starting points; the multiplicities of a
class are unchanged, because the total sum of its boundary vanishes. As the rotation reverses
products, so does the induced map of grading groups: it is an isomorphism onto the opposite group,
`R(g h) = R(h) R(g)`, because for the reversed order the form `L` defining the product becomes
`(β₁, β₂) ↦ L(β₂, β₁)` (`TauCeti.StrandGradingGroup.linking_reverse`). It fixes the central element
`λ`, so the differential keeps its degree `λ⁻¹`.

## Main definitions

* `TauCeti.StrandDiagram.map e φ`: the diagram `φ` with its points relabelled along an order
  isomorphism `e : α ≃o β`.
* `TauCeti.StrandDiagram.reverse φ`: the diagram `φ` rotated by half a turn, a diagram on the
  order dual `αᵒᵈ`, with the inverse partial bijection.
* `TauCeti.StrandsAlgebra.mapAlgEquiv e`: the algebra isomorphism `A(α) ≃ A(β)` induced by `e`.
* `TauCeti.StrandsAlgebra.reverseAlgEquiv`: the algebra isomorphism `A(α) ≃ A(αᵒᵈ)ᵐᵒᵖ`.
* `TauCeti.StrandsAlgebra.revAlgEquiv`: the anti-automorphism `A(n) ≃ A(n)ᵐᵒᵖ` of the strands
  algebra on `{1, …, n}`, rotating diagrams by half a turn.
* `TauCeti.StrandGradingGroup.map e`: the isomorphism of grading groups induced by `e : α ≃o β`.
* `TauCeti.StrandGradingGroup.reverse`: the orientation reversal `G(α) ≃ G(αᵒᵈ)ᵐᵒᵖ` of the
  grading group.
* `TauCeti.StrandGradingGroup.rev`: the anti-automorphism `G(n) ≃ G(n)ᵐᵒᵖ` of the grading group
  of the strands algebra on `{1, …, n}`.

## Main results

* `TauCeti.StrandDiagram.reverse_trans`: rotation reverses concatenation.
* `TauCeti.StrandDiagram.inversionCount_reverse`: rotation preserves the number of crossings.
* `TauCeti.StrandDiagram.composable_reverse_iff`: `ψ.reverse` and `φ.reverse` are composable
  exactly when `φ` and `ψ` are.
* `TauCeti.StrandsAlgebra.reverseAlgEquiv_of`, `TauCeti.StrandsAlgebra.reverseAlgEquiv_idem`: the
  rotation on basis elements and on the idempotents `I(s)`.
* `TauCeti.StrandDiagram.map_resolve`, `TauCeti.StrandDiagram.reverse_resolve`: relabelling and
  rotation commute with resolving a crossing.
* `TauCeti.StrandsAlgebra.mapAlgEquiv_differential`,
  `TauCeti.StrandsAlgebra.unop_reverseAlgEquiv_differential`,
  `TauCeti.StrandsAlgebra.unop_revAlgEquiv_differential`: relabelling and rotation commute with the
  differential.
* `TauCeti.StrandDiagram.grading_map`, `TauCeti.StrandDiagram.grading_reverse`: relabelling and
  rotation transform the grading of a diagram by `StrandGradingGroup.map` and
  `StrandGradingGroup.reverse`.
* `TauCeti.StrandsAlgebra.mapAlgEquiv_mem_gradedPart_iff`,
  `TauCeti.StrandsAlgebra.unop_reverseAlgEquiv_mem_gradedPart_iff`,
  `TauCeti.StrandsAlgebra.unop_revAlgEquiv_mem_gradedPart_iff`: the isomorphisms of strands
  algebras carry the part of grading `g` onto the part of the transformed grading.
* `TauCeti.StrandGradingGroup.reverse_lambda`,
  `TauCeti.StrandGradingGroup.unop_reverse_mem_gPrime_iff`: the reversal fixes `λ` and preserves
  the subgroup `G'(n)`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 (the
  strands algebra), §3.2 (the orientation reversal `-Z` of a pointed matched circle) and §10.4
  (the anti-homomorphism of grading groups induced by orientation reversal).
-/

public section

noncomputable section

open Finset OrderDual MulOpposite

namespace TauCeti

namespace StrandDiagram

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-! ### Relabelling along an order isomorphism -/

/-- The strand diagram `φ` with its points relabelled along an order isomorphism `e`: it has a
strand from `e i` to `e j` for each strand of `φ` from `i` to `j`. -/
def map (e : α ≃o β) (φ : StrandDiagram α) : StrandDiagram β where
  toPEquiv := (e.symm.toEquiv.toPEquiv.trans φ.toPEquiv).trans e.toEquiv.toPEquiv
  le_of_mem' i j h := by
    simp only [PEquiv.mem_trans, Equiv.toPEquiv_apply, Option.mem_some_iff] at h
    obtain ⟨_, ⟨_, rfl, hk⟩, rfl⟩ := h
    simpa using e.monotone (φ.le_of_mem hk)

theorem mem_map {e : α ≃o β} {φ : StrandDiagram α} {i j : β} :
    j ∈ φ.map e i ↔ e.symm j ∈ φ (e.symm i) := by
  simp only [map, ← coe_toPEquiv, PEquiv.mem_trans, Equiv.toPEquiv_apply, Option.mem_some_iff]
  constructor
  · rintro ⟨_, ⟨_, rfl, hk⟩, rfl⟩
    simpa using hk
  · exact fun h ↦ ⟨_, ⟨_, rfl, h⟩, by simp⟩

@[simp]
theorem map_apply (e : α ≃o β) (φ : StrandDiagram α) (i : β) :
    φ.map e i = (φ (e.symm i)).map e := by
  ext j
  rw [← Option.mem_def, mem_map, ← Option.mem_def, Option.mem_map]
  exact ⟨fun h ↦ ⟨_, h, e.apply_symm_apply j⟩, fun ⟨k, hk, hj⟩ ↦ by simpa [← hj] using hk⟩

theorem apply_mem_map_apply {e : α ≃o β} {φ : StrandDiagram α} {i j : α} :
    e j ∈ φ.map e (e i) ↔ j ∈ φ i := by
  rw [mem_map]
  simp

@[simp]
theorem map_refl (φ : StrandDiagram α) : φ.map (OrderIso.refl α) = φ := by
  ext i j
  rw [← Option.mem_def, ← Option.mem_def, mem_map]
  rfl

theorem map_map (e : α ≃o β) (e' : β ≃o γ) (φ : StrandDiagram α) :
    (φ.map e).map e' = φ.map (e.trans e') := by
  ext i j
  rw [← Option.mem_def, ← Option.mem_def, mem_map, mem_map, mem_map]
  rfl

theorem map_trans (e : α ≃o β) (φ ψ : StrandDiagram α) :
    (φ.trans ψ).map e = (φ.map e).trans (ψ.map e) := by
  ext i k
  rw [← Option.mem_def, ← Option.mem_def, mem_map, mem_trans, mem_trans]
  simp only [mem_map]
  exact ⟨fun ⟨j, hj, hk⟩ ↦ ⟨e j, by simpa using hj, by simpa using hk⟩,
    fun ⟨j, hj, hk⟩ ↦ ⟨e.symm j, hj, hk⟩⟩

/-- Relabelling along an order isomorphism, as an equivalence of strand diagrams. -/
def mapEquiv (e : α ≃o β) : StrandDiagram α ≃ StrandDiagram β where
  toFun := map e
  invFun := map e.symm
  left_inv φ := by simp [map_map]
  right_inv φ := by simp [map_map]

@[simp]
theorem mapEquiv_apply (e : α ≃o β) (φ : StrandDiagram α) : mapEquiv e φ = φ.map e :=
  (rfl)

@[simp]
theorem mapEquiv_symm_apply (e : α ≃o β) (φ : StrandDiagram β) :
    (mapEquiv e).symm φ = φ.map e.symm :=
  (rfl)

@[simp]
theorem map_idOn (e : α ≃o β) (s : Finset α) :
    (idOn s).map e = idOn (s.map e.toEquiv.toEmbedding) := by
  ext i j
  rw [← Option.mem_def, ← Option.mem_def, mem_map, mem_idOn, mem_idOn, mem_map_equiv]
  simp [e.symm.injective.eq_iff]

section Finite

variable [Fintype α] [Fintype β]

@[simp]
theorem source_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).source = φ.source.map e.toEquiv.toEmbedding := by
  ext i
  simp only [mem_source, mem_map, mem_map_equiv]
  exact ⟨fun ⟨j, hj⟩ ↦ ⟨_, hj⟩, fun ⟨j, hj⟩ ↦ ⟨e j, by simpa using hj⟩⟩

@[simp]
theorem target_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).target = φ.target.map e.toEquiv.toEmbedding := by
  ext j
  simp only [mem_target, mem_map, mem_map_equiv]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨_, hi⟩, fun ⟨i, hi⟩ ↦ ⟨e i, by simpa using hi⟩⟩

theorem inversions_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).inversions = φ.inversions.map (e.toEquiv.prodCongr e.toEquiv).toEmbedding := by
  ext ⟨i, j⟩
  simp only [mem_inversions, mem_map, mem_map_equiv, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  refine ⟨fun ⟨hij, a, ha, b, hb, hba⟩ ↦ ⟨by simpa using hij, _, ha, _, hb, by simpa using hba⟩,
    fun ⟨hij, a, ha, b, hb, hba⟩ ↦ ⟨by simpa using hij, e a, by simpa using ha, e b,
      by simpa using hb, by simpa using hba⟩⟩

@[simp]
theorem inversionCount_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).inversionCount = φ.inversionCount := by
  rw [inversionCount_def, inversions_map, card_map, inversionCount_def]

@[simp]
theorem composable_map_iff (e : α ≃o β) {φ ψ : StrandDiagram α} :
    (φ.map e).Composable (ψ.map e) ↔ φ.Composable ψ := by
  simp only [composable_iff, target_map, source_map, map_inj, ← map_trans, inversionCount_map]

end Finite

/-! ### Rotation by half a turn -/

/-- The strand diagram `φ` rotated by half a turn: a diagram on the order dual `αᵒᵈ` with a strand
from `j` to `i` for each strand of `φ` from `i` to `j`. Its underlying partial bijection is the
inverse of that of `φ`, and its strands go upwards for the reversed order. -/
def reverse (φ : StrandDiagram α) : StrandDiagram αᵒᵈ where
  toPEquiv := (ofDual.toPEquiv.trans φ.toPEquiv.symm).trans toDual.toPEquiv
  le_of_mem' i j h := by
    simp only [PEquiv.mem_trans, Equiv.toPEquiv_apply, Option.mem_some_iff,
      PEquiv.mem_iff_mem] at h
    obtain ⟨_, ⟨_, rfl, hk⟩, rfl⟩ := h
    exact le_toDual.2 (φ.le_of_mem hk)

theorem mem_reverse {φ : StrandDiagram α} {i j : αᵒᵈ} :
    j ∈ φ.reverse i ↔ ofDual i ∈ φ (ofDual j) := by
  simp only [reverse, ← coe_toPEquiv, PEquiv.mem_trans, Equiv.toPEquiv_apply,
    Option.mem_some_iff, PEquiv.mem_iff_mem]
  constructor
  · rintro ⟨_, ⟨_, rfl, hk⟩, rfl⟩
    exact hk
  · exact fun h ↦ ⟨_, ⟨_, rfl, h⟩, rfl⟩

@[simp]
theorem reverse_apply (φ : StrandDiagram α) (i : αᵒᵈ) :
    φ.reverse i = (φ.toPEquiv.symm (ofDual i)).map toDual := by
  ext j
  rw [← Option.mem_def, mem_reverse, ← Option.mem_def, Option.mem_map]
  simp only [PEquiv.mem_iff_mem, coe_toPEquiv]
  exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨_, hk, hj⟩ ↦ hj ▸ hk⟩

theorem toDual_mem_reverse_toDual {φ : StrandDiagram α} {i j : α} :
    toDual j ∈ φ.reverse (toDual i) ↔ i ∈ φ j :=
  mem_reverse

/-- Rotating a concatenation by half a turn concatenates the rotated diagrams in the opposite
order. -/
theorem reverse_trans (φ ψ : StrandDiagram α) :
    (φ.trans ψ).reverse = ψ.reverse.trans φ.reverse := by
  ext i k
  rw [← Option.mem_def, ← Option.mem_def, mem_reverse, mem_trans, mem_trans]
  simp only [mem_reverse]
  exact ⟨fun ⟨j, hj, hk⟩ ↦ ⟨toDual j, hk, hj⟩, fun ⟨j, hj, hk⟩ ↦ ⟨ofDual j, hk, hj⟩⟩

/-- Rotating twice by half a turn is the identity, up to the identification `αᵒᵈᵒᵈ ≃o α`. -/
theorem reverse_reverse (φ : StrandDiagram α) :
    φ.reverse.reverse = φ.map (OrderIso.dualDual α) := by
  ext i j
  rw [← Option.mem_def, ← Option.mem_def, mem_reverse, mem_reverse, mem_map]
  rfl

theorem reverse_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).reverse = φ.reverse.map e.dual := by
  ext i j
  rw [← Option.mem_def, ← Option.mem_def, mem_reverse, mem_map, mem_map, mem_reverse]
  rfl

/-- Rotation by half a turn, as an equivalence between the strand diagrams of `α` and those of
`αᵒᵈ`. -/
def reverseEquiv : StrandDiagram α ≃ StrandDiagram αᵒᵈ where
  toFun := reverse
  invFun ψ := ψ.reverse.map (OrderIso.dualDual α).symm
  left_inv φ := by simp [reverse_reverse, map_map]
  right_inv ψ := by
    ext i j
    rw [← Option.mem_def, ← Option.mem_def, mem_reverse, mem_map, mem_reverse]
    rfl

@[simp]
theorem reverseEquiv_apply (φ : StrandDiagram α) : reverseEquiv φ = φ.reverse :=
  (rfl)

@[simp]
theorem reverseEquiv_symm_apply (ψ : StrandDiagram αᵒᵈ) :
    reverseEquiv.symm ψ = ψ.reverse.map (OrderIso.dualDual α).symm :=
  (rfl)

@[simp]
theorem reverse_idOn (s : Finset α) : (idOn s).reverse = idOn (s.map toDual.toEmbedding) := by
  ext i j
  rw [← Option.mem_def, ← Option.mem_def, mem_reverse, mem_idOn, mem_idOn, mem_map_equiv]
  simp only [toDual_symm_eq, ofDual_inj]
  exact ⟨fun ⟨h, hj⟩ ↦ ⟨h.symm, h ▸ hj⟩, fun ⟨h, hi⟩ ↦ ⟨h.symm, h ▸ hi⟩⟩

section Finite

variable [Fintype α]

@[simp]
theorem source_reverse (φ : StrandDiagram α) :
    φ.reverse.source = φ.target.map toDual.toEmbedding := by
  ext i
  simp only [mem_source, mem_target, mem_reverse, mem_map_equiv]
  exact ⟨fun ⟨j, hj⟩ ↦ ⟨_, hj⟩, fun ⟨j, hj⟩ ↦ ⟨toDual j, hj⟩⟩

@[simp]
theorem target_reverse (φ : StrandDiagram α) :
    φ.reverse.target = φ.source.map toDual.toEmbedding := by
  ext j
  simp only [mem_source, mem_target, mem_reverse, mem_map_equiv]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨_, hi⟩, fun ⟨i, hi⟩ ↦ ⟨toDual i, hi⟩⟩

/-- Rotation by half a turn preserves the number of crossings: the strands of `φ` starting at
`i < j` cross exactly when the rotated strands starting at their end points cross. -/
@[simp]
theorem inversionCount_reverse (φ : StrandDiagram α) :
    φ.reverse.inversionCount = φ.inversionCount := by
  symm
  rw [inversionCount_def, inversionCount_def]
  refine card_bij (fun p _ ↦ (toDual ((φ p.1).getD p.1), toDual ((φ p.2).getD p.2))) ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    obtain ⟨hij, a, ha, b, hb, hba⟩ := mem_inversions.1 hp
    rw [Option.mem_def] at ha hb
    simp only [ha, hb, Option.getD_some, mem_inversions, mem_reverse, ofDual_toDual]
    exact ⟨toDual_lt_toDual.2 hba, toDual i, ha, toDual j, hb, toDual_lt_toDual.2 hij⟩
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' h
    obtain ⟨-, a, ha, b, hb, -⟩ := mem_inversions.1 hp
    obtain ⟨-, a', ha', b', hb', -⟩ := mem_inversions.1 hp'
    rw [Option.mem_def] at ha hb ha' hb'
    simp only [ha, hb, ha', hb', Option.getD_some, Prod.mk.injEq, toDual_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Prod.ext (φ.toPEquiv.inj ha ha') (φ.toPEquiv.inj hb hb')
  · rintro ⟨c, d⟩ hp
    obtain ⟨hcd, x, hx, y, hy, hyx⟩ := mem_inversions.1 hp
    rw [mem_reverse] at hx hy
    refine ⟨(ofDual x, ofDual y), mem_inversions.2 ⟨hyx, _, hx, _, hy, hcd⟩, ?_⟩
    rw [Option.mem_def] at hx hy
    simp [hx, hy]

/-- The rotated diagrams `ψ.reverse` and `φ.reverse` are composable, in this order, exactly when
`φ` and `ψ` are. -/
@[simp]
theorem composable_reverse_iff {φ ψ : StrandDiagram α} :
    ψ.reverse.Composable φ.reverse ↔ φ.Composable ψ := by
  simp only [composable_iff, target_reverse, source_reverse, map_inj, ← reverse_trans,
    inversionCount_reverse]
  exact and_congr eq_comm (by rw [add_comm])

end Finite

/-! ### Resolving a crossing of a relabelled or rotated diagram -/

section Resolve

variable [Fintype α] [Fintype β] {φ : StrandDiagram α}

/-- The strands of `φ` starting at `x` and `y` cross exactly when the relabelled strands starting at
`e x` and `e y` cross. -/
theorem mem_inversions_map_iff (e : α ≃o β) {x y : α} :
    (e x, e y) ∈ (φ.map e).inversions ↔ (x, y) ∈ φ.inversions := by
  rw [inversions_map, mem_map_equiv]
  simp

/-- Relabelling along an order isomorphism commutes with resolving a crossing. -/
theorem map_resolve (e : α ≃o β) (φ : StrandDiagram α) (x y : α) :
    (φ.resolve (x, y)).map e = (φ.map e).resolve (e x, e y) := by
  by_cases h : (x, y) ∈ φ.inversions
  · ext i j
    have hs : Equiv.swap (e x) (e y) i = e (Equiv.swap x y (e.symm i)) := by
      conv_lhs => rw [← e.apply_symm_apply i]
      exact e.injective.swap_apply _ _ _
    rw [map_apply, resolve_apply ((mem_inversions_map_iff e).2 h), resolve_apply h, map_apply, hs,
      OrderIso.symm_apply_apply]
  · rw [resolve_of_notMem h, resolve_of_notMem (mt (mem_inversions_map_iff e).1 h)]

/-- The resolvable crossings of a relabelled diagram are the relabelled resolvable crossings. -/
theorem resolvableInversions_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).resolvableInversions =
      φ.resolvableInversions.map (e.toEquiv.prodCongr e.toEquiv).toEmbedding := by
  ext ⟨i, j⟩
  obtain ⟨x, rfl⟩ := e.surjective i
  obtain ⟨y, rfl⟩ := e.surjective j
  rw [mem_map_equiv, mem_resolvableInversions, mem_inversions_map_iff, ← map_resolve,
    inversionCount_map, inversionCount_map]
  simp

/-- The strands of `φ` from `x` to `a` and from `y` to `b` cross exactly when the rotated strands
from `a` to `x` and from `b` to `y` cross. -/
theorem toDual_mem_inversions_reverse_iff {x y a b : α} (ha : a ∈ φ x) (hb : b ∈ φ y) :
    (toDual a, toDual b) ∈ φ.reverse.inversions ↔ (x, y) ∈ φ.inversions := by
  rw [mem_inversions_iff_of_mem (toDual_mem_reverse_toDual.2 ha)
    (toDual_mem_reverse_toDual.2 hb), mem_inversions_iff_of_mem ha hb, toDual_lt_toDual,
    toDual_lt_toDual, and_comm]

/-- Rotation by half a turn commutes with resolving a crossing: resolving the crossing of the
strands of `φ` from `x` to `a` and from `y` to `b` and rotating is resolving the crossing of the
rotated strands, which start at `a` and `b`. -/
theorem reverse_resolve {x y a b : α} (ha : a ∈ φ x) (hb : b ∈ φ y) :
    (φ.resolve (x, y)).reverse = φ.reverse.resolve (toDual a, toDual b) := by
  by_cases h : (x, y) ∈ φ.inversions
  · ext i j
    obtain ⟨i, rfl⟩ := toDual.surjective i
    obtain ⟨j, rfl⟩ := toDual.surjective j
    rw [← Option.mem_def, ← Option.mem_def, toDual_mem_reverse_toDual,
      resolve_apply ((toDual_mem_inversions_reverse_iff ha hb).2 h), toDual.injective.swap_apply,
      toDual_mem_reverse_toDual, resolve_apply h]
    -- Precomposing with the transposition of `x` and `y` is postcomposing with that of `a` and `b`.
    have hs := congrArg (fun f : α ≃. α ↦ i ∈ f j) (swap_trans_eq_trans_swap (p := (x, y)) ha hb)
    simp only [PEquiv.mem_trans, Equiv.toPEquiv_apply, Option.mem_some_iff, coe_toPEquiv,
      exists_eq_left'] at hs
    rw [hs]
    exact ⟨fun ⟨c, hc, hci⟩ ↦ by rwa [← hci, Equiv.swap_apply_self],
      fun hi ↦ ⟨_, hi, Equiv.swap_apply_self _ _ _⟩⟩
  · rw [resolve_of_notMem h, resolve_of_notMem (mt (toDual_mem_inversions_reverse_iff ha hb).1 h)]

/-- Rotation by half a turn preserves the resolvable crossings, in the form of
`TauCeti.StrandDiagram.toDual_mem_inversions_reverse_iff`. -/
theorem toDual_mem_resolvableInversions_reverse_iff {x y a b : α} (ha : a ∈ φ x)
    (hb : b ∈ φ y) :
    (toDual a, toDual b) ∈ φ.reverse.resolvableInversions ↔ (x, y) ∈ φ.resolvableInversions := by
  rw [mem_resolvableInversions, mem_resolvableInversions, toDual_mem_inversions_reverse_iff ha hb,
    ← reverse_resolve ha hb, inversionCount_reverse, inversionCount_reverse]

end Resolve

end StrandDiagram

namespace StrandsAlgebra

variable {R : Type*} [CommSemiring R]
variable {α β : Type*} [LinearOrder α] [Fintype α] [LinearOrder β] [Fintype β]

/-- Relabelling the points along an order isomorphism `e : α ≃o β` is an isomorphism of strands
algebras, sending the basis element of `φ` to that of `φ.map e`. -/
def mapAlgEquiv (e : α ≃o β) : StrandsAlgebra R α ≃ₐ[R] StrandsAlgebra R β :=
  AlgEquiv.ofLinearEquiv ((basis R α).equiv (basis R β) (StrandDiagram.mapEquiv e))
    (by
      rw [← sum_idem, ← sum_idem, map_sum]
      simp only [idem_def, ← basis_apply, Module.Basis.equiv_apply, StrandDiagram.mapEquiv_apply,
        StrandDiagram.map_idOn, ← Equiv.finsetCongr_apply]
      exact Equiv.sum_comp (e.toEquiv.finsetCongr) fun t ↦ basis R β (StrandDiagram.idOn t))
    (map_mul_of_basis _ fun φ ψ ↦ by
      simp only [LinearEquiv.coe_coe, ← basis_apply, Module.Basis.equiv_apply,
        StrandDiagram.mapEquiv_apply]
      simp only [basis_apply, of_mul_of, StrandDiagram.composable_map_iff,
        ← StrandDiagram.map_trans]
      split_ifs
      · rw [← basis_apply, Module.Basis.equiv_apply, StrandDiagram.mapEquiv_apply, basis_apply]
      · rw [map_zero])

@[simp]
theorem mapAlgEquiv_of (e : α ≃o β) (φ : StrandDiagram α) :
    mapAlgEquiv e (of φ : StrandsAlgebra R α) = of (φ.map e) := by
  rw [mapAlgEquiv, AlgEquiv.ofLinearEquiv_apply, ← basis_apply, Module.Basis.equiv_apply,
    basis_apply, StrandDiagram.mapEquiv_apply]

/-- The coefficient of a relabelled diagram in a relabelled element. -/
@[simp]
theorem repr_mapAlgEquiv_apply_map (e : α ≃o β) (x : StrandsAlgebra R α) (φ : StrandDiagram α) :
    (basis R β).repr (mapAlgEquiv e x) (φ.map e) = (basis R α).repr x φ := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul_of r ψ =>
    simp only [map_smul, mapAlgEquiv_of, basis_repr_of, Finsupp.smul_apply, Finsupp.single_apply,
      ← StrandDiagram.mapEquiv_apply, (StrandDiagram.mapEquiv e).injective.eq_iff]

@[simp]
theorem mapAlgEquiv_symm (e : α ≃o β) :
    (mapAlgEquiv e).symm = (mapAlgEquiv e.symm : StrandsAlgebra R β ≃ₐ[R] _) := by
  refine AlgEquiv.ext fun x ↦ ?_
  induction x using induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_of r φ =>
    rw [map_smul, map_smul, mapAlgEquiv_of]
    congr 1
    rw [AlgEquiv.symm_apply_eq, mapAlgEquiv_of, StrandDiagram.map_map, OrderIso.symm_trans_self,
      StrandDiagram.map_refl]

@[simp]
theorem mapAlgEquiv_idem (e : α ≃o β) (s : Finset α) :
    mapAlgEquiv e (idem s : StrandsAlgebra R α) = idem (s.map e.toEquiv.toEmbedding) := by
  rw [idem_def, mapAlgEquiv_of, StrandDiagram.map_idOn, idem_def]

/-- **Orientation reversal of the strands algebra.** Rotating strand diagrams by half a turn is an
isomorphism from the strands algebra of `α` to the opposite of the strands algebra of the reversed
order `αᵒᵈ`, sending the basis element of `φ` to that of `φ.reverse`. -/
def reverseAlgEquiv : StrandsAlgebra R α ≃ₐ[R] (StrandsAlgebra R αᵒᵈ)ᵐᵒᵖ :=
  AlgEquiv.ofLinearEquiv
    (((basis R α).equiv (basis R αᵒᵈ) StrandDiagram.reverseEquiv).trans (opLinearEquiv R))
    (by
      rw [← sum_idem, map_sum, ← op_one, ← sum_idem, op_sum]
      simp only [idem_def, LinearEquiv.trans_apply, ← basis_apply, Module.Basis.equiv_apply,
        StrandDiagram.reverseEquiv_apply, StrandDiagram.reverse_idOn, coe_opLinearEquiv,
        ← Equiv.finsetCongr_apply]
      exact Equiv.sum_comp (toDual.finsetCongr) fun t ↦ op (basis R αᵒᵈ (StrandDiagram.idOn t)))
    (map_mul_of_basis _ fun φ ψ ↦ by
      simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, ← basis_apply,
        Module.Basis.equiv_apply, StrandDiagram.reverseEquiv_apply, coe_opLinearEquiv, ← op_mul]
      simp only [basis_apply, of_mul_of, StrandDiagram.composable_reverse_iff,
        ← StrandDiagram.reverse_trans]
      split_ifs
      · rw [← basis_apply, Module.Basis.equiv_apply, StrandDiagram.reverseEquiv_apply,
          basis_apply]
      · rw [map_zero, op_zero])

@[simp]
theorem reverseAlgEquiv_of (φ : StrandDiagram α) :
    reverseAlgEquiv (of φ : StrandsAlgebra R α) = op (of φ.reverse) := by
  rw [reverseAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearEquiv.trans_apply, ← basis_apply,
    Module.Basis.equiv_apply, basis_apply, StrandDiagram.reverseEquiv_apply, coe_opLinearEquiv]

/-- The coefficient of a rotated diagram in a rotated element. -/
@[simp]
theorem mulOpposite_repr_reverseAlgEquiv_apply_reverse (x : StrandsAlgebra R α)
    (φ : StrandDiagram α) :
    (basis R αᵒᵈ).mulOpposite.repr (reverseAlgEquiv x) φ.reverse = (basis R α).repr x φ := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul_of r ψ =>
    simp only [← Module.Basis.repr_unop_eq_mulOpposite_repr, map_smul, reverseAlgEquiv_of, unop_op,
      basis_repr_of, Finsupp.smul_apply, Finsupp.single_apply, ← StrandDiagram.reverseEquiv_apply,
      StrandDiagram.reverseEquiv.injective.eq_iff]

@[simp]
theorem reverseAlgEquiv_symm_op_of (ψ : StrandDiagram αᵒᵈ) :
    reverseAlgEquiv.symm (op (of ψ : StrandsAlgebra R αᵒᵈ)) =
      of (ψ.reverse.map (OrderIso.dualDual α).symm) := by
  rw [AlgEquiv.symm_apply_eq, reverseAlgEquiv_of, ← StrandDiagram.reverseEquiv_symm_apply,
    ← StrandDiagram.reverseEquiv_apply, Equiv.apply_symm_apply]

@[simp]
theorem reverseAlgEquiv_idem (s : Finset α) :
    reverseAlgEquiv (idem s : StrandsAlgebra R α) = op (idem (s.map toDual.toEmbedding)) := by
  rw [idem_def, reverseAlgEquiv_of, StrandDiagram.reverse_idOn, idem_def]

/-- The strands algebra on `{1, …, n}` is isomorphic to its opposite: rotate each diagram by half a
turn and relabel the reversed order by `i ↦ n + 1 - i` (here `Fin.rev`). -/
def revAlgEquiv (n : ℕ) : StrandsAlgebra R (Fin n) ≃ₐ[R] (StrandsAlgebra R (Fin n))ᵐᵒᵖ :=
  reverseAlgEquiv.trans (AlgEquiv.op (mapAlgEquiv Fin.revOrderIso))

@[simp]
theorem revAlgEquiv_of {n : ℕ} (φ : StrandDiagram (Fin n)) :
    revAlgEquiv n (of φ : StrandsAlgebra R (Fin n)) = op (of (φ.reverse.map Fin.revOrderIso)) := by
  simp [revAlgEquiv, AlgEquiv.op]

/-- The anti-automorphism of the strands algebra on `{1, …, n}` is the rotation followed by the
relabelling of the reversed order. -/
theorem unop_revAlgEquiv_apply {n : ℕ} (x : StrandsAlgebra R (Fin n)) :
    unop (revAlgEquiv n x) = mapAlgEquiv Fin.revOrderIso (unop (reverseAlgEquiv x)) :=
  (rfl)

/-! ### Compatibility with the differential -/

/-- Relabelling along an order isomorphism commutes with the differential. -/
theorem mapAlgEquiv_differential (e : α ≃o β) (x : StrandsAlgebra R α) :
    mapAlgEquiv e (differential R α x) = differential R β (mapAlgEquiv e x) := by
  refine LinearMap.congr_fun ((basis R α).ext fun φ ↦ ?_ :
    (mapAlgEquiv e).toLinearMap ∘ₗ differential R α =
      differential R β ∘ₗ (mapAlgEquiv e).toLinearMap) x
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, basis_apply,
    mapAlgEquiv_of, differential_of, map_sum, StrandDiagram.resolvableInversions_map, sum_map]
  refine sum_congr rfl fun ⟨x, y⟩ _ ↦ ?_
  rw [StrandDiagram.map_resolve, Equiv.coe_toEmbedding, Equiv.prodCongr_apply, Prod.map_apply,
    OrderIso.coe_toEquiv]

open StrandDiagram in
/-- **Orientation reversal preserves the differential.** Rotating strand diagrams by half a turn
commutes with the differential, which resolves crossings. -/
theorem unop_reverseAlgEquiv_differential (x : StrandsAlgebra R α) :
    unop (reverseAlgEquiv (differential R α x)) =
      differential R αᵒᵈ (unop (reverseAlgEquiv x)) := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, unop_add, hx, hy]
  | smul_of r φ =>
    simp only [map_smul, unop_smul, reverseAlgEquiv_of, unop_op, differential_of, map_sum,
      unop_sum]
    congr 1
    -- The two strands of a resolvable crossing of `φ`, or of its rotation, and their end points.
    have hφ {x y : α} (h : (x, y) ∈ φ.resolvableInversions) :
        φ.endpoint x ∈ φ x ∧ φ.endpoint y ∈ φ y :=
      have h := resolvableInversions_subset_inversions φ h
      ⟨endpoint_mem (fst_mem_source_of_mem_inversions h),
        endpoint_mem (snd_mem_source_of_mem_inversions h)⟩
    have hψ {c d : αᵒᵈ} (h : (c, d) ∈ φ.reverse.resolvableInversions) :
        ofDual c ∈ φ (ofDual (φ.reverse.endpoint c)) ∧
          ofDual d ∈ φ (ofDual (φ.reverse.endpoint d)) :=
      have h := resolvableInversions_subset_inversions _ h
      ⟨mem_reverse.1 (endpoint_mem (fst_mem_source_of_mem_inversions h)),
        mem_reverse.1 (endpoint_mem (snd_mem_source_of_mem_inversions h))⟩
    -- The crossing of the strands from `x` to `a` and from `y` to `b` corresponds to the crossing
    -- of the rotated strands starting at `a` and `b`.
    refine sum_nbij' (fun p ↦ (toDual (φ.endpoint p.1), toDual (φ.endpoint p.2)))
      (fun q ↦ (ofDual (φ.reverse.endpoint q.1), ofDual (φ.reverse.endpoint q.2)))
      (fun _ h ↦ (toDual_mem_resolvableInversions_reverse_iff (hφ h).1 (hφ h).2).2 h)
      (fun _ h ↦ (toDual_mem_resolvableInversions_reverse_iff (hψ h).1 (hψ h).2).1 h)
      (fun _ h ↦ ?_) (fun _ h ↦ ?_) fun _ h ↦ by rw [reverse_resolve (hφ h).1 (hφ h).2]
    · simp [endpoint_eq_of_mem (toDual_mem_reverse_toDual.2 (hφ h).1),
        endpoint_eq_of_mem (toDual_mem_reverse_toDual.2 (hφ h).2)]
    · simp [endpoint_eq_of_mem (hψ h).1, endpoint_eq_of_mem (hψ h).2]

/-- The anti-automorphism of the strands algebra on `{1, …, n}` commutes with the differential. -/
theorem unop_revAlgEquiv_differential {n : ℕ} (x : StrandsAlgebra R (Fin n)) :
    unop (revAlgEquiv n (differential R (Fin n) x)) =
      differential R (Fin n) (unop (revAlgEquiv n x)) := by
  rw [unop_revAlgEquiv_apply, unop_revAlgEquiv_apply, unop_reverseAlgEquiv_differential,
    mapAlgEquiv_differential]

end StrandsAlgebra

/-! ### Relabelling and reversing the grading group -/

namespace StrandGradingGroup

variable {α β γ : Type*} [LinearOrder α] [Fintype α] [LinearOrder β] [Fintype β]
  [LinearOrder γ] [Fintype γ]

/-- The multiplicity of a class at a point does not change when the points are relabelled along
an order isomorphism. -/
theorem pointMultiplicity_comp_symm (e : α ≃o β) (p : α) (δ : α → ℤ) :
    pointMultiplicity (e p) (δ ∘ e.symm) = pointMultiplicity p δ := by
  have h : ∑ y ∈ ({y | y < e p} : Finset β), (δ (e.symm y) : ℚ) =
      ∑ y ∈ ({y | y < p} : Finset α), (δ y : ℚ) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv e.symm.toEquiv _ _ fun y ↦ by simp [e.symm_apply_lt]
  simp only [pointMultiplicity_apply, Function.comp_apply, OrderIso.symm_apply_apply, h]

/-- The form `L` does not change when the points are relabelled along an order isomorphism. -/
theorem linking_comp_symm (e : α ≃o β) (δ₁ δ₂ : α → ℤ) :
    linking (δ₁ ∘ e.symm) (δ₂ ∘ e.symm) = linking δ₁ δ₂ := by
  rw [linking_apply, linking_apply]
  exact Fintype.sum_equiv e.symm.toEquiv _ _ fun q ↦ by
    simp [← pointMultiplicity_comp_symm e (e.symm q) δ₂]

/-- Relabelling the points along an order isomorphism `e : α ≃o β` is an isomorphism of grading
groups: it keeps the Maslov component and transports the boundary along `e`. -/
def map (e : α ≃o β) : StrandGradingGroup α ≃* StrandGradingGroup β where
  toFun g := mk g.maslov (g.boundary ∘ e.symm)
  invFun g := mk g.maslov (g.boundary ∘ e)
  left_inv g := by ext <;> simp [Function.comp_def]
  right_inv g := by ext <;> simp [Function.comp_def]
  map_mul' g h := by
    ext
    · simp [linking_comp_symm]
    · simp [Function.comp_def, Pi.add_def]

@[simp]
theorem map_maslov (e : α ≃o β) (g : StrandGradingGroup α) : (map e g).maslov = g.maslov := by
  simp [map]

@[simp]
theorem map_boundary (e : α ≃o β) (g : StrandGradingGroup α) (y : β) :
    (map e g).boundary y = g.boundary (e.symm y) := by
  simp [map]

@[simp]
theorem map_symm (e : α ≃o β) : (map e).symm = map e.symm := by
  ext g y
  · simp [map]
  · simp [map]

@[simp]
theorem map_refl : map (OrderIso.refl α) = MulEquiv.refl (StrandGradingGroup α) := by
  ext g y
  · simp [map]
  · simp [map]

theorem map_trans (e : α ≃o β) (e' : β ≃o γ) : map (e.trans e') = (map e).trans (map e') := by
  ext g y
  · simp [map]
  · simp [map]

@[simp]
theorem map_lambda (e : α ≃o β) : map e lambda = lambda := by
  ext <;> simp

/-- Relabelling preserves the subgroup `G'(n)`. -/
@[simp]
theorem map_mem_gPrime_iff (e : α ≃o β) {g : StrandGradingGroup α} :
    map e g ∈ gPrime ↔ g ∈ gPrime := by
  have h : #{y | Odd (g.boundary (e.symm y))} = #{x | Odd (g.boundary x)} := by
    simp only [Finset.card_filter]
    exact Fintype.sum_equiv e.symm.toEquiv _ _ fun _ ↦ rfl
  simp only [mem_gPrime, map_maslov, map_boundary, h]
  rw [Fintype.sum_equiv e.symm.toEquiv (fun y ↦ g.boundary (e.symm y)) g.boundary fun _ ↦ rfl]

/-- The multiplicity of the reversed class, with boundary `x ↦ -δ x`, at `p` for the reversed
order exceeds `m(β, p)` by the total sum of `δ`. For the classes of diagrams, whose boundaries
have total sum zero, the two multiplicities agree. -/
theorem pointMultiplicity_toDual (p : α) (δ : α → ℤ) :
    pointMultiplicity (toDual p) (fun x ↦ -δ (ofDual x)) =
      pointMultiplicity p δ + ∑ x, (δ x : ℚ) := by
  have h : ∑ y ∈ ({y | y < toDual p} : Finset αᵒᵈ), ((-δ (ofDual y) : ℤ) : ℚ) =
      -∑ y ∈ ({y | p < y} : Finset α), (δ y : ℚ) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ofDual _ _ fun y ↦ by split_ifs <;> simp_all [lt_toDual]
  rw [pointMultiplicity_apply, h, pointMultiplicity_eq_sum_gt, ofDual_toDual]
  push_cast
  ring

/-- **Reversal turns `L` around**: for the reversed order and the reversed classes, with
boundaries `x ↦ -δ x`, the form `L` takes the value `L(β₂, β₁)`. -/
theorem linking_reverse (δ₁ δ₂ : α → ℤ) :
    linking (fun x : αᵒᵈ ↦ -δ₁ (ofDual x)) (fun x ↦ -δ₂ (ofDual x)) = linking δ₂ δ₁ := by
  have h : linking (fun x : αᵒᵈ ↦ -δ₁ (ofDual x)) (fun x ↦ -δ₂ (ofDual x)) =
      -∑ p, (δ₁ p : ℚ) * (pointMultiplicity p δ₂ + ∑ x, (δ₂ x : ℚ)) := by
    rw [linking_apply, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ofDual _ _ fun x ↦ by
      simp [← pointMultiplicity_toDual (ofDual x) δ₂]
  rw [h]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ← linking_apply]
  linear_combination (-1 : ℚ) * linking_add_linking_swap δ₁ δ₂

/-- **Orientation reversal of the grading group.** Reversing the order of the points, and with it
the orientation of the classes, is an isomorphism from the grading group of `α` onto the opposite
of the grading group of `αᵒᵈ`: it keeps the Maslov component and negates the boundary. So it is an
anti-isomorphism, `R(g h) = R(h) R(g)`, matching the orientation reversal of the strands algebra
`TauCeti.StrandsAlgebra.reverseAlgEquiv`. -/
def reverse : StrandGradingGroup α ≃* (StrandGradingGroup αᵒᵈ)ᵐᵒᵖ where
  toFun g := op (mk g.maslov fun x ↦ -g.boundary (ofDual x))
  invFun g := mk g.unop.maslov fun x ↦ -g.unop.boundary (toDual x)
  left_inv g := by ext <;> simp
  right_inv g := unop_injective <| by ext <;> simp
  map_mul' g h := unop_injective <| by
    ext
    · simp only [mul_maslov, mk_maslov, mk_boundary, unop_mul, unop_op, linking_reverse]
      ring
    · simp only [mul_boundary, mk_boundary, unop_mul, unop_op, Pi.add_apply]
      ring

@[simp]
theorem reverse_maslov (g : StrandGradingGroup α) : (reverse g).unop.maslov = g.maslov := by
  simp [reverse]

@[simp]
theorem reverse_boundary (g : StrandGradingGroup α) (x : αᵒᵈ) :
    (reverse g).unop.boundary x = -g.boundary (ofDual x) := by
  simp [reverse]

@[simp]
theorem reverse_symm_maslov (g : (StrandGradingGroup αᵒᵈ)ᵐᵒᵖ) :
    (reverse.symm g).maslov = g.unop.maslov := by
  simp [reverse]

@[simp]
theorem reverse_symm_boundary (g : (StrandGradingGroup αᵒᵈ)ᵐᵒᵖ) (x : α) :
    (reverse.symm g).boundary x = -g.unop.boundary (toDual x) := by
  simp [reverse]

/-- Reversal commutes with relabelling, which becomes relabelling along the dual order
isomorphism `e.dual : αᵒᵈ ≃o βᵒᵈ`. -/
theorem reverse_map (e : α ≃o β) (g : StrandGradingGroup α) :
    (reverse (map e g)).unop = map e.dual (reverse g).unop := by
  ext x
  · simp
  · simp

/-- Reversing twice is the identity, up to the identification `α ≃o αᵒᵈᵒᵈ`. -/
theorem reverse_reverse (g : StrandGradingGroup α) :
    (reverse (reverse g).unop).unop = map (OrderIso.dualDual α) g := by
  ext x
  · simp
  · simp

/-- Reversal fixes the central element `λ`, so the differential keeps its degree `λ⁻¹`. -/
@[simp]
theorem reverse_lambda : reverse (lambda : StrandGradingGroup α) = op lambda :=
  unop_injective <| by ext <;> simp

/-- Reversal preserves the subgroup `G'(n)`. -/
@[simp]
theorem unop_reverse_mem_gPrime_iff {g : StrandGradingGroup α} :
    (reverse g).unop ∈ gPrime ↔ g ∈ gPrime := by
  have h : #{x : αᵒᵈ | Odd (g.boundary (ofDual x))} = #{x | Odd (g.boundary x)} := by
    simp only [Finset.card_filter]
    exact Fintype.sum_equiv ofDual _ _ fun _ ↦ rfl
  simp only [mem_gPrime, reverse_maslov, reverse_boundary, Finset.sum_neg_distrib, neg_eq_zero,
    odd_neg, h]
  rw [Fintype.sum_equiv ofDual (fun x ↦ g.boundary (ofDual x)) g.boundary fun _ ↦ rfl]

variable (n : ℕ)

/-- The orientation reversal of the grading group of the strands algebra on `{1, …, n}`: reverse
the order and relabel it by `i ↦ n + 1 - i` (here `Fin.rev`). It is the anti-automorphism matching
`TauCeti.StrandsAlgebra.revAlgEquiv`. -/
def rev : StrandGradingGroup (Fin n) ≃* (StrandGradingGroup (Fin n))ᵐᵒᵖ :=
  reverse.trans (MulEquiv.op (map Fin.revOrderIso))

variable {n}

@[simp]
theorem rev_maslov (g : StrandGradingGroup (Fin n)) : (rev n g).unop.maslov = g.maslov := by
  simp [rev, MulEquiv.op]

@[simp]
theorem rev_boundary (g : StrandGradingGroup (Fin n)) (i : Fin n) :
    (rev n g).unop.boundary i = -g.boundary i.rev := by
  simp [rev, MulEquiv.op]

@[simp]
theorem rev_symm_maslov (g : (StrandGradingGroup (Fin n))ᵐᵒᵖ) :
    ((rev n).symm g).maslov = g.unop.maslov := by
  simp [rev, MulEquiv.op]

@[simp]
theorem rev_symm_boundary (g : (StrandGradingGroup (Fin n))ᵐᵒᵖ) (i : Fin n) :
    ((rev n).symm g).boundary i = -g.unop.boundary i.rev := by
  simp [rev, MulEquiv.op]

@[simp]
theorem rev_lambda : rev n lambda = op lambda := by
  simp [rev, MulEquiv.op]

@[simp]
theorem unop_rev_mem_gPrime_iff {g : StrandGradingGroup (Fin n)} :
    (rev n g).unop ∈ gPrime ↔ g ∈ gPrime := by
  simp [rev, MulEquiv.op]

end StrandGradingGroup

namespace StrandDiagram

open StrandGradingGroup

variable {α β : Type*} [LinearOrder α] [Fintype α] [LinearOrder β] [Fintype β]

/-- The boundary of the class of a relabelled diagram is the relabelled boundary. -/
@[simp]
theorem boundary_map (e : α ≃o β) (φ : StrandDiagram α) (y : β) :
    (φ.map e).boundary y = φ.boundary (e.symm y) := by
  simp [boundary_apply]

/-- Relabelling a diagram along an order isomorphism relabels its grading. -/
@[simp]
theorem grading_map (e : α ≃o β) (φ : StrandDiagram α) :
    (φ.map e).grading = StrandGradingGroup.map e φ.grading := by
  have hb : (φ.map e).boundary = φ.boundary ∘ e.symm := funext (boundary_map e φ)
  ext
  · simp [hb, Finset.sum_map, pointMultiplicity_comp_symm]
  · simp

/-- The class of a rotated diagram has the negated boundary: its strands run from the end points
of `φ` to its starting points. -/
@[simp]
theorem boundary_reverse (φ : StrandDiagram α) (x : αᵒᵈ) :
    φ.reverse.boundary x = -φ.boundary (ofDual x) := by
  simp only [boundary_apply, source_reverse, target_reverse, Finset.mem_map_equiv,
    toDual_symm_eq]
  ring

/-- **Rotation reverses the grading.** The grading of a diagram rotated by half a turn is the
orientation reversal of its grading. Its Maslov component is unchanged: rotation preserves the
crossings, and the multiplicities of the class of a diagram at its starting points have the same
sum as its multiplicities at its end points, because `L` vanishes on the class. -/
@[simp]
theorem grading_reverse (φ : StrandDiagram α) :
    φ.reverse.grading = (StrandGradingGroup.reverse φ.grading).unop := by
  have hb : φ.reverse.boundary = fun x ↦ -φ.boundary (ofDual x) := funext φ.boundary_reverse
  have hsum : ∑ x, (φ.boundary x : ℚ) = 0 := by exact_mod_cast φ.sum_boundary
  -- The multiplicities at the end points and at the starting points have the same sum.
  have hST : ∑ t ∈ φ.target, pointMultiplicity t φ.boundary =
      ∑ s ∈ φ.source, pointMultiplicity s φ.boundary := by
    have h := linking_boundary φ φ.boundary
    rw [linking_self, hsum] at h
    linear_combination -h
  ext
  · simp only [grading_maslov, inversionCount_reverse, source_reverse, Finset.sum_map, hb,
      reverse_maslov]
    simp [pointMultiplicity_toDual, hsum, hST]
  · simp

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram StrandGradingGroup

variable {R : Type*} [CommSemiring R]
variable {α β : Type*} [LinearOrder α] [Fintype α] [LinearOrder β] [Fintype β]

/-- Relabelling along an order isomorphism `e` carries the part of grading `g` onto the part of
grading `StrandGradingGroup.map e g`. -/
@[simp]
theorem mapAlgEquiv_mem_gradedPart_iff (e : α ≃o β) {g : StrandGradingGroup α}
    {x : StrandsAlgebra R α} :
    mapAlgEquiv e x ∈ gradedPart R (StrandGradingGroup.map e g) ↔ x ∈ gradedPart R g :=
  mem_gradedPart_iff_of_basis (mapAlgEquiv e).toLinearEquiv (mapEquiv e)
    (StrandGradingGroup.map e).injective
    (mapAlgEquiv_of e) (grading_map e)

/-- **Orientation reversal of the strands algebra is graded by the reversal of the grading
group**: it carries the part of grading `g` onto the part of grading `R(g)`. -/
@[simp]
theorem unop_reverseAlgEquiv_mem_gradedPart_iff {g : StrandGradingGroup α}
    {x : StrandsAlgebra R α} :
    (reverseAlgEquiv x).unop ∈ gradedPart R (StrandGradingGroup.reverse g).unop ↔
      x ∈ gradedPart R g :=
  mem_gradedPart_iff_of_basis (reverseAlgEquiv.toLinearEquiv.trans (opLinearEquiv R).symm)
    reverseEquiv (unop_injective.comp StrandGradingGroup.reverse.injective)
    (fun φ ↦ by simp) grading_reverse

/-- The anti-automorphism of the strands algebra on `{1, …, n}` carries the part of grading `g`
onto the part of grading `TauCeti.StrandGradingGroup.rev n g`. -/
@[simp]
theorem unop_revAlgEquiv_mem_gradedPart_iff {n : ℕ} {g : StrandGradingGroup (Fin n)}
    {x : StrandsAlgebra R (Fin n)} :
    (revAlgEquiv n x).unop ∈ gradedPart R (rev n g).unop ↔ x ∈ gradedPart R g :=
  mem_gradedPart_iff_of_basis ((revAlgEquiv n).toLinearEquiv.trans (opLinearEquiv R).symm)
    (reverseEquiv.trans (mapEquiv Fin.revOrderIso))
    (unop_injective.comp (rev n).injective) (fun φ ↦ by simp)
    (fun φ ↦ by simp [rev, MulEquiv.op])

end StrandsAlgebra

end TauCeti
