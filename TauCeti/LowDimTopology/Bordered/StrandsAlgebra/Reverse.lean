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

## Main definitions

* `TauCeti.StrandDiagram.map e φ`: the diagram `φ` with its points relabelled along an order
  isomorphism `e : α ≃o β`.
* `TauCeti.StrandDiagram.reverse φ`: the diagram `φ` rotated by half a turn, a diagram on the
  order dual `αᵒᵈ`, with the inverse partial bijection.
* `TauCeti.StrandsAlgebra.mapAlgEquiv e`: the algebra isomorphism `A(α) ≃ A(β)` induced by `e`.
* `TauCeti.StrandsAlgebra.reverseAlgEquiv`: the algebra isomorphism `A(α) ≃ A(αᵒᵈ)ᵐᵒᵖ`.
* `TauCeti.StrandsAlgebra.revAlgEquiv`: the anti-automorphism `A(n) ≃ A(n)ᵐᵒᵖ` of the strands
  algebra on `{1, …, n}`, rotating diagrams by half a turn.

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
  exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨k, hk, hj⟩ ↦ hj ▸ hk⟩

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

end TauCeti
