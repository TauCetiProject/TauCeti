/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Order.Fin.Basic
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic

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
the reversed order of `{1, …, n}` with `{1, …, n}`.

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

end StrandsAlgebra

end TauCeti
