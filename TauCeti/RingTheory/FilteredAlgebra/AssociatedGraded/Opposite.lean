/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.RingTheory.FilteredAlgebra.AssociatedGraded.Noetherian

/-!
# The opposite of a filtered ring

A decreasing filtration `F` of a ring `A` by two-sided ideals is also a filtration of the
opposite ring `Aᵐᵒᵖ`, the opposite filtration `TauCeti.AlgFiltration.op F`. Its graded pieces are
those of `F`, and reversing the order of multiplication identifies its associated graded ring
with the opposite of the associated graded ring of `F`.

Right ideals of `A` are left ideals of `Aᵐᵒᵖ`, so right-sided statements about filtered rings
follow from left-sided ones through this file. In particular, a complete separated filtered ring
whose associated graded ring is right noetherian is right noetherian.

## Main definitions

* `TauCeti.AlgFiltration.op F`: the filtration of `Aᵐᵒᵖ` given by the same ideals.
* `TauCeti.AlgFiltration.gradedPieceOpEquiv F n`: the identification of the graded pieces.
* `TauCeti.AlgFiltration.associatedGradedOpEquiv F`: the ring isomorphism
  `gr (Aᵐᵒᵖ) ≃+* (gr A)ᵐᵒᵖ`.

## Main results

* `TauCeti.AlgFiltration.isCompleteFiltration_op`: the opposite of a complete separated
  filtration is complete and separated.
* `AlgFiltration.isNoetherianRing_mulOpposite_of_isNoetherianRing_mulOpposite_associatedGraded`:
  a complete separated filtered ring with right noetherian associated graded ring is right
  noetherian.
-/

public section

open MulOpposite

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] (F : AlgFiltration A)

/-- The filtration of the opposite ring `Aᵐᵒᵖ` by the same two-sided ideals. -/
def op : AlgFiltration Aᵐᵒᵖ where
  ideal k :=
    { carrier := {x | x.unop ∈ F.ideal k}
      add_mem' := add_mem
      zero_mem' := zero_mem (F.ideal k)
      smul_mem' a x hx := F.mul_mem (b := 0) hx (by simp) }
  isTwoSided k := ⟨fun b hx => (F.ideal k).smul_mem b.unop hx⟩
  antitone _ _ h _ hx := F.antitone h hx
  ideal_zero := by
    ext
    simp
  mul_mem {a b} _ _ hx hy := by
    have h := F.mul_mem hy hx
    rw [Nat.add_comm b a] at h
    exact h

variable {F}

/-- An element of `Aᵐᵒᵖ` lies in the opposite filtration exactly when its image in `A` lies in
the filtration. -/
@[simp]
theorem mem_op_ideal {k : ℕ} {x : Aᵐᵒᵖ} : x ∈ F.op.ideal k ↔ x.unop ∈ F.ideal k :=
  (Iff.rfl)

/-- The opposite of a complete separated filtration is complete and separated. -/
theorem isCompleteFiltration_op (hF : IsCompleteFiltration F.ideal) :
    IsCompleteFiltration F.op.ideal where
  antitone := F.op.antitone
  eq_zero_of_forall_mem x hx := unop_injective (hF.eq_zero_of_forall_mem x.unop fun n => by
    simpa using hx n)
  exists_limit x hx := by
    obtain ⟨L, hL⟩ := hF.exists_limit (fun n => (x n).unop) fun n => by simpa using hx n
    exact ⟨MulOpposite.op L, fun n => by simpa using hL n⟩

variable (F) in
/-- The `n`-th term of the opposite filtration is additively the `n`-th term of the
filtration. -/
private def opIdealEquiv (n : ℕ) : F.op.ideal n ≃+ F.ideal n where
  toFun x := ⟨x.val.unop, mem_op_ideal.1 x.property⟩
  invFun y := ⟨MulOpposite.op y.val, mem_op_ideal.2 y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (F) in
/-- The graded pieces of the opposite filtration are those of the filtration. -/
def gradedPieceOpEquiv (n : ℕ) : F.op.GradedPiece n ≃+ F.GradedPiece n :=
  QuotientAddGroup.congr _ _ (opIdealEquiv F n) <| by
    ext y
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
      LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, mem_op_ideal]
    exact ⟨fun ⟨_, hx, hxy⟩ => hxy ▸ hx,
      fun hy => ⟨(opIdealEquiv F n).symm y, hy, (opIdealEquiv F n).apply_symm_apply y⟩⟩

/-- The identification of graded pieces keeps representatives. -/
@[simp]
theorem gradedPieceOpEquiv_mk {n : ℕ} (x : F.op.ideal n) :
    F.gradedPieceOpEquiv n x =
      ((⟨x.val.unop, mem_op_ideal.1 x.property⟩ : F.ideal n) : F.GradedPiece n) :=
  (rfl)

/-- The ring homomorphism `gr (Aᵐᵒᵖ) → (gr A)ᵐᵒᵖ` sending the class of `x` to the class of
`x.unop`. -/
private def associatedGradedOpHom : F.op.AssociatedGraded →+* F.AssociatedGradedᵐᵒᵖ :=
  DirectSum.toSemiring
    (fun i => (opAddEquiv : F.AssociatedGraded ≃+ _).toAddMonoidHom.comp
      ((DirectSum.of F.GradedPiece i).comp (F.gradedPieceOpEquiv i).toAddMonoidHom))
    (by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, gOne_def, gradedZeroMk_apply,
        AddEquiv.coe_toAddMonoidHom, gradedPieceOpEquiv_mk, unop_one, opAddEquiv_apply,
        op_eq_one_iff]
      rw [one_eq_of_gradedZeroMk, gradedZeroMk_apply])
    fun {i j} x y => by
      induction x using QuotientAddGroup.induction_on with | H x =>
      induction y using QuotientAddGroup.induction_on with | H y =>
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, gMul_def, gradedMul_mk_mk,
        AddEquiv.coe_toAddMonoidHom, gradedPieceOpEquiv_mk, opAddEquiv_apply, ← op_mul,
        of_mk_mul_of_mk, op_inj, unop_mul]
      exact of_mk_eq_of_mk (Nat.add_comm i j) _ _ _

/-- Additively, `associatedGradedOpHom` is the identification of graded pieces in each degree. -/
private theorem associatedGradedOpHom_eq :
    ⇑(associatedGradedOpHom (F := F)) =
      (DFinsupp.mapRange.addEquiv F.gradedPieceOpEquiv).trans
        (opAddEquiv : F.AssociatedGraded ≃+ F.AssociatedGradedᵐᵒᵖ) := by
  refine congrArg DFunLike.coe
    (DirectSum.addHom_ext (f := (associatedGradedOpHom (F := F)).toAddMonoidHom)
      (g := ((DFinsupp.mapRange.addEquiv F.gradedPieceOpEquiv).trans
        (opAddEquiv : F.AssociatedGraded ≃+ F.AssociatedGradedᵐᵒᵖ)).toAddMonoidHom)
      fun i x => ?_)
  -- `DirectSum.of` is `DFinsupp.single`, on which `DFinsupp.mapRange` is computed.
  have hof : DirectSum.of F.op.GradedPiece i x = DFinsupp.single i x := rfl
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, associatedGradedOpHom,
    DirectSum.toSemiring_of, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply, opAddEquiv_apply]
  rw [hof, DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_single]
  rfl

variable (F) in
/-- The associated graded ring of the opposite filtration is the opposite of the associated graded
ring: the class of `x ∈ (Aᵐᵒᵖ)ⁿ` corresponds to the class of `x.unop ∈ Aⁿ`. -/
noncomputable def associatedGradedOpEquiv : F.op.AssociatedGraded ≃+* F.AssociatedGradedᵐᵒᵖ :=
  RingEquiv.ofBijective associatedGradedOpHom
    (associatedGradedOpHom_eq (F := F) ▸ AddEquiv.bijective _)

/-- The ring isomorphism `gr (Aᵐᵒᵖ) ≃+* (gr A)ᵐᵒᵖ` on homogeneous classes. -/
@[simp]
theorem associatedGradedOpEquiv_of_mk {n : ℕ} (x : F.op.ideal n) :
    F.associatedGradedOpEquiv (DirectSum.of F.op.GradedPiece n (x : F.op.GradedPiece n)) =
      MulOpposite.op (DirectSum.of F.GradedPiece n
        ((⟨x.val.unop, mem_op_ideal.1 x.property⟩ : F.ideal n) : F.GradedPiece n)) := by
  simp [associatedGradedOpEquiv, associatedGradedOpHom]

/-- A ring with a complete separated decreasing ideal filtration whose associated graded ring is
right noetherian is right noetherian. -/
theorem isNoetherianRing_mulOpposite_of_isNoetherianRing_mulOpposite_associatedGraded
    (hF : IsCompleteFiltration F.ideal) [IsNoetherianRing F.AssociatedGradedᵐᵒᵖ] :
    IsNoetherianRing Aᵐᵒᵖ :=
  have := isNoetherianRing_of_ringEquiv _ (associatedGradedOpEquiv F).symm
  isNoetherianRing_of_isNoetherianRing_associatedGraded (isCompleteFiltration_op hF)

end TauCeti.AlgFiltration
