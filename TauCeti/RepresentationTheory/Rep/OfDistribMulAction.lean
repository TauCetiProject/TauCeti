/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.GroupTheory.GroupAction.FixedPoints

/-!
# Fixed points of a distributive action as a quotient representation

Let a group `G` act distributively on an additive group `M`, and let `H` be a normal subgroup of
`G`. There are two ways to make the `H`-fixed points of `M` into a `ℤ`-linear representation of
`G ⧸ H`:

* Mathlib's `Rep.quotientToInvariants` applied to `Rep.ofDistribMulAction ℤ G M`, whose carrier is
  the submodule of invariants of the restricted representation;
* `Rep.ofDistribMulAction ℤ (G ⧸ H)` applied to the additive subgroup
  `FixedPoints.addSubgroup H M`, with the quotient action of
  `TauCeti.distribMulActionQuotientFixedPointsAddSubgroup`.

The first is the coefficient module of Mathlib's group cohomology of `G ⧸ H`, for instance of
inflation and of the finite-quotient system `TauCeti.finiteQuotientSystem`; the second is the one
the explicit cochain description of cohomology uses. This file identifies the two.

## Main definitions

* `TauCeti.ofDistribMulActionFixedPointsIso`: the isomorphism of representations of `G ⧸ H`
  between `Rep.ofDistribMulAction ℤ (G ⧸ H) (FixedPoints.addSubgroup H M)` and
  `(Rep.ofDistribMulAction ℤ G M).quotientToInvariants H`. It does not move an element of `M`
  (`TauCeti.ofDistribMulActionFixedPointsIso_hom_hom_apply_coe`).
-/

public section

namespace TauCeti

open CategoryTheory

universe u w

variable {G : Type u} [Group G] (M : Type w) [AddCommGroup M] [DistribMulAction G M]
  (H : Subgroup G) [H.Normal]

/-- The representation of `G ⧸ H` on the fixed points `M ^ H` of a distributive action is Mathlib's
representation `Rep.quotientToInvariants` on the `H`-invariants of `Rep.ofDistribMulAction ℤ G M`.
Both have the same elements of `M`, and the isomorphism does not move them. -/
noncomputable def ofDistribMulActionFixedPointsIso :
    Rep.ofDistribMulAction ℤ (G ⧸ H) (FixedPoints.addSubgroup H M) ≅
      (Rep.ofDistribMulAction ℤ G M).quotientToInvariants H :=
  Rep.mkIso <| .mk (AddEquiv.toIntLinearEquiv
    { toFun m := ⟨(m : M), fun h ↦ (FixedPoints.mem_addSubgroup H M _).1 m.property h⟩
      invFun m := ⟨m.val, (FixedPoints.mem_addSubgroup H M _).2 fun h ↦ m.property h⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }) fun q ↦ by
    -- On the class of `g`, both actions are the action of `g` on `M`.
    induction q using QuotientGroup.induction_on with
    | H g => rfl

/-- `ofDistribMulActionFixedPointsIso` does not move an element of `M`. -/
@[simp]
theorem ofDistribMulActionFixedPointsIso_hom_hom_apply_coe (m : FixedPoints.addSubgroup H M) :
    ((ofDistribMulActionFixedPointsIso M H).hom.hom m).val = (m : M) :=
  (rfl)

/-- The inverse of `ofDistribMulActionFixedPointsIso` does not move an element of `M`. -/
@[simp]
theorem ofDistribMulActionFixedPointsIso_inv_hom_apply_coe
    (m : Representation.invariants ((Rep.ofDistribMulAction ℤ G M).ρ.comp H.subtype)) :
    ((ofDistribMulActionFixedPointsIso M H).inv.hom m).val = m.val :=
  (rfl)

end TauCeti
