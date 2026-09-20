/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Induction.Restriction

/-!
# The unit map into an induced representation

For a finite-index subgroup `S` of a group `G`, every finite-dimensional representation `A` of
`S` maps naturally into the restriction of `Ind_S^G A`.  On Mathlib's induced carrier this is the
map `a ↦ ⟦1 ⊗ a⟧`; this file transports it to the small carrier used by
`TauCeti.indFDRep`.

The map is injective.  This is the representation-theoretic statement that the identity coset
supplies a distinguished copy of `A` inside the restriction of its induced representation.  It is
used in Clifford theory to show that induction preserves the property of lying over a constituent.

## Main definitions

* `TauCeti.indFDRepUnit`: the canonical map `A ⟶ Res_S (Ind_S^G A)`.

## Main statements

* `TauCeti.indFDRepUnit_apply`: the map on the induced-representation model.
* `TauCeti.indFDRepUnit_injective`: the unit map is injective.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- The unit of induction--restriction on finite-dimensional representations.  Under the
comparison with Mathlib's induced carrier it sends `a` to the generator `⟦1 ⊗ a⟧`. -/
noncomputable def indFDRepUnit (A : FDRep k S) : A ⟶ resFDRep S (indFDRep A) :=
  FDRep.forget₂HomLinearEquiv A (resFDRep S (indFDRep A)) <|
    (Rep.indResAdjunction k S.subtype).unit.app
      ((forget₂ (FDRep k S) (Rep k S)).obj A) ≫
    (Rep.resFunctor S.subtype).map (indFDRepForgetIso A).inv

/-- On Mathlib's induced carrier, `indFDRepUnit` is the generator map `a ↦ ⟦1 ⊗ a⟧`. -/
theorem indFDRepUnit_apply (A : FDRep k S) (a : A) :
    indFDRepForgetEquiv A (indFDRepUnit A a) =
      Representation.IndV.mk S.subtype
        ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 a := by
  -- The small induced carrier is sealed, so expose it through its public comparison isomorphism.
  change indFDRepForgetEquiv A
      ((indFDRepForgetIso A).inv.hom
        (Representation.IndV.mk S.subtype
          ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 a)) = _
  rw [indFDRepForgetIso_inv_hom_apply,
    Representation.Equiv.apply_symm_apply]

/-- The unit map from a representation to the restriction of its induction is injective. -/
theorem indFDRepUnit_injective (A : FDRep k S) : Function.Injective (indFDRepUnit A) := by
  intro a b hab
  have h : indFDRepForgetEquiv A (indFDRepUnit A a) =
      indFDRepForgetEquiv A (indFDRepUnit A b) := congrArg (indFDRepForgetEquiv A) hab
  rw [indFDRepUnit_apply, indFDRepUnit_apply] at h
  let _ : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  have h' := congrArg
    (fun x => ((Rep.indCoindIso
      ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom x).1 1) h
  have heval (x : (forget₂ (FDRep k S) (Rep k S)).obj A) :
      ((Rep.indCoindIso ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom
        (Representation.IndV.mk S.subtype
          ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 x)).1 1 = x := by
    -- Pass from the bundled representation morphism to its linear map so the generated
    -- `indCoindIso_hom_hom_toLinearMap` equation can rewrite it.
    change (((Rep.indCoindIso
      ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom.toLinearMap
        (Representation.IndV.mk S.subtype
          ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 x))).1 1 = x
    rw [show (Rep.indCoindIso
      ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom.toLinearMap =
        Rep.indToCoind ((forget₂ (FDRep k S) (Rep k S)).obj A) from
      Rep.indCoindIso_hom_hom_toLinearMap _]
    simp only [FGModuleCat.obj_carrier, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.mk_apply, Representation.Coinvariants.lift_mk, TensorProduct.lift.tmul,
      LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
      MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, one_smul]
    -- The remaining subtype coercion is the defining codomain restriction in `indToCoind`.
    change (Rep.indToCoindAux
      ((forget₂ (FDRep k S) (Rep k S)).obj A) 1 x) 1 = x
    exact Rep.indToCoindAux_self 1 x
  exact (heval a).symm.trans (h'.trans (heval b))

end TauCeti
