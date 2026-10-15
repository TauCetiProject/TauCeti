/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.CategoryTheory.Monoidal.Mod
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction

/-!
# Internal actions from the toric coaction

The coordinate-ring coaction is an internal action in the opposite category of complex
algebras. Its unit and associativity laws are the counit and coassociativity identities of
the coaction. Face restrictions are equivariant morphisms of these internal actions.

This packaging allows a lax monoidal functor, in particular the spectrum functor, to
transport the action and its laws together. No regularity or finite-generation assumption
on the cone is needed.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open CategoryTheory MonoidalCategory MonObj Opposite

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The toric coaction as an internal action of the zero-cone monoid object on the cone
algebra, in the opposite category of complex algebras. -/
@[instance_reducible]
noncomputable def affineCoordinateRingCoactionModObj (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    ModObj (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
      (op (CommAlgCat.of ℂ (affineCoordinateRing hi σ))) where
  smul := (CommAlgCat.ofHom (affineCoordinateRingCoaction hi σ)).op
  one_smul := by
    simp only [selfLeftAction_actionUnitIso]
    rw [← cancel_epi (λ_ (op (CommAlgCat.of ℂ (affineCoordinateRing hi σ)))).inv,
      Iso.inv_hom_id]
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact affineCoordinateRingCoaction_counit hi σ
  mul_smul := by
    simp only [selfLeftAction_actionAssocIso]
    rw [← cancel_epi (α_
      (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
      (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
      (op (CommAlgCat.of ℂ (affineCoordinateRing hi σ)))).inv,
      Iso.inv_hom_id_assoc]
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact affineCoordinateRingCoaction_coassoc hi σ

/-- The internal action has precisely the toric coaction as its comorphism. -/
@[simp]
theorem affineCoordinateRingCoactionModObj_smul (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    (affineCoordinateRingCoactionModObj hi σ).smul =
      (CommAlgCat.ofHom (affineCoordinateRingCoaction hi σ)).op := by
  rw [affineCoordinateRingCoactionModObj]
  rfl

/-- Restriction to a face is a morphism of internal torus actions. -/
theorem isModHom_faceAffineCoordinateRingMap (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ) :
    letI := affineCoordinateRingCoactionModObj hi τ
    letI := affineCoordinateRingCoactionModObj hi σ
    IsModHom (op (CommAlgCat.of ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
      (CommAlgCat.ofHom (faceAffineCoordinateRingMap hi hτσ)).op := by
  let := affineCoordinateRingCoactionModObj hi τ
  let := affineCoordinateRingCoactionModObj hi σ
  constructor
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact affineCoordinateRingCoaction_comp_face hi hτσ

/-- On the zero cone, the internal torus action is the regular action on itself. -/
@[simp]
theorem affineCoordinateRingCoactionModObj_bot (hi : IsIntegralLattice i) :
    affineCoordinateRingCoactionModObj hi (⊥ : PointedCone ℝ V) =
      ModObj.regular (op (CommAlgCat.of ℂ
        (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))) := by
  apply ModObj.ext
  rw [affineCoordinateRingCoactionModObj_smul]
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact affineCoordinateRingCoaction_bot hi

end TauCeti.Toric
