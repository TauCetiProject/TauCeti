/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Basic

/-!
# The Drinfeld centre of a pivotal category is pivotal

Let `C` be a rigid monoidal category with a pivotal structure `φ_X : X ≅ Xᘁᘁ`. The Drinfeld
centre `Center C` is rigid, with the right dual of `(X, β)` the right dual `Xᘁ` of `X` carrying the
induced half-braiding, so the double right dual of `(X, β)` is `Xᘁᘁ` with the half-braiding induced
twice. The components of `φ` lift to the centre: `φ_X` intertwines the half-braiding `β` of `X`
with the twice-induced half-braiding of `Xᘁᘁ`. Since the forgetful functor `Center C ⥤ C` is
faithful and carries the unit and tensor comparisons of the double right dual functor of the
centre to those of `C`, the lifted components form a monoidal natural isomorphism from the
identity functor of `Center C` to its double right dual functor, that is, a pivotal structure on
the centre. Together with the braiding of the centre, this makes `Center C` a braided pivotal
category.

The intertwining property comes from naturality and monoidality of `φ`. Naturality at the
half-braiding `β U : X ⊗ U ⟶ U ⊗ X` says that `β U` is conjugate under `φ` to its double mate,
and monoidality writes `φ` at `X ⊗ U` and at `U ⊗ X` through `φ_X` and `φ_U`. On the other side,
the half-braiding induced on `Xᘁ` is, at `Uᘁ`, the mate of `β U`
(`CategoryTheory.HalfBraiding.rightDualβHom_rightDual`), so the twice-induced half-braiding of
`Xᘁᘁ` is, at `Uᘁᘁ`, the double mate of `β U`; naturality in `U` moves it back along `φ_U`.

## Main declarations

* `CategoryTheory.HalfBraiding.pivotalIsoApp_hom_whiskerRight_comp_rightDual_rightDual_β_hom`:
  the component `φ_X` intertwines a half-braiding of `X` with the half-braiding it induces on
  `Xᘁᘁ`;
* `CategoryTheory.Center.pivotalCategory`: the pivotal structure on the centre of a pivotal
  category, whose components are those of `C` (`CategoryTheory.Center.pivotalIsoApp_hom_f` and
  `CategoryTheory.Center.pivotalIsoApp_inv_f`).

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937),
  Proposition 2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13 and 8.10
-/

public section

open CategoryTheory MonoidalCategory TauCeti

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

namespace HalfBraiding

variable {X : C} (b : HalfBraiding X)

/-- In a pivotal category, the component `φ_X : X ⟶ Xᘁᘁ` of the pivotal structure intertwines a
half-braiding `b` of `X` with the half-braiding induced from it on the double right dual `Xᘁᘁ`. -/
theorem pivotalIsoApp_hom_whiskerRight_comp_rightDual_rightDual_β_hom (U : C) :
    (pivotalIsoApp X).hom ▷ U ≫ (((b.rightDual Xᘁ).rightDual ((Xᘁ : C)ᘁ : C)).β U).hom =
      (b.β U).hom ≫ U ◁ (pivotalIsoApp X).hom := by
  rw [rightDual_β, rightDualβ_hom]
  -- The monoidality of the pivotal structure, with the tensor comparison of the double right dual
  -- functor written out, so that every object below is an iterated right dual.
  have hT (A B : C) : (pivotalIsoApp (A ⊗ B)).hom =
      ((pivotalIsoApp A).hom ⊗ₘ (pivotalIsoApp B).hom) ≫ (rightDualTensorIso Bᘁ Aᘁ).inv ≫
        ((rightDualTensorIso A B).hom)ᘁ :=
    (pivotalIsoApp_tensor_hom A B).trans (congrArg _ (doubleRightDualFunctor_μ C A B))
  -- Move the induced half-braiding of `Xᘁᘁ` from `U` to `Uᘁᘁ` by naturality.
  have hN : (b.rightDual Xᘁ).rightDualβHom ((Xᘁ : C)ᘁ : C) U =
      ((Xᘁ : C)ᘁ : C) ◁ (pivotalIsoApp U).hom ≫
        (b.rightDual Xᘁ).rightDualβHom ((Xᘁ : C)ᘁ : C) ((Uᘁ : C)ᘁ : C) ≫
          (pivotalIsoApp U).inv ▷ ((Xᘁ : C)ᘁ : C) := by
    rw [rightDualβHom_naturality_assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
      Category.comp_id]
  -- At `Uᘁᘁ` it is the double mate of `b.β U`, which is conjugate to `b.β U` under `φ`.
  rw [hN, (b.rightDual Xᘁ).rightDualβHom_rightDual, rightDual_β, rightDualβ_hom,
    b.rightDualβHom_rightDual]
  simp only [comp_rightAdjointMate, rightAdjointMate_rightAdjointMate, Category.assoc]
  calc
    _ = (pivotalIsoApp (X ⊗ U)).hom ≫ (pivotalIsoApp (X ⊗ U)).inv ≫ (b.β U).hom ≫
          (pivotalIsoApp (U ⊗ X)).hom ≫ ((rightDualTensorIso U X).inv)ᘁ ≫
            (rightDualTensorIso Xᘁ Uᘁ).hom ≫ (pivotalIsoApp U).inv ▷ ((Xᘁ : C)ᘁ : C) := by
      rw [hT X U, tensorHom_def]
      simp only [Category.assoc]
    _ = _ := by
      rw [Iso.hom_inv_id_assoc, hT U X, tensorHom_def']
      simp only [Category.assoc]
      rw [← comp_rightAdjointMate_assoc, Iso.inv_hom_id, rightAdjointMate_id, Category.id_comp,
        Iso.inv_hom_id_assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
        Category.comp_id]

end HalfBraiding

namespace Center

open Functor.LaxMonoidal

/-- **The Drinfeld centre of a pivotal category is pivotal.** The component at `X : Center C` is
the component `φ_{X.1} : X.1 ≅ X.1ᘁᘁ` of the pivotal structure of `C`, which is a morphism of the
centre from `X` to its double right dual. -/
noncomputable instance pivotalCategory : PivotalCategory (Center C) where
  pivotalIso := NatIso.ofComponents
    (fun X => @isoMk _ _ _ _ _
      ⟨(pivotalIsoApp X.1).hom, X.2.pivotalIsoApp_hom_whiskerRight_comp_rightDual_rightDual_β_hom⟩
      (inferInstanceAs (IsIso (pivotalIsoApp X.1).hom)))
    (fun f => by
      ext
      have h : (fᘁᘁ).f = (f.f)ᘁᘁ := by
        rw [rightAdjointMate_f, rightAdjointMate_f]
        -- The two sides differ only in how `(Xᘁ).1` and `X.1ᘁ` are written.
        exact rfl
      exact (pivotalIsoApp_hom_naturality f.f).trans (congrArg _ h.symm))
  pivotalIso_isMonoidal :=
    { unit := by
        ext
        simp only [Functor.LaxMonoidal.id_ε, NatIso.ofComponents_hom_app, isoMk_hom,
          Category.id_comp, doubleRightDualFunctor_ε_f]
        exact pivotalIsoApp_unit_hom
      tensor := fun (X Y : Center C) => by
        ext
        simp only [Functor.LaxMonoidal.id_μ, NatIso.ofComponents_hom_app, isoMk_hom, comp_f,
          Category.id_comp, tensor_f, doubleRightDualFunctor_μ_f]
        exact pivotalIsoApp_tensor_hom X.1 Y.1 }

/-- The component of the pivotal structure of the centre at `X` is that of `C` at `X.1`. -/
@[simp]
theorem pivotalIsoApp_hom_f (X : Center C) : (pivotalIsoApp X).hom.f = (pivotalIsoApp X.1).hom := by
  rw [← pivotalIso_hom_app]
  -- The component of `pivotalCategory` at `X` is defined to be `pivotalIsoApp X.1`.
  exact rfl

/-- The inverse of the component of the pivotal structure of the centre at `X` is that of `C` at
`X.1`. -/
@[simp]
theorem pivotalIsoApp_inv_f (X : Center C) : (pivotalIsoApp X).inv.f = (pivotalIsoApp X.1).inv := by
  have h := congrArg Hom.f (pivotalIsoApp X).inv_hom_id
  simp only [comp_f, id_f, pivotalIsoApp_hom_f] at h
  exact (Iso.comp_hom_eq_id _).1 h

end Center

end CategoryTheory
