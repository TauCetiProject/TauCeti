/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Rigid
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor

/-!
# The pivotal structure on the Drinfeld centre

Let `C` be a rigid monoidal category. Its Drinfeld centre `Center C` is rigid, with the right dual
of `(X, β)` the right dual `Xᘁ` of `C`, carrying the half-braiding obtained from `β` by taking
mates. A pivotal structure `φ : 𝟭 C ≅ doubleRightDualFunctor C` on `C` induces one on
`Center C`, whose component at `(X, β)` is `φ_X : X ≅ Xᘁᘁ`.

The content is that `φ_X` is a morphism of the centre, that is, that it intertwines `β` with the
half-braiding induced on the double dual `Xᘁᘁ`. Taking mates twice, the induced half-braiding at
an object `Uᘁᘁ` is the double mate `(β_U)ᘁᘁ`, read through the tensor comparisons
`μ : Xᘁᘁ ⊗ Uᘁᘁ ≅ (X ⊗ U)ᘁᘁ` and `δ : (U ⊗ X)ᘁᘁ ≅ Uᘁᘁ ⊗ Xᘁᘁ` of the double right dual functor
(`CategoryTheory.HalfBraiding.rightDualβHom_rightDual_rightDual`). Naturality of `φ` at `β_U`
and its monoidality then show that `φ_X` intertwines the half-braidings at `U`, after composing
with `φ_U`. Naturality and monoidality of the lifted components hold because they hold in `C` and
the forgetful functor `Center.forget C` is faithful; the tensor comparison of the double right
dual functor of the centre is computed in `C`.

The forgetful functor is then a pivotal functor, so traces and dimensions in the centre are
computed in `C`, and the centre of a spherical category is spherical. Together with the braiding
of the centre, this is the pivotal and spherical structure on `Center C` used to study the centre
of a spherical fusion category.

## Main declarations

* `CategoryTheory.HalfBraiding.pivotalIsoApp_hom_whiskerRight_comp_rightDual_rightDual_β_hom`: in
  a pivotal category, `φ_X` intertwines a half-braiding on `X` with the one induced on `Xᘁᘁ`;
* `CategoryTheory.Center.pivotalCategory`: the pivotal structure on the centre of a pivotal
  category, with components computed by `CategoryTheory.Center.pivotalIsoApp_hom_f`;
* `CategoryTheory.Center.isPivotal_forget`: the forgetful functor from the centre is pivotal, so
  that `CategoryTheory.Center.leftTrace_f` and `CategoryTheory.Center.rightTrace_f` compute the
  traces of the centre in `C`;
* `CategoryTheory.Center.sphericalCategory`: the centre of a spherical category is spherical.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937),
  Proposition 2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal TauCeti

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace HalfBraiding

variable {X : C} (b : HalfBraiding X) [RigidCategory C] [PivotalCategory C]

/-- In a pivotal category, the pivotal isomorphism `φ_X : X ≅ Xᘁᘁ` intertwines a half-braiding on
`X` with the half-braiding induced on the double right dual `Xᘁᘁ`. -/
theorem pivotalIsoApp_hom_whiskerRight_comp_rightDual_rightDual_β_hom (U : C) :
    (pivotalIsoApp X).hom ▷ U ≫ (((b.rightDual Xᘁ).rightDual Xᘁᘁ).β U).hom =
      (b.β U).hom ≫ U ◁ (pivotalIsoApp X).hom := by
  rw [rightDual_β, rightDualβ_hom]
  -- Monoidality of `φ`, with the tensor comparison of the double right dual functor unfolded.
  have hφ (Y Z : C) : (pivotalIsoApp (Y ⊗ Z)).hom = ((pivotalIsoApp Y).hom ⊗ₘ
      (pivotalIsoApp Z).hom) ≫ (rightDualTensorIso Zᘁ Yᘁ).inv ≫ ((rightDualTensorIso Y Z).hom)ᘁ :=
    (pivotalIsoApp_tensor_hom Y Z).trans (congrArg _ (doubleRightDualFunctor_μ C Y Z))
  have hc : ((rightDualTensorIso U X).hom)ᘁ ≫ ((rightDualTensorIso U X).inv)ᘁ = 𝟙 _ := by
    rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
  -- Compose both sides with the isomorphism `φ_U ▷ Xᘁᘁ`. Naturality of the induced
  -- half-braiding moves `φ_U` to the left, where `φ_X ⊗ φ_U` combines with the tensor
  -- comparison into `φ_{X ⊗ U}`; naturality of `φ` at `β_U` then moves `φ` back to the right,
  -- where the comparisons cancel.
  rw [← cancel_mono ((pivotalIsoApp U).hom ▷ ((Xᘁ : C)ᘁ : C)), Category.assoc,
    ← rightDualβHom_naturality, ← tensorHom_def_assoc, rightDualβHom_rightDual_rightDual,
    ← reassoc_of% hφ, ← pivotalIsoApp_hom_naturality_assoc, hφ]
  simp [reassoc_of% hc, tensorHom_def']

end HalfBraiding

namespace Center

/-- An endomorphism `a` of the unit of the centre has underlying endomorphism `b` as soon as `b` is
the image of `a` under the forgetful functor, read through its unit comparisons. -/
private theorem f_eq_of_eq_forget_map {a : 𝟙_ (Center C) ⟶ 𝟙_ (Center C)} {b : 𝟙_ C ⟶ 𝟙_ C}
    (h : b = ε (forget C) ≫ (forget C).map a ≫ η (forget C)) : a.f = b := by
  simp only [forget_ε, forget_η, forget_map] at h
  exact (h.trans ((Category.id_comp _).trans (Category.comp_id _))).symm

variable [RigidCategory C]

/-- The tensor comparison of the double right dual functor of the centre is computed in `C`. -/
@[simp]
theorem doubleRightDualFunctor_μ_f (X Y : Center C) :
    (μ (doubleRightDualFunctor (Center C)) X Y).f = μ (doubleRightDualFunctor C) X.1 Y.1 := by
  rw [doubleRightDualFunctor_μ, doubleRightDualFunctor_μ, comp_f, rightAdjointMate_f,
    rightDualTensorIso_inv_f, rightDualTensorIso_hom_f]
  -- The remaining difference is only in how the objects `(Xᘁ).1` and `X.1ᘁ` are written.
  rfl

/-- The comparison between the image of a right dual under the forgetful functor of the centre
and the right dual of the image is the identity: right duals in the centre are computed in
`C`. -/
@[simp]
theorem forget_mapRightDualIso (X : Center C) :
    (forget C).mapRightDualIso X = Iso.refl X.1ᘁ := by
  ext
  refine ExactPairing.rightHom_ext (X := X.1) (Y := X.1ᘁ)
    ((Functor.mapRightDualIso_hom_whiskerRight_evaluation X).trans ?_)
  have h : 𝟙 X.1ᘁ ▷ X.1 ≫ ε_ X.1 X.1ᘁ = ε_ X.1 X.1ᘁ := by simp
  exact (Category.id_comp _).trans ((Category.comp_id _).trans ((evaluation_f (X := X)).trans
    h.symm))

variable [PivotalCategory C]

/-- Auxiliary definition for the `PivotalCategory` instance on `Center C`: the component
`φ_{X.1} : X.1 ⟶ X.1ᘁᘁ` of the pivotal structure of `C`, as a morphism of the centre. -/
noncomputable def pivotalIsoAppHom (X : Center C) : X ⟶ ((Xᘁ : Center C)ᘁ : Center C) where
  f := (pivotalIsoApp X.1).hom
  comm U := by
    simp only [rightDual_snd]
    exact X.2.pivotalIsoApp_hom_whiskerRight_comp_rightDual_rightDual_β_hom U

private theorem pivotalIsoAppHom_f (X : Center C) :
    (pivotalIsoAppHom X).f = (pivotalIsoApp X.1).hom :=
  (rfl)

private theorem pivotalIsoAppHom_naturality {X Y : Center C} (f : X ⟶ Y) :
    f ≫ pivotalIsoAppHom Y = pivotalIsoAppHom X ≫ fᘁᘁ := by
  ext
  simp only [comp_f, pivotalIsoAppHom_f, rightAdjointMate_f]
  exact pivotalIsoApp_hom_naturality f.f

private instance (X : Center C) : IsIso (pivotalIsoAppHom X).f := by
  rw [pivotalIsoAppHom_f]
  exact Iso.isIso_hom _

/-- Auxiliary definition for the `PivotalCategory` instance on `Center C`: the natural isomorphism
`𝟭 (Center C) ≅ doubleRightDualFunctor (Center C)` with components `pivotalIsoAppHom`. -/
noncomputable def pivotalNatIso : 𝟭 (Center C) ≅ doubleRightDualFunctor (Center C) :=
  NatIso.ofComponents (fun X => (isoMk (pivotalIsoAppHom X) : X ≅ ((Xᘁ : Center C)ᘁ : Center C)))
    pivotalIsoAppHom_naturality

private theorem pivotalNatIso_hom_app_f (X : Center C) :
    (pivotalNatIso.hom.app X).f = (pivotalIsoApp X.1).hom := by
  unfold pivotalNatIso
  exact pivotalIsoAppHom_f X

/-- The pivotal structure of a pivotal category `C` induces a pivotal structure on its Drinfeld
centre, with components the pivotal isomorphisms `X.1 ≅ X.1ᘁᘁ` of `C`. -/
noncomputable instance pivotalCategory : PivotalCategory (Center C) where
  pivotalIso := pivotalNatIso
  pivotalIso_isMonoidal := .of_tensor _ fun X Y => by
    ext
    simp only [comp_f, pivotalNatIso_hom_app_f, tensor_f, doubleRightDualFunctor_μ_f]
    exact (Category.id_comp _).trans (pivotalIsoApp_tensor_hom X.1 Y.1)

/-- The components of the pivotal isomorphism of the centre are those of `C`. -/
@[simp]
theorem pivotalIsoApp_hom_f (X : Center C) :
    (pivotalIsoApp X).hom.f = (pivotalIsoApp X.1).hom := by
  rw [← pivotalIso_hom_app (X := X)]
  exact pivotalNatIso_hom_app_f X

/-- The inverses of the components of the pivotal isomorphism of the centre are those of `C`. -/
@[simp]
theorem pivotalIsoApp_inv_f (X : Center C) :
    (pivotalIsoApp X).inv.f = (pivotalIsoApp X.1).inv := by
  have h := congrArg Hom.f (pivotalIsoApp X).hom_inv_id
  rw [comp_f, pivotalIsoApp_hom_f, id_f] at h
  exact (Iso.hom_comp_eq_id _).1 h

/-- The forgetful functor from the centre of a pivotal category is a pivotal functor. -/
instance isPivotal_forget : (forget C).IsPivotal :=
  .mk' fun X => by
    simp only [forget_map, pivotalIsoApp_hom_f, forget_mapRightDualIso, rightDual_fst,
      Iso.refl_hom]
    -- The remaining identity `(𝟙 _)ᘁ` is stated at the object `(Xᘁ).1ᘁ`, which is `X.1ᘁᘁ`
    -- only up to unfolding, so `rightAdjointMate_id` is applied by unification.
    congr 1
    exact rightAdjointMate_id.symm

/-- The left trace of an endomorphism of the centre is its left trace in `C`. -/
@[simp]
theorem leftTrace_f {X : Center C} (f : X ⟶ X) : (leftTrace f).f = leftTrace f.f :=
  f_eq_of_eq_forget_map ((forget C).leftTrace_map f)

/-- The right trace of an endomorphism of the centre is its right trace in `C`. -/
@[simp]
theorem rightTrace_f {X : Center C} (f : X ⟶ X) : (rightTrace f).f = rightTrace f.f :=
  f_eq_of_eq_forget_map ((forget C).rightTrace_map f)

/-- The left dimension of an object of the centre is the left dimension of its underlying
object. -/
@[simp]
theorem leftDim_f (X : Center C) : (leftDim X).f = leftDim X.1 :=
  f_eq_of_eq_forget_map ((forget C).leftDim_map X)

/-- The right dimension of an object of the centre is the right dimension of its underlying
object. -/
@[simp]
theorem rightDim_f (X : Center C) : (rightDim X).f = rightDim X.1 :=
  f_eq_of_eq_forget_map ((forget C).rightDim_map X)

/-- The Drinfeld centre of a spherical category is spherical, for the induced pivotal
structure. -/
instance sphericalCategory [SphericalCategory C] : SphericalCategory (Center C) where
  leftTrace_eq_rightTrace f := by
    ext
    exact (leftTrace_f f).trans
      ((SphericalCategory.leftTrace_eq_rightTrace f.f).trans (rightTrace_f f).symm)

end Center

end CategoryTheory
