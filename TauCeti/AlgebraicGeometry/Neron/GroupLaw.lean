/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Over
public import TauCeti.AlgebraicGeometry.Neron.Model

/-!
# The group law of a Néron model

Let `j : T ⟶ S` be a morphism of schemes (in the arithmetic application, the inclusion of the
generic point of a Dedekind scheme) and let `M` be a Néron model of a group object `A` of
`Over T`, such as an abelian variety. The model carries exactly one group object structure in
`Over S` for which the marking `M.genericIso : (Over.pullback j).obj M.model ≅ A` is a
homomorphism (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Proposition 6).

Products of smooth `S`-schemes are smooth, so the identity, the multiplication and the inverse
of `A` extend uniquely to morphisms `𝟙_ (Over S) ⟶ M.model`, `M.model ⊗ M.model ⟶ M.model`
and `M.model ⟶ M.model` by the Néron mapping property, and the group axioms hold on the model
because base change along `j` is injective on morphisms out of smooth `S`-schemes. The
construction follows Mathlib's `CategoryTheory.Functor.FullyFaithful.grpObj` and Tau Ceti's
`CategoryTheory.Functor.grpObjOfFaithful`, which pull a group object back along a fully faithful,
respectively faithful, monoidal functor. Neither applies here: the base change functor
`Over.pullback j` is monoidal but not faithful, and the mapping property supplies the injectivity
and surjectivity of base change only on morphisms out of smooth `S`-schemes, which is exactly
what the construction uses.

The group law is commutative when that of `A` is, and the extension to Néron models of a
morphism `A ⟶ B` is a homomorphism exactly when the morphism is. For every smooth `S`-scheme
`Y`, marked restriction is a group isomorphism from the `S`-morphisms `Y ⟶ M.model` to the
morphisms from the base change of `Y` to `A`; for `Y = S` over a discrete valuation ring `R`
with fraction field `K`, this identifies the group of `R`-points of the model with `A(K)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Neron.NeronModel.grpObj`: the group law of a Néron model.
* `NeronModel.isMonHom_genericIso_hom`: the marking is a homomorphism.
* `NeronModel.existsUnique_grpObj_isMonHom`: the group law is the only group object structure
  on the model for which the marking is a homomorphism.
* `NeronModel.isCommMonObj`: the model of a commutative group object is commutative.
* `NeronModel.isMonHom_extendHom_iff`: a morphism of generic group objects extends to a
  homomorphism of Néron models exactly when it is a homomorphism.
* `NeronModel.homMulEquiv`: marked restriction as a group isomorphism.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Proposition 6.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open Functor
open scoped MonObj Obj

namespace TauCeti.AlgebraicGeometry

universe u

variable {T S : Scheme.{u}}

namespace Neron

namespace NeronModel

variable {j : T ⟶ S} {A B : Over T} [GrpObj A] (M : NeronModel j A)

/-- The group law of a Néron model: the identity, multiplication and inverse are the extensions
of those of `A`, transported to the base change of the model along the marking
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Proposition 6). -/
instance grpObj : GrpObj M.model :=
  letI : GrpObj ((Over.pullback j).obj M.model) := .ofIso M.genericIso.symm
  { one := M.extend _ ((OplaxMonoidal.η (Over.pullback j) ≫ η[_]) ≫ M.genericIso.hom)
    mul := M.extend _ ((OplaxMonoidal.δ (Over.pullback j) _ _ ≫ μ[_]) ≫ M.genericIso.hom)
    inv := M.extend _ (ι[_] ≫ M.genericIso.hom)
    one_mul := M.mappingProperty.hom_ext <| by
      simp [map_extend_eq_comp_inv, ← OplaxMonoidal.δ_natural_left_assoc]
    mul_one := M.mappingProperty.hom_ext <| by
      simp [map_extend_eq_comp_inv, ← OplaxMonoidal.δ_natural_right_assoc]
    mul_assoc := M.mappingProperty.hom_ext <| by
      simp [map_extend_eq_comp_inv, ← OplaxMonoidal.δ_natural_left_assoc,
        ← OplaxMonoidal.δ_natural_right_assoc]
    left_inv := M.mappingProperty.hom_ext <| by
      simp [map_extend_eq_comp_inv, OplaxMonoidal.η_of_cartesianMonoidalCategory]
    right_inv := M.mappingProperty.hom_ext <| by
      simp [map_extend_eq_comp_inv, OplaxMonoidal.η_of_cartesianMonoidalCategory] }

/-- The identity of the model restricts to the identity of `A` along the marking. -/
@[reassoc (attr := simp)]
theorem map_one_comp_genericIso_hom :
    (Over.pullback j).map η[M.model] ≫ M.genericIso.hom =
      OplaxMonoidal.η (Over.pullback j) ≫ η[A] :=
  (M.map_extend _).trans (by simp [MonObj.ofIso_one])

/-- The multiplication of the model restricts to the multiplication of `A` along the marking. -/
@[reassoc (attr := simp)]
theorem map_mul_comp_genericIso_hom :
    (Over.pullback j).map μ[M.model] ≫ M.genericIso.hom =
      OplaxMonoidal.δ (Over.pullback j) _ _ ≫ (M.genericIso.hom ⊗ₘ M.genericIso.hom) ≫ μ[A] :=
  (M.map_extend _).trans (by simp [MonObj.ofIso_mul])

/-- The inverse of the model restricts to the inverse of `A` along the marking. -/
@[reassoc (attr := simp)]
theorem map_inv_comp_genericIso_hom :
    (Over.pullback j).map ι[M.model] ≫ M.genericIso.hom = M.genericIso.hom ≫ ι[A] :=
  (M.map_extend _).trans (by simp [GrpObj.ofIso_inv])

/-- The marking is a homomorphism from the base change of the group law of the model to the group
law of `A`. -/
instance isMonHom_genericIso_hom : IsMonHom M.genericIso.hom where
  one_hom := by simp
  mul_hom := by simp

/-- A monoid object structure on the model for which the marking is a homomorphism is the
monoid structure underlying the group law. -/
theorem eq_toMonObj_of_isMonHom (h : MonObj M.model)
    (hh : letI := h; IsMonHom M.genericIso.hom) : h = (grpObj M).toMonObj := by
  refine MonObj.ext _ _ (M.hom_ext ?_)
  rw [map_mul_comp_genericIso_hom, ← cancel_epi (LaxMonoidal.μ (Over.pullback j) _ _)]
  simpa using hh.mul_hom

/-- Existence and uniqueness of the group law: the model carries exactly one group object
structure for which the marking is a homomorphism (Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§1.2, Proposition 6). -/
theorem existsUnique_grpObj_isMonHom :
    ∃! h : GrpObj M.model, letI := h; IsMonHom M.genericIso.hom :=
  ⟨M.grpObj, M.isMonHom_genericIso_hom, fun h hh ↦
    GrpObj.ext _ _ (M.eq_toMonObj_of_isMonHom h.toMonObj hh)⟩

/-- The Néron model of a commutative group object is commutative. -/
instance isCommMonObj [IsCommMonObj A] : IsCommMonObj M.model where
  mul_comm := M.hom_ext <| by
    simp [Functor.map_braiding, ← BraidedCategory.braiding_naturality_assoc]

/-- The extension of a homomorphism `φ : A ⟶ B` to Néron models is a homomorphism. -/
instance isMonHom_extendHom [GrpObj B] (N : NeronModel j B) (φ : A ⟶ B) [IsMonHom φ] :
    IsMonHom (M.extendHom N φ) where
  one_hom := N.hom_ext <| by simp
  mul_hom := N.hom_ext <| by simp [← OplaxMonoidal.δ_natural_assoc]

/-- A morphism `φ : A ⟶ B` of group objects extends to a homomorphism of Néron models exactly
when it is a homomorphism. -/
theorem isMonHom_extendHom_iff [GrpObj B] (N : NeronModel j B) (φ : A ⟶ B) :
    IsMonHom (M.extendHom N φ) ↔ IsMonHom φ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have e : M.genericIso.inv ≫ (Over.pullback j).map (M.extendHom N φ) ≫ N.genericIso.hom = φ :=
    by simp
  exact e ▸ inferInstance

/-- For a smooth test object `Y`, marked restriction is a group isomorphism from the
`S`-morphisms `Y ⟶ M.model` to the morphisms from the base change of `Y` to `A`. -/
def homMulEquiv (Y : Over S) [Smooth Y.hom] :
    (Y ⟶ M.model) ≃* ((Over.pullback j).obj Y ⟶ A) where
  __ := M.homEquiv Y
  map_mul' f g := by simp [Functor.map_mul, MonObj.mul_comp]

/-- `NeronModel.homMulEquiv` is marked restriction. -/
@[simp]
theorem homMulEquiv_apply {Y : Over S} [Smooth Y.hom] (g : Y ⟶ M.model) :
    M.homMulEquiv Y g = (Over.pullback j).map g ≫ M.genericIso.hom :=
  M.homEquiv_apply g

/-- The inverse of `NeronModel.homMulEquiv` is extension. -/
@[simp]
theorem homMulEquiv_symm_apply {Y : Over S} [Smooth Y.hom] (f : (Over.pullback j).obj Y ⟶ A) :
    (M.homMulEquiv Y).symm f = M.extend Y f :=
  (M.homMulEquiv Y).symm_apply_eq.2 (by simp)

end NeronModel

end Neron

end TauCeti.AlgebraicGeometry
