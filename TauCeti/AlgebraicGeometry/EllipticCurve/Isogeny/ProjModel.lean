/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.HomOfAlgHom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Place
import TauCeti.AlgebraicGeometry.Curves.Restrict
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Isogenies are the pointed morphisms of projective models

Let `W₁` and `W₂` be elliptic Weierstrass curves over a field `K`, with projective models
`E₁ = projModel W₁` and `E₂ = projModel W₂`, regular proper curves over `K`
(`WeierstrassCurve.projModelCurve`) whose function fields
are identified with the function fields `K(W₁)` and `K(W₂)` of the affine equations
(`WeierstrassCurve.projModelFunctionFieldEquiv`). An isogeny `φ : W₁ → W₂` in the sense of
`TauCeti.Isogeny` is a coordinate pullback `K[W₂] → K(W₁)` sending the point at infinity to the
point at infinity; it extends to a `K`-embedding `φ^* : K(W₂) → K(W₁)`
(`TauCeti.Isogeny.fieldPullback`).

This file proves that **isogenies `W₁ → W₂` correspond exactly to the dominant `K`-morphisms
`E₁ ⟶ E₂` carrying the zero section `O₁` to the zero section `O₂`**. A `K`-embedding of function
fields induces a unique dominant `K`-morphism of regular proper curves
(`TauCeti.AlgebraicGeometry.RegularProperCurveCat.homOfAlgHom`), and the condition at infinity
matches on both sides:

* the point `O` of `E = projModel W` is the point of the place at infinity of `K(W)`
  (`WeierstrassCurve.projModelCodimensionOnePointEquivPlace_projModelZeroPoint`);
* a morphism of curves sends `O₁` to `O₂` exactly when the place of `O₁` lies over the place of
  `O₂` (`TauCeti.AlgebraicGeometry.RegularProperCurveCat.hom_apply_eq_iff_isEquiv_comap`), that
  is, when the place at infinity of `K(W₁)` restricts to the place at infinity of `K(W₂)`;
* the latter is exactly the condition `MapsInfinity` of an isogeny
  (`TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace`);
* since `O₁` and `O₂` are `K`-rational points, `f (O₁) = O₂` on points is the equality
  `O₁ ≫ f = O₂` of sections (`TauCeti.AlgebraicGeometry.comp_eq_comp_iff_of_section`).

The correspondence respects identities and composition.

## Main definitions

* `TauCeti.Isogeny.toProjModelHom φ`: the dominant `K`-morphism `E₁ ⟶ E₂` induced by an isogeny.
* `TauCeti.Isogeny.equivProjModelHom`: isogenies `W₁ → W₂` are the dominant `K`-morphisms
  `E₁ ⟶ E₂` with `O₁ ≫ f = O₂`.

## Main results

* `TauCeti.Isogeny.projModelFunctionFieldEquiv_functionFieldMap_toProjModelHom`: the pullback of
  rational functions along `toProjModelHom φ` is the function-field pullback `φ^*`.
* `TauCeti.Isogeny.projModelZero_comp_toProjModelHom`: `toProjModelHom φ` carries `O₁` to `O₂`.
* `TauCeti.Isogeny.toProjModelHom_id` and `TauCeti.Isogeny.toProjModelHom_comp`: functoriality.
* `TauCeti.Isogeny.fieldPullback_equivProjModelHom_symm_apply`: the isogeny attached to a pointed
  morphism `f` has function-field pullback `f^*`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.4.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti TauCeti.AlgebraicGeometry

universe u

-- The function field of the projective model carries two `K`-algebra structures: the one defined
-- by its structure morphism, `Scheme.functionFieldBaseAlgebra`, which the curve category uses, and
-- the one transported from the affine function field, `projModelFunctionFieldAlgebra`. They agree
-- (`projModelFunctionFieldEquiv_baseRingToFunctionField`), but not definitionally; this file works
-- with the first one throughout.
attribute [local instance high] Scheme.functionFieldBaseAlgebra

namespace TauCeti

open WeierstrassCurve

variable {K : Type u} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

omit [W₁.IsElliptic] [W₂.IsElliptic] in
/-- Transport of `K`-embeddings of function fields from the projective models to the affine
equations, along `projModelFunctionFieldBaseAlgEquiv`. -/
private noncomputable abbrev pullbackEquiv :
    (W₂.projModel.functionField →ₐ[K] W₁.projModel.functionField) ≃
      (W₂.toAffine.FunctionField →ₐ[K] W₁.toAffine.FunctionField) :=
  AlgEquiv.arrowCongr W₂.projModelFunctionFieldBaseAlgEquiv W₁.projModelFunctionFieldBaseAlgEquiv

/-- The pullback of rational functions along a morphism of projective models, read on the
function fields of the affine equations. -/
private noncomputable def affinePullback (f : W₁.projModelCurve ⟶ W₂.projModelCurve) :
    W₂.toAffine.FunctionField →ₐ[K] W₁.toAffine.FunctionField :=
  pullbackEquiv (f.hom.functionFieldAlgHom K)

private theorem affinePullback_apply (f : W₁.projModelCurve ⟶ W₂.projModelCurve)
    (z : W₂.toAffine.FunctionField) :
    affinePullback f z =
      W₁.projModelFunctionFieldEquiv (f.hom.functionFieldAlgHom K
        (W₂.projModelFunctionFieldEquiv.symm z)) := by
  simp [affinePullback]

/-- A morphism of projective models is determined by its pullback on the affine function fields. -/
private theorem affinePullback_injective :
    Function.Injective (affinePullback (W₁ := W₁) (W₂ := W₂)) :=
  pullbackEquiv.injective.comp RegularProperCurveCat.functionFieldAlgHom_injective

private theorem affinePullback_id :
    affinePullback (𝟙 W₁.projModelCurve) = AlgHom.id K W₁.toAffine.FunctionField :=
  AlgHom.ext fun z ↦ by simp [affinePullback_apply]

private theorem affinePullback_comp (f : W₁.projModelCurve ⟶ W₂.projModelCurve)
    (g : W₂.projModelCurve ⟶ W₃.projModelCurve) :
    affinePullback (f ≫ g) = (affinePullback f).comp (affinePullback g) :=
  (congrArg pullbackEquiv (Scheme.Hom.functionFieldAlgHom_comp K f.hom g.hom)).trans
    (AlgEquiv.arrowCongr_comp _ W₂.projModelFunctionFieldBaseAlgEquiv _ _ _)

/-- A `K`-embedding of the function fields of the affine equations, read on the function fields of
the projective models. -/
private noncomputable def projPullback
    (σ : W₂.toAffine.FunctionField →ₐ[K] W₁.toAffine.FunctionField) :
    W₂.projModel.functionField →ₐ[K] W₁.projModel.functionField :=
  pullbackEquiv.symm σ

private theorem affinePullback_homOfAlgHom
    (σ : W₂.toAffine.FunctionField →ₐ[K] W₁.toAffine.FunctionField) :
    affinePullback (RegularProperCurveCat.homOfAlgHom (Y := W₂.projModelCurve) (projPullback σ)) =
      σ := by
  rw [affinePullback, RegularProperCurveCat.functionFieldAlgHom_homOfAlgHom, projPullback,
    Equiv.apply_symm_apply]

/-- **A morphism of projective models carries `O₁` to `O₂` exactly when the place at infinity of
`K(W₁)` restricts to the place at infinity of `K(W₂)`** along the pullback of rational functions. -/
private theorem projModelZero_comp_eq_iff (f : W₁.projModelCurve ⟶ W₂.projModelCurve) :
    W₁.projModelZero ≫ f.hom = W₂.projModelZero ↔
      ((Affine.infinityPlace W₁.toAffine).comap (affinePullback f).toRingHom).IsEquiv
        (Affine.infinityPlace W₂.toAffine) := by
  -- both sides of the first equation are `K`-rational points of `E₂`, so they agree exactly when
  -- they agree on points
  have h₁ : (W₁.projModelZero ≫ f.hom) ≫ (W₂.projModel ↘ Spec (.of K)) = 𝟙 _ := by
    rw [Category.assoc, comp_over, over_projModel, projModelZero_projModelOver]
  have h₂ : W₂.projModelZero ≫ (W₂.projModel ↘ Spec (.of K)) = 𝟙 _ := by
    rw [over_projModel, projModelZero_projModelOver]
  have hpt := comp_eq_comp_iff_of_section h₁ h₂ (𝟙 _) (IsLocalRing.closedPoint K)
  rw [Category.id_comp, Category.id_comp, Scheme.Hom.comp_apply] at hpt
  -- on points, `f` sends `O₁` to `O₂` exactly when the place of `O₁` lies over that of `O₂`
  have key := RegularProperCurveCat.hom_apply_eq_iff_isEquiv_comap f W₁.projModelZeroPoint
    W₂.projModelZeroPoint
  rw [valuation_toPlace_projModelZeroPoint, valuation_toPlace_projModelZeroPoint,
    coe_projModelZeroPoint, coe_projModelZeroPoint] at key
  refine hpt.trans (key.trans ?_)
  -- transport along the identification of `K(E₂)` with `K(W₂)`
  have hcomp : ((Affine.infinityPlace W₁.toAffine).comap
      (W₁.projModelFunctionFieldEquiv : W₁.projModel.functionField →+* _)).comap
        (f.hom.functionFieldAlgHom K).toRingHom =
      ((Affine.infinityPlace W₁.toAffine).comap (affinePullback f).toRingHom).comap
        (W₂.projModelFunctionFieldEquiv : W₂.projModel.functionField →+* _) := by
    ext z
    simp [affinePullback_apply]
  rw [hcomp]
  refine ⟨fun h r s ↦ ?_, fun h ↦ h.comap _⟩
  simpa using h (W₂.projModelFunctionFieldEquiv.symm r) (W₂.projModelFunctionFieldEquiv.symm s)

namespace Isogeny

/-- **The morphism of projective models induced by an isogeny**: the unique dominant `K`-morphism
`projModel W₁ ⟶ projModel W₂` whose pullback of rational functions is the function-field pullback
`φ^* : K(W₂) → K(W₁)` (`projModelFunctionFieldEquiv_functionFieldMap_toProjModelHom`). -/
noncomputable def toProjModelHom (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.projModelCurve ⟶ W₂.projModelCurve :=
  RegularProperCurveCat.homOfAlgHom (projPullback φ.fieldPullback)

private theorem affinePullback_toProjModelHom (φ : Isogeny W₁.toAffine W₂.toAffine) :
    affinePullback φ.toProjModelHom = φ.fieldPullback :=
  affinePullback_homOfAlgHom _

/-- **The pullback of rational functions along `toProjModelHom φ` is `φ^*`**, read through the
identifications of the function fields of the projective models with those of the affine
equations. -/
@[simp]
theorem projModelFunctionFieldEquiv_functionFieldMap_toProjModelHom
    (φ : Isogeny W₁.toAffine W₂.toAffine) (z : W₂.toAffine.FunctionField) :
    W₁.projModelFunctionFieldEquiv
        (φ.toProjModelHom.hom.functionFieldMap (W₂.projModelFunctionFieldEquiv.symm z)) =
      φ.fieldPullback z := by
  rw [← Scheme.Hom.functionFieldAlgHom_apply K, ← affinePullback_apply,
    affinePullback_toProjModelHom]

/-- **The morphism induced by an isogeny carries `O₁` to `O₂`.** -/
@[simp]
theorem projModelZero_comp_toProjModelHom (φ : Isogeny W₁.toAffine W₂.toAffine) :
    W₁.projModelZero ≫ φ.toProjModelHom.hom = W₂.projModelZero := by
  rw [projModelZero_comp_eq_iff, affinePullback_toProjModelHom,
    ← CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace]
  convert φ.mapsInfinity
  exact AlgHom.ext fun x ↦ by simp

/-- The morphism induced by the identity isogeny is the identity. -/
@[simp]
theorem toProjModelHom_id :
    (Isogeny.id W₁.toAffine).toProjModelHom = 𝟙 W₁.projModelCurve := by
  refine affinePullback_injective ?_
  rw [affinePullback_toProjModelHom, affinePullback_id, id_fieldPullback]

/-- The morphism induced by a composite of isogenies is the composite of the morphisms. -/
@[simp]
theorem toProjModelHom_comp (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).toProjModelHom = φ.toProjModelHom ≫ ψ.toProjModelHom := by
  refine affinePullback_injective ?_
  rw [affinePullback_toProjModelHom, comp_fieldPullback, affinePullback_comp,
    affinePullback_toProjModelHom, affinePullback_toProjModelHom]

/-- **Isogenies are the pointed morphisms of projective models**: isogenies `W₁ → W₂` correspond
to the dominant `K`-morphisms `f : projModel W₁ ⟶ projModel W₂` carrying the zero section to the
zero section, `O₁ ≫ f = O₂`. An isogeny goes to the morphism with pullback of rational functions
`φ^*` (`toProjModelHom`). -/
noncomputable def equivProjModelHom :
    Isogeny W₁.toAffine W₂.toAffine ≃
      {f : W₁.projModelCurve ⟶ W₂.projModelCurve // W₁.projModelZero ≫ f.hom = W₂.projModelZero}
    where
  toFun φ := ⟨φ.toProjModelHom, φ.projModelZero_comp_toProjModelHom⟩
  invFun f :=
    { pullback := (affinePullback f.1).comp
        (IsScalarTower.toAlgHom K W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField)
      mapsInfinity := (CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace _).mpr
        ((projModelZero_comp_eq_iff f.1).mp f.2) }
  left_inv φ := Isogeny.ext <| AlgHom.ext fun x ↦ by
    simp [affinePullback_toProjModelHom]
  right_inv f := Subtype.ext <| affinePullback_injective <| by
    rw [affinePullback_toProjModelHom]
    exact (fieldPullback_unique _ (affinePullback f.1) fun _ ↦ rfl).symm

@[simp]
theorem coe_equivProjModelHom_apply (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (equivProjModelHom φ : W₁.projModelCurve ⟶ W₂.projModelCurve) = φ.toProjModelHom :=
  (rfl)

/-- The function-field pullback of the isogeny attached to a pointed morphism `f` of projective
models is the pullback of rational functions along `f`, read through the identifications of the
function fields. -/
@[simp]
theorem fieldPullback_equivProjModelHom_symm_apply (f : W₁.projModelCurve ⟶ W₂.projModelCurve)
    (hf : W₁.projModelZero ≫ f.hom = W₂.projModelZero) (z : W₂.toAffine.FunctionField) :
    (equivProjModelHom.symm ⟨f, hf⟩).fieldPullback z = W₁.projModelFunctionFieldEquiv
      (f.hom.functionFieldMap (W₂.projModelFunctionFieldEquiv.symm z)) := by
  rw [← Scheme.Hom.functionFieldAlgHom_apply K, ← affinePullback_apply]
  exact congrArg (· z)
    (fieldPullback_unique (equivProjModelHom.symm ⟨f, hf⟩) (affinePullback f) fun _ ↦ rfl).symm

end Isogeny

end TauCeti
