/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Iso
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.GroupLaw
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth

/-!
# Elliptic curves as abelian varieties

Let `W` be an elliptic Weierstrass curve over a field `K`. Its projective model
`projModel W ⟶ Spec K` is proper (`WeierstrassCurve.isProper_projModelOver`), geometrically
integral (`WeierstrassCurve.geometricallyIntegral_projModelOver`) and a commutative group scheme
under the Bosma–Lenstra addition morphism (`WeierstrassCurve.grpObjProjModel`). This file packages
these facts as an abelian variety `W.toAbelianVariety` over `K`, so that the general theory of
abelian varieties (homomorphisms, rigidity, the Albanese property, isogenies, endomorphisms)
applies to elliptic curves.

The unit, multiplication and inverse of `W.toAbelianVariety` are the zero section
`[0 : 1 : 0]`, the addition morphism and the negation morphism. The abelian variety has dimension
one, and products of two elliptic curves have dimension two. Extension of the base field commutes
with the construction: for a field extension `L / K`, the abelian variety of the base change
`W.map (algebraMap K L)` is isomorphic, as an abelian variety over `L`, to the base change of
`W.toAbelianVariety`.

## Main definitions

* `WeierstrassCurve.toAbelianVariety`: the abelian variety of an elliptic curve over a field.
* `WeierstrassCurve.toAbelianVarietyBaseChangeIso`: the isomorphism of abelian varieties over `L`
  between `(W.map (algebraMap K L)).toAbelianVariety` and `W.toAbelianVariety.baseChange L`.

## Main results

* `WeierstrassCurve.dim_toAbelianVariety`: an elliptic curve is an abelian variety of
  dimension one.
* `WeierstrassCurve.dim_prod_toAbelianVariety`: the product of two elliptic curves is an abelian
  variety of dimension two.

## References

* J. S. Milne, *Abelian Varieties*, Chapter I, §1.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, Chapter III, §3.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **An elliptic curve is an abelian variety.** The projective model `projModel W ⟶ Spec K` of an
elliptic Weierstrass curve over a field, with the group law `grpObjProjModel`, is a proper
geometrically integral group scheme over `Spec K`. -/
noncomputable def toAbelianVariety : AbelianVariety K :=
  @AbelianVariety.ofGeometricallyIntegral K _ (Over.mk W.projModelOver) _
    W.isProper_projModelOver W.geometricallyIntegral_projModelOver

/-- The group scheme underlying the abelian variety of `W` is the projective model of `W` over
`Spec K`. -/
@[simp]
theorem toAbelianVariety_toOver : W.toAbelianVariety.toOver = Over.mk W.projModelOver :=
  @AbelianVariety.ofGeometricallyIntegral_toOver K _ (Over.mk W.projModelOver) _
    W.isProper_projModelOver W.geometricallyIntegral_projModelOver

/-- The scheme underlying the abelian variety of `W` is the projective model of `W`. -/
@[simp]
theorem toAbelianVariety_toScheme : W.toAbelianVariety.toScheme = W.projModel :=
  congrArg Over.left W.toAbelianVariety_toOver

/-- The unit of the abelian variety of `W` is the unit of the group scheme `projModel W`, the zero
section `[0 : 1 : 0]` (`WeierstrassCurve.one_projModelOver_left`). -/
-- Not `@[simp]`: `simp` proves it from `isMonHom_eqToHom_toAbelianVariety_toOver`.
theorem toAbelianVariety_one :
    η[W.toAbelianVariety.toOver] ≫ eqToHom W.toAbelianVariety_toOver =
      η[Over.mk W.projModelOver] :=
  @AbelianVariety.ofGeometricallyIntegral_one K _ (Over.mk W.projModelOver) _
    W.isProper_projModelOver W.geometricallyIntegral_projModelOver

/-- The multiplication of the abelian variety of `W` is the multiplication of the group scheme
`projModel W`, the addition morphism (`WeierstrassCurve.mul_projModelOver_left`). -/
-- Not `@[simp]`: `simp` proves it from `isMonHom_eqToHom_toAbelianVariety_toOver`.
theorem toAbelianVariety_mul :
    μ[W.toAbelianVariety.toOver] ≫ eqToHom W.toAbelianVariety_toOver =
      (eqToHom W.toAbelianVariety_toOver ⊗ₘ eqToHom W.toAbelianVariety_toOver) ≫
        μ[Over.mk W.projModelOver] :=
  @AbelianVariety.ofGeometricallyIntegral_mul K _ (Over.mk W.projModelOver) _
    W.isProper_projModelOver W.geometricallyIntegral_projModelOver

/-- The inverse of the abelian variety of `W` is the inverse of the group scheme `projModel W`,
the negation morphism (`WeierstrassCurve.inv_projModelOver_left`). -/
-- Not `@[simp]`: `simp` proves it from `GrpObj.inv_hom` and the `IsMonHom` instance below.
theorem toAbelianVariety_inv :
    ι[W.toAbelianVariety.toOver] ≫ eqToHom W.toAbelianVariety_toOver =
      eqToHom W.toAbelianVariety_toOver ≫ ι[Over.mk W.projModelOver] :=
  @AbelianVariety.ofGeometricallyIntegral_inv K _ (Over.mk W.projModelOver) _
    W.isProper_projModelOver W.geometricallyIntegral_projModelOver

/-- **An elliptic curve has dimension one** as an abelian variety. -/
@[simp]
theorem dim_toAbelianVariety : W.toAbelianVariety.dim = 1 := by
  rw [AbelianVariety.dim_def, toAbelianVariety_toScheme, topologicalKrullDim_projModel]

/-- **The product of two elliptic curves has dimension two** as an abelian variety. -/
theorem dim_prod_toAbelianVariety (W' : WeierstrassCurve K) [W'.IsElliptic] :
    (W.toAbelianVariety.prod W'.toAbelianVariety).dim = 2 := by
  rw [AbelianVariety.dim_prod, dim_toAbelianVariety, dim_toAbelianVariety]
  exact one_add_one_eq_two

/-- The transport isomorphism identifying the group scheme underlying `W.toAbelianVariety` with
`projModel W` preserves the unit and the multiplication. -/
instance isMonHom_eqToHom_toAbelianVariety_toOver :
    IsMonHom (eqToHom W.toAbelianVariety_toOver) where
  one_hom := W.toAbelianVariety_one
  mul_hom := W.toAbelianVariety_mul

/-- The inverse transport isomorphism is a homomorphism of monoid objects as well. -/
instance isMonHom_eqToHom_toAbelianVariety_toOver_symm :
    IsMonHom (eqToHom W.toAbelianVariety_toOver.symm) :=
  haveI : IsMonHom (eqToIso W.toAbelianVariety_toOver).hom :=
    W.isMonHom_eqToHom_toAbelianVariety_toOver
  inferInstanceAs (IsMonHom (eqToIso W.toAbelianVariety_toOver).inv)

section BaseChange

open scoped CategoryTheory.Obj

variable (L : Type u) [Field L] [Algebra K L]

/-- The isomorphism over `Spec L` underlying `toAbelianVarietyBaseChangeIso`: the base change
isomorphism `projModelOverBaseChangeIso` of projective models, composed with the transport
isomorphisms of `toAbelianVariety_toOver` and `AbelianVariety.baseChange_toOver`. -/
private noncomputable def toOverBaseChangeIso :
    (W.map (algebraMap K L)).toAbelianVariety.toOver ≅ (W.toAbelianVariety.baseChange L).toOver :=
  eqToIso (W.map (algebraMap K L)).toAbelianVariety_toOver ≪≫
    W.projModelOverBaseChangeIso (algebraMap K L) ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso
      (eqToIso W.toAbelianVariety_toOver.symm) ≪≫
    eqToIso (AbelianVariety.baseChange_toOver W.toAbelianVariety L).symm

private lemma toOverBaseChangeIso_hom : (W.toOverBaseChangeIso L).hom =
    eqToHom (W.map (algebraMap K L)).toAbelianVariety_toOver ≫
      (W.projModelOverBaseChangeIso (algebraMap K L)).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
        (eqToHom W.toAbelianVariety_toOver.symm) ≫
      eqToHom (AbelianVariety.baseChange_toOver W.toAbelianVariety L).symm := by
  simp [toOverBaseChangeIso]

private instance isMonHom_toOverBaseChangeIso_hom : IsMonHom (W.toOverBaseChangeIso L).hom := by
  rw [toOverBaseChangeIso_hom]
  infer_instance

/-- **The abelian variety of an elliptic curve commutes with extension of the base field.** For a
field extension `L / K`, the abelian variety over `L` of the base change `W.map (algebraMap K L)`
is isomorphic to the base change of the abelian variety of `W`. Its underlying isomorphism over
`Spec L` is the base change isomorphism `projModelOverBaseChangeIso` of projective models
(`WeierstrassCurve.isoToOver_toAbelianVarietyBaseChangeIso`). -/
noncomputable def toAbelianVarietyBaseChangeIso :
    (W.map (algebraMap K L)).toAbelianVariety ≅ W.toAbelianVariety.baseChange L where
  hom := AbelianVariety.Hom.mk' (W.toOverBaseChangeIso L).hom
    (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  inv := AbelianVariety.Hom.mk' (W.toOverBaseChangeIso L).inv
    (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  hom_inv_id := by
    apply AbelianVariety.Hom.toOverHom_injective
    simp only [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_mk',
      Iso.hom_inv_id, AbelianVariety.Hom.toOverHom_id]
  inv_hom_id := by
    apply AbelianVariety.Hom.toOverHom_injective
    simp only [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_mk',
      Iso.inv_hom_id, AbelianVariety.Hom.toOverHom_id]

/-- The isomorphism over `Spec L` underlying `toAbelianVarietyBaseChangeIso` is the base change
isomorphism `projModelOverBaseChangeIso` of projective models, up to the transport isomorphisms
of `toAbelianVariety_toOver` and `AbelianVariety.baseChange_toOver`. -/
theorem isoToOver_toAbelianVarietyBaseChangeIso :
    AbelianVariety.isoToOver (W.toAbelianVarietyBaseChangeIso L) =
      eqToIso (W.map (algebraMap K L)).toAbelianVariety_toOver ≪≫
        W.projModelOverBaseChangeIso (algebraMap K L) ≪≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso
          (eqToIso W.toAbelianVariety_toOver.symm) ≪≫
        eqToIso (AbelianVariety.baseChange_toOver W.toAbelianVariety L).symm := by
  ext1
  simp [toAbelianVarietyBaseChangeIso, toOverBaseChangeIso]

end BaseChange

end WeierstrassCurve
