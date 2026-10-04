/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Product

/-!
# Products of affine toric schemes

The affine scheme of a product cone is the fibre product over `Spec ℂ` of the affine schemes
of the factors. Its coordinate ring is their tensor product: a tensor of two monomials becomes
the monomial of the sum of the two pulled-back characters. The two projections agree with
the toric morphisms induced by the lattice projections.

The construction uses `dualSemigroupProdEquiv`, `TauCeti.MonoidAlgebra.prodTensorBialgEquiv`,
and `AlgebraicGeometry.pullbackSpecIso`. No regularity, rationality,
or finite-generation hypothesis on the cones is required. These affine comparisons provide
the local product description for toric fan schemes. The scheme-level comparison uses lattices
in `Type`, so the affine spectra and `Spec ℂ` belong to the same universe, as for the complex
structure morphisms of toric fan schemes; the character and coordinate-ring comparisons remain
universe-polymorphic.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative TensorProduct

namespace TauCeti.Toric

section CoordinateRing

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (σ : PointedCone ℝ V) (τ : PointedCone ℝ V')

/-- The tensor product of the coordinate rings of two cones is the coordinate ring of their
product, canonically and without choosing bases. -/
noncomputable def affineCoordinateRingProdEquiv :
    affineCoordinateRing hi σ ⊗[ℂ] affineCoordinateRing hi' τ ≃ₐ[ℂ]
      affineCoordinateRing (hi.prod hi') (σ.prod τ) :=
  (TauCeti.MonoidAlgebra.prodTensorBialgEquiv ℂ
    (G := Multiplicative (dualSemigroup hi σ))
    (H := Multiplicative (dualSemigroup hi' τ))).symm.toAlgEquiv.trans <|
    MonoidAlgebra.domCongr ℂ ℂ
      ((MulEquiv.prodMultiplicative _ _).symm.trans
        (dualSemigroupProdEquiv hi hi' σ τ).symm.toMultiplicative)

/-- A tensor of monomials maps to the monomial of the coproduct character, with the product
of the coefficients. -/
@[simp]
theorem affineCoordinateRingProdEquiv_single_tmul_single
    (m : dualSemigroup hi σ) (m' : dualSemigroup hi' τ) (z z' : ℂ) :
    affineCoordinateRingProdEquiv hi hi' σ τ
        (MonoidAlgebra.single (ofAdd m) z ⊗ₜ[ℂ] MonoidAlgebra.single (ofAdd m') z') =
      MonoidAlgebra.single
        (ofAdd ((dualSemigroupProdEquiv hi hi' σ τ).symm (m, m'))) (z * z') := by
  calc
    _ = affineCoordinateRingProdEquiv hi hi' σ τ
        ((z * z') • (MonoidAlgebra.single (ofAdd m) 1 ⊗ₜ[ℂ]
          MonoidAlgebra.single (ofAdd m') 1)) := by
      rw [← TensorProduct.smul_tmul_smul]
      simp only [MonoidAlgebra.smul_single', mul_one]
    _ = _ := by
      simp only [map_smul, affineCoordinateRingProdEquiv, AlgEquiv.trans_apply,
        BialgEquiv.coe_toAlgEquiv,
        TauCeti.MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single,
        MonoidAlgebra.domCongr_single, MulEquiv.trans_apply,
        MulEquiv.prodMultiplicative_symm_apply, AddEquiv.toMultiplicative_apply_apply,
        toAdd_ofAdd, MonoidAlgebra.smul_single', mul_one]

/-- The inverse product comparison splits a monomial into monomials on the two factors. -/
@[simp]
theorem affineCoordinateRingProdEquiv_symm_single
    (m : dualSemigroup (hi.prod hi') (σ.prod τ)) (z : ℂ) :
    (affineCoordinateRingProdEquiv hi hi' σ τ).symm (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd (dualSemigroupProdEquiv hi hi' σ τ m).1) z ⊗ₜ[ℂ]
        MonoidAlgebra.single (ofAdd (dualSemigroupProdEquiv hi hi' σ τ m).2) 1 := by
  apply (affineCoordinateRingProdEquiv hi hi' σ τ).injective
  simp

/-- The first lattice projection induces the first inclusion into the tensor product of
coordinate rings under the product comparison. -/
@[simp]
theorem affineCoordinateRingProdEquiv_comp_includeLeft :
    (affineCoordinateRingProdEquiv hi hi' σ τ).toAlgHom.comp
        Algebra.TensorProduct.includeLeft =
      affineCoordinateRingMap (σ := σ.prod τ) (τ := σ)
        (hi.prod hi') hi (AddMonoidHom.fst N N')
        (LinearMap.fst ℝ V V') (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
            (Set.mapsTo_fst_prod (s := (σ : Set V)) (t := (τ : Set V')))) := by
  ext m : 1
  · cases m
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.includeLeft_apply, MonoidAlgebra.one_def, ← ofAdd_zero]
    rw [affineCoordinateRingProdEquiv_single_tmul_single, affineCoordinateRingMap_single]
    simp only [mul_one]
    congr 1
    apply Multiplicative.ext
    apply Subtype.ext
    ext n
    simp
  · ext

/-- The second lattice projection induces the second inclusion into the tensor product of
coordinate rings under the product comparison. -/
@[simp]
theorem affineCoordinateRingProdEquiv_comp_includeRight :
    (affineCoordinateRingProdEquiv hi hi' σ τ).toAlgHom.comp
        Algebra.TensorProduct.includeRight =
      affineCoordinateRingMap (σ := σ.prod τ) (τ := τ)
        (hi.prod hi') hi' (AddMonoidHom.snd N N')
        (LinearMap.snd ℝ V V') (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
            (Set.mapsTo_snd_prod (s := (σ : Set V)) (t := (τ : Set V')))) := by
  ext m : 1
  · cases m
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.includeRight_apply, MonoidAlgebra.one_def, ← ofAdd_zero]
    rw [affineCoordinateRingProdEquiv_single_tmul_single, affineCoordinateRingMap_single]
    simp only [one_mul]
    congr 1
    apply Multiplicative.ext
    apply Subtype.ext
    ext n
    simp
  · ext

end CoordinateRing

section Scheme

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (σ : PointedCone ℝ V) (τ : PointedCone ℝ V')

/-- The affine toric scheme of a product cone is canonically the fibre product of the
factor affine toric schemes over `Spec ℂ`. -/
noncomputable def affineToricSchemeProdIso :
    affineToricScheme (hi.prod hi') (σ.prod τ) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi' τ)))) :=
  Scheme.Spec.mapIso
    (affineCoordinateRingProdEquiv hi hi' σ τ).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso ℂ (affineCoordinateRing hi σ) (affineCoordinateRing hi' τ)).symm

/-- The first fibre-product projection is the toric morphism of the first lattice projection. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeProdIso_hom_fst :
    (affineToricSchemeProdIso hi hi' σ τ).hom ≫ pullback.fst _ _ =
      affineToricSchemeMap (σ := σ.prod τ) (τ := σ)
        (hi.prod hi') hi (AddMonoidHom.fst N N') (LinearMap.fst ℝ V V')
        (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
            (Set.mapsTo_fst_prod (s := (σ : Set V)) (t := (τ : Set V')))) := by
  simp only [affineToricSchemeProdIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, pullbackSpecIso_inv_fst, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp, affineToricSchemeMap_def]
  congr 1
  exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom)
    (affineCoordinateRingProdEquiv_comp_includeLeft hi hi' σ τ)

/-- The second fibre-product projection is the toric morphism of the second lattice projection. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeProdIso_hom_snd :
    (affineToricSchemeProdIso hi hi' σ τ).hom ≫ pullback.snd _ _ =
      affineToricSchemeMap (σ := σ.prod τ) (τ := τ)
        (hi.prod hi') hi' (AddMonoidHom.snd N N') (LinearMap.snd ℝ V V')
        (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
            (Set.mapsTo_snd_prod (s := (σ : Set V)) (t := (τ : Set V')))) := by
  simp only [affineToricSchemeProdIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, pullbackSpecIso_inv_snd, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp, affineToricSchemeMap_def]
  congr 1
  exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom)
    (affineCoordinateRingProdEquiv_comp_includeRight hi hi' σ τ)

/-- The inverse comparison carries the first toric projection to the first fibre-product
projection. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeProdIso_inv_fst :
    (affineToricSchemeProdIso hi hi' σ τ).inv ≫
      affineToricSchemeMap (σ := σ.prod τ) (τ := σ)
        (hi.prod hi') hi (AddMonoidHom.fst N N') (LinearMap.fst ℝ V V')
        (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
            (Set.mapsTo_fst_prod (s := (σ : Set V)) (t := (τ : Set V')))) =
      pullback.fst _ _ := by
  rw [← affineToricSchemeProdIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The inverse comparison carries the second toric projection to the second fibre-product
projection. -/
@[reassoc (attr := simp)]
theorem affineToricSchemeProdIso_inv_snd :
    (affineToricSchemeProdIso hi hi' σ τ).inv ≫
      affineToricSchemeMap (σ := σ.prod τ) (τ := τ)
        (hi.prod hi') hi' (AddMonoidHom.snd N N') (LinearMap.snd ℝ V V')
        (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
            (Set.mapsTo_snd_prod (s := (σ : Set V)) (t := (τ : Set V')))) =
      pullback.snd _ _ := by
  rw [← affineToricSchemeProdIso_hom_snd, Iso.inv_hom_id_assoc]

end Scheme

end TauCeti.Toric
