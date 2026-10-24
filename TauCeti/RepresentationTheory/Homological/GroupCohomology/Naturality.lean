/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Resolution
public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Coefficient naturality for group cohomology computed from a resolution

Computing group cohomology using a projective resolution of the trivial representation
commutes with every morphism of coefficient representations. The isomorphism is Mathlib's
`groupCohomologyIso`, which is defined through `Ext`; the existing explicit formula for its
inverse reduces naturality to commutation of precomposition and postcomposition on cochains.

The bar-cochain identification is Mathlib's `groupCohomology.inhomogeneousCochainsIso`, by
Amelia Livingston. Its naturality expresses evaluation on a free generator. These results
allow comparisons with topological cohomology to preserve the coefficient maps.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapters I.7 and III.1.
-/

public section

open CategoryTheory

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}

/-- The bar-resolution identification of cochains commutes with coefficient morphisms. -/
@[reassoc]
theorem inhomogeneousCochainsIso_inv_naturality (f : A ⟶ B) :
    (Rep.barComplex k G).linearYonedaObjMap k f ≫ (inhomogeneousCochainsIso B).inv =
      (inhomogeneousCochainsIso A).inv ≫ cochainsMap (MonoidHom.id G) f := by
  ext n a x
  -- Evaluate the inverse bar identification on the free generator indexed by `x`.
  -- The cochain component is a morphism only after unfolding `linearYonedaObj`.
  change (((Rep.barComplex k G).linearYonedaObjMap k f).f n a).hom
      (Finsupp.single x (MonoidAlgebra.single 1 1)) =
    f.hom (a.hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  erw [ChainComplex.linearYonedaObjMap_f_hom_apply]
  rfl

end groupCohomology

namespace CategoryTheory.ProjectiveResolution

variable {k G : Type u} [CommRing k] [Group G]

/-- Computing group cohomology from a fixed projective resolution is natural in the
coefficient representation. -/
@[reassoc]
theorem groupCohomologyIso_inv_naturality (P : ProjectiveResolution (Rep.trivial k G k))
    {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k f) n ≫
        (groupCohomologyIso B n P).inv =
      (groupCohomologyIso A n P).inv ≫ groupCohomology.map (MonoidHom.id G) f n := by
  let φ := lift (𝟙 _) (Rep.barResolution k G) P
  have hφ : φ.f 0 ≫ P.π.f 0 = (Rep.barResolution k G).π.f 0 := by
    exact (lift_commutes_zero (𝟙 _) (Rep.barResolution k G) P).trans (Category.comp_id _)
  rw [TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap B P φ hφ n,
    TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap A P φ hφ n]
  have hchain :
      P.complex.linearYonedaObjMap k f ≫
          (TauCeti.ChainComplex.linearYonedaFunctor k B).map φ.op ≫
            (groupCohomology.inhomogeneousCochainsIso B).inv =
        ((TauCeti.ChainComplex.linearYonedaFunctor k A).map φ.op ≫
          (groupCohomology.inhomogeneousCochainsIso A).inv) ≫
            groupCohomology.cochainsMap (MonoidHom.id G) f := by
    erw [← Category.assoc, ChainComplex.linearYonedaObjMap_naturality,
      Category.assoc, groupCohomology.inhomogeneousCochainsIso_inv_naturality, Category.assoc]
    rfl
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun F ↦ HomologicalComplex.homologyMap F n) hchain).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

end CategoryTheory.ProjectiveResolution
