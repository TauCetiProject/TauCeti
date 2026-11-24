/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients

/-!
# Restriction of scalars in singular homology

Let `R` be a commutative ring, `S` an `R`-algebra, and `M` an `S`-module carrying a compatible
`R`-module structure (`IsScalarTower R S M`). Restricting scalars along `algebraMap R S` recovers
`M` as an `R`-module (`ModuleCat.restrictScalarsAlgebraMapIso`), and restriction of scalars
preserves coproducts and homology. Combining this with
`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`, singular homology with `R`-module
coefficients `M` is naturally isomorphic to singular homology with `S`-module coefficients `M`
followed by restriction of scalars along `algebraMap R S`
(`TauCeti.singularHomologyRestrictScalarsNatIso`).

Because restriction of scalars is faithful and reflects isomorphisms, singular homology with
`R`-module coefficients `M` vanishes if and only if singular homology with `S`-module coefficients
`M` does (`TopCat.isZero_singularHomology_restrictScalars_iff`), and a continuous map induces an
isomorphism on one if and only if it induces an isomorphism on the other
(`TopCat.Hom.isIso_singularHomologyMap_restrictScalars_iff`).

## Main definitions

* `TauCeti.singularHomologyRestrictScalarsNatIso`: natural isomorphism comparing
  `Hₙ(-; M)` over `R` with restriction of scalars of `Hₙ(-; M)` over `S`.

## Main results

* `TopCat.isZero_singularHomology_restrictScalars_iff`: vanishing of singular homology with
  coefficients `M` is invariant under restriction of scalars along `algebraMap R S`.
* `TopCat.Hom.isIso_singularHomologyMap_restrictScalars_iff`: inducing an isomorphism on singular
  homology with coefficients `M` is invariant under restriction of scalars along `algebraMap R S`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u u₁ u₂

namespace TauCeti

/-- For an `R`-algebra `S` and an `S`-module `M` carrying a compatible `R`-module structure,
singular homology with `R`-module coefficients `M` is naturally isomorphic to singular homology with
`S`-module coefficients `M` followed by restriction of scalars along `algebraMap R S`. -/
def singularHomologyRestrictScalarsNatIso (R : Type u₁) (S : Type u₂) [CommRing R] [Ring S]
    [Algebra R S] (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (n : ℕ) :
    (singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R M) ≅
      (singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S M) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap R S) :=
  (singularHomologyFunctor (ModuleCat.{u} R) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := R) (S := S) M).symm ≪≫
    (Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.restrictScalars.{u} (algebraMap R S))
      (ModuleCat.of S M) n).symm

end TauCeti

namespace TopCat

/-- Singular homology with coefficients in an `S`-module `M`, viewed as an `R`-module through
`IsScalarTower R S M`, vanishes exactly when singular homology with `S`-module coefficients `M`
does. -/
theorem isZero_singularHomology_restrictScalars_iff (X : TopCat.{u})
    (R : Type u₁) (S : Type u₂) [CommRing R] [Ring S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R M)).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S M)).obj X) := by
  rw [Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{u} R) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := R) (S := S) M).symm).app X)]
  exact (ModuleCat.restrictScalars.{u} (algebraMap R S)).isZero_singularHomologyFunctor_iff
    (ModuleCat.of S M) n X

end TopCat

namespace TopCat.Hom

/-- A continuous map induces an isomorphism on singular homology with coefficients in an
`S`-module `M`, viewed as an `R`-module through `IsScalarTower R S M`, exactly when it induces one
with `S`-module coefficients `M`. -/
theorem isIso_singularHomologyMap_restrictScalars_iff {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : Type u₁) (S : Type u₂) [CommRing R] [Ring S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R M)).map f) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S M)).map f) :=
  (NatIso.isIso_map_iff (TauCeti.singularHomologyRestrictScalarsNatIso R S M n) f).trans
    (isIso_iff_of_reflects_iso _ (ModuleCat.restrictScalars.{u} (algebraMap R S)))

end TopCat.Hom

end
