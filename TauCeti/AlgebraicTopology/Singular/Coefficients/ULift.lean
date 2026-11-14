/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import TauCeti.Algebra.Category.ModuleCat.ULift
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

import TauCeti.Algebra.Category.ModuleCat.AB

/-!
# Singular homology with universe-lifted ring coefficients

For a ring `R : Type v` and a topological space `X : TopCat.{max v u}`, the singular homology of `X`
with coefficients in `R` can be formed in two ways:

* inside `ModuleCat.{max v u} R`, with coefficient object `ModuleCat.of R (ULift.{u} R)`, which is
  the form used by coefficient exact sequences and the Hurewicz homomorphism over `R`;
* inside `ModuleCat.{max v u} (ULift.{u} R)`, with coefficient ring `ULift.{u} R`, which is the
  homology of `TauCeti.singularChains (ULift.{u} R)` and compares directly with normalized cubical
  chains over `ULift.{u} R`.

Since restriction of scalars along `(ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R`
is exact and preserves all coproducts, the two agree: the `R`-module homology is the
`ULift.{u} R`-ring homology with its scalars restricted to `R` (`TopCat.singularHomologyUliftIso`).
On underlying abelian groups this furnishes a natural additive equivalence
`TopCat.singularHomologyUliftAddEquiv` intertwined with `ULift.up : R → ULift.{u} R`, and one
homology group vanishes if and only if the other does (`TopCat.isZero_singularHomology_ulift_iff`).

When `R = ℤ : Type 0`, `max 0 u` is definitionally `u`, so these declarations apply directly to
`X : TopCat.{u}` with coefficients in `ModuleCat.of ℤ (ULift.{u} ℤ)`.

## Main declarations

* `TopCat.singularHomologyUliftIso`: `Hₙ(X; ModuleCat.of R (ULift.{u} R))` is isomorphic to the
  restriction of scalars of `Hₙ(X; ModuleCat.of (ULift.{u} R) (ULift.{u} R))`.
* `TopCat.singularHomologyUliftAddEquiv`: the induced natural additive equivalence with the
  homology of `TauCeti.singularChains (ULift.{u} R)`.
* `TopCat.isZero_singularHomology_ulift_iff`: vanishing equivalence between the two models.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u v

namespace TopCat

/-- **Singular homology with `ULift.{u} R` as an `R`-module agrees with singular homology over the
ring `ULift.{u} R`**: the former is isomorphic in `ModuleCat.{max v u} R` to the restriction of
scalars of the latter along `ULift.up : R →+* ULift.{u} R`. -/
def singularHomologyUliftIso (R : Type v) [Ring R] (X : TopCat.{max v u}) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
        (ModuleCat.of R (ULift.{u} R))).obj X ≅
      (ModuleCat.restrictScalars
        ((ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R)).obj
        (((singularHomologyFunctor (ModuleCat.{max v u} (ULift.{u} R)) n).obj
          (ModuleCat.of (ULift.{u} R) (ULift.{u} R))).obj X) :=
  ((singularHomologyFunctor (ModuleCat.{max v u} R) n).mapIso
      (ModuleCat.restrictScalarsUliftIso.{u} (R := R) (ULift.{u} R)).symm).app X ≪≫
    ((Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.restrictScalars.{max v u}
        ((ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R))
        (ModuleCat.of (ULift.{u} R) (ULift.{u} R)) n).app X).symm

/-- Explicit formula for the forward morphism of `TopCat.singularHomologyUliftIso`. -/
theorem singularHomologyUliftIso_hom (R : Type v) [Ring R] (X : TopCat.{max v u}) (n : ℕ) :
    (X.singularHomologyUliftIso R n).hom =
      ((singularHomologyFunctor (ModuleCat.{max v u} R) n).map
          (ModuleCat.restrictScalarsUliftIso.{u} (R := R) (ULift.{u} R)).inv).app X ≫
        (Functor.singularHomologyFunctorObjCompIso
          (ModuleCat.restrictScalars.{max v u}
            ((ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R))
            (ModuleCat.of (ULift.{u} R) (ULift.{u} R)) n).inv.app X :=
  (rfl)

/-- `TopCat.singularHomologyUliftIso` is natural in the space `X`. -/
@[reassoc]
theorem singularHomologyUliftIso_hom_naturality (R : Type v) [Ring R] {X Y : TopCat.{max v u}}
    (f : X ⟶ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
        (ModuleCat.of R (ULift.{u} R))).map f ≫ (Y.singularHomologyUliftIso R n).hom =
      (X.singularHomologyUliftIso R n).hom ≫
        (ModuleCat.restrictScalars
          ((ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R)).map
          (((singularHomologyFunctor (ModuleCat.{max v u} (ULift.{u} R)) n).obj
            (ModuleCat.of (ULift.{u} R) (ULift.{u} R))).map f) := by
  rw [singularHomologyUliftIso_hom, singularHomologyUliftIso_hom, NatTrans.naturality_assoc]
  exact congrArg _ ((Functor.singularHomologyFunctorObjCompIso _ _ n).inv.naturality f)

/-- Naturality of the inverse of `TopCat.singularHomologyUliftIso`. -/
@[reassoc]
theorem singularHomologyUliftIso_inv_naturality (R : Type v) [Ring R] {X Y : TopCat.{max v u}}
    (f : X ⟶ Y) (n : ℕ) :
    (ModuleCat.restrictScalars
        ((ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R)).map
        (((singularHomologyFunctor (ModuleCat.{max v u} (ULift.{u} R)) n).obj
          (ModuleCat.of (ULift.{u} R) (ULift.{u} R))).map f) ≫
      (Y.singularHomologyUliftIso R n).inv =
    (X.singularHomologyUliftIso R n).inv ≫
      ((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
        (ModuleCat.of R (ULift.{u} R))).map f := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (singularHomologyUliftIso_hom_naturality R f n).symm

/-- Singular homology with coefficients in `ModuleCat.of R (ULift.{u} R)` vanishes if and only if
singular homology over the lifted ring `ULift.{u} R` vanishes. -/
theorem isZero_singularHomology_ulift_iff (R : Type v) [Ring R] (X : TopCat.{max v u}) (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
        (ModuleCat.of R (ULift.{u} R))).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{max v u} (ULift.{u} R)) n).obj
        (ModuleCat.of (ULift.{u} R) (ULift.{u} R))).obj X) := by
  rw [Iso.isZero_iff (X.singularHomologyUliftIso R n), ModuleCat.isZero_iff_subsingleton,
    ModuleCat.isZero_iff_subsingleton]
  -- Restriction of scalars leaves the underlying carrier unchanged.
  rfl

/-- **Additive equivalence between `R`-module homology with `ULift.{u} R` coefficients and
singular chain homology over `ULift.{u} R`**, obtained by passing to underlying abelian groups in
`TopCat.singularHomologyUliftIso`. -/
def singularHomologyUliftAddEquiv (R : Type v) [Ring R] (X : TopCat.{max v u}) (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
        (ModuleCat.of R (ULift.{u} R))).obj X) ≃+
      (((TauCeti.singularChains (ULift.{u} R)).obj X).homology n) :=
  -- Restriction of scalars preserves the underlying `AddCommGroup` definitionally, and
  -- `singularHomologyFunctor` applied to `ModuleCat.of k k` is the homology of `singularChains k`.
  (X.singularHomologyUliftIso R n).toLinearEquiv.toAddEquiv

/-- Evaluating `TopCat.singularHomologyUliftAddEquiv` applies the forward morphism of
`TopCat.singularHomologyUliftIso`. -/
theorem singularHomologyUliftAddEquiv_apply (R : Type v) [Ring R] (X : TopCat.{max v u}) (n : ℕ)
    (c : ((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
      (ModuleCat.of R (ULift.{u} R))).obj X) :
    X.singularHomologyUliftAddEquiv R n c = (X.singularHomologyUliftIso R n).hom c :=
  (rfl)

/-- Evaluating the inverse of `TopCat.singularHomologyUliftAddEquiv` applies the inverse morphism
of `TopCat.singularHomologyUliftIso`. -/
theorem singularHomologyUliftAddEquiv_symm_apply (R : Type v) [Ring R] (X : TopCat.{max v u})
    (n : ℕ) (c : ((TauCeti.singularChains (ULift.{u} R)).obj X).homology n) :
    (X.singularHomologyUliftAddEquiv R n).symm c = (X.singularHomologyUliftIso R n).inv c :=
  (rfl)

/-- `TopCat.singularHomologyUliftAddEquiv` intertwines the `R`-action with the lifted
`ULift.{u} R`-action. -/
theorem singularHomologyUliftAddEquiv_smul (R : Type v) [Ring R] (X : TopCat.{max v u}) (n : ℕ)
    (r : R)
    (c : ((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
      (ModuleCat.of R (ULift.{u} R))).obj X) :
    X.singularHomologyUliftAddEquiv R n (r • c) =
      (ULift.up r : ULift.{u} R) • X.singularHomologyUliftAddEquiv R n c :=
  (X.singularHomologyUliftIso R n).hom.hom.map_smul r c

/-- The inverse of `TopCat.singularHomologyUliftAddEquiv` intertwines the `ULift.{u} R`-action with
the `R`-action. -/
theorem singularHomologyUliftAddEquiv_symm_smul (R : Type v) [Ring R] (X : TopCat.{max v u})
    (n : ℕ) (r : R) (c : ((TauCeti.singularChains (ULift.{u} R)).obj X).homology n) :
    (X.singularHomologyUliftAddEquiv R n).symm ((ULift.up r : ULift.{u} R) • c) =
      r • (X.singularHomologyUliftAddEquiv R n).symm c :=
  (X.singularHomologyUliftIso R n).inv.hom.map_smul r c

/-- `TopCat.singularHomologyUliftAddEquiv` is natural in `X`. -/
theorem singularHomologyUliftAddEquiv_naturality (R : Type v) [Ring R] {X Y : TopCat.{max v u}}
    (f : X ⟶ Y) (n : ℕ)
    (c : ((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
      (ModuleCat.of R (ULift.{u} R))).obj X) :
    Y.singularHomologyUliftAddEquiv R n
        ((((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
          (ModuleCat.of R (ULift.{u} R))).map f).hom c) =
      HomologicalComplex.homologyMap ((TauCeti.singularChains (ULift.{u} R)).map f) n
        (X.singularHomologyUliftAddEquiv R n c) :=
  ConcreteCategory.congr_hom (singularHomologyUliftIso_hom_naturality R f n) c

/-- The inverse of `TopCat.singularHomologyUliftAddEquiv` is natural in `X`. -/
theorem singularHomologyUliftAddEquiv_symm_naturality (R : Type v) [Ring R]
    {X Y : TopCat.{max v u}} (f : X ⟶ Y) (n : ℕ)
    (c : ((TauCeti.singularChains (ULift.{u} R)).obj X).homology n) :
    (Y.singularHomologyUliftAddEquiv R n).symm
        (HomologicalComplex.homologyMap ((TauCeti.singularChains (ULift.{u} R)).map f) n c) =
      (((singularHomologyFunctor (ModuleCat.{max v u} R) n).obj
        (ModuleCat.of R (ULift.{u} R))).map f).hom
          ((X.singularHomologyUliftAddEquiv R n).symm c) :=
  ConcreteCategory.congr_hom (singularHomologyUliftIso_inv_naturality R f n) c

end TopCat

end
