/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine

/-!
# Cohomology along arbitrary affine morphisms

For an affine morphism `f : X ⟶ Y` and a quasi-coherent module `M`, the positive
higher direct images vanish. Hence `Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` in every degree,
naturally in `M` and linearly over any base ring. No finite open cover or separation
hypothesis on the schemes is required.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Exercise 4.1.
-/

public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- An affine morphism preserves the cohomology of a quasi-coherent coefficient module. -/
def cohomologyPushforwardIsoOfIsAffineHom (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((pushforward f).obj M) n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  f.cohomologyPushforwardIsoOfIsZeroHigherDirectImage M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n

/-- The affine cohomology comparison is natural in the quasi-coherent coefficient module. -/
@[reassoc]
theorem cohomologyPushforwardIsoOfIsAffineHom_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) (n : ℕ) :
    (cohomologyFunctor Y n).map ((pushforward f).map φ) ≫
        (cohomologyPushforwardIsoOfIsAffineHom f N n).hom =
      (cohomologyPushforwardIsoOfIsAffineHom f M n).hom ≫
        (cohomologyFunctor X n).map φ :=
  f.cohomologyPushforwardIsoOfIsZeroHigherDirectImage_naturality φ
    (f.isZero_higherDirectImage_succ_of_isAffineHom M)
    (f.isZero_higherDirectImage_succ_of_isAffineHom N) n

/-- The affine cohomology comparison intertwines a global function with its pullback. -/
lemma cohomologyPushforwardIsoOfIsAffineHom_hom_smul (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (r : Γ(Y, ⊤)) (x : Cohomology ((pushforward f).obj M) n) :
    (cohomologyPushforwardIsoOfIsAffineHom f M n).hom (r • x) =
      f.appTop r • (cohomologyPushforwardIsoOfIsAffineHom f M n).hom x :=
  f.cohomologyPushforwardIsoOfIsZeroHigherDirectImage_hom_smul M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n r x

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))]

/-- An affine morphism over `R` preserves quasi-coherent cohomology as an `R`-module. -/
def cohomologyPushforwardBaseLinearEquivOfIsAffineHom (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : Cohomology ((pushforward f).obj M) n ≃ₗ[R] Cohomology M n :=
  f.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImage R M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n

/-- The linear affine comparison has the forward map of the additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsAffineHom_apply (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquivOfIsAffineHom f R M n x =
      (cohomologyPushforwardIsoOfIsAffineHom f M n).hom x :=
  f.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImage_apply R M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n x

/-- The inverse linear affine comparison has the map of the inverse additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsAffineHom_symm_apply (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (x : Cohomology M n) :
    (cohomologyPushforwardBaseLinearEquivOfIsAffineHom f R M n).symm x =
      (cohomologyPushforwardIsoOfIsAffineHom f M n).inv x :=
  f.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImage_symm_apply R M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n x

/-- Finiteness of quasi-coherent cohomology transfers through any affine morphism over `R`. -/
theorem moduleFinite_cohomology_pushforward_iff_of_isAffineHom (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    Module.Finite R (Cohomology ((pushforward f).obj M) n) ↔
      Module.Finite R (Cohomology M n) :=
  Module.Finite.equiv_iff (cohomologyPushforwardBaseLinearEquivOfIsAffineHom f R M n)

end AlgebraicGeometry.Scheme.Hom
