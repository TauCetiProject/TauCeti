/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linear cohomology comparison for acyclic direct images

If the positive higher direct images of `M` along `f : X ⟶ Y` vanish, the comparison
`Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` sends multiplication by a global function on `Y` to
multiplication by its pullback. For a morphism over a commutative ring `R`, it is therefore
an `R`-linear equivalence. In particular, finiteness of cohomology over `R` can be transferred
in either direction through an acyclic direct image.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Exercise 8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The acyclic direct-image comparison intertwines a global function with its pullback. -/
lemma cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc_hom_smul (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) (r : Γ(Y, ⊤))
    (x : Cohomology ((pushforward f).obj M) n) :
    (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).hom (r • x) =
      f.appTop r • (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).hom x := by
  rw [cohomology_smul, cohomology_smul]
  simpa only [pushforward_map_globalSectionsSmul] using
    cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc_hom_apply_naturality f
      (M.globalSectionsSmul (f.appTop r)) hM hM n x

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))]

/-- The acyclic direct-image comparison for a morphism over `R` is `R`-linear. -/
def cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    Cohomology ((pushforward f).obj M) n ≃ₗ[R] Cohomology M n where
  __ := (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    have hr : f.appTop (baseRingToGlobalSections R Y r) =
        baseRingToGlobalSections R X r := by
      rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
        ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
    -- The inherited forward map must be identified with the additive comparison before
    -- its scalar-compatibility theorem can rewrite the goal.
    change (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).hom (r • x) =
      r • (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).hom x
    simp only [base_smul_cohomology]
    rw [cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc_hom_smul, hr]

/-- The linear comparison has the forward map of the additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_apply (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ)
    (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc f R M hM n x =
      (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).hom x :=
  (rfl)

/-- The inverse linear comparison has the map of the inverse additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_symm_apply (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ)
    (x : Cohomology M n) :
    (cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc f R M hM n).symm x =
      (cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc f M hM n).inv x :=
  (rfl)

/-- The linear acyclic direct-image comparison commutes with maps of coefficient modules. -/
lemma cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_naturality
    {M N : X.Modules} (φ : M ⟶ N)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M))
    (hN : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj N)) (n : ℕ)
    (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc f R N hN n
        (cohomologyMapBaseLinear R Y ((pushforward f).map φ) n x) =
      cohomologyMapBaseLinear R X φ n
        (cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc f R M hM n x) := by
  rw [cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_apply,
    cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_apply]
  simp only [cohomologyMapBaseLinear_apply]
  exact cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc_hom_apply_naturality f
    φ hM hN n x

/-- Cohomology is finite over the base ring exactly when the cohomology of its acyclic
direct image is finite. -/
theorem moduleFinite_cohomology_pushforward_iff_of_isZero_higherDirectImage_succ (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    Module.Finite R (Cohomology ((pushforward f).obj M) n) ↔
      Module.Finite R (Cohomology M n) :=
  Module.Finite.equiv_iff
    (cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc f R M hM n)

/-- The base-module finrank of cohomology is preserved by an acyclic direct image. -/
theorem finrank_cohomology_pushforward_of_isZero_higherDirectImage_succ (M : X.Modules)
    (hM : ∀ q, IsZero ((f.higherDirectImage (q + 1)).obj M)) (n : ℕ) :
    Module.finrank R (Cohomology ((pushforward f).obj M) n) =
      Module.finrank R (Cohomology M n) :=
  (cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc f R M hM n).finrank_eq

end AlgebraicGeometry.Scheme.Hom
