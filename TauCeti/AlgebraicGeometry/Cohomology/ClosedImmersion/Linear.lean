/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic

/-!
# Linear cohomology comparison for closed immersions

For a closed immersion `f : X ⟶ Y`, the cohomology comparison
`Hⁿ(Y, f_* M) ≅ Hⁿ(X, M)` respects global functions: a scalar `r` on `Y` acts on the
right through its pullback `f^♯ r`. When `f` is a morphism over a commutative ring `R`,
the comparison is therefore `R`-linear, naturally in the coefficient sheaf `M`.

Over a field, this preserves cohomology dimensions and truncated Euler characteristics.
In particular, finite-dimensionality may be proved on an ambient projective scheme and
transferred to a closed subscheme. These comparisons impose no coherence, Noetherianity,
or properness assumptions on the schemes or coefficient sheaves.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Lemma 2.10 and Theorem 5.2.
-/

-- The underlying additive comparison is `cohomologyPushforwardIso`; scalar compatibility
-- uses its naturality and `Scheme.Modules.pushforward_map_globalSectionsSmul`.

public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- The closed-immersion cohomology comparison carries the action of a global function on
the ambient scheme to the action of its pullback on the closed subscheme. -/
-- Scalar actions simplify to cohomology maps, so this is a rewriting lemma.
lemma cohomologyPushforwardIso_hom_smul (M : X.Modules) (n : ℕ) (r : Γ(Y, ⊤))
    (x : Cohomology ((pushforward f).obj M) n) :
    (cohomologyPushforwardIso f M n).hom (r • x) =
      f.appTop r • (cohomologyPushforwardIso f M n).hom x := by
  rw [cohomology_smul, cohomology_smul]
  have h := ConcreteCategory.congr_hom
    (cohomologyPushforwardIso_naturality f (M.globalSectionsSmul (f.appTop r)) n) x
  simp only [Functor.comp_map, pushforward_map_globalSectionsSmul] at h
  -- The functor objects are definitionally the displayed cohomology groups, but rewriting
  -- their concrete-category composites requires unfolding the functor-object wrappers.
  erw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

section BaseRing

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))]

/-- Direct image along a closed immersion over `R` preserves cohomology as an `R`-module.
The underlying additive equivalence is the closed-immersion cohomology comparison. -/
def cohomologyPushforwardBaseLinearEquiv (M : X.Modules) (n : ℕ) :
    Cohomology ((pushforward f).obj M) n ≃ₗ[R] Cohomology M n where
  __ := (cohomologyPushforwardIso f M n).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    have hr : f.appTop (baseRingToGlobalSections R Y r) =
        baseRingToGlobalSections R X r := by
      rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
        ← CommRingCat.comp_apply, ← comp_appTop, HomIsOver.comp_over]
    -- The inherited `toFun` field must be identified with the isomorphism's forward map
    -- before applying its public scalar-compatibility theorem.
    change (cohomologyPushforwardIso f M n).hom (r • x) =
      r • (cohomologyPushforwardIso f M n).hom x
    simp only [base_smul_cohomology]
    rw [cohomologyPushforwardIso_hom_smul, hr]

/-- The linear comparison has the same forward map as the additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquiv_apply (M : X.Modules) (n : ℕ)
    (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquiv f R M n x =
      (cohomologyPushforwardIso f M n).hom x :=
  (rfl)

/-- The inverse linear comparison has the same map as the inverse additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquiv_symm_apply (M : X.Modules) (n : ℕ)
    (x : Cohomology M n) :
    (cohomologyPushforwardBaseLinearEquiv f R M n).symm x =
      (cohomologyPushforwardIso f M n).inv x :=
  (rfl)

/-- The base-linear closed-immersion comparison commutes with maps of coefficient sheaves. -/
lemma cohomologyPushforwardBaseLinearEquiv_naturality {M N : X.Modules} (α : M ⟶ N)
    (n : ℕ) (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquiv f R N n
        (cohomologyMapBaseLinear R Y ((pushforward f).map α) n x) =
      cohomologyMapBaseLinear R X α n (cohomologyPushforwardBaseLinearEquiv f R M n x) := by
  rw [cohomologyPushforwardBaseLinearEquiv_apply, cohomologyPushforwardBaseLinearEquiv_apply]
  simp only [cohomologyMapBaseLinear_apply]
  have h := ConcreteCategory.congr_hom (cohomologyPushforwardIso_naturality f α n) x
  -- As in scalar compatibility, the categorical functor objects require default transparency.
  dsimp only [Functor.comp_map] at h
  erw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

/-- Cohomology of a direct image along a closed immersion is finite over the base ring
exactly when the original cohomology is finite. -/
@[simp]
theorem moduleFinite_cohomology_pushforward_iff (M : X.Modules) (n : ℕ) :
    Module.Finite R (Cohomology ((pushforward f).obj M) n) ↔
      Module.Finite R (Cohomology M n) :=
  Module.Finite.equiv_iff (cohomologyPushforwardBaseLinearEquiv f R M n)

/-- Direct image along a closed immersion over a commutative ring preserves cohomology
finranks, including the value zero assigned to modules of infinite rank. -/
@[simp]
theorem finrank_cohomology_pushforward (M : X.Modules) (n : ℕ) :
    Module.finrank R (Cohomology ((pushforward f).obj M) n) =
      Module.finrank R (Cohomology M n) :=
  (cohomologyPushforwardBaseLinearEquiv f R M n).finrank_eq

end BaseRing

section Field

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [f.IsOver (Spec (.of k))]

/-- Direct image along a closed immersion preserves the truncated Euler characteristic.
When cohomology is finite-dimensional and vanishes above the truncation, this is the
equality of the usual Euler characteristics. -/
@[simp]
theorem eulerCharBelow_pushforward (M : X.Modules) (n : ℕ) :
    eulerCharBelow k Y ((pushforward f).obj M) n = eulerCharBelow k X M n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [eulerCharBelow_succ, finrank_cohomology_pushforward, ih]

end Field

end

end AlgebraicGeometry.Scheme.Hom
