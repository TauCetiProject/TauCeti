/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

/-!
# Scheme-valued points of the symplectic group

This file identifies scheme-valued points of `Sp₂ₘ` with the standard symplectic matrix group.
This interface lets group-scheme morphisms and identities, including root-subgroup and torus
actions, be computed as explicit symplectic matrix equations.

## Main declarations

* `TauCeti.Symplectic.groupSchemePointMulEquiv`: the spectrum-points equivalence for the
  symplectic coordinate Hopf algebra.
* `TauCeti.Symplectic.schemePointsMulEquiv`: scheme-valued points of `Sp₂ₘ` are
  `TauCeti.GLSymplecticFin`.

## References

* The scheme-points interface follows the formal template in
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme`.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The scheme underlying the symplectic group scheme is the spectrum of its coordinate Hopf
algebra. -/
lemma groupScheme_X_left :
    (groupScheme R m).X.left = Spec (CommRingCat.of (coordinateHopfAlgebra R m)) := by
  simpa only [groupScheme, ConstantForm.groupScheme, coordinateHopfAlgebra,
    ConstantForm.coordinateHopfAlgebra] using
    hopfSpec_obj_X_left R (coordinateHopfAlgebra R m)

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- Mathlib's spectrum-points equivalence for the symplectic coordinate Hopf algebra. -/
noncomputable def groupSchemePointMulEquiv :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
        (groupScheme R m).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation
    (coordinateHopfAlgebra R m) A (groupScheme_def R m)

/-- The underlying spectrum map of the scheme point associated to a symplectic algebra point. -/
-- Not `@[simp]`: `groupScheme` is a reducible specialization of the constant-form construction,
-- so the linter normalizes the target object before it can use this higher-level equation.
lemma groupSchemePointMulEquiv_apply_left
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (groupSchemePointMulEquiv m A f).left =
      Spec.map (CommRingCat.ofHom f.ofConv) ≫
        eqToHom (groupScheme_X_left R m).symm := by
  simpa only [groupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (coordinateHopfAlgebra R m) A (groupScheme_def R m)
        (groupScheme_X_left R m) f

/-- The group of scheme-valued points of `Sp₂ₘ` is the standard symplectic matrix group. -/
noncomputable def schemePointsMulEquiv :
    ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R m).X) ≃* GLSymplecticFin m A :=
  (groupSchemePointMulEquiv m A).symm.trans (pointsMulEquiv (A := A) R m)

/-- A scheme point presented by an algebra point corresponds to the same symplectic matrix. -/
-- Not `@[simp]`: the reducible `groupScheme` target prevents this statement from being in simp
-- normal form.
theorem schemePointsMulEquiv_groupSchemePointMulEquiv
    (q : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    schemePointsMulEquiv m A (groupSchemePointMulEquiv m A q) =
      pointsMulEquiv (A := A) R m q := by
  simp [schemePointsMulEquiv]

/-- Evaluating the symplectic scheme-points equivalence directly on a scheme morphism. -/
theorem schemePointsMulEquiv_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (groupScheme R m).X) :
    schemePointsMulEquiv m A p =
      pointsMulEquiv (A := A) R m ((groupSchemePointMulEquiv m A).symm p) := by
  unfold schemePointsMulEquiv
  rfl

/-- The inverse scheme-points equivalence sends a symplectic matrix to the spectrum point induced
by its canonical coordinate-algebra point. -/
-- Not `@[simp]`: the reducible `groupScheme` target prevents the left-hand side from being in simp
-- normal form.
theorem schemePointsMulEquiv_symm_apply (g : GLSymplecticFin m A) :
    (schemePointsMulEquiv m A).symm g =
      groupSchemePointMulEquiv m A ((pointsMulEquiv (A := A) R m).symm g) := by
  rfl

end TauCeti.Symplectic
