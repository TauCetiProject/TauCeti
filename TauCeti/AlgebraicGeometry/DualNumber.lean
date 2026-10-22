/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The spectrum of the dual numbers

For a commutative ring `R`, the structure morphism `Spec R[ε] ⟶ Spec R` of the spectrum of the dual
numbers `R[ε] = R[X]/(X²)` has the section `Spec R ⟶ Spec R[ε]` induced by `ε ↦ 0`. Base change
along the projection is the trivial first-order deformation of a scheme over `R`, and base change
along the section is reduction modulo `ε`; together they compare automorphisms of a first-order
deformation with automorphisms of the original object.

## Main definitions

* `TauCeti.AlgebraicGeometry.dualNumberSplitEpi`: the projection `Spec R[ε] ⟶ Spec R`, split by
  the section `ε ↦ 0`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- The projection `Spec R[ε] ⟶ Spec R` from the spectrum of the dual numbers over `R`, split by
the section `Spec R ⟶ Spec R[ε]` induced by `ε ↦ 0`. Base change along this projection is the
trivial first-order deformation of a scheme over `R`, and base change along its section is
reduction modulo `ε`. -/
def dualNumberSplitEpi (R : Type u) [CommRing R] :
    SplitEpi (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))) where
  section_ := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)
  id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    refine congrArg Spec.map ?_
    ext r
    simp

/-- The section of `dualNumberSplitEpi R` is induced by the projection `R[ε] → R`, `ε ↦ 0`. -/
theorem dualNumberSplitEpi_section (R : Type u) [CommRing R] :
    (dualNumberSplitEpi R).section_ =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) :=
  (rfl)

end TauCeti.AlgebraicGeometry
