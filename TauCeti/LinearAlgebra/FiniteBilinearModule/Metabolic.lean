/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

/-!
# Metabolic finite quadratic modules

A finite quadratic module is metabolic when it has a quadratic Lagrangian: a subgroup on
which the quadratic form vanishes and which equals its orthogonal complement for the polar
pairing. This is the condition that arises when an even lattice is glued to an even
unimodular overlattice. Bilinear isotropy alone does not suffice.

The terminology follows Nikulin, *Integral symmetric bilinear forms and some of their
applications*, §1.4.
-/

public section

namespace TauCeti

namespace FiniteQuadraticModule

/-- A finite quadratic module is metabolic if it admits a quadratic Lagrangian. -/
def IsMetabolic (A : FiniteQuadraticModule) : Prop :=
  ∃ H : AddSubgroup A, A.IsLagrangian H

/-- Metabolicity means that a quadratic Lagrangian exists. -/
@[simp]
theorem isMetabolic_def (A : FiniteQuadraticModule) :
    A.IsMetabolic ↔ ∃ H : AddSubgroup A, A.IsLagrangian H := Iff.rfl

/-- A nondegenerate metabolic finite quadratic module has square order: a quadratic Lagrangian
has order whose square is the order of the ambient group. -/
theorem IsMetabolic.isSquare_natCard {A : FiniteQuadraticModule} (h : A.IsMetabolic)
    (hA : A.IsNondegenerate) : IsSquare (Nat.card A) := by
  obtain ⟨H, hH⟩ := A.isMetabolic_def.mp h
  refine ⟨Nat.card H, ?_⟩
  simpa only [pow_two] using
    (FiniteBilinearModule.IsLagrangian.card_sq _ hH.toFiniteBilinearModule hA).symm

/-- An isometry preserves the existence of a quadratic Lagrangian.
The isometry must be supplied explicitly: it occurs in neither side of the equivalence. -/
theorem Isometry.isMetabolic_iff {A B : FiniteQuadraticModule} (f : Isometry A B) :
    A.IsMetabolic ↔ B.IsMetabolic := by
  rw [A.isMetabolic_def, B.isMetabolic_def]
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨H.map f.toAddEquiv,
      (FiniteQuadraticModule.Isometry.isLagrangian_map_iff A f H).2 hH⟩
  · rintro ⟨H, hH⟩
    exact ⟨H.map f.symm.toAddEquiv,
      (FiniteQuadraticModule.Isometry.isLagrangian_map_iff B (f.symm : Isometry B A) H).2 hH⟩

end FiniteQuadraticModule

end TauCeti
