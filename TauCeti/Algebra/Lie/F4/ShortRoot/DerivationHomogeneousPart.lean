/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationGrading

/-!
# Homogeneous parts of derivations

The root-lattice homogeneous components of a derivation are again derivations.
-/

public section

open Matrix TauCeti.DynkinType

namespace TauCeti.F4ShortRoot

universe u
variable {R : Type u} [CommRing R]

/-- The part of a matrix supported in one root-lattice degree. -/
@[expose] def homogeneousPart (d : Fin 4 → ℤ) (X : Matrix (Fin 26) (Fin 26) R) :
    Matrix (Fin 26) (Fin 26) R :=
  fun i j => if entryDegree i j = d then X i j else 0

/-- Projection to one degree produces a homogeneous matrix. -/
theorem isHomogeneous_homogeneousPart (d : Fin 4 → ℤ)
    (X : Matrix (Fin 26) (Fin 26) R) : IsHomogeneous d (homogeneousPart d X) := by
  unfold IsHomogeneous
  intro i j hij
  simp [homogeneousPart, hij]

private def equationDegree (k i j : Fin 26) : Fin 4 → ℤ :=
  f4ShortRootWeight i - f4ShortRootWeight k - f4ShortRootWeight j

private theorem degrees_of_derivation_entry : ∀ k i j,
    (multCoeffOne k j = 0 ∨ entryDegree i (multTargetOne k j) = equationDegree k i j) ∧
    (multCoeffTwo k j = 0 ∨ entryDegree i (multTargetTwo k j) = equationDegree k i j) ∧
    (multRowCoeffOne k i = 0 ∨ entryDegree (multRowTargetOne k i) j = equationDegree k i j) ∧
    (multRowCoeffTwo k i = 0 ∨ entryDegree (multRowTargetTwo k i) j = equationDegree k i j) ∧
    (multIndexCoeffOne i j = 0 ∨ entryDegree (multIndexOne i j) k = equationDegree k i j) ∧
    (multIndexCoeffTwo i j = 0 ∨ entryDegree (multIndexTwo i j) k = equationDegree k i j) := by
  simp only [equationDegree]
  decide +kernel

private theorem mask_mul_intCast (d e q : Fin 4 → ℤ) (x : R) (c : ℤ)
    (hs : c = 0 ∨ e = q) :
    (if e = d then x else 0) * (c : R) = if q = d then x * (c : R) else 0 := by
  rcases hs with rfl | rfl <;> simp

private theorem intCast_mul_mask (d e q : Fin 4 → ℤ) (x : R) (c : ℤ)
    (hs : c = 0 ∨ e = q) :
    (c : R) * (if e = d then x else 0) = if q = d then (c : R) * x else 0 := by
  rcases hs with rfl | rfl <;> simp

/-- Every homogeneous part of a derivation is again a derivation. -/
theorem IsDerivation.homogeneousPart {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (d : Fin 4 → ℤ) : IsDerivation (homogeneousPart d X) := by
  rw [isDerivation_def]
  intro k
  ext i j
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.mul_apply (isDoubleStep_map_multiplicationOperator k),
    Matrix.IsDoubleStep.transpose_mul_apply (isDoubleStep_transpose_map_multiplicationOperator k),
    multiplicationBy_apply]
  have h := hX.entry k i j
  rcases degrees_of_derivation_entry k i j with ⟨h1, h2, h3, h4, h5, h6⟩
  simp only [F4ShortRoot.homogeneousPart]
  rw [mask_mul_intCast d _ _ _ _ h1, mask_mul_intCast d _ _ _ _ h2,
    intCast_mul_mask d _ _ _ _ h3, intCast_mul_mask d _ _ _ _ h4,
    intCast_mul_mask d _ _ _ _ h5, intCast_mul_mask d _ _ _ _ h6]
  by_cases hd : equationDegree k i j = d
  · simp only [hd, ↓reduceIte]
    exact h
  · simp only [hd, ↓reduceIte, add_zero, sub_self]

end TauCeti.F4ShortRoot
