/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight

/-!
# Recovering E₆ torus coordinates from six minuscule weights

The minuscule weights at indices `0`, `1`, `2`, `4`, `5`, `11` form an integral basis of the
character lattice. This file reads the fundamental-weight torus coordinates from values on
those six weights and verifies that evaluation recovers the seed values. It shares the
coordinate calculation used for the minuscule cubic stabilizer and the doubled carrier's torus.

Writing `μₐ` for the minuscule weights, the coordinate change is
`ϖ₁ = μ₀`, `ϖ₂ = μ₂ + μ₅ + μ₁₁`, `ϖ₃ = μ₀ + μ₁`, `ϖ₄ = μ₀ + μ₁ + μ₂`,
`ϖ₅ = μ₂ + μ₄ + μ₅ + μ₁₁` and `ϖ₆ = μ₄ + μ₅`.

The calculation is extracted from `TauCeti.Algebra.Lie.E6.DoubledMinuscule.MaximalTorus`.
-/

public section

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

/-- Fundamental-weight torus coordinates obtained from values on the six seed minuscule
weights at indices `0`, `1`, `2`, `4`, `5`, `11`. Values at the other indices are unused. -/
def torusParameterOfSeedValues {G : Type*} [CommGroup G] (t : Fin 27 → G) : Fin 6 → G :=
  ![t 0, t 2 * t 5 * t 11, t 0 * t 1, t 0 * t 1 * t 2,
    t 2 * t 4 * t 5 * t 11, t 4 * t 5]

/-- The six fundamental-weight coordinates in terms of the seed values. -/
theorem torusParameterOfSeedValues_def {G : Type*} [CommGroup G] (t : Fin 27 → G) :
    torusParameterOfSeedValues t =
      ![t 0, t 2 * t 5 * t 11, t 0 * t 1, t 0 * t 1 * t 2,
        t 2 * t 4 * t 5 * t 11, t 4 * t 5] := (rfl)

/-- The zeroth coordinate is the value at seed `0`. -/
@[simp] theorem torusParameterOfSeedValues_apply_zero {G : Type*} [CommGroup G]
    (t : Fin 27 → G) : torusParameterOfSeedValues t 0 = t 0 := (rfl)

/-- The first coordinate is the product of the values at seeds `2`, `5`, `11`. -/
@[simp] theorem torusParameterOfSeedValues_apply_one {G : Type*} [CommGroup G]
    (t : Fin 27 → G) : torusParameterOfSeedValues t 1 = t 2 * t 5 * t 11 := (rfl)

/-- The second coordinate is the product of the values at seeds `0`, `1`. -/
@[simp] theorem torusParameterOfSeedValues_apply_two {G : Type*} [CommGroup G]
    (t : Fin 27 → G) : torusParameterOfSeedValues t 2 = t 0 * t 1 := (rfl)

/-- The third coordinate is the product of the values at seeds `0`, `1`, `2`. -/
@[simp] theorem torusParameterOfSeedValues_apply_three {G : Type*} [CommGroup G]
    (t : Fin 27 → G) : torusParameterOfSeedValues t 3 = t 0 * t 1 * t 2 := (rfl)

/-- The fourth coordinate is the product of the values at seeds `2`, `4`, `5`, `11`. -/
@[simp] theorem torusParameterOfSeedValues_apply_four {G : Type*} [CommGroup G]
    (t : Fin 27 → G) : torusParameterOfSeedValues t 4 = t 2 * t 4 * t 5 * t 11 := (rfl)

/-- The fifth coordinate is the product of the values at seeds `4`, `5`. -/
@[simp] theorem torusParameterOfSeedValues_apply_five {G : Type*} [CommGroup G]
    (t : Fin 27 → G) : torusParameterOfSeedValues t 5 = t 4 * t 5 := (rfl)

/-- Evaluating the torus parameter recovered from seed values returns those values on each
of the six seed minuscule weights. -/
theorem torusCharacter_torusParameterOfSeedValues {A : Type*} [CommRing A]
    (t : Fin 27 → Aˣ) :
    ∀ a ∈ ({0, 1, 2, 4, 5, 11} : Finset (Fin 27)),
      torusCharacter (torusParameterOfSeedValues t) (e6MinusculeWeight a) = t a := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro a (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [torusParameterOfSeedValues, torusCharacter_def, Fin.prod_univ_six] <;>
    apply Additive.ofMul.injective <;>
    simp [e6MinusculeWeight, ofMul_mul, ofMul_inv] <;> abel

end TauCeti.E6Minuscule
