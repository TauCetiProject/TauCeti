/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.AffineRay
public import TauCeti.Geometry.Toric.Arithmetic.Fan

/-!
# The positive ray as an arithmetic cone system

This is the cone system at a cusp of a modular curve, for the component of the upper half-plane:
the positivity cone is the open positive ray `ℝ_{>0}`, its rational closure is the closed ray
`ℝ_{≥0}`, and the faces of the closed ray form an arithmetic cone system for the trivial group.
It is complete, because its support is the closed ray. The same cones form an arithmetic cone
system whose rational closure is the whole line, and that system is not complete: completeness
is measured against the rational closure of the positivity cone, not against the ambient space.

## Main declarations

* `TauCeti.Toric.affineRayArithmeticFan`: the faces of the positive ray, as an arithmetic cone
  system for any rational closure containing the closed ray.
* `TauCeti.Toric.isComplete_affineRayArithmeticFan_iff`: this system is complete exactly when the
  rational closure is the closed positive ray.
-/

public section

namespace TauCeti.Toric

/-- The faces of the positive ray, as an arithmetic cone system for the trivial group, the open
positive ray as positivity cone, and any rational closure `Cstar` containing the closed ray. -/
def affineRayArithmeticFan {Cstar : Set (Fin 1 → ℝ)} (h : (affineRayCone : Set _) ⊆ Cstar) :
    ArithmeticFan ((Int.castAddHom ℝ).compLeft (Fin 1)) ⊥ {x | 0 < x 0} Cstar :=
  affineRayFan.toArithmeticFan affineRayFan.map_mem_of_mem_bot (support_affineRayFan ▸ h)

/-- The cones of the positive-ray system are the faces of the positive ray. -/
@[simp]
theorem affineRayArithmeticFan_cones {Cstar : Set (Fin 1 → ℝ)}
    (h : (affineRayCone : Set _) ⊆ Cstar) :
    (affineRayArithmeticFan h).cones = affineRayFan.cones :=
  Fan.toArithmeticFan_cones ..

/-- The support of the positive-ray system is the closed positive ray. -/
theorem support_affineRayArithmeticFan {Cstar : Set (Fin 1 → ℝ)}
    (h : (affineRayCone : Set _) ⊆ Cstar) :
    (affineRayArithmeticFan h).support = affineRayCone := by
  rw [← support_affineRayFan]
  ext
  simp only [ArithmeticFan.mem_support, affineRayArithmeticFan_cones, Fan.mem_support]

/-- The positive-ray system is complete exactly when the rational closure of the positivity cone
is the closed positive ray. In particular it is complete for `Cstar = ℝ_{≥0}`, and not complete
for `Cstar = ℝ`. -/
theorem isComplete_affineRayArithmeticFan_iff {Cstar : Set (Fin 1 → ℝ)}
    (h : (affineRayCone : Set _) ⊆ Cstar) :
    (affineRayArithmeticFan h).IsComplete ↔ Cstar = affineRayCone := by
  rw [ArithmeticFan.isComplete_def, support_affineRayArithmeticFan, eq_comm]

/-- The positive-ray system for the closed positive ray is complete. -/
theorem isComplete_affineRayArithmeticFan :
    (affineRayArithmeticFan subset_rfl).IsComplete :=
  (isComplete_affineRayArithmeticFan_iff _).2 rfl

/-- The positive-ray system for the whole line is not complete. -/
theorem not_isComplete_affineRayArithmeticFan_univ :
    ¬ (affineRayArithmeticFan (Set.subset_univ _)).IsComplete := by
  rw [isComplete_affineRayArithmeticFan_iff]
  intro h
  have : (-1 : Fin 1 → ℝ) ∈ (affineRayCone : Set (Fin 1 → ℝ)) := h ▸ Set.mem_univ _
  simp at this
  linarith

end TauCeti.Toric
