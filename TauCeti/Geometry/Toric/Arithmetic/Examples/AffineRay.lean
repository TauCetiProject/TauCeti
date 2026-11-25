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
It is complete, because its support is the closed ray. Since `ArithmeticFan` takes the set
`Cstar` as a parameter, the same cones also form an arithmetic cone system for `Cstar = ℝ`. The
whole line is not the rational closure of `ℝ_{>0}`, and that system is not complete: the example
only shows that completeness is measured against the parameter `Cstar`, not the ambient space.

## Main declarations

* `TauCeti.Toric.affineRayArithmeticFan`: the faces of the positive ray, as an arithmetic cone
  system for any parameter `Cstar` containing the closed ray.
* `TauCeti.Toric.isComplete_affineRayArithmeticFan_iff`: this system is complete exactly when
  `Cstar` is the closed positive ray, the rational closure of the open positive ray.
-/

public section

namespace TauCeti.Toric

/-- The faces of the positive ray, as an arithmetic cone system for the trivial group, the open
positive ray as positivity cone, and any set `Cstar` containing the closed ray in place of the
rational closure. The rational closure of the open positive ray is the closed positive ray. -/
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
  rw [affineRayArithmeticFan, Fan.support_toArithmeticFan, support_affineRayFan]

/-- The positive-ray system is complete exactly when `Cstar` is the closed positive ray, which is
the rational closure of the positivity cone. In particular it is complete for `Cstar = ℝ_{≥0}`,
and not complete for `Cstar = ℝ`, which is not the rational closure of the positivity cone. -/
theorem isComplete_affineRayArithmeticFan_iff {Cstar : Set (Fin 1 → ℝ)}
    (h : (affineRayCone : Set _) ⊆ Cstar) :
    (affineRayArithmeticFan h).IsComplete ↔ Cstar = affineRayCone := by
  rw [ArithmeticFan.isComplete_def, support_affineRayArithmeticFan, eq_comm]

/-- The positive-ray system for the closed positive ray is complete. -/
theorem isComplete_affineRayArithmeticFan :
    (affineRayArithmeticFan subset_rfl).IsComplete :=
  (isComplete_affineRayArithmeticFan_iff _).2 rfl

/-- The positive-ray system with `Cstar` the whole line is not complete. The whole line is not
the rational closure of the positivity cone: this only shows that completeness is relative to the
parameter `Cstar`, not to the ambient space. -/
theorem not_isComplete_affineRayArithmeticFan_univ :
    ¬ (affineRayArithmeticFan (Set.subset_univ _)).IsComplete := by
  rw [isComplete_affineRayArithmeticFan_iff]
  intro h
  have : (-1 : Fin 1 → ℝ) ∈ (affineRayCone : Set (Fin 1 → ℝ)) := h ▸ Set.mem_univ _
  norm_num at this

end TauCeti.Toric
