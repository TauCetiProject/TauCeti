/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# The fan of a point

The zero cone on the zero-dimensional lattice is the fan of a point. Every fan has a canonical
morphism to it, induced by the zero lattice map.
-/

public section

namespace TauCeti.Toric

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The fan of a point, on the zero-dimensional lattice. -/
def pointFan : Fan ((Int.castAddHom ℝ).compLeft (Fin 0)) :=
  Fan.ofCone (isIntegralLattice_intCast 0)
    (isToricCone_bot ((Int.castAddHom ℝ).compLeft (Fin 0)))

/-- A cone belongs to the fan of a point exactly when it is the zero cone. -/
@[simp]
theorem mem_pointFan_cones (σ : PointedCone ℝ (Fin 0 → ℝ)) :
    σ ∈ pointFan.cones ↔ σ = ⊥ := by
  rw [pointFan, Fan.mem_ofCone_cones]
  constructor
  · intro h
    exact le_antisymm h.le bot_le
  · rintro rfl
    exact PointedCone.IsFaceOf.refl _

/-- The fan of a point is regular. -/
theorem isRegular_pointFan : pointFan.IsRegular :=
  Fan.isRegular_ofCone (isIntegralLattice_intCast 0)
    (isRegularCone_bot (isIntegralLattice_intCast 0))

/-- The canonical fan morphism from any fan to the fan of a point. -/
noncomputable def Fan.toPoint (Φ : Fan i) : FanHom Φ pointFan :=
  FanHom.ofLatticeMap Φ pointFan 0 fun σ hσ ↦ by
    refine ⟨⊥, ?_, ?_⟩
    · exact (mem_pointFan_cones ⊥).2 rfl
    · exact le_of_eq (Subsingleton.elim _ _)

/-- The real-linear map of `Fan.toPoint` is zero. -/
@[simp]
theorem Fan.toPoint_realMap (Φ : Fan i) : Φ.toPoint.realMap = 0 := by
  rw [Fan.toPoint, FanHom.ofLatticeMap_realMap]
  exact Subsingleton.elim _ _

/-- The lattice map of `Fan.toPoint` is zero. -/
@[simp]
theorem Fan.toPoint_latticeMap (Φ : Fan i) : Φ.toPoint.latticeMap = 0 := by
  rw [Fan.toPoint, FanHom.ofLatticeMap_latticeMap]

/-- Every fan morphism to the fan of a point is the canonical one. -/
theorem FanHom.eq_toPoint
    (f : FanHom Φ (pointFan : Fan
      ((Int.castAddHom ℝ).compLeft (Fin 0) : (Fin 0 → ℤ) →+ (Fin 0 → ℝ)))) :
    f = Fan.toPoint (i := i) Φ := by
  apply FanHom.ext (Φ := Φ) (Ψ := (pointFan : Fan
    ((Int.castAddHom ℝ).compLeft (Fin 0) : (Fin 0 → ℤ) →+ (Fin 0 → ℝ))))
  rw [Fan.toPoint_latticeMap]
  apply AddMonoidHom.ext
  intro n
  exact Subsingleton.elim _ _

end TauCeti.Toric
