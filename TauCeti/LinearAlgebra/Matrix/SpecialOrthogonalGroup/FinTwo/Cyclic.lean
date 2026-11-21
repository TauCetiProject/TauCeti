/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.FinTwo

/-!
# Finite subgroups of `SO(2)` are cyclic

Over an integral domain `R` in which `2 ≠ 0`, the group `SO(2, R)` embeds into the units of the
algebraic closure `L` of the fraction field of `R`: choosing a square root `i` of `-1` in `L`, the
map `!![a, b; -b, a] ↦ a + i b` is `Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits` over `L`.
Finite subgroups of the units of a field are cyclic, hence so is every finite group embedding into
`SO(2, R)`.

## Main declarations

* `TauCeti.Matrix.SpecialOrthogonalGroup.isCyclic_of_injective_specialOrthogonalGroup_fin_two`:
  a finite group embedding into `SO(2, R)` is cyclic.
-/

public section

namespace TauCeti.Matrix.SpecialOrthogonalGroup

attribute [local instance] starRingOfComm

variable {R : Type*} [CommRing R]

/-- Over an integral domain in which `2 ≠ 0`, **a finite group embedding into `SO(2)` is
cyclic**: `!![a, b; -b, a] ↦ a + i b` embeds `SO(2)` into the units of an algebraically closed
field containing a square root `i` of `-1`. -/
theorem isCyclic_of_injective_specialOrthogonalGroup_fin_two [IsDomain R] [NeZero (2 : R)]
    {G : Type*} [Group G] [Finite G] (f : G →* _root_.Matrix.specialOrthogonalGroup (Fin 2) R)
    (hf : Function.Injective f) : IsCyclic G := by
  let L := AlgebraicClosure (FractionRing R)
  have hφ : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R)]
    exact (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R _)
  have h2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap R L) 2, ← map_zero (algebraMap R L)]
    exact hφ.ne two_ne_zero
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) two_pos
  let e := Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits i 2⁻¹ hi (mul_inv_cancel₀ h2)
  refine isCyclic_of_injective_ringHom ((Units.coeHom L).comp
    (e.toMonoidHom.comp ((Matrix.SpecialOrthogonalGroup.map (algebraMap R L)).comp f))) ?_
  exact Units.val_injective.comp (e.injective.comp
    ((Matrix.SpecialOrthogonalGroup.map_injective hφ).comp hf))

end TauCeti.Matrix.SpecialOrthogonalGroup
