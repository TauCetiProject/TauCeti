/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Quadratic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.GeneralLinear
public import TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Quotient

/-!
# Units of a quadratic order fix the values of level-`N` functions at its quadratic point

Let `τ ∈ ℍ` satisfy `τ² + Bτ + C = 0` with `B, C ∈ ℤ`, so that `ℤ τ + ℤ` is the quadratic order
`ℤ[τ] ≅ QuadraticAlgebra ℤ (-C) (-B)`; the canonical CM point `τ_D` of
`TauCeti.BinaryQuadraticForm.cmPoint` is the main example. Multiplication by `t + sτ` has matrix
`!![t - Bs, -Cs; s, t]` in row coordinates on `(τ, 1)`, and reducing these matrices modulo `N`
gives the group `QuadraticAlgebra.periodMatrixGroup` through which `(ℤ[τ] / N)ˣ` acts in
finite-level CM reciprocity (Shin, Proposition 2.5). The reductions of the actual units of
`ℤ[τ]` form the subgroup `QuadraticAlgebra.unitPeriodMatrixSubgroup (-C) (-B) N`. For the
maximal order of an imaginary quadratic field `K`, the quotient by this subgroup is
`Gal(K_(N) / H_K)` (`TauCeti.ClassFieldTheory.periodMatrixQuotientArtinEquiv`).

This file proves the modular-function side of that comparison. The stabilizer of `τ` in
`SL(2, ℤ)` consists exactly of the multiplication matrices of the units of `ℤ[τ]`
(`UpperHalfPlane.stabilizer_eq_range_periodUnitSLMatrix`), so its reduction modulo `N` is the
unit subgroup (`UpperHalfPlane.map_stabilizer_eq_map_unitPeriodMatrixSubgroup`). A unit has norm
`1`, so its matrix acts on `F_N` through the fractional linear action of `SL(2, ℤ/Nℤ)` alone, and
since it fixes `τ`, every element of the unit subgroup leaves the value at `τ` of every level-`N`
function unchanged
(`TauCeti.unop_modularFunctionFieldGLAction_apply_ofQuotient_of_mem_unitPeriodMatrixSubgroup`).
This includes the exceptional units at `D = -4` and `D = -3`, where the stabilizer of `τ_D` has
order `4` and `6` rather than `2`
(`TauCeti.BinaryQuadraticForm.natCard_stabilizer_cmPoint`).

## Main results

* `UpperHalfPlane.map_stabilizer_eq_map_unitPeriodMatrixSubgroup`: the reduction modulo `N` of
  the stabilizer of `τ` in `SL(2, ℤ)` is `unitPeriodMatrixSubgroup (-C) (-B) N`.
* `TauCeti.unop_modularFunctionFieldGLAction_unitPeriodMatrixHom_apply_ofQuotient` and
  `TauCeti.unop_modularFunctionFieldGLAction_apply_ofQuotient_of_mem_unitPeriodMatrixSubgroup`:
  the reduced units act trivially on the values at `τ` of the functions in `F_N`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, arXiv:1009.2253,
  §2, Proposition 2.5.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.8.
-/

public noncomputable section

open Matrix MulOpposite CongruenceSubgroup Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped MatrixGroups UpperHalfPlane

namespace UpperHalfPlane

variable (τ : ℍ) {B C : ℤ}

/-- **Reduced stabilizer of a quadratic point**: reducing the stabilizer of `τ` in `SL(2, ℤ)`
modulo `N` gives exactly the reductions `unitPeriodMatrixSubgroup (-C) (-B) N` of the
multiplication matrices of the units of `ℤ[τ]`. -/
theorem map_stabilizer_eq_map_unitPeriodMatrixSubgroup (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (N : ℕ) :
    (MulAction.stabilizer SL(2, ℤ) τ).map
        (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (Int.castRingHom (ZMod N)))) =
      (QuadraticAlgebra.unitPeriodMatrixSubgroup (-C) (-B) N).map
        (QuadraticAlgebra.periodMatrixGroup ((-C : ℤ) : ZMod N) ((-B : ℤ) : ZMod N)).subtype := by
  rw [τ.stabilizer_eq_range_periodUnitSLMatrix hτ, QuadraticAlgebra.unitPeriodMatrixSubgroup_def,
    MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  ext u : 1
  exact (QuadraticAlgebra.coe_unitPeriodMatrixHom_eq_toGL_map _ N u).symm

end UpperHalfPlane

namespace TauCeti

variable {N : ℕ} [NeZero N] (τ : ℍ) {B C : ℤ}

/-- **Units act trivially on values at their quadratic point**: for a unit `u` of `ℤ[τ]`, the
reduction modulo `N` of its multiplication matrix sends every `F ∈ F_N` to a function with the
same value as `F` at the orbit of `τ`. -/
theorem unop_modularFunctionFieldGLAction_unitPeriodMatrixHom_apply_ofQuotient
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (u : (QuadraticAlgebra ℤ (-C) (-B))ˣ)
    (F : modularFunctionField N) :
    (unop (modularFunctionFieldGLAction N (QuadraticAlgebra.unitPeriodMatrixHom (-C) (-B) N u))
        F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)
        (ofQuotient (Quotient.mk _ τ)) =
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)
        (ofQuotient (Quotient.mk _ τ)) := by
  rw [QuadraticAlgebra.coe_unitPeriodMatrixHom_eq_toGL_map (τ.discr_lt_zero_of_quadratic hτ).le,
    modularFunctionFieldGLAction_toGL, coe_unop_modularFunctionFieldActionZMod_apply,
    modularFunctionActionZMod_map, modularFunctionAction_apply_ofQuotient,
    τ.periodUnitSLMatrix_smul hτ u]

/-- **The reduced units lie in the kernel of the value action at `τ`**: every matrix of
`unitPeriodMatrixSubgroup (-C) (-B) N` sends each `F ∈ F_N` to a function with the same value as
`F` at the orbit of `τ`. -/
theorem unop_modularFunctionFieldGLAction_apply_ofQuotient_of_mem_unitPeriodMatrixSubgroup
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    {M : QuadraticAlgebra.periodMatrixGroup ((-C : ℤ) : ZMod N) ((-B : ℤ) : ZMod N)}
    (hM : M ∈ QuadraticAlgebra.unitPeriodMatrixSubgroup (-C) (-B) N)
    (F : modularFunctionField N) :
    (unop (modularFunctionFieldGLAction N M)
        F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)
        (ofQuotient (Quotient.mk _ τ)) =
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)
        (ofQuotient (Quotient.mk _ τ)) := by
  obtain ⟨u, rfl⟩ := QuadraticAlgebra.mem_unitPeriodMatrixSubgroup_iff.mp hM
  exact unop_modularFunctionFieldGLAction_unitPeriodMatrixHom_apply_ofQuotient τ hτ u F

end TauCeti
