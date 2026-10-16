/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Tactic.FinCases

/-!
# The absolute norm of a binary quadratic form ideal

The two-generator form ideal has index `|a|` in its actual quadratic order. This is
computed from the determinant of the integral basis change and applies to both field and
split quadratic algebras whenever `a ≠ 0`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section

namespace TauCeti.BinaryQuadraticForm

/-- The index, hence absolute norm, of the two-generator form ideal is `|a|`. -/
theorem relIndex_orderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) :
    ((f.orderIdeal D hf).restrictScalars ℤ).toAddSubgroup.relIndex
      (QuadraticOrder.toSubalgebra D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubmodule.toAddSubgroup = f.a.natAbs := by
  let hD := hf ▸ f.discrim_emod_four_eq_zero_or_one
  let I := (f.orderIdeal D hf).restrictScalars ℤ
  let O := (QuadraticOrder.toSubalgebra D hD).toSubmodule
  have H : I ≤ O := orderIdeal_le_order f D hf
  let bI : Module.Basis (Fin 2) ℤ I := (f.idealBasis D hf ha).map
    (((f.orderIdeal D hf).restrictScalarsEquiv ℤ).restrictScalars ℤ).symm
  let bO : Module.Basis (Fin 2) ℤ O := (QuadraticOrder.basis D hD).map
    (QuadraticOrder.toSubalgebra D hD).toSubmoduleEquiv.symm
  have hbI (i : Fin 2) : (bI i : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (f.idealBasis D hf ha i : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    dsimp only [bI]
    rw [Module.Basis.map_apply]
    -- Scalar restriction changes the subtype's scalar action, not its underlying vector.
    rfl
  have hbO (i : Fin 2) : (bO i : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (QuadraticOrder.basis D hD i : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    dsimp only [bO]
    rw [Module.Basis.map_apply]
    -- The subalgebra-to-submodule equivalence is the identity on underlying vectors.
    rfl
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ H bI bO]
  let v : Fin 2 → O := fun i ↦ ⟨(bI i : QuadraticAlgebra ℚ (D : ℚ) 0), H (bI i).property⟩
  have hv₀ : v 0 = f.a • bO 0 := by
    apply Subtype.ext
    simp only [v, Submodule.coe_smul_of_tower, hbI, hbO]
    rw [coe_idealBasis_zero, QuadraticOrder.coe_basis_zero]
    simp
  have hv₁ : v 1 = (-((D + f.b) / 2)) • bO 0 + bO 1 := by
    apply Subtype.ext
    simp only [v, Submodule.coe_add, Submodule.coe_smul_of_tower, hbI, hbO]
    rw [coe_idealBasis_one, QuadraticOrder.coe_basis_zero, QuadraticOrder.coe_basis_one]
    rw [generator_eq_idealGenerator_add f D hf]
    simp only [neg_smul]
    abel
  -- The index theorem includes each ideal-basis vector in O via H. The local family v
  -- names exactly that subtype inclusion; this conversion folds v without unfolding det.
  change (bO.det v).natAbs = f.a.natAbs
  have hmat : bO.toMatrix v = !![f.a, -((D + f.b) / 2); 0, 1] := by
    ext i j
    fin_cases j <;> fin_cases i <;>
      simp [Module.Basis.toMatrix_apply, hv₀, hv₁]
  rw [Module.Basis.det_apply, hmat, Matrix.det_fin_two]
  simp

/-- The native nonsquare fractional ideal has absolute norm `|a|` in its order. -/
theorem relIndex_fractionalIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] :
    ((f.fractionalIdeal D hf :
      Submodule (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra
        (QuadraticAlgebra ℚ (D : ℚ) 0)).restrictScalars ℤ).toAddSubgroup.relIndex
      (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra.toSubmodule.toAddSubgroup =
        f.a.natAbs := by
  rw [fractionalIdeal_restrictScalars]
  have hO : (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubalgebra.toSubmodule.toAddSubgroup =
      (QuadraticOrder.toSubalgebra D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).toSubmodule.toAddSubgroup := by
    exact congrArg (fun O ↦ O.toSubmodule.toAddSubgroup)
      (QuadraticOrder.numberFieldOrder_toSubalgebra D (hf ▸ f.discrim_emod_four_eq_zero_or_one))
  rw [hO]
  exact relIndex_orderIdeal f D hf (a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out))

end TauCeti.BinaryQuadraticForm
