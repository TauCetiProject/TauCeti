/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AffineGrassmannian.Lattice.JetAction
import TauCeti.RingTheory.AffineGrassmannian.Lattice.Stabilizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# A lattice interval on which first-jet factorization fails

The matrix `1 + XE₁₂` has trivial first jet, but moves the diagonal lattice with exponents
`(1, -1)`. Thus first jets do not suffice for the interval between `XL₀` and `X⁻¹L₀`.
The calculation works over every nonzero commutative ring, in particular over every field.
Laurent series use Mathlib's localization algebra structure over power series.
-/

public section

open Matrix
open scoped Polynomial PowerSeries LaurentSeries

namespace TauCeti.ProjectiveLattice

variable {R : Type*} [CommRing R]

local instance : FaithfulSMul R⟦X⟧ R⸨X⸩ :=
  (faithfulSMul_iff_algebraMap_injective R⟦X⟧ R⸨X⸩).2 HahnSeries.ofPowerSeries_injective

-- The first-jet action on XL₀ ⊆ L ⊆ L₀ computes the original arc action.
example {n : Type*} [Fintype n] [DecidableEq n] (g : GL n R⟦X⟧)
    (L : powerSeriesInterval R n 0 1) :
    letI := jetMulAction R n 0 1 1 (by norm_num)
    (GeneralLinearGroup.map
      (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X]))
      g • L).val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val := by
  exact coe_jetAction_map (by norm_num) g L

-- This same action is obtained by taking the constant coefficient of the arc.
example {n : Type*} [Fintype n] [DecidableEq n] (L : powerSeriesInterval R n 0 1)
    (g : GL n R⟦X⟧) :
    GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩)
        (GeneralLinearGroup.map (PowerSeries.C : R →+* R⟦X⟧)
          (GeneralLinearGroup.map (PowerSeries.constantCoeff : R⟦X⟧ →+* R) g)) • L.val :=
  map_smul_eq_constantCoeff (by norm_num) L g

-- The first jet of this transvection is the identity, over arbitrary coefficient rings.
example : GeneralLinearGroup.map
    (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X]))
    (transvectionUnit (zero_ne_one : (0 : Fin 2) ≠ 1) (PowerSeries.X : R⟦X⟧)) = 1 := by
  rw [map_transvectionUnit]
  have hX : PowerSeries.jet R 1 PowerSeries.X = 0 :=
    PowerSeries.jet_eq_zero_iff.mpr (by simp)
  exact (congrArg (transvectionUnit (zero_ne_one : (0 : Fin 2) ≠ 1)) hX).trans
    (transvectionUnit_zero _)

variable [Nontrivial R]

-- The diagonal lattice used below belongs to the width-two interval.
example (hX : IsUnit (algebraMap R⟦X⟧ R⸨X⸩ PowerSeries.X)) :
    diagonal ![1, -1] hX ∈
      Set.Icc (diagonal (fun _ : Fin 2 ↦ 1) hX) (diagonal (fun _ : Fin 2 ↦ -1) hX) := by
  have hnu : ¬IsUnit (PowerSeries.X : R⟦X⟧) := by
    simp [PowerSeries.isUnit_iff_constantCoeff]
  constructor <;> rw [diagonal_le_diagonal_iff hnu] <;> decide

/-- The arc `1 + XE₁₂` moves the lattice of `(1, -1)`, although its first jet is the identity.
At entry `(0,1)`, preserving the lattice would require `X²` to divide `X`. -/
theorem transvection_X_smul_diagonal_ne
    (hX : IsUnit (algebraMap R⟦X⟧ R⸨X⸩ PowerSeries.X)) :
    GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩)
        (transvectionUnit (zero_ne_one : (0 : Fin 2) ≠ 1) (PowerSeries.X : R⟦X⟧)) •
      diagonal ![1, -1] hX ≠ diagonal ![1, -1] hX := by
  intro heq
  have hsub := congrArg ProjectiveLattice.toSubmodule heq
  rw [toSubmodule_GL_smul, toSubmodule_diagonal] at hsub
  have hmem := (mem_diagonalLatticeStabilizer_iff_map_eq
    (FaithfulSMul.algebraMap_injective R⟦X⟧ R⸨X⸩) hX).2 hsub
  have hdiv := (mem_diagonalLatticeSubalgebra.mp (mem_diagonalLatticeStabilizer.mp hmem)) 0 1
  norm_num [coe_transvectionUnit, Matrix.transvection] at hdiv
  have hcoeff := PowerSeries.X_pow_dvd_iff.mp hdiv 1 (by decide)
  simp at hcoeff

end TauCeti.ProjectiveLattice
