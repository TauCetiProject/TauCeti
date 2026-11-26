/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuity of the compact `Spin(4)` equivalence with pairs of unit quaternions

The algebraic equivalence `TauCeti.realSpinFourEquivQuaternionUnitaryProd` of the compact Spin group
`Spin(4)` with `Sp(1) × Sp(1)` has a continuous inverse, for the subtype topology of `Spin(4)` in
its Clifford algebra and the subtype topology of the unit quaternions in `ℍ`: the Clifford value of
the inverse is a linear function of the pair of quaternions.

## Main results

* `TauCeti.continuous_realSpinFourEquivQuaternionUnitaryProd_symm`: the inverse equivalence
  `Sp(1) × Sp(1) → Spin(4)` is continuous.
-/

public section

open CliffordAlgebra
open scoped Quaternion

namespace TauCeti

/-- The inverse of the compact `Spin(4)` equivalence with pairs of unit quaternions is
continuous. -/
@[fun_prop]
theorem continuous_realSpinFourEquivQuaternionUnitaryProd_symm :
    Continuous realSpinFourEquivQuaternionUnitaryProd.symm := by
  refine continuous_induced_rng.mpr ?_
  have hlin : Continuous fun q : ℍ[ℝ] × ℍ[ℝ] ↦
      ((realCliffordFourZeroEvenEquivQuaternionProd.symm q :
        even (realCliffordForm 4 0)) : CliffordAlgebra (realCliffordForm 4 0)) :=
    ((even (realCliffordForm 4 0)).val.toLinearMap ∘ₗ
      realCliffordFourZeroEvenEquivQuaternionProd.symm.toLinearMap).continuous_of_finiteDimensional
  exact (hlin.comp ((continuous_subtypeVal.comp continuous_fst).prodMk
    (continuous_subtypeVal.comp continuous_snd))).congr fun q ↦
      (coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply q).symm

end TauCeti
