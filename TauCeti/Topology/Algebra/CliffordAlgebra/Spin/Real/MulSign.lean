/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.MulSign
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Euclidean

/-!
# Continuity of the multiplication by the central signs of `Spin(n)`

The multiplication `μ : Spin(n) × ℤ/2 → Spin(n)`, `(g, ε) ↦ g ε`, by the kernel `{1, -1}` of the
double cover `Spin(n) → SO(n)` (`CliffordAlgebra.realCliffordSpinMulSign`) is continuous for the
subspace topology of `Spin(n)` and the discrete topology of `ℤ/2`
(`CliffordAlgebra.continuous_realCliffordSpinMulSign`). This is what extending a principal
`(Spin(n) × ℤ/2)`-bundle along `μ` needs, as in the twist of a Spin structure by a principal
`ℤ/2`-bundle (`TauCeti.SpinStructure.twist`).

## Main results

* `CliffordAlgebra.continuous_realCliffordSpinMulSign`: the multiplication is continuous.
-/

public section

namespace CliffordAlgebra

variable (n : ℕ) [NeZero n]

/-- Multiplication by the central signs is continuous. -/
@[fun_prop]
theorem continuous_realCliffordSpinMulSign : Continuous (realCliffordSpinMulSign n) := by
  have h : Continuous fun g : realCliffordSpinGroupZero n × Multiplicative (ZMod 2) ↦
      g.1 * (realCliffordSpinDoubleCoverZero n).inl g.2 :=
    continuous_fst.mul (continuous_of_discreteTopology.comp continuous_snd)
  exact h.congr fun g ↦ (realCliffordSpinMulSign_apply n g.1 g.2).symm

end CliffordAlgebra
