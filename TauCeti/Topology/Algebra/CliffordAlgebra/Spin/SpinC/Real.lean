/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic

/-!
# Compactness of `Spinᶜ(n)`

The group `Spinᶜ(n)` of the standard positive-definite form on `ℝⁿ`
(`CliffordAlgebra.realCliffordSpinCGroupZero`) is compact
(`CliffordAlgebra.instCompactSpaceRealCliffordSpinCGroupZero`), as a quotient of the compact group
`Spin(n) × U(1)` (`CliffordAlgebra.spinCGroup.compactSpace_of_posDef_or_negDef`).

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

namespace CliffordAlgebra

/-- `Spinᶜ(n)` is compact, as a quotient of `Spin(n) × U(1)`. -/
instance instCompactSpaceRealCliffordSpinCGroupZero (n : ℕ) [NeZero n] :
    CompactSpace (realCliffordSpinCGroupZero n) :=
  spinCGroup.compactSpace_of_posDef_or_negDef _ _ (.inl (TauCeti.posDef_realCliffordForm_zero n))

end CliffordAlgebra
