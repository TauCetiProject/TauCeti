/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Euclidean
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic

/-!
# Compactness and rotations of `Spinᶜ(n)`

The group `Spinᶜ(n)` of the standard positive-definite form on `ℝⁿ`
(`CliffordAlgebra.realCliffordSpinCGroupZero`) is compact
(`CliffordAlgebra.instCompactSpaceRealCliffordSpinCGroupZero`), as a quotient of the compact group
`Spin(n) × U(1)` (`CliffordAlgebra.spinCGroup.compactSpace_of_posDef_or_negDef`).

Its rotations of `ℝⁿ`, through `Spinᶜ(n) → SO(n)`, preserve the Euclidean norm
(`TauCeti.CliffordAlgebra.norm_toLp_spinCGroup_toSpecialOrthogonal_apply`) and rotating a fixed
vector is continuous in the group element
(`TauCeti.CliffordAlgebra.continuous_spinCGroup_toSpecialOrthogonal_apply`). These are the norm and
continuity hypotheses for extending a lift of an orthonormal frame bundle to a `Spinᶜ` structure.

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

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

variable {n : ℕ} [NeZero n]

/-- **The rotations of `Spinᶜ(n)` preserve the Euclidean norm**: the norm hypothesis of
`TauCeti.OrthonormalFrameLift.extend` for the rotation homomorphism `Spinᶜ(n) → SO(n)`, used by
every extension to a `Spinᶜ` structure. -/
theorem norm_toLp_spinCGroup_toSpecialOrthogonal_apply
    (g : spinCGroup (realCliffordForm n 0)
      (QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)))
    (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
      (spinCGroup.toSpecialOrthogonal _ _) g v)‖ = ‖WithLp.toLp 2 v‖ :=
  norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n _ v

/-- **Rotating a fixed vector is continuous in the element of `Spinᶜ(n)`**: the continuity
hypothesis of `TauCeti.OrthonormalFrameLift.extend` for the rotation homomorphism
`Spinᶜ(n) → SO(n)`, used by every extension to a `Spinᶜ` structure. -/
theorem continuous_spinCGroup_toSpecialOrthogonal_apply (v : Fin n → ℝ) :
    Continuous fun g : spinCGroup (realCliffordForm n 0)
        (QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)) ↦
      (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal _ _) g v :=
  (continuous_specialOrthogonalGroup_realCliffordForm_apply n v).comp
    (spinCGroup.continuous_toSpecialOrthogonal_pi _ _)

end TauCeti.CliffordAlgebra
