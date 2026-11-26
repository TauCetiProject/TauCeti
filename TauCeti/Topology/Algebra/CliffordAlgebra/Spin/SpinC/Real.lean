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
# Compactness of `Spinᶜ(n)` and its rotations of `ℝⁿ`

The group `Spinᶜ(n)` of the standard positive-definite form on `ℝⁿ`
(`CliffordAlgebra.realCliffordSpinCGroupZero`) is compact
(`CliffordAlgebra.instCompactSpaceRealCliffordSpinCGroupZero`), as a quotient of the compact group
`Spin(n) × U(1)` (`CliffordAlgebra.spinCGroup.compactSpace_of_posDef_or_negDef`).

Its rotation homomorphism `[s, z] ↦ π(s)` (`CliffordAlgebra.spinCGroup.toSpecialOrthogonal`)
preserves the Euclidean norm of `ℝⁿ`
(`CliffordAlgebra.spinCGroup.norm_toLp_toSpecialOrthogonal_apply`), and rotating a fixed vector is
continuous in the group element (`CliffordAlgebra.spinCGroup.continuous_toSpecialOrthogonal_apply`).
These are the norm and continuity hypotheses of `TauCeti.OrthonormalFrameLift.extend` for
extensions of structure group to `Spinᶜ(n)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

namespace CliffordAlgebra

/-- `Spinᶜ(n)` is compact, as a quotient of `Spin(n) × U(1)`. -/
instance instCompactSpaceRealCliffordSpinCGroupZero (n : ℕ) [NeZero n] :
    CompactSpace (realCliffordSpinCGroupZero n) :=
  spinCGroup.compactSpace_of_posDef_or_negDef _ _ (.inl (TauCeti.posDef_realCliffordForm_zero n))

namespace spinCGroup

variable {n : ℕ} [NeZero n]

/-- The rotations of `Spinᶜ(n)` preserve the Euclidean norm of `ℝⁿ`. -/
theorem norm_toLp_toSpecialOrthogonal_apply (h : realCliffordSpinCGroupZero n) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((toSpecialOrthogonal (TauCeti.realCliffordForm n 0) _ h :
      (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v)‖ = ‖WithLp.toLp 2 v‖ :=
  TauCeti.CliffordAlgebra.norm_toLp_specialOrthogonalGroup_realCliffordForm_apply n _ v

/-- Rotating a fixed vector of `ℝⁿ` by an element of `Spinᶜ(n)` is continuous in the element. -/
@[fun_prop]
theorem continuous_toSpecialOrthogonal_apply (v : Fin n → ℝ) :
    Continuous fun h : realCliffordSpinCGroupZero n ↦
      (toSpecialOrthogonal (TauCeti.realCliffordForm n 0) _ h :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v :=
  (TauCeti.CliffordAlgebra.continuous_specialOrthogonalGroup_realCliffordForm_apply n v).comp
    (continuous_toSpecialOrthogonal_pi _ _)

end spinCGroup

end CliffordAlgebra
