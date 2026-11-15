/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Involution

/-!
# Involutions and Fredholm operators

Let `σ_X`, `σ_Y` be continuous linear involutions anticommuted by continuous linear maps `J_X`,
`J_Y` with `J² = -1`, and let `T : X →L Y` commute with both `σ` and `J`. By
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Involution`, splitting into
`±1`-eigenspaces conjugates `T` to the product of its two restrictions, `J` conjugates these
restrictions to each other, and the kernel, cokernel and index of `T` are twice those of its
restriction to the `1`-eigenspaces. This file adds that `T` is Fredholm exactly when that
restriction is, so that the doubling formula
`ContinuousLinearMap.index_eq_two_mul_index_restrictEigenspace` is a statement about Fredholm
indices.

This is the abstract form of the doubling step for real Cauchy–Riemann operators with totally real
boundary conditions, McDuff–Salamon, *J-holomorphic Curves and Symplectic Topology*, proof of
Theorem C.1.10.

## Main declarations

* `ContinuousLinearMap.isFredholm_iff_isFredholm_restrictEigenspace`: Fredholmness is detected on
  the `1`-eigenspaces.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [NeZero (2 : 𝕜)]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
variable [ContinuousConstSMul 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
variable [ContinuousConstSMul 𝕜 Y]
variable {σX JX : X →L[𝕜] X} {σY JY : Y →L[𝕜] Y}

/-- An operator commuting with the involutions `σ` and the anticommuting maps `J` is Fredholm if
and only if its restriction to the `1`-eigenspaces is. -/
theorem isFredholm_iff_isFredholm_restrictEigenspace (T : X →L[𝕜] Y)
    (hσX : Function.Involutive σX) (hσY : Function.Involutive σY)
    (hJX : JX.comp JX = -ContinuousLinearMap.id 𝕜 X) (hJσX : σX.comp JX = -JX.comp σX)
    (hJY : JY.comp JY = -ContinuousLinearMap.id 𝕜 Y) (hJσY : σY.comp JY = -JY.comp σY)
    (hT : T.comp σX = σY.comp T) (hTJ : T.comp JX = JY.comp T) :
    IsFredholm T ↔ IsFredholm (T.restrictEigenspace hT 1) := by
  have hconj := equivEigenspaceProd_comp T hσX hσY hT
  have hswap := restrictEigenspace_comp_eigenspaceNegEquiv T hJX hJσX hJY hJσY hT hTJ 1
  rw [isFredholm_iff_of_comp_eq _ _ hconj, isFredholm_prodMap_iff,
    ← isFredholm_iff_of_comp_eq _ _ hswap.symm, and_self]

end ContinuousLinearMap
