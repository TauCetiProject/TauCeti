/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# The weak topology in finite dimension

The weak topology of a finite-dimensional normed space over `RCLike` scalars is Hausdorff, since
continuous linear functionals separate points, so `toWeakSpace` is a continuous linear
equivalence (`TauCeti.toWeakSpaceContinuousLinearEquiv`): the weak topology is the norm topology.
In particular a set is weakly closed exactly when it is closed
(`TauCeti.isClosed_toWeakSpace_image_iff`).

## Main results

* `TauCeti.toWeakSpaceContinuousLinearEquiv`: in finite dimension, `toWeakSpace` is a
  continuous linear equivalence, so the weak and norm topologies agree.
* `TauCeti.isClosed_toWeakSpace_image_iff`: in finite dimension, a set is weakly closed exactly
  when it is closed.
-/

public section

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

variable (𝕜 V) in
/-- In finite dimension, the weak topology is the norm topology: `toWeakSpace` is a continuous
linear equivalence onto `WeakSpace 𝕜 V`. -/
noncomputable def toWeakSpaceContinuousLinearEquiv : V ≃L[𝕜] WeakSpace 𝕜 V :=
  (toWeakSpace 𝕜 V).toContinuousLinearEquiv

/-- The continuous linear equivalence onto the weak space is `toWeakSpace`. -/
@[simp]
theorem coe_toWeakSpaceContinuousLinearEquiv :
    ⇑(toWeakSpaceContinuousLinearEquiv 𝕜 V) = toWeakSpace 𝕜 V := by
  simp [toWeakSpaceContinuousLinearEquiv]

/-- The inverse of the continuous linear equivalence onto the weak space is that of
`toWeakSpace`. -/
@[simp]
theorem coe_toWeakSpaceContinuousLinearEquiv_symm :
    ⇑(toWeakSpaceContinuousLinearEquiv 𝕜 V).symm = (toWeakSpace 𝕜 V).symm := by
  simp [toWeakSpaceContinuousLinearEquiv]

/-- In finite dimension, a set is weakly closed exactly when it is closed. -/
theorem isClosed_toWeakSpace_image_iff {s : Set V} :
    IsClosed (toWeakSpace 𝕜 V '' s) ↔ IsClosed s := by
  rw [← coe_toWeakSpaceContinuousLinearEquiv]
  exact (toWeakSpaceContinuousLinearEquiv 𝕜 V).toHomeomorph.isClosed_image

end TauCeti
