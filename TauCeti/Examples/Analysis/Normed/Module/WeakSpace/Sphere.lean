/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakSpace.Sphere
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Checks: spheres are weakly closed in finite dimension

In finite dimension every sphere is weakly closed (`TauCeti.isClosed_toWeakSpace_setOf_norm_eq`),
unlike in infinite dimension (`TauCeti.not_isClosed_toWeakSpace_setOf_norm_eq`). The argument in
infinite dimension, `TauCeti.exists_ne_zero_forall_toWeakSpace_smul_mem_of_mem_nhds_zero`, finds
a nonzero vector in the common kernel of finitely many continuous linear functionals. The second
check records the algebraic fact that defeats this step in finite dimension: the common
kernel of the coordinate functionals of a basis is `{0}`.
-/

public section

namespace TauCeti.WeakSphereExamples

/-- The unit sphere of `ℝ²` is weakly closed. -/
example : IsClosed (toWeakSpace ℝ (EuclideanSpace ℝ (Fin 2)) ''
    {u | ‖(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) u‖ = 1}) :=
  isClosed_toWeakSpace_setOf_norm_eq _ 1

/-- The common kernel of the coordinate functionals of a basis is `{0}`. -/
example {𝕜 V ι : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V] (b : Module.Basis ι 𝕜 V)
    {u : V} (h : ∀ i, b.coord i u = 0) : u = 0 :=
  b.forall_coord_eq_zero_iff.1 h

end TauCeti.WeakSphereExamples
