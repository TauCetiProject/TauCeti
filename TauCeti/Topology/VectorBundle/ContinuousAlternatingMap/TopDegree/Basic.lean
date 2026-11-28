/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Top-degree alternating forms in finite-rank vector bundles

In top degree (`Fintype.card ι = Module.finrank 𝕜 F`), pulling back any scalar-valued top-degree
continuous alternating form in a fibre of a finite-rank vector bundle along a fibre endomorphism
multiplies the form by the endomorphism's determinant
(`TauCeti.fiber_compContinuousLinearMap_eq_det_smul`).
-/

public section

open Bundle FiberBundle

namespace TauCeti

variable {𝕜 ι B F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On a finite-rank vector bundle `V` of model rank `Fintype.card ι`, pulling back any scalar
top-degree alternating form in the fibre `V x [⋀^ι]→L[𝕜] 𝕜` along a continuous linear endomorphism
`A : V x →L[𝕜] V x` multiplies the form by `A.det`. -/
theorem fiber_compContinuousLinearMap_eq_det_smul
    (h : Fintype.card ι = Module.finrank 𝕜 F) {x : B}
    (α : V x [⋀^ι]→L[𝕜] 𝕜) (A : V x →L[𝕜] V x) :
    α.compContinuousLinearMap A = A.det • α := by
  let _ : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x (mem_baseSet_trivializationAt F V x)
  exact α.compContinuousLinearMap_eq_det_smul (h.trans e.toLinearEquiv.symm.finrank_eq) A

end TauCeti
