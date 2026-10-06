/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Index

/-!
# The zero Fredholm operator

This file characterizes when the zero continuous linear map is Fredholm. Its kernel is the whole
domain and its cokernel is the whole codomain, so it is Fredholm exactly when both spaces are
finite dimensional. In that case its index is `dim E - dim F`.

The result isolates the finite-dimensional block in a Fredholm decomposition: after an
invertible block is split off, a remaining zero block records precisely the kernel and cokernel.
The characterization needs only topologies on the domain and codomain, with the codomain `T1`;
neither a norm nor continuity of addition or scalar multiplication is required.

## Main declarations

* `TauCeti.isFredholm_zero_iff`: the zero operator is Fredholm exactly when its domain and
  codomain are finite dimensional.
* `ContinuousLinearMap.index_zero`: the index of the zero operator is the difference of
  the dimensions of its domain and codomain.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜]

section Topological

variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [T1Space F]

/-- The zero continuous linear map is Fredholm exactly when its domain and codomain are both
finite dimensional. -/
@[simp]
lemma isFredholm_zero_iff :
    ContinuousLinearMap.IsFredholm (0 : E →L[𝕜] F) ↔
      FiniteDimensional 𝕜 E ∧ FiniteDimensional 𝕜 F := by
  constructor
  · intro h
    constructor
    · simpa only [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero,
        ← Submodule.fg_iff_finiteDimensional, ← Module.finite_def] using h.finite_ker
    · simpa only [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero,
        Module.Finite.iff_cofg_bot] using h.finite_coker
  · rintro ⟨hE, hF⟩
    let := hE
    let := hF
    exact
      { isStrictMap := isClosedMap_const.isStrictMap continuous_const
        isClosed_range := by simp
        finite_ker := inferInstance
        finite_coker := inferInstance
        closedComplemented_ker := by simp }

end Topological

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The index of the zero continuous linear map is the dimension of its domain minus the
dimension of its codomain. -/
@[simp]
lemma _root_.ContinuousLinearMap.index_zero :
    ContinuousLinearMap.index (0 : E →L[𝕜] F) = (finrank 𝕜 E : ℤ) - finrank 𝕜 F := by
  simpa only [ContinuousLinearMap.index_def, ContinuousLinearMap.toLinearMap_zero] using
    (LinearMap.index_zero (R := 𝕜) (M := E) (N := F))

end TauCeti

end
