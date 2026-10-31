/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# Spectrum of a partial linear map

The spectrum `LinearPMap.spectrum`, defined in
`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic`, is closed when the continuous
endomorphism algebra has summable geometric series, in particular on Banach spaces.
The comparison with Mathlib's algebraic spectrum for continuous, everywhere-defined operators
is developed in that topological module.
-/

public section

namespace TauCeti

open _root_.LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The spectrum of a partial linear map is closed when the continuous endomorphism algebra
has summable geometric series. -/
theorem _root_.LinearPMap.isClosed_spectrum [HasSummableGeomSeries (E →L[𝕜] E)] (A : E →ₗ.[𝕜] E) :
    IsClosed A.spectrum := by
  have h : A.spectrum = A.resolventSetᶜ := by
    ext z
    simp only [mem_spectrum_iff, Set.mem_compl_iff]
  rw [h]
  exact A.isOpen_resolventSet.isClosed_compl

end TauCeti
