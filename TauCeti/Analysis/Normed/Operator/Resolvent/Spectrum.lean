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
`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic`, is closed on Banach spaces.
For bounded, everywhere-defined operators it agrees with Mathlib's Banach-algebra spectrum.
-/

public section

namespace TauCeti

open _root_.LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The spectrum of a partial linear map on a Banach space is closed. -/
theorem _root_.LinearPMap.isClosed_spectrum [CompleteSpace E] (A : E →ₗ.[𝕜] E) :
    IsClosed A.spectrum := by
  have h : A.spectrum = A.resolventSetᶜ := by
    ext z
    simp only [mem_spectrum_iff, Set.mem_compl_iff]
  rw [h]
  exact A.isOpen_resolventSet.isClosed_compl

/-- For a bounded operator on the full domain, the partial-operator spectrum agrees with
Mathlib's Banach-algebra spectrum. -/
@[simp]
theorem _root_.ContinuousLinearMap.spectrum_toPMap_top (T : E →L[𝕜] E) :
    (T.toLinearMap.toPMap ⊤).spectrum = _root_.spectrum 𝕜 T := by
  ext z
  simp only [mem_spectrum_iff, ContinuousLinearMap.mem_resolventSet_toPMap_top_iff,
    _root_.spectrum.mem_iff, _root_.spectrum.mem_resolventSet_iff]

end TauCeti
