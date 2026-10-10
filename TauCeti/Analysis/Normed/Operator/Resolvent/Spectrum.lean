/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# Spectrum of a partial linear map

The spectrum of a partial linear map is the complement of its continuous-inverse resolvent
set. On Banach spaces it is closed. For bounded, everywhere-defined operators this spectrum
agrees with Mathlib's Banach-algebra spectrum.
-/

public section

namespace TauCeti.LinearPMap

section Topological

variable {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

/-- The spectrum of a partial linear map consists of the scalars whose shifts do not admit
continuous linear two-sided inverses. -/
def spectrum (A : E →ₗ.[𝕜] E) : Set 𝕜 := A.resolventSetᶜ

/-- Membership in the partial-operator spectrum is failure of resolvent membership. -/
@[simp]
theorem mem_spectrum_iff (A : E →ₗ.[𝕜] E) (z : 𝕜) :
    z ∈ spectrum A ↔ z ∉ A.resolventSet := (Iff.rfl)

end Topological

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The spectrum of a partial linear map on a Banach space is closed. -/
theorem isClosed_spectrum [CompleteSpace E] (A : E →ₗ.[𝕜] E) :
    IsClosed (spectrum A) := A.isOpen_resolventSet.isClosed_compl

/-- For a bounded operator on the full domain, the partial-operator spectrum agrees with
Mathlib's Banach-algebra spectrum. -/
@[simp]
theorem _root_.ContinuousLinearMap.spectrum_toPMap_top (T : E →L[𝕜] E) :
    spectrum (T.toLinearMap.toPMap ⊤) = _root_.spectrum 𝕜 T := by
  ext z
  simp only [mem_spectrum_iff, ContinuousLinearMap.mem_resolventSet_toPMap_top_iff,
    _root_.spectrum.mem_iff, _root_.spectrum.mem_resolventSet_iff]

end TauCeti.LinearPMap
