/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.LocallyProConstructible
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.InductiveDimension.Classes

/-!
# Checks for locally pro-constructible images

Every subset of discrete `ℕ` is locally pro-constructible, without being compact in general.
The inclusion into its one-point compactification is locally spectral but its image is not
locally pro-constructible: quasi-compactness in the image theorem cannot be dropped.

The final check applies the closed-map criterion to a map with infinite noncompact domain.
-/

open Set Topology

namespace TauCeti

/-- All subsets of discrete `ℕ`, including infinite ones, are locally pro-constructible. -/
example (s : Set ℕ) : IsLocallyProConstructible s :=
  (isClosed_discrete s).isLocallyProConstructible

/-- The image theorem applies to the identity even on a noncompact space. -/
example (s : Set ℕ) : IsLocallyProConstructible (id '' s) := by
  have hN : IsLocallySpectralSpace ℕ := isLocallySpectralSpace_iff.mpr fun n ↦
    ⟨{n}, isOpen_discrete _, rfl, {}⟩
  exact (isClosed_discrete s).isLocallyProConstructible.image hN
    isLocallySpectralMap_id isSpectralMap_id

/-- Quasi-compactness is essential: the open inclusion of discrete `ℕ` into its one-point
compactification has image that is not locally pro-constructible. -/
example : IsLocallySpectralMap ((↑) : ℕ → OnePoint ℕ) ∧
    ¬ IsLocallyProConstructible (((↑) : ℕ → OnePoint ℕ) '' univ) := by
  have : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  refine ⟨.of_forall_exists fun n ↦ ⟨{n}, {(n : OnePoint ℕ)}, mapsTo_singleton.mpr rfl,
    isOpen_discrete _, ?_, rfl, inferInstance, continuous_of_discreteTopology,
    fun _ _ _ ↦ (toFinite _).isCompact⟩, fun h ↦ ?_⟩
  · rw [← image_singleton]
    exact OnePoint.isOpen_image_coe.mpr (isOpen_discrete _)
  · have hc := (isLocallyProConstructible_iff_isProConstructible.mp h).isCompact
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff.symm,
      isCompact_iff_finite] at hc
    exact infinite_univ hc

/-- The criterion for closed maps works on a noncompact source: the identity of discrete `ℕ`
is both quasi-compact and specializing. -/
example : IsClosedMap (id : ℕ → ℕ) := by
  have hN : IsLocallySpectralSpace ℕ := isLocallySpectralSpace_iff.mpr fun n ↦
    ⟨{n}, isOpen_discrete _, rfl, {}⟩
  exact (isLocallySpectralMap_id.isClosedMap_iff_specializingMap hN hN
    isSpectralMap_id).mpr IsClosedMap.id.specializingMap

end TauCeti
