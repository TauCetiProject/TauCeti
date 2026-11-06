/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Compact-open spaces of continuous maps are polynormable

For a normed target over an arbitrary normed field, compact restrictions induce the existing
compact-open topology. Each compact restriction is a seminormed function space, so the native
induced-topology and infimum results give polynormability without ordering the scalar field.
-/

public noncomputable section

namespace ContinuousMap

open TopologicalSpace

/-- The compact-open topology on continuous maps into a normed space is polynormable over the
same field, including unordered fields such as the complex numbers. -/
instance instPolynormableSpace {𝕜 X F : Type*} [NormedField 𝕜] [TopologicalSpace X]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : PolynormableSpace 𝕜 C(X, F) := by
  have ht : (compactOpen : TopologicalSpace C(X, F)) =
      ⨅ K : Compacts X, TopologicalSpace.induced
        (restrict (K : Set X)) compactOpen := by
    rw [compactOpen_eq_iInf_induced]
    apply le_antisymm
    · exact le_iInf fun K ↦ iInf₂_le K.1 K.2
    · exact le_iInf fun K ↦ le_iInf fun hK ↦ iInf_le _ (⟨K, hK⟩ : Compacts X)
  rw [ht]
  apply PolynormableSpace.iInf
  intro K
  exact PolynormableSpace.induced
    (compCLM 𝕜 F (⟨Subtype.val, continuous_subtype_val⟩ : C(K, X))).toLinearMap

end ContinuousMap
