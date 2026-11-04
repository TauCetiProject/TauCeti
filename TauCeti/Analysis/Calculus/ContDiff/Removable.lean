/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Removing exceptional points of smoothness

Suppose that near every point `z` a function `u` agrees, except possibly at `z` itself, with a
function `g_z` which is `Cⁿ` at `z`. Then `u` agrees with a globally `Cⁿ` function at every point
where `u` is continuous (`exists_contDiff_eq_of_eventuallyEq_nhdsNE`). The `Cⁿ` function takes
the value `g_z z` at `z`; the local models are compatible because punctured neighbourhoods are
nontrivial. A typical use is a function with logarithmic singularities at finitely many points,
corrected by explicit singular terms: the corrected function is `Cⁿ` off the singular points, and
near each of them it agrees off the point with a `Cⁿ` local model.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [∀ z : E, NeBot (𝓝[≠] z)] {n : WithTop ℕ∞} {u : E → F}

/-- If near every point `z` the function `u` agrees off `z` with a function `Cⁿ` at `z`, then
`u` agrees with a `Cⁿ` function at every point where `u` is continuous. -/
theorem exists_contDiff_eq_of_eventuallyEq_nhdsNE
    (hloc : ∀ z, ∃ g : E → F, ContDiffAt 𝕜 n g z ∧ u =ᶠ[𝓝[≠] z] g) :
    ∃ v : E → F, ContDiff 𝕜 n v ∧ ∀ z, ContinuousAt u z → v z = u z := by
  choose g hg hgu using hloc
  -- Near `z`, the local models `g w` at nearby points `w` all agree with `g z` at `w`.
  have key : ∀ z, (fun w ↦ g w w) =ᶠ[𝓝 z] g z := by
    intro z
    filter_upwards [((hg z).of_le (zero_le (a := n))).eventually (by simp),
      eventually_eventually_nhds.mpr (eventually_nhdsWithin_iff.mp (hgu z))] with w hw₁ hw₂
    rcases eq_or_ne w z with rfl | hwz
    · rfl
    · have hA : u =ᶠ[𝓝[≠] w] g z := nhdsWithin_le_nhds <|
        (hw₂.and (eventually_ne_nhds hwz)).mono fun w' h ↦ h.1 h.2
      exact tendsto_nhds_unique_of_eventuallyEq
        ((hg w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (hw₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ((hgu w).symm.trans hA)
  refine ⟨fun w ↦ g w w, contDiff_iff_contDiffAt.mpr fun z ↦
    (hg z).congr_of_eventuallyEq (key z), fun z hz ↦ ?_⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hg z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hz.tendsto.mono_left nhdsWithin_le_nhds) (hgu z).symm

end TauCeti
