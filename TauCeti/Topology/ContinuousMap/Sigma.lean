/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Retracting a disjoint union onto a summand

For a point `z` of the summand `Z i` of a disjoint union `Σ j, Z j`, the continuous map
`ContinuousMap.sigmaRetraction i z` is the identity on `Z i` and sends every other summand to
`z`. It is a retraction of the inclusion `ContinuousMap.sigmaMk i`
(`ContinuousMap.sigmaRetraction_comp_sigmaMk`).

## Main definitions

* `ContinuousMap.sigmaRetraction i z`: the retraction of `Σ j, Z j` onto `Z i` collapsing the
  other summands to `z`.
-/

public section

namespace ContinuousMap

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]

open scoped Classical in
/-- The retraction of a disjoint union onto its summand `Z i`, sending every other summand to the
point `z`. -/
noncomputable def sigmaRetraction (i : ι) (z : Z i) : C((Σ j, Z j), Z i) where
  toFun p := if h : p.1 = i then h ▸ p.2 else z
  continuous_toFun := continuous_sigma fun j ↦ by
    by_cases h : j = i
    · subst h
      simpa using continuous_id'
    · simpa [h] using continuous_const

@[simp]
theorem sigmaRetraction_sigmaMk (i : ι) (z w : Z i) : sigmaRetraction i z ⟨i, w⟩ = w := by
  simp [sigmaRetraction]

@[simp]
theorem sigmaRetraction_apply_of_ne {i j : ι} (z : Z i) (w : Z j) (h : j ≠ i) :
    sigmaRetraction i z ⟨j, w⟩ = z := by
  simp [sigmaRetraction, h]

@[simp]
theorem sigmaRetraction_comp_sigmaMk (i : ι) (z : Z i) :
    (sigmaRetraction i z).comp (sigmaMk i) = ContinuousMap.id (Z i) := by
  ext w
  exact sigmaRetraction_sigmaMk i z w

end ContinuousMap
