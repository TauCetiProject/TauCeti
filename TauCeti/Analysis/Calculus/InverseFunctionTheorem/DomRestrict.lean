/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.Topology.Maps.DomRestrict

/-!
# Maps with invertible derivative on an open set are open there

Mathlib's `isOpenMap_of_hasStrictFDerivAt_equiv` says that a map with an invertible strict
derivative at every point is an open map. This file proves the local version: if `f` has an
invertible strict derivative at every point of an open set `s`, then its restriction
`s.domRestrict f` is an open map
(`TauCeti.isOpenMap_domRestrict_of_hasStrictFDerivAt_of_isInvertible`). Together with injectivity
on `s`, this is what `OpenPartialHomeomorph.ofContinuousOpenRestrict` needs to make `f` an open
partial homeomorphism with source `s`.
-/

public section

open Set Filter

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E]

/-- If a map has an invertible strict derivative at every point of an open set `s`, its restriction
to `s` is an open map. -/
theorem isOpenMap_domRestrict_of_hasStrictFDerivAt_of_isInvertible {f : E → F}
    {f' : E → E →L[𝕜] F} {s : Set E} (hs : IsOpen s) (hf : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x)
    (hinv : ∀ x ∈ s, (f' x).IsInvertible) : IsOpenMap (s.domRestrict f) := by
  refine isOpenMap_domRestrict_iff.2 fun x hx t ht ↦ ?_
  obtain ⟨e, he⟩ := hinv x hx
  have hfx := hf x hx
  rw [← he] at hfx
  rw [← hfx.map_nhds_eq_of_equiv]
  exact image_mem_map (inter_mem ht (hs.mem_nhds hx))

end TauCeti
