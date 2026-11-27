/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Precomposition with a rescaling of a normed space

A map `u : V → M` from a real normed space to a manifold that is `Cⁿ` on a set `U` stays `Cⁿ`
after precomposition with the rescaling `w ↦ c + ε • w`, on the preimage of `U`
(`ContMDiffOn.comp_add_smul`).
-/

public section

open Set
open scoped Manifold

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M]

/-- A map `u` which is `Cⁿ` on `U` stays `Cⁿ` after precomposition with the rescaling
`w ↦ c + ε • w`, on the preimage of `U`. -/
theorem ContMDiffOn.comp_add_smul {n : WithTop ℕ∞} {u : V → M} {U : Set V}
    (hu : ContMDiffOn 𝓘(ℝ, V) I n u U) (c : V) (ε : ℝ) :
    ContMDiffOn 𝓘(ℝ, V) I n (fun w ↦ u (c + ε • w)) ((fun w ↦ c + ε • w) ⁻¹' U) :=
  hu.comp (contDiff_const.add (contDiff_id.const_smul ε)).contMDiff.contMDiffOn
    (mapsTo_preimage _ _)
