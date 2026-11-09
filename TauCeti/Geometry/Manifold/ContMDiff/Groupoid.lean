/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
# The groupoid of `C^n` local diffeomorphisms of a manifold

For a manifold `X` modelled on `I`, the open partial homeomorphisms `e` of `X` such that `e` is
`C^n` on its source and `e.symm` is `C^n` on its target form a structure groupoid
`TauCeti.contMDiffGroupoid I n X` on `X`. It plays for a manifold the role that Mathlib's
`contDiffGroupoid` plays for a model space, with smoothness read through the charts of `X`.

Its use is to build manifolds in two stages. A space `M` charted over the manifold `X`, whose
transition maps are `C^n` local diffeomorphisms of `X`, is a `C^n` manifold modelled on `I` for
the composite charts `ChartedSpace.comp H X M`
(`TauCeti.isManifold_of_hasGroupoid_contMDiffGroupoid`). For instance, the total space of a fibre
bundle is charted over the product of its base and its fibre by its trivializations, and its smooth
atlas is obtained in this way when the fibre is itself a manifold.

## Main definitions

* `TauCeti.contMDiffPregroupoid I n X`: the maps of `X` that are `C^n` on a set.
* `TauCeti.contMDiffGroupoid I n X`: the open partial homeomorphisms of `X` that are `C^n` with
  `C^n` inverse.

## Main results

* `TauCeti.mem_contMDiffGroupoid_iff`: membership is smoothness of the map on its source and of its
  inverse on its target.
* `TauCeti.isManifold_of_hasGroupoid_contMDiffGroupoid`: a space charted over a `C^n` manifold `X`
  with transitions in `contMDiffGroupoid I n X` is a `C^n` manifold for the composite charts.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]

section Groupoid

variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (X : Type*) [TopologicalSpace X]
  [ChartedSpace H X]

/-- The pregroupoid of maps of a manifold `X` modelled on `I` that are `C^n` on a set. -/
def contMDiffPregroupoid : Pregroupoid X where
  property f u := ContMDiffOn I I n f u
  comp hf hg _ _ _ := hg.comp (hf.mono inter_subset_left) fun _ hx ↦ hx.2
  id_mem := contMDiffOn_id
  locality _ h := contMDiffOn_of_locally_contMDiffOn h
  congr _ h hf := hf.congr h

/-- The structure groupoid of `C^n` local diffeomorphisms of a manifold `X` modelled on `I`: the
open partial homeomorphisms of `X` that are `C^n` on their source, with inverse `C^n` on their
target. -/
def contMDiffGroupoid : StructureGroupoid X :=
  (contMDiffPregroupoid I n X).groupoid

variable {I n X}

@[simp]
theorem contMDiffPregroupoid_property {f : X → X} {u : Set X} :
    (contMDiffPregroupoid I n X).property f u ↔ ContMDiffOn I I n f u :=
  Iff.rfl

/-- An open partial homeomorphism of `X` is a `C^n` local diffeomorphism when it is `C^n` on its
source and its inverse is `C^n` on its target. -/
theorem mem_contMDiffGroupoid_iff {e : OpenPartialHomeomorph X X} :
    e ∈ contMDiffGroupoid I n X ↔
      ContMDiffOn I I n e e.source ∧ ContMDiffOn I I n e.symm e.target :=
  Iff.rfl

end Groupoid

variable {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} {X : Type*} [TopologicalSpace X]
  [ChartedSpace H X]

variable (I n) in
/-- A space `M` charted over a `C^n` manifold `X` modelled on `I`, whose transition maps are `C^n`
local diffeomorphisms of `X`, is a `C^n` manifold for the composite charts
`ChartedSpace.comp H X M`. -/
theorem isManifold_of_hasGroupoid_contMDiffGroupoid [IsManifold I n X] (M : Type*)
    [TopologicalSpace M] [ChartedSpace X M] [HasGroupoid M (contMDiffGroupoid I n X)] :
    letI := ChartedSpace.comp H X M
    IsManifold I n M := by
  let := ChartedSpace.comp H X M
  refine { StructureGroupoid.HasGroupoid.comp (contMDiffGroupoid I n X) fun e he ↦ ?_ with }
  rwa [isLocalStructomorphOn_contDiffGroupoid_iff]

end TauCeti
