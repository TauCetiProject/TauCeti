/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.ContMDiffMap.SmoothFamily

/-!
# The weak Whitney topology on global-chart diffeomorphisms

For a pair of normed spaces, `ContMDiffMap.WeakWhitney` supplies the weak Whitney topology on
global-chart `C^n` maps.  This file transports that topology to the self-diffeomorphisms of a
global-chart manifold by the canonical forgetful map
`Diffeomorph.toContMDiffMap`.

This is the chart-level topology used by the geometric-topology roadmap's Layer 3.  The manifold
topology is obtained by applying the same construction in charts; the present result isolates the
transport step and gives the continuity criterion needed for smooth families.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞ω}

local notation "𝓓" => (E ≃ₘ^n⟮modelWithCornersSelf 𝕜 E, modelWithCornersSelf 𝕜 E⟯ E)
local notation "𝓒" => C^n⟮modelWithCornersSelf 𝕜 E, E; modelWithCornersSelf 𝕜 E, E⟯

/-- The global-chart weak Whitney topology on self-diffeomorphisms.

It is the topology induced by forgetting the inverse and retaining the underlying bundled smooth
map.  The latter already carries the initial topology of all compact-open derivative projections.
-/
@[instance_reducible]
noncomputable def weakWhitneyTopology :
    TopologicalSpace 𝓓 :=
  TopologicalSpace.induced Diffeomorph.toContMDiffMap inferInstance

noncomputable instance instTopologicalSpaceWeakWhitney :
    TopologicalSpace 𝓓 :=
  weakWhitneyTopology

/-- The weak Whitney topology is induced by the forgetful map to bundled smooth maps. -/
theorem isInducing_toContMDiffMap :
    IsInducing (Diffeomorph.toContMDiffMap : 𝓓 → 𝓒) :=
  ⟨rfl⟩

/-- The forgetful map embeds diffeomorphisms into bundled smooth maps with the weak Whitney
topology. -/
theorem isEmbedding_toContMDiffMap :
    IsEmbedding (Diffeomorph.toContMDiffMap : 𝓓 → 𝓒) where
  toIsInducing := isInducing_toContMDiffMap
  injective := by
    intro f g h
    apply Diffeomorph.ext
    intro x
    exact congr_fun (congrArg (fun k : 𝓒 => fun y => k y) h) x

/-- The forgetful map to bundled smooth maps is continuous by construction. -/
theorem continuous_toContMDiffMap :
    Continuous (Diffeomorph.toContMDiffMap :
      𝓓 → 𝓒) :=
  continuous_induced_dom

/-- A map into global-chart diffeomorphisms is continuous exactly when its underlying smooth maps
are continuous in the weak Whitney topology. -/
theorem continuous_iff_toContMDiffMap {X : Type*} [TopologicalSpace X]
    {f : X → 𝓓} :
    Continuous f ↔ Continuous (fun x => (f x).toContMDiffMap) := by
  convert (continuous_induced_rng (f := Diffeomorph.toContMDiffMap) (g := f)) using 1
  · rfl

/-- A jointly smooth family whose fibres are diffeomorphisms is continuous in the weak Whitney
topology on global-chart diffeomorphisms.

The family is supplied as a map into diffeomorphisms, so the fibrewise inverse data is explicit;
the proof only needs joint smoothness of the forward map, exactly as in the chart-level smooth
family theorem.
-/
theorem continuous_of_contDiff_family {P : Type*}
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : P → 𝓓}
    (hf : ContDiff 𝕜 n (fun z : P × E => f z.1 z.2)) :
    Continuous f := by
  rw [continuous_iff_toContMDiffMap]
  exact _root_.ContDiff.continuous_weakWhitney hf

/-- Convergence of global-chart diffeomorphisms is convergence of every derivative of their
underlying maps on compact sets. -/
theorem tendsto_weakWhitney_iff {X : Type*} {l : Filter X}
    {f : X → 𝓓} {g : 𝓓} :
    Tendsto f l (nhds g) ↔
      Tendsto (fun x => (f x).toContMDiffMap) l (nhds g.toContMDiffMap) := by
  rw [isInducing_toContMDiffMap.tendsto_nhds_iff]
  rfl

end Diffeomorph
