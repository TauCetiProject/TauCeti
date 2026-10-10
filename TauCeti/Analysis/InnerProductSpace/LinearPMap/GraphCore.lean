/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Graph cores of a partial linear map

A *graph core* of `A` is a submodule of its domain from which every domain
vector can be reached by a sequence converging in the graph norm — that is,
converging in the ambient space with its `A`-images converging too.

The sequence formulation is deliberate: it records exactly the two convergences
the closed-graph argument consumes, without installing a second topology on the
domain subtype.

## Sources

*Follows nothing in particular*: a sequence-level formulation of graph-norm density,
chosen to avoid installing a second topology on the domain subtype.

## Provenance

* Original module: `DavisKahan/Sources/DavisKahan1970/SineTheta/CommonCore.lean`,
  where it was stated for the bundled DKPS `ClosedOperator` record, since deleted.
* Extraction class: **representation migration** onto Mathlib's `LinearPMap`,
  per the U1 lane.  Generalised on
  the way: the original was stated for an endomorphism, this is stated for
  `E →ₗ.[𝕜] F`.
* Spectra influence: none.
-/

public section

namespace TauCeti
namespace LinearPMap

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A submodule of the operator domain that is sequentially dense in the graph
norm: every domain vector is the limit of a sequence from the core whose
`A`-images also converge to its image. -/
def IsGraphCore (A : E →ₗ.[𝕜] F) (D : Submodule 𝕜 A.domain) : Prop :=
  ∀ x : A.domain, ∃ u : ℕ → D,
    Tendsto (fun n => (((u n : D) : A.domain) : E)) atTop (𝓝 (x : E)) ∧
    Tendsto (fun n => A ((u n : D) : A.domain)) atTop (𝓝 (A x))

namespace IsGraphCore

/-- The whole domain is a graph core. -/
theorem top (A : E →ₗ.[𝕜] F) : IsGraphCore A ⊤ := by
  intro x
  exact ⟨fun _ => ⟨x, Submodule.mem_top⟩, by simp, by simp⟩

/-- A graph core is ambiently dense in the operator domain. -/
theorem ambient_approximation {A : E →ₗ.[𝕜] F} {D : Submodule 𝕜 A.domain}
    (hD : IsGraphCore A D) (x : A.domain) :
    ∃ u : ℕ → D,
      Tendsto (fun n => (((u n : D) : A.domain) : E)) atTop (𝓝 (x : E)) := by
  obtain ⟨u, hu, -⟩ := hD x
  exact ⟨u, hu⟩

end IsGraphCore

/-- **Closedness in sequential form.**

If `uₙ ∈ dom A` with `uₙ → x` and `A uₙ → y`, then `x ∈ dom A` and `A x = y`.

This is the shape every closed-graph argument actually consumes, and stating it
once avoids re-deriving it from `LinearPMap.mem_graph_iff` at each use.  It is
what carries a graph-core identity from the core to the whole domain. -/
theorem _root_.LinearPMap.IsClosed.mem_domain_of_tendsto
    {A : E →ₗ.[𝕜] F} (hA : A.IsClosed)
    {u : ℕ → E} {x : E} {y : F} (hu : ∀ n, u n ∈ A.domain)
    (hlim : Tendsto u atTop (𝓝 x))
    (hAlim : Tendsto (fun n => A ⟨u n, hu n⟩) atTop (𝓝 y)) :
    ∃ h : x ∈ A.domain, A ⟨x, h⟩ = y := by
  have hmem : ∀ n, (u n, A ⟨u n, hu n⟩) ∈ (A.graph : Set (E × F)) :=
    fun n => A.mem_graph ⟨u n, hu n⟩
  have hpair : Tendsto (fun n => (u n, A ⟨u n, hu n⟩)) atTop (𝓝 (x, y)) :=
    hlim.prodMk_nhds hAlim
  have hlimmem : (x, y) ∈ (A.graph : Set (E × F)) :=
    hA.mem_of_tendsto hpair (Eventually.of_forall hmem)
  obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff A).1 hlimmem
  dsimp only at hv1 hv2
  have hxmem : x ∈ A.domain := hv1 ▸ v.property
  refine ⟨hxmem, ?_⟩
  have hveq : (⟨x, hxmem⟩ : A.domain) = v := Subtype.ext hv1.symm
  rw [hveq, hv2]

end LinearPMap
end TauCeti
