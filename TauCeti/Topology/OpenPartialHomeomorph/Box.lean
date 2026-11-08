/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Open embeddings from open partial homeomorphisms with box target

An open partial homeomorphism `ψ : M → F × G` into a product with a seminormed real normed space
`G` whose target is a box `u ×ˢ ball 0 r` gives an open embedding of `u × G` into `M`, extending
the inverse of `ψ` on the zero slice
(`OpenPartialHomeomorph.exists_isOpenEmbedding_prod_symm_zero`). The open ball is identified with
the whole space `G` by `OpenPartialHomeomorph.univBall`.
-/

public section

open Metric Set Topology

namespace OpenPartialHomeomorph

variable {M F G : Type*} [TopologicalSpace M] [TopologicalSpace F] [SeminormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- An open partial homeomorphism whose target is a box `u ×ˢ ball 0 r` gives an open embedding of
`u × G` into the domain space, restricting to the inverse on the zero slice. -/
theorem exists_isOpenEmbedding_prod_symm_zero {ψ : OpenPartialHomeomorph M (F × G)}
    {u : Set F} {r : ℝ} (hu : IsOpen u) (hr : 0 < r) (hψt : ψ.target = u ×ˢ ball (0 : G) r) :
    ∃ σ : u × G → M, IsOpenEmbedding σ ∧ ∀ v : u, σ (v, 0) = ψ.symm ((v : F), (0 : G)) := by
  -- Read the normal factor of the box as the whole complementary model.
  set ρ := OpenPartialHomeomorph.univBall (0 : G) r with hρ
  have hρs : ρ.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hρr : range ρ = ball (0 : G) r := by
    rw [← image_univ, ← hρs, OpenPartialHomeomorph.image_source_eq_target, hρ,
      OpenPartialHomeomorph.univBall_target _ hr]
  have hρ0 : ρ 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero ..
  -- `σ` presents the source of the chart as a product.
  set j : u × G → F × G := Prod.map ((↑) : u → F) ρ with hj
  have hje : IsOpenEmbedding j :=
    hu.isOpenEmbedding_subtypeVal.prodMap (ρ.isOpenEmbedding hρs)
  have hjr : range j = ψ.target := by
    rw [hj, range_prodMap, Subtype.range_coe, hρr, hψt]
  exact ⟨ψ.symm ∘ j, ψ.symm.isOpenEmbedding_comp hje hjr.subset, fun v => by
    simp [hj, hρ0]⟩

end OpenPartialHomeomorph
