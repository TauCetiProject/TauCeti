/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Semialgebraic partial equivalences

The inverse of a semialgebraic partial equivalence is semialgebraic on its target.
Its graph is obtained by exchanging input and output coordinates; projection closure
supplies semialgebraicity of the target. In particular this applies to local inverses
without requiring a globally defined semialgebraic inverse.
-/

public section

open Set TauCeti

namespace PartialEquiv

variable {σ τ R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

/-- A semialgebraic partial equivalence with finitely many input coordinates has a
semialgebraic inverse on its target. No continuity assumption is needed. -/
theorem isSemialgebraicOn_symm [Finite σ] (e : PartialEquiv (σ → R) (τ → R))
    (he : IsSemialgebraicOn e e.source) : IsSemialgebraicOn e.symm e.target := by
  refine isSemialgebraicOn_def.mpr ⟨?_, ?_⟩
  · rw [← e.image_source_eq_target]
    exact he.isSemialgebraic_image
  · convert he.graph.preimage_comp (Sum.swap : σ ⊕ τ → τ ⊕ σ) using 1
    ext z
    rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_preimage,
      mem_preimage_sumArrowEquivProdArrow_graphOn]
    simp only [Function.comp_def, Sum.swap, Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨hz, hze⟩
      exact ⟨hze ▸ e.map_target hz, by rw [← hze, e.right_inv hz]⟩
    · rintro ⟨hz, hez⟩
      exact ⟨hez ▸ e.map_source hz, by rw [← hez, e.left_inv hz]⟩

/-- Semialgebraicity of a partial equivalence on its source is equivalent to
semialgebraicity of its inverse on its target, in finite coordinate spaces. -/
@[simp]
theorem isSemialgebraicOn_symm_iff [Finite σ] [Finite τ]
    (e : PartialEquiv (σ → R) (τ → R)) :
    IsSemialgebraicOn e.symm e.target ↔ IsSemialgebraicOn e e.source :=
  ⟨fun h ↦ e.symm.isSemialgebraicOn_symm h, e.isSemialgebraicOn_symm⟩

end PartialEquiv
