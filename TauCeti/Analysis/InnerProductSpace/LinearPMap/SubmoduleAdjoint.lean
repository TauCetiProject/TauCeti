/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, and ultimately for Mathlib: additions to
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`, beside `Submodule.adjoint`.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The double adjoint of a submodule

`Submodule.adjoint` sends a submodule of `E × F` to one of `F × E`; it is the
graph-level form of the adjoint of an unbounded operator, and Mathlib's
`LinearPMap.adjoint_graph_eq_graph_adjoint` identifies `Γ(T†)` with
`Γ(T).adjoint`.

Mathlib does not record how the operation composes with itself.  That gap is
what stops the von Neumann theorem — *the adjoint of a closed densely defined
operator is again densely defined* — from being stated, because that proof needs
`g.adjoint.adjoint = g` for a closed graph.

This module supplies that composition law and the density theorem it unlocks.

## Main results

* `Submodule.le_adjoint_adjoint`: `g ≤ g.adjoint.adjoint`, for **any** submodule.
* `Submodule.adjoint_adjoint_le`: the reverse, for a **closed** `g`.
* `Submodule.adjoint_adjoint`: `g.adjoint.adjoint = g` for closed `g` — the
  involutivity that lets the adjoint theory close on itself.
* `LinearPMap.dense_adjoint_domain`: **von Neumann's theorem** — the adjoint of a
  closed densely defined operator is itself densely defined.

## The reverse inclusion

`adjoint_adjoint_le` needs `g` closed — and genuinely so: the double adjoint is
always closed, so it contains the closure of `g`, and the inclusion fails for a
non-closed `g`.  Completeness of `E` and `F` is used only to get the orthogonal
projection.

The mechanism is one separating vector.  For closed `g` and `x ∉ g`, project in
`WithLp 2 (E × F)` to get `y = (y₁, y₂)` orthogonal to `g` with `⟪y, x⟫ ≠ 0`;
then `(a, b) := (-y₂, y₁)` lies in `g.adjoint`, because
`Submodule.mem_adjoint_iff` unfolds its membership to
`∀ (c, d) ∈ g, ⟪d, -y₂⟫ - ⟪c, y₁⟫ = 0`, which is exactly `y ⟂ g` — and the
pairing that `x ∈ g.adjoint.adjoint` would force to vanish is
`⟪b, x.1⟫ - ⟪a, x.2⟫ = ⟪y₁, x.1⟫ + ⟪y₂, x.2⟫ = ⟪y, x⟫`.

## Sources

*Follows nothing in particular*: the inclusion is the standard graph-adjoint
computation, and the proof is `Submodule.mem_adjoint_iff` on both sides.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti and ultimately for
  Mathlib, beside `Submodule.adjoint`.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib.
-/

public section

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **A submodule sits inside its double adjoint.**

This inclusion is unconditional: no closedness, no completeness, and no contact
with the `WithLp 2` structure `Submodule.adjoint` is defined through.  Unfolding
`Submodule.mem_adjoint_iff` twice produces the defining relation of `g` with its
two arguments exchanged, and conjugating exchanges them back. -/
theorem le_adjoint_adjoint (g : Submodule 𝕜 (E × F)) : g ≤ g.adjoint.adjoint := by
  intro x hx
  rw [Submodule.mem_adjoint_iff]
  intro a b hab
  rw [Submodule.mem_adjoint_iff] at hab
  have h := hab x.1 x.2 (by simpa using hx)
  have h2 := congrArg (starRingEnd 𝕜) h
  simp only [map_sub, inner_conj_symm, map_zero] at h2
  exact sub_eq_zero.mpr (sub_eq_zero.mp h2).symm

/-- **The double adjoint of a closed submodule is itself.**

Closedness is necessary: `g.adjoint.adjoint` is always closed, so it contains the
closure of `g`.  Completeness enters only through the orthogonal projection used
to separate a point from `g`. -/
theorem adjoint_adjoint_le [CompleteSpace E] [CompleteSpace F] (g : Submodule 𝕜 (E × F))
    (hg : IsClosed (g : Set (E × F))) : g.adjoint.adjoint ≤ g := by
  classical
  set L := WithLp.prodContinuousLinearEquiv 2 𝕜 E F with hL
  set G : Submodule 𝕜 (WithLp 2 (E × F)) :=
    g.comap (L : WithLp 2 (E × F) →L[𝕜] E × F).toLinearMap with hG
  have hGclosed : IsClosed (G : Set (WithLp 2 (E × F))) := hg.preimage L.continuous
  have : CompleteSpace G := hGclosed.completeSpace_coe
  have : G.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace G
  intro x hx
  have hmem : (L.symm x) ∈ Gᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hab : ((-(WithLp.ofLp y).2 : F), ((WithLp.ofLp y).1 : E)) ∈ g.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro c d hcd
      have hu : (L.symm (c, d)) ∈ G := by simpa [hG, hL] using hcd
      have := hy _ hu
      rw [WithLp.prod_inner_apply] at this
      simp only [hL, WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp] at this ⊢
      simp only [inner_neg_right]
      linear_combination -this
    have hxy := (Submodule.mem_adjoint_iff _ x).mp hx _ _ hab
    rw [WithLp.prod_inner_apply]
    simp only [hL, WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.ofLp_toLp]
    simp only [inner_neg_left] at hxy
    linear_combination hxy
  rw [G.orthogonal_orthogonal] at hmem
  simpa [hG, hL] using hmem

/-- **Involutivity of the submodule adjoint on closed submodules.**

This is the graph-level statement that makes the unbounded-operator adjoint
theory close on itself: with `LinearPMap.adjoint_graph_eq_graph_adjoint` it says
`Γ(T††) = Γ(T)` for closed densely defined `T`. -/
theorem adjoint_adjoint [CompleteSpace E] [CompleteSpace F] (g : Submodule 𝕜 (E × F))
    (hg : IsClosed (g : Set (E × F))) : g.adjoint.adjoint = g :=
  le_antisymm (adjoint_adjoint_le g hg) (le_adjoint_adjoint g)

end Submodule

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **von Neumann's theorem: the adjoint of a closed densely defined operator is
densely defined.**

This is the fact that makes the unbounded adjoint theory close on itself.  Without
it, every development iterating the adjoint — `T††`, self-adjointness criteria,
the Cayley transform, unbounded spectral theory — must carry density of the
adjoint domain as a standing hypothesis.

The proof is one separating vector.  If `y ⟂ T†.domain` then `(0, y)` lies in
`Γ(T).adjoint.adjoint`, because that membership unfolds to exactly
`∀ a ∈ T†.domain, ⟪a, y⟫ = 0`.  Closedness of `Γ(T)` collapses the double
adjoint, so `(0, y) ∈ Γ(T)`, forcing `y = T 0 = 0`. -/
theorem dense_adjoint_domain {T : E →ₗ.[𝕜] E}
    (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) :
    Dense (T.adjoint.domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have hmem : ((0 : E), y) ∈ T.graph.adjoint.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hT] at hab
    simpa using hy a (LinearPMap.mem_domain_of_mem_graph hab)
  rw [Submodule.adjoint_adjoint _ hTc] at hmem
  rw [LinearPMap.mem_graph_iff] at hmem
  obtain ⟨z, hz1, hz2⟩ := hmem
  have hz0 : z = 0 := Subtype.ext hz1
  simpa [hz0] using hz2.symm

end LinearPMap
