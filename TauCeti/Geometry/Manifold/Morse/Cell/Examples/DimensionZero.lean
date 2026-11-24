/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.HandlePushout
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.Topology.Category.TopCat.Limits.Products
import TauCeti.AlgebraicTopology.Disk

/-!
# Handle attachment in dimension zero

Milnor's handle attachment theorem in pushout form
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches, across a critical level `c`, one
handle `𝔻 λ × 𝔻 (m - λ)` along its attaching region `∂𝔻 λ × 𝔻 (m - λ)` for each critical point of
index `λ` on the level, in dimension `m`. This file reads off what it says in dimension `0`, where
every case of the theorem is degenerate at once.

On a manifold modelled on a zero-dimensional space every function is a Morse function
(`TauCeti.isMorse_of_subsingleton`), every point is a critical point of index `0`, each handle
`𝔻 0 × 𝔻 0` is a point and each attaching region `∂𝔻 0 × 𝔻 0` is empty. So the pushout attaches
nothing to the lower sublevel: it is the disjoint union of the lower sublevel and one point for each
critical point on the level. Hence `M_{c+ε} = {f ≤ c + ε}` is homeomorphic to `M_{c-ε}` with the
points of the level `c` added as isolated points
(`TauCeti.exists_homeomorph_sublevel_sum_of_subsingleton`). The statement is derived from the
handle attachment theorem, not built by hand, and tests that its conventions (the empty unit sphere
`∂𝔻 0`, the one-point disc `𝔻 0`, the coindex `m - λ` in `ℕ`) behave as they should in this edge
case.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorem 3.2 and Remark 3.3.
-/

public section

open Set CategoryTheory Limits Topology Module
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [Subsingleton E]

/-- **Handle attachment in dimension zero.** Let `M` be a manifold modelled on a zero-dimensional
space, `f : M → ℝ` any function and `c` a value whose band `f⁻¹[c - δ, c + δ]` is compact for some
`δ > 0`. Then for some width `0 < ε ≤ δ`, the sublevel `{f ≤ c + ε}` is homeomorphic to the
disjoint union of `{f ≤ c - ε}` and the set of critical points of `f` on the level `c`: crossing
the level adds those points as isolated points. In dimension `0` every point is critical, so these
are all the points of the level. This is the handle attachment theorem
`TauCeti.IsMorse.exists_isPushout_sublevel_handles` in dimension `0`, where every handle is a point
and every attaching region is empty. -/
theorem exists_homeomorph_sublevel_sum_of_subsingleton (f : M → ℝ) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ Nonempty ({x | f x ≤ c + ε} ≃ₜ
      {x | f x ≤ c - ε} ⊕ ↥(criticalPoints I f ∩ f ⁻¹' {c})) := by
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := ChartedSpace.discreteTopology H M
  have : I.Boundaryless := ⟨eq_univ_of_forall fun x ↦ ⟨I.symm x, Subsingleton.elim _ _⟩⟩
  have : IsManifold I ∞ M := isManifold_of_contDiffOn I ∞ M fun _ _ _ _ ↦ contDiffOn_of_subsingleton
  obtain ⟨ε, hε, hεδ, α, χ, j, hpush, -⟩ :=
    (isMorse_of_subsingleton (I := I) (f := f)).exists_isPushout_sublevel_handles hδ hcompact
  refine ⟨ε, hε, hεδ, ⟨?_⟩⟩
  -- Every critical point has index `0`, and the dimension is `0`.
  have hk : ∀ p, manifoldMorseIndex I f p = 0 := fun _ ↦ manifoldMorseIndex_eq_zero_of_subsingleton
  have hl : ∀ p, finrank ℝ E - manifoldMorseIndex I f p = 0 := fun _ ↦ by
    simp [finrank_zero_of_subsingleton]
  have hD₀ : ∀ {k : ℕ}, k = 0 → Unique (TopCat.disk.{u} k) := by rintro _ rfl; infer_instance
  have hS₀ : ∀ {k : ℕ}, k = 0 → IsEmpty (TopCat.diskBoundary.{u} k) := by
    rintro _ rfl; infer_instance
  -- Every attaching region `∂𝔻 0 × 𝔻 0` is empty, so their coproduct is initial.
  have hinit : IsInitial (∐ fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
      TopCat.of (TopCat.diskBoundary.{u} (manifoldMorseIndex I f p) ×
        TopCat.disk.{u} (finrank ℝ E - manifoldMorseIndex I f p))) := by
    have hX : IsEmpty ((∐ fun p : ↥(criticalPoints I f ∩ f ⁻¹' {c}) ↦
        TopCat.of (TopCat.diskBoundary.{u} (manifoldMorseIndex I f p) ×
          TopCat.disk.{u} (finrank ℝ E - manifoldMorseIndex I f p)) : TopCat.{u})) := by
      refine ⟨fun x ↦ ?_⟩
      obtain ⟨p, y, -⟩ := (TopCat.sigmaIsoSigma _).hom x
      exact (hS₀ (hk p)).false y
    exact TopCat.isInitialPEmpty.ofIso (TopCat.isoOfHomeo Homeomorph.empty)
  -- So the pushout is the coproduct of the lower sublevel and the handles `𝔻 0 × 𝔻 0`, which are
  -- points, one for each critical point on the level.
  have hc := isCoproductOfIsInitialIsPushout _ _ _ _ hinit hpush.isColimit
  refine (TopCat.homeoOfIso (hc.coconePointUniqueUpToIso
    (TopCat.binaryCofanIsColimit _ _))).trans (Homeomorph.sumCongr (.refl _) ?_)
  have : ∀ p : ↥(criticalPoints I f ∩ f ⁻¹' {c}), Unique
      (TopCat.disk.{u} (manifoldMorseIndex I f p) ×
        TopCat.disk.{u} (finrank ℝ E - manifoldMorseIndex I f p)) := fun p ↦
    have := hD₀ (hk p)
    have := hD₀ (hl p)
    uniqueOfSubsingleton (default, default)
  exact (TopCat.homeoOfIso (TopCat.sigmaIsoSigma _)).trans
    { Equiv.sigmaUnique _ _ with
      continuous_toFun := continuous_sigma fun _ ↦ continuous_const
      continuous_invFun := continuous_of_discreteTopology }

end TauCeti
