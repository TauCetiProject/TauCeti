/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.HandlePushout
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.AlgebraicTopology.Disk
import TauCeti.Geometry.Manifold.ModelWithCorners.Boundaryless

/-!
# Deformation and handle attachment in dimension zero

Milnor's handle attachment theorem in pushout form
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches, across a critical level `c`, one
handle `𝔻 λ × 𝔻 (m - λ)` along its attaching region `∂𝔻 λ × 𝔻 (m - λ)` for each critical point of
index `λ` on the level, in dimension `m`. This file reads off what it says in dimension `0`, where
every case of the theorem is degenerate at once.

On a manifold modelled on a zero-dimensional space every function is a Morse function
(`TauCeti.isMorse_of_subsingleton`), every point is a critical point of index `0`, each handle
`𝔻 0 × 𝔻 0` is a point and each attaching region `∂𝔻 0 × 𝔻 0` is empty. Handles of index `0` glue
nothing and add one disc `𝔻 m` each
(`TauCeti.IsMorse.exists_homeomorph_sublevel_sum_of_manifoldMorseIndex_eq_zero`), here the point
`𝔻 0`. Hence `M_{c+ε} = {f ≤ c + ε}` is homeomorphic to `M_{c-ε}` with the points of the level `c`
added as isolated points (`TauCeti.exists_homeomorph_sublevel_sum_of_subsingleton`). The statement
is derived from the handle attachment theorem, not built by hand, and tests that its conventions
(the empty unit sphere `∂𝔻 0`, the one-point disc `𝔻 0`, the coindex `m - λ` in `ℕ`) behave as they
should in this edge case.

Since every point is critical, a band `f⁻¹[a, b]` without critical points is empty in dimension
`0`, and the deformation across such a band (`TauCeti.exists_sublevelDeformation`) has nothing to
move: the two sublevels `{f ≤ a}` and `{f ≤ b}` are the same set, and the inclusion of one into the
other is a homeomorphism. This is recorded below as an example.

The deformation across a band without critical points is degenerate there too: every point being
critical, such a band `f⁻¹[a, b]` is empty
(`TauCeti.preimage_Icc_eq_empty_of_subsingleton`), so the sublevels `{f ≤ a}` and `{f ≤ b}` have the
same points and the inclusion of the first into the second is onto
(`TauCeti.surjective_sublevelInclusion_of_subsingleton`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorem 3.2 and Remark 3.3.
-/

public section

open Set Topology Module
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [Subsingleton E]

/-- **A band without critical points is empty in dimension zero.** On a manifold modelled on a
zero-dimensional space every point is critical, so a band `f⁻¹[a, b]` containing no critical point
is empty. -/
theorem preimage_Icc_eq_empty_of_subsingleton (f : M → ℝ) {a b : ℝ}
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) : f ⁻¹' Icc a b = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ hreg x hx.1 hx.2 <|
    mem_criticalPoints_iff_mfderiv_eq_zero.1 (by simp)

/-- **The sublevels across a band without critical points agree in dimension zero.** On a manifold
modelled on a zero-dimensional space, if the band `f⁻¹[a, b]` contains no critical point, then it is
empty, and the inclusion of `{f ≤ a}` into `{f ≤ b}` is onto. -/
theorem surjective_sublevelInclusion_of_subsingleton (f : M → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    Function.Surjective (sublevelInclusion f a b hab) := by
  rw [← range_eq_univ, range_sublevelInclusion]
  refine eq_univ_of_forall fun x ↦ not_lt.1 fun hx ↦ ?_
  have h := preimage_Icc_eq_empty_of_subsingleton f hreg
  exact h.subset ⟨hx.le, x.property⟩

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
  have : IsManifold I ∞ M := isManifold_of_contDiffOn I ∞ M fun _ _ _ _ ↦ contDiffOn_of_subsingleton
  -- Every critical point has index `0`, so each handle adds a disc `𝔻 m`, here the point `𝔻 0`.
  obtain ⟨ε, hε, hεδ, ⟨e⟩⟩ :=
    IsMorse.exists_homeomorph_sublevel_sum_of_manifoldMorseIndex_eq_zero
      (isMorse_of_subsingleton (I := I) (f := f)) hδ hcompact
      fun _ _ ↦ manifoldMorseIndex_eq_zero_of_subsingleton
  have : Unique (TopCat.disk.{u} (finrank ℝ E)) := by
    rw [finrank_zero_of_subsingleton]; infer_instance
  exact ⟨ε, hε, hεδ, ⟨e.trans (Homeomorph.sumCongr (.refl _) (Homeomorph.prodUnique _ _))⟩⟩

/-- **A band without critical points in dimension zero.** In dimension `0` every point is critical
(`TauCeti.criticalPoints_eq_univ_of_subsingleton`), so a band `f⁻¹[a, b]` without critical points
is empty, the sublevels `{f ≤ a}` and `{f ≤ b}` are equal, and the inclusion of one into the other
is a homeomorphism. -/
example (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b = ∅) :
    f ⁻¹' Icc a b = ∅ ∧ {x | f x ≤ b} = {x | f x ≤ a} ∧
      IsHomeomorph (sublevelInclusion f a b hab) := by
  rw [criticalPoints_eq_univ_of_subsingleton, univ_inter] at hcrit
  have hsub : {x | f x ≤ b} = {x | f x ≤ a} :=
    Subset.antisymm (fun x hx ↦ not_lt.1 fun hax ↦ hcrit.subset ⟨hax.le, hx⟩)
      (sublevel_mono f hab)
  refine ⟨hcrit, hsub, isHomeomorph_iff_isEmbedding_surjective.2 ⟨?_, fun y ↦
    ⟨⟨y, hsub ▸ y.property⟩, Subtype.ext (coe_sublevelInclusion_apply f hab _)⟩⟩⟩
  rw [sublevelInclusion_eq_inclusion]
  exact IsEmbedding.inclusion (sublevel_mono f hab)

end TauCeti
