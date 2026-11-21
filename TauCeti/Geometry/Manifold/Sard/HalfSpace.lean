/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sard.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Geometry.Manifold.Boundary.Charts

/-!
# Sard's theorem for manifolds with boundary

For a map from a Lindelöf manifold modelled on the Euclidean half-space, the critical values
are chartwise null, and the regular values are dense. The target may have corners and its
model may have any finite dimension. The regularity bound is the sharp Sard bound
`k > dim M - dim N`, with `k ≥ 1`; in particular smooth maps satisfy it.

The interior critical values are null by
`TauCeti.isNullSet_image_of_not_isRegularPoint_of_isInteriorPoint`. At a boundary
critical point the restriction to the boundary is also critical, because its derivative
factors through the nonsurjective ambient derivative. The boundary carries the canonical
charts of `TauCeti.boundaryChartedSpace` and is a `C^k` manifold of dimension one less by
`TauCeti.isManifold_boundary`. It is Lindelöf as a closed subspace. Applying the boundaryless
Sard theorem to this restriction and taking a union proves the result.
The converse implication on critical points is false: the identity on the half-line is
regular at its endpoint, while its restriction to that endpoint is critical.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_halfSpace`: a pointwise version for any set
  of critical points.
* `ContMDiff.isNullSet_image_criticalPoints_halfSpace`: the critical values are null.
* `ContMDiff.dense_isRegularValue_halfSpace`: the regular values are dense.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 6.10, including the reduction from manifolds with boundary to their interior and
  boundary.
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {d : ℕ} [NeZero d] {k : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
  [IsManifold (𝓡∂ d) k M] [LindelofSpace M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J k N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with boundary**, on a set of critical points. Let `M` be a
Lindelöf half-space `C^k` manifold of dimension `d` and `N` a finite-dimensional real `C^k`
manifold. If `f` is `C^k` at every point of a set `s` of critical points, then `f '' s` is null
when `k > d - dim N` and `k ≥ 1`. -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace
    (hk : ((d - finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ k)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡∂ d) J k f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡∂ d) J f x) : IsNullSet J (f '' s) := by
  rcases d with _ | d
  · exact (NeZero.ne 0 rfl).elim
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  let : IsManifold (𝓡∂ (d + 1)) 1 M :=
    .of_le (ENat.one_le_iff_ne_zero_withTop.2 hk0)
  let : IsManifold J 1 N := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hk0)
  let := isManifold_boundary (n := d) (k := k) M
  let : LindelofSpace ↥((𝓡∂ (d + 1)).boundary M) :=
    ((𝓡∂ (d + 1)).isClosed_boundary hk0).isClosedEmbedding_subtypeVal.LindelofSpace
  have hi : IsNullSet J (f '' (s ∩ (𝓡∂ (d + 1)).interior M)) :=
    isNullSet_image_of_not_isRegularPoint_of_isInteriorPoint (by simpa using hk)
      (fun x hx ↦ hf x hx.1) (fun x hx ↦ hs x hx.1) (fun _ hx ↦ hx.2)
  have hb : IsNullSet J ((f ∘ Subtype.val) ''
      {x : ↥((𝓡∂ (d + 1)).boundary M) | (x : M) ∈ s}) := by
    have hinc := (isSmoothEmbedding_subtypeVal_boundary (n := d) (k := k) M).contMDiff
    apply isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
      (f := f ∘ (Subtype.val : ↥((𝓡∂ (d + 1)).boundary M) → M))
      (le_trans (by simp only [finrank_euclideanSpace, Fintype.card_fin]; gcongr; omega) hk)
      (fun x hx ↦ (hf x hx).comp x (hinc x))
    intro x hx hreg
    apply hs x hx
    rw [isRegularPoint_iff, mfderiv_comp x ((hf x hx).mdifferentiableAt hk0)
      ((hinc x).mdifferentiableAt hk0)] at hreg
    exact isRegularPoint_iff.2 (Surjective.of_comp hreg)
  apply (hi.union hb).mono
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxi : (𝓡∂ (d + 1)).IsInteriorPoint x
  · exact Or.inl ⟨x, ⟨hx, hxi⟩, rfl⟩
  · exact Or.inr ⟨⟨x, ((𝓡∂ (d + 1)).isBoundaryPoint_iff_not_isInteriorPoint x).2 hxi⟩, hx, rfl⟩

/-- The critical values of a `C^k` map from a Lindelöf half-space `C^k` manifold of dimension
`d` to a finite-dimensional real `C^k` manifold `N` are null when `k > d - dim N` and `k ≥ 1`.
In particular, this holds for every smooth map. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace
    (hf : ContMDiff (𝓡∂ d) J k f)
    (hk : ((d - finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ k) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡∂ d) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E] [BorelSpace E] in
/-- The regular values of a `C^k` map from a Lindelöf half-space `C^k` manifold of dimension
`d` to a finite-dimensional real `C^k` manifold `N` are dense when `k > d - dim N` and `k ≥ 1`.
In particular, this holds for every smooth map. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace
    (hf : ContMDiff (𝓡∂ d) J k f)
    (hk : ((d - finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ k) :
    Dense {y | IsRegularValue (𝓡∂ d) J f y} := by
  borelize E
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace hk).dense_compl

end TauCeti
