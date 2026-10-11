/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Coordinates
public import TauCeti.Analysis.Calculus.QuotientRange
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Changes of complementary normal coordinates

In tangent charts, the normal fibre of an immersion is the quotient of the ambient
model by the range of its coordinate differential. A complementary parametrization
identifies that quotient with a fixed vector space. Changing the ambient chart and
the complement gives the operator obtained by inserting the ambient tangent transition
between the complementary representative and the new quotient-coordinate operator.

These transitions are invertible on chart overlaps and inherit the differentiability
of the differential, losing one derivative from the original map. Together with
`ContinuousLinearMap.quotientRangeCoordinate_comp_cocycle`, these are the compatibility
conditions for assembling the smooth normal-bundle atlas. They require neither a metric
nor finite-dimensionality; all choices of charts and complementary parametrizations
are explicit.

Reuse Mathlib's smooth tangent-bundle transitions, the fixed-chart differential
regularity theorem, and `ContinuousLinearMap.quotientRangeCoordinate`.
References: M. Hirsch, *Differential Topology*, Chapter 4, §5 (normal bundles);
J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24
(tubular neighbourhoods).
-/

public section

open Bundle Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F Q Q' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
  [NormedAddCommGroup Q'] [NormedSpace 𝕜 Q']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

namespace TauCeti

/-- Valid complementary coordinates for the differential are related by an invertible
operator when both source and target tangent charts contain the evaluation points. -/
theorem isInvertible_normalQuotientCoordinateChange [IsManifold I 1 M] [IsManifold J 1 N]
    (f : M → N) (x₀ x₁ x : M) (B : Q →L[𝕜] F) (B' : Q' →L[𝕜] F)
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source)
    (hy₀ : f x ∈ (chartAt G (f x₀)).source)
    (hy₁ : f x ∈ (chartAt G (f x₁)).source)
    (hB : ((inTangentCoordinates I J id f (mfderiv I J f) x₀ x).coprod B).IsInvertible)
    (hB' : ((inTangentCoordinates I J id f (mfderiv I J f) x₁ x).coprod B').IsInvertible) :
    ((inTangentCoordinates I J id f (mfderiv I J f) x₁ x).quotientRangeCoordinate B' ∘L
      ((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
        (trivializationAt F (TangentSpace J) (f x₁)) (f x)).toContinuousLinearMap ∘L
      B).IsInvertible := by
  apply ContinuousLinearMap.isInvertible_quotientRangeCoordinate_comp_of_map_range_eq hB hB'
  exact ContinuousLinearMap.map_range_inCoordinates_coordChangeL (mfderiv I J f x)
    (by simpa using hx₀) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁)

end TauCeti

variable {m n : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
  {f : M → N} {s : Set M}

/-- Changes between fixed complementary normal coordinates are `C^m` on an open overlap
for a `C^n` map with `m + 1 ≤ n`. Smooth and analytic orders are included. Only the new
complement must be valid to establish regularity of the operator formula. -/
theorem ContMDiffOn.normalQuotientCoordinateChange [CompleteSpace (E × Q')]
    (hf : ContMDiffOn I J n f s) (hmn : m + 1 ≤ n) (hs : IsOpen s)
    (x₀ x₁ : M) (B : Q →L[𝕜] F) (B' : Q' →L[𝕜] F)
    (hx₁ : ∀ x ∈ s, x ∈ (chartAt H x₁).source)
    (hy₀ : ∀ x ∈ s, f x ∈ (chartAt G (f x₀)).source)
    (hy₁ : ∀ x ∈ s, f x ∈ (chartAt G (f x₁)).source)
    (hB' : ∀ x ∈ s,
      haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
      haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
      ((inTangentCoordinates I J id f (mfderiv I J f) x₁ x).coprod B').IsInvertible) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    ContMDiffOn I 𝓘(𝕜, Q →L[𝕜] Q') m
      (fun x => (inTangentCoordinates I J id f (mfderiv I J f) x₁ x).quotientRangeCoordinate B' ∘L
        ((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
          (trivializationAt F (TangentSpace J) (f x₁)) (f x)).toContinuousLinearMap ∘L B) s := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  intro x hx
  have hA := (hf.contMDiffAt (hs.mem_nhds hx)).mfderiv_inTangentCoordinates
    hmn (hx₁ x hx) (hy₁ x hx)
  have hcop : ContMDiffAt I 𝓘(𝕜, (E × Q') →L[𝕜] F) m
      (fun y => (inTangentCoordinates I J id f (mfderiv I J f) x₁ y).coprod B') x := by
    exact (ContinuousLinearMap.coprodEquivL (𝕜 := 𝕜) (E := E) (F := Q')
      (G := F) 𝕜).contDiff.contDiffAt.comp_contMDiffAt
        (hA.prodMk_space (contMDiffAt_const (c := B')))
  have hinv := (hB' x hx).contDiffAt_map_inverse.comp_contMDiffAt
    (f := fun y => (inTangentCoordinates I J id f (mfderiv I J f) x₁ y).coprod B') hcop
  have hcoord := (contMDiffAt_const (c := ContinuousLinearMap.snd 𝕜 E Q')).clm_comp hinv
  have htrans := ((hf.contMDiffAt (hs.mem_nhds hx)).of_le (le_self_add.trans hmn)).coordChangeL
    (e := trivializationAt F (TangentSpace J) (f x₀))
    (e' := trivializationAt F (TangentSpace J) (f x₁))
    (by simpa using hy₀ x hx) (by simpa using hy₁ x hx)
  simpa only [ContinuousLinearMap.quotientRangeCoordinate_def, Function.comp_apply] using
    (hcoord.clm_comp (htrans.clm_comp (contMDiffAt_const (c := B)))).contMDiffWithinAt
