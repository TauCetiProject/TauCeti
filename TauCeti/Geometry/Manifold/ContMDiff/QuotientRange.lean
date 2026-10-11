/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.QuotientRange
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth quotient coordinates over manifold parameters

A family of split injections parametrized by a manifold admits a fixed closed complement
near each parameter. If the family is `C^n` on an open domain, its quotient-coordinate
operators are `C^n` on a single smaller open domain, including when `n = ∞`.

These operators give fixed model fibres for normal-bundle charts: the quotient of the
ambient model space by the range of a coordinate differential is identified with the
complement by `ContinuousLinearMap.quotientRangeEquiv`. Regularity is checked on ambient
representatives, before assigning a smooth structure to the total quotient bundle.

The neighbourhood theorem uses regularity on an open domain, rather than regularity
only at its centre. This distinction matters at smooth order: smoothness at one point
does not in general give one neighbourhood on which the family is smooth.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

/- Formal sources: the quotient-coordinate calculus in `TauCeti.Analysis.Calculus.QuotientRange`
and the fixed-complement theorem `ContinuousAt.exists_isInvertible_coprod_subtypeL`. -/

public section

open Set Filter Topology
open scoped Manifold ContDiff

variable {𝕜 X E F G H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 X H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {A : M → E →L[𝕜] F} {x : M} {s : Set M} {n : ℕ∞ω}

/-- Quotient coordinates inherit the regularity of a manifold-parametrized family,
within a set, wherever the fixed complement is valid. -/
theorem ContMDiffWithinAt.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] F) n A s x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜] G) n
      (fun y => (A y).quotientRangeCoordinate B) s x :=
  (contDiffAt_id.quotientRangeCoordinate B h).contMDiffAt.comp_contMDiffWithinAt x hA

/-- Quotient-coordinate operators are `C^n` at a parameter where the fixed complement
is valid and the operator family is `C^n`. -/
theorem ContMDiffAt.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) n A x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n (fun y => (A y).quotientRangeCoordinate B) x :=
  (hA.contMDiffWithinAt.quotientRangeCoordinate B h).contMDiffAt univ_mem

/-- A fixed complement gives `C^n` quotient-coordinate operators throughout any
domain on which it is valid and the operator family is `C^n`. -/
theorem ContMDiffOn.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] F) n A s) (B : G →L[𝕜] F)
    (h : ∀ y ∈ s, ((A y).coprod B).IsInvertible) :
    ContMDiffOn I 𝓘(𝕜, F →L[𝕜] G) n (fun y => (A y).quotientRangeCoordinate B) s :=
  fun y hy => (hA y hy).quotientRangeCoordinate B (h y hy)

/-- A `C^n` operator family on an open manifold domain, split injective at one point,
admits a fixed closed complementary fibre and `C^n` quotient coordinates on one open
neighbourhood of that point. Smooth and analytic orders are included.

The complement is valid at every point of the neighbourhood, so
`ContinuousLinearMap.quotientRangeEquiv` identifies every moving quotient with this
same model fibre. Completeness is required only of the ambient model. -/
theorem ContMDiffOn.exists_contMDiffOn_quotientRangeCoordinate [CompleteSpace F]
    (hA : ContMDiffOn I 𝓘(𝕜, E →L[𝕜] F) n A s) (hs : IsOpen s) (hx : x ∈ s)
    (h : (A x).HasLeftInverse) :
    ∃ Q : Submodule 𝕜 F, IsClosed (Q : Set F) ∧
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧
        (∀ y ∈ U, ((A y).coprod Q.subtypeL).IsInvertible) ∧
        ContMDiffOn I 𝓘(𝕜, F →L[𝕜] Q) n
          (fun y => (A y).quotientRangeCoordinate Q.subtypeL) U := by
  obtain ⟨Q, hQ, V, hV, hxV, hInv⟩ :=
    (hA.continuousOn.continuousAt (hs.mem_nhds hx)).exists_isInvertible_coprod_subtypeL h
  obtain ⟨e, _⟩ := hInv x hxV
  have : CompleteSpace (E × Q) :=
    (e.isUniformEmbedding.completeSpace_congr e.surjective).mpr inferInstance
  refine ⟨Q, hQ, V ∩ s, hV.inter hs, ⟨hxV, hx⟩, inter_subset_right,
    (fun y hy => hInv y hy.1), ?_⟩
  exact (hA.mono inter_subset_right).quotientRangeCoordinate Q.subtypeL
    (fun y hy => hInv y hy.1)
