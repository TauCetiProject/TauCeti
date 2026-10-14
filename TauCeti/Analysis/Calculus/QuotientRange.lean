/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.QuotientRange
public import TauCeti.Analysis.Normed.Operator.QuotientRange
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differentiability of coordinates for quotients by varying ranges

A continuous family of split injections admits a single complementary subspace
on a neighbourhood of each parameter. In these coordinates, the quotient by the
moving range has a fixed model fibre, and its coordinate operator has the same
differentiability as the original family. Coordinate changes inherit this regularity as well.

Applied to the differential of an immersion in manifold charts, this supplies
local models for intrinsic normal fibres without choosing a Riemannian metric.
The fibre equivalence is `ContinuousLinearMap.quotientRangeEquiv`; differentiability is
expressed on ambient representatives so it does not presuppose a differentiable structure
on the total quotient bundle.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
the normal-bundle construction preceding Theorem 6.24.
-/

public section

open Set Filter Topology
open scoped ContDiff

variable {𝕜 X E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {A : X → E →L[𝕜] F} {x : X} {s : Set X} {n : ℕ∞ω}

/-- Complementary coordinate operators inherit the differentiability of a varying range
parametrization at every parameter where the fixed complement is valid. -/
theorem ContDiffWithinAt.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContDiffWithinAt 𝕜 n A s x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContDiffWithinAt 𝕜 n (fun y => (A y).quotientRangeCoordinate B) s x := by
  have hcop : ContDiffWithinAt 𝕜 n (fun y => (A y).coprod B) s x :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := 𝕜) (E := E) (F := G) (G := F)
      𝕜).contDiff.contDiffAt.comp_contDiffWithinAt x (hA.prodMk
        (contDiffWithinAt_const (c := B)))
  simpa only [ContinuousLinearMap.quotientRangeCoordinate_def, Function.comp_apply] using
    (contDiffWithinAt_const (c := ContinuousLinearMap.snd 𝕜 E G)).clm_comp
      (h.contDiffAt_map_inverse.comp_contDiffWithinAt x hcop)

/-- Complementary coordinate operators are `C^n` at valid parameters for a `C^n` family. -/
theorem ContDiffAt.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContDiffAt 𝕜 n A x) (B : G →L[𝕜] F)
    (h : ((A x).coprod B).IsInvertible) :
    ContDiffAt 𝕜 n (fun y => (A y).quotientRangeCoordinate B) x := by
  rw [← contDiffWithinAt_univ] at hA ⊢
  exact hA.quotientRangeCoordinate B h

/-- Complementary coordinates are `C^n` throughout an invertibility domain for a `C^n` family. -/
theorem ContDiffOn.quotientRangeCoordinate [CompleteSpace (E × G)]
    (hA : ContDiffOn 𝕜 n A s) (B : G →L[𝕜] F)
    (h : ∀ x ∈ s, ((A x).coprod B).IsInvertible) :
    ContDiffOn 𝕜 n (fun y => (A y).quotientRangeCoordinate B) s :=
  fun x hx => (hA x hx).quotientRangeCoordinate B (h x hx)

/-- A `C^n` family of operators which is split injective at one parameter admits `C^n`
quotient coordinates with a fixed closed model fibre near that parameter. The neighbourhood
is contained in the original open parameter domain. -/
theorem ContDiffOn.exists_contDiffOn_quotientRangeCoordinate
    [CompleteSpace F]
    (hA : ContDiffOn 𝕜 n A s) (hs : IsOpen s) (hx : x ∈ s)
    (h : (A x).HasLeftInverse) :
    ∃ Q : Submodule 𝕜 F, IsClosed (Q : Set F) ∧
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧
        (∀ y ∈ U, ((A y).coprod Q.subtypeL).IsInvertible) ∧
        ContDiffOn 𝕜 n (fun y => (A y).quotientRangeCoordinate Q.subtypeL) U := by
  obtain ⟨Q, hQ, V, hV, hxV, hInv⟩ :=
    (hA.continuousOn.continuousAt (hs.mem_nhds hx)).exists_isInvertible_coprod_subtypeL h
  obtain ⟨e, _⟩ := hInv x hxV
  have : CompleteSpace (E × Q) :=
    (e.isUniformEmbedding.completeSpace_congr e.surjective).mpr inferInstance
  refine ⟨Q, hQ, V ∩ s, hV.inter hs, ⟨hxV, hx⟩, inter_subset_right,
    (fun y hy => hInv y hy.1), ?_⟩
  exact (hA.mono inter_subset_right).quotientRangeCoordinate Q.subtypeL
    (fun y hy => hInv y hy.1)
