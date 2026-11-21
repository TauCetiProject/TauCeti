/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Exhaustion
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel
public import TauCeti.Geometry.Manifold.Sard.Basic
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Compact smooth neighbourhoods

Every compact subset of a finite-dimensional, sigma-compact Hausdorff smooth manifold without
boundary lies in the interior of a compact regular sublevel of a smooth proper function.
In positive dimension this sublevel has an actual manifold-with-boundary atlas, and its inclusion
is smooth with invertible derivative, including at boundary points. Thus it is a compact
codimension-zero neighbourhood, not just a compact topological neighbourhood.

`IsCompact.exists_isRegularValue_isCompact_sublevel` also allows the proper function to be
prescribed, provided it is bounded below. No Morse hypothesis is needed: Sard's theorem supplies
a regular value above the values on the compact set. The regular-sublevel atlas identifies its
boundary with the corresponding level set. These neighbourhoods can be used to localize
constructions on noncompact manifolds to compact manifolds with boundary.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 6.10 (Sard's theorem) and Proposition 5.47 (regular domains).
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace IsCompact

section RegularSublevel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {K : Set M}

/-- A compact set lies strictly below a regular value of any smooth proper real-valued
function bounded below. The closed sublevel at that value is compact. The value may also be
required to exceed any prescribed threshold `b`. -/
theorem exists_isRegularValue_isCompact_sublevel (hK : IsCompact K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) (b : ℝ) :
    ∃ c > b, TauCeti.IsRegularValue I 𝓘(ℝ) f c ∧
      K ⊆ f ⁻¹' Iio c ∧ IsCompact (f ⁻¹' Iic c) := by
  have : SigmaCompactSpace M := hp.sigmaCompactSpace
  obtain ⟨a, ha⟩ := (hK.image hf.continuous).bddAbove
  obtain ⟨c, hreg, hc⟩ := (hf.dense_isRegularValue (by simp)).exists_gt (max a b)
  obtain ⟨d, hd⟩ := hbdd
  have heq : f ⁻¹' Iic c = f ⁻¹' Icc d c := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Icc]
    exact (and_iff_right (hd (mem_range_self x))).symm
  refine ⟨c, lt_of_le_of_lt (le_max_right a b) hc, hreg, ?_, ?_⟩
  · intro x hx
    exact (ha (mem_image_of_mem f hx)).trans_lt (lt_of_le_of_lt (le_max_left a b) hc)
  · rw [heq]
    exact hp.isCompact_preimage isCompact_Icc

end RegularSublevel

section Exhaustion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] {K : Set M}

/-- Every compact subset of a sigma-compact Hausdorff smooth manifold without boundary lies
in a compact regular sublevel of a nonnegative smooth proper function. The compact subset lies
in the strict sublevel, hence in the topological interior of the closed sublevel. -/
theorem exists_contMDiffMap_regularSublevel (hK : IsCompact K) :
    ∃ (f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (c : ℝ), IsProperMap f ∧ (∀ x, 0 ≤ f x) ∧
      TauCeti.IsRegularValue I 𝓘(ℝ) f c ∧ K ⊆ f ⁻¹' Iio c ∧ IsCompact (f ⁻¹' Iic c) := by
  obtain ⟨f, hp, hnonneg⟩ := TauCeti.exists_contMDiffMap_isProperMap_nonneg (M := M) I
  obtain ⟨c, -, hreg, hKc, hc⟩ := hK.exists_isRegularValue_isCompact_sublevel f.contMDiff hp
    ⟨0, by rintro y ⟨x, rfl⟩; exact hnonneg x⟩ 0
  exact ⟨f, c, hp, hnonneg, hreg, hKc, hc⟩

end Exhaustion

section Neighborhood

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] {K : Set M}

/-- A compact subset of a positive-dimensional sigma-compact Hausdorff smooth manifold without
boundary is contained in the interior of a compact smooth manifold with boundary, realized as
a subset of the original manifold. Its inclusion has invertible derivative at every point.

The atlas is on the native half-space of the same dimension as the ambient manifold. Empty
compact sets and empty or disconnected ambient manifolds are allowed. -/
theorem exists_compact_manifoldWithBoundary (hK : IsCompact K) {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) :
    ∃ (S : Set M) (_ : ChartedSpace (EuclideanHalfSpace (n + 1)) S),
      IsCompact S ∧ K ⊆ interior S ∧ IsManifold (𝓡∂ (n + 1)) ∞ S ∧
        ContMDiff (𝓡∂ (n + 1)) I ∞ (Subtype.val : S → M) ∧
        ∀ x : S, (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : S → M) x).IsInvertible := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  obtain ⟨f, c, -, -, hreg, hKc, hc⟩ := hK.exists_contMDiffMap_regularSublevel (I := I)
  let := TauCeti.scalarRegularSublevelChartedSpace (f.contMDiff.of_le (by simp)) hreg hn
  have hM := TauCeti.isManifold_scalarRegularSublevel hreg hn (by simp : (1 : ℕ∞ω) ≤ ∞)
    f.contMDiff
  refine ⟨{x | f x ≤ c}, inferInstance, hc, ?_, hM,
    TauCeti.contMDiff_subtypeVal_scalarRegularSublevel hreg hn (by simp) f.contMDiff,
    TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularSublevel _ hreg hn⟩
  have hsub : f ⁻¹' Iio c ⊆ {x | f x ≤ c} := fun x hx ↦ mem_ofPred.2 (hx : f x < c).le
  exact hKc.trans (interior_maximal hsub (isOpen_Iio.preimage f.contMDiff.continuous))

end Neighborhood

end IsCompact
