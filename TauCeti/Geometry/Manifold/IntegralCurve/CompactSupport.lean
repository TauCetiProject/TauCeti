/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
# Completeness of compactly supported vector fields

A `C¹` vector field vanishing outside a compact set on a boundaryless manifold is complete.
Each maximal integral curve stays in the compact set together with its initial point.

The ambient manifold need not be compact, and its model may be any real Banach space.
This supplies completeness for vector fields obtained by cutting off local ambient motions.
The compact set is explicit, avoiding any choice of a trivialization to define the support
of a tangent-bundle section.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 9.16.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {x : M} {K : Set M}

/-- A maximal integral curve of a `C¹` vector field vanishing off `K` stays in `K`
together with its initial point. No closedness or compactness of `K` is required. -/
theorem mapsTo_maximalIntegralCurve_insert_of_eq_zero_off
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hzero : ∀ y ∉ K, v y = 0) :
    MapsTo (maximalIntegralCurve v x) (maximalIntegralCurveInterval v x) (insert x K) := by
  intro t ht
  by_cases hK : maximalIntegralCurve v x t ∈ K
  · exact mem_insert_of_mem _ hK
  · obtain ⟨γ, a, b, hγ, hγ0, h0, ht', heq⟩ :=
      exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
    have hconst := isMIntegralCurve_const (hzero _ hK)
    have heqOn := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht' hv hγ
      (hconst.isMIntegralCurveOn (Ioo a b)) heq.symm
    exact mem_insert_iff.mpr (Or.inl ((heqOn h0).symm.trans hγ0))

/-- A `C¹` vector field on a boundaryless Banach manifold that vanishes outside a compact
set is complete. Compactness of the ambient manifold is unnecessary. -/
theorem maximalIntegralCurveInterval_eq_univ_of_isCompact_of_eq_zero_off [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hK : IsCompact K) (hzero : ∀ y ∉ K, v y = 0) :
    maximalIntegralCurveInterval v x = univ :=
  maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt) (hK.insert x)
    (mapsTo_maximalIntegralCurve_insert_of_eq_zero_off hv hzero)

end TauCeti
