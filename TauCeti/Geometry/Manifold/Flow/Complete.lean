/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.CompactSupport
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Complete vector fields

A vector field is complete when every maximal integral curve is defined for all real time.
This file expresses completeness through the joint maximal-flow domain and relates it to the
pointwise maximal intervals and to the existence of global integral curves.

Compactly supported `C¹` vector fields on boundaryless Banach manifolds are complete. In
particular, every `C¹` vector field on a compact boundaryless Banach manifold is complete. So is
every `C¹` vector field admitting a proper map that is constant along its integral curves, such
as a Hamiltonian vector field with a proper family of first integrals. These criteria make
completeness available without choosing a global flow or assuming finite dimensionality.

## Main declarations

* `TauCeti.IsCompleteVectorField`: the maximal flow is defined at every time and point, with
  eliminators `IsCompleteVectorField.flowDomain_eq_univ`, `IsCompleteVectorField.mem_flowDomain`,
  and `IsCompleteVectorField.mem_maximalIntegralCurveInterval`.
* `TauCeti.isCompleteVectorField_iff_maximalIntegralCurveInterval`: completeness in terms of
  pointwise maximal intervals.
* `TauCeti.isCompleteVectorField_iff_exists_isMIntegralCurve`: completeness in terms of global
  integral curves through every point.
* `TauCeti.isCompleteVectorField_of_exists_isMIntegralCurveOn`: the uniform-time completeness
  criterion.
* `TauCeti.isCompleteVectorField_of_isCompact_of_eq_zero_off`: compactly supported fields are
  complete.
* `TauCeti.isCompleteVectorField_of_compactSpace`: fields on compact manifolds are complete.
* `TauCeti.isCompleteVectorField_of_isProperMap`: fields whose maximal integral curves stay in
  the fibres of a proper map are complete.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.16.
* Winston Yin, `Mathlib.Geometry.Manifold.IntegralCurve.UniformTime`, whose
  `exists_isMIntegralCurve_of_isMIntegralCurveOn` supplies the uniform-time criterion.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A vector field is complete when its maximal flow is defined at every time and point. -/
def IsCompleteVectorField (v : (x : M) → TangentSpace I x) : Prop :=
  flowDomain v = univ

namespace IsCompleteVectorField

/-- The maximal-flow domain of a complete vector field is all of `ℝ × M`. This is the defining
property, named so that it can be used for rewriting. -/
theorem flowDomain_eq_univ {v : (x : M) → TangentSpace I x} (hv : IsCompleteVectorField v) :
    flowDomain v = univ :=
  hv

/-- Every time and point lie in the maximal-flow domain of a complete vector field. -/
theorem mem_flowDomain {v : (x : M) → TangentSpace I x} (hv : IsCompleteVectorField v)
    (t : ℝ) (x : M) : (t, x) ∈ flowDomain v :=
  hv.flowDomain_eq_univ ▸ mem_univ _

/-- Every time lies in each maximal interval of a complete vector field. -/
theorem mem_maximalIntegralCurveInterval {v : (x : M) → TangentSpace I x}
    (hv : IsCompleteVectorField v) (x : M) (t : ℝ) : t ∈ maximalIntegralCurveInterval v x :=
  TauCeti.mem_flowDomain.mp (hv.mem_flowDomain t x)

end IsCompleteVectorField

/-- A vector field is complete precisely when every pointwise maximal interval is all of `ℝ`. -/
theorem isCompleteVectorField_iff_maximalIntegralCurveInterval
    {v : (x : M) → TangentSpace I x} :
    IsCompleteVectorField v ↔ ∀ x, maximalIntegralCurveInterval v x = univ := by
  rw [IsCompleteVectorField, Set.eq_univ_iff_forall]
  constructor
  · intro h x
    apply Set.eq_univ_iff_forall.mpr
    intro t
    exact mem_flowDomain.mp (h (t, x))
  · intro h p
    exact mem_flowDomain.mpr (Set.eq_univ_iff_forall.mp (h p.2) p.1)

namespace IsCompleteVectorField

/-- Every pointwise maximal interval of a complete vector field is all of `ℝ`. -/
theorem maximalIntegralCurveInterval_eq_univ {v : (x : M) → TangentSpace I x}
    (hv : IsCompleteVectorField v) (x : M) :
    maximalIntegralCurveInterval v x = univ :=
  isCompleteVectorField_iff_maximalIntegralCurveInterval.mp hv x

end IsCompleteVectorField

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]

/-- A `C¹` vector field is complete precisely when a global integral curve through every point
exists. -/
theorem isCompleteVectorField_iff_exists_isMIntegralCurve
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    IsCompleteVectorField v ↔
      ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  exact forall_congr' fun x ↦ maximalIntegralCurveInterval_eq_univ_iff hv

/-- A uniform positive time of existence for local integral curves through every point makes a
`C¹` vector field complete. -/
theorem isCompleteVectorField_of_exists_isMIntegralCurveOn
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε)) :
    IsCompleteVectorField v :=
  (isCompleteVectorField_iff_exists_isMIntegralCurve hv).mpr fun x ↦
    exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε h x

namespace IsCompleteVectorField

/-- A global integral curve of a complete `C¹` vector field through a prescribed point. -/
theorem exists_isMIntegralCurve {v : (x : M) → TangentSpace I x}
    (hcomplete : IsCompleteVectorField v)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
  (isCompleteVectorField_iff_exists_isMIntegralCurve hv).mp hcomplete x

end IsCompleteVectorField

variable [CompleteSpace E]

/-- A `C¹` vector field that vanishes outside a compact set is complete. -/
theorem isCompleteVectorField_of_isCompact_of_eq_zero_off {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x ∉ K, v x = 0) :
    IsCompleteVectorField v := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  exact fun x ↦ maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt) (hK.insert x)
    (mapsTo_maximalIntegralCurve_insert_of_eq_zero_off hv hvK)

/-- Every `C¹` vector field on a compact boundaryless Banach manifold is complete. -/
theorem isCompleteVectorField_of_compactSpace [CompactSpace M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    IsCompleteVectorField v := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  exact fun _ ↦ maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt) isCompact_univ fun _ _ ↦ mem_univ _

/-- **A `C¹` vector field with a proper invariant map is complete.** If a proper map `G` is
constant along every maximal integral curve of `v`, then each maximal integral curve stays in the
compact fibre of `G` through its initial point, so it is defined for all time. No regularity of
the fibres is needed. -/
theorem isCompleteVectorField_of_isProperMap {Y : Type*} [TopologicalSpace Y]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {G : M → Y} (hG : IsProperMap G)
    (hGv : ∀ x, ∀ t ∈ maximalIntegralCurveInterval v x, G (maximalIntegralCurve v x t) = G x) :
    IsCompleteVectorField v := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  exact fun x ↦ maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv
    (zero_mem_maximalIntegralCurveInterval hv.contMDiffAt)
    (hG.isCompact_preimage isCompact_singleton) (hGv x)

end TauCeti
