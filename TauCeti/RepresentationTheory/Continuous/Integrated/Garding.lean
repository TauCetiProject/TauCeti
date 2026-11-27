/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Integrated.Lie.Basic
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Weighted

/-!
# Gårding smoothing

Let `π` be a strongly continuous representation of a Lie group `G` on a complex Banach space `V`
and `μ` a left-invariant measure on `G`, finite on compact sets. For a test function `a` and a
vector `v`, the vector `π(a) v = ∫ y, a y • π y v ∂μ` is smooth: by left invariance its orbit map
is `x ↦ π x (π(a) v) = ∫ y, a (x⁻¹ * y) • π y v ∂μ`, and such a weighted parametric integral is
smooth because `a` is (`ContinuousLinearMap.contMDiff_integral_comp_inv_mul`).

Along the smooth approximate identities `u_U`, `π(u_U) v → v` for a Haar measure `μ`. Hence the
smooth vectors are dense in `V`.

## Main results

* `ContRepresentation.isLieSmoothVector_lieIntegratedOperator`: `π(a) v` is a smooth vector.
* `ContRepresentation.dense_lieSmoothVectors`: the smooth vectors are dense.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TauCeti
open scoped ContDiff Manifold

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (π : ContRepresentation ℂ G V) (hπ : ∀ v, Continuous fun g ↦ π g v)

/-- **Gårding smoothing.** For a left-invariant measure, `π(a) v` is a smooth vector for every
test function `a`: its orbit map `x ↦ ∫ y, a (x⁻¹ * y) • π y v ∂μ` is smooth. -/
theorem isLieSmoothVector_lieIntegratedOperator [LocallyCompactSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [MeasurableMul G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (a : LieTestFunction I G) (v : V) :
    IsLieSmoothVector I π (lieIntegratedOperator π hπ μ a v) := by
  have hsmooth := ContinuousLinearMap.contMDiff_integral_comp_inv_mul (ν := μ) (n := ⊤)
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V) a.contMDiff a.hasCompactSupport (hπ v)
  refine (isLieSmoothVector_iff I π).2 (hsmooth.congr fun x ↦ ?_)
  rw [apply_lieIntegratedOperator, lieIntegratedOperator_apply]
  simp [LieTestFunction.leftTranslate_apply]

include hπ in
/-- **The smooth vectors are dense** in a strongly continuous representation of a Lie group on a
complex Banach space: for a Haar measure `μ`, each `v` is the limit of the smooth vectors
`π(u_U) v` along the smooth approximate identities. -/
theorem dense_lieSmoothVectors [FiniteDimensional ℝ E] :
    Dense (lieSmoothVectors I π : Set V) := fun v ↦ by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional I
  borelize G
  exact mem_closure_of_tendsto
    (tendsto_lieIntegratedOperator_smoothApproximateIdentity I hπ Measure.haar v)
    (Eventually.of_forall fun _ ↦ (mem_lieSmoothVectors I π).2
      (isLieSmoothVector_lieIntegratedOperator π hπ Measure.haar _ v))

end ContRepresentation
