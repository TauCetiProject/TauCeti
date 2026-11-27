/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.RegularValue
public import TauCeti.Geometry.Manifold.Riemannian.InwardUnitNormal
public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Basic

/-!
# The gradient represents the co-orientation of regular faces

Let `f : N → ℝ` be a `C¹` function on a boundaryless manifold `N` modelled on a real space `E` of
dimension `n + 1`, and fix a Riemannian metric on `N`. At a regular value `a`, the sublevel
`{f ≤ a}` is a manifold with boundary the level `f⁻¹(a)`, and between regular values `a < b` the
band `f⁻¹([a, b])` is one with boundary the two levels `f⁻¹(a)` and `f⁻¹(b)`
(`TauCeti.scalarRegularSublevelChartedSpace`, `TauCeti.scalarRegularBandChartedSpace`). Which
tangent vectors along these faces point outward depends on `f` alone: those on which `df` is
positive on `{f ≤ a}` and on the upper face of the band, and those on which it is negative on the
lower face (`TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mfderiv`,
`TauCeti.isOutwardPointing_scalarRegularBand_iff_mfderiv_of_eq_left`,
`TauCeti.isOutwardPointing_scalarRegularBand_iff_mfderiv_of_eq_right`).

This file shows that once a metric is chosen, `± grad f` represent these co-orientations. At a
point of a regular level, `df(grad f) = |grad f|² > 0`. So a tangent vector of `{f ≤ a}` that the
inclusion `j` carries to `grad f` points outward
(`TauCeti.isOutwardPointing_scalarRegularSublevel_of_mfderiv_eq_mgradient`). On a band the same
holds for `grad f` at the upper face
(`TauCeti.isOutwardPointing_scalarRegularBand_of_mfderiv_eq_mgradient`) and for `-grad f` at the
lower face (`TauCeti.isOutwardPointing_scalarRegularBand_of_mfderiv_eq_neg_mgradient`). Since `dj`
is invertible at every point, boundary points included
(`TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularSublevel`,
`TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularBand`), such tangent vectors exist and are
unique.

For a smooth `f` and a smooth metric, the sublevel carries the pulled-back metric
`TauCeti.scalarRegularSublevelMetric`, and its outward unit normal `TauCeti.outwardUnitNormal` is
the unit gradient of `f`: `dj (ν_out q) = grad f / |grad f|` at every boundary point `q`
(`TauCeti.mfderiv_subtypeVal_outwardUnitNormal_scalarRegularSublevel`). Indeed `f ∘ j` has a
maximum at `q`, so its gradient for the pulled-back metric is a nonnegative multiple of `ν_out q`.
The differential `dj` carries that gradient to `grad f`, which is nonzero since `a` is regular, and
`dj` preserves lengths.

## Main results

* `TauCeti.isOutwardPointing_scalarRegularSublevel_of_mfderiv_eq_mgradient`: `grad f` points out
  of `{f ≤ a}`.
* `TauCeti.isOutwardPointing_scalarRegularBand_of_mfderiv_eq_mgradient`: `grad f` points out of
  `f⁻¹([a, b])` at the upper level.
* `TauCeti.isOutwardPointing_scalarRegularBand_of_mfderiv_eq_neg_mgradient`: `-grad f` points out
  of `f⁻¹([a, b])` at the lower level.
* `TauCeti.mfderiv_subtypeVal_outwardUnitNormal_scalarRegularSublevel`: the outward unit normal of
  `{f ≤ a}` for the pulled-back metric is `grad f / |grad f|`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 5 (regular sublevel sets are regular domains, Proposition 5.47).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
  Springer, 2018, Chapter 2 (the outward unit normal along the boundary).
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {n : ℕ} {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H N] {f : N → ℝ} {a b : ℝ}

section Gradient

variable [IsManifold I 1 N] [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  (hf : ContMDiff I 𝓘(ℝ) 1 f) (hn : finrank ℝ E = n + 1)

/-- **The gradient points out of a regular sublevel.** At a point `x` of the regular level
`f⁻¹(a)`, a tangent vector `v` of the sublevel `{f ≤ a}` that the differential of the inclusion
carries to `grad f` points outward. -/
theorem isOutwardPointing_scalarRegularSublevel_of_mfderiv_eq_mgradient
    (hreg : IsRegularValue I 𝓘(ℝ) f a) {x : {x | f x ≤ a}} (hx : f x = a)
    {v : letI := scalarRegularSublevelChartedSpace hf hreg hn; TangentSpace (𝓡∂ (n + 1)) x}
    (hv : letI := scalarRegularSublevelChartedSpace hf hreg hn
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) x v =
        Manifold.mgradient I f (x : N)) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    IsOutwardPointing x v := by
  rw [isOutwardPointing_scalarRegularSublevel_iff_mfderiv hf hn hreg hx v, hv]
  exact (hreg.isRegularPoint hx).mvfderiv_apply_mgradient_pos

section Band

variable (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- **The gradient points out of a regular band at its upper level.** At a point `x` of the upper
level `f⁻¹(b)` of a band `f⁻¹([a, b])` between regular values, a tangent vector `v` of the band that
the differential of the inclusion carries to `grad f` points outward. -/
theorem isOutwardPointing_scalarRegularBand_of_mfderiv_eq_mgradient {x : f ⁻¹' Icc a b}
    (hx : f x = b)
    {v : letI := scalarRegularBandChartedSpace hf hn ha hb hab; TangentSpace (𝓡∂ (n + 1)) x}
    (hv : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : f ⁻¹' Icc a b → N) x v =
        Manifold.mgradient I f (x : N)) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    IsOutwardPointing x v := by
  rw [isOutwardPointing_scalarRegularBand_iff_mfderiv_of_eq_right hf hn ha hb hab hx v, hv]
  exact (hb.isRegularPoint hx).mvfderiv_apply_mgradient_pos

/-- **The negative gradient points out of a regular band at its lower level.** At a point `x` of
the lower level `f⁻¹(a)` of a band `f⁻¹([a, b])` between regular values, a tangent vector `v` of the
band that the differential of the inclusion carries to `-grad f` points outward. -/
theorem isOutwardPointing_scalarRegularBand_of_mfderiv_eq_neg_mgradient {x : f ⁻¹' Icc a b}
    (hx : f x = a)
    {v : letI := scalarRegularBandChartedSpace hf hn ha hb hab; TangentSpace (𝓡∂ (n + 1)) x}
    (hv : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : f ⁻¹' Icc a b → N) x v =
        -Manifold.mgradient I f (x : N)) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    IsOutwardPointing x v := by
  rw [isOutwardPointing_scalarRegularBand_iff_mfderiv_of_eq_left hf hn ha hb hab hx v, hv, map_neg,
    neg_lt_zero]
  exact (ha.isRegularPoint hx).mvfderiv_apply_mgradient_pos

end Band

end Gradient

section UnitNormal

variable [IsManifold I ∞ N] [RiemannianBundle (fun y : N ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun y : N ↦ TangentSpace I y)]
  (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1)

/-- **The outward unit normal of a regular sublevel is the unit gradient.** For the metric
`TauCeti.scalarRegularSublevelMetric` pulled back to the sublevel `{f ≤ a}` at a regular value `a`
of a smooth function `f`, the differential of the inclusion carries the outward unit normal at a
boundary point `q` to `grad f / |grad f|` at `q`. -/
theorem mfderiv_subtypeVal_outwardUnitNormal_scalarRegularSublevel
    (q : letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
      (𝓡∂ (n + 1)).boundary {x | f x ≤ a}) :
    letI := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
    letI : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
    mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) q (outwardUnitNormal q) =
      NormedSpace.normalize (Manifold.mgradient I f ((q : {x | f x ≤ a}) : N)) := by
  let := scalarRegularSublevelChartedSpace (hf.of_le ENat.LEInfty.out) hreg hn
  have := isManifold_scalarRegularSublevel hreg hn ENat.LEInfty.out hf
  let : RiemannianBundle (fun x : {x | f x ≤ a} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric hf hreg hn).toRiemannianMetric⟩
  have hqa : f (q : {x | f x ≤ a}) = a :=
    (Set.ext_iff.mp (boundary_scalarRegularSublevel hreg hn ENat.LEInfty.out hf) _).mp q.property
  -- `f ∘ j` attains its maximum `a` at `q`, so its gradient is `c • ν_out q` with `c ≥ 0`.
  set c := ‖mvfderiv (𝓡∂ (n + 1)) (-(f ∘ Subtype.val : {x | f x ≤ a} → ℝ))
    (q : {x | f x ≤ a})‖ with hc_def
  have hmin : IsLocalMin (-(f ∘ Subtype.val : {x | f x ≤ a} → ℝ)) (q : {x | f x ≤ a}) :=
    Filter.Eventually.of_forall fun x ↦ neg_le_neg (x.property.trans_eq hqa.symm)
  have hgrad : Manifold.mgradient (𝓡∂ (n + 1)) (f ∘ Subtype.val) (q : {x | f x ≤ a}) =
      c • outwardUnitNormal q := by
    rw [← neg_neg (Manifold.mgradient _ _ _), ← Manifold.mgradient_neg,
      mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin hmin, ← smul_neg,
      neg_inwardUnitNormal]
  -- The inclusion carries that gradient to `grad f`, which is nonzero at the regular level.
  have hj : Manifold.mgradient I f ((q : {x | f x ≤ a}) : N) =
      c • mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) q (outwardUnitNormal q) := by
    rw [← map_smul, ← hgrad]
    exact (mfderiv_mgradient_comp_subtypeVal_scalarRegularSublevel hf hreg hn _
      (hf.mdifferentiableAt (by simp))).symm
  have hc : 0 < c := by
    have hc₀ : 0 ≤ c := by
      rw [hc_def]
      positivity
    exact hc₀.lt_of_ne' fun hc0 ↦
      (hreg.isRegularPoint hqa).mgradient_ne_zero (by rw [hj, hc0, zero_smul])
  -- The inclusion is a local isometry, so it carries `ν_out q` to a unit vector.
  have hnorm : ‖mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → N) q
      (outwardUnitNormal q)‖ = 1 := by
    rw [(isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel hf hreg hn).norm_mfderiv,
      norm_outwardUnitNormal]
  rw [hj, NormedSpace.normalize_smul_of_pos hc, NormedSpace.normalize_eq_self_of_norm_eq_one hnorm]

end UnitNormal

end TauCeti
