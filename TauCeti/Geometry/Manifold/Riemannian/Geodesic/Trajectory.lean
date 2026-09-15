/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Maximal

/-!
# The maximal geodesic with prescribed initial data

This file turns the maximal-interval description of geodesic existence into a canonical curve.
The maximal geodesic through `p` with initial velocity `v` is the base projection of the maximal
integral curve of the geodesic spray through `(p, v)`.  Its integral-curve domain is proved to be
exactly `geodesicInterval I M p v`, so the projected curve is a geodesic with the prescribed
initial data on the whole of that interval.

The definition is total and takes the value `p` outside its natural domain.  Mathematical uses of
the curve therefore carry membership in `geodesicInterval`; this is the domain discipline needed
to define the Riemannian exponential map by evaluation at time one.

## Main definitions and results

* `TauCeti.Manifold.maximalGeodesic` is the chosen maximal geodesic with prescribed initial data.
* `TauCeti.Manifold.maximalIntegralCurveInterval_geodesicSpray` identifies the two independently
  defined maximal domains.
* `TauCeti.Manifold.isGeodesicCurveOnFrom_maximalGeodesic` gives the geodesic equation and initial
  data on the maximal domain.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom.eqOn_maximalGeodesic` is the corresponding uniqueness
  theorem for any open-interval geodesic witness.
* `TauCeti.Manifold.maximalGeodesic_smul` is homogeneity in the initial velocity and time.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5.
-/

-- Roadmap: HopfRinow

public section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable [T2Space (TangentBundle I M)]

omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
private theorem contMDiff_one_geodesicSpray :
    CMDiff 1 (fun w : TangentBundle I M ↦
      (⟨w, geodesicSpray I M w⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
  exact (contMDiff_geodesicSpray (I := I) (M := M) (n := (1 : ℕ∞ω))
    (m := ∞) (k := ∞) (by norm_num) (by norm_num)).of_le (by norm_num)

omit [T2Space (TangentBundle I M)] in
private theorem contMDiffOn_two_proj_of_isMIntegralCurveOn_geodesicSpray
    {z : ℝ → TangentBundle I M} {s : Set ℝ} (hs : IsOpen s)
    (hz : IsMIntegralCurveOn z (geodesicSpray I M) s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 2 (fun t ↦ (z t).proj) s := by
  intro t ht
  have hz2 : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 z t :=
    (hz.isMIntegralCurveAt (hs.mem_nhds ht)).contMDiffAt_two
      (contMDiff_one_geodesicSpray (I := I) (M := M)).contMDiffAt
  have hproj : ContMDiffAt I.tangent I 2 TotalSpace.proj (z t) :=
    Bundle.contMDiffAt_proj (fun x : M ↦ TangentSpace I x) (IB := I) (n := (2 : ℕ∞ω))
  exact (hproj.comp t hz2).contMDiffWithinAt

omit [T2Space (TangentBundle I M)] in
/-- The maximal integral-curve domain of the geodesic spray through `(p, v)` is the maximal
geodesic interval with initial data `(p, v)`. -/
theorem maximalIntegralCurveInterval_geodesicSpray (p : M) (v : TangentSpace I p) :
    maximalIntegralCurveInterval (geodesicSpray I M) (TotalSpace.mk' E p v) =
      geodesicInterval I M p v := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨z, a, b, hz, hz0, h0, ht, -⟩ :=
      exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
    have hbase : ContMDiffOn 𝓘(ℝ, ℝ) I 2 (fun r ↦ (z r).proj) (Ioo a b) :=
      contMDiffOn_two_proj_of_isMIntegralCurveOn_geodesicSpray isOpen_Ioo hz
    have hgeo : IsGeodesicCurveOn I (fun r ↦ (z r).proj) (Ioo a b) :=
      isGeodesicCurveOn_proj_of_isMIntegralCurveOn (uniqueDiffOn_Ioo a b) hz hbase
    have hlift := eq_curveVelocityLiftWithin_of_isMIntegralCurveOn
      (I := I) (M := M) (s := Ioo a b) (t := (0 : ℝ))
      ((uniqueDiffOn_Ioo a b) 0 h0) hz h0
    have hinitial : TotalSpace.mk' E (z 0).proj
        (curveVelocityWithin I (fun r ↦ (z r).proj) (Ioo a b) 0) =
        TotalSpace.mk' E p v := by
      simpa only [curveVelocityLiftWithin_apply] using hlift.symm.trans hz0
    exact (mem_geodesicInterval_iff (I := I) (M := M)).2
      ⟨fun r ↦ (z r).proj, a, b, ⟨hgeo, h0, hinitial⟩, ht⟩
  · intro t ht
    obtain ⟨γ, a, b, hγ, ht⟩ :=
      (mem_geodesicInterval_iff (I := I) (M := M)).1 ht
    have hlift : IsMIntegralCurveOn (curveVelocityLiftWithin I γ (Ioo a b))
        (geodesicSpray I M) (Ioo a b) :=
      (isMIntegralCurveOn_curveVelocityLiftWithin_iff (uniqueDiffOn_Ioo a b)
        hγ.isGeodesicCurveOn.contMDiffOn).2 hγ.isGeodesicCurveOn
    have hinitial : curveVelocityLiftWithin I γ (Ioo a b) 0 = TotalSpace.mk' E p v := by
      simpa only [curveVelocityLiftWithin_apply] using hγ.initial_eq
    exact hlift.subset_maximalIntegralCurveInterval hγ.zero_mem hinitial ht

variable (I M) in
/-- The maximal geodesic through `p` with initial velocity `v`, junk-valued at `p` outside its
maximal interval. -/
def maximalGeodesic (p : M) (v : TangentSpace I p) (t : ℝ) : M :=
  (maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) t).proj

/-- The maximal geodesic has the prescribed initial data on its maximal interval. -/
theorem isGeodesicCurveOnFrom_maximalGeodesic (p : M) (v : TangentSpace I p) :
    IsGeodesicCurveOnFrom I (maximalGeodesic I M p v) (geodesicInterval I M p v) p v := by
  have hdomains := maximalIntegralCurveInterval_geodesicSpray (I := I) (M := M) p v
  have hz : IsMIntegralCurveOn
      (maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v)) (geodesicSpray I M)
      (geodesicInterval I M p v) := by
    rw [← hdomains]
    exact isMIntegralCurveOn_maximalIntegralCurve
      (contMDiff_one_geodesicSpray (I := I) (M := M))
  have hbase : ContMDiffOn 𝓘(ℝ, ℝ) I 2 (maximalGeodesic I M p v)
      (geodesicInterval I M p v) := by
    exact contMDiffOn_two_proj_of_isMIntegralCurveOn_geodesicSpray
      isOpen_geodesicInterval hz
  have hgeo : IsGeodesicCurveOn I (maximalGeodesic I M p v)
      (geodesicInterval I M p v) :=
    isGeodesicCurveOn_proj_of_isMIntegralCurveOn
      (isOpen_geodesicInterval.uniqueDiffOn) hz hbase
  have h0 : (0 : ℝ) ∈ geodesicInterval I M p v := zero_mem_geodesicInterval
  have hlift := eq_curveVelocityLiftWithin_of_isMIntegralCurveOn
    (I := I) (M := M) (s := geodesicInterval I M p v) (t := (0 : ℝ))
    (isOpen_geodesicInterval.uniqueDiffOn 0 h0) hz h0
  have hz0 : maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) 0 =
      TotalSpace.mk' E p v := by
    apply maximalIntegralCurve_zero
    rw [hdomains]
    exact h0
  refine ⟨hgeo, h0, ?_⟩
  unfold maximalGeodesic
  simpa only [curveVelocityLiftWithin_apply] using hlift.symm.trans hz0

/-- The maximal geodesic starts at its prescribed base point. -/
@[simp] theorem maximalGeodesic_zero (p : M) (v : TangentSpace I p) :
    maximalGeodesic I M p v 0 = p :=
  (isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v).base_eq

/-- Every geodesic with initial data `(p, v)` on an open interval around zero agrees there with
the maximal geodesic. -/
theorem IsGeodesicCurveOnFrom.eqOn_maximalGeodesic
    {p : M} {v : TangentSpace I p} {γ : ℝ → M} {a b : ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ (Ioo a b) p v) :
    EqOn (maximalGeodesic I M p v) γ (Ioo a b) := by
  have hlift : IsMIntegralCurveOn (curveVelocityLiftWithin I γ (Ioo a b))
      (geodesicSpray I M) (Ioo a b) :=
    (isMIntegralCurveOn_curveVelocityLiftWithin_iff (uniqueDiffOn_Ioo a b)
      hγ.isGeodesicCurveOn.contMDiffOn).2 hγ.isGeodesicCurveOn
  have hinitial : curveVelocityLiftWithin I γ (Ioo a b) 0 = TotalSpace.mk' E p v := by
    simpa only [curveVelocityLiftWithin_apply] using hγ.initial_eq
  have heq := hlift.eqOn_maximalIntegralCurve
    (contMDiff_one_geodesicSpray (I := I) (M := M)) hγ.zero_mem hinitial
  intro t ht
  rw [maximalGeodesic]
  simpa only [curveVelocityLiftWithin_proj] using congrArg TotalSpace.proj (heq ht)

/-- The maximal geodesic with zero initial velocity is the constant curve. -/
@[simp] theorem maximalGeodesic_zero_velocity (p : M) :
    maximalGeodesic I M p (0 : TangentSpace I p) = fun _ ↦ p := by
  funext t
  let a : ℝ := -(|t| + 1)
  let b : ℝ := |t| + 1
  have h0 : (0 : ℝ) ∈ Ioo a b := by
    exact ⟨by dsimp [a]; linarith [abs_nonneg t], by dsimp [b]; linarith [abs_nonneg t]⟩
  have ht : t ∈ Ioo a b := by
    exact ⟨by dsimp [a]; linarith [neg_abs_le t], by dsimp [b]; linarith [le_abs_self t]⟩
  have hconst : IsMIntegralCurve
      (fun _ : ℝ ↦ TotalSpace.mk' E p (0 : TangentSpace I p)) (geodesicSpray I M) :=
    isMIntegralCurve_const (geodesicSpray_zero (I := I) (M := M) p)
  have heq := (hconst.isMIntegralCurveOn (Ioo a b)).eqOn_maximalIntegralCurve
    (contMDiff_one_geodesicSpray (I := I) (M := M)) h0 rfl ht
  rw [maximalGeodesic]
  exact congrArg TotalSpace.proj heq

/-- Rescaling the initial velocity rescales time along the maximal geodesic, whenever the displayed
time belongs to the corresponding maximal interval. -/
@[simp] theorem maximalGeodesic_smul {p : M} {v : TangentSpace I p} {a t : ℝ}
    (ht : t ∈ geodesicInterval I M p (a • v)) :
    maximalGeodesic I M p (a • v) t = maximalGeodesic I M p v (a * t) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_smul, zero_mul, maximalGeodesic_zero_velocity, maximalGeodesic_zero]
  · have hat : a * t ∈ geodesicInterval I M p v :=
      (mem_geodesicInterval_smul_iff (I := I) (M := M) ha).1 ht
    obtain ⟨γ, b, c, hγ, hatbc⟩ :=
      (mem_geodesicInterval_iff (I := I) (M := M)).1 hat
    obtain ⟨d, e, hpre, hγ'⟩ := hγ.exists_comp_mul_left_Ioo ha
    have htde : t ∈ Ioo d e := by
      rw [← hpre]
      exact hatbc
    calc
      maximalGeodesic I M p (a • v) t = (γ ∘ fun s : ℝ ↦ a * s) t :=
        hγ'.eqOn_maximalGeodesic htde
      _ = γ (a * t) := rfl
      _ = maximalGeodesic I M p v (a * t) :=
        (hγ.eqOn_maximalGeodesic hatbc).symm

omit [T2Space (TangentBundle I M)] in
/-- Outside its maximal interval, the total maximal geodesic takes its junk value `p`. -/
@[simp] theorem maximalGeodesic_eq_of_not_mem {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∉ geodesicInterval I M p v) : maximalGeodesic I M p v t = p := by
  have ht' : t ∉ maximalIntegralCurveInterval
      (geodesicSpray I M) (TotalSpace.mk' E p v) := by
    rwa [maximalIntegralCurveInterval_geodesicSpray]
  rw [maximalGeodesic, maximalIntegralCurve_eq_of_not_mem ht']

end TauCeti.Manifold

end
