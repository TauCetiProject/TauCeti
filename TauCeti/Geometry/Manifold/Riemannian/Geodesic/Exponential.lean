/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Flow
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Riemannian exponential map

For a point `p` of a smooth finite-dimensional Riemannian manifold `M`, the exponential map sends
a tangent vector `v ∈ T_p M` to the point reached at time `1` by the maximal geodesic leaving `p`
with velocity `v`.  Its natural domain is the set of `v` whose maximal geodesic interval contains
`1`.

The map is defined as a total function which takes the junk value `p` outside its natural domain;
every theorem about its mathematical value carries the corresponding domain hypothesis.  The
homogeneity of maximal geodesics turns into the two basic facts relating the exponential map to
geodesics: `t` lies in the maximal interval of `v` exactly when `t • v` lies in the domain, and
then `exp_p (t • v)` is the maximal geodesic at time `t`.  In particular the domain is star-shaped
at `0`.  Smooth dependence of the maximal geodesic flow shows that the tangent vectors `z ∈ T_x M`
with `z` in the domain of `exp_x` form an open subset of the tangent bundle, on which
`z ↦ exp_x z` is smooth, being the geodesic flow at time `1` followed by the base projection.
Restricting to the fibre over `p`, the domain of `exp_p` is open and `exp_p` is smooth there.
Its differential at the origin is the identity of `T_p M`, once the tangent space to `T_p M` at
`0` is identified with `T_p M` itself by `NormedSpace.fromTangentSpace`; by the inverse function
theorem the exponential map is therefore a local diffeomorphism at `0`, the input to normal
neighbourhoods.  Finally, the domain is all of `T_p M` exactly when every geodesic leaving `p` is
defined for all time.

## Main definitions and results

* `TauCeti.Manifold.expDomain`: the natural domain of the exponential map at `p`.
* `TauCeti.Manifold.riemannianExp`: the exponential map at `p`.
* `TauCeti.Manifold.IsGeodesicallyCompleteAt`: every geodesic leaving `p` is defined for all time.
* `TauCeti.Manifold.mem_geodesicInterval_iff_smul_mem_expDomain`: the maximal interval of `v` is
  the set of times `t` with `t • v` in the domain.
* `TauCeti.Manifold.riemannianExp_smul`: `exp_p (t • v)` is the maximal geodesic at time `t`,
  on and off its natural interval (where both sides take the junk value).
* `TauCeti.Manifold.mem_expDomain_of_norm_le_dist`: a vector with `‖v‖ ≤ dist p (exp_p v)` lies
  in the domain, since off it `exp_p v` is the junk value `p`.
* `TauCeti.Manifold.starConvex_expDomain`: the domain is star-shaped at `0`.
* `TauCeti.Manifold.isOpen_setOfPred_mem_expDomain` and
  `TauCeti.Manifold.contMDiffOn_riemannianExp_tangentBundle`: on the tangent bundle, the domain of
  the exponential map is open and the exponential map is smooth there.
* `TauCeti.Manifold.isOpen_expDomain`: the natural domain is open.
* `TauCeti.Manifold.contMDiffOn_riemannianExp`: the exponential map is smooth on its domain.
* `TauCeti.Manifold.curveVelocity_riemannianExp_add_smul` and
  `TauCeti.Manifold.curveVelocity_riemannianExp_smul`: velocities of affine and radial curves
  through the exponential map.
* `TauCeti.Manifold.curveVelocity_riemannianExp_smul_zero`: the radial curve `s ↦ exp_p (s • v)`
  leaves `p` with velocity `v`.
* `TauCeti.Manifold.mfderiv_riemannianExp_zero`: the differential of the exponential map at `0`
  is the identity.
* `TauCeti.Manifold.isLocalDiffeomorphAt_riemannianExp_zero`: the exponential map is a local
  diffeomorphism at `0`.
* `TauCeti.Manifold.radialVariation_eq_maximalGeodesic`,
  `TauCeti.Manifold.contMDiffAt_radialVariation` and
  `TauCeti.Manifold.eventually_acceleration_radialVariation_eq_zero`: the radial variation
  `exp_p (t • (v + u • w))` is a smooth family of geodesics.
* `TauCeti.Manifold.variationField_radialVariation`: the variation field of the radial variation
  is `t ↦ d(exp_p)_{t v}(t w)`.
* `TauCeti.Manifold.expDomain_eq_univ_iff`: the exponential map at `p` is defined on all of
  `T_p M` exactly when `M` is geodesically complete at `p`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2, Prop. 2.9.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5, Prop. 5.19.
-/

-- Roadmap: HopfRinow

public section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### The domain and the map -/

variable (I M) in
/-- The natural domain of the Riemannian exponential map at `p`: the tangent vectors `v` whose
maximal geodesic from `p` with initial velocity `v` is defined at time `1`. -/
def expDomain (p : M) : Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ geodesicInterval I M p v}

variable (I M) in
/-- The Riemannian exponential map at `p`: the value at time `1` of the maximal geodesic from `p`
with initial velocity `v`.  Outside `expDomain I M p` it takes the junk value `p`. -/
def riemannianExp (p : M) (v : TangentSpace I p) : M :=
  maximalGeodesic I M p v 1

/-- A tangent vector lies in the domain of the exponential map exactly when its maximal geodesic
interval contains `1`. -/
@[simp] theorem mem_expDomain_iff {p : M} {v : TangentSpace I p} :
    v ∈ expDomain I M p ↔ (1 : ℝ) ∈ geodesicInterval I M p v :=
  Iff.rfl

/-- The exponential map is the maximal geodesic evaluated at time `1`. -/
theorem riemannianExp_def (p : M) (v : TangentSpace I p) :
    riemannianExp I M p v = maximalGeodesic I M p v 1 := by
  rfl

/-- The zero vector lies in the domain of the exponential map. -/
theorem zero_mem_expDomain (p : M) : (0 : TangentSpace I p) ∈ expDomain I M p := by
  simp only [mem_expDomain_iff, geodesicInterval_zero, mem_univ]

section Boundaryless

variable [I.Boundaryless]

/-- The exponential map sends the zero vector to the base point. -/
@[simp] theorem riemannianExp_zero [T2Space M] (p : M) :
    riemannianExp I M p 0 = p := by
  simp [riemannianExp_def]

/-- Outside its natural domain, the exponential map takes its junk value `p`. -/
@[simp] theorem riemannianExp_of_notMem_expDomain {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain I M p) : riemannianExp I M p v = p :=
  maximalGeodesic_eq_of_not_mem (mt mem_expDomain_iff.2 hv)

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A tangent vector `v` with `‖v‖ ≤ dist p (exp_p v)` lies in the domain of `exp_p`: off the
domain `exp_p v` is the junk value `p`, which forces `v = 0`. -/
theorem mem_expDomain_of_norm_le_dist {p : M} {v : TangentSpace I p}
    (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) : v ∈ expDomain I M p := by
  by_contra hv
  rw [riemannianExp_of_notMem_expDomain hv, dist_self, norm_le_zero_iff] at hmin
  exact hv (hmin ▸ zero_mem_expDomain p)

end Metric

/-! ### Homogeneity -/

/-- **The domain of the exponential map along a ray.**  A time `t` lies in the maximal geodesic
interval of `v` exactly when `t • v` lies in the domain of the exponential map. -/
theorem mem_geodesicInterval_iff_smul_mem_expDomain {p : M} {v : TangentSpace I p} {t : ℝ} :
    t ∈ geodesicInterval I M p v ↔ t • v ∈ expDomain I M p := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [mem_expDomain_iff, mem_geodesicInterval_smul_iff ht, mul_one]

/-- The geodesic interval of `v` is the preimage of the domain of the exponential map under
`t ↦ t • v`. -/
theorem geodesicInterval_eq_preimage_expDomain (p : M) (v : TangentSpace I p) :
    geodesicInterval I M p v = (fun t : ℝ ↦ t • v) ⁻¹' expDomain I M p := by
  ext t
  exact mem_geodesicInterval_iff_smul_mem_expDomain

/-- **The exponential map along a ray.**  For every `t`, the exponential of `t • v` is the maximal
geodesic from `p` with initial velocity `v` at time `t`: on the maximal interval this is the
homogeneity of maximal geodesics, while off it both sides take the junk value `p`. -/
theorem riemannianExp_smul [T2Space M]
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    riemannianExp I M p (t • v) = maximalGeodesic I M p v t := by
  by_cases ht : t ∈ geodesicInterval I M p v
  · have h1 : (1 : ℝ) ∈ geodesicInterval I M p (t • v) :=
      mem_expDomain_iff.1 (mem_geodesicInterval_iff_smul_mem_expDomain.1 ht)
    rw [riemannianExp_def, maximalGeodesic_smul h1, mul_one]
  · rw [riemannianExp_of_notMem_expDomain
        (mt mem_geodesicInterval_iff_smul_mem_expDomain.mpr ht),
      maximalGeodesic_eq_of_not_mem ht]

omit [I.Boundaryless] in
/-- The domain of the exponential map is star-shaped at the zero vector. -/
theorem starConvex_expDomain (p : M) : StarConvex ℝ (0 : TangentSpace I p) (expDomain I M p) := by
  intro v hv a b _ hb hab
  rw [smul_zero, zero_add]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [zero_smul]
    exact zero_mem_expDomain p
  · rw [mem_expDomain_iff, mem_geodesicInterval_smul_iff hb0, mul_one]
    have hv1 := mem_expDomain_iff.1 hv
    exact ordConnected_geodesicInterval.out (zero_mem_geodesicInterval_of_mem hv1) hv1
      ⟨hb, by linarith⟩

/-! ### Regularity -/

/-- Each tangent space is a charted space over itself (via the identity chart), so that
smoothness of maps out of a tangent space can be stated in the manifold API. -/
local instance tangentSpaceChartedSpace (p : M) :
    ChartedSpace (TangentSpace I p) (TangentSpace I p) :=
  chartedSpaceSelf (TangentSpace I p)

/-- **The domain of the exponential map in the tangent bundle is open**: the tangent vectors
`z ∈ T_x M` lying in the natural domain of `exp_x` form an open subset of `TM`. -/
theorem isOpen_setOfPred_mem_expDomain [T2Space M] :
    IsOpen {z : TangentBundle I M | z.2 ∈ expDomain I M z.proj} := by
  simp only [mem_expDomain_iff]
  exact isOpen_setOfPred_mem_geodesicInterval.preimage (continuous_id.prodMk continuous_const)

/-- **The exponential map is smooth on the tangent bundle.**  The map `z ↦ exp_x z`, for `z` a
tangent vector at `x`, is smooth on the open subset of `TM` where it is naturally defined: it is
the geodesic flow at time `1` followed by the base projection. -/
theorem contMDiffOn_riemannianExp_tangentBundle [T2Space M] :
    ContMDiffOn I.tangent I ∞ (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2)
      {z | z.2 ∈ expDomain I M z.proj} :=
  (contMDiffOn_maximalGeodesic.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
    fun _ hz ↦ mem_expDomain_iff.1 hz).congr fun z _ ↦ riemannianExp_def z.proj z.2

/-- The exponential map is continuous on the open subset of the tangent bundle where it is
naturally defined. -/
theorem continuousOn_riemannianExp_tangentBundle [T2Space M] :
    ContinuousOn (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2)
      {z | z.2 ∈ expDomain I M z.proj} :=
  contMDiffOn_riemannianExp_tangentBundle.continuousOn

/-- The natural domain of the Riemannian exponential map is open. -/
theorem isOpen_expDomain [T2Space M] (p : M) :
    IsOpen (expDomain I M p) :=
  isOpen_setOfPred_mem_expDomain.preimage (FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p)

/-- The Riemannian exponential map is smooth on its natural domain. -/
theorem contMDiffOn_riemannianExp [T2Space M] (p : M) :
    ContMDiffOn 𝓘(ℝ, TangentSpace I p) I ∞
      (riemannianExp I M p) (expDomain I M p) := by
  have hinitial : ContMDiff 𝓘(ℝ, TangentSpace I p) I.tangent ∞
      (fun v : TangentSpace I p ↦ TotalSpace.mk' E p v) :=
    contMDiff_tangentBundle_mk_constBase (I := I) (M := M) (n := ∞)
      ((tangentSpaceCastModel I p).toContinuousLinearMap.contMDiff (n := ∞)) p
  exact contMDiffOn_riemannianExp_tangentBundle.comp hinitial.contMDiffOn fun _ hv ↦ hv

/-- The Riemannian exponential map is continuous on its natural domain. -/
theorem continuousOn_riemannianExp [T2Space M] (p : M) :
    ContinuousOn (riemannianExp I M p) (expDomain I M p) :=
  (contMDiffOn_riemannianExp (I := I) (M := M) p).continuousOn

/-- The Riemannian exponential map is smooth at every point of its natural domain. -/
theorem contMDiffAt_riemannianExp [T2Space M] {p : M}
    {v : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v :=
  (contMDiffOn_riemannianExp (I := I) (M := M) p v hv).contMDiffAt
    (isOpen_expDomain (I := I) (M := M) p |>.mem_nhds hv)

/-- The velocity of the exponential image of a path is the differential of the exponential map
applied to the derivative of the path in the tangent space. -/
theorem curveVelocity_riemannianExp_comp [T2Space M]
    {p : M} {w : ℝ → TangentSpace I p} {w' : TangentSpace I p} {t : ℝ}
    (hw : HasDerivAt w w' t) (hwt : w t ∈ expDomain I M p) :
    curveVelocity I (riemannianExp I M p ∘ w) t =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) w' :=
  ((contMDiffAt_riemannianExp hwt).mdifferentiableAt (by simp)).curveVelocity_comp_mfderiv hw

/-- The velocity of an affine curve through the exponential map is its differential in the
affine direction. -/
theorem curveVelocity_riemannianExp_add_smul [T2Space M]
    {p : M} {v w : TangentSpace I p} {u : ℝ} (hu : v + u • w ∈ expDomain I M p) :
    curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (v + s • w)) u =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (v + u • w) w := by
  have hg : HasDerivAt (fun s : ℝ ↦ v + s • w) w u := by
    simpa using (hasDerivAt_id u).smul_const w |>.const_add v
  exact curveVelocity_riemannianExp_comp (I := I) (M := M) hg hu

/-- The velocity of a radial curve through the exponential map is its differential in the
radial direction. -/
theorem curveVelocity_riemannianExp_smul [T2Space M]
    {p : M} {v : TangentSpace I p} {t : ℝ} (ht : t • v ∈ expDomain I M p) :
    curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) t =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) v := by
  have h := curveVelocity_riemannianExp_add_smul
    (I := I) (M := M) (v := 0) (w := v) (u := t) (by simpa only [zero_add] using ht)
  have hcurve : (fun s : ℝ ↦ riemannianExp I M p (0 + s • v)) =
      fun s : ℝ ↦ riemannianExp I M p (s • v) := by
    funext s
    rw [zero_add]
  rw [hcurve, zero_add] at h
  exact h

/-- The Riemannian exponential map is continuous at every point of its natural domain. -/
theorem continuousAt_riemannianExp [T2Space M] {p : M}
    {v : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    ContinuousAt (riemannianExp I M p) v :=
  (contMDiffAt_riemannianExp (I := I) (M := M) hv).continuousAt

/-! ### The derivative at the origin -/

/-- **The differential of the exponential map at the origin** sends every tangent vector to
itself. -/
@[simp] theorem mfderiv_riemannianExp_apply_zero [T2Space M] (p : M)
    (v : TangentSpace I p) :
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v = v := by
  have hd : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 :=
    (contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt (by simp)
  have hray : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, TangentSpace I p) (fun t : ℝ ↦ t • v) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).hasFDerivAt
    rw [one_smul] at h
    exact hasMFDerivAt_iff_hasFDerivAt.2 h
  have hexp : HasMFDerivAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) ((0 : ℝ) • v)
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0) := by
    rw [zero_smul]
    exact hd.hasMFDerivAt
  have hray_eq : (riemannianExp I M p ∘ fun t : ℝ ↦ t • v) =ᶠ[𝓝 0] maximalGeodesic I M p v :=
    Filter.Eventually.of_forall fun t ↦ riemannianExp_smul p v t
  have hgeo := ((isGeodesicCurveOnFrom_maximalGeodesic p v).hasMFDerivAt_zero
    (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval)).congr_of_eventuallyEq_abuse
    hray_eq
  have hv : ((1 : ℝ →L[ℝ] ℝ).smulRight v) 1 = v := by
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  have hcomp :
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 ∘L
        (1 : ℝ →L[ℝ] ℝ).smulRight v) 1 =
        mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v := by
    rw [ContinuousLinearMap.comp_apply]
    -- the argument of the differential lives in `TangentSpace 𝓘(ℝ, T_p M) 0`, which is the
    -- canonical identification of `T_p M` that `hv` is stated in
    exact congrArg _ hv
  exact hcomp.symm.trans
    ((DFunLike.congr_fun (hasMFDerivAt_unique (hexp.comp 0 hray) hgeo) (1 : ℝ)).trans hv)

/-- The radial curve `s ↦ exp_p (s • v)` is smooth at time zero. -/
theorem contMDiffAt_riemannianExp_smul_zero [T2Space M] (p : M) (v : TangentSpace I p) :
    ContMDiffAt 𝓘(ℝ) I ∞ (fun s : ℝ ↦ riemannianExp I M p (s • v)) 0 := by
  have hlin : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, TangentSpace I p) ∞ (fun s : ℝ ↦ s • v) 0 :=
    (contMDiff_iff_contDiff.mpr (by fun_prop)).contMDiffAt
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      ((0 : ℝ) • v) := by
    simpa only [zero_smul] using contMDiffAt_riemannianExp (zero_mem_expDomain p)
  exact hexp.comp (f := fun s : ℝ ↦ s • v) (g := riemannianExp I M p) 0 hlin

/-- The radial curve `s ↦ exp_p (s • v)` leaves `p` with velocity `v`. -/
@[simp] theorem curveVelocity_riemannianExp_smul_zero [T2Space M] (p : M) (v : TangentSpace I p) :
    curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (s • v)) 0 = v := by
  rw [curveVelocity_riemannianExp_smul (by simp)]
  -- `mfderiv_congr_point` moves the base point of the differential from `0 • v` to `0`
  exact (DFunLike.congr_fun (mfderiv_congr_point (I := 𝓘(ℝ, TangentSpace I p)) (I' := I)
    (f := riemannianExp I M p) (zero_smul ℝ v)) v).trans (mfderiv_riemannianExp_apply_zero p v)

/-- **The differential of the exponential map at the origin is the identity**, under the
canonical identification `NormedSpace.fromTangentSpace` of the tangent space to `T_p M` at `0`
with `T_p M`. -/
theorem mfderiv_riemannianExp_zero [T2Space M] (p : M) :
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 =
      (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).toContinuousLinearMap := by
  ext v
  exact mfderiv_riemannianExp_apply_zero (I := I) p v

/-- The exponential map has the identity of `T_p M` as its derivative at the origin. -/
theorem hasMFDerivAt_riemannianExp_zero [T2Space M] (p : M) :
    HasMFDerivAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0
      (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).toContinuousLinearMap := by
  rw [← mfderiv_riemannianExp_zero]
  exact ((contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt
    (by simp)).hasMFDerivAt

/-- In extended coordinates, the exponential map has the canonical identification
`T_p M →L[ℝ] E` as its strict derivative at the origin. -/
theorem hasStrictFDerivAt_riemannianExp_zero [T2Space M] (p : M) :
    HasStrictFDerivAt
      (writtenInExtChartAt 𝓘(ℝ, TangentSpace I p) I 0 (riemannianExp I M p))
      (tangentSpaceCastModel I p).toContinuousLinearMap 0 := by
  have hsmooth := contMDiffAt_riemannianExp (I := I) (M := M) (zero_mem_expDomain p)
  have hcoord : ContDiffAt ℝ ∞
      (writtenInExtChartAt 𝓘(ℝ, TangentSpace I p) I 0 (riemannianExp I M p)) 0 := by
    have h := (contMDiffAt_iff.1 hsmooth).2.contDiffAt (by simp)
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.comp_id, Function.id_def, riemannianExp_zero] using h
  apply hcoord.hasStrictFDerivAt
  · have h := (hasMFDerivAt_riemannianExp_zero (I := I) p).2
    rw [riemannianExp_zero] at h
    have h' : HasFDerivWithinAt
        (writtenInExtChartAt 𝓘(ℝ, TangentSpace I p) I 0 (riemannianExp I M p))
        ((tangentSpaceCastModel I p).toContinuousLinearMap.comp
          ((NormedSpace.fromTangentSpace (0 : TangentSpace I p)).toContinuousLinearMap.comp
            (tangentSpaceCastModel 𝓘(ℝ, TangentSpace I p) 0).symm.toContinuousLinearMap))
        Set.univ 0 := by
      simpa only [modelWithCornersSelf_coe, Set.range_id, ext_chart_model_space_apply] using h
    refine (h'.hasFDerivAt Filter.univ_mem).congr_fderiv ?_
    -- `NormedSpace.fromTangentSpace` is by definition `tangentSpaceCastModel` at a model space,
    -- so the two identifications of `TangentSpace 𝓘(ℝ, T_p M) 0` with `T_p M` cancel
    have hcancel :
        (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).toContinuousLinearMap ∘L
          (tangentSpaceCastModel 𝓘(ℝ, TangentSpace I p) 0).symm.toContinuousLinearMap =
          ContinuousLinearMap.id ℝ (TangentSpace I p) :=
      (tangentSpaceCastModel 𝓘(ℝ, TangentSpace I p) 0).coe_comp_coe_symm
    rw [hcancel, ContinuousLinearMap.comp_id]
  · simp

/-- **The exponential map is a local diffeomorphism at the origin.** -/
theorem isLocalDiffeomorphAt_riemannianExp_zero [T2Space M] (p : M) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) 0 :=
  isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_riemannianExp (I := I) p)
    (isOpen_expDomain (I := I) p) (zero_mem_expDomain (I := I) p)
    BoundarylessManifold.isInteriorPoint (by simp)
    (mfderiv_riemannianExp_zero (I := I) p).symm

/-! ### Radial variations

The radial variation `F (u, t) = exp_p (t • (v + u • w))` of the geodesic `t ↦ exp_p (t • v)`
is the family of maximal geodesics leaving `p` with initial velocities `v + u • w`.  Its variation
field computes the differential of the exponential map, which is how the Gauss lemma and the
identification of that differential with Jacobi fields are proved.

Each statement takes the variation as a function `F` together with its defining equation, rather
than as the explicit two-parameter formula.  The fibre in which a velocity vector lives is indexed
by the point of the curve, so rewriting a radial curve into the maximal geodesic it equals has to
reach the index as well; that is possible for `F u` and not for the formula, whose index appears
already evaluated. -/

section RadialVariation

open CovariantDerivative

variable [T2Space M] {p : M} {v w : TangentSpace I p} {F : ℝ → ℝ → M}

/-- Each radial curve of the variation is the maximal geodesic with the corresponding initial
velocity. -/
theorem radialVariation_eq_maximalGeodesic
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) (u : ℝ) :
    F u = maximalGeodesic I M p (v + u • w) :=
  funext fun t ↦ (hF u t).trans (riemannianExp_smul p (v + u • w) t)

omit [I.Boundaryless] [T2Space M] in
/-- The central curve of the radial variation is the radial geodesic `t ↦ exp_p (t • v)`. -/
theorem radialVariation_zero (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) :
    F 0 = fun t : ℝ ↦ riemannianExp I M p (t • v) :=
  funext fun t ↦ by rw [hF, zero_smul, add_zero]

/-- Every curve of the radial variation starts at `p`. -/
theorem radialVariation_apply_zero
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) (u : ℝ) : F u 0 = p := by
  rw [hF, zero_smul, riemannianExp_zero]

/-- The radial variation is smooth at every parameter pair whose radial vector lies in the natural
domain of the exponential map. -/
theorem contMDiffAt_radialVariation
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {u t : ℝ}
    (hut : t • (v + u • w) ∈ expDomain I M p) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t) := by
  have hFfun : (fun z : ℝ × ℝ ↦ F z.1 z.2) =
      fun z : ℝ × ℝ ↦ riemannianExp I M p (z.2 • (v + z.1 • w)) :=
    funext fun z ↦ hF z.1 z.2
  have hinput : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, TangentSpace I p) ∞
      (fun z : ℝ × ℝ ↦ z.2 • (v + z.1 • w)) (u, t) :=
    (contMDiff_iff_contDiff.mpr
      (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.2 • (v + z.1 • w)))).contMDiffAt
  rw [hFfun]
  exact (contMDiffAt_riemannianExp (I := I) (M := M) hut).comp (u, t) hinput

/-- A parameter of the maximal geodesic interval of `v` stays in the maximal geodesic interval of
`v + u • w` for all `u` near `0`. -/
theorem eventually_mem_geodesicInterval_add_smul {t : ℝ} (ht : t ∈ geodesicInterval I M p v) :
    ∀ᶠ u in 𝓝 (0 : ℝ), t ∈ geodesicInterval I M p (v + u • w) := by
  have hcont : ContinuousAt (fun u : ℝ ↦ t • (v + u • w)) 0 := by fun_prop
  have hpre : (fun u : ℝ ↦ t • (v + u • w)) ⁻¹' expDomain I M p ∈ 𝓝 0 :=
    hcont.preimage_mem_nhds ((isOpen_expDomain p).mem_nhds
      (by simpa using mem_geodesicInterval_iff_smul_mem_expDomain.mp ht))
  filter_upwards [hpre] with u hu
  exact mem_geodesicInterval_iff_smul_mem_expDomain.mpr hu

/-- The covariant acceleration of a radial curve of the variation vanishes on its maximal
interval. -/
theorem acceleration_radialVariation_eq_zero
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {u t : ℝ}
    (ht : t ∈ geodesicInterval I M p (v + u • w)) :
    acceleration (leviCivitaConnection I M) (F u) t = 0 := by
  rw [radialVariation_eq_maximalGeodesic hF u]
  exact acceleration_maximalGeodesic_eq_zero ht

/-- At a parameter of the central geodesic, the radial curves of the variation near the central
one have vanishing covariant acceleration. -/
theorem eventually_acceleration_radialVariation_eq_zero
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    ∀ᶠ u in 𝓝 (0 : ℝ), acceleration (leviCivitaConnection I M) (F u) t = 0 :=
  (eventually_mem_geodesicInterval_add_smul ht).mono fun _ hu ↦
    acceleration_radialVariation_eq_zero hF hu

/-- The variation field of the radial variation at a parameter `t` of the central geodesic is the
differential `d(exp_p)_{t v}(t w)` of the exponential map. -/
theorem variationField_radialVariation
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    variationField I F t =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w) := by
  have hcurve : (fun u ↦ F u t) = fun u ↦ riemannianExp I M p (t • v + u • t • w) :=
    funext fun u ↦ by rw [hF, smul_add, smul_comm t u w]
  have hu : t • v + (0 : ℝ) • t • w ∈ expDomain I M p := by
    simpa using mem_geodesicInterval_iff_smul_mem_expDomain.mp ht
  -- The goal is stated in the fibre over `F 0 t`, while the differential lives in the fibre over
  -- `exp_p (t • v)`; both fibres are `E`.
  rw [variationField_apply, hcurve, curveVelocity_riemannianExp_add_smul hu, zero_smul, add_zero]

end RadialVariation

end Boundaryless

/-! ### Completeness at a point -/

variable (I M) in
/-- A Riemannian manifold is **geodesically complete at `p`** when every maximal geodesic leaving
`p` is defined for all time. -/
def IsGeodesicallyCompleteAt (p : M) : Prop :=
  ∀ v : TangentSpace I p, geodesicInterval I M p v = univ

/-- **Completeness at a point via the exponential map.**  The exponential map at `p` is defined on
all of `T_p M` exactly when every geodesic leaving `p` is defined for all time. -/
theorem expDomain_eq_univ_iff {p : M} :
    expDomain I M p = univ ↔ IsGeodesicallyCompleteAt I M p := by
  refine ⟨fun h v ↦ eq_univ_of_forall fun t ↦ ?_, fun h ↦ eq_univ_of_forall fun v ↦ ?_⟩
  · have h1 : ∀ w : TangentSpace I p, (1 : ℝ) ∈ geodesicInterval I M p w := fun w ↦
      mem_expDomain_iff.1 (eq_univ_iff_forall.1 h w)
    rcases eq_or_ne t 0 with rfl | ht
    · exact zero_mem_geodesicInterval_of_mem (h1 v)
    · simpa only [mul_one] using (mem_geodesicInterval_smul_iff ht).1 (h1 (t • v))
  · rw [mem_expDomain_iff, h v]
    exact mem_univ _

/-- Geodesic completeness at a point is equivalent to every initial velocity admitting a
geodesic at time `1`. -/
theorem isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval {p : M} :
    IsGeodesicallyCompleteAt I M p ↔
      ∀ v : TangentSpace I p, (1 : ℝ) ∈ geodesicInterval I M p v := by
  rw [← expDomain_eq_univ_iff, eq_univ_iff_forall]
  simp only [mem_expDomain_iff]

/-- Failure of geodesic completeness supplies an initial velocity whose geodesic is undefined
at time `1`. -/
theorem not_isGeodesicallyCompleteAt_iff_exists_one_notMem_geodesicInterval {p : M} :
    ¬ IsGeodesicallyCompleteAt I M p ↔
      ∃ v : TangentSpace I p, (1 : ℝ) ∉ geodesicInterval I M p v := by
  simpa only [not_forall] using
    (isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval (I := I) (M := M)
      (p := p)).not

end TauCeti.Manifold

end
