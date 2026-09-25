/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
import TauCeti.Geometry.Manifold.IntegralCurve.Flow
import TauCeti.Geometry.Manifold.LocalDiffeomorph
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
at `0`.  Smooth dependence of the maximal geodesic flow shows that this domain is open and that
the exponential map is smooth there.  Its differential at the origin is the identity of `T_p M`,
once the tangent space to `T_p M` at `0` is identified with `T_p M` itself by
`NormedSpace.fromTangentSpace`; by the inverse function theorem the exponential map is therefore
a local diffeomorphism at `0`, the input to normal neighbourhoods.  Finally, the domain is all of
`T_p M` exactly when every geodesic leaving `p` is defined for all time.

## Main definitions and results

* `TauCeti.Manifold.expDomain`: the natural domain of the exponential map at `p`.
* `TauCeti.Manifold.riemannianExp`: the exponential map at `p`.
* `TauCeti.Manifold.IsGeodesicallyCompleteAt`: every geodesic leaving `p` is defined for all time.
* `TauCeti.Manifold.mem_geodesicInterval_iff_smul_mem_expDomain`: the maximal interval of `v` is
  the set of times `t` with `t • v` in the domain.
* `TauCeti.Manifold.riemannianExp_smul`: `exp_p (t • v)` is the maximal geodesic at time `t`,
  on and off its natural interval (where both sides take the junk value).
* `TauCeti.Manifold.starConvex_expDomain`: the domain is star-shaped at `0`.
* `TauCeti.Manifold.isOpen_expDomain`: the natural domain is open.
* `TauCeti.Manifold.contMDiffOn_riemannianExp`: the exponential map is smooth on its domain.
* `TauCeti.Manifold.curveVelocity_riemannianExp_add_smul` and
  `TauCeti.Manifold.curveVelocity_riemannianExp_smul`: velocities of affine and radial curves
  through the exponential map.
* `TauCeti.Manifold.mfderiv_riemannianExp_zero`: the differential of the exponential map at `0`
  is the identity.
* `TauCeti.Manifold.norm_mfderiv_riemannianExp_zero`: in particular it preserves norms.
* `TauCeti.Manifold.isLocalDiffeomorphAt_riemannianExp_zero`: the exponential map is a local
  diffeomorphism at `0`.
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

variable [FiniteDimensional ℝ E] [I.Boundaryless]
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

omit [I.Boundaryless] in
/-- A tangent vector lies in the domain of the exponential map exactly when its maximal geodesic
interval contains `1`. -/
@[simp] theorem mem_expDomain_iff {p : M} {v : TangentSpace I p} :
    v ∈ expDomain I M p ↔ (1 : ℝ) ∈ geodesicInterval I M p v :=
  Iff.rfl

omit [I.Boundaryless] in
/-- The exponential map is the maximal geodesic evaluated at time `1`. -/
theorem riemannianExp_def (p : M) (v : TangentSpace I p) :
    riemannianExp I M p v = maximalGeodesic I M p v 1 := by
  rfl

omit [I.Boundaryless] in
/-- The zero vector lies in the domain of the exponential map. -/
theorem zero_mem_expDomain (p : M) : (0 : TangentSpace I p) ∈ expDomain I M p := by
  simp only [mem_expDomain_iff, geodesicInterval_zero, mem_univ]

/-- The exponential map sends the zero vector to the base point. -/
@[simp] theorem riemannianExp_zero [T2Space (TangentBundle I M)] (p : M) :
    riemannianExp I M p 0 = p := by
  simp [riemannianExp_def]

/-- Outside its natural domain, the exponential map takes its junk value `p`. -/
@[simp] theorem riemannianExp_of_notMem_expDomain {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain I M p) : riemannianExp I M p v = p :=
  maximalGeodesic_eq_of_not_mem (mt mem_expDomain_iff.2 hv)

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
theorem riemannianExp_smul [T2Space (TangentBundle I M)]
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    riemannianExp I M p (t • v) = maximalGeodesic I M p v t := by
  by_cases ht : t ∈ geodesicInterval I M p v
  · have h1 : (1 : ℝ) ∈ geodesicInterval I M p (t • v) :=
      mem_expDomain_iff.1 (mem_geodesicInterval_iff_smul_mem_expDomain.1 ht)
    rw [riemannianExp_def, maximalGeodesic_smul h1, mul_one]
  · rw [riemannianExp_of_notMem_expDomain
        (mt mem_geodesicInterval_iff_smul_mem_expDomain.mpr ht),
      maximalGeodesic_eq_of_not_mem ht]

/-- The domain of the exponential map is star-shaped at the zero vector. -/
theorem starConvex_expDomain (p : M) : StarConvex ℝ (0 : TangentSpace I p) (expDomain I M p) := by
  intro v hv a b _ hb hab
  rw [smul_zero, zero_add, ← mem_geodesicInterval_iff_smul_mem_expDomain]
  have hb1 : b ≤ 1 := by linarith
  exact ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
    ⟨hb, hb1⟩

/-! ### Regularity -/

/-- Each tangent space is a charted space over itself (via the identity chart), so that
smoothness of maps out of a tangent space can be stated in the manifold API. -/
local instance tangentSpaceChartedSpace (p : M) :
    ChartedSpace (TangentSpace I p) (TangentSpace I p) :=
  chartedSpaceSelf (TangentSpace I p)

/-- The domain of the exponential map at `p` is the slice at time `1` of the maximal flow domain
of the geodesic spray over the fibre `T_p M`. -/
private theorem expDomain_eq_preimage_maximalIntegralCurveFlowDomain (p : M) :
    expDomain I M p = (fun v : TangentSpace I p ↦ (TotalSpace.mk' E p v, (1 : ℝ))) ⁻¹'
      maximalIntegralCurveFlowDomain (geodesicSpray I M) := by
  ext v
  simp only [mem_expDomain_iff, mem_preimage, mem_maximalIntegralCurveFlowDomain,
    maximalIntegralCurveInterval_geodesicSpray]

/-- The natural domain of the Riemannian exponential map is open. -/
theorem isOpen_expDomain [T2Space (TangentBundle I M)] (p : M) :
    IsOpen (expDomain I M p) := by
  have hspray : ContMDiff I.tangent I.tangent.tangent 1
      (fun z : TangentBundle I M ↦
        (⟨z, geodesicSpray I M z⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    (contMDiff_geodesicSpray (I := I) (M := M) (n := (1 : ℕ∞ω))
      (m := ∞) (k := ∞) (by norm_num) (by norm_num)).of_le (by norm_num)
  have hinitial : Continuous
      (fun v : TangentSpace I p ↦ TotalSpace.mk' E p v) :=
    FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p
  have hinput : Continuous (fun v : TangentSpace I p ↦
      (TotalSpace.mk' E p v, (1 : ℝ))) :=
    hinitial.prodMk continuous_const
  have hflow : IsOpen (maximalIntegralCurveFlowDomain (geodesicSpray I M)) :=
    isOpen_maximalIntegralCurveFlowDomain hspray
  rw [expDomain_eq_preimage_maximalIntegralCurveFlowDomain]
  exact hflow.preimage hinput

/-- The Riemannian exponential map is smooth on its natural domain. -/
theorem contMDiffOn_riemannianExp [T2Space (TangentBundle I M)] (p : M) :
    ContMDiffOn 𝓘(ℝ, TangentSpace I p) I ∞
      (riemannianExp I M p) (expDomain I M p) := by
  have hspray : ContMDiff I.tangent I.tangent.tangent ∞
      (fun z : TangentBundle I M ↦
        (⟨z, geodesicSpray I M z⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    contMDiff_geodesicSpray (I := I) (M := M) (n := ∞)
      (m := ∞) (k := ∞) (by simp) (by simp)
  have hinitial : ContMDiff 𝓘(ℝ, TangentSpace I p) I.tangent ∞
      (fun v : TangentSpace I p ↦ TotalSpace.mk' E p v) :=
    contMDiff_tangentBundle_mk_constBase (I := I) (M := M) (n := ∞)
      ((tangentSpaceCastModel I p).toContinuousLinearMap.contMDiff (n := ∞)) p
  have hinput : ContMDiff 𝓘(ℝ, TangentSpace I p)
      (I.tangent.prod 𝓘(ℝ, ℝ)) ∞
      (fun v : TangentSpace I p ↦ (TotalSpace.mk' E p v, (1 : ℝ))) :=
    hinitial.prodMk contMDiff_const
  have hflow := contMDiffOn_maximalIntegralCurve (I := I.tangent) (n := (⊤ : ℕ∞))
    (by simp) hspray
  have hstate : ContMDiffOn 𝓘(ℝ, TangentSpace I p) I.tangent ∞
      (fun v : TangentSpace I p ↦ maximalIntegralCurve (geodesicSpray I M)
        (TotalSpace.mk' E p v) 1) (expDomain I M p) := by
    apply hflow.comp hinput.contMDiffOn
    rw [← expDomain_eq_preimage_maximalIntegralCurveFlowDomain]
  have hbase := (Bundle.contMDiff_proj
    (fun x : M ↦ TangentSpace I x) (n := ∞)).comp_contMDiffOn hstate
  exact hbase.congr fun v _ ↦ by
    simp only [Function.comp_apply, riemannianExp_def, maximalGeodesic_def]

/-- The Riemannian exponential map is continuous on its natural domain. -/
theorem continuousOn_riemannianExp [T2Space (TangentBundle I M)] (p : M) :
    ContinuousOn (riemannianExp I M p) (expDomain I M p) :=
  (contMDiffOn_riemannianExp (I := I) (M := M) p).continuousOn

/-- The Riemannian exponential map is smooth at every point of its natural domain. -/
theorem contMDiffAt_riemannianExp [T2Space (TangentBundle I M)] {p : M}
    {v : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    ContMDiffAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) v :=
  (contMDiffOn_riemannianExp (I := I) (M := M) p v hv).contMDiffAt
    (isOpen_expDomain (I := I) (M := M) p |>.mem_nhds hv)

/-- The velocity of the exponential image of a path is the differential of the exponential map
applied to the derivative of the path in the tangent space. -/
theorem curveVelocity_riemannianExp_comp [T2Space (TangentBundle I M)]
    {p : M} {w : ℝ → TangentSpace I p} {w' : TangentSpace I p} {t : ℝ}
    (hw : HasDerivAt w w' t) (hwt : w t ∈ expDomain I M p) :
    curveVelocity I (riemannianExp I M p ∘ w) t =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (w t) w' :=
  ((contMDiffAt_riemannianExp hwt).mdifferentiableAt (by simp)).curveVelocity_comp_mfderiv hw

/-- The velocity of an affine curve through the exponential map is its differential in the
affine direction. -/
theorem curveVelocity_riemannianExp_add_smul [T2Space (TangentBundle I M)]
    {p : M} {v w : TangentSpace I p} {u : ℝ} (hu : v + u • w ∈ expDomain I M p) :
    curveVelocity I (fun s : ℝ ↦ riemannianExp I M p (v + s • w)) u =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (v + u • w) w := by
  have hg : HasDerivAt (fun s : ℝ ↦ v + s • w) w u := by
    simpa using (hasDerivAt_id u).smul_const w |>.const_add v
  exact curveVelocity_riemannianExp_comp (I := I) (M := M) hg hu

/-- The velocity of a radial curve through the exponential map is its differential in the
radial direction. -/
theorem curveVelocity_riemannianExp_smul [T2Space (TangentBundle I M)]
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
theorem continuousAt_riemannianExp [T2Space (TangentBundle I M)] {p : M}
    {v : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    ContinuousAt (riemannianExp I M p) v :=
  (contMDiffAt_riemannianExp (I := I) (M := M) hv).continuousAt

/-! ### The derivative at the origin -/

/-- **The differential of the exponential map at the origin** sends every tangent vector to
itself. -/
@[simp] theorem mfderiv_riemannianExp_apply_zero [T2Space (TangentBundle I M)] (p : M)
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

/-- At the origin, the differential of `exp_p` preserves the norm of every tangent vector. -/
@[simp] theorem norm_mfderiv_riemannianExp_zero [T2Space (TangentBundle I M)] (p : M)
    (v : TangentSpace I p) :
    ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 v‖ = ‖v‖ := by
  rw [mfderiv_riemannianExp_apply_zero, riemannianExp_zero]

/-- **The differential of the exponential map at the origin is the identity**, under the
canonical identification `NormedSpace.fromTangentSpace` of the tangent space to `T_p M` at `0`
with `T_p M`. -/
theorem mfderiv_riemannianExp_zero [T2Space (TangentBundle I M)] (p : M) :
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0 =
      (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).toContinuousLinearMap := by
  ext v
  exact mfderiv_riemannianExp_apply_zero (I := I) p v

/-- The exponential map has the identity of `T_p M` as its derivative at the origin. -/
theorem hasMFDerivAt_riemannianExp_zero [T2Space (TangentBundle I M)] (p : M) :
    HasMFDerivAt 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0
      (NormedSpace.fromTangentSpace (0 : TangentSpace I p)).toContinuousLinearMap := by
  rw [← mfderiv_riemannianExp_zero]
  exact ((contMDiffAt_riemannianExp (zero_mem_expDomain p)).mdifferentiableAt
    (by simp)).hasMFDerivAt

/-- In extended coordinates, the exponential map has the canonical identification
`T_p M →L[ℝ] E` as its strict derivative at the origin. -/
theorem hasStrictFDerivAt_riemannianExp_zero [T2Space (TangentBundle I M)] (p : M) :
    HasStrictFDerivAt
      (writtenInExtChartAt 𝓘(ℝ, TangentSpace I p) I 0 (riemannianExp I M p))
      (tangentSpaceCastModel I p).toContinuousLinearMap 0 := by
  have hsmooth := contMDiffAt_riemannianExp (I := I) (M := M) (zero_mem_expDomain p)
  have hcoord : ContDiffAt ℝ ∞
      (writtenInExtChartAt 𝓘(ℝ, TangentSpace I p) I 0 (riemannianExp I M p)) 0 := by
    have h := (contMDiffAt_iff.1 hsmooth).2.contDiffAt (by simp)
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.comp_id, Function.id_def, riemannianExp_zero] using h
  apply hcoord.hasStrictFDerivAt'
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
theorem isLocalDiffeomorphAt_riemannianExp_zero [T2Space (TangentBundle I M)] (p : M) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p) 0 :=
  isLocalDiffeomorphAt_of_mfderiv_eq (contMDiffOn_riemannianExp (I := I) p)
    (isOpen_expDomain (I := I) p) (zero_mem_expDomain (I := I) p)
    BoundarylessManifold.isInteriorPoint (by simp)
    (mfderiv_riemannianExp_zero (I := I) p).symm

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
  refine ⟨fun h v ↦ ?_, fun h ↦ eq_univ_of_forall fun v ↦ ?_⟩
  · rw [geodesicInterval_eq_preimage_expDomain, h, preimage_univ]
  · rw [mem_expDomain_iff, h v]
    exact mem_univ _

end TauCeti.Manifold

end
