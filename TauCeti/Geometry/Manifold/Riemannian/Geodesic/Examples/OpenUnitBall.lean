/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Examples.OpenUnitBall
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow
import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Geodesics of the real open unit ball

The Euclidean metric restricted to the open unit ball in `ℝ` is an example where every point
is joined to the centre by a minimizing geodesic, but geodesics cannot all be continued
indefinitely, and the space is neither complete nor proper.

Abstractly, some initial velocity at each point has a maximal geodesic whose domain does not
contain time `1`; this follows from the Hopf–Rinow equivalence and the failure of metric
completeness proved in `TauCeti.RealOpenUnitBall.not_completeSpace`. The geodesics can also be
computed. A geodesic has constant speed, so in the coordinate of `ℝ` it is an affine line
`t ↦ p + t * v` on its maximal interval. Conversely, the geodesic runs along this line for as
long as the line stays in the ball: at a finite endpoint of its maximal interval inside the ball,
it would stay in a compact set, contradicting the escape lemma
`TauCeti.Manifold.eventually_notMem_nhdsLT_maximalGeodesic`. In particular a unit-speed geodesic
from the centre is defined exactly on `(-1, 1)` and reaches the missing boundary in finite time.

## Main results

* `TauCeti.RealOpenUnitBall.not_isGeodesicallyCompleteAt`: the open unit ball is not
  geodesically complete at any point.
* `TauCeti.RealOpenUnitBall.coe_maximalGeodesic`: on its maximal interval, a maximal geodesic
  is the affine line `t ↦ p + t * v`.
* `TauCeti.RealOpenUnitBall.geodesicInterval_eq`: the maximal interval is the set of times at
  which that line stays in the ball.
* `TauCeti.RealOpenUnitBall.geodesicInterval_center_of_norm_eq_one` and
  `TauCeti.RealOpenUnitBall.tendsto_abs_coe_maximalGeodesic_center`: a unit-speed geodesic from
  the centre is defined exactly on `(-1, 1)` and tends to the boundary as `t → 1⁻`.
* `TauCeti.RealOpenUnitBall.isGeodesicCurveOn_radialSegment`: the radial segment from the centre
  is a geodesic on `[0, 1]`.
* `TauCeti.RealOpenUnitBall.exists_isGeodesicCurveOn_Icc_pathELength_eq_edist`: every point is
  joined to the centre by a geodesic on `[0, 1]` realizing the distance, although the space is
  not proper.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2 (the open-ball example
  of an incomplete Riemannian manifold).
-/
public section

open Bundle Filter Manifold Set TauCeti.Manifold
open scoped Manifold TauCeti Topology

noncomputable section

namespace TauCeti.RealOpenUnitBall

/-- The open unit ball is not geodesically complete at any point: an initial velocity there
has a maximal geodesic that cannot be extended to all real times. -/
theorem not_isGeodesicallyCompleteAt (p : realOpenUnitBall) :
    ¬ Manifold.IsGeodesicallyCompleteAt 𝓘(ℝ, ℝ) realOpenUnitBall p := by
  intro h
  exact not_completeSpace
    ((Manifold.completeSpace_iff_isGeodesicallyCompleteAt (I := 𝓘(ℝ, ℝ)) p).2 h)

/-- Some maximal geodesic starting at any point of the open unit ball is undefined at time
`1`. -/
theorem exists_one_notMem_geodesicInterval (p : realOpenUnitBall) :
    ∃ v : TangentSpace 𝓘(ℝ, ℝ) p,
      (1 : ℝ) ∉ Manifold.geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v := by
  exact (Manifold.not_isGeodesicallyCompleteAt_iff_exists_one_notMem_geodesicInterval
    (I := 𝓘(ℝ, ℝ)) (M := realOpenUnitBall)).mp (not_isGeodesicallyCompleteAt p)

/-! ### The geodesics of the open unit ball -/

/-- Read in the coordinate of `ℝ`, a curve in the open unit ball has its velocity as derivative. -/
private theorem hasDerivAt_coe {γ : ℝ → realOpenUnitBall} {s : Set ℝ} {t : ℝ} (hs : s ∈ 𝓝 t)
    (hγ : MDiffAt γ t) :
    HasDerivAt (fun r ↦ (γ r : ℝ)) (NormedSpace.fromTangentSpace (γ t : ℝ)
      (tangentSpaceOpenEquiv (γ t) (curveVelocityWithin 𝓘(ℝ, ℝ) γ s t))) t := by
  have hval : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : realOpenUnitBall → ℝ) (γ t)
      (tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℝ)) (γ t)).toContinuousLinearMap := by
    rw [← mfderiv_subtype_val]
    exact (contMDiff_subtype_val.mdifferentiableAt one_ne_zero).hasMFDerivAt
  have h := hasMFDerivAt_iff_hasFDerivAt.1 (hval.comp t (hasMFDerivAt_curveVelocity hγ))
  rw [curveVelocityWithin_of_mem_nhds hs, hasDerivAt_iff_hasFDerivAt]
  refine h.congr_fderiv (ContinuousLinearMap.ext_ring ?_)
  -- Both sides are `1 • w` for the velocity `w`, once the tangent spaces are read as `ℝ`. The
  -- goal composes maps out of `TangentSpace 𝓘(ℝ, ℝ) t` with maps out of `ℝ`, so it is type-correct
  -- only up to the definitional identification `TangentSpace 𝓘(ℝ, ℝ) t = ℝ`: `rw` with
  -- `ContinuousLinearMap.comp_apply` fails on it (instance mismatch), and `simp` only removes
  -- `tangentSpaceOpenEquiv`. The `change` states it in a type-correct form. The final `rfl` is
  -- needed because Mathlib's `NormedSpace.fromTangentSpace` is the identity by definition and has
  -- no application lemma, so no rewrite lemma can remove it.
  change tangentSpaceOpenEquiv (γ t) ((1 : ℝ) • curveVelocity 𝓘(ℝ, ℝ) γ t) =
    (1 : ℝ) • NormedSpace.fromTangentSpace (γ t : ℝ)
      (tangentSpaceOpenEquiv (γ t) (curveVelocity 𝓘(ℝ, ℝ) γ t))
  rw [one_smul, one_smul]
  rfl

variable (p : realOpenUnitBall) (v : TangentSpace 𝓘(ℝ, ℝ) p)

/-- On its maximal interval, the maximal geodesic of the open unit ball from `p` with initial
velocity `v` is the affine line `t ↦ p + t * v`, read in the coordinate of `ℝ`. -/
theorem coe_maximalGeodesic {t : ℝ} (ht : t ∈ geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v) :
    (maximalGeodesic 𝓘(ℝ, ℝ) realOpenUnitBall p v t : ℝ) =
      p + t * NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p v) := by
  set J := geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v
  set γ := maximalGeodesic 𝓘(ℝ, ℝ) realOpenUnitBall p v
  set c := NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p v)
  have hγ := isGeodesicCurveOnFrom_maximalGeodesic (I := 𝓘(ℝ, ℝ)) (M := realOpenUnitBall) p v
  have hJ : IsOpen J := isOpen_geodesicInterval
  -- The coordinate `f` of the geodesic is `C²`, with derivative the coordinate of its velocity.
  set f : ℝ → ℝ := fun r ↦ (γ r : ℝ)
  have hf : ContDiffOn ℝ 2 f J :=
    (contMDiff_subtype_val.comp_contMDiffOn hγ.isGeodesicCurveOn.contMDiffOn).contDiffOn
  have hderiv (s : ℝ) (hs : s ∈ J) : HasDerivAt f (NormedSpace.fromTangentSpace (γ s : ℝ)
      (tangentSpaceOpenEquiv (γ s) (curveVelocityWithin 𝓘(ℝ, ℝ) γ J s))) s :=
    hasDerivAt_coe (hJ.mem_nhds hs)
      ((hγ.isGeodesicCurveOn.mdifferentiableOn s hs).mdifferentiableAt (hJ.mem_nhds hs))
  -- By constant speed, the derivative of `f` has absolute value `|c|` on `J`.
  have habs (s : ℝ) (hs : s ∈ J) : |deriv f s| = |c| := by
    rw [(hderiv s hs).deriv, ← Real.norm_eq_abs, ← Real.norm_eq_abs,
      ← norm_tangentSpace_vectorSpace, ← norm_tangentSpace_open, ← norm_tangentSpace_vectorSpace,
      ← norm_tangentSpace_open]
    exact norm_curveVelocityWithin_maximalGeodesic hs
  have h0 : deriv f 0 = c := by
    rw [(hderiv 0 zero_mem_geodesicInterval).deriv]
    exact congrArg (fun z : TangentBundle 𝓘(ℝ, ℝ) realOpenUnitBall ↦
      NormedSpace.fromTangentSpace (z.proj : ℝ) (tangentSpaceOpenEquiv z.proj z.2))
      hγ.initial_eq
  -- A continuous function of constant absolute value on an interval is constant.
  have hconst : EqOn (deriv f) (fun _ ↦ c) J := by
    rcases eq_or_ne c 0 with hc | hc
    · intro s hs
      simpa [hc] using habs s hs
    exact isPreconnected_geodesicInterval.eq_of_sq_eq (hf.continuousOn_deriv_of_isOpen hJ
      (by norm_num)) continuousOn_const (fun s hs ↦ by simp [← sq_abs, habs s hs])
      (fun _ ↦ hc) zero_mem_geodesicInterval h0
  have hline (s : ℝ) : HasDerivAt (fun r : ℝ ↦ (p : ℝ) + r * c) c s := by
    simpa using ((hasDerivAt_id s).mul_const c).const_add (p : ℝ)
  refine hJ.eqOn_of_deriv_eq isPreconnected_geodesicInterval
    (fun s hs ↦ (hderiv s hs).differentiableAt.differentiableWithinAt)
    (fun s _ ↦ (hline s).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hconst hs).trans (hline s).deriv.symm) zero_mem_geodesicInterval ?_ ht
  simp [f, γ, maximalGeodesic_zero]

/-- If the affine line `t ↦ p + t * v` stays in the open unit ball up to a time `t ≥ 0`, then the
maximal geodesic with initial data `(p, v)` is defined at time `t`. -/
private theorem mem_geodesicInterval_of_nonneg {t : ℝ} (ht0 : 0 ≤ t)
    (ht : |(p : ℝ) + t * NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p v)| < 1) :
    t ∈ geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v := by
  set J := geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v
  set c := NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p v)
  by_contra htJ
  -- Otherwise the maximal interval is bounded above by `t`; let `b ≤ t` be its supremum.
  have hub : t ∈ upperBounds J := fun s hs ↦ le_of_not_ge fun hts ↦
    htJ (ordConnected_geodesicInterval.out zero_mem_geodesicInterval hs ⟨ht0, hts⟩)
  have hlub := isLUB_csSup ⟨0, zero_mem_geodesicInterval⟩ ⟨t, hub⟩
  have hbt : sSup J ≤ t := hlub.2 hub
  obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isLUB hlub
  -- The segment of the line over `[0, b]` is a compact subset of the open unit ball.
  set S := (fun s : ℝ ↦ (p : ℝ) + s * c) '' Icc 0 (sSup J)
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSU : S ⊆ range (Subtype.val : realOpenUnitBall → ℝ) := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨_, mem_iff.2 ?_⟩, rfl⟩
    -- The line is inside the ball at times `0` and `t`, hence at every time in between.
    have hp := abs_lt.1 (mem_iff.1 p.2)
    have ht' := abs_lt.1 ht
    have hst : s ≤ t := hs.2.trans hbt
    rw [abs_lt]
    rcases le_total 0 c with hc | hc
    · constructor <;> nlinarith [mul_le_mul_of_nonneg_right hst hc, mul_nonneg hs.1 hc]
    · constructor <;>
        nlinarith [mul_le_mul_of_nonpos_right hst hc, mul_nonpos_of_nonneg_of_nonpos hs.1 hc]
  have hC : IsCompact ((Subtype.val : realOpenUnitBall → ℝ) ⁻¹' S) :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff hSU).2 hS
  -- By the escape lemma the geodesic leaves this compact set before time `b`, but it runs along it.
  obtain ⟨s, hsC, hs⟩ :=
    ((eventually_notMem_nhdsLT_maximalGeodesic hlub hC).and (Ioo_mem_nhdsLT hb0)).exists
  apply hsC
  rw [mem_preimage, coe_maximalGeodesic p v (hsub ⟨ha.trans hs.1, hs.2⟩)]
  exact ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩

/-- **The maximal interval of a geodesic in the open unit ball** is the set of times at which the
affine line `t ↦ p + t * v` stays in the ball. -/
theorem geodesicInterval_eq :
    geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall p v =
      {t | |(p : ℝ) + t * NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p v)| <
        1} := by
  ext t
  constructor
  · intro ht
    rw [mem_ofPred_eq, ← coe_maximalGeodesic p v ht]
    exact mem_iff.1 (maximalGeodesic 𝓘(ℝ, ℝ) realOpenUnitBall p v t).2
  · intro ht
    rcases le_total 0 t with h | h
    · exact mem_geodesicInterval_of_nonneg p v h ht
    · -- Negative times are positive times for the reversed initial velocity `-v`.
      have hc : NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p ((-1 : ℝ) • v)) =
          -NormedSpace.fromTangentSpace (p : ℝ) (tangentSpaceOpenEquiv p v) := by
        rw [ContinuousLinearEquiv.map_smul, ContinuousLinearEquiv.map_smul, neg_one_smul]
      have hneg := mem_geodesicInterval_of_nonneg p ((-1 : ℝ) • v) (neg_nonneg.2 h)
        (by rwa [hc, neg_mul_neg])
      rw [mem_geodesicInterval_smul_iff (by norm_num)] at hneg
      simpa using hneg

/-- From the centre of the open unit ball, a unit-speed geodesic is defined exactly for times in
`(-1, 1)`. -/
theorem geodesicInterval_center_of_norm_eq_one {v : TangentSpace 𝓘(ℝ, ℝ) center} (hv : ‖v‖ = 1) :
    geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall center v = Ioo (-1) 1 := by
  rw [geodesicInterval_eq]
  set c := NormedSpace.fromTangentSpace (center : ℝ) (tangentSpaceOpenEquiv center v)
  have hc : |c| = 1 := by
    rw [← hv, norm_tangentSpace_open, norm_tangentSpace_vectorSpace, Real.norm_eq_abs]
  ext t
  simp only [mem_ofPred_eq, mem_Ioo, coe_center, zero_add, abs_mul, hc, mul_one, abs_lt]

/-- **A unit-speed geodesic from the centre reaches the missing boundary in finite time**: as
`t → 1⁻`, the end of its maximal interval, its coordinate tends to the boundary of the ball. -/
theorem tendsto_abs_coe_maximalGeodesic_center {v : TangentSpace 𝓘(ℝ, ℝ) center}
    (hv : ‖v‖ = 1) :
    Tendsto (fun t ↦ |(maximalGeodesic 𝓘(ℝ, ℝ) realOpenUnitBall center v t : ℝ)|) (𝓝[<] 1)
      (𝓝 1) := by
  set c := NormedSpace.fromTangentSpace (center : ℝ) (tangentSpaceOpenEquiv center v)
  have hc : |c| = 1 := by
    rw [← hv, norm_tangentSpace_open, norm_tangentSpace_vectorSpace, Real.norm_eq_abs]
  refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
  have htJ : t ∈ geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall center v := by
    rw [geodesicInterval_center_of_norm_eq_one hv]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hγ : (maximalGeodesic 𝓘(ℝ, ℝ) realOpenUnitBall center v t : ℝ) = center + t * c :=
    coe_maximalGeodesic center v htJ
  rw [hγ, coe_center, zero_add, abs_mul, hc, mul_one, abs_of_pos ht.1, id]

/-- The radial segment from the centre to `q` is a geodesic on `[0, 1]`. -/
theorem isGeodesicCurveOn_radialSegment (q : realOpenUnitBall) :
    IsGeodesicCurveOn 𝓘(ℝ, ℝ) (radialSegment q) (Icc 0 1) := by
  set v : TangentSpace 𝓘(ℝ, ℝ) center := (tangentSpaceOpenEquiv center).symm
    ((NormedSpace.fromTangentSpace (center : ℝ)).symm q)
  have hc : NormedSpace.fromTangentSpace (center : ℝ) (tangentSpaceOpenEquiv center v) = q := by
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hJ : Icc 0 1 ⊆ geodesicInterval 𝓘(ℝ, ℝ) realOpenUnitBall center v := by
    intro t ht
    rw [geodesicInterval_eq, mem_ofPred_eq, hc, coe_center, zero_add, abs_mul,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt (mem_iff.1 q.2)
  refine ((isGeodesicCurveOnFrom_maximalGeodesic center v).isGeodesicCurveOn.mono
    (uniqueDiffOn_Icc zero_lt_one) hJ).congr fun t ht ↦ Subtype.ext ?_
  rw [coe_radialSegment q t ht, coe_maximalGeodesic center v (hJ ht), hc, coe_center, zero_add]

/-- Every point `q` of the open unit ball is joined to the centre by a geodesic on `[0, 1]` whose
length is the distance from the centre to `q`. Since the open unit ball is not proper
(`not_properSpace`), minimizing geodesics from one point do not by themselves imply properness. -/
theorem exists_isGeodesicCurveOn_Icc_pathELength_eq_edist (q : realOpenUnitBall) :
    ∃ γ : ℝ → realOpenUnitBall, IsGeodesicCurveOn 𝓘(ℝ, ℝ) γ (Icc 0 1) ∧ γ 0 = center ∧
      γ 1 = q ∧ pathELength 𝓘(ℝ, ℝ) γ 0 1 = edist center q :=
  ⟨radialSegment q, isGeodesicCurveOn_radialSegment q, radialSegment_zero q, radialSegment_one q,
    pathELength_radialSegment q⟩

end TauCeti.RealOpenUnitBall

end
