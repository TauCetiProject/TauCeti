/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Constant speed of geodesics

A geodesic has constant speed on every preconnected parameter set, and hence on each connected
component of an arbitrary parameter set. We first prove that the inner product of its within-set
velocity with itself is constant, by differentiating it with the within-set metric-product rule
and using the geodesic equation. Taking square roots gives the usual
constant-speed statement. On an open set this velocity agrees with the unrestricted
`curveVelocity` by `curveVelocityWithin_of_mem_nhds`; the all-time specializations below are stated
directly with `curveVelocity`.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq`: squared speed is constant
  on a preconnected parameter set.
* `TauCeti.Manifold.IsGeodesicCurveOn.norm_curveVelocityWithin_eq`: speed is constant there.
* `TauCeti.Manifold.IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq_of_mem_connectedComponentIn`
  and `TauCeti.Manifold.IsGeodesicCurveOn.norm_curveVelocityWithin_eq_of_mem_connectedComponentIn`:
  on an arbitrary parameter set, squared speed and speed are constant on each connected
  component.
* `TauCeti.Manifold.IsGeodesicCurveOn.energy_eq`: the energy of a geodesic segment is
  `(b - a) ‖γ'(a)‖² / 2`.
* `TauCeti.Manifold.IsGeodesicCurve.inner_curveVelocity_self_eq`: an all-time geodesic has the
  same squared speed at any two parameters.
* `TauCeti.Manifold.IsGeodesicCurve.norm_curveVelocity_eq`: an all-time geodesic has the same
  speed at any two parameters.
* `TauCeti.Manifold.inner_curveVelocity_maximalGeodesic_self`: the squared speed of a maximal
  geodesic is that of its initial velocity.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Constant speed".
* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, §2.
* The proof follows the organization of
  `DoCarmoLib/Riemannian/Geodesic/HopfRinow/ConstantSpeed.lean` in the Apache-2.0
  [frenzymath/Poincare-Conjecture](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision 24f32e4d600878bfaac6bc2f2f9324175571c321, using Tau Ceti's
  set-aware geodesic predicate and Mathlib's Riemannian norm.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ}

/-- Squared speed is constant along a geodesic. On a preconnected parameter set, the inner product
of the within-set velocity with itself has the same value at every two parameters. On an open set
this velocity agrees with the unrestricted `curveVelocity` by
`curveVelocityWithin_of_mem_nhds`. -/
theorem IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq
    (h : IsGeodesicCurveOn I γ s) (hconn : IsPreconnected s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) =
      inner ℝ (curveVelocityWithin I γ s b) (curveVelocityWithin I γ s b) := by
  have hmetric := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  apply hconn.ordConnected.convex.is_const_of_fderivWithin_eq_zero
    (𝕜 := ℝ)
    (f := fun t : ℝ ↦
      inner ℝ (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t))
  · intro t ht
    have hcoord := differentiableWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn
      h.contMDiffOn ht (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    exact hmetric.differentiableWithinAt_inner (h.uniqueDiffOn t ht)
      (h.mdifferentiableOn t ht) hcoord hcoord
  · intro t ht
    have hcoord := differentiableWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn
      h.contMDiffOn ht (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    have hprod := hmetric.hasDerivWithinAt_inner_alongCurveWithin (h.uniqueDiffOn t ht)
      (h.mdifferentiableOn t ht) hcoord hcoord
    have hderiv : HasDerivWithinAt (fun r ↦
        inner ℝ (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r)) 0 s t :=
      hprod.congr_deriv (by
        rw [h.alongCurveWithin_curveVelocityWithin_eq_zero t ht]
        simp)
    simpa using hderiv.hasFDerivWithinAt.fderivWithin (h.uniqueDiffOn t ht)
  · exact ha
  · exact hb

/-- A geodesic has constant speed. On a preconnected parameter set, the norm of its within-set
velocity has the same value at every two parameters. On an open set this velocity agrees with the
unrestricted `curveVelocity` by `curveVelocityWithin_of_mem_nhds`. -/
theorem IsGeodesicCurveOn.norm_curveVelocityWithin_eq
    (h : IsGeodesicCurveOn I γ s) (hconn : IsPreconnected s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖curveVelocityWithin I γ s a‖ = ‖curveVelocityWithin I γ s b‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    h.inner_curveVelocityWithin_self_eq hconn ha hb]

/-- Squared speed is constant on each connected component of the parameter set: without
preconnectedness, two parameters in the same connected component of `s` give the within-set
velocity the same inner product with itself. -/
theorem IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq_of_mem_connectedComponentIn
    (h : IsGeodesicCurveOn I γ s) {a b : ℝ} (hb : b ∈ connectedComponentIn s a) :
    inner ℝ (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) =
      inner ℝ (curveVelocityWithin I γ s b) (curveVelocityWithin I γ s b) := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  -- the component is an interval of `ℝ`, so it contains the nondegenerate segment `[a, b]`;
  -- restrict to that segment, where the velocity is unchanged, and use the preconnected case
  have ha : a ∈ connectedComponentIn s a :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp ⟨b, hb⟩)
  have hsub : uIcc a b ⊆ s :=
    (isPreconnected_connectedComponentIn.ordConnected.uIcc_subset ha hb).trans
      (connectedComponentIn_subset s a)
  have hu : UniqueDiffOn ℝ (uIcc a b) := uniqueDiffOn_Icc (inf_lt_sup.mpr hab)
  have hvel {t : ℝ} (ht : t ∈ uIcc a b) :
      curveVelocityWithin I γ s t = curveVelocityWithin I γ (uIcc a b) t :=
    (curveVelocityWithin_subset hsub (hu t ht) (h.mdifferentiableOn t (hsub ht))).symm
  rw [hvel left_mem_uIcc, hvel right_mem_uIcc]
  exact (h.mono hu hsub).inner_curveVelocityWithin_self_eq isPreconnected_uIcc left_mem_uIcc
    right_mem_uIcc

/-- A geodesic has constant speed on each connected component of its parameter set: two
parameters in the same connected component of `s` give within-set velocities of the same
norm. -/
theorem IsGeodesicCurveOn.norm_curveVelocityWithin_eq_of_mem_connectedComponentIn
    (h : IsGeodesicCurveOn I γ s) {a b : ℝ} (hb : b ∈ connectedComponentIn s a) :
    ‖curveVelocityWithin I γ s a‖ = ‖curveVelocityWithin I γ s b‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    h.inner_curveVelocityWithin_self_eq_of_mem_connectedComponentIn hb]

/-- **The energy of a geodesic segment.** A geodesic has constant speed, so its energy between
`a` and `b` is `(b - a) ‖γ'(a)‖² / 2`. -/
theorem IsGeodesicCurveOn.energy_eq (h : IsGeodesicCurveOn I γ s)
    (hs : IsOpen s) {a b : ℝ} (hsub : uIcc a b ⊆ s) :
    energy I γ a b = (b - a) * ‖curveVelocity I γ a‖ ^ 2 / 2 := by
  have key : EqOn (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) (fun _ ↦ ‖curveVelocity I γ a‖ ^ 2)
      (uIcc a b) := by
    intro t ht
    have ht' : t ∈ connectedComponentIn s a :=
      isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hsub ht
    simp only
    rw [← curveVelocityWithin_of_mem_nhds (hs.mem_nhds (hsub ht)),
      ← curveVelocityWithin_of_mem_nhds (hs.mem_nhds (hsub left_mem_uIcc)),
      h.norm_curveVelocityWithin_eq_of_mem_connectedComponentIn ht']
  rw [energy_def, intervalIntegral.integral_congr key, intervalIntegral.integral_const,
    smul_eq_mul]

/-- An all-time geodesic has the same squared speed, expressed using the unrestricted
`curveVelocity`, at every two parameters. -/
theorem IsGeodesicCurve.inner_curveVelocity_self_eq
    (h : IsGeodesicCurve I γ) (a b : ℝ) :
    inner ℝ (curveVelocity I γ a) (curveVelocity I γ a) =
      inner ℝ (curveVelocity I γ b) (curveVelocity I γ b) := by
  simpa only [curveVelocityWithin_univ] using
    IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq
      ((isGeodesicCurveOn_univ (I := I) (γ := γ)).mpr h) isPreconnected_univ
      (Set.mem_univ a) (Set.mem_univ b)

/-- An all-time geodesic has the same speed, expressed using the unrestricted `curveVelocity`, at
every two parameters. -/
theorem IsGeodesicCurve.norm_curveVelocity_eq
    (h : IsGeodesicCurve I γ) (a b : ℝ) :
    ‖curveVelocity I γ a‖ = ‖curveVelocity I γ b‖ := by
  simpa only [curveVelocityWithin_univ] using
    IsGeodesicCurveOn.norm_curveVelocityWithin_eq
      ((isGeodesicCurveOn_univ (I := I) (γ := γ)).mpr h) isPreconnected_univ
      (Set.mem_univ a) (Set.mem_univ b)

end TauCeti.Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The squared speed of a maximal geodesic equals the squared norm of its initial velocity at
every point of its maximal interval. -/
theorem inner_curveVelocity_maximalGeodesic_self [T2Space (TangentBundle I M)]
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    inner ℝ (curveVelocity I (maximalGeodesic I M p v) t)
        (curveVelocity I (maximalGeodesic I M p v) t) = inner ℝ v v := by
  have hgeo := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  have hsquared := hgeo.isGeodesicCurveOn.inner_curveVelocityWithin_self_eq
    isPreconnected_geodesicInterval ht zero_mem_geodesicInterval
  have ht_nhds := isOpen_geodesicInterval.mem_nhds ht
  have hzero_nhds := isOpen_geodesicInterval.mem_nhds
    (zero_mem_geodesicInterval (I := I) (M := M) (p := p) (v := v))
  rw [curveVelocityWithin_of_mem_nhds ht_nhds,
    curveVelocityWithin_of_mem_nhds hzero_nhds] at hsquared
  have hinitial := congrArg (fun z : TangentBundle I M ↦ inner ℝ z.2 z.2) hgeo.initial_eq
  rw [curveVelocityWithin_of_mem_nhds hzero_nhds] at hinitial
  exact hsquared.trans hinitial

end TauCeti.Manifold

end
