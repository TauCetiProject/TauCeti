/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.ModelSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Geodesics and the exponential map in inner-product spaces

This file identifies the Riemannian geodesics of a finite-dimensional real inner-product space.
Its standard Riemannian metric is constant, so the Levi-Civita connection has vanishing
Christoffel map, and the geodesic equation says that the acceleration vanishes.  On every interval
the geodesics are therefore exactly the affine segments.  Consequently the maximal intervals are
all of `ℝ`, and the chosen maximal geodesic with initial point `p` and velocity `v` is
`t ↦ p + t • v`.

It follows that the exponential map at `p` is defined on all of `T_p F` and is translation by `p`,
under the canonical identification `NormedSpace.fromTangentSpace` of `T_p F` with `F`, so its
differential is the identity everywhere.  Since the metric is the inner product of `F` at every
point, this differential preserves inner products; in particular it satisfies the radial identity
of the Gauss lemma.  Every open neighbourhood of the origin that is
star-shaped at the origin is therefore a normal domain.  In particular the tangent ball of radius
`r > 0` is a normal domain whose normal neighbourhood is `Metric.ball p r`, and on it the
Riemannian logarithm is `q ↦ q - p`.

These formulas include the zero-dimensional space. They provide the flat model against which the
exponential map, normal domains, and the logarithm can be checked.

## Main results

* `TauCeti.Manifold.christoffelMap_leviCivita_model_space`: the Christoffel map of the standard
  Riemannian metric vanishes.
* `TauCeti.Manifold.isGeodesicCurve_add_smul`: an affine line is an all-time geodesic.
* `TauCeti.Manifold.isGeodesicCurveOn_iff_model_space`: the geodesic equation is the vanishing of
  the acceleration.
* `TauCeti.Manifold.isGeodesicCurveOn_iff_exists_eqOn_add_smul` and
  `TauCeti.Manifold.isGeodesicCurveOnFrom_iff_eqOn_add_smul`: on an interval, the geodesics are
  exactly the affine segments, and the one with initial data `(p, v)` is `t ↦ p + t • v`.
* `TauCeti.Manifold.isGeodesicCurve_iff_exists_eq_add_smul`: the all-time geodesics are exactly
  the affine lines.
* `TauCeti.Manifold.geodesicInterval_model_space`: every affine initial condition exists for all
  time.
* `TauCeti.Manifold.maximalGeodesic_model_space`: the chosen maximal geodesic is the affine line.
* `TauCeti.Manifold.expDomain_model_space` and
  `TauCeti.Manifold.isGeodesicallyCompleteAt_model_space`: the exponential map is defined
  everywhere, so the space is geodesically complete at every point.
* `TauCeti.Manifold.riemannianExp_model_space`: the exponential map at `p` is translation by `p`.
* `TauCeti.Manifold.mfderiv_riemannianExp_apply_model_space` and
  `TauCeti.Manifold.fderiv_riemannianExp_apply_model_space`: its differential is the identity.
* `TauCeti.Manifold.inner_mfderiv_riemannianExp_model_space`: hence its differential preserves
  inner products; in particular it satisfies the radial identity of the Gauss lemma.
* `TauCeti.Manifold.isNormalDomain_model_space` and
  `TauCeti.Manifold.isNormalDomain_ball_model_space`: open star-shaped neighbourhoods of the
  origin, in particular tangent balls, are normal domains.
* `TauCeti.Manifold.image_riemannianExp_ball_model_space`: the exponential image of the tangent
  ball of radius `r` is the ball of radius `r` about `p`.
* `TauCeti.Manifold.riemannianLog_model_space` and
  `TauCeti.Manifold.riemannianLog_ball_model_space`: the logarithm sends `q` to `q - p`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, §§2–3.
-/

public section

open Bundle CovariantDerivative Function Manifold Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem leviCivitaConnection_const_apply (u v : F) (x : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (fun _ : F ↦ v) x u = 0 := by
  let C (a : F) : ∀ y : F, TangentSpace 𝓘(ℝ, F) y := fun _ ↦ a
  -- Writing the constant sections dependently keeps all Koszul-formula terms well typed.
  change leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x) = 0
  have hconst (a : F) :
      MDiffAt (fun y : F ↦ (TotalSpace.mk' F y (C a y) : TangentBundle 𝓘(ℝ, F) F)) x := by
    simpa only [C] using
      ((contMDiffAt_vectorSpace_iff_contDiffAt (n := (1 : ℕ∞ω))
        (V := fun _ : F ↦ a)).2 contDiffAt_const).mdifferentiableAt one_ne_zero
  -- The inner product of two constant fields is constant, so its differential vanishes.
  have hinner (a b : F) : d% (fun y : F ↦ inner ℝ (C a y) (C b y)) x = 0 :=
    mvfderiv_const (I := 𝓘(ℝ, F)) (c := inner ℝ a b)
  -- Constant fields commute, so every bracket term of the Koszul formula vanishes.
  have hbracket (a b c : F) :
      inner ℝ (C a x) (VectorField.mlieBracket 𝓘(ℝ, F) (C b) (C c) x) = 0 := by
    have h : VectorField.mlieBracket 𝓘(ℝ, F) (C b) (C c) x = 0 := by
      simpa only [C] using TauCeti.mlieBracket_const_model_space b c x
    rw [h]
    exact inner_zero_right (𝕜 := ℝ) (C a x)
  let w : F := leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x)
  -- `w` abbreviates a tangent vector represented in the model vector space.
  change w = 0
  rw [← inner_self_eq_zero (𝕜 := ℝ)]
  -- Re-expose the dependent constant section so the Koszul formula applies directly.
  change inner ℝ (leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x)) (C w x) = 0
  rw [leviCivitaConnection_apply_inner 𝓘(ℝ, F)
    (X := C u) (Y := C v) (Z := C w) (hconst u) (hconst v) (hconst w)]
  simp [hinner, hbracket]

/-- The Levi-Civita connection of the standard Riemannian metric differentiates a constant vector
field to zero. -/
@[simp]
theorem leviCivitaConnection_const_model_space (v : F) (x : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (fun _ : F ↦ v) x = 0 := by
  ext u
  simpa using leviCivitaConnection_const_apply (F := F) u v x

/-- The Christoffel map of the standard Riemannian metric on an inner-product space vanishes in
its canonical coordinates. -/
@[simp]
theorem christoffelMap_leviCivita_model_space (x : F) :
    christoffelMap (Module.finBasis ℝ F)
      ((leviCivitaConnection 𝓘(ℝ, F) F).isCovariantDerivativeOn
        (s := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet)) x = 0 := by
  ext v u
  rw [christoffelMap_model_space, leviCivitaConnection_const_model_space]
  -- The zero map on tangent vectors, evaluated at `u`.
  rfl

/-- Every affine line in a finite-dimensional real inner-product space is a geodesic for the
standard Riemannian metric, with its evident initial point and velocity. -/
theorem isGeodesicCurveOnFrom_add_smul (p v : F) :
    IsGeodesicCurveOnFrom 𝓘(ℝ, F) (fun t : ℝ ↦ p + t • v) univ p v := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hderiv : deriv (fun t : ℝ ↦ p + t • v) = fun _ : ℝ ↦ v :=
    funext fun t ↦ (hline t).deriv
  refine ⟨?_, mem_univ 0, ?_⟩
  · rw [isGeodesicCurveOn_iff_chart (I := 𝓘(ℝ, F)) uniqueDiffOn_univ]
    refine ⟨?_, fun r _ ↦ ?_⟩
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_comp, derivWithin_univ,
        hderiv, deriv_const', christoffelMap_leviCivita_model_space, zero_apply, add_zero]
  · apply TotalSpace.ext
    · simp
    · refine heq_of_eq ?_
      rw [curveVelocityWithin_univ, curveVelocity_apply, mfderiv_eq_fderiv]
      exact (hline 0).deriv

/-- Every affine line in a finite-dimensional real inner-product space is a geodesic for the
standard Riemannian metric. -/
theorem isGeodesicCurve_add_smul (p v : F) :
    IsGeodesicCurve 𝓘(ℝ, F) (fun t : ℝ ↦ p + t • v) :=
  (isGeodesicCurveOn_univ (I := 𝓘(ℝ, F))).1
    (isGeodesicCurveOnFrom_add_smul p v).isGeodesicCurveOn

/-- Geodesics in a finite-dimensional inner-product space exist for every real parameter. -/
@[simp]
theorem geodesicInterval_model_space (p v : F) :
    geodesicInterval 𝓘(ℝ, F) F p v = univ := by
  apply eq_univ_of_forall
  intro t
  let a := -(|t| + 1)
  let b := |t| + 1
  have h0 : (0 : ℝ) ∈ Ioo a b := by
    simp only [a, b, mem_Ioo]
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo a b := by
    simp only [a, b, mem_Ioo]
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hline := (isGeodesicCurveOnFrom_add_smul p v).mono
    (uniqueDiffOn_Ioo a b) (subset_univ _) h0
  exact (mem_geodesicInterval_iff (I := 𝓘(ℝ, F)) (M := F)).2
    ⟨fun s : ℝ ↦ p + s • v, a, b, hline, ht⟩

/-- The chosen maximal geodesic in an inner-product space is its affine line. -/
@[simp]
theorem maximalGeodesic_model_space (p v : F) (t : ℝ) :
    maximalGeodesic 𝓘(ℝ, F) F p v t = p + t • v := by
  exact (isGeodesicCurveOnFrom_add_smul p v).eq_maximalGeodesic_of_univ t

/-- **The geodesic equation in an inner-product space.**  Since the Christoffel map vanishes, a
curve is a geodesic on a parameter set with unique derivatives exactly when it is `C²` there and
its acceleration within that set vanishes. -/
theorem isGeodesicCurveOn_iff_model_space {γ : ℝ → F} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    IsGeodesicCurveOn 𝓘(ℝ, F) γ s ↔
      ContDiffOn ℝ 2 γ s ∧ ∀ r ∈ s, derivWithin (derivWithin γ s) s r = 0 := by
  rw [isGeodesicCurveOn_iff_chart hs, contMDiffOn_iff_contDiffOn]
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_comp,
    christoffelMap_leviCivita_model_space, zero_apply, add_zero]

/-- **The geodesics of an inner-product space on an interval are affine segments.**  On a
preconnected parameter set with unique derivatives, such as a nondegenerate interval, a curve in a
finite-dimensional real inner-product space is a geodesic exactly when it agrees there with an
affine line. -/
theorem isGeodesicCurveOn_iff_exists_eqOn_add_smul {γ : ℝ → F} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hs' : IsPreconnected s) :
    IsGeodesicCurveOn 𝓘(ℝ, F) γ s ↔ ∃ p v : F, EqOn γ (fun t : ℝ ↦ p + t • v) s := by
  refine ⟨fun hγ ↦ ?_, fun ⟨p, v, hpv⟩ ↦
    ((isGeodesicCurveOnFrom_add_smul p v).isGeodesicCurveOn.mono hs (subset_univ s)).congr hpv⟩
  obtain rfl | ⟨t₀, ht₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, 0, eqOn_empty _ _⟩
  obtain ⟨hC2, hacc⟩ := (isGeodesicCurveOn_iff_model_space hs).1 hγ
  have hconv : Convex ℝ s := Real.convex_iff_isPreconnected.2 hs'
  have hdiff : DifferentiableOn ℝ (derivWithin γ s) s :=
    (hC2.derivWithin hs (m := 1) (by norm_num)).differentiableOn (by norm_num)
  set v := derivWithin γ s t₀
  -- The velocity has vanishing derivative on the convex set `s`, so it is constant there.
  have hvel : EqOn (derivWithin γ s) (fun _ ↦ v) s :=
    hconv.eqOn_of_fderivWithin_eq hdiff (differentiableOn_const v) hs
      (fun r hr ↦ by simp [← toSpanSingleton_derivWithin, hacc r hr]) ht₀ rfl
  have hline (p : F) (r : ℝ) : HasDerivAt (fun t : ℝ ↦ p + t • v) v r := by
    simpa using ((hasDerivAt_id r).smul_const v).const_add p
  -- A curve with constant velocity `v` on `s` agrees there with the line through `γ t₀`.
  refine ⟨γ t₀ - t₀ • v, v, hconv.eqOn_of_fderivWithin_eq (hC2.differentiableOn (by norm_num))
    (fun r _ ↦ (hline _ r).differentiableAt.differentiableWithinAt) hs (fun r hr ↦ ?_) ht₀
    (by simp)⟩
  rw [← toSpanSingleton_derivWithin, ← toSpanSingleton_derivWithin, hvel hr,
    (hline _ r).hasDerivWithinAt.derivWithin (hs r hr)]

/-- **The geodesic of an inner-product space with given initial data.**  On a preconnected
parameter set with unique derivatives containing `0`, the geodesic starting at `p` with velocity
`v` is the affine line `t ↦ p + t • v` there. -/
theorem isGeodesicCurveOnFrom_iff_eqOn_add_smul {γ : ℝ → F} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hs' : IsPreconnected s) (h0 : (0 : ℝ) ∈ s) {p v : F} :
    IsGeodesicCurveOnFrom 𝓘(ℝ, F) γ s p v ↔ EqOn γ (fun t : ℝ ↦ p + t • v) s := by
  -- On `s`, a curve agreeing with an affine line has the line's velocity at `0`.
  have hvel {q w : F} (h : EqOn γ (fun t : ℝ ↦ q + t • w) s) :
      curveVelocityWithin 𝓘(ℝ, F) γ s 0 = w := by
    have hline : HasDerivWithinAt γ w s 0 := by
      refine HasDerivWithinAt.congr_of_mem ?_ h h0
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q).hasDerivWithinAt
    have hchart := derivWithin_extChartAt_comp_curve (I := 𝓘(ℝ, F))
      hline.differentiableWithinAt.mdifferentiableWithinAt (hs 0 h0)
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_comp,
      hline.derivWithin (hs 0 h0)] at hchart
    exact hchart.symm
  constructor
  · intro h
    obtain ⟨q, w, hqw⟩ := (isGeodesicCurveOn_iff_exists_eqOn_add_smul hs hs').1
      h.isGeodesicCurveOn
    have hq : q = p := by simpa using (hqw h0).symm.trans h.base_eq
    have hw : w = v := (hvel hqw).symm.trans (eq_of_heq h.velocity_heq)
    rwa [← hq, ← hw]
  · intro h
    refine ⟨(isGeodesicCurveOn_iff_exists_eqOn_add_smul hs hs').2 ⟨p, v, h⟩, h0, ?_⟩
    apply TotalSpace.ext
    · simpa using h h0
    · exact heq_of_eq (hvel h)

/-- The geodesics in a finite-dimensional real inner-product space are exactly the affine
lines. -/
theorem isGeodesicCurve_iff_exists_eq_add_smul {γ : ℝ → F} :
    IsGeodesicCurve 𝓘(ℝ, F) γ ↔ ∃ p v : F, γ = fun t : ℝ ↦ p + t • v := by
  simp only [← isGeodesicCurveOn_univ, isGeodesicCurveOn_iff_exists_eqOn_add_smul
    uniqueDiffOn_univ isPreconnected_univ, eqOn_univ]

/-! ### The exponential map and the logarithm -/

/-- The exponential map of a finite-dimensional inner-product space is defined on every tangent
vector. -/
@[simp]
theorem expDomain_model_space (p : F) : expDomain 𝓘(ℝ, F) F p = univ :=
  eq_univ_of_forall fun v ↦ mem_expDomain_iff.2 <| by
    rw [geodesicInterval_model_space p v]
    exact mem_univ 1

/-- A finite-dimensional inner-product space is geodesically complete at every point. -/
theorem isGeodesicallyCompleteAt_model_space (p : F) : IsGeodesicallyCompleteAt 𝓘(ℝ, F) F p :=
  expDomain_eq_univ_iff.1 (expDomain_model_space p)

/-- The exponential map of a finite-dimensional inner-product space at `p` is translation by
`p`, under the canonical identification `NormedSpace.fromTangentSpace` of `T_p F` with `F`. -/
@[simp]
theorem riemannianExp_model_space (p : F) (v : TangentSpace 𝓘(ℝ, F) p) :
    riemannianExp 𝓘(ℝ, F) F p v = p + NormedSpace.fromTangentSpace p v :=
  (riemannianExp_def p v).trans <| (maximalGeodesic_model_space p v 1).trans <|
    congrArg (p + ·) (one_smul ℝ (NormedSpace.fromTangentSpace p v))

/-- The identification `NormedSpace.fromTangentSpace p`, typed with the instances that the
Riemannian metric induces on `T_p F`, so that it can be differentiated. -/
private def tangentSpaceEquivModel (p : F) : TangentSpace 𝓘(ℝ, F) p ≃L[ℝ] F :=
  ContinuousLinearEquiv.refl ℝ F

omit [FiniteDimensional ℝ F] in
-- Both maps are the identity of `F`; they differ only in the instances elaborated on `T_p F`.
private theorem tangentSpaceEquivModel_apply (p : F) (v : TangentSpace 𝓘(ℝ, F) p) :
    tangentSpaceEquivModel p v = NormedSpace.fromTangentSpace p v := (rfl)

private theorem hasFDerivAt_riemannianExp_model_space (p : F) (v : TangentSpace 𝓘(ℝ, F) p) :
    HasFDerivAt (riemannianExp 𝓘(ℝ, F) F p)
      (tangentSpaceEquivModel p : TangentSpace 𝓘(ℝ, F) p →L[ℝ] F) v := by
  have hexp : riemannianExp 𝓘(ℝ, F) F p = fun u ↦ p + tangentSpaceEquivModel p u :=
    funext fun u ↦ by rw [riemannianExp_model_space, tangentSpaceEquivModel_apply]
  rw [hexp]
  exact (tangentSpaceEquivModel p).hasFDerivAt.const_add p

private theorem hasMFDerivAt_riemannianExp_model_space (p : F) (v : TangentSpace 𝓘(ℝ, F) p) :
    HasMFDerivAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) p) 𝓘(ℝ, F) (riemannianExp 𝓘(ℝ, F) F p) v
      (tangentSpaceEquivModel p : TangentSpace 𝓘(ℝ, F) p →L[ℝ] F) :=
  hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_riemannianExp_model_space p v)

/-- The differential of the exponential map of a finite-dimensional inner-product space is the
identity at every tangent vector. -/
theorem mfderiv_riemannianExp_apply_model_space (p : F) (v w : TangentSpace 𝓘(ℝ, F) p) :
    mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) p) 𝓘(ℝ, F) (riemannianExp 𝓘(ℝ, F) F p) v w =
      NormedSpace.fromTangentSpace p w := by
  rw [← tangentSpaceEquivModel_apply]
  exact DFunLike.congr_fun (hasMFDerivAt_riemannianExp_model_space p v).mfderiv w

/-- The Fréchet derivative of the exponential map of a finite-dimensional inner-product space is
the identity at every tangent vector. This is the simp-normal form of
`mfderiv_riemannianExp_apply_model_space`. -/
@[simp]
theorem fderiv_riemannianExp_apply_model_space (p : F) (v w : TangentSpace 𝓘(ℝ, F) p) :
    fderiv ℝ (riemannianExp 𝓘(ℝ, F) F p) v w = NormedSpace.fromTangentSpace p w := by
  rw [← tangentSpaceEquivModel_apply]
  exact DFunLike.congr_fun (hasFDerivAt_riemannianExp_model_space p v).fderiv w

/-- **The Gauss lemma in an inner-product space.** The differential of the exponential map of a
finite-dimensional inner-product space at every tangent vector `v` preserves inner products. Taking
`w₁ = v` gives the radial identity `⟪d(exp_p)_v(v), d(exp_p)_v(w)⟫ = ⟪v, w⟫` of the Gauss lemma
`TauCeti.Manifold.inner_mfderiv_riemannianExp_radial`; in this flat case it holds for every pair of
tangent vectors, not only for the radial direction. -/
@[simp]
theorem inner_mfderiv_riemannianExp_model_space (p : F) (v w₁ w₂ : TangentSpace 𝓘(ℝ, F) p) :
    inner ℝ (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) p) 𝓘(ℝ, F) (riemannianExp 𝓘(ℝ, F) F p) v w₁)
        (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) p) 𝓘(ℝ, F) (riemannianExp 𝓘(ℝ, F) F p) v w₂) =
      inner ℝ w₁ w₂ := by
  rw [mfderiv_riemannianExp_apply_model_space, mfderiv_riemannianExp_apply_model_space]
  -- Both sides are the inner product of `F`: the standard metric of `F` at every point is it.
  rfl

/-- The exponential map of a finite-dimensional inner-product space at `p` maps the tangent ball of
radius `r` onto the ball of radius `r` about `p`. -/
theorem image_riemannianExp_ball_model_space (p : F) (r : ℝ) :
    riemannianExp 𝓘(ℝ, F) F p '' Metric.ball (0 : TangentSpace 𝓘(ℝ, F) p) r =
      Metric.ball p r := by
  ext q
  simp only [mem_image, Metric.mem_ball, riemannianExp_model_space, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [norm_tangentSpace_vectorSpace] at hv
    rw [add_sub_cancel_left]
    exact hv
  · intro hq
    refine ⟨(NormedSpace.fromTangentSpace p).symm (q - p), ?_, ?_⟩
    · rw [norm_tangentSpace_vectorSpace]
      exact hq
    · rw [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]

/-- In a finite-dimensional inner-product space, every open neighbourhood of the origin that is
star-shaped at the origin is a normal domain. -/
theorem isNormalDomain_model_space (p : F) {U : Set (TangentSpace 𝓘(ℝ, F) p)} (hU : IsOpen U)
    (h0 : 0 ∈ U) (hstar : StarConvex ℝ 0 U) : IsNormalDomain 𝓘(ℝ, F) F p U := by
  refine ⟨hU, h0, hstar, (expDomain_model_space p).symm ▸ subset_univ U, fun v _ w _ h ↦ ?_,
    fun v ↦ ?_⟩
  · simp only [riemannianExp_model_space, add_right_inj] at h
    exact (NormedSpace.fromTangentSpace p).injective h
  · have hsmooth := contMDiffOn_riemannianExp (I := 𝓘(ℝ, F)) (M := F) p
    rw [expDomain_model_space] at hsmooth
    exact isLocalDiffeomorphAt_of_mfderiv_eq hsmooth isOpen_univ (mem_univ _)
      BoundarylessManifold.isInteriorPoint (by simp)
      (hasMFDerivAt_riemannianExp_model_space p v.1).mfderiv.symm

/-- In a finite-dimensional inner-product space, every tangent ball of positive radius is a
normal domain; its normal neighbourhood is the ball of the same radius about the base point
(`image_riemannianExp_ball_model_space`). -/
theorem isNormalDomain_ball_model_space (p : F) {r : ℝ} (hr : 0 < r) :
    IsNormalDomain 𝓘(ℝ, F) F p (Metric.ball (0 : TangentSpace 𝓘(ℝ, F) p) r) :=
  isNormalDomain_model_space p Metric.isOpen_ball (Metric.mem_ball_self hr)
    ((convex_ball (0 : TangentSpace 𝓘(ℝ, F) p) r).starConvex (Metric.mem_ball_self hr))

/-- The Riemannian logarithm of a finite-dimensional inner-product space at `p` sends `q` to
`q - p`, read in `T_p F`, whenever this vector lies in the chosen set of tangent vectors. -/
theorem riemannianLog_model_space {p q : F} {U : Set (TangentSpace 𝓘(ℝ, F) p)}
    (hq : (NormedSpace.fromTangentSpace p).symm (q - p) ∈ U) :
    riemannianLog 𝓘(ℝ, F) F p U q = (NormedSpace.fromTangentSpace p).symm (q - p) := by
  have hex : ∃ v ∈ U, riemannianExp 𝓘(ℝ, F) F p v = q :=
    ⟨_, hq, by rw [riemannianExp_model_space, ContinuousLinearEquiv.apply_symm_apply,
      add_sub_cancel]⟩
  have heq := invFunOn_eq hex
  rw [← riemannianLog_def, riemannianExp_model_space] at heq
  exact (NormedSpace.fromTangentSpace p).eq_symm_apply.2 (eq_sub_of_add_eq' heq)

/-- On the ball of radius `r` about `p` in a finite-dimensional inner-product space, the
Riemannian logarithm relative to the tangent ball of radius `r` sends `q` to `q - p`, read in
`T_p F`. -/
@[simp]
theorem riemannianLog_ball_model_space {p q : F} {r : ℝ} (hq : q ∈ Metric.ball p r) :
    riemannianLog 𝓘(ℝ, F) F p (Metric.ball 0 r) q =
      (NormedSpace.fromTangentSpace p).symm (q - p) := by
  rw [← image_riemannianExp_ball_model_space p r] at hq
  obtain ⟨v, hv, rfl⟩ := hq
  apply riemannianLog_model_space
  rwa [riemannianExp_model_space, add_sub_cancel_left,
    ContinuousLinearEquiv.symm_apply_apply]

end TauCeti.Manifold

end
