/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# The Gauss lemma for the Riemannian exponential map

The Gauss lemma says that the differential of the exponential map preserves the radial component
of a tangent vector.  If `v` belongs to the natural domain of `exp_p`, then

`<d(exp_p)_v(v), d(exp_p)_v(w)> = <v, w>`.

The proof uses the radial variation `F(u,t) = exp_p(t (v + u w))`.  Its `t`-curves are geodesics,
so they have constant speed.  Metric compatibility and the symmetry of the two mixed covariant
derivatives turn the derivative in `t` of `<∂_u F, ∂_t F>` into `<v,w>`.  Integrating from
`t = 0`, where the transverse field vanishes, gives the identity at `t = 1`.

The statement is made on the full natural domain of the exponential map.  In particular, every
normal domain inherits it without choosing a smaller ball.

## Main result

* `TauCeti.Manifold.inner_mfderiv_riemannianExp_radial`: the differential of the exponential map
  preserves inner products with the radial direction.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Lemma 3.5.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Lemma 6.3.
* The organization follows `DoCarmoLib/Riemannian/Exponential/GaussLemma.lean` in the
  Apache-2.0 [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, replacing its chart-level
  connection and exponential-map infrastructure with Tau Ceti's intrinsic APIs.
-/

public section

open Bundle CovariantDerivative Filter Function Manifold Set
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

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem curveVelocity_comp_apply
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    {f : F₀ → M} {g : ℝ → F₀} {t : ℝ} {w : F₀}
    (hf : MDifferentiableAt 𝓘(ℝ, F₀) I f (g t))
    (hg : HasDerivAt g w t) :
    curveVelocity I (f ∘ g) t = mfderiv 𝓘(ℝ, F₀) I f (g t) w := by
  have hcomp := hf.hasMFDerivAt.comp t hg.hasFDerivAt.hasMFDerivAt
  have hwithin : curveVelocityWithin I (f ∘ g) univ t =
      mfderiv 𝓘(ℝ, F₀) I f (g t) w := by
    apply curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (w := mfderiv 𝓘(ℝ, F₀) I f (g t) w) _ uniqueDiffWithinAt_univ
    apply hcomp.hasMFDerivWithinAt.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro z
    -- The source model of a real curve is one-dimensional; exposing its scalar coordinate lets
    -- linearity identify the derivative on `z` with its value on `1`.
    change mfderiv 𝓘(ℝ, F₀) I f (g t) ((show ℝ from z) • w) =
      (show ℝ from z) • mfderiv 𝓘(ℝ, F₀) I f (g t) w
    exact map_smul _ _ _
  simpa only [curveVelocityWithin_univ] using hwithin

private theorem curveVelocity_riemannianExp_affine
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    {p : M} {v w : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    curveVelocity I (fun u : ℝ ↦ riemannianExp I M p (v + u • w)) 0 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w := by
  have hg : HasDerivAt (fun u : ℝ ↦ v + u • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add v
  have h := curveVelocity_comp_apply (f := riemannianExp I M p)
    (g := fun u : ℝ ↦ v + u • w)
    (by simpa using
      (contMDiffAt_riemannianExp (I := I) (M := M) hv).mdifferentiableAt (by simp))
    hg
  have hzero : v + (0 : ℝ) • w = v := by simp
  rw [hzero] at h
  exact h

private theorem curveVelocity_riemannianExp_ray
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    {p : M} {v : TangentSpace I p} (hv : v ∈ expDomain I M p) :
    curveVelocity I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 1 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v := by
  have hg : HasDerivAt (fun t : ℝ ↦ t • v) v 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const v
  have h := curveVelocity_comp_apply (f := riemannianExp I M p)
    (g := fun t : ℝ ↦ t • v)
    (by simpa using
      (contMDiffAt_riemannianExp (I := I) (M := M) hv).mdifferentiableAt (by simp))
    hg
  rw [one_smul] at h
  exact h

/-- **The Gauss lemma.** The differential of the Riemannian exponential map preserves the inner
product with the radial direction at every vector in its natural domain. -/
theorem inner_mfderiv_riemannianExp_radial [I.Boundaryless]
    [T2Space (TangentBundle I M)] {p : M} {v w : TangentSpace I p}
    (hv : v ∈ expDomain I M p) :
    inner ℝ
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w) =
      inner ℝ v w := by
  let _ : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let F : ℝ → ℝ → M := fun u t ↦ riemannianExp I M p (t • (v + u • w))
  let P : (u t : ℝ) → TangentSpace I (F u t) := fun u ↦ curveVelocity I (F u)
  let Q : (t u : ℝ) → TangentSpace I (F u t) :=
    fun t u ↦ curveVelocity I (fun q ↦ F q t) u
  let cov := leviCivitaConnection I M
  have hF_smooth {u t : ℝ} (hut : t • (v + u • w) ∈ expDomain I M p) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t) := by
    have hinput : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, TangentSpace I p) ∞
        (fun z : ℝ × ℝ ↦ z.2 • (v + z.1 • w)) (u, t) := by
      exact (contMDiff_iff_contDiff.mpr
        (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.2 • (v + z.1 • w)))).contMDiffAt
    exact (contMDiffAt_riemannianExp (I := I) (M := M) hut).comp (u, t) hinput
  have hF_eq_maximal (u : ℝ) :
      F u = maximalGeodesic I M p (v + u • w) := by
    funext t
    by_cases ht : t ∈ geodesicInterval I M p (v + u • w)
    · exact riemannianExp_smul ht
    · dsimp only [F]
      rw [riemannianExp_of_notMem_expDomain
          (mt mem_geodesicInterval_iff_smul_mem_expDomain.mpr ht),
        maximalGeodesic_eq_of_not_mem ht]
  have haccel {u t : ℝ} (ht : t ∈ geodesicInterval I M p (v + u • w)) :
      alongCurve cov (F u) (curveVelocity I (F u)) t = 0 := by
    rw [hF_eq_maximal u, ← alongCurveWithin_curveVelocityWithin_of_isOpen cov
      (maximalGeodesic I M p (v + u • w)) isOpen_geodesicInterval ht]
    exact (isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p (v + u • w))
      |>.isGeodesicCurveOn.alongCurveWithin_curveVelocityWithin_eq_zero t ht
  have hspeed {u t : ℝ} (ht : t ∈ geodesicInterval I M p (v + u • w)) :
      inner ℝ (P u t) (P u t) = inner ℝ (v + u • w) (v + u • w) := by
    have hgeo := isGeodesicCurveOnFrom_maximalGeodesic
      (I := I) (M := M) p (v + u • w)
    have hsquared := hgeo.isGeodesicCurveOn.inner_curveVelocityWithin_self_eq
      isPreconnected_geodesicInterval ht zero_mem_geodesicInterval
    have ht_nhds := isOpen_geodesicInterval.mem_nhds ht
    have hzero_nhds := isOpen_geodesicInterval.mem_nhds
      (zero_mem_geodesicInterval (I := I) (M := M) (p := p) (v := v + u • w))
    rw [curveVelocityWithin_of_mem_nhds ht_nhds,
      curveVelocityWithin_of_mem_nhds hzero_nhds] at hsquared
    have hinitial := congrArg (fun z : TangentBundle I M ↦ inner ℝ z.2 z.2) hgeo.initial_eq
    rw [curveVelocityWithin_of_mem_nhds hzero_nhds] at hinitial
    dsimp only [P]
    rw [hF_eq_maximal u]
    exact hsquared.trans hinitial
  have hIcc : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.mp hv)
  have hmain : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r ↦ inner ℝ (Q r 0) (P 0 r)) (inner ℝ v w) t := by
    intro t ht
    have htJ : t ∈ geodesicInterval I M p v := hIcc ht
    have htExp : t • v ∈ expDomain I M p :=
      mem_geodesicInterval_iff_smul_mem_expDomain.mp htJ
    have hsurface := hF_smooth (u := 0) (t := t) (by simpa using htExp)
    have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
    have hDuP_inner : inner ℝ
        (alongCurve cov (fun q ↦ F q t) (fun q ↦ P q t) 0) (P 0 t) = inner ℝ v w := by
      have hfield := CovariantDerivative.differentiableAt_sectionCoord_curveVelocity_snd
        (f := F) (hsurface.of_le (by simp)) hbase
      have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) 0 :=
        by
          have hinput : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, TangentSpace I p) ∞
              (fun q : ℝ ↦ t • (v + q • w)) 0 :=
            (contMDiff_iff_contDiff.mpr
              (by fun_prop : ContDiff ℝ ∞ (fun q : ℝ ↦ t • (v + q • w)))).contMDiffAt
          have hzeroExp : t • (v + (0 : ℝ) • w) ∈ expDomain I M p := by
            simpa using htExp
          have hs : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
              (fun q : ℝ ↦ riemannianExp I M p (t • (v + q • w))) 0 :=
            (contMDiffAt_riemannianExp (I := I) (M := M) hzeroExp).comp 0 hinput
          -- Unfold the local name `F` so the exponential-map chain rule has the expected curve.
          change MDifferentiableAt 𝓘(ℝ, ℝ) I
            (fun q : ℝ ↦ riemannianExp I M p (t • (v + q • w))) 0
          exact hs.mdifferentiableAt (by simp)
      have hmetric := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
      have hleft := hmetric.hasDerivAt_inner_alongCurve hcurve hfield hfield
      have hnear : ∀ᶠ u in nhds (0 : ℝ),
          t ∈ geodesicInterval I M p (v + u • w) := by
        have hopen := (isOpen_expDomain (I := I) (M := M) p).mem_nhds htExp
        have hcont : ContinuousAt (fun u : ℝ ↦ t • (v + u • w)) 0 := by fun_prop
        have hpre : (fun u : ℝ ↦ t • (v + u • w)) ⁻¹' expDomain I M p ∈ nhds 0 :=
          hcont.preimage_mem_nhds (by simpa using hopen)
        filter_upwards [hpre] with u hu
        exact mem_geodesicInterval_iff_smul_mem_expDomain.mpr hu
      have heq : (fun u ↦ inner ℝ (P u t) (P u t)) =ᶠ[nhds (0 : ℝ)]
          fun u ↦ inner ℝ (v + u • w) (v + u • w) :=
        hnear.mono fun u hu ↦ hspeed hu
      have ha : HasDerivAt (fun u : ℝ ↦ v + u • w) w 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add v
      have hright := (ha.inner ℝ ha).congr_of_eventuallyEq heq
      have hderiv_eq := hleft.unique hright
      simp only [zero_smul, add_zero] at hderiv_eq
      have hraw : inner ℝ
          (alongCurve cov (fun q ↦ F q t) (fun q ↦ curveVelocity I (F q) t) 0)
          (curveVelocity I (F 0) t) = inner ℝ v w := by
        linarith [real_inner_comm (curveVelocity I (F 0) t)
          (alongCurve cov (fun q ↦ F q t) (fun q ↦ curveVelocity I (F q) t) 0),
          real_inner_comm v w]
      simpa only [P, cov] using hraw
    have hQcoord := CovariantDerivative.differentiableAt_sectionCoord_curveVelocity_fst
      (f := F) (hsurface.of_le (by simp)) hbase
    have hPcoord : DifferentiableAt ℝ
        (sectionCoord (F := E) (F 0) (curveVelocity I (F 0)) (F 0 t)) t := by
      have hFzero : F 0 = maximalGeodesic I M p v := by
        simpa using hF_eq_maximal 0
      exact differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (M := M) (γ := F 0)
        ((isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v)
          |>.isGeodesicCurveOn.contMDiffOn.congr fun r _ ↦ congrFun hFzero r)
        isOpen_geodesicInterval htJ
    have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (F 0) t :=
      by
        have hinput : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, TangentSpace I p) ∞
            (fun r : ℝ ↦ r • v) t :=
          (contMDiff_iff_contDiff.mpr
            (by fun_prop : ContDiff ℝ ∞ (fun r : ℝ ↦ r • v))).contMDiffAt
        have hs : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
            (fun r ↦ riemannianExp I M p (r • v)) t :=
          (contMDiffAt_riemannianExp (I := I) (M := M) htExp).comp t hinput
        have hFzero : F 0 = fun r : ℝ ↦ riemannianExp I M p (r • v) := by
          funext r
          simp only [F, zero_smul, add_zero]
        rw [hFzero]
        exact hs.mdifferentiableAt (by simp)
    have hprod := (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
      |>.hasDerivAt_inner_alongCurve hcurve hQcoord hPcoord
    have hswap := CovariantDerivative.alongCurve_curveVelocity_comm cov
      ((CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2
        (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I))
      (f := F) (u := 0) (v := t) (hsurface.of_le (by simp))
    have htJ0 : t ∈ geodesicInterval I M p (v + (0 : ℝ) • w) := by simpa using htJ
    rw [haccel htJ0, inner_zero_right, add_zero, hswap, hDuP_inner] at hprod
    simpa only [P, Q] using hprod
  have hzero : inner ℝ (Q 0 0) (P 0 0) = 0 := by
    have hQzero : Q 0 0 = 0 := by
      have hfun : (fun q : ℝ ↦ F q 0) = fun _ ↦ p := by
        funext q
        simp only [F, zero_smul, riemannianExp_zero]
      dsimp only [Q]
      rw [hfun, curveVelocity_const]
      rfl
    rw [hQzero, inner_zero_left]
  have hconst : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ (Q t 0) (P 0 t) - t * inner ℝ v w = 0 := by
    let g : ℝ → ℝ := fun t ↦ inner ℝ (Q t 0) (P 0 t) - t * inner ℝ v w
    have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := by
      intro t ht
      have hlin : HasDerivAt (fun s : ℝ ↦ s * inner ℝ v w) (inner ℝ v w) t := by
        exact hasDerivAt_mul_const (inner ℝ v w)
      have hsub := (hmain t ht).sub hlin
      -- `HasDerivAt.sub` selects an extensionally equal scalar-module instance for `ℝ`; this
      -- explicit target presents the pointwise subtraction before simplifying its derivative.
      change HasDerivAt
        (fun r ↦ inner ℝ (Q r 0) (P 0 r) - r * inner ℝ v w)
        (inner ℝ v w - inner ℝ v w) t at hsub
      simpa only [g, sub_self] using hsub
    have hcont : ContinuousOn g (Icc (0 : ℝ) 1) := fun t ht ↦
      (hg t ht).continuousAt.continuousWithinAt
    have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt g 0 (Ici t) t :=
      fun t ht ↦ (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt
    intro t ht
    have hgt := constant_of_has_deriv_right_zero hcont hderiv t ht
    have hg0 : g 0 = 0 := by simp only [g, hzero, zero_mul, sub_zero]
    rwa [hg0] at hgt
  have hone := hconst 1 (by simp)
  have hPone : P 0 1 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v := by
    have hfun : F 0 = fun t : ℝ ↦ riemannianExp I M p (t • v) := by
      funext t
      simp only [F, zero_smul, add_zero]
    dsimp only [P]
    rw [hfun]
    exact curveVelocity_riemannianExp_ray (I := I) (M := M) hv
  have hQone : Q 1 0 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w := by
    have hfun : (fun q : ℝ ↦ F q 1) =
        fun q : ℝ ↦ riemannianExp I M p (v + q • w) := by
      funext q
      simp only [F, one_smul]
    dsimp only [Q]
    rw [hfun]
    exact curveVelocity_riemannianExp_affine (I := I) (M := M) hv
  rw [one_mul, sub_eq_zero, hPone, hQone] at hone
  have hbaseeq : F 0 1 = riemannianExp I M p v := by
    simp only [F, zero_smul, add_zero, one_smul]
  rw [hbaseeq] at hone
  have hsymm := (real_inner_comm
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v))
  simpa only [F, zero_smul, add_zero, one_smul] using hsymm.trans hone

end TauCeti.Manifold

end
