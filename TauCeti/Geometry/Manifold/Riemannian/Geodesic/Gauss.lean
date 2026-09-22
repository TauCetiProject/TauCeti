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

section RadialVariation

variable [I.Boundaryless] [T2Space (TangentBundle I M)] {p : M} {v w : TangentSpace I p}
  {F : ℝ → ℝ → M}

/-! ### The radial variation

The Gauss lemma is proved by differentiating the radial variation

`F (u, t) = exp_p (t • (v + u • w))`

of the geodesic `t ↦ exp_p (t • v)`.  The facts below are what the variational argument consumes:
each radial curve of the variation is a maximal geodesic, the variation is smooth wherever the
exponential map is, and the transverse covariant derivative of the radial velocity field is
determined by the constant speed of those geodesics.

Each statement takes the variation as a function `F` together with its defining equation, rather
than as the explicit two-parameter formula.  The fibre in which a velocity vector lives is indexed
by the point of the curve, so rewriting a radial curve into the maximal geodesic it equals has to
reach the index as well; that is possible for `F u` and not for the formula, whose index appears
already evaluated. -/

/-- Each radial curve of the variation is the maximal geodesic with the corresponding initial
velocity. -/
private theorem radialVariation_eq_maximalGeodesic
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) (u : ℝ) :
    F u = maximalGeodesic I M p (v + u • w) :=
  funext fun t ↦ (hF u t).trans (riemannianExp_smul p (v + u • w) t)

/-- The radial variation is smooth at every parameter pair whose radial vector lies in the natural
domain of the exponential map. -/
private theorem contMDiffAt_radialVariation
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

/-- The covariant acceleration of a radial curve of the variation vanishes on its maximal
interval. -/
private theorem alongCurve_curveVelocity_radialVariation_eq_zero
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {u t : ℝ}
    (ht : t ∈ geodesicInterval I M p (v + u • w)) :
    alongCurve (leviCivitaConnection I M) (F u) (curveVelocity I (F u)) t = 0 := by
  rw [radialVariation_eq_maximalGeodesic hF u]
  exact alongCurve_curveVelocity_maximalGeodesic_eq_zero ht

/-- A radial curve of the variation has the squared speed of its initial velocity. -/
private theorem inner_curveVelocity_radialVariation_self
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {u t : ℝ}
    (ht : t ∈ geodesicInterval I M p (v + u • w)) :
    inner ℝ (curveVelocity I (F u) t) (curveVelocity I (F u) t) =
      inner ℝ (v + u • w) (v + u • w) := by
  rw [radialVariation_eq_maximalGeodesic hF u]
  exact inner_curveVelocity_maximalGeodesic_self ht

/-- **Metric compatibility along the radial variation.**  At a parameter of the central geodesic,
the inner product of the transverse covariant derivative of the radial velocity field with that
radial velocity is `⟪v, w⟫`.  It is half the derivative at `u = 0` of the squared speed
`⟪v + u • w, v + u • w⟫`, which is the squared speed of the radial curve at parameter `u` because
that curve is a geodesic. -/
private theorem inner_alongCurve_curveVelocity_radialVariation
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    inner ℝ
        (alongCurve (leviCivitaConnection I M) (fun q ↦ F q t)
          (fun q ↦ curveVelocity I (F q) t) 0)
        (curveVelocity I (F 0) t) =
      inner ℝ v w := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have htExp : t • v ∈ expDomain I M p :=
    mem_geodesicInterval_iff_smul_mem_expDomain.mp ht
  have hsurface : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    contMDiffAt_radialVariation hF (u := 0) (t := t) (by simpa using htExp)
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  have hfield := (hsurface.of_le (by simp))
    |>.differentiableAt_sectionCoord_curveVelocity_snd (f := F) hbase
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) 0 :=
    (hsurface.comp 0 (contMDiff_iff_contDiff.mpr
      (contDiff_prodMk_left (n := ∞) t)).contMDiffAt).mdifferentiableAt (by simp)
  have hleft := (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve hcurve hfield hfield
  -- Near `u = 0` the radial curve of the variation still reaches `t`, so its squared speed there
  -- is the squared norm `⟪v + u • w, v + u • w⟫` of its initial velocity.
  have hnear : ∀ᶠ u in nhds (0 : ℝ), t ∈ geodesicInterval I M p (v + u • w) := by
    have hopen := (isOpen_expDomain (I := I) (M := M) p).mem_nhds htExp
    have hcont : ContinuousAt (fun u : ℝ ↦ t • (v + u • w)) 0 := by fun_prop
    have hpre : (fun u : ℝ ↦ t • (v + u • w)) ⁻¹' expDomain I M p ∈ nhds 0 :=
      hcont.preimage_mem_nhds (by simpa using hopen)
    filter_upwards [hpre] with u hu
    exact mem_geodesicInterval_iff_smul_mem_expDomain.mpr hu
  have heq : (fun u ↦ inner ℝ (curveVelocity I (F u) t) (curveVelocity I (F u) t)) =ᶠ[nhds (0 : ℝ)]
      fun u ↦ inner ℝ (v + u • w) (v + u • w) :=
    hnear.mono fun u hu ↦ inner_curveVelocity_radialVariation_self hF hu
  have ha : HasDerivAt (fun u : ℝ ↦ v + u • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add v
  have hderiv_eq := hleft.unique ((ha.inner ℝ ha).congr_of_eventuallyEq heq)
  -- Both sides of the product rule are symmetric in their two arguments, so the identity halves.
  have halve : ∀ {x : M} (a b : TangentSpace I x) (c d : TangentSpace I p),
      inner ℝ a b + inner ℝ b a = inner ℝ d c + inner ℝ c d → inner ℝ a b = inner ℝ c d := by
    intro x a b c d h
    linarith [real_inner_comm a b, real_inner_comm c d]
  exact (halve _ _ _ _ hderiv_eq).trans (by rw [zero_smul, add_zero, real_inner_comm])

end RadialVariation

/-- **The Gauss lemma.** The differential of the Riemannian exponential map preserves the inner
product with the radial direction at every vector in its natural domain. -/
theorem inner_mfderiv_riemannianExp_radial [I.Boundaryless]
    [T2Space (TangentBundle I M)] {p : M} {v w : TangentSpace I p}
    (hv : v ∈ expDomain I M p) :
    inner ℝ
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w) =
      inner ℝ v w := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  let F : ℝ → ℝ → M := fun u t ↦ riemannianExp I M p (t • (v + u • w))
  let P : (u t : ℝ) → TangentSpace I (F u t) := fun u ↦ curveVelocity I (F u)
  let Q : (t u : ℝ) → TangentSpace I (F u t) :=
    fun t u ↦ curveVelocity I (fun q ↦ F q t) u
  let cov := leviCivitaConnection I M
  have hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w)) := fun _ _ ↦ rfl
  have hF_eq_maximal (u : ℝ) : F u = maximalGeodesic I M p (v + u • w) :=
    radialVariation_eq_maximalGeodesic hF u
  have hIcc : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.mp hv)
  -- Metric compatibility and symmetry of mixed covariant derivatives compute the derivative of
  -- `⟪∂ᵤ F, ∂ₜ F⟩` along the central radial geodesic.
  have hmain : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r ↦ inner ℝ (Q r 0) (P 0 r)) (inner ℝ v w) t := by
    intro t ht
    have htJ : t ∈ geodesicInterval I M p v := hIcc ht
    have htExp : t • v ∈ expDomain I M p :=
      mem_geodesicInterval_iff_smul_mem_expDomain.mp htJ
    have hsurface : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
      contMDiffAt_radialVariation hF (u := 0) (t := t) (by simpa using htExp)
    have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
    have haccel : alongCurve cov (F 0) (curveVelocity I (F 0)) t = 0 :=
      alongCurve_curveVelocity_radialVariation_eq_zero hF (u := 0) (by simpa using htJ)
    have hDuP_inner : inner ℝ (alongCurve cov (fun q ↦ F q t) (fun q ↦ P q t) 0) (P 0 t) =
        inner ℝ v w :=
      inner_alongCurve_curveVelocity_radialVariation hF htJ
    have hQcoord := (hsurface.of_le (by simp))
      |>.differentiableAt_sectionCoord_curveVelocity_fst (f := F) hbase
    have hPcoord : DifferentiableAt ℝ
        (sectionCoord (F := E) (F 0) (curveVelocity I (F 0)) (F 0 t)) t := by
      have hFzero : F 0 = maximalGeodesic I M p v := by
        simpa using hF_eq_maximal 0
      exact differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (M := M) (γ := F 0)
        ((isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v)
          |>.isGeodesicCurveOn.contMDiffOn.congr fun r _ ↦ congrFun hFzero r)
        isOpen_geodesicInterval htJ
    have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (F 0) t :=
      (hsurface.comp t (contMDiff_iff_contDiff.mpr
        (contDiff_prodMk_right (n := ∞) 0)).contMDiffAt).mdifferentiableAt (by simp)
    have hprod := (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
      |>.hasDerivAt_inner_alongCurve hcurve hQcoord hPcoord
    have hswap := CovariantDerivative.alongCurve_curveVelocity_comm cov
      ((CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2
        (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I))
      (f := F) (u := 0) (v := t) (hsurface.of_le (by simp))
    rw [haccel, inner_zero_right, add_zero, hswap, hDuP_inner] at hprod
    simpa only [P, Q] using hprod
  have hzero : inner ℝ (Q 0 0) (P 0 0) = 0 := by
    have hQzero : Q 0 0 = 0 := by
      have hfun : (fun q : ℝ ↦ F q 0) = fun _ ↦ p := by
        funext q
        simp only [F, zero_smul, riemannianExp_zero]
      have hbase : F 0 0 = p := by
        simp only [F, zero_smul, riemannianExp_zero]
      dsimp only [Q]
      rw [hbase]
      rw [hfun, curveVelocity_const]
    rw [hQzero, inner_zero_left]
  -- The preceding derivative identity makes `⟪∂ᵤ F, ∂ₜ F⟩ - t ⟨v,w⟩` constant on
  -- `[0,1]`; its value at zero is zero.
  have hconst : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ (Q t 0) (P 0 t) - t * inner ℝ v w = 0 := by
    let g : ℝ → ℝ := fun t ↦ inner ℝ (Q t 0) (P 0 t) - t * inner ℝ v w
    have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := by
      intro t ht
      have hlin : HasDerivAt (fun s : ℝ ↦ s * inner ℝ v w) (inner ℝ v w) t :=
        hasDerivAt_mul_const (inner ℝ v w)
      have hsub := (hmain t ht).sub hlin
      -- `HasDerivAt.sub` concludes for the pointwise difference `f - g` of two functions into
      -- `ℝ`, carrying the module instance `RCLike.toInnerProductSpaceReal.toModule`, whereas `g`
      -- is the explicit lambda below with `Semiring.toModule`.  The two instances are equal but
      -- not syntactically so; this `change` presents the conclusion in the goal's form before its
      -- derivative is simplified.
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
  -- Evaluate the constant identity at one and identify both velocities with differentials of
  -- the exponential map.
  have hone := hconst 1 (by simp)
  have hPone : P 0 1 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v := by
    have hfun : F 0 = fun t : ℝ ↦ riemannianExp I M p (t • v) := by
      funext t
      simp only [F, zero_smul, add_zero]
    have h := curveVelocity_riemannianExp_smul (I := I) (M := M) (v := v) (t := 1)
      (by simpa using hv)
    rw [one_smul] at h
    dsimp only [P]
    rw [hfun]
    exact h
  have hQone : Q 1 0 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w := by
    have hfun : (fun q : ℝ ↦ F q 1) =
        fun q : ℝ ↦ riemannianExp I M p (v + q • w) := by
      funext q
      simp only [F, one_smul]
    have h := curveVelocity_riemannianExp_add_smul (I := I) (M := M) (v := v) (w := w) (u := 0)
      (by simpa using hv)
    rw [zero_smul, add_zero] at h
    dsimp only [Q]
    rw [hfun]
    exact h
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
