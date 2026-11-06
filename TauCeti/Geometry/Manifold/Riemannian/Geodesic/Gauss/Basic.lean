/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.VariationField
import Mathlib.Analysis.InnerProductSpace.Calculus

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
* `TauCeti.Manifold.norm_mfderiv_riemannianExp_radial`: the differential of the exponential map
  preserves the norm of the radial direction.

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

variable [I.Boundaryless] [T2Space M] {p : M} {v w : TangentSpace I p}
  {F : ℝ → ℝ → M}

/-! ### The radial variation

The Gauss lemma is proved by differentiating the radial variation

`F (u, t) = exp_p (t • (v + u • w))`

of the geodesic `t ↦ exp_p (t • v)`.  Each radial curve of the variation is a maximal geodesic
and the variation is smooth wherever the exponential map is
(`TauCeti.Manifold.radialVariation_eq_maximalGeodesic`,
`TauCeti.Manifold.contMDiffAt_radialVariation`).  The facts below add what the variational
argument consumes beyond these: the transverse covariant derivative of the radial velocity field is
determined by the constant speed of those geodesics.  As in the shared API, the variation is a
function `F` together with its defining equation. -/

/-- A radial curve of the variation has the squared speed of its initial velocity. -/
private theorem inner_curveVelocity_radialVariation_self
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {u t : ℝ}
    (ht : t ∈ geodesicInterval I M p (v + u • w)) :
    inner ℝ (curveVelocity I (F u) t) (curveVelocity I (F u) t) =
      inner ℝ (v + u • w) (v + u • w) := by
  rw [radialVariation_eq_maximalGeodesic hF u]
  exact inner_curveVelocity_maximalGeodesic_self ht

/-- **Metric compatibility along the radial variation.**  At a parameter of the central geodesic,
the inner product of the covariant derivative along that geodesic of the variation field with the
radial velocity is `⟪v, w⟫`.  It is half the transverse derivative at `u = 0` of the squared speed
of the radial curves, which is `⟪v + u • w, v + u • w⟫` at parameter `u` because that curve is a
geodesic. -/
private theorem inner_alongCurve_variationField_radialVariation
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
        (curveVelocity I (F 0) t) =
      inner ℝ v w := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have htExp : t • v ∈ expDomain I M p :=
    mem_geodesicInterval_iff_smul_mem_expDomain.mp ht
  have hsurface : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    contMDiffAt_radialVariation hF (u := 0) (t := t) (by simpa using htExp)
  have hleft := hasDerivAt_norm_sq_curveVelocity (hsurface.of_le (by simp))
  -- Near `u = 0` the radial curve of the variation still reaches `t`, so its squared speed there
  -- is the squared norm `⟪v + u • w, v + u • w⟫` of its initial velocity.
  have hnear : ∀ᶠ u in nhds (0 : ℝ), t ∈ geodesicInterval I M p (v + u • w) :=
    eventually_mem_geodesicInterval_add_smul ht
  have heq : (fun u ↦ ‖curveVelocity I (F u) t‖ ^ 2) =ᶠ[nhds (0 : ℝ)]
      fun u ↦ inner ℝ (v + u • w) (v + u • w) :=
    hnear.mono fun u hu ↦
      (real_inner_self_eq_norm_sq _).symm.trans (inner_curveVelocity_radialVariation_self hF hu)
  have ha : HasDerivAt (fun u : ℝ ↦ v + u • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add v
  have hderiv_eq := hleft.unique ((ha.inner ℝ ha).congr_of_eventuallyEq heq)
  rw [zero_smul, add_zero, real_inner_comm v w, ← two_mul] at hderiv_eq
  exact mul_left_cancel₀ two_ne_zero hderiv_eq

/-- For the radial variation `F`, at every `t ∈ geodesicInterval I M p v`, the inner product
of the variation field with the central geodesic's velocity has derivative `⟪v, w⟫`. -/
private theorem hasDerivAt_inner_variationField_radialVariation
    (hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w))) {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) :
    HasDerivAt (fun r ↦ inner ℝ (variationField I F r) (curveVelocity I (F 0) r))
      (inner ℝ v w) t := by
  -- Apply the product rule, the vanishing acceleration of the central geodesic, and the
  -- metric-compatibility identity above.
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have htExp : t • v ∈ expDomain I M p := mem_geodesicInterval_iff_smul_mem_expDomain.mp ht
  have hprod := hasDerivAt_inner_variationField_curveVelocity
    ((contMDiffAt_radialVariation hF (u := 0) (t := t) (by simpa using htExp)).of_le (by simp))
  rwa [acceleration_radialVariation_eq_zero hF (u := 0) (by simpa using ht), inner_zero_right,
    add_zero, inner_alongCurve_variationField_radialVariation hF ht] at hprod

end RadialVariation

/-- **The Gauss lemma.** The differential of the Riemannian exponential map preserves the inner
product with the radial direction at every vector in its natural domain. -/
theorem inner_mfderiv_riemannianExp_radial [I.Boundaryless]
    [T2Space M] {p : M} {v w : TangentSpace I p}
    (hv : v ∈ expDomain I M p) :
    inner ℝ
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w) =
      inner ℝ v w := by
  let F : ℝ → ℝ → M := fun u t ↦ riemannianExp I M p (t • (v + u • w))
  have hF : ∀ u t : ℝ, F u t = riemannianExp I M p (t • (v + u • w)) := fun _ _ ↦ rfl
  have hIcc : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.mp hv)
  have hmain (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    hasDerivAt_inner_variationField_radialVariation hF (hIcc ht)
  -- `⟪∂ᵤ F, ∂ₜ F⟫` and `t ⟪v, w⟫` have the same derivative on `[0, 1]` and agree at `0`, where
  -- the transverse field vanishes; so they agree at `1`.
  have hone := eq_of_has_deriv_right_eq (f' := fun _ ↦ inner ℝ v w)
    (g := fun r : ℝ ↦ r * inner ℝ v w)
    (fun t ht ↦ (hmain t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t _ ↦ (hasDerivAt_mul_const _).hasDerivWithinAt)
    (fun t ht ↦ (hmain t ht).continuousAt.continuousWithinAt)
    (continuous_id.mul continuous_const).continuousOn
    (by rw [variationField_eq_zero (.of_forall fun s ↦ (radialVariation_apply_zero hF s).trans
      (radialVariation_apply_zero hF 0).symm), inner_zero_left, zero_mul]) 1 (by simp)
  -- Identify both velocities at `t = 1` with differentials of the exponential map.
  have hPone : curveVelocity I (F 0) 1 =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v := by
    have h := curveVelocity_riemannianExp_smul (I := I) (M := M) (v := v) (t := 1)
      (by simpa using hv)
    rw [one_smul] at h
    rw [radialVariation_zero hF]
    exact h
  have hQone := variationField_radialVariation hF (mem_expDomain_iff.mp hv)
  rw [one_smul, one_smul] at hQone
  rw [one_mul, hPone, hQone] at hone
  have hbaseeq : F 0 1 = riemannianExp I M p v := by
    simp only [F, zero_smul, add_zero, one_smul]
  rw [hbaseeq] at hone
  have hsymm := (real_inner_comm
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w)
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v))
  simpa only [F, zero_smul, add_zero, one_smul] using hsymm.trans hone

/-- **Radial norm preservation.** The differential of the Riemannian exponential map preserves
the norm of the radial direction at every vector in its natural domain. -/
@[simp] theorem norm_mfderiv_riemannianExp_radial [I.Boundaryless]
    [T2Space M] {p : M} {v : TangentSpace I p}
    (hv : v ∈ expDomain I M p) :
    ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq,
    ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm,
    inner_mfderiv_riemannianExp_radial hv]

end TauCeti.Manifold

end
