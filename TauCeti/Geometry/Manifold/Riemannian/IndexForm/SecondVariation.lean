/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# The second variation of energy

Let `F` be a two-parameter family of curves in a Riemannian manifold, with central curve
`γ = F 0`, variation field `V(t) = ∂_s F (0, t)` (`TauCeti.Manifold.variationField`) and
transverse acceleration `A(t) = D_s ∂_s F (0, t)`, the covariant acceleration at `s = 0` of the
transverse curve `s ↦ F s t`. This file computes the second derivative at `s = 0` of the energy
`E(s) = ½ ∫_a^b ‖∂_t F (s, t)‖² dt` (`TauCeti.Manifold.energy`) of the curves `F s`:

`E''(0) = I(V, V) + ∫_a^b ⟪D_t A, γ'⟫ dt`,

where `I(V, V) = ∫_a^b ‖D_t V‖² - ⟪R(V, γ') γ', V⟫ dt` is the index form
(`TauCeti.Manifold.indexForm`). When `γ` is a geodesic the last integral is a boundary term:

`E''(0) = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`,

and for a variation with fixed endpoints the transverse acceleration vanishes at `a` and `b`, so
`E''(0) = I(V, V)`: the Hessian of the energy at a geodesic, on variations with fixed endpoints,
is the index form. This is how the index form computes the index and nullity of the energy at its
critical points.

The family is assumed `C³` at the points of `{0} × [a, b]`. Differentiating the energy twice
under the integral sign gives half the integral of `∂_s² ‖∂_t F‖²` at `s = 0`. Pointwise,
`½ ∂_s ‖∂_t F‖² = ⟪D_s ∂_t F, ∂_t F⟫` and, differentiating again,
`½ ∂_s² ‖∂_t F‖² = ⟪D_s D_s ∂_t F, ∂_t F⟫ + ‖D_s ∂_t F‖²`. The symmetry lemma
`D_s ∂_t F = D_t ∂_s F` (`CovariantDerivative.alongCurve_curveVelocity_comm`) turns
`D_s D_s ∂_t F` into `D_s D_t ∂_s F`, which is `D_t D_s ∂_s F + R(∂_s F, ∂_t F) ∂_s F` by the
commutation of covariant derivatives on a surface
(`CovariantDerivative.alongCurve_alongCurve_sub_alongCurve_alongCurve`). At `s = 0` this is
`D_t A + R(V, γ') V`, and the skew-symmetry of the curvature tensor rewrites
`⟪R(V, γ') V, γ'⟫` as `-⟪R(V, γ') γ', V⟫`.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_energy`: **the second variation formula** of the energy,
  `E''(0) = I(V, V) + ∫_a^b ⟪D_t A, γ'⟫ dt`.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_acceleration_eq_zero`: the second variation of the
  energy at a geodesic, `E''(0) = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_acceleration_eq_zero`:
  for a variation of a geodesic with fixed endpoints, `E''(0) = I(V, V)`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §13, Theorem 13.1
  (the second variation formula).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Proposition 2.8.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Ch. 10, section The Second Variation Formula (stated there for the length of unit-speed
  geodesics rather than for the energy).
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M} {a b : ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
variable (I) in
/-- The squared speed `‖∂_t F‖²` of the family at `z = (s, t)`, written through the differential
of the uncurried family. -/
private abbrev sqSpeed (F : ℝ → ℝ → M) (z : ℝ × ℝ) : ℝ :=
  inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The squared speed is `C²` on the open set of points where the family is `C³`. -/
private theorem contDiffOn_sqSpeed :
    ContDiffOn ℝ 2 (sqSpeed I F)
      {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  exact (show ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2)
    {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} from
      fun _ hz ↦ hz.contMDiffWithinAt).contDiffOn_inner_mfderiv (by norm_num)
        (TauCeti.isOpen_setOfPred_contMDiffAt (by simp)) _ _

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- At a point `(s, t)` where the family is `C³`, the velocities `P q = ∂_t F (q, t)` form a `C²`
field along the transverse curve `q ↦ F q t`, which is differentiable at `s`. -/
private theorem contMDiffAt_curveVelocity_slice {s t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
        (fun q ↦ TotalSpace.mk' E (F q t) (curveVelocity I (F q) t)) s ∧
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) s := by
  have hP := hF.contMDiffAt_curveVelocity_snd_slice (m := 2) (by norm_num)
  exact ⟨hP, ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp s hP).mdifferentiableAt
    two_ne_zero⟩

/-- **The second transverse derivative of the squared speed.** At a parameter `t` where the
family is `C³`, the transverse derivative at `s = 0` of `⟪D_s ∂_t F, ∂_t F⟫ = ½ ∂_s ‖∂_t F‖²` is
the index-form integrand `‖D_t V‖² - ⟪R(V, γ') γ', V⟫` plus `⟪D_t A, γ'⟫`, where `V` is the
variation field, `γ = F 0` and `A` the transverse acceleration. -/
private theorem hasDerivAt_inner_alongCurve_curveVelocity {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun q ↦ inner ℝ
        (alongCurve (leviCivitaConnection I M) (fun q ↦ F q t)
          (fun q ↦ curveVelocity I (F q) t) q) (curveVelocity I (F q) t))
      (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
          (curveVelocity I (F 0) t)) 0 := by
  set cov := leviCivitaConnection I M
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hcov := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have htor : cov.IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)
  have hF2 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I (minSmoothness ℝ 2) (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    hF.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  -- The velocity field `P q = ∂_t F (q, t)` along the transverse curve `c q = F q t` is `C²`, so
  -- `X = D_s P` has differentiable coordinates and the product rule applies to `⟪X, P⟫`.
  obtain ⟨hP, hc⟩ := contMDiffAt_curveVelocity_slice hF
  have hprod := hcov.hasDerivAt_inner_alongCurve hc
    (differentiableAt_sectionCoord_alongCurve_leviCivitaConnection hP)
    (differentiableAt_sectionCoord (fun q ↦ F q t) _ (hP.mdifferentiableAt two_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _))
  -- By the symmetry lemma, `X q = D_t ∂_s F (q, t)` for `q` near `0`; at `q = 0` it is `D_t V`.
  have hsymm : ∀ᶠ q in 𝓝 0,
      alongCurve cov (fun q ↦ F q t) (fun q ↦ curveVelocity I (F q) t) q =
        alongCurve cov (F q) (fun r ↦ curveVelocity I (fun q' ↦ F q' r) q) t := by
    have hF' : ∀ᶠ q in 𝓝 (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I (minSmoothness ℝ 2)
        (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t) :=
      ((continuous_id.prodMk continuous_const).tendsto 0).eventually
        ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF2)
    filter_upwards [hF'] with q hq
    exact (alongCurve_curveVelocity_comm cov htor hq).symm
  -- Exchanging the covariant derivatives costs the curvature term.
  have hcomm := alongCurve_alongCurve_sub_alongCurve_alongCurve cov
    (W := fun q r ↦ curveVelocity I (fun q' ↦ F q' r) q) (u := 0) (v := t)
    (hF.contMDiffAt_curveVelocity_fst (m := 2) (by norm_num))
  simp only [← acceleration_def] at hcomm
  rw [alongCurve_congr cov _ _ hsymm, hsymm.self_of_nhds, sub_eq_iff_eq_add.mp hcomm] at hprod
  refine hprod.congr_deriv ?_
  rw [indexFormIntegrand_def, ← variationField_def, ← variationField_apply, inner_add_left,
    hcov.inner_curvatureTensor_eq_neg (F 0 t) (variationField I F t) (curveVelocity I (F 0) t)
      (variationField I F t), real_inner_comm (variationField I F t)]
  ring

omit [T2Space M] in
/-- **The transverse derivative of the squared speed.** At a point `(s, t)` where the family is
`C³`, the partial derivative in `s` of the squared speed `‖∂_t F‖²`, written through the
differential of the uncurried family, is `2 ⟪D_s ∂_t F, ∂_t F⟫`. -/
private theorem fderiv_inner_mfderiv_snd_eq {s t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t)) :
    fderiv ℝ (sqSpeed I F) (s, t) (1, 0) =
      2 * inner ℝ (alongCurve (leviCivitaConnection I M) (fun q ↦ F q t)
        (fun q ↦ curveVelocity I (F q) t) s) (curveVelocity I (F s) t) := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have hWo := TauCeti.isOpen_setOfPred_contMDiffAt (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I)
    (f := fun z : ℝ × ℝ ↦ F z.1 z.2) (n := 3) (by simp)
  have hGs := TauCeti.hasDerivAt_slice_left ((contDiffOn_sqSpeed.differentiableOn two_ne_zero _ hF)
    |>.differentiableAt (hWo.mem_nhds hF))
  -- Near `s`, the squared speed is `⟪P, P⟫` for the field `P q = ∂_t F (q, t)` along the transverse
  -- curve `q ↦ F q t`, which the product rule differentiates.
  obtain ⟨hP, hc⟩ := contMDiffAt_curveVelocity_slice hF
  have hP' := differentiableAt_sectionCoord (fun q ↦ F q t) _ (hP.mdifferentiableAt two_ne_zero)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F s t))
  have heq : ∀ᶠ q in 𝓝 s, sqSpeed I F (q, t) =
        inner ℝ (curveVelocity I (F q) t) (curveVelocity I (F q) t) := by
    filter_upwards [((Continuous.prodMk_left t).tendsto s).eventually (hWo.mem_nhds hF)]
      with q hq
    rw [curveVelocity_eq_mfderiv_snd ((hq : ContMDiffAt _ _ 3 _ _).mdifferentiableAt
      (by norm_num))]
  rw [hGs.unique (((isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve hc hP' hP').congr_of_eventuallyEq heq),
    real_inner_comm (curveVelocity I (F s) t)]
  ring

/-- **The integrand of the second variation.** At a parameter `t` where the family is `C³`, half
the second partial derivative in `s` at `s = 0` of the squared speed `‖∂_t F‖²` is the
index-form integrand of the variation field plus `⟪D_t A, γ'⟫`. -/
private theorem fderiv_fderiv_inner_mfderiv_snd_eq {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    fderiv ℝ (fun y : ℝ × ℝ ↦ fderiv ℝ (sqSpeed I F) y (1, 0)) (0, t) (1, 0) / 2 =
      indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
          (curveVelocity I (F 0) t) := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have hWo := TauCeti.isOpen_setOfPred_contMDiffAt (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I)
    (f := fun z : ℝ × ℝ ↦ F z.1 z.2) (n := 3) (by simp)
  -- The squared speed is `C²` on the open set of `C³` points, so its partial derivative in `s` is
  -- `C¹` there.
  have hG₁s := TauCeti.hasDerivAt_slice_left (((contDiffOn_sqSpeed.fderiv_of_isOpen hWo (m := 1)
    (by norm_num)).clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).differentiableOn
      one_ne_zero _ hF |>.differentiableAt (hWo.mem_nhds hF))
  have heq : ∀ᶠ q in 𝓝 (0 : ℝ), fderiv ℝ (sqSpeed I F) (q, t) (1, 0) =
      2 * inner ℝ (alongCurve (leviCivitaConnection I M) (fun q ↦ F q t)
        (fun q ↦ curveVelocity I (F q) t) q) (curveVelocity I (F q) t) := by
    filter_upwards [((Continuous.prodMk_left t).tendsto 0).eventually (hWo.mem_nhds hF)]
      with q hq
    exact fderiv_inner_mfderiv_snd_eq hq
  rw [hG₁s.unique (((hasDerivAt_inner_alongCurve_curveVelocity hF).const_mul 2)
    |>.congr_of_eventuallyEq heq)]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Differentiation of the energy under the integral sign.** If the family is `C²` on an open
box `U ×ˢ V` with `[a, b] ⊆ V`, then at every `s ∈ U` the energy of the curves `F s` between `a`
and `b` has derivative half the integral of the partial derivative in `s` of the squared speed. -/
private theorem hasDerivAt_energy_integral_fderiv {U V : Set ℝ} (hUo : IsOpen U)
    (hVo : IsOpen V) (hV : uIcc a b ⊆ V)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (U ×ˢ V)) {s : ℝ}
    (hs : s ∈ U) :
    HasDerivAt (fun s ↦ energy I (F s) a b)
      ((∫ t in a..b, fderiv ℝ (sqSpeed I F) (s, t) (1, 0)) / 2) s := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  have henergy : (fun s ↦ energy I (F s) a b) =ᶠ[𝓝 s]
      fun s ↦ (∫ t in a..b, sqSpeed I F (s, t)) / 2 := by
    filter_upwards [hUo.mem_nhds hs] with q hq
    rw [energy_def]
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [sqSpeed, ← curveVelocity_eq_mfderiv_snd ((hF.contMDiffAt (hUVo.mem_nhds ⟨hq, hV ht⟩))
      |>.mdifferentiableAt two_ne_zero), real_inner_self_eq_norm_sq]
  exact ((TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo
    (hF.contDiffOn_inner_mfderiv (by norm_num) hUVo _ _)
    (prod_mono (singleton_subset_iff.mpr hs) hV)).2.div_const 2).congr_of_eventuallyEq henergy

/-- **The second variation of energy, with the integrability of its acceleration term.** For a
family `F` which is `C³` at every point of `{0} × [a, b]`, the pairing `⟪D_t A, γ'⟫` of the
covariant derivative of the transverse acceleration with the velocity of `γ = F 0` is interval
integrable, and the derivative of the energy has derivative `I(V, V) + ∫_a^b ⟪D_t A, γ'⟫ dt` at
`s = 0`. -/
private theorem intervalIntegrable_and_hasDerivAt_deriv_energy
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    IntervalIntegrable (fun t ↦ inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
        (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
        (curveVelocity I (F 0) t)) volume a b ∧
      HasDerivAt (deriv fun s ↦ energy I (F s) a b)
        (indexForm I (F 0) (variationField I F) (variationField I F) a b +
          ∫ t in a..b, inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
            (curveVelocity I (F 0) t)) 0 := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  have hsurf : ∀ {t : ℝ}, t ∈ V →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    fun ht ↦ hfUV.contMDiffAt (hUVo.mem_nhds ⟨h0U, ht⟩)
  -- Differentiating twice under the integral sign, `E''(0)` is half the integral of the second
  -- partial derivative in `s` of the squared speed.
  obtain ⟨hint, hG₁deriv⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo
    ((hfUV.contDiffOn_inner_mfderiv (m := 2) (by norm_num) hUVo _ _).fderiv_of_isOpen hUVo
      (m := 1) (by norm_num) |>.clm_apply contDiffOn_const)
    (prod_mono (singleton_subset_iff.mpr h0U) hV)
  have hderiv := (hG₁deriv.div_const 2).congr_of_eventuallyEq
    (Filter.mem_of_superset (hUo.mem_nhds h0U) fun s hs ↦
      (hasDerivAt_energy_integral_fderiv hUo hVo hV (hfUV.of_le (by norm_num)) hs).deriv)
  -- The variation field has a `C²` lift on `V`, so the index-form integrand is integrable.
  have hVuIcc : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := fun t ht ↦
    ((hsurf (hV ht)).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
  have hIint := intervalIntegrable_indexFormIntegrand hVuIcc hVuIcc
  have hAeq := fun t (ht : t ∈ uIcc a b) ↦ fderiv_fderiv_inner_mfderiv_snd_eq (hsurf (hV ht))
  have hAint : IntervalIntegrable (fun t ↦ inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
      (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
      (curveVelocity I (F 0) t)) volume a b :=
    ((hint.div_const 2).sub hIint).congr_uIoo fun t ht ↦ by
      beta_reduce
      rw [hAeq t (uIoo_subset_uIcc_self ht), add_sub_cancel_left]
  refine ⟨hAint, hderiv.congr_deriv ?_⟩
  rw [← intervalIntegral.integral_div, intervalIntegral.integral_congr hAeq,
    intervalIntegral.integral_add hIint hAint, indexForm_def]

/-- **The second variation of energy.** Let `F` be a two-parameter family which is `C³` at every
point of `{0} × [a, b]`, with central curve `γ = F 0`, variation field `V` and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`, the acceleration at `s = 0` of `s ↦ F s t`. Then the
derivative of the energy of the curves `F s` between `a` and `b` has derivative

`I(V, V) + ∫_a^b ⟪D_t A(t), γ'(t)⟫ dt`

at `s = 0`, where `I` is the index form. -/
theorem hasDerivAt_deriv_energy
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        ∫ t in a..b, inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
          (curveVelocity I (F 0) t)) 0 :=
  (intervalIntegrable_and_hasDerivAt_deriv_energy hF).2

/-- **The second variation of energy at a geodesic.** Let `F` be a two-parameter family which is
`C³` at every point of `{0} × [a, b]`, whose central curve `γ = F 0` has vanishing acceleration
on `[a, b]`. Then the derivative of the energy of the curves `F s` between `a` and `b` has
derivative

`I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`

at `s = 0`, where `V` is the variation field, `I` the index form and `A(t) = D_s ∂_s F (0, t)` the
transverse acceleration. -/
theorem hasDerivAt_deriv_energy_of_acceleration_eq_zero
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ uIcc a b, acceleration (leviCivitaConnection I M) (F 0) t = 0) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q a) 0)
          (curveVelocity I (F 0) a)) 0 := by
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  set cov := leviCivitaConnection I M
  obtain ⟨hAint, hE⟩ := intervalIntegrable_and_hasDerivAt_deriv_energy hF
  -- Along a geodesic, `⟪D_t A, γ'⟫` is the derivative of `⟪A, γ'⟫`.
  have hFTC : ∀ t ∈ uIcc a b, HasDerivAt
      (fun r ↦ inner ℝ (acceleration cov (fun q ↦ F q r) 0) (curveVelocity I (F 0) r))
      (inner ℝ (alongCurve cov (F 0) (fun r ↦ acceleration cov (fun q ↦ F q r) 0) t)
        (curveVelocity I (F 0) t)) t := by
    intro t ht
    have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 3 (F 0) t :=
      (hF t ht).comp t
        (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt
    have hA := differentiableAt_sectionCoord_alongCurve_snd cov (f := fun r q ↦ F q r)
      (W := fun r q ↦ curveVelocity I (fun q' ↦ F q' r) q) (u := t) (v := 0)
      ((hF t ht).comp (t, 0) (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffAt
        |>.contMDiffAt_curveVelocity_snd (f := fun r q ↦ F q r) (by norm_num))
    simp only [← acceleration_def] at hA
    have hd := (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
      |>.hasDerivAt_inner_alongCurve (hγt.mdifferentiableAt (by norm_num)) hA
      ((hγt.of_le (by norm_num)).differentiableAt_sectionCoord_curveVelocity)
    rw [← acceleration_def, hγ t ht, inner_zero_right, add_zero] at hd
    exact hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFTC hAint] at hE
  convert hE using 1
  ring

/-- **The Hessian of the energy at a geodesic is the index form.** For a variation `F` with fixed
endpoints between `a` and `b`, `C³` at every point of `{0} × [a, b]`, whose central curve
`γ = F 0` has vanishing acceleration on `[a, b]`, the derivative of the energy of the curves
`F s` has derivative `I(V, V)` at `s = 0`, where `V` is the variation field and `I` the index
form. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_acceleration_eq_zero
    (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : ∀ t ∈ uIcc a b, acceleration (leviCivitaConnection I M) (F 0) t = 0) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  have h := TauCeti.Manifold.hasDerivAt_deriv_energy_of_acceleration_eq_zero hF.contMDiffAt hγ
  have ha : (fun q ↦ F q a) =ᶠ[𝓝 0] fun _ ↦ F 0 a := hF.eventually_apply_left
  have hb : (fun q ↦ F q b) =ᶠ[𝓝 0] fun _ ↦ F 0 b := hF.eventually_apply_right
  rwa [ha.acceleration_eq, hb.acceleration_eq, acceleration_const, acceleration_const,
    inner_zero_left, inner_zero_left, add_zero, sub_zero] at h

end TauCeti.Manifold

end
