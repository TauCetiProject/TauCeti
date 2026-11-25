/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Variation
public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.Variation
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# The second variation of energy

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a Riemannian manifold, with central
curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)` and *transverse acceleration*
`A(t) = D_s ∂_s F (0, t)`, the covariant acceleration at `s = 0` of the transverse curve
`s ↦ F s t`. This file computes the second derivative at `s = 0` of the energy
`E(s) = ½ ∫_a^b ‖∂_t F (s, t)‖² dt` (`TauCeti.Manifold.energy`) of the curves `F s`:

`E''(0) = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`,

where `I(V, V) = ∫_a^b ‖D_t V‖² - ⟪R(V, γ') γ', V⟫ dt` is the index form
(`TauCeti.Manifold.indexForm`), for any family which is `C³` near `{0} × [a, b]`. When `γ` is a
geodesic the last integral vanishes, and only the endpoint terms `⟪A, γ'⟫` remain besides the
index form: this is the second variation with free endpoints. When moreover the endpoints are
fixed, `A` vanishes at `a` and `b`, and the second variation is the index form `I(V, V)`.

The integrand is computed pointwise. Twice differentiating `‖∂_t F‖²` in `s` along the
transverse curve, the symmetry lemma `D_s ∂_t F = D_t ∂_s F` and the commutation of the two
covariant derivatives up to curvature give

`½ ∂_s² ‖∂_t F‖² = ‖D_t V‖² - ⟪R(V, γ') γ', V⟫ + ⟪D_t A, γ'⟫` at `s = 0`

(`TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`). The last term is
`d/dt ⟪A, γ'⟫ - ⟪A, D_t γ'⟫`, and integrating gives the formula above.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`: the second transverse derivative of
  the squared speed.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_integral`: the second variation of energy as half the
  integral of the second transverse derivatives of the squared speed.
* `TauCeti.Manifold.hasDerivAt_deriv_energy`: **the second variation of energy** of a `C³`
  family, with endpoint terms and the acceleration term of the central curve.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_acceleration_eq_zero`: the second variation of
  energy along a geodesic, with free endpoints.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_acceleration_eq_zero`: for
  a variation of a geodesic with fixed endpoints, the second variation of energy is the index
  form.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`,
  `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy`,
  `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`,
  `TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn_of_curveVelocityLift_eq`, and
  `TauCeti.Manifold.hasDerivAt_deriv_energy_exponentialVariation`: second variation of energy along
  `IsGeodesicCurveOn` geodesics, general fixed-endpoint variations, smoothly closed variations, and
  exponential variations.
* `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy`,
  `TauCeti.Manifold.IsFixedEndpointVariation.indexForm_nonneg_of_isLocalMin_energy`,
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_of_curveVelocityLift_eq`,
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_exponentialVariation`, and
  `TauCeti.Manifold.eventually_energy_exponentialVariation_lt_of_indexForm_neg`: index-form
  nonnegativity at local minima of energy and strict energy shortening for negative-index fields.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §13, Theorem 13.1
  (the second variation formula; Milnor's energy has no factor `½`, so his Hessian is twice ours).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, the formula of the second
  variation.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 10, the second
  variation formula.
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
  {F : ℝ → ℝ → M}

/-- **The second transverse derivative of the squared speed.** At a parameter `t` where the
family is `C³`, the derivative at `s = 0` of `s ↦ d/ds ‖∂_t F (s, t)‖²` is twice
`‖D_t V(t)‖² - ⟪R(V, γ') γ', V⟫(t) + ⟪D_t A(t), γ'(t)⟫`, where `γ = F 0`, `V` is the variation
field and `A(r) = D_s ∂_s F (0, r)` is the transverse acceleration. The first two terms are the
integrand of the index form. -/
theorem hasDerivAt_deriv_norm_sq_curveVelocity {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      (2 * (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
          (curveVelocity I (F 0) t))) 0 := by
  set cov := leviCivitaConnection I M
  have hmet := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have htor : cov.IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- Along the transverse curve `q ↦ F q t`, the field `X q = ∂_t F (q, t)` has covariant
  -- derivative `Y q = D_t ∂_s F (q, t)` near `q = 0`, by the symmetry lemma.
  set X : ∀ q, TangentSpace I (F q t) := fun q ↦ curveVelocity I (F q) t
  set W : ∀ q r, TangentSpace I (F q r) := fun q r ↦ curveVelocity I (fun q' ↦ F q' r) q
  set Y : ∀ q, TangentSpace I (F q t) := fun q ↦ alongCurve cov (F q) (W q) t
  have hnear : ∀ᶠ q in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t) :=
    ((continuous_id.prodMk continuous_const).tendsto 0).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF)
  have hc {q : ℝ} (hq : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t)) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) q :=
    (hq.comp q (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 3) t)).contMDiffAt)
      |>.mdifferentiableAt (by norm_num)
  have hX {q : ℝ} (hq : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t)) :
      DifferentiableAt ℝ (sectionCoord ℝ (F := E) (fun q ↦ F q t) X (F q t)) q :=
    (hq.of_le (by norm_num)).differentiableAt_sectionCoord_curveVelocity_snd (f := F)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _)
  have hDX : ∀ᶠ q in 𝓝 0, alongCurve cov (fun q ↦ F q t) X q = Y q := by
    filter_upwards [hnear] with q hq
    exact (alongCurve_curveVelocity_comm cov htor
      (hq.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))).symm
  -- Near `0`, the first derivative of the squared speed is `2 ⟪Y, X⟫`.
  have hderiv : deriv (fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) =ᶠ[𝓝 0]
      fun q ↦ 2 * inner ℝ (Y q) (X q) := by
    filter_upwards [hnear, hDX] with q hq hqY
    have h := hmet.hasDerivAt_inner_alongCurve (hc hq) (hX hq) (hX hq)
    rw [hqY, real_inner_comm (Y q) (X q), ← two_mul] at h
    exact (h.congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ (real_inner_self_eq_norm_sq _).symm)).deriv
  -- The derivative of `⟪Y, X⟫` at `0`; exchanging the covariant derivatives in `D_s Y = D_s D_t W`
  -- costs the curvature term, and `D_t D_s W = D_t A`.
  have hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (F z.1 z.2) (W z.1 z.2)) (0, t) :=
    hF.contMDiffAt_curveVelocity_fst (by norm_num)
  have hYX := hmet.hasDerivAt_inner_alongCurve (hc hF)
    (differentiableAt_sectionCoord_alongCurve cov hW) (hX hF)
  have hcomm := alongCurve_alongCurve_sub_alongCurve_alongCurve cov hW
  rw [sub_eq_iff_eq_add'] at hcomm
  simp only [W, ← acceleration_def] at hcomm
  rw [hcomm, hDX.self_of_nhds] at hYX
  refine ((hYX.const_mul 2).congr_of_eventuallyEq hderiv).congr_deriv ?_
  rw [indexFormIntegrand_def, inner_add_left, hmet.inner_curvatureTensor_eq_neg,
    real_inner_comm (variationField I F t)]
  simp only [X, Y, W, cov, ← variationField_def, ← variationField_apply]
  ring

/-- The transverse acceleration `A(r) = D_s ∂_s F (0, r)` of a family which is `C³` at `(0, t)`
is differentiable at `t` as a field along the central curve. -/
private theorem differentiableAt_sectionCoord_acceleration_fst {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    DifferentiableAt ℝ (sectionCoord ℝ (F := E) (F 0)
      (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) (F 0 t)) t := by
  -- In the swapped family `(r, q) ↦ F q r`, the field `A` is the covariant derivative along the
  -- second-parameter curves of the transverse velocity.
  have hswap : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.2 z.1) (t, 0) :=
    hF.comp (t, 0) (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffAt
  simp only [acceleration_def]
  exact differentiableAt_sectionCoord_alongCurve (leviCivitaConnection I M) (f := fun r q ↦ F q r)
    (W := fun r q ↦ curveVelocity I (fun q' ↦ F q' r) q) (u := t) (v := 0)
    (hswap.contMDiffAt_curveVelocity_snd (f := fun r q ↦ F q r) (m := 2) (by norm_num))

/-- **The product rule for the transverse acceleration against the velocity.** At a parameter
where the family is `C³`, `r ↦ ⟪A(r), γ'(r)⟫` has derivative `⟪D_t A, γ'⟫ + ⟪A, D_t γ'⟫`,
where `γ = F 0` and `A(r) = D_s ∂_s F (0, r)`. -/
private theorem hasDerivAt_inner_acceleration_fst_curveVelocity {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0)
        (curveVelocity I (F 0) r))
      (inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0) t)
          (curveVelocity I (F 0) t) +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) t := by
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 3 (F 0) t :=
    hF.comp t (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F 0)
    ((hγu.mono interior_subset).of_le (by norm_num)) isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hu)
  rw [acceleration_def (γ := F 0)]
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).hasDerivAt_inner_alongCurve
    (hγt.mdifferentiableAt (by norm_num)) (differentiableAt_sectionCoord_acceleration_fst hF)
    hγcoord

/-- At a parameter where the family is `C³`, the pairing `⟪A(r), D_t γ'(r)⟫` of the transverse
acceleration with the acceleration of `γ = F 0` is continuous. -/
private theorem continuousAt_inner_acceleration_fst_acceleration {t : ℝ}
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContinuousAt (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0)
      (acceleration (leviCivitaConnection I M) (F 0) r)) t := by
  have hvel : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (F 0 r) (curveVelocity I (F 0) r)) t :=
    (hF.contMDiffAt_curveVelocity_snd (by norm_num)).comp t
      (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) (0 : ℝ))).contMDiffAt
  have hacc : DifferentiableAt ℝ (sectionCoord ℝ (F := E) (F 0)
      (acceleration (leviCivitaConnection I M) (F 0)) (F 0 t)) t := by
    rw [funext (acceleration_def (leviCivitaConnection I M) (F 0))]
    exact differentiableAt_sectionCoord_alongCurve_leviCivitaConnection hvel
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I (F 0) t :=
    (hF.comp t (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt)
      |>.mdifferentiableAt (by norm_num)
  exact ((isMetricCompatible_leviCivitaConnection (I := I) (M := M)).differentiableAt_inner hγt
    (differentiableAt_sectionCoord_acceleration_fst hF) hacc).continuousAt

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Differentiating the energy twice under the integral sign.** For a family which is `C³` at
every point of `{0} × [a, b]`, the second transverse derivatives `∂_s² ‖∂_t F (0, t)‖²` of the
squared speed are integrable on `[a, b]`, and the derivative of the energy of `F s` has at `s = 0`
the derivative half their integral. -/
theorem hasDerivAt_deriv_energy_integral {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    IntervalIntegrable (fun t ↦ deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0)
        volume a b ∧
      HasDerivAt (deriv fun s ↦ energy I (F s) a b)
        ((∫ t in a..b, deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0) / 2) 0 := by
  obtain ⟨U, V, hUo, hVo, h0U, hV, -, hG⟩ :=
    exists_isOpen_prod_contDiffOn_norm_sq_curveVelocity (m := 2) (by norm_num) (by simp) hF
  obtain ⟨hint, hmain⟩ := TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn (hUo.prod hVo)
    hG (prod_mono (singleton_subset_iff.mpr h0U) hV)
  refine ⟨hint, (hmain.div_const 2).congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)⟩
  -- the energy is half the integral of the squared speed
  simp only [energy_def, deriv_div_const]

/-- **The second variation of energy.** Let `F` be a two-parameter family which is `C³` at every
point of `{0} × [a, b]`, with central curve `γ = F 0`, variation field `V` and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`, the covariant acceleration at `s = 0` of `s ↦ F s t`.
Then the derivative of the energy of `F s` between `a` and `b` is differentiable at `s = 0`, with
derivative

`I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`,

where `I` is the index form of `γ` on `[a, b]` and `D_t γ'` is the covariant acceleration of
`γ`. -/
theorem hasDerivAt_deriv_energy {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q a) 0)
          (curveVelocity I (F 0) a) -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) 0 := by
  set cov := leviCivitaConnection I M
  obtain ⟨hint, hmain⟩ := hasDerivAt_deriv_energy_integral hF
  refine hmain.congr_deriv ?_
  -- Pointwise, half the second derivative of the squared speed is the index-form integrand plus
  -- `P = ⟪D_t A, γ'⟫`.
  set P : ℝ → ℝ := fun r ↦ inner ℝ (alongCurve cov (F 0)
    (fun r ↦ acceleration cov (fun q ↦ F q r) 0) r) (curveVelocity I (F 0) r)
  have hpt {t : ℝ} (ht : t ∈ uIcc a b) :
      deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0 / 2 =
        indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t + P t := by
    rw [(hasDerivAt_deriv_norm_sq_curveVelocity (hF t ht)).deriv]
    ring
  -- Both terms are integrable, and `⟪D_t A, γ'⟫ = d/dt ⟪A, γ'⟫ - ⟪A, D_t γ'⟫`.
  have hVfield : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) :=
    fun t ht ↦ ((hF t ht).contMDiffAt_variationField (by norm_num)).contMDiffWithinAt
  have hIint := intervalIntegrable_indexFormIntegrand hVfield hVfield
  have hPint : IntervalIntegrable P volume a b :=
    ((hint.div_const 2).sub hIint).congr_uIoo fun t ht ↦ by
      simp only [hpt (uIoo_subset_uIcc_self ht)]
      ring
  have hAint : IntervalIntegrable (fun t ↦ inner ℝ (acceleration cov (fun q ↦ F q t) 0)
      (acceleration cov (F 0) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_acceleration_fst_acceleration (hF t ht)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_inner_acceleration_fst_curveVelocity (hF t ht)) (hPint.add hAint)
  rw [intervalIntegral.integral_add hPint hAint] at hFTC
  calc (∫ t in a..b, deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0) / 2
      = ∫ t in a..b, (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          P t) := by
        rw [← intervalIntegral.integral_div]
        exact intervalIntegral.integral_congr fun t ht ↦ hpt ht
    _ = _ := by
        rw [intervalIntegral.integral_add hIint hPint, indexForm_def]
        linarith

/-- **The second variation of energy along a geodesic.** If the central curve `γ = F 0` of a
family which is `C³` at every point of `{0} × [a, b]` has vanishing covariant acceleration on the
open interval between `a` and `b`, that is, it is a geodesic there, then the derivative of the
energy of `F s` is differentiable at `s = 0`, with derivative `I(V, V) + ⟪A(b), γ'(b)⟫ -
⟪A(a), γ'(a)⟫`, where `I` is the index form, `V` the variation field and
`A(t) = D_s ∂_s F (0, t)` the transverse acceleration. -/
theorem hasDerivAt_deriv_energy_of_acceleration_eq_zero {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : ∀ t ∈ uIoo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q a) 0)
          (curveVelocity I (F 0) a)) 0 := by
  have hzero : ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0)
      (acceleration (leviCivitaConnection I M) (F 0) t) = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ 0) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [hγ t ht, inner_zero_right]
  simpa only [hzero, sub_zero] using hasDerivAt_deriv_energy hF

/-- **The second variation of energy at a geodesic with fixed endpoints is the index form.** For
a `C³` variation `F` with fixed endpoints between `a` and `b` of a curve `γ = F 0` with vanishing
covariant acceleration on the open interval between `a` and `b`, the derivative of the energy of
`F s` is differentiable at `s = 0`, with derivative the index form `I(V, V)` of the variation
field `V`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_acceleration_eq_zero {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : ∀ t ∈ uIoo a b, acceleration (leviCivitaConnection I M) (F 0) t = 0) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  have hA {t : ℝ} (h : (fun q ↦ F q t) =ᶠ[𝓝 0] fun _ ↦ F 0 t) :
      acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0 = 0 := by
    rw [h.acceleration_eq, acceleration_const]
  simpa only [hA hF.eventually_apply_left, hA hF.eventually_apply_right, inner_zero_left,
    add_zero, sub_zero] using
    TauCeti.Manifold.hasDerivAt_deriv_energy_of_acceleration_eq_zero hF.contMDiffAt hγ

omit [T2Space M] in
/-- A transverse curve `s ↦ F s t` which is stationary near `s = 0` has zero covariant
acceleration at `s = 0`. -/
theorem acceleration_fst_eq_zero {t : ℝ} (ht : ∀ᶠ s in 𝓝 (0 : ℝ), F s t = F 0 t) :
    acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0 = 0 :=
  (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) ht).trans
    (acceleration_const _ _ 0)

omit [T2Space M] in
/-- The transverse acceleration at the stationary left endpoint of a fixed-endpoint variation
vanishes at `s = 0`. -/
theorem IsFixedEndpointVariation.acceleration_left_eq_zero {n : WithTop ℕ∞} {a b : ℝ}
    (hF : IsFixedEndpointVariation I n F a b) :
    acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0 = 0 :=
  acceleration_fst_eq_zero hF.eventually_apply_left

omit [T2Space M] in
/-- The transverse acceleration at the stationary right endpoint of a fixed-endpoint variation
vanishes at `s = 0`. -/
theorem IsFixedEndpointVariation.acceleration_right_eq_zero {n : WithTop ℕ∞} {a b : ℝ}
    (hF : IsFixedEndpointVariation I n F a b) :
    acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0 = 0 :=
  acceleration_fst_eq_zero hF.eventually_apply_right

omit [T2Space M] in
/-- If the transverse curves of `F` at `a` and `b` agree near `s = 0` and the central curve `F 0`
has matching endpoint velocity lifts at `a` and `b`, then the endpoint transverse-acceleration
pairings `⟪A(a), γ'(a)⟫` and `⟪A(b), γ'(b)⟫` agree. -/
theorem inner_acceleration_fst_curveVelocity_eq_of_curveVelocityLift_eq {a b : ℝ}
    (hper : ∀ᶠ s in 𝓝 (0 : ℝ), F s a = F s b)
    (hvel : curveVelocityLift I (F 0) a = curveVelocityLift I (F 0) b) :
    inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
        (curveVelocity I (F 0) a) =
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
        (curveVelocity I (F 0) b) :=
  TauCeti.inner_eq_of_totalSpaceMk_eq
    (Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper)
    (by simpa only [curveVelocityLift_apply] using hvel)

/-- **The second variation of energy of a geodesic.** If `F` is `C³` along `{0} × [a, b]` and its
central curve `γ = F 0` is a geodesic on the open segment `uIoo a b`, then

`d²/ds² E(F s) |₀ = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`,

where `A(t) = D_s ∂_s F (0, t)` is the transverse acceleration at `s = 0`. -/
theorem hasDerivAt_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
          (curveVelocity I (F 0) a)) 0 := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  simpa only [hγ.integral_inner_acceleration_eq_zero Subset.rfl, sub_zero] using
    hasDerivAt_deriv_energy hF

/-! ### Fixed-endpoint, periodic, and exponential variations -/

/-- **Second variation of energy for a variation with fixed endpoints.** When `F` is a `C³`
variation with fixed endpoints between `a` and `b`, the endpoint transverse accelerations vanish,
leaving `I(V, V) - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) 0 := by
  refine (TauCeti.Manifold.hasDerivAt_deriv_energy hF.contMDiffAt).congr_deriv ?_
  rw [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero, inner_zero_left, inner_zero_left]
  ring

/-- **Second variation of energy of a geodesic for fixed endpoints.** For a `C³` fixed-endpoint
variation `F` of a curve `γ = F 0` which is a geodesic on `uIoo a b`, the second derivative of
`s ↦ E(F s)` at `s = 0` is the index form `I(V, V)`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  simpa only [hγ.integral_inner_acceleration_eq_zero Subset.rfl, sub_zero] using
    hF.hasDerivAt_deriv_energy

/-- **Second variation of energy of a smoothly closed geodesic.** If `F` is `C³` along
`{0} × [a, b]`, its nearby curves are closed (`F s a = F s b` for `s` near `0`), and its central
curve `γ = F 0` is a geodesic on `uIoo a b` with matching endpoint velocity lifts
`curveVelocityLift I γ a = curveVelocityLift I γ b`, then the boundary transverse-acceleration
pairings cancel and `d²/ds² E(F s) |₀ = I(V, V)`. -/
theorem hasDerivAt_deriv_energy_of_isGeodesicCurveOn_of_curveVelocityLift_eq {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : curveVelocityLift I (F 0) a = curveVelocityLift I (F 0) b) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  refine (hasDerivAt_deriv_energy_of_isGeodesicCurveOn hF hγ).congr_deriv ?_
  rw [inner_acceleration_fst_curveVelocity_eq_of_curveVelocityLift_eq hper hvel]; ring

section ExponentialVariation

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **Second variation of energy along an exponential variation.** Let `V` be a tangent field along
an arbitrary curve `γ` whose lift to the tangent bundle is `C³` on `uIcc a b`. Because each
transverse curve `s ↦ exp_(γ t) (s • V t)` is geodesic near `s = 0`, its covariant acceleration at
`s = 0` vanishes, so all transverse-acceleration terms in `hasDerivAt_deriv_energy` drop out and
`d²/ds² E(exp_(γ ·) (s • V ·)) |₀ = I(V, V)`, even without assuming that `γ` is a geodesic or that
`V` vanishes at the endpoints. -/
theorem hasDerivAt_deriv_energy_exponentialVariation {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b)) :
    HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (indexForm I γ V V a b) 0 := by
  obtain ⟨γ', V', hV', hEq, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hV
  have hd' : HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ' V' s) a b)
      (indexForm I γ' V' V' a b) 0 := by
    have h := hasDerivAt_deriv_energy
      fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t ht)
    simp only [acceleration_exponentialVariation_zero, inner_zero_left,
      intervalIntegral.integral_zero, add_zero, sub_zero] at h
    rwa [variationField_exponentialVariation_eq, exponentialVariation_zero] at h
  rw [energy_exponentialVariation_eq_of_eqOn hExp]
  refine hd'.congr_deriv (indexForm_congr_of_totalSpaceMk_eq
    (fun t ht ↦ hEq t (uIoo_subset_uIcc_self ht))
    (fun t ht ↦ hEq t (uIoo_subset_uIcc_self ht)))

end ExponentialVariation

/-! ### Index-form nonnegativity at local minima and energy-decreasing variations -/

/-- **Nonnegativity of the index form at a local minimum of the energy.** If `F` is `C³` along
`{0} × uIcc a b`, its central curve `γ = F 0` is a geodesic on `uIoo a b`, its endpoint
transverse-acceleration pairings satisfy `⟪A(b), γ'(b)⟫ ≤ ⟪A(a), γ'(a)⟫`, and `s ↦ E(F s)` has a
local minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hbdry : inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
        (curveVelocity I (F 0) b) ≤
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
        (curveVelocity I (F 0) a))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b := by
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_energy (fun t ht ↦ (hF t ht).of_le (by norm_num))).continuousAt hmin
  rw [(hasDerivAt_deriv_energy_of_isGeodesicCurveOn hF hγ).deriv] at hnn; linarith

/-- **Nonnegativity of the index form at a local minimum of the energy for fixed endpoints.** If `F`
is a `C³` fixed-endpoint variation of a geodesic `γ = F 0` on `uIoo a b` and `s ↦ E(F s)` has a
local minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem IsFixedEndpointVariation.indexForm_nonneg_of_isLocalMin_energy {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b :=
  TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy hF.contMDiffAt hγ
    (by simp [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero]) hmin

/-- **Nonnegativity of the index form at a local minimum of the energy for closed geodesics.** If
`F` is `C³` along `{0} × uIcc a b` with `F s a = F s b` near `0`, `γ = F 0` is a geodesic on
`uIoo a b` with matching endpoint velocity lifts, and `s ↦ E(F s)` has a local minimum at `s = 0`,
then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy_of_curveVelocityLift_eq {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : curveVelocityLift I (F 0) a = curveVelocityLift I (F 0) b)
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b :=
  indexForm_nonneg_of_isLocalMin_energy hF hγ
    (inner_acceleration_fst_curveVelocity_eq_of_curveVelocityLift_eq hper hvel).symm.le hmin

section ExponentialExtremum

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **Nonnegativity of the index form from local energy minimality along an exponential
variation.** If `V` has a `C³` lift on `uIcc a b` and `s ↦ E(exp_(γ ·) (s • V ·))` has a local
minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy_exponentialVariation {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b))
    (hmin : IsLocalMin (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0) :
    0 ≤ indexForm I γ V V a b := by
  simpa only [(hasDerivAt_deriv_energy_exponentialVariation hV).deriv] using
    TauCeti.deriv_deriv_nonneg_of_isLocalMin
      (hasDerivAt_energy_exponentialVariation (hV.of_le (by norm_num))).continuousAt hmin

/-- **Negative index form strictly decreases energy.** Let `γ` be a geodesic on `uIoo a b` and `V`
a field along `γ` with a `C³` lift on `uIcc a b` whose endpoint pairings satisfy
`⟪V(b), γ'_{uIcc a b}(b)⟫ = ⟪V(a), γ'_{uIcc a b}(a)⟫` (for instance because `V` vanishes at `a`
and `b`, is orthogonal to `γ'_{uIcc a b}` at both endpoints, or `V` has matching endpoint values
along a smoothly closed geodesic with matching endpoint velocities). If `I(V, V) < 0`, then for
every small nonzero `s` the curve `exp_(γ ·) (s • V ·)` has strictly smaller energy than `γ`. -/
theorem eventually_energy_exponentialVariation_lt_of_indexForm_neg {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b))
    (hbdry : inner ℝ (V b) (curveVelocityWithin I γ (uIcc a b) b) =
      inner ℝ (V a) (curveVelocityWithin I γ (uIcc a b) a))
    (hneg : indexForm I γ V V a b < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ), energy I (exponentialVariation I γ V s) a b < energy I γ a b := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hd₁ := hasDerivAt_energy_exponentialVariation (hV.of_le (by norm_num))
  have hd₁_zero : deriv (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 = 0 := by
    rw [hd₁.deriv, hγ.integral_inner_acceleration_eq_zero Subset.rfl, hbdry, sub_self, sub_zero]
  have hneg' : deriv (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 < 0 := by
    rwa [(hasDerivAt_deriv_energy_exponentialVariation hV).deriv]
  simpa only [exponentialVariation_zero] using TauCeti.eventually_gt_of_deriv_deriv_neg
    hneg' hd₁_zero hd₁.continuousAt

end ExponentialExtremum

end TauCeti.Manifold

end
