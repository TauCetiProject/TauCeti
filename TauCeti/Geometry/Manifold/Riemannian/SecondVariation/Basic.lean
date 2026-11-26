/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Variation
public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

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

end TauCeti.Manifold

end
