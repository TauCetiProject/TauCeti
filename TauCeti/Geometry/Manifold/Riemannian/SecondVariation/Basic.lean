/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Variation
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VariationField
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface

/-!
# The second variation of energy

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a Riemannian manifold, with central
curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)` and transverse acceleration
`A(t) = D_s ∂_s F (0, t)`, the covariant acceleration at `s = 0` of the transverse curve
`s ↦ F s t`. This file computes the second derivative at `s = 0` of the energy
`E(s) = ½ ∫_a^b ‖∂_t F (s, t)‖² dt` of the curves `F s`:

`E''(0) = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`,

where `I` is the index form `TauCeti.Manifold.indexForm` of `γ` on `[a, b]`,
`I(V, V) = ∫_a^b ‖D_t V‖² - ⟪R(V, γ') γ', V⟫ dt`.

The proof differentiates the squared speed twice in `s`. Half of its second derivative is
`‖D_s ∂_t F‖² + ⟪D_s D_s ∂_t F, ∂_t F⟫`. The symmetry lemma turns `D_s ∂_t F` into `D_t V`
and `D_s D_s ∂_t F` into `D_s D_t ∂_s F`, and exchanging the two covariant derivatives costs the
curvature term: `D_s D_t ∂_s F = D_t A + R(V, γ') V`. The antisymmetry
`⟪R(V, γ') V, γ'⟫ = -⟪R(V, γ') γ', V⟫` produces the curvature term of the index form, and
`⟪D_t A, γ'⟫ = d/dt ⟪A, γ'⟫ - ⟪A, D_t γ'⟫` integrates to the endpoint terms.

For a variation with fixed endpoints the transverse curves through the endpoints are constant, so
the endpoint accelerations vanish; if moreover `γ` is a geodesic on `[a, b]`, the last integral
vanishes as well and the second variation is the index form `I(V, V)`.

The formulas hold for a family which is `C³` at the points of `{0} × [a, b]`, on a smooth manifold
with a smooth Riemannian metric.

## Main results

* `TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`: the pointwise second variation of
  the squared speed, whose integral over `[a, b]` is the second variation of energy.
* `TauCeti.Manifold.hasDerivAt_deriv_energy`: **the second variation formula** for the energy,
  with endpoint acceleration terms.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy`: the second variation
  formula for a `C³` variation with fixed endpoints.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`: for a
  fixed-endpoint variation of a geodesic, the second variation of energy is the index form of the
  variation field.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, the second variation
  formula.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §13, the second
  variation formula.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 10, the second
  variation of length, proved by the same computation.
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

/-- At a point where the family is `C³`, the transverse acceleration `A(r) = D_s ∂_s F (0, r)` is a
`C¹` field along the central curve. -/
private theorem contMDiffAt_acceleration_slice {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (F 0 r)
      (acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0)) t := by
  have hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2 (fun z : ℝ × ℝ ↦
      TotalSpace.mk' E (F z.2 z.1) (curveVelocity I (fun p ↦ F p z.1) z.2)) (t, 0) :=
    (hf.contMDiffAt_curveVelocity_fst (by norm_num)).comp (t, 0) (contMDiff_iff_contDiff.mpr
      (by fun_prop : ContDiff ℝ 2 fun z : ℝ × ℝ ↦ (z.2, z.1))).contMDiffAt
  simpa only [acceleration_def] using contMDiffAt_alongCurve_slice (leviCivitaConnection I M)
    (f := fun a b ↦ F b a) (W := fun a b ↦ curveVelocity I (fun p ↦ F p a) b) hW

/-- **The pointwise second variation of the squared speed.** At a parameter `t` where the family
is `C³`, the second derivative at `s = 0` of `s ↦ ‖∂_t F (s, t)‖²` is twice

`‖D_t V(t)‖² - ⟪R(V, γ') γ', V⟫(t) + d/dt ⟪A, γ'⟫(t) - ⟪A(t), D_t γ'(t)⟫`,

the integrand of the index form plus a derivative and an acceleration term, where `γ = F 0`, `V`
is the variation field and `A(r) = D_s ∂_s F (0, r)` is the transverse acceleration. Integrated
over `[a, b]`, this is the second variation of energy. -/
theorem hasDerivAt_deriv_norm_sq_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      (2 * (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        deriv (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0)
          (curveVelocity I (F 0) r)) t -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t))) 0 := by
  set cov := leviCivitaConnection I M
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  -- The transverse velocity field `W q r = ∂_s F (q, r)` and the transverse acceleration `A`.
  set W : ∀ q r, TangentSpace I (F q r) := fun q r ↦ curveVelocity I (fun p ↦ F p r) q
  set A : ∀ r, TangentSpace I (F 0 r) := fun r ↦ acceleration cov (fun q ↦ F q r) 0
  have hAfun : (fun r ↦ alongCurve cov (fun q ↦ F q r) (fun q ↦ W q r) 0) = A :=
    funext fun r ↦ by simp only [A, W, acceleration_def]
  have hV0 : W 0 = variationField I F := funext fun r ↦ by simp only [W, variationField_apply]
  have hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (F z.1 z.2) (W z.1 z.2)) (0, t) :=
    hf.contMDiffAt_curveVelocity_fst (by norm_num)
  -- Near `s = 0`, `∂_s ‖∂_t F (s, t)‖² = 2 ⟪D_t W (s, t), ∂_t F (s, t)⟫`.
  have hderiv : (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) =ᶠ[𝓝 0]
      fun q ↦ 2 * inner ℝ (alongCurve cov (F q) (W q) t) (curveVelocity I (F q) t) := by
    have hnear : ∀ᶠ q in 𝓝 (0 : ℝ),
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t) :=
      ((continuous_id.prodMk continuous_const).tendsto (0 : ℝ)).eventually
        ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf)
    filter_upwards [hnear] with q hq
    exact (hasDerivAt_norm_sq_curveVelocity_curveVelocity_fst (hq.of_le (by norm_num))).deriv
  -- Differentiate `⟪D_t W, ∂_t F⟫` along the transverse curve through `F 0 t`.
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) 0 :=
    (hf.comp 0 (contMDiff_iff_contDiff.mpr
      (contDiff_prodMk_left (n := 3) t)).contMDiffAt).mdifferentiableAt (by norm_num)
  have hXcoord : DifferentiableAt ℝ (sectionCoord (F := E) (fun q ↦ F q t)
      (fun q ↦ alongCurve cov (F q) (W q) t) (F 0 t)) 0 :=
    differentiableAt_sectionCoord (fun q ↦ F q t) _
      ((contMDiffAt_alongCurve_slice cov hW).mdifferentiableAt one_ne_zero) hbase
  have hYcoord := (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
    |>.differentiableAt_sectionCoord_curveVelocity_snd (f := F) hbase
  have hprod := hm.hasDerivAt_inner_alongCurve hcurve hXcoord hYcoord
  -- The mixed derivatives: `D_s D_t W = D_t A + R(V, γ') V` and `D_s ∂_t F = D_t V`.
  have hcomm := alongCurve_alongCurve_sub_alongCurve_alongCurve cov hW
  have hsymm := alongCurve_curveVelocity_comm cov
    ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
    (hf.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))
  -- The product rule for `⟪A, γ'⟫` along `γ`.
  have hAcoord : DifferentiableAt ℝ (sectionCoord (F := E) (F 0) A (F 0 t)) t :=
    differentiableAt_sectionCoord (F 0) A
      ((contMDiffAt_acceleration_slice hf).mdifferentiableAt one_ne_zero) hbase
  have hγcoord : DifferentiableAt ℝ
      (sectionCoord (F := E) (F 0) (curveVelocity I (F 0)) (F 0 t)) t :=
    differentiableAt_sectionCoord (F 0) _
      (((hf.contMDiffAt_curveVelocity_snd (m := 2) (by norm_num)).comp t
        (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) (0 : ℝ))).contMDiffAt)
        |>.mdifferentiableAt two_ne_zero) hbase
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I (F 0) t :=
    (hf.comp t (contMDiff_iff_contDiff.mpr
      (contDiff_prodMk_right (n := 3) (0 : ℝ))).contMDiffAt).mdifferentiableAt (by norm_num)
  have hkd := (hm.hasDerivAt_inner_alongCurve hγt hAcoord hγcoord).deriv
  -- The antisymmetry of the curvature in its last two slots.
  have hcurv : inner ℝ (cov.curvatureTensor (F 0 t) (variationField I F t)
      (curveVelocity I (F 0) t) (variationField I F t)) (curveVelocity I (F 0) t) =
      -inner ℝ (cov.curvatureTensor (F 0 t) (variationField I F t)
        (curveVelocity I (F 0) t) (curveVelocity I (F 0) t)) (variationField I F t) := by
    rw [hm.inner_curvatureTensor_eq_neg, real_inner_comm]
  rw [sub_eq_iff_eq_add', hAfun, ← variationField_apply, hV0] at hcomm
  rw [← acceleration_def] at hkd
  rw [hV0] at hprod
  rw [← variationField_def] at hsymm
  refine ((hprod.const_mul 2).congr_of_eventuallyEq hderiv).congr_deriv ?_
  rw [hcomm, ← hsymm, inner_add_left, hcurv, hkd, indexFormIntegrand_def]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Differentiation under the integral sign, twice: for a family which is `C³` at every point of
`{0} × [a, b]`, the derivative of the energy of `F s` is differentiable at `s = 0`, with derivative
half the integral of the second transverse derivatives of the squared speed, which is interval
integrable. -/
private theorem hasDerivAt_deriv_energy_eq_integral {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    IntervalIntegrable (fun t ↦ deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0)
        volume a b ∧
      HasDerivAt (deriv fun s ↦ energy I (F s) a b)
        ((∫ t in a..b, deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0) / 2) 0 := by
  obtain ⟨U, O, hUo, hOo, h0U, hO, hFUO⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUOo : IsOpen (U ×ˢ O) := hUo.prod hOo
  -- The squared speed `G (s, t) = ‖∂_t F (s, t)‖²` is jointly `C²` on `U ×ˢ O`, and so its
  -- partial derivative `D₁` in `s` is jointly `C¹` there.
  set G : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  have hG : ContDiffOn ℝ 2 G (U ×ˢ O) := hFUO.contDiffOn_inner_mfderiv (by norm_num) hUOo _ _
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ O → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 :=
    fun hs ht ↦ by
      rw [← real_inner_self_eq_norm_sq, curveVelocity_eq_mfderiv_snd
        ((hFUO.contMDiffAt (hUOo.mem_nhds ⟨hs, ht⟩)).mdifferentiableAt (by norm_num))]
  set D₁ : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ G z (1, 0)
  have hD₁ : ContDiffOn ℝ 1 D₁ (U ×ˢ O) :=
    (hG.fderiv_of_isOpen hUOo (by norm_num)).clm_apply contDiffOn_const
  -- On `U ×ˢ O` the first transverse derivative of the squared speed is `D₁`, and the second
  -- one at `s = 0` is the partial derivative of `D₁` in `s`.
  have hD₁eq : ∀ {s t : ℝ}, s ∈ U → t ∈ O →
      deriv (fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) s = D₁ (s, t) := fun {s t} hs ht ↦ by
    have h := hasDerivAt_parameterCurve ((hG.differentiableOn (by norm_num) _
      ⟨hs, ht⟩).differentiableAt (hUOo.mem_nhds ⟨hs, ht⟩))
    rw [timeFDeriv_apply] at h
    refine (h.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hUo.mem_nhds hs] with p hp using (hGeq hp ht).symm
  have hD₂eq : ∀ t ∈ O, deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0 =
      fderiv ℝ D₁ (0, t) (1, 0) := fun t ht ↦ by
    have h := hasDerivAt_parameterCurve ((hD₁.differentiableOn one_ne_zero _
      ⟨h0U, ht⟩).differentiableAt (hUOo.mem_nhds ⟨h0U, ht⟩))
    rw [timeFDeriv_apply] at h
    refine (h.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hUo.mem_nhds h0U] with s hs using hD₁eq hs ht
  -- Near `s = 0` the derivative of the energy is `½ ∫ D₁ (s, t) dt`.
  have hderiv : deriv (fun s ↦ energy I (F s) a b) =ᶠ[𝓝 0]
      fun s ↦ (∫ t in a..b, D₁ (s, t)) / 2 := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    have henergy : (fun s ↦ energy I (F s) a b) =ᶠ[𝓝 s]
        fun s ↦ (∫ t in a..b, G (s, t)) / 2 := by
      filter_upwards [hUo.mem_nhds hs] with s' hs'
      rw [energy_def]
      congr 1
      exact intervalIntegral.integral_congr fun t ht ↦ (hGeq hs' (hO ht)).symm
    exact (((TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUOo (hG.of_le one_le_two)
      (prod_mono (singleton_subset_iff.mpr hs) hO)).2.div_const 2).congr_of_eventuallyEq
        henergy).deriv
  obtain ⟨hint, hD₂⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUOo hD₁
    (prod_mono (singleton_subset_iff.mpr h0U) hO)
  have hcongr : EqOn (fun t ↦ fderiv ℝ D₁ (0, t) (1, 0))
      (fun t ↦ deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0) (uIcc a b) :=
    fun t ht ↦ (hD₂eq t (hO ht)).symm
  refine ⟨hint.congr (hcongr.mono uIoc_subset_uIcc), ?_⟩
  rw [← intervalIntegral.integral_congr hcongr]
  exact (hD₂.div_const 2).congr_of_eventuallyEq hderiv

/-- **The second variation of energy.** Let `F` be a two-parameter family which is `C³` at every
point of `{0} × [a, b]`, with central curve `γ = F 0`, variation field `V` and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`. Then the derivative of the energy of `F s` between `a`
and `b` is differentiable at `s = 0`, with derivative

`I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`,

where `I` is the index form of `γ` on `[a, b]` and `D_t γ'` is the covariant acceleration of `γ`
for the Levi-Civita connection. -/
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
  obtain ⟨hD₂int, hmain⟩ := hasDerivAt_deriv_energy_eq_integral hF
  -- Half of the second transverse derivative of the squared speed is the index-form integrand
  -- plus the derivative of `k = ⟪A, γ'⟫` minus `⟪A, D_t γ'⟫`.
  have hpt : ∀ t ∈ uIcc a b, deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0 / 2 =
      indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        deriv (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0)
          (curveVelocity I (F 0) r)) t -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t) := fun t ht ↦ by
    rw [(hasDerivAt_deriv_norm_sq_curveVelocity (hF t ht)).deriv]
    ring
  set A : ∀ r, TangentSpace I (F 0 r) := fun r ↦
    acceleration (leviCivitaConnection I M) (fun q ↦ F q r) 0
  set k : ℝ → ℝ := fun r ↦ inner ℝ (A r) (curveVelocity I (F 0) r)
  -- `k` is `C¹` on an open set containing `[a, b]`, by the regularity of `A` and of `γ'`.
  obtain ⟨U, O, hUo, hOo, h0U, hO, hFUO⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hsurf : ∀ {t : ℝ}, t ∈ O →
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) :=
    fun ht ↦ hFUO.contMDiffAt ((hUo.prod hOo).mem_nhds ⟨h0U, ht⟩)
  have hk : ContDiffOn ℝ 1 k O := contMDiffOn_iff_contDiffOn.mp
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := F 0)
      (fun t ht ↦ (contMDiffAt_acceleration_slice (hsurf ht)).contMDiffWithinAt)
      (fun t ht ↦ (((hsurf ht).contMDiffAt_curveVelocity_snd (m := 1) (by norm_num)).comp t
        (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 1) (0 : ℝ))).contMDiffAt)
        |>.contMDiffWithinAt))
  -- Integrate the pointwise identity over `[a, b]`.
  have hIint : IntervalIntegrable
      (indexFormIntegrand I (F 0) (variationField I F) (variationField I F)) volume a b := by
    have hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
        (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) :=
      fun t ht ↦ ((hF t ht).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
    exact intervalIntegrable_indexFormIntegrand hV hV
  have hk'int : IntervalIntegrable (deriv k) volume a b :=
    ((hk.continuousOn_deriv_of_isOpen hOo le_rfl).mono hO).intervalIntegrable
  have hJint : IntervalIntegrable
      (fun t ↦ inner ℝ (A t) (acceleration (leviCivitaConnection I M) (F 0) t)) volume a b :=
    ((hIint.add hk'int).sub (hD₂int.div_const 2)).congr_uIoo fun t ht ↦ by
      simp only [hpt t (uIoo_subset_uIcc_self ht)]
      ring
  have hFTC : ∫ t in a..b, deriv k t = k b - k a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ ((hk.differentiableOn one_ne_zero t (hO ht)).differentiableAt
        (hOo.mem_nhds (hO ht))).hasDerivAt) hk'int
  refine hmain.congr_deriv ?_
  rw [← intervalIntegral.integral_div, intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub (hIint.add hk'int) hJint,
    intervalIntegral.integral_add hIint hk'int, hFTC, indexForm_def]
  ring

/-- **The second variation of energy for a variation with fixed endpoints.** For a `C³` variation
`F` of `γ = F 0` with fixed endpoints between `a` and `b`, with variation field `V` and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`, the derivative of the energy of `F s` is differentiable at
`s = 0`, with derivative `I(V, V) - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun q ↦ F q t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) 0 := by
  have hA {c : ℝ} (hc : ∀ᶠ s in 𝓝 0, F s c = F 0 c) :
      acceleration (leviCivitaConnection I M) (fun q ↦ F q c) 0 = 0 := by
    rw [Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M)
      (η := fun _ ↦ F 0 c) hc, acceleration_const]
  refine (TauCeti.Manifold.hasDerivAt_deriv_energy hF.contMDiffAt).congr_deriv ?_
  rw [hA hF.eventually_apply_left, hA hF.eventually_apply_right, inner_zero_left,
    inner_zero_left]
  ring

/-- **The second variation of energy at a geodesic is the index form.** For a `C³` variation `F`
with fixed endpoints between `a` and `b` of a geodesic `γ = F 0` on `[a, b]`, the derivative of
the energy of `F s` is differentiable at `s = 0`, with derivative the index form `I(V, V)` of the
variation field `V`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) (hγ : IsGeodesicCurveOn I (F 0) (uIcc a b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  refine hF.hasDerivAt_deriv_energy.congr_deriv ?_
  rw [intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_,
    intervalIntegral.integral_zero, sub_zero]
  have hmem : uIcc a b ∈ 𝓝 t := mem_of_superset (isOpen_Ioo.mem_nhds ht) uIoo_subset_uIcc_self
  dsimp only
  rw [← accelerationWithin_of_mem_nhds (leviCivitaConnection I M) (γ := F 0) hmem,
    hγ.accelerationWithin_eq_zero t (uIoo_subset_uIcc_self ht), inner_zero_right]

end TauCeti.Manifold
