/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.Variation
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface

/-!
# The second variation of energy

Let `F : ℝ → ℝ → M` be a `C³` variation of the curve `γ = F 0` between the parameters `a` and `b`
in a smooth Riemannian manifold, with variation field `V = TauCeti.Manifold.variationField I F`
and transverse acceleration `A(t) = D_s ∂_s F (0, t)`, the covariant acceleration at `s = 0` of
the transverse curve `s ↦ F s t` for the Levi-Civita connection.

At each parameter `t`, differentiating `s ↦ ‖∂_t F (s, t)‖²` twice at `s = 0`, using torsion-free
symmetry `D_s ∂_t F = D_t ∂_s F` and the curvature identity `D_s D_t ∂_s F - D_t D_s ∂_s F =
R(∂_s F, ∂_t F) ∂_s F`, gives

`d²/ds² ‖∂_t F (s, t)‖² |₀ = 2 (‖D_t V(t)‖² - ⟪R(V(t), γ'(t)) γ'(t), V(t)⟫ + ⟪D_t A(t), γ'(t)⟫)`.

Differentiating the energy `E(F s) = ½ ∫_a^b ‖∂_t F (s, t)‖² dt` twice under the integral sign
and integrating `⟪D_t A, γ'⟫ = d/dt ⟪A, γ'⟫ - ⟪A, D_t γ'⟫` by parts yields **the second variation
formula for the energy**:

`d²/ds² E(F s) |₀ = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`,

where `I(V, V) = TauCeti.Manifold.indexForm I γ V V a b` is the index form of `γ` on `[a, b]`.

When `γ` is a geodesic on the open segment `uIoo a b`, the bulk acceleration integral vanishes.
When the endpoints are fixed (`TauCeti.Manifold.IsFixedEndpointVariation`), or when `γ` is a
closed geodesic and the variation is periodic, or when `F` is the exponential variation
`exp_(γ t) (s • V t)` (whose transverse curves are geodesics even with moving endpoints), the
boundary acceleration pairings also vanish and the second derivative of the energy at `s = 0` is
`I(V, V)`. In particular, at any local minimum of the energy along a geodesic, the index form is
nonnegative on the variation field.

## Main results

* `TauCeti.Manifold.contMDiffAt_acceleration_fst`: for a `C³` family `F`, the transverse
  acceleration `t ↦ D_s ∂_s F (u, t)` is a `C¹` tangent field along `F u`.
* `TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`: the pointwise second transverse
  derivative of the squared speed.
* `TauCeti.Manifold.hasDerivAt_deriv_energy` and `TauCeti.Manifold.deriv_deriv_energy`: **the
  second variation of energy** with free endpoints and arbitrary central curve.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn` and
  `TauCeti.Manifold.deriv_deriv_energy_of_isGeodesicCurveOn`: specialization to a central curve
  which is a geodesic on `uIoo a b`.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy`,
  `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`, and
  `TauCeti.Manifold.IsFixedEndpointVariation.indexForm_nonneg_of_isLocalMin_energy`: fixed-endpoint
  specialization and nonnegativity of the index form at a local minimum of the energy.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_periodic` and
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_of_periodic`: periodic variations of a
  closed geodesic, where the periodic endpoint acceleration terms cancel.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_exponentialVariation`: the second variation of the
  energy of `exp_(γ t) (s • V t)` is `I(V, V)`, even with free endpoints and non-geodesic `γ`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2 and Ch. 10, §1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §13, Theorem 13.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 10.4 and Theorem 10.6.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-! ### Transverse acceleration and pointwise second derivative of the squared speed -/

/-- **Regularity of the transverse acceleration.** For a two-parameter family `F` which is `C³` at
`(u, t)`, the transverse acceleration `r ↦ D_s ∂_s F (u, r)` at `s = u` has a `C¹` lift to the
tangent bundle along `F u` at `t`. -/
theorem contMDiffAt_acceleration_fst {u t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F u r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)) t := by
  set cov := leviCivitaConnection I M
  set e := trivializationAt E (TangentSpace I) (F u t)
  have hbase : F u t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hWo : IsOpen {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z} :=
    TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  obtain ⟨U, V, hUo, hVo, huU, htV, hUV⟩ := isOpen_prod_iff.mp hWo u t hf
  have hFu : ContMDiffAt 𝓘(ℝ, ℝ) I 1 (F u) t :=
    (hf.of_le (by norm_num)).comp t (contDiff_prodMk_right u).contMDiff.contMDiffAt
  set φ : ℝ × ℝ → E := fun z ↦ extChartAt I (F u t) (F z.1 z.2)
  have hφ : ContDiffAt ℝ 3 φ (u, t) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (mem_chart_source H (F u t))).comp (u, t) hf)
  have hφ₁ : ContDiffAt ℝ (1 + 1) (fun z : ℝ × ℝ ↦ deriv (fun s ↦ φ (s, z.2)) z.1) (u, t) := by
    obtain ⟨w, hw, hφw⟩ := hφ.contDiffOn (m := 1) (by norm_num) (by simp)
    refine ((hφ.fderiv_right (m := 2) le_rfl).clm_apply
      (contDiffAt_const (c := ((1 : ℝ), (0 : ℝ))))).congr_of_eventuallyEq ?_
    filter_upwards [(hφw.differentiableOn one_ne_zero).eventually_differentiableAt hw] with z hz
    simpa only [timeFDeriv_apply] using (hasDerivAt_parameterCurve (F := φ) hz).deriv
  have hφ₂ : ContDiffAt ℝ 1 (fun r ↦ deriv (fun s ↦ deriv (fun q ↦ φ (q, r)) s) u) t :=
    TauCeti.contDiffAt_deriv_slice_left hφ₁
  have hφu : ContDiffAt ℝ 1 (fun r ↦ deriv (fun s ↦ φ (s, r)) u) t :=
    (TauCeti.contDiffAt_deriv_slice_left (n := 2) hφ).of_le one_le_two
  have hΓ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) 1
      (christoffelMap (Module.finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet)))
      (F u t) :=
    (contMDiffOn_christoffelMap_leviCivitaConnection (I := I) (M := M) (n := 1) (m := ∞) (k := ∞)
      (e := e) (Module.finBasis ℝ E) (by simp) (by simp)).contMDiffAt
      (e.open_baseSet.mem_nhds hbase)
  have hcoord : ContDiffAt ℝ 1
      (fun r ↦ deriv (fun s ↦ deriv (fun q ↦ φ (q, r)) s) u +
        christoffelMap (Module.finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet))
          (F u r) (deriv (fun s ↦ φ (s, r)) u) (deriv (fun s ↦ φ (s, r)) u)) t :=
    hφ₂.add (((hΓ.comp t hFu).contDiffAt.clm_apply hφu).clm_apply hφu)
  rw [← contMDiffWithinAt_univ, ← contDiffWithinAt_sectionCoord_iff (F u) _ hFu.contMDiffWithinAt
    hbase, contDiffWithinAt_univ]
  refine hcoord.congr_of_eventuallyEq ?_
  filter_upwards [hVo.mem_nhds htV,
    hFu.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)] with r hrV hrbase
  have hγr : ContMDiffOn 𝓘(ℝ, ℝ) I 2 (fun s ↦ F s r) U := fun s hs ↦
    ((hUV ⟨hs, hrV⟩).of_le (by norm_num)).comp s
      (contDiff_prodMk_left r).contMDiff.contMDiffAt |>.contMDiffWithinAt
  have hd1 : derivWithin (extChartAt I (F u t) ∘ fun s ↦ F s r) U =ᶠ[𝓝 u]
      fun s ↦ deriv (fun q ↦ φ (q, r)) s := by
    filter_upwards [hUo.mem_nhds huU] with s hs
    exact derivWithin_of_mem_nhds (hUo.mem_nhds hs)
  rw [sectionCoord_apply, ← accelerationWithin_of_mem_nhds cov _ (hUo.mem_nhds huU),
    accelerationWithin_eq_symmL cov (fun s ↦ F s r) hUo.uniqueDiffOn hγr huU hrbase,
    e.continuousLinearMapAt_symmL (R := ℝ) hrbase,
    derivWithin_of_mem_nhds (hUo.mem_nhds huU), hd1.deriv_eq, hd1.self_of_nhds]

/-- **The product rule for the transverse acceleration against the curve velocity.** At a parameter
`t` where the family is `C³`, the pairing `r ↦ ⟪A(r), γ'(r)⟫` differentiates to
`⟪D_t A(t), γ'(t)⟫ + ⟪A(t), D_t γ'(t)⟫`. -/
theorem hasDerivAt_inner_acceleration_fst_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt
      (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0)
        (curveVelocity I (F 0) r))
      (inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t)
          (curveVelocity I (F 0) t) +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) t := by
  have hA := contMDiffAt_acceleration_fst hf
  have hAcoord : DifferentiableAt ℝ (sectionCoord (F := E) (F 0)
      (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) (F 0 t)) t := by
    rw [← differentiableWithinAt_univ]
    exact differentiableWithinAt_sectionCoord (F 0) _
      (hA.mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t))
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F 0) t :=
    (hf.of_le (by norm_num)).comp t (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F 0)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  rw [acceleration_def (leviCivitaConnection I M) (F 0) t]
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M)).hasDerivAt_inner_alongCurve
    (hγt.mdifferentiableAt two_ne_zero) hAcoord hγcoord

variable [T2Space M]

/-- **The second transverse derivative of the squared speed.** At a parameter `t` where `F` is
`C³`, the second derivative at `s = 0` of `s ↦ ‖∂_t F (s, t)‖²` is twice the index-form integrand
of the variation field `V` plus `2 ⟪D_t A(t), γ'(t)⟫`, where `A(r) = D_s ∂_s F (0, r)` is the
transverse acceleration and `γ = F 0`. -/
theorem hasDerivAt_deriv_norm_sq_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      (2 * (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t)
          (curveVelocity I (F 0) t))) 0 := by
  set cov := leviCivitaConnection I M
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have htor : cov.IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hnear : ∀ᶠ q in 𝓝 (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t) :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf)
  have hfirst : (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) =ᶠ[𝓝 0]
      fun q ↦ 2 * inner ℝ
        (alongCurve cov (fun p ↦ F p t) (fun p ↦ curveVelocity I (F p) t) q)
        (curveVelocity I (F q) t) := by
    filter_upwards [hnear] with q hq
    have hq2 := hq.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)
    have hP := hq2.differentiableAt_sectionCoord_curveVelocity_snd (f := F)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F q t))
    have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun p ↦ F p t) q :=
      (hq2.comp q (contDiff_prodMk_left t).contMDiff.contMDiffAt).mdifferentiableAt two_ne_zero
    have hprod := (hm.hasDerivAt_inner_alongCurve hc hP hP).congr_of_eventuallyEq
      (Eventually.of_forall fun p ↦ (real_inner_self_eq_norm_sq (curveVelocity I (F p) t)).symm)
    rw [hprod.deriv, real_inner_comm (curveVelocity I (F q) t), two_mul]
  have hswap : (fun q ↦ alongCurve cov (fun p ↦ F p t) (fun p ↦ curveVelocity I (F p) t) q)
      =ᶠ[𝓝 (0 : ℝ)]
      fun q ↦ alongCurve cov (F q) (fun r ↦ curveVelocity I (fun p ↦ F p r) q) t :=
    hnear.mono fun q hq ↦ (alongCurve_curveVelocity_comm cov htor (f := F) (u := q) (v := t)
      (hq.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))).symm
  have hDTcoord := differentiableAt_sectionCoord_alongCurve_leviCivitaConnection
    (hf.contMDiffAt_curveVelocity_snd_slice (by norm_num))
  have hTcoord := (hf.of_le (by norm_num)).differentiableAt_sectionCoord_curveVelocity_snd (f := F)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t))
  have hc0 : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) 0 :=
    ((hf.of_le (by norm_num)).comp 0
      (contDiff_prodMk_left t).contMDiff.contMDiffAt).mdifferentiableAt two_ne_zero
  have hd2 := ((hm.hasDerivAt_inner_alongCurve hc0 hDTcoord hTcoord).const_mul 2
    ).congr_of_eventuallyEq hfirst
  have hcomm := alongCurve_alongCurve_sub_alongCurve_alongCurve cov (f := F)
    (W := fun q r ↦ curveVelocity I (fun p ↦ F p r) q) (u := 0) (v := t)
    (hf.contMDiffAt_curveVelocity_fst (by norm_num))
  have hskew := hm.inner_curvatureTensor_eq_neg (F 0 t) (variationField I F t)
    (curveVelocity I (F 0) t) (variationField I F t) (curveVelocity I (F 0) t)
  have hswap0 : cov.alongCurve (fun p ↦ F p t) (fun p ↦ curveVelocity I (F p) t) 0 =
      cov.alongCurve (F 0) (fun r ↦ curveVelocity I (fun p ↦ F p r) 0) t := hswap.self_of_nhds
  refine hd2.congr_deriv ?_
  dsimp only [cov] at hswap hswap0 hcomm ⊢
  rw [alongCurve_congr _ (fun p ↦ F p t) _ hswap, hswap0, sub_eq_iff_eq_add.mp hcomm]
  simp only [← variationField_apply, ← acceleration_def]
  rw [inner_add_left, indexFormIntegrand_def, real_inner_comm (variationField I F t)] at *
  linarith

/-- Evaluating `hasDerivAt_deriv_norm_sq_curveVelocity` as an iterated `deriv`. -/
theorem deriv_deriv_norm_sq_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    deriv (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) 0 =
      2 * (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
        inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t)
          (curveVelocity I (F 0) t)) :=
  (hasDerivAt_deriv_norm_sq_curveVelocity hf).deriv

/-! ### Differentiating the energy integral twice -/

/-- Twice differentiating `s ↦ energy I (F s) a b` under the integral sign gives half the integral
of the pointwise second transverse derivative of the squared speed. -/
theorem hasDerivAt_deriv_energy_eq_integral {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (∫ t in a..b,
        (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t)
            (curveVelocity I (F 0) t))) 0 := by
  set W := {z : ℝ × ℝ | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) z}
  have hWo : IsOpen W := TauCeti.isOpen_setOfPred_contMDiffAt (by simp)
  have hG : ContDiffOn ℝ 2 (fun z : ℝ × ℝ ↦ ‖curveVelocity I (F z.1) z.2‖ ^ 2) W :=
    ContMDiffOn.contDiffOn_norm_sq_curveVelocity (fun _ hz ↦ hz.contMDiffWithinAt) (by norm_num) hWo
  obtain ⟨_, hd⟩ := TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn hWo hG
    (by rintro ⟨_, t⟩ ⟨rfl, ht⟩; exact hF t ht)
  have henergy : (deriv fun s ↦ energy I (F s) a b) =
      fun s ↦ deriv (fun q ↦ ∫ t in a..b, ‖curveVelocity I (F q) t‖ ^ 2) s / 2 := by
    ext s; simp only [energy_def, deriv_div_const]
  rw [henergy]
  refine (hd.div_const 2).congr_deriv ?_
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [deriv_deriv_norm_sq_curveVelocity (hF t ht)]
  ring

/-- **The second variation of energy.** Let `F` be a two-parameter family which is `C³` at every
point of `{0} × [a, b]`, with central curve `γ = F 0`, variation field `V`, and transverse
acceleration `A(t) = D_s ∂_s F (0, t)`. Then `s ↦ d/ds E(F s)` is differentiable at `s = 0`, with
derivative

`I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`. -/
theorem hasDerivAt_deriv_energy {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
          (curveVelocity I (F 0) a) -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) 0 := by
  set cov := leviCivitaConnection I M
  set P : ℝ → ℝ := fun r ↦ inner ℝ (acceleration cov (fun s ↦ F s r) 0) (curveVelocity I (F 0) r)
  set Q : ℝ → ℝ := fun r ↦ inner ℝ (acceleration cov (fun s ↦ F s r) 0) (acceleration cov (F 0) r)
  have hVl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) := fun t ht ↦
    ((hF t ht).contMDiffAt_variationField (m := 1) (by norm_num)).contMDiffWithinAt
  have hAl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (acceleration cov (fun s ↦ F s r) 0)) (uIcc a b) :=
    fun t ht ↦ (contMDiffAt_acceleration_fst (hF t ht)).contMDiffWithinAt
  have hTl : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (F 0 r) (curveVelocity I (F 0) r)) t := fun t ht ↦
    ((hF t ht).contMDiffAt_curveVelocity_snd (m := 2) (by norm_num)).comp t
      (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt
  have hAccl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F 0 r) (acceleration cov (F 0) r)) (uIcc a b) := fun t ht ↦ by
    simpa only [acceleration_def] using
      (contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) ((hTl t ht).of_le one_le_two)).contMDiffWithinAt
  have hDAl : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F 0 r)
        (alongCurve cov (F 0) (fun r ↦ acceleration cov (fun s ↦ F s r) 0) r)) (uIcc a b) :=
    fun t ht ↦ (contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
      (by simp) (by simp) (contMDiffAt_acceleration_fst (hF t ht))).contMDiffWithinAt
  have hIint := intervalIntegrable_indexFormIntegrand hVl hVl
  have hQint : IntervalIntegrable Q volume a b :=
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := F 0)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      (hAl.of_le zero_le_one) hAccl).continuousOn.intervalIntegrable
  have hDAint : IntervalIntegrable
      (fun t ↦ inner ℝ (alongCurve cov (F 0) (fun r ↦ acceleration cov (fun s ↦ F s r) 0) t)
        (curveVelocity I (F 0) t)) volume a b :=
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := F 0)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le) hDAl
      (fun t ht ↦ ((hTl t ht).of_le (by simp)).contMDiffWithinAt)).continuousOn.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_inner_acceleration_fst_curveVelocity (hF t ht)) (hDAint.add hQint)
  rw [intervalIntegral.integral_add hDAint hQint] at hFTC
  refine (hasDerivAt_deriv_energy_eq_integral hF).congr_deriv ?_
  rw [intervalIntegral.integral_add hIint hDAint, ← indexForm_def, eq_sub_of_add_eq hFTC]
  ring

/-- **The second variation of energy**, written as an iterated `deriv`. -/
theorem deriv_deriv_energy {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    deriv (deriv fun s ↦ energy I (F s) a b) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
          (curveVelocity I (F 0) a) -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t) :=
  (hasDerivAt_deriv_energy hF).deriv

/-! ### Geodesics, fixed endpoints, periodic variations, and exponential variations -/

/-- **The second variation of energy along a geodesic.** When the central curve `γ = F 0` is a
geodesic on `uIoo a b`, its bulk acceleration vanishes and the second variation of energy is
`I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫`. -/
theorem hasDerivAt_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
          (curveVelocity I (F 0) a)) 0 := by
  refine (hasDerivAt_deriv_energy hF).congr_deriv ?_
  have hint0 : ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
      (acceleration (leviCivitaConnection I M) (F 0) t) = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    have hnhds : uIoo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    rw [← accelerationWithin_of_mem_nhds _ _ hnhds,
      hgeo.accelerationWithin_eq_zero t ht, inner_zero_right]
  rw [hint0, sub_zero]

/-- **The second variation of energy along a geodesic**, written as an iterated `deriv`. -/
theorem deriv_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    deriv (deriv fun s ↦ energy I (F s) a b) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) a b +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
          (curveVelocity I (F 0) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
          (curveVelocity I (F 0) a) :=
  (hasDerivAt_deriv_energy_of_isGeodesicCurveOn hF hgeo).deriv

namespace IsFixedEndpointVariation

omit [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The transverse acceleration of a fixed-endpoint variation vanishes at the left endpoint. -/
theorem acceleration_left_eq_zero {n : WithTop ℕ∞} {a b : ℝ}
    (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (hF : IsFixedEndpointVariation I n F a b) :
    acceleration cov (fun s ↦ F s a) 0 = 0 :=
  (Filter.EventuallyEq.acceleration_eq cov hF.eventually_apply_left).trans
    (acceleration_const cov (F 0 a) 0)

omit [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The transverse acceleration of a fixed-endpoint variation vanishes at the right endpoint. -/
theorem acceleration_right_eq_zero {n : WithTop ℕ∞} {a b : ℝ}
    (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (hF : IsFixedEndpointVariation I n F a b) :
    acceleration cov (fun s ↦ F s b) 0 = 0 :=
  (Filter.EventuallyEq.acceleration_eq cov hF.eventually_apply_right).trans
    (acceleration_const cov (F 0 b) 0)

/-- **The second variation of energy for a variation with fixed endpoints.** -/
theorem hasDerivAt_deriv_energy {a b : ℝ} (hF : IsFixedEndpointVariation I 3 F a b) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
          (acceleration (leviCivitaConnection I M) (F 0) t)) 0 := by
  refine (TauCeti.Manifold.hasDerivAt_deriv_energy hF.contMDiffAt).congr_deriv ?_
  rw [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero, inner_zero_left, inner_zero_left]
  ring

/-- **The second variation of energy for a fixed-endpoint variation of a geodesic** is the index
form `I(V, V)` of its variation field. -/
theorem hasDerivAt_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  refine (TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn
    hF.contMDiffAt hgeo).congr_deriv ?_
  rw [hF.acceleration_left_eq_zero, hF.acceleration_right_eq_zero, inner_zero_left, inner_zero_left]
  ring

/-- **The second variation of energy for a fixed-endpoint variation of a geodesic**, written as an
iterated `deriv`. -/
theorem deriv_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    deriv (deriv fun s ↦ energy I (F s) a b) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) a b :=
  (hF.hasDerivAt_deriv_energy_of_isGeodesicCurveOn hgeo).deriv

/-- **Necessary second-order condition at a local minimum of energy.** If a geodesic `F 0` on
`uIoo a b` locally minimizes energy along a `C³` fixed-endpoint variation `F`, then the index form
of its variation field is nonnegative. -/
theorem indexForm_nonneg_of_isLocalMin_energy {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b := by
  rw [← hF.deriv_deriv_energy_of_isGeodesicCurveOn hgeo]
  exact TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (TauCeti.Manifold.hasDerivAt_energy (hF.of_le (by norm_num)).contMDiffAt).continuousAt hmin

end IsFixedEndpointVariation

/-- **The second variation of energy for a periodic variation of a closed geodesic.** Suppose `F`
is `C³` along `{0} × [a, b]`, its central curve `F 0` is a geodesic on `uIoo a b` with matching
tangent vectors `(F 0 a, γ'(a)) = (F 0 b, γ'(b))` in the tangent bundle, and `F s a = F s b` for
`s` near `0`. Then the endpoint acceleration pairings cancel and the second derivative of the
energy at `s = 0` is `I(V, V)`. -/
theorem hasDerivAt_deriv_energy_of_periodic {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  have hacc := Filter.EventuallyEq.totalSpaceMk_acceleration_eq
    (leviCivitaConnection I M) hper
  have hinner :
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0)
        (curveVelocity I (F 0) a) =
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0)
        (curveVelocity I (F 0) b) :=
    TauCeti.inner_tangentSpace_congr (mem_of_mem_nhds hper)
      (congrArg TotalSpace.snd hacc) (congrArg TotalSpace.snd hvel)
  refine (hasDerivAt_deriv_energy_of_isGeodesicCurveOn hF hgeo).congr_deriv ?_
  rw [hinner, add_sub_cancel_right]

/-- **The second variation of energy for a periodic variation of a closed geodesic**, written as
an iterated `deriv`. -/
theorem deriv_deriv_energy_of_periodic {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b)) :
    deriv (deriv fun s ↦ energy I (F s) a b) 0 =
      indexForm I (F 0) (variationField I F) (variationField I F) a b :=
  (hasDerivAt_deriv_energy_of_periodic hF hgeo hper hvel).deriv

/-- **Nonnegativity of the index form at a periodic local minimum of energy.** -/
theorem indexForm_nonneg_of_isLocalMin_energy_of_periodic {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hgeo : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : TotalSpace.mk' E (F 0 a) (curveVelocity I (F 0) a) =
      TotalSpace.mk' E (F 0 b) (curveVelocity I (F 0) b))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b := by
  rw [← deriv_deriv_energy_of_periodic hF hgeo hper hvel]
  exact TauCeti.deriv_deriv_nonneg_of_isLocalMin
    (hasDerivAt_energy fun t ht ↦ (hF t ht).of_le (by norm_num)).continuousAt hmin

/-- **The second variation of energy of an exponential variation.** Along `exp_(γ t) (s • V t)`,
every transverse curve is a geodesic, so all transverse accelerations vanish and the second
derivative of the energy at `s = 0` is `I(V, V)`, even with moving endpoints and without assuming
that `γ` is a geodesic. -/
theorem hasDerivAt_deriv_energy_exponentialVariation [I.Boundaryless]
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (indexForm I γ V V a b) 0 := by
  have hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  have hacc (t : ℝ) :
      acceleration (leviCivitaConnection I M) (fun s ↦ exponentialVariation I γ V s t) 0 = 0 := by
    have hmem : geodesicInterval I M (γ t) (V t) ∈ 𝓝 (0 : ℝ) :=
      isOpen_geodesicInterval.mem_nhds (zero_mem_geodesicInterval (E := E))
    rw [← accelerationWithin_of_mem_nhds _ _ hmem]
    exact (isGeodesicCurveOnFrom_exponentialVariation γ V t
      ).isGeodesicCurveOn.accelerationWithin_eq_zero 0 (zero_mem_geodesicInterval (E := E))
  have hd := hasDerivAt_deriv_energy hF
  simp only [hacc, inner_zero_left, intervalIntegral.integral_zero, sub_zero, add_zero] at hd
  refine hd.congr_deriv ?_
  have hVeq : ∀ t ∈ uIoo a b, HEq (variationField I (exponentialVariation I γ V) t) (V t) :=
    fun t _ ↦ heq_of_eq (variationField_exponentialVariation γ V t)
  exact indexForm_congr (fun t _ ↦ by simp) hVeq hVeq

/-- **The second variation of energy of an exponential variation**, written as an iterated
`deriv`. -/
theorem deriv_deriv_energy_exponentialVariation [I.Boundaryless]
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    deriv (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 =
      indexForm I γ V V a b :=
  (hasDerivAt_deriv_energy_exponentialVariation hV).deriv

end TauCeti.Manifold

end
