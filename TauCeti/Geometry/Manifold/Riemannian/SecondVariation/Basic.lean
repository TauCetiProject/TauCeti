/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.Variation
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# The second variation of energy

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a smooth Riemannian manifold, with
central curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)`, and transverse acceleration
`A(t) = D_s ∂_s F (0, t)` at `s = 0`. When `F` is `C³` along `{0} × [a, b]`, differentiating the
squared speed `s ↦ ‖∂_t F (s, t)‖²` twice in `s` at `s = 0` exchanges two covariant derivatives
along `F` via `CovariantDerivative.alongCurve_alongCurve_sub_alongCurve_alongCurve`, producing the
integrand of `TauCeti.Manifold.indexForm` together with `⟪D_t A(t), γ'(t)⟫`. Integrating over
`[a, b]` and integrating `⟪D_t A, γ'⟫` by parts via
`TauCeti.Manifold.integral_inner_alongCurve_acceleration_fst_curveVelocity` gives the second
variation of energy:

`d²/ds² E(F s) |₀ = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`.

Along a geodesic `γ`, the bulk acceleration integral vanishes and only the index form and the two
endpoint transverse-acceleration pairings remain. Those boundary terms vanish in three geometric
situations: for fixed-endpoint variations (`TauCeti.Manifold.IsFixedEndpointVariation`), for
periodic variations of a smoothly closed geodesic, and for exponential variations
`(s, t) ↦ exp_(γ t) (s • V t)` of a `C³` field `V` on `uIcc a b` whose transverse curves are
geodesics even when the endpoints move. Applying the second-derivative tests then shows that
`I(V, V) ≥ 0` at a local minimum of the energy (for any `C³` variation whose endpoint
transverse-acceleration pairings satisfy `⟪A(b), γ'(b)⟫ ≤ ⟪A(a), γ'(a)⟫`, as well as its
fixed-endpoint, periodic, and exponential-variation specializations) and that a closed-interval
`C³` field with `I(V, V) < 0` and cancelling endpoint first-variation pairings strictly decreases
the energy of nearby exponential-variation curves.

## Main results

* `TauCeti.Manifold.continuousAt_inner_acceleration_fst_acceleration`,
  `TauCeti.Manifold.hasDerivAt_inner_acceleration_fst_curveVelocity`,
  `TauCeti.Manifold.continuousAt_inner_alongCurve_acceleration_fst_curveVelocity`, and
  `TauCeti.Manifold.integral_inner_alongCurve_acceleration_fst_curveVelocity`: low-regularity
  continuity, product rule, and integration by parts for the transverse acceleration against the
  longitudinal velocity and acceleration along `F u`.
* `TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`: pointwise second transverse derivative
  of the squared speed `‖∂_t F (s, t)‖²` at `s = 0`.
* `TauCeti.Manifold.hasDerivAt_deriv_energy`: **the second variation of energy** for a `C³` family
  with free endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_acceleration_eq_zero` and
  `TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`: specialization to a central
  curve which is a geodesic on `uIoo a b`.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy`,
  `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_acceleration_eq_zero`, and
  `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`:
  fixed-endpoint specializations.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn_of_curveVelocityLift_eq`:
  periodic specialization for smoothly closed geodesics.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_exponentialVariation`: the second variation of energy
  along `TauCeti.Manifold.exponentialVariation` of a `C³` section on `uIcc a b` equals `I(V, V)`
  even with free endpoints.
* `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy`,
  `TauCeti.Manifold.IsFixedEndpointVariation.indexForm_nonneg_of_isLocalMin_energy`,
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_of_curveVelocityLift_eq`, and
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_exponentialVariation`: nonnegativity of
  the index form at a local minimum of the energy.
* `TauCeti.Manifold.eventually_energy_exponentialVariation_lt_of_indexForm_neg`: strict energy
  decrease along the exponential variation of a geodesic when `I(V, V) < 0` and the endpoint
  first-variation pairings cancel.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 9, §2 and Chapter 10, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10
  (where the length counterpart of the second variation formula is developed).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §13 (the second variation of the energy).
-/

public section

open Bundle CovariantDerivative Filter Function MeasureTheory Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

section AccelerationContinuity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-! ### Product rule, continuity, and integration by parts for transverse acceleration -/

/-- At a parameter `(u, t)` where `F` is `C²`, the pairing
`r ↦ ⟪D_s ∂_s F (u, r), D_r ∂_r F (u, r)⟫` of the transverse and longitudinal accelerations along
`F u` is continuous at `t`. -/
theorem continuousAt_inner_acceleration_fst_acceleration {u t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t)) :
    ContinuousAt
      (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)
        (acceleration (leviCivitaConnection I M) (F u) r)) t := by
  have hA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F u r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)) t :=
    hf.contMDiffAt_acceleration_leviCivitaConnection_fst_slice (n := 0) (m := 2) (k := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hvel : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F u r) (curveVelocity I (F u) r)) t :=
    hf.contMDiffAt_curveVelocity_snd (m := 1) (by norm_num)
      |>.comp t (contDiff_prodMk_right u).contMDiff.contMDiffAt
  have hacc : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F u r) (acceleration (leviCivitaConnection I M) (F u) r)) t := by
    simpa only [acceleration_def] using
      contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := 2) (k := 1)
        (by norm_num) (by norm_num) (by simpa using hvel)
  exact (ContMDiffAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := F u) (h := IsContMDiffRiemannianBundle.of_le (n := 1) zero_le) hA hacc).continuousAt

end AccelerationContinuity

section AccelerationDeriv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-- **Product rule for the transverse acceleration against the velocity.** At a parameter `(u, t)`
where the family `F` is `C³`, the pairing `r ↦ ⟪D_s ∂_s F (u, r), ∂_r F (u, r)⟫` along `F u`
differentiates to `⟪D_t (D_s ∂_s F) (u, t), ∂_t F (u, t)⟫ + ⟪D_s ∂_s F (u, t), D_t ∂_t F (u, t)⟫`.
Integrated over `[a, b]`, this turns the `⟪D_t A, γ'⟫` term of the second variation into boundary
terms minus `∫ ⟪A, D_t γ'⟫`. -/
theorem hasDerivAt_inner_acceleration_fst_curveVelocity {u t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t)) :
    HasDerivAt
      (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)
        (curveVelocity I (F u) r))
      (inner ℝ (alongCurve (leviCivitaConnection I M) (F u)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u) t)
          (curveVelocity I (F u) t) +
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) u)
          (acceleration (leviCivitaConnection I M) (F u) t)) t := by
  have : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_num)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  have hA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F u r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)) t :=
    hf.contMDiffAt_acceleration_leviCivitaConnection_fst_slice (n := 1) (m := 3) (k := 2)
      (by norm_num) (by norm_num) (by norm_num)
  have hAcoord : DifferentiableAt ℝ
      (sectionCoord ℝ (F := E) (F u)
        (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u) (F u t)) t :=
    differentiableAt_sectionCoord (F u) _ (hA.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F u t))
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F u) t :=
    (hf.of_le (by norm_num)).comp t (contDiff_prodMk_right u).contMDiff.contMDiffAt
  obtain ⟨v, hv, hγv⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F u)
    (hγv.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hv)
  rw [acceleration_def (γ := F u)]
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve (hγt.mdifferentiableAt two_ne_zero) hAcoord hγcoord

/-- At a parameter `(u, t)` where `F` is `C³`, the pairing
`r ↦ ⟪D_r (D_s ∂_s F) (u, r), ∂_r F (u, r)⟫` along `F u` is continuous at `t`. -/
theorem continuousAt_inner_alongCurve_acceleration_fst_curveVelocity {u t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t)) :
    ContinuousAt
      (fun r ↦ inner ℝ (alongCurve (leviCivitaConnection I M) (F u)
        (fun q ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s q) u) r)
        (curveVelocity I (F u) r)) t := by
  have : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_num)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  have hA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F u r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)) t :=
    hf.contMDiffAt_acceleration_leviCivitaConnection_fst_slice (n := 1) (m := 3) (k := 2)
      (by norm_num) (by norm_num) (by norm_num)
  have hDA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F u r) (alongCurve (leviCivitaConnection I M) (F u)
        (fun q ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s q) u) r)) t :=
    contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := 3) (k := 2)
      (by norm_num) (by norm_num) (by simpa using hA)
  have hvel : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F u r) (curveVelocity I (F u) r)) t :=
    hf.contMDiffAt_curveVelocity_snd (m := 0) (by norm_num)
      |>.comp t (contDiff_prodMk_right u).contMDiff.contMDiffAt
  exact (ContMDiffAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := F u) (h := IsContMDiffRiemannianBundle.of_le (n := 2) zero_le) hDA hvel).continuousAt

/-- **Integration by parts for the transverse acceleration term.** For a family `F` which is `C³`
along `{u} × uIcc a b`, integrating `hasDerivAt_inner_acceleration_fst_curveVelocity` gives
`∫_a^b ⟪D_t A(t), γ'(t)⟫ dt = ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`,
where `γ = F u` and `A(t) = D_s ∂_s F (u, t)`. -/
theorem integral_inner_alongCurve_acceleration_fst_curveVelocity {u a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t)) :
    ∫ t in a..b,
        inner ℝ (alongCurve (leviCivitaConnection I M) (F u)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u) t)
          (curveVelocity I (F u) t) =
      inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s b) u)
          (curveVelocity I (F u) b) -
        inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s a) u)
          (curveVelocity I (F u) a) -
        ∫ t in a..b, inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) u)
          (acceleration (leviCivitaConnection I M) (F u) t) := by
  have : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_num)
  have : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  have hintDA : IntervalIntegrable (fun t ↦ inner ℝ
      (alongCurve (leviCivitaConnection I M) (F u)
        (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u) t)
      (curveVelocity I (F u) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_alongCurve_acceleration_fst_curveVelocity (hF t ht)).continuousWithinAt
  have hintAA : IntervalIntegrable (fun t ↦ inner ℝ
      (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) u)
      (acceleration (leviCivitaConnection I M) (F u) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_acceleration_fst_acceleration
        ((hF t ht).of_le (by norm_num))).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_inner_acceleration_fst_curveVelocity (hF t ht)) (hintDA.add hintAA)
  rw [intervalIntegral.integral_add hintDA hintAA] at hFTC
  exact eq_sub_of_add_eq hFTC

end AccelerationDeriv

section SecondVariation

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : ℝ → ℝ → M}

/-! ### Pointwise second transverse derivative of the squared speed -/

/-- Commuting the second transverse covariant derivative of the longitudinal velocity at `(0, t)`
produces `D_t (D_s ∂_s F) (0, t) + R(V, γ') V`. -/
private theorem alongCurve_alongCurve_curveVelocity_snd_zero {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    alongCurve (leviCivitaConnection I M) (fun s ↦ F s t)
        (fun s ↦ alongCurve (leviCivitaConnection I M) (fun q ↦ F q t)
          (fun q ↦ curveVelocity I (F q) t) s) 0 =
      alongCurve (leviCivitaConnection I M) (F 0)
          (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t +
        (leviCivitaConnection I M).curvatureTensor (F 0 t) (variationField I F t)
          (curveVelocity I (F 0) t) (variationField I F t) := by
  set cov := leviCivitaConnection I M
  have htor : cov.IsTorsionFree :=
    (isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hnear : ∀ᶠ s in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) :=
    ((continuous_id.prodMk continuous_const).tendsto 0).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf)
  have hswap : ∀ᶠ s in 𝓝 0,
      alongCurve cov (fun q ↦ F q t) (fun q ↦ curveVelocity I (F q) t) s =
        alongCurve cov (F s) (fun r ↦ curveVelocity I (fun q ↦ F q r) s) t := by
    filter_upwards [hnear] with s hs
    exact (alongCurve_curveVelocity_comm cov htor (f := F) (u := s) (v := t)
      (hs.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))).symm
  have hcomm := alongCurve_alongCurve_sub_alongCurve_alongCurve cov
    (W := fun q r ↦ curveVelocity I (fun p ↦ F p r) q) (u := 0) (v := t)
    (hf.contMDiffAt_curveVelocity_fst (by norm_num))
  rw [alongCurve_congr cov (fun s ↦ F s t) _ hswap, sub_eq_iff_eq_add.mp hcomm]
  dsimp only [cov]
  simp only [acceleration_def, variationField_def, add_comm]

/-- **Pointwise second variation of the squared speed.** At a parameter `t` where `F` is `C³` at
`(0, t)`, the transverse derivative `s ↦ d/ds ‖∂_t F (s, t)‖²` is differentiable at `s = 0`, with
derivative `2 (I_t(V, V) + ⟪D_t (D_s ∂_s F) (0, t), γ'(t)⟫)`, where `V` is the variation field of
`F`, `γ = F 0`, and `I_t(V, V)` is `TauCeti.Manifold.indexFormIntegrand`. -/
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
  -- Differentiate `s ↦ ‖∂_t F (s, t)‖²` twice along the transverse curve `s ↦ F s t`.
  let σ : ℝ → M := fun s ↦ F s t
  let P : ∀ s, TangentSpace I (σ s) := fun s ↦ curveVelocity I (F s) t
  have hP : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun s ↦ TotalSpace.mk' E (σ s) (P s)) 0 :=
    hf.contMDiffAt_curveVelocity_snd_slice (by norm_num)
  have hPnear : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 (fun q ↦ TotalSpace.mk' E (σ q) (P q)) s :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hP.of_le one_le_two)
  have hσ : ∀ᶠ s in 𝓝 (0 : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I σ s :=
    hPnear.mono fun s hs ↦
      ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp s hs).mdifferentiableAt one_ne_zero
  have hPcoord : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (sectionCoord ℝ (F := E) σ P (σ s)) s :=
    hPnear.mono fun s hs ↦ differentiableAt_sectionCoord σ P (hs.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (σ s))
  have hDPcoord : DifferentiableAt ℝ (sectionCoord ℝ (F := E) σ (alongCurve cov σ P) (σ 0)) 0 :=
    differentiableAt_sectionCoord_alongCurve_leviCivitaConnection hP
  have hd₂ := hm.hasDerivAt_deriv_norm_sq_alongCurve hσ hPcoord hDPcoord
  -- Use curvature skew-symmetry and torsion-free symmetry `D_s γ' = D_t V` to match `I_t(V, V)`.
  have hcurv : inner ℝ (cov.curvatureTensor (F 0 t) (variationField I F t)
        (curveVelocity I (F 0) t) (variationField I F t)) (curveVelocity I (F 0) t) =
      -inner ℝ (cov.curvatureTensor (F 0 t) (variationField I F t)
        (curveVelocity I (F 0) t) (curveVelocity I (F 0) t)) (variationField I F t) := by
    have hskew := hm.inner_curvatureTensor_eq_neg (F 0 t) (variationField I F t)
      (curveVelocity I (F 0) t) (variationField I F t) (curveVelocity I (F 0) t)
    rwa [real_inner_comm _ (variationField I F t)] at hskew
  have hswap0 : alongCurve cov σ P 0 = alongCurve cov (F 0) (variationField I F) t := by
    simpa only [variationField_def] using
      (alongCurve_curveVelocity_comm cov htor (f := F) (u := 0) (v := t)
        (hf.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num))).symm
  refine hd₂.congr_deriv ?_
  dsimp only [σ, P, cov]
  rw [alongCurve_alongCurve_curveVelocity_snd_zero hf, hswap0, inner_add_left, hcurv,
    indexFormIntegrand_def, ← real_inner_self_eq_norm_sq]
  ring

/-! ### The second variation of energy -/

/-- Differentiating `s ↦ E(F s)` twice under the integral sign gives the integral of
`I_t(V, V) + ⟪D_t A(t), γ'(t)⟫`. -/
private theorem hasDerivAt_deriv_energy_eq_integral {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (∫ t in a..b,
        (indexFormIntegrand I (F 0) (variationField I F) (variationField I F) t +
          inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
            (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t)
            (curveVelocity I (F 0) t))) 0 := by
  -- Build a `C²` squared-speed representative `G` on an open product neighbourhood `U ×ˢ V`.
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  let G : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  have hG : ContDiffOn ℝ 2 G (U ×ˢ V) :=
    hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 := by
    intro s t hs ht
    dsimp only [G]
    rw [← curveVelocity_eq_mfderiv_snd
      ((hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)).mdifferentiableAt (by norm_num)),
      real_inner_self_eq_norm_sq]
  -- Differentiate `s ↦ (∫ t in a..b, G (s, t)) / 2` twice under the integral sign.
  have hdG := (TauCeti.hasDerivAt_deriv_intervalIntegral_of_contDiffOn hUVo hG
    (prod_mono (singleton_subset_iff.mpr h0U) hV)).2
  have henergy : (fun s ↦ energy I (F s) a b) =ᶠ[𝓝 0] fun s ↦ (∫ t in a..b, G (s, t)) / 2 := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    rw [energy_def]
    exact congrArg (· / 2) (intervalIntegral.integral_congr fun t ht ↦ (hGeq hs (hV ht)).symm)
  have hdE : (deriv fun s ↦ energy I (F s) a b) =ᶠ[𝓝 0]
      fun s ↦ deriv (fun q ↦ ∫ t in a..b, G (q, t)) s / 2 := by
    filter_upwards [henergy.deriv] with s hs
    rw [hs, deriv_div_const]
  refine ((hdG.div_const 2).congr_of_eventuallyEq hdE).congr_deriv ?_
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have hsq : (fun s ↦ G (s, t)) =ᶠ[𝓝 0] fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2 := by
    filter_upwards [hUo.mem_nhds h0U] with s hs using hGeq hs (hV ht)
  rw [hsq.deriv.deriv.self_of_nhds, (hasDerivAt_deriv_norm_sq_curveVelocity (hF t ht)).deriv]
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
  have : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hVF : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (variationField I F r)) (uIcc a b) :=
    fun r hr ↦ ((hF r hr).contMDiffAt_variationField (by norm_num)).contMDiffWithinAt
  have hintI : IntervalIntegrable
      (indexFormIntegrand I (F 0) (variationField I F) (variationField I F)) volume a b :=
    intervalIntegrable_indexFormIntegrand hVF hVF
  have hintDA : IntervalIntegrable (fun t ↦ inner ℝ
      (alongCurve (leviCivitaConnection I M) (F 0)
        (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) t)
      (curveVelocity I (F 0) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_alongCurve_acceleration_fst_curveVelocity (hF t ht)).continuousWithinAt
  refine (hasDerivAt_deriv_energy_eq_integral hF).congr_deriv ?_
  rw [intervalIntegral.integral_add hintI hintDA, ← indexForm_def,
    integral_inner_alongCurve_acceleration_fst_curveVelocity hF]
  ring

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
  refine (hasDerivAt_deriv_energy hF).congr_deriv ?_
  rw [hγ.integral_inner_acceleration_eq_zero Subset.rfl, sub_zero]

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
  have ha : acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_left).trans
      (acceleration_const (leviCivitaConnection I M) (F 0 a) 0)
  have hb : acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_right).trans
      (acceleration_const (leviCivitaConnection I M) (F 0 b) 0)
  refine (TauCeti.Manifold.hasDerivAt_deriv_energy hF.contMDiffAt).congr_deriv ?_
  rw [ha, hb, inner_zero_left, inner_zero_left]
  ring

/-- **The second variation of energy at a geodesic with fixed endpoints is the index form.** For
a `C³` variation `F` with fixed endpoints between `a` and `b` of a curve `γ = F 0` which is a
geodesic on `uIoo a b`, the derivative of the energy of `F s` is differentiable at `s = 0`, with
derivative the index form `I(V, V)` of the variation field `V`. -/
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
  refine hF.hasDerivAt_deriv_energy.congr_deriv ?_
  rw [hγ.integral_inner_acceleration_eq_zero Subset.rfl, sub_zero]

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
  have hA := Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper
  rw [curveVelocityLift_apply, curveVelocityLift_apply] at hvel
  rw [TauCeti.inner_eq_of_totalSpaceMk_eq hA hvel]
  ring

section ExponentialVariation

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **Second variation of energy along an exponential variation.** Let `V` be a tangent field along
an arbitrary curve `γ` whose lift to the tangent bundle is `C³` on `uIcc a b`. Because each
transverse curve `s ↦ exp_(γ t) (s • V t)` is a geodesic, all transverse-acceleration terms in
`hasDerivAt_deriv_energy` vanish and `d²/ds² E(exp_(γ ·) (s • V ·)) |₀ = I(V, V)`, even without
assuming that `γ` is a geodesic or that `V` vanishes at the endpoints. -/
theorem hasDerivAt_deriv_energy_exponentialVariation {a b : ℝ}
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 3
      (fun t ↦ TotalSpace.mk' E (γ t) (V t)) (uIcc a b)) :
    HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (indexForm I γ V V a b) 0 := by
  obtain ⟨γ', V', hV', hEq, hExp⟩ := exists_contMDiffAt_exponentialVariation_eqOn γ V hV
  have hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ' V' z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ' V' (hV' t ht)
  have hd' : HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ' V' s) a b)
      (indexForm I γ' V' V' a b) 0 := by
    have h0 : exponentialVariation I γ' V' 0 = γ' := exponentialVariation_zero γ' V'
    have hVF : ∀ t, HEq (variationField I (exponentialVariation I γ' V') t) (V' t) :=
      fun t ↦ heq_of_eq (variationField_exponentialVariation γ' V' t)
    have hA := acceleration_exponentialVariation_zero γ' V'
    generalize exponentialVariation I γ' V' = G at hF h0 hVF hA ⊢
    subst h0
    simpa only [funext fun t ↦ eq_of_heq (hVF t), hA, inner_zero_left,
      intervalIntegral.integral_zero, add_zero, sub_zero] using hasDerivAt_deriv_energy hF
  have henergy : (fun s ↦ energy I (exponentialVariation I γ V s) a b) =
      fun s ↦ energy I (exponentialVariation I γ' V' s) a b :=
    funext fun s ↦ (energy_congr ((hExp s).mono uIoo_subset_uIcc_self)).symm
  rw [henergy]
  refine hd'.congr_deriv (indexForm_congr
    (fun t ht ↦ congrArg TotalSpace.proj (hEq t (uIoo_subset_uIcc_self ht)))
    (fun t ht ↦ (Bundle.TotalSpace.ext_iff.mp (hEq t (uIoo_subset_uIcc_self ht))).2)
    (fun t ht ↦ (Bundle.TotalSpace.ext_iff.mp (hEq t (uIoo_subset_uIcc_self ht))).2))

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
  have hcont : ContinuousAt (fun s ↦ energy I (F s) a b) 0 :=
    (hasDerivAt_energy (fun t ht ↦ (hF t ht).of_le (by norm_num))).continuousAt
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rw [(hasDerivAt_deriv_energy_of_isGeodesicCurveOn hF hγ).deriv] at hnn
  linarith

/-- **Nonnegativity of the index form at a local minimum of the energy for fixed endpoints.** If `F`
is a `C³` fixed-endpoint variation of a geodesic `γ = F 0` on `uIoo a b` and `s ↦ E(F s)` has a
local minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem IsFixedEndpointVariation.indexForm_nonneg_of_isLocalMin_energy {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b := by
  have ha : acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_left).trans
      (acceleration_const (leviCivitaConnection I M) (F 0 a) 0)
  have hb : acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_right).trans
      (acceleration_const (leviCivitaConnection I M) (F 0 b) 0)
  exact TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy hF.contMDiffAt hγ
    (by rw [ha, hb, inner_zero_left, inner_zero_left]) hmin

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
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b := by
  have hA := Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M) hper
  rw [curveVelocityLift_apply, curveVelocityLift_apply] at hvel
  exact indexForm_nonneg_of_isLocalMin_energy hF hγ
    (TauCeti.inner_eq_of_totalSpaceMk_eq hA hvel).symm.le hmin

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
  have hcont : ContinuousAt (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 :=
    (hasDerivAt_energy_exponentialVariation (hV.of_le (by norm_num))).continuousAt
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rwa [(hasDerivAt_deriv_energy_exponentialVariation hV).deriv] at hnn

/-- **Negative index form strictly decreases energy.** Let `γ` be a geodesic on `uIoo a b` and `V`
a field along `γ` with a `C³` lift on `uIcc a b` whose endpoint pairings satisfy
`⟪V(b), γ'_{uIcc a b}(b)⟫ = ⟪V(a), γ'_{uIcc a b}(a)⟫` (for instance because `V` vanishes at `a`
and `b`, is orthogonal to `γ'` at both endpoints, or closes periodically). If `I(V, V) < 0`, then
for every small nonzero `s` the curve `exp_(γ ·) (s • V ·)` has strictly smaller energy than `γ`. -/
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
  have hd₂ := hasDerivAt_deriv_energy_exponentialVariation hV
  simpa only [exponentialVariation_zero] using
    TauCeti.eventually_gt_of_deriv_deriv_neg (hd₂.deriv.symm ▸ hneg) hd₁_zero hd₁.continuousAt

end ExponentialExtremum

end SecondVariation

end TauCeti.Manifold

end
