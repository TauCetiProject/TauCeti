/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.Variation
public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Chart
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Surface
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# The second variation of energy

Let `F : ℝ → ℝ → M` be a two-parameter family of curves in a smooth Riemannian manifold, with
central curve `γ = F 0`, variation field `V(t) = ∂_s F (0, t)`, and transverse acceleration
`A(t) = D_s ∂_s F (0, t)` at `s = 0`. When `F` is `C³` along `{0} × [a, b]`, differentiating the
squared speed `s ↦ ‖∂_t F (s, t)‖²` twice in `s` at `s = 0` exchanges two covariant derivatives
along `F` via `CovariantDerivative.alongCurve_alongCurve_sub_alongCurve_alongCurve`, producing the
integrand of `TauCeti.Manifold.indexForm` together with `⟪D_t A(t), γ'(t)⟫`. Integrating over
`[a, b]` and integrating `⟪D_t A, γ'⟫` by parts gives the second variation of energy:

`d²/ds² E(F s) |₀ = I(V, V) + ⟪A(b), γ'(b)⟫ - ⟪A(a), γ'(a)⟫ - ∫_a^b ⟪A(t), D_t γ'(t)⟫ dt`.

Along a geodesic `γ`, the bulk acceleration integral vanishes and only the index form and the two
endpoint transverse-acceleration pairings remain. Those boundary terms vanish in three geometric
situations: for fixed-endpoint variations (`TauCeti.Manifold.IsFixedEndpointVariation`), for
periodic variations of a smoothly closed geodesic, and for exponential variations
`(s, t) ↦ exp_(γ t) (s • V t)` whose transverse curves are geodesics even when the endpoints move.
Applying the second-derivative tests then shows that `I(V, V) ≥ 0` at a local minimum of the energy
and that a field with `I(V, V) < 0` and vanishing first variation strictly decreases the energy of
nearby exponential-variation curves.

## Main results

* `ContMDiffAt.contMDiffAt_acceleration_fst`: for a jointly `C^n` two-parameter family `F`, the
  transverse acceleration `r ↦ D_s ∂_s F (u, r)` has a `C^m` lift to the tangent bundle along `F u`
  whenever `m + 2 ≤ n`.
* `TauCeti.Manifold.hasDerivAt_deriv_norm_sq_curveVelocity`: pointwise second transverse derivative
  of the squared speed `‖∂_t F (s, t)‖²` at `s = 0`.
* `TauCeti.Manifold.hasDerivAt_deriv_energy`: **the second variation of energy** for a `C³` family
  with free endpoints.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`: specialization to a central
  curve which is a geodesic on `uIoo a b`.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy` and
  `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn`:
  fixed-endpoint specializations.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_of_periodic`: periodic specialization for smoothly
  closed geodesics.
* `TauCeti.Manifold.hasDerivAt_deriv_energy_exponentialVariation`: the second variation of energy
  along `TauCeti.Manifold.exponentialVariation` equals `I(V, V)` even with free endpoints.
* `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy` and
  `TauCeti.Manifold.indexForm_nonneg_of_isLocalMin_energy_exponentialVariation`: nonnegativity of
  the index form at a local minimum of the energy.
* `TauCeti.Manifold.eventually_energy_exponentialVariation_lt_of_indexForm_neg`: strict energy
  decrease along the exponential variation of a geodesic when `I(V, V) < 0` and the endpoint
  first-variation pairings cancel.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 9, Proposition 2.5 and
  Chapter 10, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 10.4 (the second variation formula).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §13 (the second variation of the energy).
-/

public section

open Bundle CovariantDerivative Filter Function MeasureTheory Module Set
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

/-! ### Regularity and product rule for the transverse acceleration -/

omit [T2Space M] in
/-- Near `v`, reading the first-parameter covariant derivative `r ↦ D_q W (u, r)` in the
trivialization at `f u v` gives its chart coordinate formula. -/
private theorem continuousLinearMapAt_alongCurve_fst_eventuallyEq {f : ℝ → ℝ → M}
    {W : ∀ q r, TangentSpace I (f q r)} {u v : ℝ}
    (hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 1
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    let e := trivializationAt E (TangentSpace I) (f u v)
    let hcov := (leviCivitaConnection I M).isCovariantDerivativeOn (s := e.baseSet)
    let Γ := christoffelMap (finBasis ℝ E) hcov
    let φ : ℝ × ℝ → E := fun z ↦ extChartAt I (f u v) (f z.1 z.2)
    let w : ℝ × ℝ → E := fun z ↦ e.continuousLinearMapAt ℝ (f z.1 z.2) (W z.1 z.2)
    (fun r ↦ e.continuousLinearMapAt ℝ (f u r)
        (alongCurve (leviCivitaConnection I M) (fun q ↦ f q r) (fun q ↦ W q r) u)) =ᶠ[𝓝 v]
      fun r ↦ deriv (fun q ↦ w (q, r)) u + Γ (f u r) (w (u, r)) (deriv (fun q ↦ φ (q, r)) u) := by
  intro e hcov Γ φ w
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := ∞) (by norm_num)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1 (fun z : ℝ × ℝ ↦ f z.1 z.2) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp (u, v) hW
  have hnear : ∀ᶠ r in 𝓝 v, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 1
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, r) ∧ f u r ∈ e.baseSet :=
    ((continuous_const.prodMk continuous_id).tendsto v).eventually
      (((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hW).and
        (hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)))
  filter_upwards [hnear] with r ⟨hr, hrb⟩
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun q ↦ TotalSpace.mk' E (f q r) (W q r)) u :=
    hr.comp u (contDiff_prodMk_left r).contMDiff.contMDiffAt
  have hfr : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ f q r) u :=
    ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp u hcurve).mdifferentiableAt one_ne_zero
  have hWr : DifferentiableAt ℝ (sectionCoord (F := E) (fun q ↦ f q r) (fun q ↦ W q r) (f u r)) u :=
    differentiableAt_sectionCoord (fun q ↦ f q r) (fun q ↦ W q r)
      (hcurve.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _)
  have hsc : sectionCoord (F := E) (fun q ↦ f q r) (fun q ↦ W q r) (f u v) = fun q ↦ w (q, r) :=
    funext fun q ↦ by rw [sectionCoord_apply]
  rw [← alongCurveWithin_univ,
    ← symmL_alongCurveInChartWithin (leviCivitaConnection I M) (fun q ↦ f q r) (fun q ↦ W q r) hrb
      hfr.mdifferentiableWithinAt hWr.differentiableWithinAt,
    e.continuousLinearMapAt_symmL (R := ℝ) hrb, alongCurveInChartWithin_apply,
    derivWithin_univ, derivWithin_univ, Function.comp_def, hsc]

/-- If a vector field `W` along a parametrized surface `f : ℝ → ℝ → M` has a `C^(m + 1)` lift to
the tangent bundle at `(u, v)`, then its covariant derivative in the first parameter at `u` has a
`C^m` lift along `f u` at `v`. -/
private theorem contMDiffAt_alongCurve_fst {f : ℝ → ℝ → M}
    {W : ∀ q r, TangentSpace I (f q r)} {u v : ℝ} {m : ℕ∞}
    (hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent ((m : ℕ∞ω) + 1)
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent m
      (fun r ↦ TotalSpace.mk' E (f u r)
        (alongCurve (leviCivitaConnection I M) (fun q ↦ f q r) (fun q ↦ W q r) u)) v := by
  set cov := leviCivitaConnection I M
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  set Γ := christoffelMap (finBasis ℝ E) hcov
  have : ContMDiffCovariantDerivativeOn E ∞ cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) cov e.open_baseSet
  have hm1_le : (m : ℕ∞ω) + 1 ≤ ∞ := by
    rw [← WithTop.coe_one, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.mpr le_top
  have hm2_le : (m : ℕ∞ω) + 1 + 1 ≤ ∞ := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.mpr le_top
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold I m M := IsManifold.of_le (le_self_add.trans hm1_le)
  have : IsManifold I ((m : ℕ∞ω) + 1) M := IsManifold.of_le hm1_le
  have : IsManifold I ((m : ℕ∞ω) + 1 + 1) M := IsManifold.of_le hm2_le
  have : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : ContMDiffVectorBundle m E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : ContMDiffVectorBundle ((m : ℕ∞ω) + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ((m : ℕ∞ω) + 1) (fun z : ℝ × ℝ ↦ f z.1 z.2) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp (u, v) hW
  have hfu : ContMDiffAt 𝓘(ℝ, ℝ) I ((m : ℕ∞ω) + 1) (f u) v :=
    hf.comp v (contDiff_prodMk_right u).contMDiff.contMDiffAt
  set φ : ℝ × ℝ → E := fun z ↦ extChartAt I (f u v) (f z.1 z.2)
  set w : ℝ × ℝ → E := fun z ↦ e.continuousLinearMapAt ℝ (f z.1 z.2) (W z.1 z.2)
  have hφ : ContDiffAt ℝ ((m : ℕ∞ω) + 1) φ (u, v) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (mem_chart_source H (f u v))).comp (u, v) hf)
  have hw : ContDiffAt ℝ ((m : ℕ∞ω) + 1) w (u, v) :=
    hW.contDiffAt_continuousLinearMapAt_trivializationAt
  have hΓv : ContDiffAt ℝ m (fun r ↦ Γ (f u r)) v := by
    have hΓm : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) m Γ (f u v) :=
      ((contMDiffOn_christoffelMap (n := ∞) (finBasis ℝ E) hcov).contMDiffAt
        (e.open_baseSet.mem_nhds hbase)).of_le (WithTop.coe_le_coe.mpr le_top)
    exact contMDiffAt_iff_contDiffAt.mp (hΓm.comp v (hfu.of_le le_self_add))
  have hwv : ContDiffAt ℝ m (fun r ↦ w (u, r)) v :=
    (hw.of_le le_self_add).comp v (contDiff_prodMk_right u).contDiffAt
  have hcoord : ContDiffAt ℝ m
      (fun r ↦ deriv (fun q ↦ w (q, r)) u + Γ (f u r) (w (u, r)) (deriv (fun q ↦ φ (q, r)) u)) v :=
    (TauCeti.contDiffAt_deriv_slice_left hw).add
      ((hΓv.clm_apply hwv).clm_apply (TauCeti.contDiffAt_deriv_slice_left hφ))
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨hfu.of_le le_self_add, (contMDiffAt_iff_contDiffAt.mpr hcoord).congr_of_eventuallyEq ?_⟩
  filter_upwards [continuousLinearMapAt_alongCurve_fst_eventuallyEq (hW.of_le le_add_self),
    hfu.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)] with r hr hrb
  rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hrb, hr]

/-- **Regularity of the transverse acceleration.** If a two-parameter family `F : ℝ → ℝ → M` is
jointly `C^n` at `(u, t)` and `m + 2 ≤ n`, then the covariant accelerations
`r ↦ D_s ∂_s F (u, r)` of its transverse curves form a `C^m` section along `F u` at `t`. -/
theorem _root_.ContMDiffAt.contMDiffAt_acceleration_fst {u t : ℝ} {m : ℕ∞} {n : ℕ∞ω}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (u, t))
    (hmn : (m : ℕ∞ω) + 2 ≤ n) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent m
      (fun r ↦ TotalSpace.mk' E (F u r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) u)) t := by
  have hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent ((m : ℕ∞ω) + 1)
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (F z.1 z.2) (curveVelocity I (fun q ↦ F q z.2) z.1))
      (u, t) :=
    hf.contMDiffAt_curveVelocity_fst (by rwa [add_assoc, one_add_one_eq_two])
  simpa only [acceleration_def] using contMDiffAt_alongCurve_fst hW

/-- **Product rule for the transverse acceleration against the velocity.** At a parameter `t`
where the family `F` is `C³` at `(0, t)`, the pairing `r ↦ ⟪D_s ∂_s F (0, r), γ'(r)⟫` along
`γ = F 0` differentiates to `⟪D_t (D_s ∂_s F) (0, t), γ'(t)⟫ + ⟪D_s ∂_s F (0, t), D_t γ'(t)⟫`.
Integrated over `[a, b]`, this turns the `⟪D_t A, γ'⟫` term of the second variation into boundary
terms minus `∫ ⟪A, D_t γ'⟫`. -/
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
  have hA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0)) t :=
    hf.contMDiffAt_acceleration_fst (m := 1) (by norm_num)
  have hAcoord : DifferentiableAt ℝ
      (sectionCoord (F := E) (F 0)
        (fun r ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0) (F 0 t)) t :=
    differentiableAt_sectionCoord (F 0) _ (hA.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t))
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F 0) t :=
    (hf.of_le (by norm_num)).comp t (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F 0)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  rw [acceleration_def (γ := F 0)]
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve (hγt.mdifferentiableAt two_ne_zero) hAcoord hγcoord

/-- At a parameter `t` where `F` is `C³` at `(0, t)`, the pairing
`r ↦ ⟪D_t (D_s ∂_s F) (0, r), γ'(r)⟫` is continuous at `t`. -/
theorem continuousAt_inner_alongCurve_acceleration_fst_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContinuousAt
      (fun r ↦ inner ℝ (alongCurve (leviCivitaConnection I M) (F 0)
        (fun q ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s q) 0) r)
        (curveVelocity I (F 0) r)) t := by
  have hDA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F 0 r) (alongCurve (leviCivitaConnection I M) (F 0)
        (fun q ↦ acceleration (leviCivitaConnection I M) (fun s ↦ F s q) 0) r)) t :=
    contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := ∞) (k := ∞) (by simp) (by simp)
      (by simpa using hf.contMDiffAt_acceleration_fst (m := 1) (by norm_num))
  have hvel : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F 0 r) (curveVelocity I (F 0) r)) t :=
    hf.contMDiffAt_curveVelocity_snd (m := 0) (by norm_num)
      |>.comp t (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt
  exact (ContMDiffAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := F 0) (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le) hDA hvel).continuousAt

/-- At a parameter `t` where `F` is `C³` at `(0, t)`, the pairing
`r ↦ ⟪D_s ∂_s F (0, r), D_r γ'(r)⟫` of the transverse and longitudinal accelerations is continuous
at `t`. -/
theorem continuousAt_inner_acceleration_fst_acceleration {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    ContinuousAt
      (fun r ↦ inner ℝ (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0)
        (acceleration (leviCivitaConnection I M) (F 0) r)) t := by
  have hA : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F 0 r)
        (acceleration (leviCivitaConnection I M) (fun s ↦ F s r) 0)) t :=
    hf.contMDiffAt_acceleration_fst (m := 0) (by norm_num)
  have hvel : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (F 0 r) (curveVelocity I (F 0) r)) t :=
    hf.contMDiffAt_curveVelocity_snd (m := 1) (by norm_num)
      |>.comp t (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt
  have hacc : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (F 0 r) (acceleration (leviCivitaConnection I M) (F 0) r)) t := by
    simpa only [acceleration_def] using
      contMDiffAt_alongCurve_leviCivitaConnection (n := 0) (m := ∞) (k := ∞) (by simp) (by simp)
        (by simpa using hvel)
  exact (ContMDiffAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := F 0) (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le) hA hacc).continuousAt

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
  let σ : ℝ → M := fun s ↦ F s t
  let P : ∀ s, TangentSpace I (σ s) := fun s ↦ curveVelocity I (F s) t
  have hP : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun s ↦ TotalSpace.mk' E (σ s) (P s)) 0 :=
    hf.contMDiffAt_curveVelocity_snd_slice (by norm_num)
  have hnear : ∀ᶠ s in 𝓝 0, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (s, t) :=
    ((continuous_id.prodMk continuous_const).tendsto 0).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hf)
  have hd₁ : (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) =ᶠ[𝓝 0]
      fun s ↦ 2 * inner ℝ (alongCurve cov σ P s) (P s) := by
    filter_upwards [hnear] with s hs
    have hPs : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun q ↦ TotalSpace.mk' E (σ q) (P q)) s :=
      hs.contMDiffAt_curveVelocity_snd_slice (by norm_num)
    have hPcoord : DifferentiableAt ℝ (sectionCoord (F := E) σ P (σ s)) s :=
      differentiableAt_sectionCoord σ P (hPs.mdifferentiableAt (by norm_num))
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (σ s))
    have hσs : MDifferentiableAt 𝓘(ℝ, ℝ) I σ s :=
      ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp s hPs).mdifferentiableAt (by norm_num)
    have hprod := (hm.hasDerivAt_inner_alongCurve hσs hPcoord hPcoord).congr_of_eventuallyEq
      (Eventually.of_forall fun q ↦ (real_inner_self_eq_norm_sq (P q)).symm)
    rw [hprod.deriv, real_inner_comm (P s), two_mul]
  have hDPcoord : DifferentiableAt ℝ (sectionCoord (F := E) σ (alongCurve cov σ P) (σ 0)) 0 :=
    differentiableAt_sectionCoord_alongCurve_leviCivitaConnection hP
  have hP0coord : DifferentiableAt ℝ (sectionCoord (F := E) σ P (σ 0)) 0 :=
    differentiableAt_sectionCoord σ P (hP.mdifferentiableAt (by norm_num))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (σ 0))
  have hσ0 : MDifferentiableAt 𝓘(ℝ, ℝ) I σ 0 :=
    ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp 0 hP).mdifferentiableAt (by norm_num)
  have hd₂ := ((hm.hasDerivAt_inner_alongCurve hσ0 hDPcoord hP0coord).const_mul 2)
    |>.congr_of_eventuallyEq hd₁
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
  rw [show alongCurve cov σ (alongCurve cov σ P) 0 = _ from
      alongCurve_alongCurve_curveVelocity_snd_zero hf,
    hswap0, inner_add_left, hcurv, indexFormIntegrand_def]
  dsimp only [P, cov]
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
  obtain ⟨U, V, hUo, hVo, h0U, hV, hfUV⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hF
  have hUVo : IsOpen (U ×ˢ V) := hUo.prod hVo
  let G : ℝ × ℝ → ℝ := fun z ↦
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) z ((0 : ℝ), (1 : ℝ)))
  let G₁ : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ G z (1, 0)
  have hG : ContDiffOn ℝ 2 G (U ×ˢ V) :=
    hfUV.contDiffOn_inner_mfderiv (by norm_num) hUVo ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ))
  have hG₁ : ContDiffOn ℝ 1 G₁ (U ×ˢ V) :=
    (hG.fderiv_of_isOpen hUVo (by norm_num)).clm_apply contDiffOn_const
  have hGeq : ∀ {s t : ℝ}, s ∈ U → t ∈ V → G (s, t) = ‖curveVelocity I (F s) t‖ ^ 2 := by
    intro s t hs ht
    dsimp only [G]
    rw [← curveVelocity_eq_mfderiv_snd
      ((hfUV.contMDiffAt (hUVo.mem_nhds ⟨hs, ht⟩)).mdifferentiableAt (by norm_num)),
      real_inner_self_eq_norm_sq]
  have hdE : (deriv fun s ↦ energy I (F s) a b) =ᶠ[𝓝 0]
      fun s ↦ (∫ t in a..b, G₁ (s, t)) / 2 := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    obtain ⟨_, hGs⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo (hG.of_le one_le_two)
      (prod_mono (singleton_subset_iff.mpr hs) hV)
    have heq : (fun q ↦ energy I (F q) a b) =ᶠ[𝓝 s] fun q ↦ (∫ t in a..b, G (q, t)) / 2 := by
      filter_upwards [hUo.mem_nhds hs] with q hq
      rw [energy_def]
      exact congrArg (· / 2) (intervalIntegral.integral_congr fun t ht ↦ (hGeq hq (hV ht)).symm)
    exact ((hGs.div_const 2).congr_of_eventuallyEq heq).deriv
  obtain ⟨_, hG₁d⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hUVo hG₁
    (prod_mono (singleton_subset_iff.mpr h0U) hV)
  refine ((hG₁d.div_const 2).congr_of_eventuallyEq hdE).congr_deriv ?_
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have hf₁ : HasFDerivAt G₁ (fderiv ℝ G₁ (0, t)) (0, t) :=
    ((hG₁.differentiableOn one_ne_zero (0, t) ⟨h0U, hV ht⟩).differentiableAt
      (hUVo.mem_nhds ⟨h0U, hV ht⟩)).hasFDerivAt
  have hdG₁ :=
    hf₁.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t))
  have hG₁eq : (deriv fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2) =ᶠ[𝓝 0] fun s ↦ G₁ (s, t) := by
    filter_upwards [hUo.mem_nhds h0U] with s hs
    have hfs : HasFDerivAt G (fderiv ℝ G (s, t)) (s, t) :=
      ((hG.differentiableOn (by norm_num) (s, t) ⟨hs, hV ht⟩).differentiableAt
        (hUVo.mem_nhds ⟨hs, hV ht⟩)).hasFDerivAt
    have hdGs := hfs.comp_hasDerivAt s ((hasDerivAt_id' s).prodMk (hasDerivAt_const s t))
    have hsq : (fun q ↦ ‖curveVelocity I (F q) t‖ ^ 2) =ᶠ[𝓝 s] fun q ↦ G (q, t) := by
      filter_upwards [hUo.mem_nhds hs] with q hq using (hGeq hq (hV ht)).symm
    exact (hdGs.congr_of_eventuallyEq hsq).deriv
  have hu := (hdG₁.congr_of_eventuallyEq hG₁eq).unique
    (hasDerivAt_deriv_norm_sq_curveVelocity (hF t ht))
  linarith

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
  have hintAA : IntervalIntegrable (fun t ↦ inner ℝ
      (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
      (acceleration (leviCivitaConnection I M) (F 0) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inner_acceleration_fst_acceleration (hF t ht)).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_inner_acceleration_fst_curveVelocity (hF t ht)) (hintDA.add hintAA)
  rw [intervalIntegral.integral_add hintDA hintAA] at hFTC
  refine (hasDerivAt_deriv_energy_eq_integral hF).congr_deriv ?_
  rw [intervalIntegral.integral_add hintI hintDA, ← indexForm_def, eq_sub_of_add_eq hFTC]
  ring

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
  refine (hasDerivAt_deriv_energy hF).congr_deriv ?_
  have hzero : ∫ t in a..b, inner ℝ
      (acceleration (leviCivitaConnection I M) (fun s ↦ F s t) 0)
      (acceleration (leviCivitaConnection I M) (F 0) t) = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    have hmem : uIoo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    rw [← accelerationWithin_of_mem_nhds _ (F 0) hmem,
      hγ.accelerationWithin_eq_zero t ht, inner_zero_right]
  rw [hzero, sub_zero]

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

/-- **Second variation of energy of a geodesic for fixed endpoints.** For a `C³` fixed-endpoint
variation `F` of a curve `γ = F 0` which is a geodesic on `uIoo a b`, the second derivative of
`s ↦ E(F s)` at `s = 0` is the index form `I(V, V)`. -/
theorem IsFixedEndpointVariation.hasDerivAt_deriv_energy_of_isGeodesicCurveOn {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b) (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b)) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  have ha : acceleration (leviCivitaConnection I M) (fun s ↦ F s a) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_left).trans
      (acceleration_const (leviCivitaConnection I M) (F 0 a) 0)
  have hb : acceleration (leviCivitaConnection I M) (fun s ↦ F s b) 0 = 0 :=
    (Filter.EventuallyEq.acceleration_eq (leviCivitaConnection I M) hF.eventually_apply_right).trans
      (acceleration_const (leviCivitaConnection I M) (F 0 b) 0)
  refine (TauCeti.Manifold.hasDerivAt_deriv_energy_of_isGeodesicCurveOn
    hF.contMDiffAt hγ).congr_deriv ?_
  rw [ha, hb, inner_zero_left, inner_zero_left]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Two pairs of tangent vectors with equal tangent-bundle lifts have equal Riemannian inner
product. -/
private theorem inner_eq_of_totalSpaceMk_eq {x y : M} {u v : TangentSpace I x}
    {u' v' : TangentSpace I y}
    (hu : TotalSpace.mk' E x u = TotalSpace.mk' E y u')
    (hv : TotalSpace.mk' E x v = TotalSpace.mk' E y v') :
    inner ℝ u v = inner ℝ u' v' := by
  cases hu
  cases hv
  rfl

/-- **Second variation of energy of a smoothly closed geodesic.** If `F` is `C³` along
`{0} × [a, b]`, its nearby curves are closed (`F s a = F s b` for `s` near `0`), and its central
curve `γ = F 0` is a geodesic on `uIoo a b` with matching endpoint velocity lifts
`curveVelocityLift I γ a = curveVelocityLift I γ b`, then the boundary transverse-acceleration
pairings cancel and `d²/ds² E(F s) |₀ = I(V, V)`. -/
theorem hasDerivAt_deriv_energy_of_periodic {a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hper : ∀ᶠ s in 𝓝 0, F s a = F s b)
    (hvel : curveVelocityLift I (F 0) a = curveVelocityLift I (F 0) b) :
    HasDerivAt (deriv fun s ↦ energy I (F s) a b)
      (indexForm I (F 0) (variationField I F) (variationField I F) a b) 0 := by
  refine (hasDerivAt_deriv_energy_of_isGeodesicCurveOn hF hγ).congr_deriv ?_
  have hA := Filter.EventuallyEq.totalSpaceMk_acceleration_eq
    (leviCivitaConnection I M) hper
  rw [curveVelocityLift_apply, curveVelocityLift_apply] at hvel
  rw [inner_eq_of_totalSpaceMk_eq hA hvel]
  ring

section ExponentialVariation

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- When `V` has a `C^n` lift on `[a, b]` and vanishes at `a` and `b`, the exponential variation of
`γ` along `V` is a `C^n` variation with fixed endpoints. -/
theorem isFixedEndpointVariation_exponentialVariation {n : ℕ∞} {a b : ℝ}
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (ha : V a = 0) (hb : V b = 0) :
    IsFixedEndpointVariation I n (exponentialVariation I γ V) a b :=
  ⟨fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht),
    Eventually.of_forall fun s ↦ by simp [ha],
    Eventually.of_forall fun s ↦ by simp [hb]⟩

/-- Every transverse curve `s ↦ exp_(γ t) (s • V t)` of the exponential variation has zero
covariant acceleration at `s = 0`. -/
@[simp]
theorem acceleration_exponentialVariation_zero (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) :
    acceleration (leviCivitaConnection I M) (fun s ↦ exponentialVariation I γ V s t) 0 = 0 := by
  have hgeo := (isGeodesicCurveOnFrom_exponentialVariation γ V t).isGeodesicCurveOn
  have h0 : (0 : ℝ) ∈ geodesicInterval I M (γ t) (V t) := zero_mem_geodesicInterval
  rw [← accelerationWithin_of_mem_nhds _ _ (isOpen_geodesicInterval.mem_nhds h0)]
  exact hgeo.accelerationWithin_eq_zero 0 h0

/-- **First variation of energy along an exponential variation.** Let `V` be a tangent field along
`γ` whose lift to the tangent bundle is `C²` at every point of `[a, b]`. Then the energy of
`exp_(γ ·) (s • V ·)` between `a` and `b` has derivative
`⟪V(b), γ'(b)⟫ - ⟪V(a), γ'(a)⟫ - ∫_a^b ⟪V(t), D_t γ'(t)⟫ dt` at `s = 0`. -/
theorem hasDerivAt_energy_exponentialVariation {a b : ℝ}
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    HasDerivAt (fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (inner ℝ (V b) (curveVelocity I γ b) -
        inner ℝ (V a) (curveVelocity I γ a) -
        ∫ t in a..b, inner ℝ (V t) (acceleration (leviCivitaConnection I M) γ t)) 0 := by
  have hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  have hVlift (t : ℝ) :
      TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (variationField I (exponentialVariation I γ V) t) =
      TotalSpace.mk' E (γ t) (V t) :=
    TotalSpace.ext (congrFun (exponentialVariation_zero γ V) t)
      (heq_of_eq (variationField_exponentialVariation γ V t))
  have hvel (t : ℝ) :
      TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (curveVelocity I (exponentialVariation I γ V 0) t) =
      TotalSpace.mk' E (γ t) (curveVelocity I γ t) := by
    simpa only [curveVelocityLift_apply] using
      congrArg (fun c ↦ curveVelocityLift I c t) (exponentialVariation_zero γ V)
  have hacc (t : ℝ) :
      TotalSpace.mk' E (exponentialVariation I γ V 0 t)
        (acceleration (leviCivitaConnection I M) (exponentialVariation I γ V 0) t) =
      TotalSpace.mk' E (γ t) (acceleration (leviCivitaConnection I M) γ t) :=
    Filter.EventuallyEq.totalSpaceMk_acceleration_eq (leviCivitaConnection I M)
      (Eventually.of_forall (congrFun (exponentialVariation_zero γ V)))
  refine (hasDerivAt_energy hF).congr_deriv ?_
  rw [inner_eq_of_totalSpaceMk_eq (hVlift b) (hvel b),
    inner_eq_of_totalSpaceMk_eq (hVlift a) (hvel a),
    intervalIntegral.integral_congr fun t _ ↦ inner_eq_of_totalSpaceMk_eq (hVlift t) (hacc t)]

/-- **Second variation of energy along an exponential variation.** Let `V` be a tangent field along
an arbitrary curve `γ` whose lift to the tangent bundle is `C³` at every point of `[a, b]`. Because
each transverse curve `s ↦ exp_(γ t) (s • V t)` is a geodesic, all transverse-acceleration terms in
`hasDerivAt_deriv_energy` vanish and `d²/ds² E(exp_(γ ·) (s • V ·)) |₀ = I(V, V)`, even without
assuming that `γ` is a geodesic or that `V` vanishes at the endpoints. -/
theorem hasDerivAt_deriv_energy_exponentialVariation {a b : ℝ}
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    HasDerivAt (deriv fun s ↦ energy I (exponentialVariation I γ V s) a b)
      (indexForm I γ V V a b) 0 := by
  have hF : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (0, t) :=
    fun t ht ↦ contMDiffAt_exponentialVariation_zero γ V (hV t ht)
  have hd := hasDerivAt_deriv_energy hF
  -- Rewrite the central curve `exponentialVariation I γ V 0` to `γ` and `variationField` to `V`.
  have hVheq (t : ℝ) : HEq (variationField I (exponentialVariation I γ V) t) (V t) :=
    heq_of_eq (variationField_exponentialVariation γ V t)
  have hI : indexForm I (exponentialVariation I γ V 0)
        (variationField I (exponentialVariation I γ V))
        (variationField I (exponentialVariation I γ V)) a b =
      indexForm I γ V V a b :=
    indexForm_congr (fun t _ ↦ congrFun (exponentialVariation_zero γ V) t)
      (fun t _ ↦ hVheq t) (fun t _ ↦ hVheq t)
  refine hd.congr_deriv ?_
  rw [hI, acceleration_exponentialVariation_zero, acceleration_exponentialVariation_zero,
    inner_zero_left, inner_zero_left]
  have hzero : ∫ t in a..b, inner ℝ
      (acceleration (leviCivitaConnection I M)
        (fun s ↦ exponentialVariation I γ V s t) 0)
      (acceleration (leviCivitaConnection I M)
        (exponentialVariation I γ V 0) t) = 0 := by
    simp [acceleration_exponentialVariation_zero]
  rw [hzero]
  ring

end ExponentialVariation

/-! ### Index-form nonnegativity at local minima and energy-decreasing variations -/

/-- **Nonnegativity of the index form at a local minimum of the energy.** If `F` is a `C³`
fixed-endpoint variation of a geodesic `γ = F 0` on `uIoo a b` and `s ↦ E(F s)` has a local
minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy {a b : ℝ}
    (hF : IsFixedEndpointVariation I 3 F a b)
    (hγ : IsGeodesicCurveOn I (F 0) (uIoo a b))
    (hmin : IsLocalMin (fun s ↦ energy I (F s) a b) 0) :
    0 ≤ indexForm I (F 0) (variationField I F) (variationField I F) a b := by
  have hcont : ContinuousAt (fun s ↦ energy I (F s) a b) 0 :=
    (hasDerivAt_energy (fun t ht ↦ (hF.contMDiffAt t ht).of_le (by norm_num))).continuousAt
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rwa [(hF.hasDerivAt_deriv_energy_of_isGeodesicCurveOn hγ).deriv] at hnn

section ExponentialExtremum

variable [I.Boundaryless] {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}

/-- **Nonnegativity of the index form from local energy minimality along an exponential
variation.** If `V` has a `C³` lift on `[a, b]` and `s ↦ E(exp_(γ ·) (s • V ·))` has a local
minimum at `s = 0`, then `0 ≤ I(V, V)`. -/
theorem indexForm_nonneg_of_isLocalMin_energy_exponentialVariation {a b : ℝ}
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hmin : IsLocalMin (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0) :
    0 ≤ indexForm I γ V V a b := by
  have hcont : ContinuousAt (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 :=
    (hasDerivAt_energy_exponentialVariation fun t ht ↦ (hV t ht).of_le (by norm_num)).continuousAt
  have hnn := TauCeti.deriv_deriv_nonneg_of_isLocalMin hcont hmin
  rwa [(hasDerivAt_deriv_energy_exponentialVariation hV).deriv] at hnn

/-- **Negative index form strictly decreases energy.** Let `γ` be a geodesic on `uIoo a b` and `V`
a field along `γ` with a `C³` lift on `[a, b]` whose endpoint pairings satisfy
`⟪V(b), γ'(b)⟫ = ⟪V(a), γ'(a)⟫` (for instance because `V` vanishes at `a` and `b`, is orthogonal to
`γ'` at both endpoints, or closes periodically). If `I(V, V) < 0`, then for every small nonzero `s`
the curve `exp_(γ ·) (s • V ·)` has strictly smaller energy than `γ`. -/
theorem eventually_energy_exponentialVariation_lt_of_indexForm_neg {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (uIoo a b))
    (hV : ∀ t ∈ uIcc a b,
      ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 3 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t)
    (hbdry : inner ℝ (V b) (curveVelocity I γ b) = inner ℝ (V a) (curveVelocity I γ a))
    (hneg : indexForm I γ V V a b < 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ), energy I (exponentialVariation I γ V s) a b < energy I γ a b := by
  have hd₁ := hasDerivAt_energy_exponentialVariation fun t ht ↦ (hV t ht).of_le (by norm_num)
  have hbulk : ∫ t in a..b, inner ℝ (V t) (acceleration (leviCivitaConnection I M) γ t) = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    have hmem : uIoo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    rw [← accelerationWithin_of_mem_nhds _ γ hmem,
      hγ.accelerationWithin_eq_zero t ht, inner_zero_right]
  have hd₁_zero : deriv (fun s ↦ energy I (exponentialVariation I γ V s) a b) 0 = 0 := by
    rw [hd₁.deriv, hbulk, hbdry, sub_self, sub_zero]
  have hd₂ := hasDerivAt_deriv_energy_exponentialVariation hV
  simpa only [exponentialVariation_zero] using
    TauCeti.eventually_gt_of_deriv_deriv_neg (hd₂.deriv.symm ▸ hneg) hd₁_zero hd₁.continuousAt

end ExponentialExtremum

end TauCeti.Manifold

end
