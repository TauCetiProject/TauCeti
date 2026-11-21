/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Linearization
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
import TauCeti.Analysis.Complex.Circle

/-!
# Gauge covariance of the weak kernel and of the weak right inverse

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` has formal adjoint `L_x*`
(`TauCeti.Vortex.gaugeFixedAdjoint`). A charge-one gauge `u : ℂ → Circle` acts on fields by
`TauCeti.Vortex.gaugeTransform`, and on variations and on the target of `L_x` by its linear part
`TauCeti.Vortex.gaugeLinearAction`, which fixes the two real rows and multiplies the complex row
by `u`. For differentiable gauges the two actions intertwine the operators,
`L_{u·x}* (u·η) = u·(L_x* η)` (`TauCeti.Vortex.gaugeFixedAdjoint_gaugeTransform`). This file
transfers that pointwise law to the weak `L²` theory of `L_x`, where Taubes's analysis of the
deformation theory of plane vortices takes place.

The linear action is a pointwise isometry of the values
(`TauCeti.Vortex.inner_gaugeLinearAction`), so for a continuous gauge it defines a linear
isometry `TauCeti.Vortex.gaugeLp μ u` of `L²(ℂ; ℝ⁴)`, with inverse the action of `u⁻¹`
(`TauCeti.Vortex.gaugeLp_symm`), compatible with the multiplication of gauges
(`TauCeti.Vortex.gaugeLp_mul`). It covers both the framed gauges, which tend to one at infinity,
and the constant line-frame gauges `u^(-m)` that restore the end framing after a rotation; these
do not tend to one, and only their derivative matters below.

**Weak solutions.** A square-integrable field `y` is a *weak solution* of `L_x y = f`
(`TauCeti.Vortex.IsGaugeFixedWeakSolution`) if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
supported `C²` test field `η`, and it is *minimal*
(`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution`) if moreover it is orthogonal to every weak
solution of `L_x w = 0`. The values `Q f` of the weak
right inverse `Q` of `TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`,
which exists at every plane vortex with `|α| → 1`, are minimal weak solutions.

* For a `Cⁿ` gauge with `n ≥ 1`, testing `u·y` against `L_{u·x}*` on compactly supported `Cⁿ`
  test fields is testing `y` against `L_x*` on them
  (`TauCeti.Vortex.forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff`): the test
  field `η` is traded for `u⁻¹·η`. Hence for a `C²` gauge, `u·y` is a (minimal) weak solution of
  `L_{u·x} (u·y) = u·f` exactly when `y` is one of `L_x y = f`
  (`TauCeti.Vortex.isGaugeFixedWeakSolution_gaugeLp_iff`,
  `TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_iff`).
* At a continuous field the minimal weak solution is unique
  (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`). So the weak right
  inverse is determined by `x`, and every weak right inverse `Q'` at `u·x` is the conjugate
  `Q' = u ∘ Q ∘ u⁻¹` of every weak right inverse `Q` at `x`
  (`TauCeti.Vortex.apply_gaugeLp_eq_gaugeLp_apply`). In particular a weak right inverse at `x`
  supplies one at every gauge transform of `x`
  (`TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_apply_symm`).

**The weak kernel.** For a `C¹` gauge and a continuous field, the weak `L²` kernel
`TauCeti.Vortex.weakGaugeFixedKernel` of `L_{u·x}` is the image of that of `L_x` under the gauge
(`TauCeti.Vortex.weakGaugeFixedKernel_gaugeTransform`); this is the case `n = 1`, `f = 0` of the
transport of weak equations above, since the weak kernel is detected by `C¹` test fields
(`TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff_one`). Since the gauge is a linear
isometry, the orthogonal projections onto the two kernels are conjugate
(`TauCeti.Vortex.starProjection_weakGaugeFixedKernel_gaugeTransform`) and the kernels have the
same dimension (`TauCeti.Vortex.finrank_weakGaugeFixedKernel_gaugeTransform`).

These are the line-frame and gauge laws of the kernel projections and right inverses of the
linearized vortex operator; the corresponding laws for translations and rotations of the plane
need the action of rigid motions on `L²`, and are not treated here.

## Main definitions

* `TauCeti.Vortex.gaugeLp μ u`: the linear gauge action of a continuous gauge on `L²(ℂ; ℝ⁴)`.

## Main results

* `TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_iff`: gauge covariance of minimal
  weak solutions.
* `TauCeti.Vortex.apply_gaugeLp_eq_gaugeLp_apply`: weak right inverses at `x` and `u·x` are
  conjugate by the gauge.
* `TauCeti.Vortex.weakGaugeFixedKernel_gaugeTransform`,
  `TauCeti.Vortex.starProjection_weakGaugeFixedKernel_gaugeTransform`: gauge covariance of the
  weak kernel and of the orthogonal projection onto it.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff

/-! ### Continuity of the gauge action on values -/

/-- The value of the linear gauge action is a continuous function of the value of the gauge and
of the value of the variation. -/
private theorem continuous_gaugeLinearAction_uncurry :
    Continuous fun p : Circle × EuclideanSpace ℝ (Fin 4) ↦
      gaugeLinearAction (fun _ ↦ p.1) (fun _ ↦ p.2) 0 := by
  simp only [gaugeLinearAction_apply]
  fun_prop

/-! ### The gauge action on `L²` -/

section Lp

variable {μ : Measure ℂ}

/-- The linear action of an almost everywhere strongly measurable gauge preserves `Lᵖ` fields. -/
theorem memLp_gaugeLinearAction {u : ℂ → Circle} (hu : AEStronglyMeasurable u μ) {p : ENNReal}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y p μ) :
    MemLp (gaugeLinearAction u y) p μ := by
  have h : gaugeLinearAction u y =
      fun z ↦ gaugeLinearAction (fun _ ↦ (u z, y z).1) (fun _ ↦ (u z, y z).2) 0 := by
    funext z
    simp only [gaugeLinearAction_apply]
  refine hy.of_le ?_ (ae_of_all _ fun z ↦ (norm_gaugeLinearAction u y z).le)
  rw [h]
  exact continuous_gaugeLinearAction_uncurry.comp_aestronglyMeasurable
    (hu.prodMk hy.aestronglyMeasurable)

/-- The value of the linear gauge action at a point only depends on the value of the variation
there, so the action respects almost everywhere equality. -/
theorem gaugeLinearAction_ae_eq (u : ℂ → Circle) {y w : ℂ → EuclideanSpace ℝ (Fin 4)}
    (h : y =ᵐ[μ] w) : gaugeLinearAction u y =ᵐ[μ] gaugeLinearAction u w :=
  h.mono fun z hz ↦ by simp only [gaugeLinearAction_apply, hz]

/-- The linear gauge action on `L²`, as a linear map. -/
private def gaugeLpₗ (μ : Measure ℂ) (u : C(ℂ, Circle)) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun f := (memLp_gaugeLinearAction u.continuous.aestronglyMeasurable (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ((gaugeLinearAction_ae_eq u (Lp.coeFn_add f g)).trans ?_)
    rw [map_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ((gaugeLinearAction_ae_eq u (Lp.coeFn_smul c f)).trans ?_)
    rw [map_smul]

private theorem coeFn_gaugeLpₗ (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLpₗ μ u f =ᵐ[μ] gaugeLinearAction u f :=
  (memLp_gaugeLinearAction u.continuous.aestronglyMeasurable (Lp.memLp f)).coeFn_toLp

private theorem gaugeLpₗ_gaugeLpₗ_inv (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLpₗ μ u (gaugeLpₗ μ u⁻¹ f) = f := by
  refine Lp.ext ((coeFn_gaugeLpₗ u _).trans ?_)
  refine (gaugeLinearAction_ae_eq u (coeFn_gaugeLpₗ u⁻¹ f)).trans (.of_eq ?_)
  rw [ContinuousMap.coe_inv, gaugeLinearAction_gaugeLinearAction_inv]

/-- **The linear gauge action on `L²(ℂ; ℝ⁴)`.** A continuous gauge `u : ℂ → Circle` acts on
square-integrable variations and on the target of `L_x` by its linear part
`TauCeti.Vortex.gaugeLinearAction`, fixing the two real rows and multiplying the complex row by
`u`. This is a linear isometry, with inverse the action of `u⁻¹`. -/
def gaugeLp (μ : Measure ℂ) (u : C(ℂ, Circle)) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ ≃ₗᵢ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toLinearMap := gaugeLpₗ μ u
  invFun := gaugeLpₗ μ u⁻¹
  left_inv f := by
    have h := gaugeLpₗ_gaugeLpₗ_inv (μ := μ) u⁻¹ f
    rw [inv_inv] at h
    exact h
  right_inv := gaugeLpₗ_gaugeLpₗ_inv u
  norm_map' f := by
    -- The goal is stated for the structure's underlying function; restate it for `gaugeLpₗ`.
    change ‖gaugeLpₗ μ u f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_gaugeLpₗ u f),
      eLpNorm_congr_norm_ae
      (memLp_gaugeLinearAction u.continuous.aestronglyMeasurable (Lp.memLp f)).aestronglyMeasurable
      (Lp.aestronglyMeasurable f) (ae_of_all _ (norm_gaugeLinearAction u f))]

theorem coeFn_gaugeLp (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLp μ u f =ᵐ[μ] gaugeLinearAction u f :=
  coeFn_gaugeLpₗ u f

@[simp]
theorem gaugeLp_symm (u : C(ℂ, Circle)) : (gaugeLp μ u).symm = gaugeLp μ u⁻¹ :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

@[simp]
theorem gaugeLp_one : gaugeLp μ 1 = LinearIsometryEquiv.refl ℝ _ := by
  ext1 f
  refine Lp.ext ((coeFn_gaugeLp 1 f).trans (.of_eq ?_))
  rw [ContinuousMap.coe_one, gaugeLinearAction_one, LinearIsometryEquiv.coe_refl, id_eq]

/-- The action of a product of gauges is the composite of their actions. -/
theorem gaugeLp_mul (u v : C(ℂ, Circle)) :
    gaugeLp μ (u * v) = (gaugeLp μ v).trans (gaugeLp μ u) := by
  ext1 f
  refine Lp.ext ((coeFn_gaugeLp _ f).trans ?_)
  rw [LinearIsometryEquiv.trans_apply]
  refine (EventuallyEq.of_eq ?_).trans
    ((gaugeLinearAction_ae_eq u (coeFn_gaugeLp v f)).symm.trans (coeFn_gaugeLp u _).symm)
  rw [ContinuousMap.coe_mul, gaugeLinearAction_mul]

/-- The gauge action of the inverse gauge undoes the gauge action. -/
@[simp]
theorem gaugeLp_gaugeLp_inv (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLp μ u (gaugeLp μ u⁻¹ f) = f :=
  (gaugeLp μ u).apply_symm_apply f

/-- The gauge action of the gauge undoes the gauge action of the inverse gauge. -/
@[simp]
theorem gaugeLp_inv_gaugeLp (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLp μ u⁻¹ (gaugeLp μ u f) = f :=
  (gaugeLp μ u).symm_apply_apply f

end Lp

/-! ### Gauge covariance of weak solutions -/

section WeakSolution

variable {μ : Measure ℂ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- Pairing `u·f` with a field `η` is pairing `f` with `u⁻¹·η`. -/
theorem integral_inner_gaugeLp (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    ∫ z, ⟪gaugeLp μ u f z, η z⟫ ∂μ = ∫ z, ⟪f z, gaugeLinearAction u⁻¹ η z⟫ ∂μ := by
  refine integral_congr_ae ((coeFn_gaugeLp u f).mono fun z hz ↦ ?_)
  dsimp only
  rw [hz, ← inner_gaugeLinearAction u f (gaugeLinearAction u⁻¹ η),
    gaugeLinearAction_gaugeLinearAction_inv]

/-- **Gauge covariance of the weak pairing.** Testing `u·y` against `L_{u·x}* η` is testing `y`
against `L_x* (u⁻¹·η)`. Only the gauge and the test field are differentiated; the field `x` is
arbitrary. -/
theorem integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) :
    ∫ z, ⟪gaugeLp μ u y z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x (gaugeLinearAction u⁻¹ η) z⟫ ∂μ := by
  have hη' : ContDiff ℝ 1 (gaugeLinearAction u⁻¹ η) :=
    contDiff_gaugeLinearAction (Circle.contDiff_coe_inv hu) hη
  refine integral_congr_ae ((coeFn_gaugeLp u y).mono fun z hz ↦ ?_)
  have hi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ gaugeLinearAction u⁻¹ η w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z
      (hη'.differentiable one_ne_zero z) :)
  have h := gaugeFixedAdjoint_gaugeTransform (hu.differentiable one_ne_zero z) x (hi 2) (hi 3)
  rw [gaugeLinearAction_gaugeLinearAction_inv] at h
  simp only [hz, h, inner_gaugeLinearAction]

/-- **Gauge transport of weak equations**, for test fields of any smoothness `n ≥ 1`. For a `Cⁿ`
gauge `u`, `∫ ⟪u·y, L_{u·x}* η⟫ = ∫ ⟪u·f, η⟫` holds for every compactly supported `Cⁿ` test field
`η` exactly when `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` does: the test field `η` is traded for `u⁻¹·η`, which
is again a compactly supported `Cⁿ` test field, and conversely. -/
theorem forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff {n : WithTop ℕ∞}
    (hn : 1 ≤ n) {u : C(ℂ, Circle)} (hu : ContDiff ℝ n (fun z ↦ (u z : ℂ)))
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ n η → HasCompactSupport η →
        ∫ z, ⟪gaugeLp μ u y z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ =
          ∫ z, ⟪gaugeLp μ u f z, η z⟫ ∂μ) ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ n η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ := by
  have hu₁ := hu.of_le hn
  refine ⟨fun h η hη hηc ↦ ?_, fun h η hη hηc ↦ ?_⟩
  · -- Test `u·y` against `u·η`.
    have h' := h _ (contDiff_gaugeLinearAction hu hη) (hasCompactSupport_gaugeLinearAction _ hηc)
    rwa [integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform hu₁ x y
      (contDiff_gaugeLinearAction hu₁ (hη.of_le hn)), integral_inner_gaugeLp,
      gaugeLinearAction_inv_gaugeLinearAction] at h'
  · rw [integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform hu₁ x y (hη.of_le hn),
      integral_inner_gaugeLp]
    exact h _ (contDiff_gaugeLinearAction (Circle.contDiff_coe_inv hu) hη)
      (hasCompactSupport_gaugeLinearAction _ hηc)

/-- **Gauge covariance of weak solutions.** For a `C²` gauge `u`, `u·y` is a weak solution of
`L_{u·x} (u·y) = u·f` exactly when `y` is a weak solution of `L_x y = f`. -/
theorem isGaugeFixedWeakSolution_gaugeLp_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) ↔
      IsGaugeFixedWeakSolution μ x f y := by
  rw [isGaugeFixedWeakSolution_iff, isGaugeFixedWeakSolution_iff]
  exact forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff one_le_two hu x f y

/-- The gauge action on weak solutions: if `y` is a weak solution of `L_x y = f`, then `u·y` is
a weak solution of `L_{u·x} (u·y) = u·f`, for a `C²` gauge `u`. -/
theorem IsGaugeFixedWeakSolution.gaugeLp {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsGaugeFixedWeakSolution μ x f y) :
    IsGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) :=
  (isGaugeFixedWeakSolution_gaugeLp_iff hu).2 h

/-- **Gauge covariance of minimal weak solutions.** For a `C²` gauge `u`, `u·y` is a minimal weak
solution of `L_{u·x} (u·y) = u·f` exactly when `y` is a minimal weak solution of `L_x y = f`. -/
theorem isMinimalGaugeFixedWeakSolution_gaugeLp_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) ↔
      IsMinimalGaugeFixedWeakSolution μ x f y := by
  rw [isMinimalGaugeFixedWeakSolution_iff, isMinimalGaugeFixedWeakSolution_iff]
  refine and_congr (isGaugeFixedWeakSolution_gaugeLp_iff hu) ?_
  -- The weak solutions of `L_{u·x} w = 0` are the images of those of `L_x w = 0`.
  have hker (w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) := isGaugeFixedWeakSolution_gaugeLp_iff
    (x := x) hu (f := 0) (y := w)
  simp only [map_zero] at hker
  have hpair (w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
      ∫ z, ⟪gaugeLp μ u y z, gaugeLp μ u w z⟫ ∂μ = ∫ z, ⟪y z, w z⟫ ∂μ := by
    rw [← L2.inner_def, ← L2.inner_def, LinearIsometryEquiv.inner_map_map]
  refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · rw [← hpair]
    exact h _ ((hker w).2 hw)
  · rw [← (gaugeLp μ u).apply_symm_apply w, hpair]
    refine h _ ((hker _).1 ?_)
    rwa [LinearIsometryEquiv.apply_symm_apply]

/-- The gauge action on minimal weak solutions. -/
theorem IsMinimalGaugeFixedWeakSolution.gaugeLp {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsMinimalGaugeFixedWeakSolution μ x f y) :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) :=
  (isMinimalGaugeFixedWeakSolution_gaugeLp_iff hu).2 h

/-- **Weak right inverses of gauge-equivalent fields.** If `Q f` is a minimal weak solution of
`L_x y = f` for every `f`, then `u·Q(u⁻¹·f)` is a minimal weak solution of `L_{u·x} y = f`, for
a `C²` gauge `u`. So a weak right inverse at `x` gives one at every gauge transform of `x`. -/
theorem isMinimalGaugeFixedWeakSolution_gaugeLp_apply_symm {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ)))
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) f
      (gaugeLp μ u (Q ((gaugeLp μ u).symm f))) := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using (hQ ((gaugeLp μ u).symm f)).gaugeLp hu

/-- **Gauge covariance of the weak right inverse.** Let `x` be a continuous field and `u` a `C²`
gauge. If `Q f` is a minimal weak solution of `L_x y = f` and `Q' f` one of `L_{u·x} y = f` for
every `f`, as for the weak right inverses of
`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`, then
`Q' (u·f) = u·(Q f)`. -/
theorem apply_gaugeLp_eq_gaugeLp_apply [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ)))
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (hQ' : ∀ f, IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) f (Q' f))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    Q' (gaugeLp μ u f) = gaugeLp μ u (Q f) :=
  (hQ' _).unique (continuous_gaugeTransform (hu.of_le one_le_two) hx) ((hQ f).gaugeLp hu)

end WeakSolution

/-! ### The weak kernel -/

section WeakKernel

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Gauge covariance of the weak kernel**, elementwise. For a `C¹` gauge `u` and a continuous
field `x`, `u·w` lies in the weak `L²` kernel of `L_{u·x}` exactly when `w` lies in that of
`L_x`. -/
theorem gaugeLp_mem_weakGaugeFixedKernel_gaugeTransform_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (hx : Continuous x)
    {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    gaugeLp volume u w ∈ weakGaugeFixedKernel (gaugeTransform u x) ↔
      w ∈ weakGaugeFixedKernel x := by
  rw [mem_weakGaugeFixedKernel_iff_contDiff_one (continuous_gaugeTransform hu hx),
    mem_weakGaugeFixedKernel_iff_contDiff_one hx]
  simpa only [map_zero, Lp.integral_inner_coeFn_zero_left] using
    forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff le_rfl hu x 0 w

/-- **Gauge covariance of the weak kernel.** For a `C¹` gauge `u` and a continuous field `x`,
the weak `L²` kernel of `L_{u·x}` is the image under the gauge of the weak kernel of `L_x`. -/
theorem weakGaugeFixedKernel_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (hx : Continuous x) :
    weakGaugeFixedKernel (gaugeTransform u x) =
      (weakGaugeFixedKernel x).map ((gaugeLp volume u).toLinearEquiv :
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) := by
  ext w
  rw [Submodule.mem_map_equiv, ← gaugeLp_mem_weakGaugeFixedKernel_gaugeTransform_iff hu hx]
  simp

/-- **The kernel projections are conjugate.** For a `C¹` gauge `u` and a continuous field `x`,
the orthogonal projection of `L²(ℂ; ℝ⁴)` onto the weak kernel of `L_{u·x}` is the conjugate by
the gauge of the orthogonal projection onto the weak kernel of `L_x`. -/
theorem starProjection_weakGaugeFixedKernel_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (hx : Continuous x)
    (w : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
    (weakGaugeFixedKernel (gaugeTransform u x)).starProjection (gaugeLp volume u w) =
      gaugeLp volume u ((weakGaugeFixedKernel x).starProjection w) := by
  simp_rw [weakGaugeFixedKernel_gaugeTransform hu hx]
  rw [Submodule.starProjection_map_apply, LinearIsometryEquiv.symm_apply_apply]

/-- For a `C¹` gauge `u` and a continuous field `x`, the weak kernels of `L_{u·x}` and `L_x`
have the same dimension. -/
theorem finrank_weakGaugeFixedKernel_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (hx : Continuous x) :
    Module.finrank ℝ (weakGaugeFixedKernel (gaugeTransform u x)) =
      Module.finrank ℝ (weakGaugeFixedKernel x) := by
  rw [weakGaugeFixedKernel_gaugeTransform hu hx, LinearEquiv.finrank_map_eq]

end WeakKernel

end TauCeti.Vortex
