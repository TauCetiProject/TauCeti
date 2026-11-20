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

**Weak solutions.** A square-integrable field `y` is a *weak solution* of `L_x y = f` if
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` test field `η`
(`TauCeti.Vortex.IsGaugeFixedWeakSolution`), and it is *minimal* if moreover it is orthogonal to
every weak solution of `L_x w = 0` (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution`). These are
the two properties of the values `Q f` of the weak right inverse `Q` of
`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`, which exists at
every plane vortex with `|α| → 1`.

* For a `C²` gauge, `u·y` is a (minimal) weak solution of `L_{u·x} (u·y) = u·f` exactly when `y`
  is one of `L_x y = f` (`TauCeti.Vortex.isGaugeFixedWeakSolution_gaugeLp_iff`,
  `TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_iff`). The test field `η` is traded
  for `u⁻¹·η`, which is again a compactly supported `C²` test field.
* At a continuous field the minimal weak solution is unique
  (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`): it is the weak solution of least
  `L²` norm (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.norm_le`). So the weak right
  inverse is determined by `x`, and every weak right inverse `Q'` at `u·x` is the conjugate
  `Q' = u ∘ Q ∘ u⁻¹` of every weak right inverse `Q` at `x`
  (`TauCeti.Vortex.apply_gaugeLp_eq_gaugeLp_apply`). In particular a weak right inverse at `x`
  supplies one at every gauge transform of `x`
  (`TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_apply_symm`).

**The weak kernel.** For a smooth gauge and a continuous field, the weak `L²` kernel
`TauCeti.Vortex.weakGaugeFixedKernel` of `L_{u·x}` is the image of that of `L_x` under the gauge
(`TauCeti.Vortex.weakGaugeFixedKernel_gaugeTransform`). Since the gauge is a linear isometry, the
orthogonal projections onto the two kernels are conjugate
(`TauCeti.Vortex.starProjection_weakGaugeFixedKernel_gaugeTransform`) and the kernels have the
same dimension (`TauCeti.Vortex.finrank_weakGaugeFixedKernel_gaugeTransform`).

These are the line-frame and gauge laws of the kernel projections and right inverses of the
linearized vortex operator; the corresponding laws for translations and rotations of the plane
need the action of rigid motions on `L²`, and are not treated here.

## Main definitions

* `TauCeti.Vortex.gaugeLp μ u`: the linear gauge action of a continuous gauge on `L²(ℂ; ℝ⁴)`.
* `TauCeti.Vortex.IsGaugeFixedWeakSolution μ x f y`: `y` is a weak solution of `L_x y = f`.
* `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution μ x f y`: `y` is a weak solution of
  `L_x y = f` orthogonal to the weak solutions of `L_x w = 0`.

## Main results

* `TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_iff`: gauge covariance of minimal
  weak solutions.
* `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`,
  `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.norm_le`: the minimal weak solution is unique
  and has least norm.
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

open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace ContDiff

/-! ### Regularity of the inverse gauge and of the gauge action on values -/

/-- The pointwise inverse of a `Cⁿ` circle-valued map, as a map into `ℂ`, is `Cⁿ`. -/
private theorem contDiff_coe_inv {n : WithTop ℕ∞} {u : ℂ → Circle}
    (hu : ContDiff ℝ n (fun w ↦ (u w : ℂ))) : ContDiff ℝ n (fun w ↦ ((u⁻¹ w : Circle) : ℂ)) := by
  simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, Function.comp_def, conjCLE_apply] using
    conjCLE.contDiff.comp hu

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

/-- The linear action of a continuous gauge preserves `Lᵖ` fields. -/
theorem memLp_gaugeLinearAction {u : ℂ → Circle} (hu : Continuous u) {p : ENNReal}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y p μ) :
    MemLp (gaugeLinearAction u y) p μ := by
  have h : gaugeLinearAction u y =
      fun z ↦ gaugeLinearAction (fun _ ↦ (u z, y z).1) (fun _ ↦ (u z, y z).2) 0 := by
    funext z
    simp only [gaugeLinearAction_apply]
  refine hy.of_le ?_ (ae_of_all _ fun z ↦ (norm_gaugeLinearAction u y z).le)
  rw [h]
  exact continuous_gaugeLinearAction_uncurry.comp_aestronglyMeasurable
    (hu.aestronglyMeasurable.prodMk hy.aestronglyMeasurable)

/-- The value of the linear gauge action at a point only depends on the value of the variation
there, so the action respects almost everywhere equality. -/
theorem gaugeLinearAction_ae_eq (u : ℂ → Circle) {y w : ℂ → EuclideanSpace ℝ (Fin 4)}
    (h : y =ᵐ[μ] w) : gaugeLinearAction u y =ᵐ[μ] gaugeLinearAction u w :=
  h.mono fun z hz ↦ by simp only [gaugeLinearAction_apply, hz]

/-- The linear gauge action on `L²`, as a linear map. -/
private def gaugeLpₗ (μ : Measure ℂ) (u : C(ℂ, Circle)) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun f := (memLp_gaugeLinearAction u.continuous (Lp.memLp f)).toLp _
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
  (memLp_gaugeLinearAction u.continuous (Lp.memLp f)).coeFn_toLp

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
      (memLp_gaugeLinearAction u.continuous (Lp.memLp f)).aestronglyMeasurable
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
  rw [ContinuousMap.coe_one, gaugeLinearAction_one]
  rfl

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

/-! ### Weak solutions -/

section WeakSolution

variable {μ : Measure ℂ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- `y` is a **weak solution** of `L_x y = f`: `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
supported `C²` test field `η`. -/
def IsGaugeFixedWeakSolution (μ : Measure ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) : Prop :=
  ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
    ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ

/-- `y` is a **minimal weak solution** of `L_x y = f`: a weak solution which is orthogonal to
every square-integrable weak solution `w` of `L_x w = 0`. At a continuous field it is the weak
solution of least norm (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.norm_le`), and it is
unique (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`). At a plane vortex with
`|α| → 1` it is the value at `f` of a bounded weak right inverse
(`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`). -/
def IsMinimalGaugeFixedWeakSolution (μ : Measure ℂ) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) : Prop :=
  IsGaugeFixedWeakSolution μ x f y ∧
    ∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, w z⟫ ∂μ = 0

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
    contDiff_gaugeLinearAction (contDiff_coe_inv hu) hη
  refine integral_congr_ae ((coeFn_gaugeLp u y).mono fun z hz ↦ ?_)
  have hi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ gaugeLinearAction u⁻¹ η w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z
      (hη'.differentiable one_ne_zero z) :)
  have h := gaugeFixedAdjoint_gaugeTransform (hu.differentiable one_ne_zero z) x (hi 2) (hi 3)
  rw [gaugeLinearAction_gaugeLinearAction_inv] at h
  simp only [hz, h, inner_gaugeLinearAction]

/-- The inverse action on test fields: `u⁻¹·η` is a compactly supported `C²` test field when `η`
is and `u` is `C²`. -/
private theorem contDiff_gaugeLinearAction_inv {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) : ContDiff ℝ 2 (gaugeLinearAction u⁻¹ η) :=
  contDiff_gaugeLinearAction (contDiff_coe_inv hu) hη

/-- The gauge action on weak solutions: if `y` is a weak solution of `L_x y = f`, then `u·y` is
a weak solution of `L_{u·x} (u·y) = u·f`, for a `C²` gauge `u`. -/
theorem IsGaugeFixedWeakSolution.gaugeLp {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsGaugeFixedWeakSolution μ x f y) :
    IsGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) := by
  intro η hη hηc
  rw [integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform (hu.of_le one_le_two) x y
    (hη.of_le one_le_two), h _ (contDiff_gaugeLinearAction_inv hu hη)
    (hasCompactSupport_gaugeLinearAction _ hηc)]
  refine integral_congr_ae ((coeFn_gaugeLp u f).mono fun z hz ↦ ?_)
  dsimp only
  rw [hz, ← inner_gaugeLinearAction u, gaugeLinearAction_gaugeLinearAction_inv]

/-- A `C²` gauge transformation applied twice, by `u` and then by `u⁻¹`, is the identity on
fields. -/
private theorem gaugeTransform_inv_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform ⇑u⁻¹ (gaugeTransform u x) = x := by
  rw [← gaugeTransform_mul (by simpa using (contDiff_coe_inv hu).differentiable one_ne_zero)
    (hu.differentiable one_ne_zero), ContinuousMap.coe_inv, inv_mul_cancel, gaugeTransform_one]

/-- **Gauge covariance of weak solutions.** For a `C²` gauge `u`, `u·y` is a weak solution of
`L_{u·x} (u·y) = u·f` exactly when `y` is a weak solution of `L_x y = f`. -/
theorem isGaugeFixedWeakSolution_gaugeLp_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) ↔
      IsGaugeFixedWeakSolution μ x f y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.gaugeLp hu⟩
  have hu' : ContDiff ℝ 2 (fun z ↦ (u⁻¹ z : ℂ)) := by
    simpa using contDiff_coe_inv hu
  simpa only [gaugeLp_inv_gaugeLp, gaugeTransform_inv_gaugeTransform (hu.of_le one_le_two)] using
    h.gaugeLp hu'

/-- The weak solutions of `L_{u·x} w = 0` are the images under the gauge of those of
`L_x w = 0`. -/
private theorem forall_integral_inner_gaugeLp_eq_zero_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪gaugeLp μ u w z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ = 0) ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
  have h0 (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
      ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) z, η z⟫ ∂μ = 0 := by
    rw [integral_congr_ae ((Lp.coeFn_zero _ 2 μ).mono fun z hz ↦ by rw [hz, Pi.zero_apply,
      inner_zero_left]), integral_zero]
  have h := isGaugeFixedWeakSolution_gaugeLp_iff (x := x) hu (f := 0) (y := w)
  simp only [IsGaugeFixedWeakSolution, map_zero, h0] at h
  exact h

/-- **Gauge covariance of minimal weak solutions.** For a `C²` gauge `u`, `u·y` is a minimal weak
solution of `L_{u·x} (u·y) = u·f` exactly when `y` is a minimal weak solution of `L_x y = f`. -/
theorem isMinimalGaugeFixedWeakSolution_gaugeLp_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) ↔
      IsMinimalGaugeFixedWeakSolution μ x f y := by
  refine and_congr (isGaugeFixedWeakSolution_gaugeLp_iff hu) ?_
  -- Every weak solution of `L_{u·x} w = 0` is `u·w'` for a weak solution `w'` of `L_x w' = 0`.
  have hpair (w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
      ∫ z, ⟪gaugeLp μ u y z, gaugeLp μ u w z⟫ ∂μ = ∫ z, ⟪y z, w z⟫ ∂μ := by
    rw [← L2.inner_def, ← L2.inner_def, LinearIsometryEquiv.inner_map_map]
  refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · rw [← hpair]
    exact h _ ((forall_integral_inner_gaugeLp_eq_zero_iff hu).2 hw)
  · rw [← (gaugeLp μ u).apply_symm_apply w, hpair]
    refine h _ ((forall_integral_inner_gaugeLp_eq_zero_iff hu).1 ?_)
    rwa [LinearIsometryEquiv.apply_symm_apply]

/-- The gauge action on minimal weak solutions. -/
theorem IsMinimalGaugeFixedWeakSolution.gaugeLp {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ))) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsMinimalGaugeFixedWeakSolution μ x f y) :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) :=
  (isMinimalGaugeFixedWeakSolution_gaugeLp_iff hu).2 h

/-- At a continuous field, testing against `L_x* η` is the `L²` pairing with its `L²` class, so
it is linear in the tested field. -/
private theorem integral_inner_sub_gaugeFixedAdjoint [IsFiniteMeasureOnCompacts μ]
    (hx : Continuous x)
    (y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪(y - y') z, gaugeFixedAdjoint x η z⟫ ∂μ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ - ∫ z, ⟪y' z, gaugeFixedAdjoint x η z⟫ ∂μ := by
  have hm : MemLp (gaugeFixedAdjoint x η) 2 μ :=
    (continuous_gaugeFixedAdjoint hx (hη.of_le one_le_two)).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  rw [← L2.inner_toLp _ hm, ← L2.inner_toLp _ hm, ← L2.inner_toLp _ hm, inner_sub_left]

/-- At a continuous field, the difference of two weak solutions of `L_x y = f` is a weak
solution of `L_x w = 0`. -/
private theorem IsGaugeFixedWeakSolution.integral_inner_sub_eq_zero [IsFiniteMeasureOnCompacts μ]
    (hx : Continuous x)
    {f y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsGaugeFixedWeakSolution μ x f y)
    (h' : IsGaugeFixedWeakSolution μ x f y') (η : ℂ → EuclideanSpace ℝ (Fin 4))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪(y' - y) z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
  rw [integral_inner_sub_gaugeFixedAdjoint hx _ _ hη hηc, h η hη hηc, h' η hη hηc, sub_self]

/-- **The minimal weak solution has least norm.** At a continuous field, a minimal weak solution
`y` of `L_x y = f` has norm at most that of every weak solution `y'`: indeed
`‖y'‖² = ‖y‖² + ‖y' - y‖²`, since `y' - y` is a weak solution of `L_x w = 0`. -/
theorem IsMinimalGaugeFixedWeakSolution.norm_le [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {f y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (h' : IsGaugeFixedWeakSolution μ x f y') : ‖y‖ ≤ ‖y'‖ := by
  have horth : ⟪y, y' - y⟫ = 0 := by
    rw [L2.inner_def]
    exact h.2 _ (h.1.integral_inner_sub_eq_zero hx h')
  have hsq : ‖y'‖ ^ 2 = ‖y‖ ^ 2 + ‖y' - y‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ) y (y' - y) horth
    rw [add_sub_cancel] at this
    rw [sq, sq, sq, this]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [hsq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **The minimal weak solution is unique.** At a continuous field, two minimal weak solutions of
`L_x y = f` coincide. -/
theorem IsMinimalGaugeFixedWeakSolution.unique [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {f y y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (h' : IsMinimalGaugeFixedWeakSolution μ x f y') : y = y' := by
  have hw := h.1.integral_inner_sub_eq_zero hx h'.1
  have h₁ : ⟪y, y' - y⟫ = 0 := by
    rw [L2.inner_def]
    exact h.2 _ hw
  have h₂ : ⟪y', y' - y⟫ = 0 := by
    rw [L2.inner_def]
    exact h'.2 _ hw
  have : ‖y' - y‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, h₁, h₂, sub_self]
  exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))).symm

/-- **Weak right inverse at a plane vortex.** Let `x` be a `C¹` solution of the plane vortex
equation with `|α| → 1` at infinity. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` such
that `Q f` is a minimal weak solution of `L_x y = f` for every `f`. By
`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`, `Q` is the only such map. -/
theorem exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution [μ.IsAddHaarMeasure]
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f) := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ)
    hx hsol hlim
  exact ⟨Q, fun f ↦ ⟨hQ f, hQK f⟩⟩

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
`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`, then
`Q' (u·f) = u·(Q f)`. -/
theorem apply_gaugeLp_eq_gaugeLp_apply [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 (fun z ↦ (u z : ℂ)))
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (hQ' : ∀ f, IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) f (Q' f))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    Q' (gaugeLp μ u f) = gaugeLp μ u (Q f) :=
  (hQ' _).unique (contDiff_gaugeTransform (n := 0) (hu.of_le (by norm_num))
    (contDiff_zero.2 hx)).continuous ((hQ f).gaugeLp hu)

end WeakSolution

/-! ### The weak kernel -/

section WeakKernel

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Gauge covariance of the weak kernel**, elementwise. For a smooth gauge `u` and a continuous
field `x`, `u·w` lies in the weak `L²` kernel of `L_{u·x}` exactly when `w` lies in that of
`L_x`. -/
theorem gaugeLp_mem_weakGaugeFixedKernel_gaugeTransform_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) (hx : Continuous x)
    {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    gaugeLp volume u w ∈ weakGaugeFixedKernel (gaugeTransform u x) ↔
      w ∈ weakGaugeFixedKernel x := by
  have hux : Continuous (gaugeTransform u x) :=
    (contDiff_gaugeTransform (n := 0) (hu.of_le (by simp)) (contDiff_zero.2 hx)).continuous
  have hu' : ContDiff ℝ ∞ (fun z ↦ (u⁻¹ z : ℂ)) := by
    simpa using contDiff_coe_inv hu
  rw [mem_weakGaugeFixedKernel_iff hux, mem_weakGaugeFixedKernel_iff hx]
  refine ⟨fun h η hη hηc ↦ ?_, fun h η hη hηc ↦ ?_⟩
  · -- Test `u·w` against `u·η`.
    have h' := h _ (contDiff_gaugeLinearAction (by simpa using hu) hη)
      (hasCompactSupport_gaugeLinearAction _ hηc)
    rwa [integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform (hu.of_le (by simp)) x w
      (contDiff_gaugeLinearAction (hu.of_le (by simp)) (hη.of_le (by simp))),
      gaugeLinearAction_inv_gaugeLinearAction] at h'
  · rw [integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform (hu.of_le (by simp)) x w
      (hη.of_le (by simp))]
    exact h _ (contDiff_gaugeLinearAction hu' hη) (hasCompactSupport_gaugeLinearAction _ hηc)

/-- **Gauge covariance of the weak kernel.** For a smooth gauge `u` and a continuous field `x`,
the weak `L²` kernel of `L_{u·x}` is the image under the gauge of the weak kernel of `L_x`. -/
theorem weakGaugeFixedKernel_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) (hx : Continuous x) :
    weakGaugeFixedKernel (gaugeTransform u x) =
      (weakGaugeFixedKernel x).map ((gaugeLp volume u).toLinearEquiv :
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) := by
  ext w
  rw [Submodule.mem_map_equiv, ← gaugeLp_mem_weakGaugeFixedKernel_gaugeTransform_iff hu hx]
  simp

/-- **The kernel projections are conjugate.** For a smooth gauge `u` and a continuous field `x`,
the orthogonal projection of `L²(ℂ; ℝ⁴)` onto the weak kernel of `L_{u·x}` is the conjugate by
the gauge of the orthogonal projection onto the weak kernel of `L_x`. -/
theorem starProjection_weakGaugeFixedKernel_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) (hx : Continuous x)
    (w : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
    (weakGaugeFixedKernel (gaugeTransform u x)).starProjection (gaugeLp volume u w) =
      gaugeLp volume u ((weakGaugeFixedKernel x).starProjection w) := by
  simp_rw [weakGaugeFixedKernel_gaugeTransform hu hx]
  rw [Submodule.starProjection_map_apply, LinearIsometryEquiv.symm_apply_apply]

/-- For a smooth gauge `u` and a continuous field `x`, the weak kernels of `L_{u·x}` and `L_x`
have the same dimension. -/
theorem finrank_weakGaugeFixedKernel_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) (hx : Continuous x) :
    Module.finrank ℝ (weakGaugeFixedKernel (gaugeTransform u x)) =
      Module.finrank ℝ (weakGaugeFixedKernel x) := by
  rw [weakGaugeFixedKernel_gaugeTransform hu hx, LinearEquiv.finrank_map_eq]

end WeakKernel

end TauCeti.Vortex
