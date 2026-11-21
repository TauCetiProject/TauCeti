/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Linearization
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Complex.Circle

/-!
# Gauge covariance of the weak kernel and the weak right inverse of the vortex operator

A charge-one gauge `u : ℂ → U(1)` acts on plane-vortex fields by `gaugeTransform u`, and its
linear part `gaugeLinearAction u` fixes the connection variation and the two real rows of the
target and multiplies the section variation and the complex row by `u`. The gauge-fixed operator
`L_x = d₀* ⊕ d₁` and its formal adjoint are covariant under this action at every field
(`TauCeti.Vortex.gaugeFixedOperator_gaugeTransform`,
`TauCeti.Vortex.gaugeFixedAdjoint_gaugeTransform`). This file carries that covariance to the weak
`L²` theory of `L_x`: its weak kernel, the orthogonal projection onto it, its weak solutions and
its weak right inverse orthogonal to the kernel. These are the objects whose dependence on the
vortex enters the deformation theory over the moduli space, and covariance says that they are
compatible with the gauge action defining that space. A constant gauge `u ≡ c` is a change of the
line frame, so these are in particular the line-frame laws.

* **The `L²` gauge action.** At a single value the linear action is the linear isometry
  `TauCeti.Vortex.gaugeFrame c` of `ℝ⁴` rotating the last two coordinates by `c ∈ U(1)`
  (`TauCeti.Vortex.gaugeLinearAction_apply_eq_gaugeFrame`). So a continuous gauge `u` acts on
  `L²(ℂ; ℝ⁴)` by the linear isometry equivalence `TauCeti.Vortex.gaugeLp μ u`, multiplication by
  the bounded continuous symbol `z ↦ gaugeFrame (u z)` (`BoundedContinuousFunction.mulLp`). It
  acts almost everywhere as `gaugeLinearAction u` (`TauCeti.Vortex.coeFn_gaugeLp`), and
  `u ↦ gaugeLp μ u` respects the group structure (`TauCeti.Vortex.gaugeLp_one`,
  `TauCeti.Vortex.gaugeLp_mul`, `TauCeti.Vortex.gaugeLp_symm`).
* **The weak kernel.** For a smooth gauge, the weak kernel at `u · x` is the image of the weak
  kernel at `x` (`TauCeti.Vortex.weakGaugeFixedKernel_gaugeTransform`), at every field `x`, so
  the two have the same dimension
  (`TauCeti.Vortex.finrank_weakGaugeFixedKernel_gaugeTransform`) and the orthogonal projections
  onto them are conjugate
  (`TauCeti.Vortex.starProjection_weakGaugeFixedKernel_gaugeTransform_apply`).
* **Weak solutions.** For a `C²` gauge, `y` is a weak solution of `L_x y = f` exactly when
  `u y` is a weak solution of `L_{u · x} (u y) = u f`
  (`TauCeti.Vortex.forall_integral_inner_gaugeFixedAdjoint_gaugeTransform_eq_iff`), and `y` is
  orthogonal to the weak kernel of `L_x` exactly when `u y` is orthogonal to the weak kernel of
  `L_{u · x}` (`TauCeti.Vortex.forall_integral_inner_gaugeLp_eq_zero_iff_of_gaugeFixedAdjoint`).
  Here the weak notions are those of `TauCeti.Analysis.PDE.Vortex.RightInverse`, with compactly
  supported `C²` test fields.
* **The weak right inverse.** A weak solution orthogonal to the weak kernel is unique
  (`TauCeti.Vortex.eq_of_integral_inner_gaugeFixedAdjoint_eq`), so bounded weak right inverses
  with values orthogonal to the weak kernels at `x` and at `u · x`, which exist at a plane vortex
  with `|α| → 1`
  (`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`), are
  conjugate by the `L²` gauge action (`TauCeti.Vortex.eq_gaugeLp_comp_comp_symm`). By the two
  previous laws, the conjugate of such a right inverse at `x` is one at `u · x`.

The statements hold at arbitrary fields `x` (continuous for the right inverse), with no vortex
equation, decay or framing assumption on the field or the gauge: they are consequences of the
pointwise covariance and of `|u| = 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Complex
open scoped RealInnerProductSpace ContDiff BoundedContinuousFunction

/-! ### The gauge action on `L²` -/

/-- The bounded continuous symbol `z ↦ gaugeFrame (u z)` of a continuous gauge. -/
private def gaugeSymbol (u : C(ℂ, Circle)) :
    ℂ →ᵇ (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :=
  .ofNormedAddCommGroup (fun z ↦ (gaugeFrame (u z) : _ →L[ℝ] _))
    (continuous_gaugeFrame.comp u.continuous) 1 fun z ↦
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by simp

variable {μ : Measure ℂ} [μ.InnerRegularCompactLTTop]

variable (μ) in
/-- Multiplication by the gauge symbol, as a homomorphism into the unitary operators on `L²`. -/
private def gaugeUnitary : C(ℂ, Circle) →*
    unitary (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) where
  toFun u := ⟨(gaugeSymbol u).mulLp μ 2 ENNReal.ofNat_ne_top,
    BoundedContinuousFunction.mulLp_mem_unitary fun z ↦
      (Unitary.linearIsometryEquiv.symm (gaugeFrame (u z))).prop⟩
  map_one' := Subtype.ext <| by
    rw [OneMemClass.coe_one, ← BoundedContinuousFunction.mulLp_one]
    exact congr_arg _ <| BoundedContinuousFunction.ext fun z ↦ ContinuousLinearMap.ext fun v ↦ by
      simp [gaugeSymbol]
  map_mul' u v := Subtype.ext <| by
    rw [MulMemClass.coe_mul, ← BoundedContinuousFunction.mulLp_mul]
    exact congr_arg _ <| BoundedContinuousFunction.ext fun z ↦ ContinuousLinearMap.ext fun w ↦ by
      simp [gaugeSymbol, gaugeFrame_mul]

variable (μ) in
/-- The **gauge action on `L²(ℂ; ℝ⁴)`** of a continuous gauge `u : ℂ → U(1)`: the linear isometry
equivalence acting pointwise by the gauge frame of `u`, almost everywhere equal to the linear gauge
action `gaugeLinearAction u` (`coeFn_gaugeLp`). It is multiplication by the bounded continuous
symbol `z ↦ gaugeFrame (u z)` (`BoundedContinuousFunction.mulLp`), a unitary operator
(`BoundedContinuousFunction.mulLp_mem_unitary`). -/
def gaugeLp (u : C(ℂ, Circle)) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ ≃ₗᵢ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ :=
  Unitary.linearIsometryEquiv (gaugeUnitary μ u)

/-- The `L²` gauge action is the linear gauge action almost everywhere. -/
theorem coeFn_gaugeLp (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLp μ u f =ᵐ[μ] gaugeLinearAction u f :=
  ((gaugeSymbol u).coeFn_mulLp _ f).mono fun _ hz ↦
    hz.trans (gaugeLinearAction_apply_eq_gaugeFrame _ _ _).symm

/-- An `L²` field is the gauge action of `u` on `f` exactly when it agrees almost everywhere with
`gaugeLinearAction u f`. -/
theorem gaugeLp_eq_iff {u : C(ℂ, Circle)} {f g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    gaugeLp μ u f = g ↔ gaugeLinearAction u f =ᵐ[μ] g :=
  (gaugeSymbol u).mulLp_eq_iff.trans <| by
    rw [show (fun z ↦ gaugeSymbol u z (f z)) = gaugeLinearAction u f from
      funext fun z ↦ (gaugeLinearAction_apply_eq_gaugeFrame _ _ _).symm]

/-- The trivial gauge acts trivially on `L²`. -/
@[simp]
theorem gaugeLp_one : gaugeLp μ 1 = LinearIsometryEquiv.refl ℝ _ := by
  rw [gaugeLp, map_one, map_one, LinearIsometryEquiv.one_def]

/-- The `L²` gauge actions compose as the gauges multiply. -/
theorem gaugeLp_mul (u v : C(ℂ, Circle)) :
    gaugeLp μ (u * v) = (gaugeLp μ v).trans (gaugeLp μ u) := by
  rw [gaugeLp, gaugeLp, gaugeLp, map_mul, map_mul, LinearIsometryEquiv.mul_def]

/-- The inverse of the `L²` gauge action of `u` is the `L²` gauge action of `u⁻¹`. -/
@[simp]
theorem gaugeLp_symm (u : C(ℂ, Circle)) : (gaugeLp μ u).symm = gaugeLp μ u⁻¹ := by
  rw [gaugeLp, gaugeLp, map_inv, map_inv, LinearIsometryEquiv.inv_def]

/-! ### The weak kernel -/

/-- At a `C¹` gauge `u` and a `C¹` field `η`, the formal adjoint at `u · x` on `u η` is the linear
gauge action of the formal adjoint at `x` on `η`. -/
private theorem gaugeFixedAdjoint_gaugeTransform_of_contDiff {u : ℂ → Circle}
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) (z : ℂ) :
    gaugeFixedAdjoint (gaugeTransform u x) (gaugeLinearAction u η) z =
      gaugeLinearAction u (gaugeFixedAdjoint x η) z :=
  gaugeFixedAdjoint_gaugeTransform (hu.differentiable one_ne_zero z) x
    (((contDiff_piLp _).1 hη 2).differentiable one_ne_zero z)
    (((contDiff_piLp _).1 hη 3).differentiable one_ne_zero z)

/-- At a `C¹` gauge `u`, the formal adjoint at `u · x` on a `C¹` field `η` is the linear gauge
action of the formal adjoint at `x` on `u⁻¹ η`. -/
private theorem gaugeFixedAdjoint_gaugeTransform_eq {u : ℂ → Circle}
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) (z : ℂ) :
    gaugeFixedAdjoint (gaugeTransform u x) η z =
      gaugeLinearAction u (gaugeFixedAdjoint x (gaugeLinearAction u⁻¹ η)) z := by
  have h := gaugeFixedAdjoint_gaugeTransform_of_contDiff hu x
    (contDiff_gaugeLinearAction (Circle.contDiff_coe_inv hu) hη) z
  rwa [gaugeLinearAction_gaugeLinearAction_inv] at h

/-- **The weak kernel is gauge covariant.** For a smooth gauge `u`, the weak `L²` kernel of the
gauge-fixed operator at `u · x` is the image of the weak kernel at `x` under the `L²` gauge action
of `u`. This holds at every field `x`. -/
theorem weakGaugeFixedKernel_gaugeTransform (u : C(ℂ, Circle))
    (hu : ContDiff ℝ ∞ fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    weakGaugeFixedKernel (gaugeTransform u x) =
      (weakGaugeFixedKernel x).map
        ((gaugeLp volume u).toLinearEquiv :
          Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) := by
  rw [weakGaugeFixedKernel_def, weakGaugeFixedKernel_def, Submodule.map_orthogonal_equiv,
    Submodule.map_span]
  congr 2
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_image, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  constructor
  · -- A test field `η` at `u · x` comes from the test field `u⁻¹ η` at `x`.
    rintro ⟨η, hη, hηc, hg⟩
    refine ⟨(gaugeLp volume u).symm g, ⟨gaugeLinearAction (⇑u)⁻¹ η,
      contDiff_gaugeLinearAction (Circle.contDiff_coe_inv hu) hη,
      hasCompactSupport_gaugeLinearAction _ hηc, ?_⟩, LinearIsometryEquiv.apply_symm_apply _ _⟩
    rw [gaugeLp_symm]
    filter_upwards [coeFn_gaugeLp u⁻¹ g, hg] with z h₁ h₂
    rw [h₁, gaugeLinearAction_apply_eq_gaugeFrame, h₂,
      gaugeFixedAdjoint_gaugeTransform_eq (hu.of_le (by simp)) x (hη.of_le (by simp)),
      gaugeLinearAction_apply_eq_gaugeFrame, ContinuousMap.inv_apply, ← gaugeFrame_symm,
      LinearIsometryEquiv.symm_apply_apply]
  · -- A test field `η` at `x` gives the test field `u η` at `u · x`.
    rintro ⟨g, ⟨η, hη, hηc, hg⟩, rfl⟩
    refine ⟨gaugeLinearAction u η, contDiff_gaugeLinearAction hu hη,
      hasCompactSupport_gaugeLinearAction _ hηc, ?_⟩
    have hη₁ : ContDiff ℝ 1 η := hη.of_le (by simp)
    filter_upwards [coeFn_gaugeLp u g, hg] with z h₁ h₂
    rw [h₁, gaugeFixedAdjoint_gaugeTransform_of_contDiff (hu.of_le (by simp)) x hη₁,
      gaugeLinearAction_apply_eq_gaugeFrame, gaugeLinearAction_apply_eq_gaugeFrame, h₂]

/-- Gauge-equivalent fields have weak kernels of the same dimension. -/
theorem finrank_weakGaugeFixedKernel_gaugeTransform (u : C(ℂ, Circle))
    (hu : ContDiff ℝ ∞ fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Module.finrank ℝ (weakGaugeFixedKernel (gaugeTransform u x)) =
      Module.finrank ℝ (weakGaugeFixedKernel x) := by
  rw [weakGaugeFixedKernel_gaugeTransform u hu x, LinearEquiv.finrank_map_eq]

/-- **The kernel projection is gauge covariant.** For a smooth gauge `u`, the orthogonal projection
onto the weak kernel at `u · x` is the conjugate of the orthogonal projection onto the weak kernel
at `x` by the `L²` gauge action of `u`. -/
theorem starProjection_weakGaugeFixedKernel_gaugeTransform_apply (u : C(ℂ, Circle))
    (hu : ContDiff ℝ ∞ fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) :
    (weakGaugeFixedKernel (gaugeTransform u x)).starProjection f =
      gaugeLp volume u ((weakGaugeFixedKernel x).starProjection ((gaugeLp volume u).symm f)) := by
  -- Transport along the equality of submodules; the projection instances are propositions.
  have key : ∀ (K : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 volume))
      [K.HasOrthogonalProjection], K = (weakGaugeFixedKernel x).map
        ((gaugeLp volume u).toLinearEquiv :
          Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) →
      K.starProjection f =
        gaugeLp volume u ((weakGaugeFixedKernel x).starProjection ((gaugeLp volume u).symm f)) := by
    rintro K _ rfl
    exact Submodule.starProjection_map_apply _ _ _
  exact key _ (weakGaugeFixedKernel_gaugeTransform u hu x)

/-! ### Weak solutions and the weak right inverse -/

private theorem integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) :
    ∫ z, ⟪gaugeLp μ u y z, gaugeFixedAdjoint (gaugeTransform u x) (gaugeLinearAction u η) z⟫ ∂μ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ := by
  refine integral_congr_ae ((coeFn_gaugeLp u y).mono fun z hz ↦ ?_)
  dsimp only
  rw [hz, gaugeFixedAdjoint_gaugeTransform_of_contDiff hu x hη, inner_gaugeLinearAction]

private theorem integral_inner_gaugeLp_gaugeLinearAction (u : C(ℂ, Circle))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    ∫ z, ⟪gaugeLp μ u f z, gaugeLinearAction u η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ :=
  integral_congr_ae ((coeFn_gaugeLp u f).mono fun z hz ↦ by
    dsimp only
    rw [hz, inner_gaugeLinearAction])

/-- **Weak solutions are gauge covariant.** For a `C²` gauge `u`, a square-integrable field `y` is
a weak solution of `L_x y = f` exactly when its gauge transform `u y` is a weak solution of
`L_{u · x} (u y) = u f`. Weak solutions are tested against compactly supported `C²` fields, as in
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`. -/
theorem forall_integral_inner_gaugeFixedAdjoint_gaugeTransform_eq_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪gaugeLp μ u y z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ =
        ∫ z, ⟪gaugeLp μ u f z, η z⟫ ∂μ) ↔
      ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ := by
  have hu₁ : ContDiff ℝ 1 fun z ↦ (u z : ℂ) := hu.of_le (by norm_num)
  refine ⟨fun h η hη hηc ↦ ?_, fun h η hη hηc ↦ ?_⟩
  · have := h (gaugeLinearAction u η) (contDiff_gaugeLinearAction hu hη)
      (hasCompactSupport_gaugeLinearAction _ hηc)
    rwa [integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform hu₁ x y (hη.of_le (by norm_num)),
      integral_inner_gaugeLp_gaugeLinearAction] at this
  · have hη' := contDiff_gaugeLinearAction (Circle.contDiff_coe_inv hu) hη
    have := h _ hη' (hasCompactSupport_gaugeLinearAction _ hηc)
    rwa [← integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform hu₁ x y
      (hη'.of_le (by norm_num)), ← integral_inner_gaugeLp_gaugeLinearAction u f
      (gaugeLinearAction (⇑u)⁻¹ η), gaugeLinearAction_gaugeLinearAction_inv] at this

/-- **The weak kernel condition is gauge covariant.** For a `C²` gauge `u`, a square-integrable
field `y` is a weak solution of `L_x y = 0` exactly when `u y` is a weak solution of
`L_{u · x} (u y) = 0`. -/
theorem forall_integral_inner_gaugeFixedAdjoint_gaugeTransform_eq_zero_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪gaugeLp μ u y z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ = 0) ↔
      ∀ η, ContDiff ℝ 2 η → HasCompactSupport η → ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
  have h0 (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
      ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) z, η z⟫ ∂μ = 0 :=
    integral_eq_zero_of_ae ((Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ).mono fun z hz ↦ by
      simp only [hz, Pi.zero_apply, inner_zero_left])
  simpa only [map_zero, h0] using
    forall_integral_inner_gaugeFixedAdjoint_gaugeTransform_eq_iff hu x y 0

/-- **Orthogonality to the weak kernel is gauge covariant.** For a `C²` gauge `u`, a
square-integrable field `y` is orthogonal to every weak solution of `L_x w = 0` exactly when `u y`
is orthogonal to every weak solution of `L_{u · x} w = 0`. -/
theorem forall_integral_inner_gaugeLp_eq_zero_iff_of_gaugeFixedAdjoint {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ = 0) →
      ∫ z, ⟪gaugeLp μ u y z, w z⟫ ∂μ = 0) ↔
      ∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, w z⟫ ∂μ = 0 := by
  have hK := forall_integral_inner_gaugeFixedAdjoint_gaugeTransform_eq_zero_iff (μ := μ) hu x
  refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
  · rw [← L2.inner_def, ← (gaugeLp μ u).inner_map_map, L2.inner_def]
    exact h _ ((hK w).2 hw)
  · have hw' := (hK ((gaugeLp μ u).symm w)).1 (by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hw)
    rw [← L2.inner_def, ← (gaugeLp μ u).apply_symm_apply w, (gaugeLp μ u).inner_map_map,
      L2.inner_def]
    exact h _ hw'

/-- **The weak right inverse is gauge covariant.** Let `x` be a continuous field and `u` a `C²`
gauge. If `Q` and `Q'` are bounded weak right inverses of `L_x` and of `L_{u · x}` with values
orthogonal to the respective weak kernels, as at a plane vortex
(`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`), then `Q'` is the conjugate
`u ∘ Q ∘ u⁻¹` of `Q` by the `L²` gauge action. -/
theorem eq_gaugeLp_comp_comp_symm [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) {u : C(ℂ, Circle)} (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQK : ∀ f w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪Q f z, w z⟫ ∂μ = 0)
    (hQ' : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q' f z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQ'K : ∀ f w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪w z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ = 0) →
      ∫ z, ⟪Q' f z, w z⟫ ∂μ = 0) :
    Q' = (gaugeLp μ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] _) ∘L Q ∘L
      ((gaugeLp μ u).symm : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] _) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.coe_coe'', ← (gaugeLp μ u).symm_apply_eq]
  -- Both sides are weak solutions of `L_x y = u⁻¹ f` orthogonal to the weak kernel of `L_x`.
  refine eq_of_integral_inner_gaugeFixedAdjoint_eq hx ?_ (hQ _) ?_ (hQK _)
  · refine (forall_integral_inner_gaugeFixedAdjoint_gaugeTransform_eq_iff hu x _ _).1 ?_
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hQ' f
  · refine (forall_integral_inner_gaugeLp_eq_zero_iff_of_gaugeFixedAdjoint hu x _).1 ?_
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hQ'K f

end TauCeti.Vortex
