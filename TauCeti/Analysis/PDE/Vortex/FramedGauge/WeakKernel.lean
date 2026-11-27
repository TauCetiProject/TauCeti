/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Linearization
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
public import TauCeti.MeasureTheory.Function.Lp.LinearIsometry
public import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Complex.Circle.Basic

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
line frame, so these are in particular the line-frame laws, including those for the constant
gauges `u^(-m)` that restore the end framing after a rotation and do not tend to one at infinity.

* **The `L²` gauge action.** At a single value the linear action is the linear isometry
  `TauCeti.Vortex.gaugeFrame c` of `ℝ⁴` rotating the last two coordinates by `c ∈ U(1)`
  (`TauCeti.Vortex.gaugeLinearAction_apply_eq_gaugeFrame`). So the linear action of a measurable
  gauge preserves `Lᵖ` fields (`TauCeti.Vortex.memLp_gaugeLinearAction`), and a continuous gauge
  `u` acts on `L²(ℂ; ℝ⁴)` by the linear isometry equivalence `TauCeti.Vortex.gaugeLp μ u`,
  multiplication by the bounded continuous symbol `z ↦ gaugeFrame (u z)`
  (`BoundedContinuousFunction.mulLp`). It acts almost everywhere as `gaugeLinearAction u`
  (`TauCeti.Vortex.coeFn_gaugeLp`), and `u ↦ gaugeLp μ u` respects the group structure
  (`TauCeti.Vortex.gaugeLp_one`, `TauCeti.Vortex.gaugeLp_mul`, `TauCeti.Vortex.gaugeLp_symm`). A
  constant gauge `c` acts by the pointwise isometry `(gaugeFrame c).compLpₗᵢ`
  (`TauCeti.Vortex.gaugeLp_const`).
* **The weak kernel.** The weak kernel at `u · x` is the image of the weak kernel at `x`, so the
  two have the same dimension and the orthogonal projections onto them are conjugate. This holds
  for a smooth gauge at every field `x` (`TauCeti.Vortex.weakGaugeFixedKernel_gaugeTransform`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_gaugeTransform`,
  `TauCeti.Vortex.starProjection_weakGaugeFixedKernel_gaugeTransform_apply`), and for a `C¹`
  gauge at a continuous field (the `_of_continuous` forms), where the weak kernel is detected by
  `C¹` test fields (`TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_contDiff_one`).
* **Weak solutions.** For a `Cⁿ` gauge with `n ≥ 1`, testing `u·y` against `L_{u·x}*` on compactly
  supported `Cⁿ` test fields is testing `y` against `L_x*` on them
  (`TauCeti.Vortex.forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff`): the test
  field `η` is traded for `u⁻¹·η`. Hence for a `C²` gauge, `u·y` is a (minimal) weak solution of
  `L_{u·x} (u·y) = u·f` exactly when `y` is one of `L_x y = f`
  (`TauCeti.Vortex.isGaugeFixedWeakSolution_gaugeLp_iff`,
  `TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_iff`), in the sense of
  `TauCeti.Vortex.IsGaugeFixedWeakSolution` and `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution`.
* **The weak right inverse.** At a continuous field the minimal weak solution is unique
  (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`). So every weak right inverse `Q'` at
  `u·x` is the conjugate `Q' = u ∘ Q ∘ u⁻¹` of every weak right inverse `Q` at `x`
  (`TauCeti.Vortex.apply_gaugeLp_eq_gaugeLp_apply`, `TauCeti.Vortex.eq_gaugeLp_comp_comp_symm`),
  and a weak right inverse at `x`, which exists at a plane vortex with `|α| → 1`
  (`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`), supplies one at
  every gauge transform of `x`
  (`TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_gaugeLp_apply_symm`).

The statements need no vortex equation, decay or framing assumption on the field or the gauge:
they are consequences of the pointwise covariance and of `|u| = 1`. The corresponding laws for
translations and rotations of the plane need the action of rigid motions on `L²`, and are not
treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Complex
open scoped RealInnerProductSpace ContDiff BoundedContinuousFunction

/-! ### The gauge action on `Lᵖ` fields -/

section MemLp

variable {μ : Measure ℂ}

/-- The value of the linear gauge action is a continuous function of the value of the gauge and
of the value of the variation. -/
private theorem continuous_gaugeLinearAction_uncurry :
    Continuous fun p : Circle × EuclideanSpace ℝ (Fin 4) ↦
      gaugeLinearAction (fun _ ↦ p.1) (fun _ ↦ p.2) 0 := by
  simp only [gaugeLinearAction_apply]
  fun_prop

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

end MemLp

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

/-- The gauge action of the inverse gauge undoes the gauge action. -/
@[simp]
theorem gaugeLp_gaugeLp_inv (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLp μ u (gaugeLp μ u⁻¹ f) = f := by
  rw [← gaugeLp_symm, LinearIsometryEquiv.apply_symm_apply]

/-- The gauge action of the gauge undoes the gauge action of the inverse gauge. -/
@[simp]
theorem gaugeLp_inv_gaugeLp (u : C(ℂ, Circle)) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    gaugeLp μ u⁻¹ (gaugeLp μ u f) = f := by
  rw [← gaugeLp_symm, LinearIsometryEquiv.symm_apply_apply]

/-- **A constant gauge acts on `L²` by its gauge frame.** The `L²` gauge action of the constant
gauge `c` is postcomposition with `gaugeFrame c`, the change of line frame by `c`. -/
@[simp]
theorem gaugeLp_const (c : Circle) :
    gaugeLp μ (ContinuousMap.const ℂ c) = (gaugeFrame c).compLpₗᵢ 2 μ := by
  ext1 f
  refine gaugeLp_eq_iff.2 ?_
  filter_upwards [(gaugeFrame c).coeFn_compLpₗᵢ (p := 2) (μ := μ) f] with z hz
  rw [hz, gaugeLinearAction_apply_eq_gaugeFrame, ContinuousMap.const_apply]

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
of `u`. This holds at every field `x`; for a `C¹` gauge at a continuous field, see
`weakGaugeFixedKernel_gaugeTransform_of_continuous`. -/
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

/-- If the weak kernel at `u · x` is the image of the weak kernel at `x` under the `L²` gauge
action, then the orthogonal projections onto them are conjugate. -/
private theorem starProjection_weakGaugeFixedKernel_gaugeTransform_apply_of_eq {u : C(ℂ, Circle)}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (h : weakGaugeFixedKernel (gaugeTransform u x) = (weakGaugeFixedKernel x).map
      ((gaugeLp volume u).toLinearEquiv :
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume))
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
  exact key _ h

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
      gaugeLp volume u ((weakGaugeFixedKernel x).starProjection ((gaugeLp volume u).symm f)) :=
  starProjection_weakGaugeFixedKernel_gaugeTransform_apply_of_eq
    (weakGaugeFixedKernel_gaugeTransform u hu x) f

/-! ### Weak solutions -/

section WeakSolution

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

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
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) :
    ∫ z, ⟪gaugeLp μ u y z, gaugeFixedAdjoint (gaugeTransform u x) η z⟫ ∂μ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x (gaugeLinearAction u⁻¹ η) z⟫ ∂μ := by
  refine integral_congr_ae ((coeFn_gaugeLp u y).mono fun z hz ↦ ?_)
  dsimp only
  rw [hz, gaugeFixedAdjoint_gaugeTransform_eq hu x hη, inner_gaugeLinearAction]

/-- **Gauge transport of weak equations**, for test fields of any smoothness `n ≥ 1`. For a `Cⁿ`
gauge `u`, `∫ ⟪u·y, L_{u·x}* η⟫ = ∫ ⟪u·f, η⟫` holds for every compactly supported `Cⁿ` test field
`η` exactly when `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` does: the test field `η` is traded for `u⁻¹·η`, which
is again a compactly supported `Cⁿ` test field, and conversely. -/
theorem forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff {n : WithTop ℕ∞}
    (hn : 1 ≤ n) {u : C(ℂ, Circle)} (hu : ContDiff ℝ n fun z ↦ (u z : ℂ))
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
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) ↔
      IsGaugeFixedWeakSolution μ x f y := by
  rw [isGaugeFixedWeakSolution_iff, isGaugeFixedWeakSolution_iff]
  exact forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff one_le_two hu x f y

/-- The gauge action on weak solutions: if `y` is a weak solution of `L_x y = f`, then `u·y` is
a weak solution of `L_{u·x} (u·y) = u·f`, for a `C²` gauge `u`. -/
theorem IsGaugeFixedWeakSolution.gaugeLp {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsGaugeFixedWeakSolution μ x f y) :
    IsGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) :=
  (isGaugeFixedWeakSolution_gaugeLp_iff hu).2 h

/-- **Orthogonality to the weak kernel is gauge covariant.** For a `C²` gauge `u`, a
square-integrable field `y` is orthogonal to every weak solution of `L_x w = 0` exactly when `u·y`
is orthogonal to every weak solution of `L_{u·x} w = 0`. -/
theorem forall_integral_inner_gaugeLp_eq_zero_iff_of_gaugeFixedAdjoint {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ, IsGaugeFixedWeakSolution μ (gaugeTransform u x) 0 w →
      ∫ z, ⟪gaugeLp μ u y z, w z⟫ ∂μ = 0) ↔
      ∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ, IsGaugeFixedWeakSolution μ x 0 w →
        ∫ z, ⟪y z, w z⟫ ∂μ = 0 := by
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

/-- **Gauge covariance of minimal weak solutions.** For a `C²` gauge `u`, `u·y` is a minimal weak
solution of `L_{u·x} (u·y) = u·f` exactly when `y` is a minimal weak solution of `L_x y = f`. -/
theorem isMinimalGaugeFixedWeakSolution_gaugeLp_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) ↔
      IsMinimalGaugeFixedWeakSolution μ x f y := by
  rw [isMinimalGaugeFixedWeakSolution_iff, isMinimalGaugeFixedWeakSolution_iff]
  exact and_congr (isGaugeFixedWeakSolution_gaugeLp_iff hu)
    (forall_integral_inner_gaugeLp_eq_zero_iff_of_gaugeFixedAdjoint hu y)

/-- The gauge action on minimal weak solutions. -/
theorem IsMinimalGaugeFixedWeakSolution.gaugeLp {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h : IsMinimalGaugeFixedWeakSolution μ x f y) :
    IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) (gaugeLp μ u f) (gaugeLp μ u y) :=
  (isMinimalGaugeFixedWeakSolution_gaugeLp_iff hu).2 h

/-- **Weak right inverses of gauge-equivalent fields.** If `Q f` is a minimal weak solution of
`L_x y = f` for every `f`, then `u·Q(u⁻¹·f)` is a minimal weak solution of `L_{u·x} y = f`, for
a `C²` gauge `u`. So a weak right inverse at `x` gives one at every gauge transform of `x`. -/
theorem isMinimalGaugeFixedWeakSolution_gaugeLp_apply_symm {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
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
    {u : C(ℂ, Circle)} (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (hQ' : ∀ f, IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) f (Q' f))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    Q' (gaugeLp μ u f) = gaugeLp μ u (Q f) :=
  (hQ' _).unique (continuous_gaugeTransform (hu.of_le one_le_two) hx) ((hQ f).gaugeLp hu)

/-- **The weak right inverse is gauge covariant.** Let `x` be a continuous field and `u` a `C²`
gauge. If `Q` and `Q'` are bounded weak right inverses of `L_x` and of `L_{u · x}` with values
minimal weak solutions, as at a plane vortex
(`exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`), then `Q'` is the conjugate
`u ∘ Q ∘ u⁻¹` of `Q` by the `L²` gauge action. -/
theorem eq_gaugeLp_comp_comp_symm [IsFiniteMeasureOnCompacts μ] (hx : Continuous x)
    {u : C(ℂ, Circle)} (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (hQ' : ∀ f, IsMinimalGaugeFixedWeakSolution μ (gaugeTransform u x) f (Q' f)) :
    Q' = (gaugeLp μ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] _) ∘L Q ∘L
      ((gaugeLp μ u).symm : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] _) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.coe_coe'',
    ← apply_gaugeLp_eq_gaugeLp_apply hx hu hQ hQ', LinearIsometryEquiv.apply_symm_apply]

end WeakSolution

/-! ### The weak kernel at a continuous field -/

section WeakKernel

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Gauge covariance of the weak kernel**, elementwise. For a `C¹` gauge `u` and a continuous
field `x`, `u·w` lies in the weak `L²` kernel of `L_{u·x}` exactly when `w` lies in that of
`L_x`. -/
theorem gaugeLp_mem_weakGaugeFixedKernel_gaugeTransform_iff {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (hx : Continuous x)
    {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    gaugeLp volume u w ∈ weakGaugeFixedKernel (gaugeTransform u x) ↔
      w ∈ weakGaugeFixedKernel x := by
  rw [mem_weakGaugeFixedKernel_iff_contDiff_one (continuous_gaugeTransform hu hx),
    mem_weakGaugeFixedKernel_iff_contDiff_one hx]
  simpa only [map_zero, Lp.integral_inner_coeFn_zero_left] using
    forall_integral_inner_gaugeLp_gaugeFixedAdjoint_gaugeTransform_iff le_rfl hu x 0 w

/-- **Gauge covariance of the weak kernel at a continuous field.** For a `C¹` gauge `u` and a
continuous field `x`, the weak `L²` kernel of `L_{u·x}` is the image under the gauge of the weak
kernel of `L_x`. -/
theorem weakGaugeFixedKernel_gaugeTransform_of_continuous {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (hx : Continuous x) :
    weakGaugeFixedKernel (gaugeTransform u x) =
      (weakGaugeFixedKernel x).map ((gaugeLp volume u).toLinearEquiv :
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) := by
  ext w
  rw [Submodule.mem_map_equiv, ← gaugeLp_mem_weakGaugeFixedKernel_gaugeTransform_iff hu hx]
  simp

/-- For a `C¹` gauge `u` and a continuous field `x`, the weak kernels of `L_{u·x}` and `L_x`
have the same dimension. -/
theorem finrank_weakGaugeFixedKernel_gaugeTransform_of_continuous {u : C(ℂ, Circle)}
    (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (hx : Continuous x) :
    Module.finrank ℝ (weakGaugeFixedKernel (gaugeTransform u x)) =
      Module.finrank ℝ (weakGaugeFixedKernel x) := by
  rw [weakGaugeFixedKernel_gaugeTransform_of_continuous hu hx, LinearEquiv.finrank_map_eq]

/-- **The kernel projections are conjugate at a continuous field.** For a `C¹` gauge `u` and a
continuous field `x`, the orthogonal projection of `L²(ℂ; ℝ⁴)` onto the weak kernel of `L_{u·x}`
is the conjugate by the gauge of the orthogonal projection onto the weak kernel of `L_x`. -/
theorem starProjection_weakGaugeFixedKernel_gaugeTransform_apply_of_continuous
    {u : C(ℂ, Circle)} (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ)) (hx : Continuous x)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) :
    (weakGaugeFixedKernel (gaugeTransform u x)).starProjection f =
      gaugeLp volume u ((weakGaugeFixedKernel x).starProjection ((gaugeLp volume u).symm f)) :=
  starProjection_weakGaugeFixedKernel_gaugeTransform_apply_of_eq
    (weakGaugeFixedKernel_gaugeTransform_of_continuous hu hx) f

end WeakKernel

end TauCeti.Vortex
