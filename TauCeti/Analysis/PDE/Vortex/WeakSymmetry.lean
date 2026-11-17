/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Linearization
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.Symmetry
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Complex.Circle
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Symmetries of the weak right inverse of the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has the
formal adjoint `L_x*` (`gaugeFixedAdjoint`). A field `y` is a weak solution of `L_x y = f`
(`TauCeti.Vortex.IsGaugeFixedWeakSolution`) if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
supported `C²` test field `η`; the weak kernel of `L_x` consists of the weak solutions of
`L_x y = 0`. At a plane vortex with `|α| → 1` the weak right inverse `Q` of
`TauCeti.Analysis.PDE.Vortex.RightInverse` sends `f ∈ L²` to a square-integrable weak solution
of `L_x y = f` orthogonal to the weak kernel. This file names that property
(`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution`) and proves:

* weak solutions are invariant under changes on null sets
  (`TauCeti.Vortex.IsGaugeFixedWeakSolution.congr_ae`), closed under scalar multiples and, when
  square integrable, under sums, and two square-integrable weak solutions of the same equation
  differ by an element of the weak kernel (`TauCeti.Vortex.IsGaugeFixedWeakSolution.sub_of_memLp`);
* a least weak solution is unique up to null sets
  (`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.ae_eq`), and it has the least `L²` norm among
  all square-integrable weak solutions
  (`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.integral_norm_sq_le`), so `Q` is determined by
  this property (`TauCeti.Vortex.exists_continuousLinearMap_isLeastGaugeFixedWeakSolution`);
* weak solutions, the weak kernel and least weak solutions are carried to the corresponding
  objects at the transformed field by the symmetries of the plane vortex problem:
  - the translations `translateField a` of fields and targets
    (`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.translateField`);
  - the rotations `rotateField u` of fields and `rotateTarget u` of targets
    (`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.rotateField`), for any additive Haar
    measure, since rotations of the plane preserve it (`Circle.measurePreserving_coe_mul`);
  - the `C²` gauge transformations `gaugeTransform g` of the background, acting by the linear
    gauge action `gaugeLinearAction g` on fields and targets
    (`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.gaugeTransform`). Constant gauges are the
    changes of frame of the line at infinity, and the framed gauge group is included.

Together with uniqueness, these give the translation, rotation and line-frame laws of the right
inverse: if `y` and `y'` are the least weak solutions at `x` and at a transformed field, with
transformed data, then `y'` is the transformed `y` almost everywhere
(`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.translateField_ae_eq`,
`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.rotateField_ae_eq`,
`TauCeti.Vortex.IsLeastGaugeFixedWeakSolution.gaugeTransform_ae_eq`). So if `Q` and `Q'` are the
weak right inverses at `x` and at the transformed field, then `Q'` applied to the transformed
input is the transformed `Q f`, almost everywhere.

All three symmetries act pointwise isometrically after a measure-preserving change of variables
of the plane, and intertwine `L_x*` on test fields (`gaugeFixedAdjoint_translateField`,
`gaugeFixedAdjoint_rotateField`, `gaugeFixedAdjoint_gaugeTransform`). The proofs only use these
two facts.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace TauCeti.Vortex

variable {μ : Measure ℂ} {x y y' f f' : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- `y` is a weak solution of `L_x y = f`, for the gauge-fixed vortex operator `L_x`
(`gaugeFixedOperator`): `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` test
field `η`. The weak solutions of `L_x y = 0` form the weak kernel of `L_x`. -/
def IsGaugeFixedWeakSolution (μ : Measure ℂ) (x y f : ℂ → EuclideanSpace ℝ (Fin 4)) : Prop :=
  ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
    ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ

/-- The defining condition of a weak solution of `L_x y = f`. -/
theorem isGaugeFixedWeakSolution_iff :
    IsGaugeFixedWeakSolution μ x y f ↔ ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ :=
  Iff.rfl

/-- `y` lies in the weak kernel of `L_x` exactly when `∫ ⟪y, L_x* η⟫ = 0` for every test
field `η`. -/
theorem isGaugeFixedWeakSolution_zero_iff :
    IsGaugeFixedWeakSolution μ x y 0 ↔ ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
  simp [isGaugeFixedWeakSolution_iff]

/-- `y` is the weak solution of least norm of `L_x y = f`: it is square integrable, a weak
solution of `L_x y = f`, and orthogonal in `L²` to the square-integrable weak kernel of `L_x`.
At a plane vortex this is the value at `f` of the weak right inverse of `L_x`
(`exists_continuousLinearMap_isLeastGaugeFixedWeakSolution`). -/
structure IsLeastGaugeFixedWeakSolution (μ : Measure ℂ) (x y f : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Prop where
  memLp : MemLp y 2 μ
  isGaugeFixedWeakSolution : IsGaugeFixedWeakSolution μ x y f
  integral_inner_eq_zero ⦃u : ℂ → EuclideanSpace ℝ (Fin 4)⦄ : MemLp u 2 μ →
    IsGaugeFixedWeakSolution μ x u 0 → ∫ z, ⟪y z, u z⟫ ∂μ = 0

/-! ### Linear structure and uniqueness -/

/-- Weak solutions only depend on the classes of `y` and `f` up to null sets. -/
theorem IsGaugeFixedWeakSolution.congr_ae (h : IsGaugeFixedWeakSolution μ x y f)
    (hy : y =ᵐ[μ] y') (hf : f =ᵐ[μ] f') : IsGaugeFixedWeakSolution μ x y' f' := by
  intro η hη hηc
  have hy' : ∫ z, ⟪y' z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ :=
    integral_congr_ae (hy.mono fun z hz ↦ by simp only [hz])
  have hf' : ∫ z, ⟪f' z, η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ :=
    integral_congr_ae (hf.mono fun z hz ↦ by simp only [hz])
  rw [hy', hf']
  exact h η hη hηc

/-- Least weak solutions only depend on the classes of `y` and `f` up to null sets. -/
theorem IsLeastGaugeFixedWeakSolution.congr_ae (h : IsLeastGaugeFixedWeakSolution μ x y f)
    (hy : y =ᵐ[μ] y') (hf : f =ᵐ[μ] f') : IsLeastGaugeFixedWeakSolution μ x y' f' where
  memLp := h.memLp.ae_eq hy
  isGaugeFixedWeakSolution := h.isGaugeFixedWeakSolution.congr_ae hy hf
  integral_inner_eq_zero u hu hk := by
    rw [← h.integral_inner_eq_zero hu hk]
    exact integral_congr_ae (hy.mono fun z hz ↦ by simp only [hz])

/-- A scalar multiple of a weak solution of `L_x y = f` is a weak solution of
`L_x (c y) = c f`. -/
theorem IsGaugeFixedWeakSolution.smul (h : IsGaugeFixedWeakSolution μ x y f) (c : ℝ) :
    IsGaugeFixedWeakSolution μ x (c • y) (c • f) := by
  intro η hη hηc
  simp only [Pi.smul_apply, real_inner_smul_left]
  rw [integral_const_mul, integral_const_mul, h η hη hηc]

section Uniqueness

variable [IsFiniteMeasureOnCompacts μ]

/-- The sum of square-integrable weak solutions of `L_x y = f` and `L_x y' = f'`, with
square-integrable data, is a weak solution of `L_x (y + y') = f + f'`. -/
theorem IsGaugeFixedWeakSolution.add (hx : Continuous x) (hy : MemLp y 2 μ) (hy' : MemLp y' 2 μ)
    (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) (h : IsGaugeFixedWeakSolution μ x y f)
    (h' : IsGaugeFixedWeakSolution μ x y' f') :
    IsGaugeFixedWeakSolution μ x (y + y') (f + f') := by
  intro η hη hηc
  have hL : MemLp (gaugeFixedAdjoint x η) 2 μ :=
    memLp_gaugeFixedAdjoint hx (hη.of_le (by norm_num)) hηc
  have hη2 : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
  simp only [Pi.add_apply, inner_add_left]
  rw [integral_add (hy.integrable_inner hL) (hy'.integrable_inner hL),
    integral_add (hf.integrable_inner hη2) (hf'.integrable_inner hη2), h η hη hηc, h' η hη hηc]

/-- The difference of two square-integrable weak solutions of `L_x y = f` lies in the weak
kernel. -/
theorem IsGaugeFixedWeakSolution.sub_of_memLp (hx : Continuous x) (hy : MemLp y 2 μ)
    (hy' : MemLp y' 2 μ) (h : IsGaugeFixedWeakSolution μ x y f)
    (h' : IsGaugeFixedWeakSolution μ x y' f) : IsGaugeFixedWeakSolution μ x (y - y') 0 := by
  rw [isGaugeFixedWeakSolution_zero_iff]
  intro η hη hηc
  have hL : MemLp (gaugeFixedAdjoint x η) 2 μ :=
    memLp_gaugeFixedAdjoint hx (hη.of_le (by norm_num)) hηc
  simp only [Pi.sub_apply, inner_sub_left]
  rw [integral_sub (hy.integrable_inner hL) (hy'.integrable_inner hL), h η hη hηc, h' η hη hηc,
    sub_self]

/-- **Uniqueness of the least weak solution.** Two square-integrable weak solutions of
`L_x y = f` that are orthogonal to the weak kernel agree almost everywhere. -/
theorem IsLeastGaugeFixedWeakSolution.ae_eq (hx : Continuous x)
    (h : IsLeastGaugeFixedWeakSolution μ x y f) (h' : IsLeastGaugeFixedWeakSolution μ x y' f) :
    y =ᵐ[μ] y' := by
  have hd : MemLp (y - y') 2 μ := h.memLp.sub h'.memLp
  have hk := h.isGaugeFixedWeakSolution.sub_of_memLp hx h.memLp h'.memLp
    h'.isGaugeFixedWeakSolution
  have hint : ∫ z, ‖(y - y') z‖ ^ 2 ∂μ = 0 := by
    have hpt (z : ℂ) : ‖(y - y') z‖ ^ 2 = ⟪y z, (y - y') z⟫ - ⟪y' z, (y - y') z⟫ := by
      rw [← inner_sub_left]
      exact (real_inner_self_eq_norm_sq ((y - y') z)).symm
    simp_rw [hpt]
    rw [integral_sub (h.memLp.integrable_inner hd) (h'.memLp.integrable_inner hd),
      h.integral_inner_eq_zero hd hk, h'.integral_inner_eq_zero hd hk, sub_self]
  rw [integral_eq_zero_iff_of_nonneg (fun z ↦ by positivity) (hd.integrable_norm_pow two_ne_zero)]
    at hint
  filter_upwards [hint] with z hz
  simpa [sub_eq_zero] using hz

/-- **Minimality of the least weak solution.** The least weak solution of `L_x y = f` has
`L²` norm at most that of any square-integrable weak solution of `L_x y = f`. -/
theorem IsLeastGaugeFixedWeakSolution.integral_norm_sq_le (hx : Continuous x)
    (h : IsLeastGaugeFixedWeakSolution μ x y f) (hy' : MemLp y' 2 μ)
    (h' : IsGaugeFixedWeakSolution μ x y' f) :
    ∫ z, ‖y z‖ ^ 2 ∂μ ≤ ∫ z, ‖y' z‖ ^ 2 ∂μ := by
  have hd : MemLp (y' - y) 2 μ := hy'.sub h.memLp
  have h0 := h.integral_inner_eq_zero hd (h'.sub_of_memLp hx hy' h.memLp h.isGaugeFixedWeakSolution)
  have hpt (z : ℂ) : ‖y' z‖ ^ 2 = ‖y z‖ ^ 2 + 2 * ⟪y z, (y' - y) z⟫ + ‖(y' - y) z‖ ^ 2 := by
    rw [← norm_add_sq_real, Pi.sub_apply, add_sub_cancel]
  have hy2 := h.memLp.integrable_norm_pow (p := 2) two_ne_zero
  have hd2 := hd.integrable_norm_pow (p := 2) two_ne_zero
  have hyd := (h.memLp.integrable_inner (𝕜 := ℝ) hd).const_mul 2
  simp_rw [hpt]
  rw [integral_add _ hd2, integral_add hy2 hyd, integral_const_mul, h0, mul_zero, add_zero,
    le_add_iff_nonneg_right]
  · exact integral_nonneg fun z ↦ by positivity
  · exact hy2.add hyd

end Uniqueness

/-- **The weak right inverse at a plane vortex.** Let `x` be a `C¹` solution of the plane vortex
equation with `|α| → 1` at infinity. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` whose
value `Q f` is the least weak solution of `L_x y = f` for every `f ∈ L²`. By
`IsLeastGaugeFixedWeakSolution.ae_eq`, `Q` is unique. -/
theorem exists_continuousLinearMap_isLeastGaugeFixedWeakSolution [μ.IsAddHaarMeasure]
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      ∀ f, IsLeastGaugeFixedWeakSolution μ x (Q f) f := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ)
    hx hsol hlim
  refine ⟨Q, fun f ↦ ⟨Lp.memLp _, fun η hη hηc ↦ hQ f η hη hηc, fun u hu hk ↦ ?_⟩⟩
  have hk' := hk.congr_ae hu.coeFn_toLp.symm EventuallyEq.rfl
  rw [isGaugeFixedWeakSolution_zero_iff] at hk'
  refine (integral_congr_ae (hu.coeFn_toLp.mono fun z hz ↦ ?_)).trans (hQK f _ hk')
  simp only [hz]

/-! ### Transport by symmetries -/

/-- A symmetry of the weak gauge-fixed equations relating the fields `x` and `x'`: a
measure-preserving change of variables `ψ` of the plane, with an action `S` on fields and `T`
on targets which are pointwise isometric over `ψ`, preserve square integrability, are onto on
square-integrable fields and on test fields respectively, and intertwine the formal adjoints
`L_x*` and `L_x'*` on test fields. -/
private structure WeakSymmetry (μ : Measure ℂ) (x x' : ℂ → EuclideanSpace ℝ (Fin 4)) where
  ψ : ℂ ≃ᵐ ℂ
  S : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)
  T : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)
  measurePreserving : MeasurePreserving ψ μ μ
  inner_S (y v : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ⟪S y z, S v z⟫ = ⟪y (ψ z), v (ψ z)⟫
  inner_T (f η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : ⟪T f z, T η z⟫ = ⟪f (ψ z), η (ψ z)⟫
  memLp_S (y : ℂ → EuclideanSpace ℝ (Fin 4)) : MemLp y 2 μ → MemLp (S y) 2 μ
  exists_S_eq (u : ℂ → EuclideanSpace ℝ (Fin 4)) : MemLp u 2 μ → ∃ v, MemLp v 2 μ ∧ S v = u
  test_T (η : ℂ → EuclideanSpace ℝ (Fin 4)) : ContDiff ℝ 2 η → HasCompactSupport η →
    ContDiff ℝ 2 (T η) ∧ HasCompactSupport (T η)
  exists_T_eq (η : ℂ → EuclideanSpace ℝ (Fin 4)) : ContDiff ℝ 2 η → HasCompactSupport η →
    ∃ ν, ContDiff ℝ 2 ν ∧ HasCompactSupport ν ∧ T ν = η
  gaugeFixedAdjoint_T (η : ℂ → EuclideanSpace ℝ (Fin 4)) : ContDiff ℝ 2 η → HasCompactSupport η →
    gaugeFixedAdjoint x' (T η) = S (gaugeFixedAdjoint x η)

namespace WeakSymmetry

variable {x' : ℂ → EuclideanSpace ℝ (Fin 4)}

private theorem isGaugeFixedWeakSolution (σ : WeakSymmetry μ x x')
    (h : IsGaugeFixedWeakSolution μ x y f) : IsGaugeFixedWeakSolution μ x' (σ.S y) (σ.T f) := by
  intro η hη hηc
  obtain ⟨ν, hν, hνc, rfl⟩ := σ.exists_T_eq η hη hηc
  rw [σ.gaugeFixedAdjoint_T ν hν hνc]
  simp_rw [σ.inner_S, σ.inner_T]
  rw [σ.measurePreserving.integral_comp' fun z ↦ ⟪y z, gaugeFixedAdjoint x ν z⟫,
    σ.measurePreserving.integral_comp' fun z ↦ ⟪f z, ν z⟫]
  exact h ν hν hνc

private theorem isGaugeFixedWeakSolution_zero_of_S (σ : WeakSymmetry μ x x')
    (h : IsGaugeFixedWeakSolution μ x' (σ.S y) 0) : IsGaugeFixedWeakSolution μ x y 0 := by
  rw [isGaugeFixedWeakSolution_zero_iff] at h ⊢
  intro η hη hηc
  obtain ⟨hTη, hTηc⟩ := σ.test_T η hη hηc
  have h' := h (σ.T η) hTη hTηc
  rw [σ.gaugeFixedAdjoint_T η hη hηc] at h'
  simp_rw [σ.inner_S] at h'
  rwa [σ.measurePreserving.integral_comp' fun z ↦ ⟪y z, gaugeFixedAdjoint x η z⟫] at h'

private theorem isLeastGaugeFixedWeakSolution (σ : WeakSymmetry μ x x')
    (h : IsLeastGaugeFixedWeakSolution μ x y f) :
    IsLeastGaugeFixedWeakSolution μ x' (σ.S y) (σ.T f) where
  memLp := σ.memLp_S y h.memLp
  isGaugeFixedWeakSolution := σ.isGaugeFixedWeakSolution h.isGaugeFixedWeakSolution
  integral_inner_eq_zero u hu hk := by
    obtain ⟨v, hv, rfl⟩ := σ.exists_S_eq u hu
    simp_rw [σ.inner_S]
    rw [σ.measurePreserving.integral_comp' fun z ↦ ⟪y z, v z⟫]
    exact h.integral_inner_eq_zero hv (σ.isGaugeFixedWeakSolution_zero_of_S hk)

end WeakSymmetry

/-! #### Translations -/

/-- Translation by `a` as a symmetry of the weak equations. -/
private noncomputable def translateWeakSymmetry [μ.IsAddRightInvariant] (a : ℂ) :
    WeakSymmetry μ x (translateField a x) where
  ψ := MeasurableEquiv.addRight a
  S := translateField a
  T := translateField a
  measurePreserving := measurePreserving_add_right μ a
  inner_S _ _ _ := by simp [translateField_apply]
  inner_T _ _ _ := by simp [translateField_apply]
  memLp_S _ := memLp_translateField a
  exists_S_eq u hu := ⟨translateField (-a) u, memLp_translateField (-a) hu, by simp⟩
  test_T η hη hηc := ⟨contDiff_translateField a hη, hasCompactSupport_translateField a hηc⟩
  exists_T_eq η hη hηc := ⟨translateField (-a) η, contDiff_translateField (-a) hη,
    hasCompactSupport_translateField (-a) hηc, by simp⟩
  gaugeFixedAdjoint_T η _ _ := funext fun z ↦ by
    rw [gaugeFixedAdjoint_translateField, translateField_apply]

/-- **Translation law for weak solutions.** If `y` is a weak solution of `L_x y = f`, then the
translated field is a weak solution at the translated background, with translated data. With
`f = 0`, translations carry the weak kernel of `L_x` to that of `L_(translateField a x)`. -/
theorem IsGaugeFixedWeakSolution.translateField [μ.IsAddRightInvariant]
    (h : IsGaugeFixedWeakSolution μ x y f) (a : ℂ) :
    IsGaugeFixedWeakSolution μ (translateField a x) (translateField a y) (translateField a f) :=
  (translateWeakSymmetry a).isGaugeFixedWeakSolution h

/-- **Translation law for the weak right inverse.** If `y` is the least weak solution of
`L_x y = f`, then the translated field is the least weak solution at the translated background,
with translated data. -/
theorem IsLeastGaugeFixedWeakSolution.translateField [μ.IsAddRightInvariant]
    (h : IsLeastGaugeFixedWeakSolution μ x y f) (a : ℂ) :
    IsLeastGaugeFixedWeakSolution μ (translateField a x) (translateField a y)
      (translateField a f) :=
  (translateWeakSymmetry a).isLeastGaugeFixedWeakSolution h

/-! #### Rotations -/

/-- Rotation by `u` as a symmetry of the weak equations. -/
private noncomputable def rotateWeakSymmetry [μ.IsAddHaarMeasure] (u : Circle) :
    WeakSymmetry μ x (rotateField u x) where
  ψ := MeasurableEquiv.mulLeft₀ (u : ℂ) (Circle.coe_ne_zero u)
  S := rotateField u
  T := rotateTarget u
  measurePreserving := Circle.measurePreserving_coe_mul μ u
  inner_S := inner_rotateField u
  inner_T := inner_rotateTarget u
  memLp_S _ := memLp_rotateField u
  exists_S_eq v hv := ⟨rotateField u⁻¹ v, memLp_rotateField u⁻¹ hv, by simp⟩
  test_T η hη hηc := ⟨contDiff_rotateTarget u hη, hasCompactSupport_rotateTarget u hηc⟩
  exists_T_eq η hη hηc := ⟨rotateTarget u⁻¹ η, contDiff_rotateTarget u⁻¹ hη,
    hasCompactSupport_rotateTarget u⁻¹ hηc, by simp⟩
  gaugeFixedAdjoint_T η hη _ := funext fun z ↦ gaugeFixedAdjoint_rotateField
    (((contDiff_piLp _).mp hη 2).differentiable (by norm_num) _)
    (((contDiff_piLp _).mp hη 3).differentiable (by norm_num) _)

/-- **Rotation law for weak solutions.** If `y` is a weak solution of `L_x y = f`, then the
rotated field is a weak solution at the rotated background, with data rotated by
`rotateTarget u`. With `f = 0`, rotations carry the weak kernel of `L_x` to that of
`L_(rotateField u x)`. -/
theorem IsGaugeFixedWeakSolution.rotateField [μ.IsAddHaarMeasure]
    (h : IsGaugeFixedWeakSolution μ x y f) (u : Circle) :
    IsGaugeFixedWeakSolution μ (rotateField u x) (rotateField u y) (rotateTarget u f) :=
  (rotateWeakSymmetry u).isGaugeFixedWeakSolution h

/-- **Rotation law for the weak right inverse.** If `y` is the least weak solution of
`L_x y = f`, then the rotated field is the least weak solution at the rotated background, with
data rotated by `rotateTarget u`. -/
theorem IsLeastGaugeFixedWeakSolution.rotateField [μ.IsAddHaarMeasure]
    (h : IsLeastGaugeFixedWeakSolution μ x y f) (u : Circle) :
    IsLeastGaugeFixedWeakSolution μ (rotateField u x) (rotateField u y) (rotateTarget u f) :=
  (rotateWeakSymmetry u).isLeastGaugeFixedWeakSolution h

/-! #### Gauge transformations -/

/-- A `C²` gauge transformation `g` as a symmetry of the weak equations. -/
private noncomputable def gaugeWeakSymmetry {g : ℂ → Circle}
    (hg : ContDiff ℝ 2 (fun z ↦ (g z : ℂ))) :
    WeakSymmetry μ x (gaugeTransform g x) where
  ψ := MeasurableEquiv.refl ℂ
  S := gaugeLinearAction g
  T := gaugeLinearAction g
  measurePreserving := MeasurePreserving.id μ
  inner_S := inner_gaugeLinearAction g
  inner_T := inner_gaugeLinearAction g
  memLp_S _ := memLp_gaugeLinearAction hg.continuous
  exists_S_eq v hv := ⟨gaugeLinearAction g⁻¹ v, memLp_gaugeLinearAction
    (Circle.contDiff_coe_inv hg).continuous hv, gaugeLinearAction_gaugeLinearAction_inv g v⟩
  test_T η hη hηc := ⟨contDiff_gaugeLinearAction hg hη, hasCompactSupport_gaugeLinearAction g hηc⟩
  exists_T_eq η hη hηc := ⟨gaugeLinearAction g⁻¹ η,
    contDiff_gaugeLinearAction (Circle.contDiff_coe_inv hg) hη,
    hasCompactSupport_gaugeLinearAction g⁻¹ hηc, gaugeLinearAction_gaugeLinearAction_inv g η⟩
  gaugeFixedAdjoint_T η hη _ := funext fun z ↦ gaugeFixedAdjoint_gaugeTransform
    (hg.differentiable (by norm_num) z) x
    (((contDiff_piLp _).mp hη 2).differentiable (by norm_num) z)
    (((contDiff_piLp _).mp hη 3).differentiable (by norm_num) z)

/-- **Gauge law for weak solutions.** If `y` is a weak solution of `L_x y = f` and `g` is a
`C²` gauge, then `gaugeLinearAction g y` is a weak solution at the gauge-transformed background
`gaugeTransform g x`, with data `gaugeLinearAction g f`. Constant gauges give the line-frame law.
With `f = 0`, gauges carry the weak kernel of `L_x` to that of `L_(gaugeTransform g x)`. -/
theorem IsGaugeFixedWeakSolution.gaugeTransform (h : IsGaugeFixedWeakSolution μ x y f)
    {g : ℂ → Circle} (hg : ContDiff ℝ 2 (fun z ↦ (g z : ℂ))) :
    IsGaugeFixedWeakSolution μ (gaugeTransform g x) (gaugeLinearAction g y)
      (gaugeLinearAction g f) :=
  (gaugeWeakSymmetry hg).isGaugeFixedWeakSolution h

/-- **Gauge law for the weak right inverse.** If `y` is the least weak solution of `L_x y = f`
and `g` is a `C²` gauge, then `gaugeLinearAction g y` is the least weak solution at the
gauge-transformed background `gaugeTransform g x`, with data `gaugeLinearAction g f`. -/
theorem IsLeastGaugeFixedWeakSolution.gaugeTransform (h : IsLeastGaugeFixedWeakSolution μ x y f)
    {g : ℂ → Circle} (hg : ContDiff ℝ 2 (fun z ↦ (g z : ℂ))) :
    IsLeastGaugeFixedWeakSolution μ (gaugeTransform g x) (gaugeLinearAction g y)
      (gaugeLinearAction g f) :=
  (gaugeWeakSymmetry hg).isLeastGaugeFixedWeakSolution h

/-! ### Laws of the weak right inverse -/

/-- **Translation law of the weak right inverse.** If `y` and `y'` are the least weak solutions
of `L_x y = f` and of the translated equation at `translateField a x` with data
`translateField a f`, then `y'` is the translate of `y` almost everywhere. -/
theorem IsLeastGaugeFixedWeakSolution.translateField_ae_eq [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddRightInvariant]
    (hx : Continuous x) (h : IsLeastGaugeFixedWeakSolution μ x y f) {a : ℂ}
    (h' : IsLeastGaugeFixedWeakSolution μ (Vortex.translateField a x) y'
      (Vortex.translateField a f)) :
    y' =ᵐ[μ] Vortex.translateField a y :=
  h'.ae_eq (contDiff_translateField a (contDiff_zero.2 hx)).continuous (h.translateField a)

/-- **Rotation law of the weak right inverse.** If `y` and `y'` are the least weak solutions of
`L_x y = f` and of the rotated equation at `rotateField u x` with data `rotateTarget u f`, then
`y'` is the rotation of `y` almost everywhere. -/
theorem IsLeastGaugeFixedWeakSolution.rotateField_ae_eq [μ.IsAddHaarMeasure]
    (hx : Continuous x) (h : IsLeastGaugeFixedWeakSolution μ x y f) {u : Circle}
    (h' : IsLeastGaugeFixedWeakSolution μ (Vortex.rotateField u x) y' (rotateTarget u f)) :
    y' =ᵐ[μ] Vortex.rotateField u y :=
  h'.ae_eq (contDiff_rotateField u (contDiff_zero.2 hx)).continuous (h.rotateField u)

/-- **Gauge law of the weak right inverse.** If `g` is a `C²` gauge and `y` and `y'` are the
least weak solutions of `L_x y = f` and of the gauge-transformed equation at
`gaugeTransform g x` with data `gaugeLinearAction g f`, then `y'` is `gaugeLinearAction g y`
almost everywhere. Constant gauges give the line-frame law. -/
theorem IsLeastGaugeFixedWeakSolution.gaugeTransform_ae_eq [IsFiniteMeasureOnCompacts μ]
    (hx : Continuous x)
    (h : IsLeastGaugeFixedWeakSolution μ x y f) {g : ℂ → Circle}
    (hg : ContDiff ℝ 2 (fun z ↦ (g z : ℂ)))
    (h' : IsLeastGaugeFixedWeakSolution μ (Vortex.gaugeTransform g x) y'
      (gaugeLinearAction g f)) :
    y' =ᵐ[μ] gaugeLinearAction g y :=
  h'.ae_eq
    (contDiff_gaugeTransform (n := 0) (hg.of_le (by norm_num)) (contDiff_zero.2 hx)).continuous
    (h.gaugeTransform hg)

end TauCeti.Vortex
