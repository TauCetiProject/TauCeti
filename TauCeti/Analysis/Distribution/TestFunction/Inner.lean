/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Inner-product pairings and Riesz transport on test functions

Let `Ω` be an open set of a real normed space `E` and `V` a real inner product space. A test
function `φ ∈ 𝓓(Ω, V)` pairs with a field `w : E → V` through the inner product, and the integrals
`∫ ⟪φ, w⟫` are the natural way to test a vector-valued equation. This file records that these
pairings, and those with the coordinate derivatives of `φ`, are integrable for locally integrable
`w`, and proves the fundamental lemma of the calculus of variations in this form: a locally
integrable field is determined almost everywhere on `Ω` by its pairings with `𝓓(Ω, V)`.

For real or complex Hilbert coefficients, `TestFunction.rieszEquiv` is a real continuous
linear equivalence to dual-valued tests, conjugating the coefficient scalar action. The original
test topologies and every finite regularity order and infinity are retained.
`TestFunction.eq_of_forall_integral_inner_eq` separates tests by their spatial inner pairings
for any Borel measure finite on compact sets and positive on nonempty open sets; it needs no
completeness of the coefficient space.

## Main results

* `TestFunction.integrable_inner`: `x ↦ ⟪φ x, w x⟫` is integrable for `w` locally integrable
  on `Ω`.
* `TestFunction.integrable_inner_fderiv`: `x ↦ ⟪∂_v φ x, w x⟫` is integrable for `w` locally
  integrable on `Ω`.
* `TauCeti.ae_eq_of_forall_integral_inner_eq`: two locally integrable fields with the same
  pairings against every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on `Ω`. The target `V` need only
  be complete; the proof tests against `ψ • c` for scalar test functions `ψ` and a constant
  vector `c`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions

section RealPairings

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TestFunction

/-- A test function paired with a locally integrable field is integrable. -/
theorem integrable_inner {w : E → V} (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, V)) :
    Integrable (fun x => ⟪(φ : E → V) x, w x⟫_ℝ) μ :=
  φ.integrable_bilin (innerSL ℝ) hw

/-- A directional derivative of a test function, paired with a locally integrable field, is
integrable. -/
theorem integrable_inner_fderiv {w : E → V} (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, V))
    (v : E) : Integrable (fun x => ⟪fderiv ℝ (φ : E → V) x v, w x⟫_ℝ) μ := by
  have h := (lineDerivCLM ℝ v φ : 𝓓(Ω, V)).integrable_inner hw
  simp only [coe_lineDerivCLM, lineDeriv_eq_fderiv] at h
  exact h

end TestFunction

namespace TauCeti

variable [CompleteSpace V] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The **fundamental lemma** for vector-valued test functions: locally integrable `g, h` on the
open set `Ω` with `∫ ⟪φ, g⟫ = ∫ ⟪φ, h⟫` for every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on
`Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq {g h : E → V} (hg : LocallyIntegrableOn g Ω μ)
    (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, V), ∫ x, ⟪(φ : E → V) x, g x⟫_ℝ ∂μ = ∫ x, ⟪(φ : E → V) x, h x⟫_ℝ ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hgh : LocallyIntegrableOn (g - h) Ω μ := hg.sub hh
  have key := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Ω.isOpen hgh
    fun ψ hψ hψc hψΩ => by
      set w := ∫ x, ψ x • (g - h) x ∂μ
      let ψ' : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψΩ⟩
      let Φ : 𝓓(Ω, V) := ⟨fun x => ψ x • w, hψ.smul contDiff_const, hψc.smul_right,
        (tsupport_smul_subset_left _ _).trans hψΩ⟩
      have hΦ := H Φ
      have hint : Integrable (fun x => ψ x • (g - h) x) μ :=
        ψ'.integrable_smul hgh
      have : ⟪w, w⟫_ℝ = 0 := by
        calc ⟪w, w⟫_ℝ = ∫ x, ⟪w, ψ x • (g - h) x⟫_ℝ ∂μ := (integral_inner hint w).symm
          _ = ∫ x, ⟪(Φ : E → V) x, g x⟫_ℝ ∂μ - ∫ x, ⟪(Φ : E → V) x, h x⟫_ℝ ∂μ := by
            rw [← integral_sub (Φ.integrable_inner hg) (Φ.integrable_inner hh)]
            refine integral_congr_ae (.of_forall fun x => ?_)
            simp [Φ, inner_smul_left, inner_smul_right, inner_sub_right, mul_sub]
          _ = 0 := sub_eq_zero.2 hΦ
      exact inner_self_eq_zero.1 this
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

end TauCeti

end RealPairings

noncomputable section

open TopologicalSpace ComplexConjugate MeasureTheory
open scoped Distributions

namespace TestFunction

variable {𝕜 E V : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  {n : ℕ∞} {Ω : Opens E}

/-- Native Riesz transport of coefficient values, for the original test-function topologies.
The equivalence is real-linear and conjugates the coefficient scalar action. -/
def rieszEquiv : 𝓓^{n}(Ω, V) ≃L[ℝ] 𝓓^{n}(Ω, StrongDual 𝕜 V) :=
  postcompCLE ((InnerProductSpace.toDual 𝕜 V).toIsometryEquiv
    |>.toRealLinearIsometryEquivOfMapZero (map_zero (InnerProductSpace.toDual 𝕜 V))
    |>.toContinuousLinearEquiv)

/-- Riesz transport evaluates to the original `𝕜` Hilbert pairing. -/
@[simp]
theorem rieszEquiv_apply (u : 𝓓^{n}(Ω, V)) (x : E) (v : V) :
    rieszEquiv u x v = inner 𝕜 (u x) v := by
  simp only [rieszEquiv, postcompCLE_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have he := IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero
    (InnerProductSpace.toDual 𝕜 V).toIsometryEquiv (map_zero (InnerProductSpace.toDual 𝕜 V))
  exact (congrArg (fun L : V → StrongDual 𝕜 V ↦ L (u x) v) he).trans
    InnerProductSpace.toDual_apply_apply

/-- The inverse native map recovers the Riesz representative of every original dual-valued test. -/
@[simp]
theorem rieszEquiv_symm_apply (φ : 𝓓^{n}(Ω, StrongDual 𝕜 V)) (x : E) (v : V) :
    inner 𝕜 (rieszEquiv.symm φ x) v = φ x v := by
  have h := congrArg (fun q : 𝓓^{n}(Ω, StrongDual 𝕜 V) ↦ q x v)
    (rieszEquiv.apply_symm_apply φ)
  simpa only [rieszEquiv_apply] using h

/-- Native Riesz transport conjugates the original `𝕜` test action. -/
theorem rieszEquiv_smul (c : 𝕜) (u : 𝓓^{n}(Ω, V)) :
    rieszEquiv (𝕜 := 𝕜) (c • u) = conj c • rieszEquiv (𝕜 := 𝕜) u := by
  apply TestFunction.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [rieszEquiv_apply, smul_apply, inner_smul_left]
  rfl

/-- The inverse Riesz transport has the same conjugate-scalar action. -/
theorem rieszEquiv_symm_smul (c : 𝕜) (φ : 𝓓^{n}(Ω, StrongDual 𝕜 V)) :
    (rieszEquiv (𝕜 := 𝕜) (V := V)).symm (c • φ) =
      conj c • (rieszEquiv (𝕜 := 𝕜) (V := V)).symm φ := by
  apply (rieszEquiv (𝕜 := 𝕜) (V := V)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, rieszEquiv_smul,
    starRingEnd_self_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace V] in
/-- Native tests are separated by their spatial Hilbert pairings. The measure need only be
finite on compact sets and charge every nonempty open set; no finite-dimensional base is needed. -/
theorem eq_of_forall_integral_inner_eq [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] {f g : 𝓓^{n}(Ω, V)}
    (h : ∀ u : 𝓓^{n}(Ω, V), (∫ x, inner 𝕜 (u x) (f x) ∂μ) =
      ∫ x, inner 𝕜 (u x) (g x) ∂μ) : f = g := by
  have hint (a b : 𝓓^{n}(Ω, V)) : Integrable (fun x ↦ inner 𝕜 (a x) (b x)) μ :=
    (a.continuous.inner b.continuous).integrable_of_hasCompactSupport
      (a.hasCompactSupport.mono fun x hx hz ↦ hx (by simp [hz]))
  let d := f - g
  have hz : (∫ x, inner 𝕜 (d x) (d x) ∂μ) = 0 := by
    have he (x : E) : inner 𝕜 (d x) (d x) =
        inner 𝕜 (d x) (f x) - inner 𝕜 (d x) (g x) := inner_sub_right _ _ _
    simp_rw [he]
    rw [integral_sub (hint d f) (hint d g), h d, sub_self]
  have hi : Integrable (fun x ↦ ‖d x‖ ^ 2) μ :=
    (d.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (by
        have hc := d.hasCompactSupport.comp_left
          (g := fun v : V ↦ ‖v‖ ^ 2) (by simp)
        exact hc)
  have hnorm : (∫ x, ‖d x‖ ^ 2 ∂μ) = 0 := by
    have hr := congrArg (RCLike.re : 𝕜 → ℝ) hz
    rw [← integral_re (hint d d)] at hr
    simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow, map_zero] using hr
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg ‖d x‖) hi).mp hnorm
  have hdz : (d : E → V) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hde : (d : E → V) = 0 := (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdz
  apply sub_eq_zero.mp
  apply TestFunction.ext
  intro x
  exact congrFun hde x

end TestFunction
