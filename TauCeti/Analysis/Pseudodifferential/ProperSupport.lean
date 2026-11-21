/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Basic
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Properly supported truncations of pseudodifferential operators

The Kohn–Nirenberg quantization `Op(a)` of a symbol `a` on `ℝⁿ` has a Schwartz kernel whose
support is in general all of `ℝⁿ × ℝⁿ`, so `Op(a)` does not preserve compact supports. Cutting
the kernel off near the diagonal repairs this at the cost of a smoothing error. Fix a cutoff
`ψ : ℝⁿ → ℝ` and put

`Op_ψ(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) ψ(x - y) a(x, ξ) u(y) dy dξ`,

the quantization of the amplitude `ψ(x - y) a(x, ξ)`. Equivalently, `Op_ψ(a) u (x)` is
`Op(a)` applied to the input `ψ(x - ·) u` and evaluated at `x`; this is the definition of
`TauCeti.Symbol.quantizeProperValue`.

If `ψ` has compact support, `Op_ψ(a) u (x)` only depends on `u` on `x - tsupport ψ`, so
`Op_ψ(a)` is properly supported: it sends a function supported in `L` to one supported in the
compact set `L + tsupport ψ`. If `ψ` is smooth of temperate growth and equal to `1` near `0`,
then the removed part `Op(a) - Op_ψ(a)` is the integral operator with kernel
`(1 - ψ(x - y)) K(x, y)`, where `K` is the off-diagonal kernel of `Op(a)`
(`TauCeti.Symbol.offDiagonalKernel`); this kernel vanishes near the diagonal and is smooth
everywhere. For a smooth compactly supported cutoff equal to `1` near `0`, `Op_ψ(a)` therefore
maps compactly supported Schwartz functions, that is test functions, to test functions.

## Main declarations

* `TauCeti.Symbol.quantizeProperValue`: the truncated quantization `Op_ψ(a)`, and
  `TauCeti.Symbol.quantizeAmplitudeValue_eq_quantizeProperValue`, identifying it with the
  quantization of the amplitude `ψ(x - y) a(x, ξ)`.
* `TauCeti.Symbol.quantizeProperValue_congr` and
  `TauCeti.Symbol.support_quantizeProperValue_subset`: `Op_ψ(a) u (x)` only depends on `u` on
  `x - tsupport ψ`, and the support of `Op_ψ(a) u` lies in `tsupport u + tsupport ψ`; in
  particular `Op_ψ(a) u` has compact support when `u` and `ψ` do
  (`TauCeti.Symbol.hasCompactSupport_quantizeProperValue`).
* `TauCeti.Symbol.truncationKernel`: the kernel `(1 - ψ(x - y)) K(x, y)` of the removed part,
  smooth on all of `ℝⁿ × ℝⁿ` (`TauCeti.Symbol.contDiff_truncationKernel`).
* `TauCeti.Symbol.quantizeSchwartzValue_eq_quantizeProperValue_add_integral`: **the truncation
  identity** `Op(a) u (x) = Op_ψ(a) u (x) + ∫ (1 - ψ(x - y)) K(x, y) u(y) dy` for compactly
  supported `u`.
* `TauCeti.Symbol.contDiff_quantizeProperValue`: `Op_ψ(a) u` is smooth for compactly supported
  `u`.
* `TauCeti.Symbol.quantizeProperTestFunction`: `Op_ψ(a)` as a linear map between the spaces of
  test functions `𝓓(ℝⁿ, V) → 𝓓(ℝⁿ, W)`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Function Filter Set TopologicalSpace
open scoped ContDiff SchwartzMap Topology Pointwise Distributions

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### The truncated quantization -/

/-- The **truncation of the quantization of `a` by the cutoff `ψ`** near the diagonal, on a
Schwartz function `u` and at the output position `x`:
`Op_ψ(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) ψ(x - y) a(x, ξ) u(y) dy dξ`, defined as the
quantization of `a` applied to the input `ψ(x - ·) u` and evaluated at `x`. When `ψ` does not have
temperate growth, the multiplication by `ψ(x - ·)` has the junk value `0`. -/
def quantizeProperValue (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) : W :=
  quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ ψ (x - y)) u) x

theorem quantizeProperValue_def (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    a.quantizeProperValue ψ u x =
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ ψ (x - y)) u) x :=
  (rfl)

variable {ψ : CoordinateSpace n → ℝ}

/-- **Amplitude form.** For a cutoff `ψ` of temperate growth, the truncated quantization is the
quantization of the amplitude `ψ(x - y) a(x, ξ)`. -/
theorem quantizeAmplitudeValue_eq_quantizeProperValue [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hψ : ψ.HasTemperateGrowth) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeAmplitudeValue (fun p ↦ ψ (p.1 - p.2.1) • a.coefficient (p.1, p.2.2)) u x =
      a.quantizeProperValue ψ u x := by
  have hg : (fun y ↦ ψ (x - y)).HasTemperateGrowth := by fun_prop
  rw [quantizeProperValue_def, ← quantizeAmplitudeValue_eq_quantizeSchwartzValue]
  simp only [quantizeAmplitudeValue_def, SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_apply, ContinuousLinearMap.map_smul_of_tower]

/-- With the constant cutoff `1` nothing is removed: `Op_1(a) = Op(a)`. -/
@[simp]
theorem quantizeProperValue_one (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    a.quantizeProperValue 1 u x = quantizeSchwartzValue a.coefficient u x := by
  simp [quantizeProperValue_def, Pi.one_def, SchwartzMap.smulLeftCLM_const]

/-- The truncated quantization is additive in the input. -/
theorem quantizeProperValue_add_right (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (u v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    a.quantizeProperValue ψ (u + v) x = a.quantizeProperValue ψ u x + a.quantizeProperValue ψ v x
    := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  simp only [quantizeProperValue_def, map_add]
  exact quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable hC
    _ _

/-- The truncated quantization is homogeneous in the input. -/
@[simp]
theorem quantizeProperValue_smul_right (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ) (c : ℂ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    a.quantizeProperValue ψ (c • u) x = c • a.quantizeProperValue ψ u x := by
  rw [quantizeProperValue_def, quantizeProperValue_def, ← quantizeSchwartzValue_smul_right]
  congr 1
  by_cases hψ : (fun y ↦ ψ (x - y)).HasTemperateGrowth
  · ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hψ, smul_apply, smul_comm (ψ _) c]
  · simp [SchwartzMap.smulLeftCLM, hψ]

/-- The truncated quantization is additive in the symbol. -/
theorem quantizeProperValue_add_left (a b : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    (a + b).quantizeProperValue ψ u x = a.quantizeProperValue ψ u x + b.quantizeProperValue ψ u x
    := by
  simp only [quantizeProperValue_def, coefficient_add, quantizeSchwartzValue_coefficient_add]

/-- The truncated quantization is homogeneous in the symbol. -/
@[simp]
theorem quantizeProperValue_smul_left (c : ℂ) (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    (c • a).quantizeProperValue ψ u x = c • a.quantizeProperValue ψ u x := by
  simp only [quantizeProperValue_def, coefficient_smul, quantizeSchwartzValue_smul_left]

/-! ### Proper support -/

/-- **Locality.** `Op_ψ(a) u (x)` only depends on the values of `u` on `x - tsupport ψ`. -/
theorem quantizeProperValue_congr (a : Symbol n V W m) {u v : 𝓢(CoordinateSpace n, V)}
    {x : CoordinateSpace n} (h : ∀ y, x - y ∈ tsupport ψ → u y = v y) :
    a.quantizeProperValue ψ u x = a.quantizeProperValue ψ v x := by
  rw [quantizeProperValue_def, quantizeProperValue_def]
  congr 1
  by_cases hψ : (fun y ↦ ψ (x - y)).HasTemperateGrowth
  · ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hψ, SchwartzMap.smulLeftCLM_apply_apply hψ]
    by_cases hy : x - y ∈ tsupport ψ
    · rw [h y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [SchwartzMap.smulLeftCLM, hψ]

/-- **Proper support.** The support of `Op_ψ(a) u` lies in `tsupport u + tsupport ψ`. -/
theorem support_quantizeProperValue_subset (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) :
    support (a.quantizeProperValue ψ u) ⊆ tsupport u + tsupport ψ := by
  intro x hx
  by_contra h
  refine hx ?_
  rw [a.quantizeProperValue_congr (v := 0) fun y hy ↦ ?_, quantizeProperValue_def, map_zero,
    quantizeSchwartzValue_zero_right]
  exact image_eq_zero_of_notMem_tsupport fun hu ↦ h ⟨y, hu, x - y, hy, add_sub_cancel y x⟩

/-- If `u` and the cutoff `ψ` have compact support, then so does `Op_ψ(a) u`. -/
theorem hasCompactSupport_quantizeProperValue (a : Symbol n V W m) (hψ : HasCompactSupport ψ)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    HasCompactSupport (a.quantizeProperValue ψ u) :=
  (hu.isCompact.add hψ.isCompact).of_isClosed_subset isClosed_closure <|
    closure_minimal (a.support_quantizeProperValue_subset ψ u)
      (hu.isCompact.add hψ.isCompact).isClosed

/-! ### The removed kernel -/

/-- The kernel `(1 - ψ(x - y)) K(x, y)` removed from `Op(a)` by the truncation with the cutoff
`ψ`, where `K` is the off-diagonal kernel `TauCeti.Symbol.offDiagonalKernel a` of `Op(a)`. -/
def truncationKernel (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ) (x y : CoordinateSpace n) :
    V →L[ℂ] W :=
  (1 - ψ (x - y)) • offDiagonalKernel a x y

theorem truncationKernel_def (a : Symbol n V W m) (ψ : CoordinateSpace n → ℝ)
    (x y : CoordinateSpace n) :
    a.truncationKernel ψ x y = (1 - ψ (x - y)) • offDiagonalKernel a x y :=
  (rfl)

/-- **The removed kernel is smooth.** For a smooth cutoff `ψ` equal to `1` near `0`, the kernel
`(1 - ψ(x - y)) K(x, y)` vanishes near the diagonal and is smooth on all of `ℝⁿ × ℝⁿ`. -/
theorem contDiff_truncationKernel (a : Symbol n V W m) (hψ : ContDiff ℝ ∞ ψ)
    (hψ₁ : ψ =ᶠ[𝓝 0] 1) : ContDiff ℝ ∞ (uncurry (a.truncationKernel ψ)) := by
  refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
  by_cases hp : p.1 = p.2
  · -- Near the diagonal the cutoff is `1`, so the kernel vanishes identically.
    have hsub : Tendsto (fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) (𝓝 p)
        (𝓝 0) :=
      (continuous_fst.sub continuous_snd).tendsto' p 0 (by simp [hp])
    refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [hsub.eventually hψ₁] with ⟨q₁, q₂⟩ hq
    simp only [Pi.one_apply] at hq
    simp [truncationKernel_def, hq]
  · have ho : IsOpen {q : CoordinateSpace n × CoordinateSpace n | q.1 ≠ q.2} :=
      isOpen_ne_fun continuous_fst continuous_snd
    exact (contDiff_const.sub (hψ.comp (contDiff_fst.sub contDiff_snd))).contDiffAt.smul
      ((a.contDiffOn_offDiagonalKernel).contDiffAt (ho.mem_nhds hp))

/-! ### The truncation identity -/

/-- **The truncation identity.** For a cutoff `ψ` of temperate growth equal to `1` near `0` and a
compactly supported Schwartz function `u`,
`Op(a) u (x) = Op_ψ(a) u (x) + ∫ (1 - ψ(x - y)) K(x, y) u(y) dy`, with `K` the off-diagonal kernel
of `Op(a)`. -/
theorem quantizeSchwartzValue_eq_quantizeProperValue_add_integral [CompleteSpace V]
    [CompleteSpace W] (a : Symbol n V W m) (hψ : ψ.HasTemperateGrowth) (hψ₁ : ψ =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient u x =
      a.quantizeProperValue ψ u x + ∫ y, a.truncationKernel ψ x y (u y) := by
  have hg : (fun y ↦ ψ (x - y)).HasTemperateGrowth := by fun_prop
  have hg' : (fun y ↦ 1 - ψ (x - y)).HasTemperateGrowth := by fun_prop
  set w := SchwartzMap.smulLeftCLM V (fun y ↦ 1 - ψ (x - y)) u
  have hw : ⇑w = fun y ↦ (1 - ψ (x - y)) • u y := SchwartzMap.smulLeftCLM_apply hg' u
  have hsplit : u = SchwartzMap.smulLeftCLM V (fun y ↦ ψ (x - y)) u + w := by
    ext y
    simp [hw, SchwartzMap.smulLeftCLM_apply_apply hg, sub_smul]
  -- The second part vanishes near `x`, so its kernel is the off-diagonal kernel.
  have hwc : HasCompactSupport w := by
    rw [hw]
    exact hu.smul_left
  have hxw : x ∉ tsupport w := by
    have hsub : Tendsto (fun y ↦ x - y) (𝓝 x) (𝓝 0) :=
      (continuous_const.sub continuous_id).tendsto' x 0 (sub_self x)
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [hsub.eventually hψ₁] with y hy
    simp [hw, hy]
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  conv_lhs => rw [hsplit]
  rw [quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable hC,
    quantizeSchwartzValue_eq_integral_offDiagonalKernel a hwc hxw, quantizeProperValue_def]
  congr 1
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp [hw, truncationKernel_def, ContinuousLinearMap.map_smul_of_tower]

/-- **Smoothness.** For a cutoff `ψ` of temperate growth equal to `1` near `0`, the truncated
quantization `Op_ψ(a) u` of a compactly supported Schwartz function `u` is smooth. -/
theorem contDiff_quantizeProperValue [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hψ : ψ.HasTemperateGrowth) (hψ₁ : ψ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport u) : ContDiff ℝ ∞ (a.quantizeProperValue ψ u) := by
  have heq : a.quantizeProperValue ψ u = fun x ↦ quantizeSchwartzValue a.coefficient u x -
      ∫ y in tsupport u, a.truncationKernel ψ x y (u y) := by
    funext x
    rw [a.quantizeSchwartzValue_eq_quantizeProperValue_add_integral hψ hψ₁ hu x,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
        simp [image_eq_zero_of_notMem_tsupport hy], add_sub_cancel_right]
  -- Restrict the kernel to real scalars, since smoothness is over the real base.
  have hR := (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.comp
    (a.contDiff_truncationKernel hψ.1 hψ₁)
  have hK : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦
      uncurry (a.truncationKernel ψ) p (u p.2) := by
    simpa only [Function.comp_apply, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars'] using hR.clm_apply ((u.smooth ⊤).comp contDiff_snd)
  rw [heq]
  exact (a.contDiff_quantizeSchwartzValue u).sub
    (hK.parametric_integral hu.isCompact subset_rfl hu.isCompact.measure_lt_top.ne)

/-- **Independence of the cutoff modulo smoothing.** For two cutoffs `ψ`, `ψ'` of temperate growth
equal to `1` near `0` and a compactly supported Schwartz function `u`, the truncations differ by the
integral operator with the kernel `(ψ(x - y) - ψ'(x - y)) K(x, y)`, the difference of the two
removed kernels, which is smooth by `TauCeti.Symbol.contDiff_truncationKernel`. -/
theorem quantizeProperValue_sub_quantizeProperValue [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) {ψ' : CoordinateSpace n → ℝ} (hψ : ψ.HasTemperateGrowth)
    (hψ₁ : ψ =ᶠ[𝓝 0] 1) (hψ' : ψ'.HasTemperateGrowth) (hψ'₁ : ψ' =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) (x : CoordinateSpace n) :
    a.quantizeProperValue ψ u x - a.quantizeProperValue ψ' u x =
      ∫ y, (a.truncationKernel ψ' x y - a.truncationKernel ψ x y) (u y) := by
  have hint {φ : CoordinateSpace n → ℝ} (hφ : φ.HasTemperateGrowth) (hφ₁ : φ =ᶠ[𝓝 0] 1) :
      Integrable fun y ↦ a.truncationKernel φ x y (u y) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hu.mono (support_subset_iff'.2
      fun y hy ↦ by rw [notMem_support.1 hy, map_zero]))
    exact ((a.contDiff_truncationKernel hφ.1 hφ₁).continuous.comp
      (continuous_const.prodMk continuous_id)).clm_apply u.continuous
  have h := a.quantizeSchwartzValue_eq_quantizeProperValue_add_integral hψ hψ₁ hu x
  rw [a.quantizeSchwartzValue_eq_quantizeProperValue_add_integral hψ' hψ'₁ hu x] at h
  simp only [sub_apply]
  rw [integral_sub (hint hψ' hψ'₁) (hint hψ hψ₁)]
  linear_combination (norm := module) h.symm

/-! ### The truncated quantization on test functions -/

/-- The **truncated quantization on test functions**: for a smooth compactly supported cutoff `ψ`
equal to `1` near `0`, `Op_ψ(a)` maps test functions on `ℝⁿ` to test functions, linearly. -/
def quantizeProperTestFunction [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ₁ : ψ =ᶠ[𝓝 0] 1) :
    𝓓((⊤ : Opens (CoordinateSpace n)), V) →ₗ[ℂ]
      𝓓((⊤ : Opens (CoordinateSpace n)), W) where
  toFun f := ⟨a.quantizeProperValue ψ (f.hasCompactSupport.toSchwartzMap f.contDiff),
    a.contDiff_quantizeProperValue (hψc.hasTemperateGrowth hψ) hψ₁ f.hasCompactSupport,
    a.hasCompactSupport_quantizeProperValue hψc f.hasCompactSupport, by simp⟩
  map_add' f g := by
    have h : (f + g).hasCompactSupport.toSchwartzMap (f + g).contDiff =
        f.hasCompactSupport.toSchwartzMap f.contDiff +
          g.hasCompactSupport.toSchwartzMap g.contDiff := by
      ext y
      simp only [HasCompactSupport.toSchwartzMap_toFun, add_apply]
    ext x
    simp only [TestFunction.coe_mk, add_apply, h, quantizeProperValue_add_right]
  map_smul' c f := by
    have h : (c • f).hasCompactSupport.toSchwartzMap (c • f).contDiff =
        c • f.hasCompactSupport.toSchwartzMap f.contDiff := by
      ext y
      simp only [HasCompactSupport.toSchwartzMap_toFun, smul_apply]
    ext x
    simp only [TestFunction.coe_mk, smul_apply, RingHom.id_apply, h,
      quantizeProperValue_smul_right]

/-- Evaluation of the truncated quantization on a test function. -/
@[simp]
theorem quantizeProperTestFunction_apply [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ₁ : ψ =ᶠ[𝓝 0] 1)
    (f : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) (x : CoordinateSpace n) :
    a.quantizeProperTestFunction hψ hψc hψ₁ f x =
      a.quantizeProperValue ψ (f.hasCompactSupport.toSchwartzMap f.contDiff) x :=
  (rfl)

end Symbol

end TauCeti
