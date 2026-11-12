/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Basic
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Properly supported truncation of a pseudodifferential operator

The Schwartz kernel `K_a(x, y)` of the Kohn–Nirenberg quantization `Op(a)` of a symbol `a` is in
general supported on all of `ℝⁿ × ℝⁿ`, so `Op(a)` does not map compactly supported functions to
compactly supported functions. Cutting the kernel off near the diagonal repairs this. For a cutoff
`χ : ℝⁿ → ℝ`, the *truncation*

`Op_χ(a) u (x) = Op(a) (χ(x - ·) u) (x)`

(`TauCeti.Symbol.properQuantizeValue`) is the quantization of the amplitude `χ(x - y) a(x, ξ)`, the
operator with kernel `χ(x - y) K_a(x, y)`. This kernel vanishes unless `x - y ∈ tsupport χ`, so for
compactly supported `χ` the truncation is *properly supported*: the output on a compactly supported
input `u` is supported in `tsupport u + tsupport χ`, and the value at `x` only depends on `u` on
`x - tsupport χ`.

If `χ = 1` near `0`, nothing is lost modulo smoothing operators: the removed kernel
`(1 - χ(x - y)) K_a(x, y)` (`TauCeti.Symbol.properRemainderKernel`) vanishes near the diagonal, and
off the diagonal `K_a` is smooth (`TauCeti.Symbol.contDiffOn_offDiagonalKernel`), so the removed
kernel is smooth on all of `ℝⁿ × ℝⁿ`. On compactly supported inputs,

`Op(a) u (x) = Op_χ(a) u (x) + ∫ (1 - χ(x - y)) K_a(x, y) u(y) dy`.

Consequently the truncation maps compactly supported Schwartz functions to compactly supported
smooth functions.

## Main declarations

* `TauCeti.Symbol.properQuantizeValue`: the truncation `Op_χ(a) u (x) = Op(a) (χ(x - ·) u) (x)`,
  with `TauCeti.Symbol.quantizeAmplitudeValue_eq_properQuantizeValue` identifying it with the
  quantization of the amplitude `χ(x - y) a(x, ξ)`.
* `TauCeti.Symbol.properQuantizeValue_congr_right`: **locality**, the value at `x` only depends on
  the input on `x - tsupport χ`.
* `TauCeti.Symbol.support_properQuantizeValue_subset`,
  `TauCeti.Symbol.tsupport_properQuantizeValue_subset` and
  `TauCeti.Symbol.hasCompactSupport_properQuantizeValue`: **proper support**, the output is
  supported in `tsupport u + tsupport χ`, which is compact when `u` and `χ` are compactly supported.
* `TauCeti.Symbol.properQuantizeValue_eq_integral_offDiagonalKernel`: off the support of the input,
  `Op_χ(a) u (x) = ∫ χ(x - y) K_a(x, y) u(y) dy`.
* `TauCeti.Symbol.properRemainderKernel` and `TauCeti.Symbol.contDiff_properRemainderKernel`: the
  removed kernel `(1 - χ(x - y)) K_a(x, y)`, smooth on `ℝⁿ × ℝⁿ` when `χ = 1` near `0`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_properQuantizeValue_add_integral`: **the truncation is
  `Op(a)` modulo a smoothing operator**, `Op(a) u = Op_χ(a) u + ∫ R(·, y) u(y) dy` on compactly
  supported inputs.
* `TauCeti.Symbol.contDiff_properQuantizeValue`: the truncation of a compactly supported input is
  smooth.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
-/

public section

open scoped SchwartzMap ContDiff Pointwise Topology
open MeasureTheory Set Filter Function

noncomputable section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The truncation and its proper support -/

/-- The **truncation near the diagonal** of the quantization of a symbol `a` by a cutoff `χ`:
`Op_χ(a) u (x) = Op(a) (χ(x - ·) u) (x)`. It is the quantization of the amplitude
`χ(x - y) a(x, ξ)` (`TauCeti.Symbol.quantizeAmplitudeValue_eq_properQuantizeValue`), with kernel
`χ(x - y) K_a(x, y)`. For a compactly supported `χ` this operator is properly supported
(`TauCeti.Symbol.hasCompactSupport_properQuantizeValue`), and if moreover `χ = 1` near `0` it
differs from `Op(a)` by an operator with smooth kernel
(`TauCeti.Symbol.quantizeSchwartzValue_eq_properQuantizeValue_add_integral`). If `χ` does not have
temperate growth the multiplication `SchwartzMap.smulLeftCLM` has the junk value `0`. -/
def properQuantizeValue (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) : W :=
  quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x

theorem properQuantizeValue_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    properQuantizeValue a χ u x =
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x :=
  (rfl)

/-- The truncation of the zero input vanishes. -/
@[simp]
theorem properQuantizeValue_zero (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) : properQuantizeValue a χ 0 x = 0 := by
  simp [properQuantizeValue_def]

variable {χ : CoordinateSpace n → ℝ}

private lemma hasTemperateGrowth_sub_left (hχ : χ.HasTemperateGrowth) (x : CoordinateSpace n) :
    (fun y ↦ χ (x - y)).HasTemperateGrowth :=
  hχ.comp (by fun_prop)

/-- Without temperate growth of `χ`, the multiplication by `χ(x - ·)` has the junk value `0`. -/
private lemma smulLeftCLM_sub_left_eq_zero (hχ : ¬χ.HasTemperateGrowth) (x : CoordinateSpace n) :
    SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) = 0 := by
  have hg : ¬(fun y ↦ χ (x - y)).HasTemperateGrowth := fun hg ↦ hχ <| by
    simpa [Function.comp_def] using hg.comp (show (fun y ↦ x - y).HasTemperateGrowth by fun_prop)
  simp [SchwartzMap.smulLeftCLM, hg]

/-- **The truncation as an amplitude quantization.** The truncation `Op_χ(a)` is the quantization
of the amplitude `χ(x - y) a(x, ξ)`. -/
theorem quantizeAmplitudeValue_eq_properQuantizeValue [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχ : χ.HasTemperateGrowth) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeAmplitudeValue (fun p ↦ χ (p.1 - p.2.1) • a.coefficient (p.1, p.2.2)) u x =
      properQuantizeValue a χ u x := by
  rw [properQuantizeValue_def, ← quantizeAmplitudeValue_eq_quantizeSchwartzValue]
  simp only [quantizeAmplitudeValue_def,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_sub_left hχ x),
    smul_apply, ContinuousLinearMap.map_smul_of_tower]

/-- The truncation is additive in the input. -/
theorem properQuantizeValue_add (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    properQuantizeValue a χ (u + v) x = properQuantizeValue a χ u x + properQuantizeValue a χ v x
    := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  simp only [properQuantizeValue_def, map_add]
  exact quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
    hC _ _

/-- The truncation is homogeneous in the input. -/
theorem properQuantizeValue_smul (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ) (c : ℂ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    properQuantizeValue a χ (c • u) x = c • properQuantizeValue a χ u x := by
  by_cases hχ : χ.HasTemperateGrowth
  swap
  · simp [properQuantizeValue_def, smulLeftCLM_sub_left_eq_zero hχ x]
  have hg := hasTemperateGrowth_sub_left hχ x
  have h : SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) (c • u) =
      c • SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply, smul_comm (χ _) c]
  rw [properQuantizeValue_def, h, quantizeSchwartzValue_smul_right, properQuantizeValue_def]

/-- **Locality.** The value of the truncation at `x` only depends on the input on the set
`x - tsupport χ` of points `y` with `x - y ∈ tsupport χ`. -/
theorem properQuantizeValue_congr_right (a : Symbol n V W m) {u v : 𝓢(CoordinateSpace n, V)}
    {x : CoordinateSpace n} (h : ∀ y, x - y ∈ tsupport χ → u y = v y) :
    properQuantizeValue a χ u x = properQuantizeValue a χ v x := by
  by_cases hχ : χ.HasTemperateGrowth
  · have hg := hasTemperateGrowth_sub_left hχ x
    rw [properQuantizeValue_def, properQuantizeValue_def]
    congr 1
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg]
    by_cases hy : x - y ∈ tsupport χ
    · rw [h y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [properQuantizeValue_def, smulLeftCLM_sub_left_eq_zero hχ x]

/-- **Proper support.** The truncation vanishes at `x` unless `x = y + z` for a point `y` of
`tsupport u` and a point `z` of `tsupport χ`. -/
theorem support_properQuantizeValue_subset (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) :
    support (properQuantizeValue a χ u) ⊆ tsupport u + tsupport χ := by
  intro x hx
  by_contra hmem
  have h0 : properQuantizeValue a χ u x = properQuantizeValue a χ 0 x :=
    properQuantizeValue_congr_right a fun y hy ↦
      image_eq_zero_of_notMem_tsupport fun hyu ↦ hmem ⟨y, hyu, x - y, hy, add_sub_cancel y x⟩
  exact hx (h0.trans (properQuantizeValue_zero a χ x))

/-- **Proper support.** The truncation of a compactly supported input is supported in
`tsupport u + tsupport χ`. -/
theorem tsupport_properQuantizeValue_subset (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    tsupport (properQuantizeValue a χ u) ⊆ tsupport u + tsupport χ :=
  closure_minimal (support_properQuantizeValue_subset a χ u)
    ((isClosed_tsupport χ).add_left_of_isCompact hu)

/-- **Proper support.** For a compactly supported cutoff `χ`, the truncation maps compactly
supported inputs to compactly supported outputs. -/
theorem hasCompactSupport_properQuantizeValue (a : Symbol n V W m) (hχc : HasCompactSupport χ)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    HasCompactSupport (properQuantizeValue a χ u) :=
  (hu.isCompact.add hχc.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_properQuantizeValue_subset a χ hu)

/-- **The kernel of the truncation off the diagonal.** For a smooth compactly supported cutoff
`χ`, if the input `u` vanishes near `x`, then `Op_χ(a) u (x) = ∫ χ(x - y) K_a(x, y) u(y) dy`,
where `K_a` is the off-diagonal kernel of `Op(a)`. -/
theorem properQuantizeValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {u : 𝓢(CoordinateSpace n, V)} {x : CoordinateSpace n} (hx : x ∉ tsupport u) :
    properQuantizeValue a χ u x = ∫ y, (χ (x - y) • offDiagonalKernel a x y) (u y) := by
  have hg := hasTemperateGrowth_sub_left (hχc.hasTemperateGrowth hχ) x
  set w := SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u
  have hsub := SchwartzMap.tsupport_smulLeftCLM_subset (F := V) (fun y ↦ χ (x - y)) u
  have hwc : HasCompactSupport w :=
    (hχc.comp_homeomorph (Homeomorph.subLeft x)).of_isClosed_subset (isClosed_tsupport _)
      (hsub.trans inter_subset_right)
  rw [properQuantizeValue_def, a.quantizeSchwartzValue_eq_integral_offDiagonalKernel hwc
    fun hxw ↦ hx (hsub hxw).1]
  congr 1 with y
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply,
    ContinuousLinearMap.map_smul_of_tower]

/-! ### The removed kernel -/

/-- The kernel `(1 - χ(x - y)) K_a(x, y)` removed from `Op(a)` by the truncation `Op_χ(a)`, where
`K_a` is the off-diagonal kernel `TauCeti.Symbol.offDiagonalKernel` of `Op(a)`. When `χ = 1` near
`0` it is smooth on `ℝⁿ × ℝⁿ` (`TauCeti.Symbol.contDiff_properRemainderKernel`), so `Op(a)` and
`Op_χ(a)` differ by a smoothing operator
(`TauCeti.Symbol.quantizeSchwartzValue_eq_properQuantizeValue_add_integral`). -/
def properRemainderKernel (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x y : CoordinateSpace n) : V →L[ℂ] W :=
  (1 - χ (x - y)) • offDiagonalKernel a x y

theorem properRemainderKernel_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x y : CoordinateSpace n) :
    properRemainderKernel a χ x y = (1 - χ (x - y)) • offDiagonalKernel a x y :=
  (rfl)

/-- The removed kernel vanishes where `χ(x - y) = 1`, in particular near the diagonal. -/
theorem properRemainderKernel_eq_zero (a : Symbol n V W m) {x y : CoordinateSpace n}
    (h : χ (x - y) = 1) : properRemainderKernel a χ x y = 0 := by
  simp [properRemainderKernel_def, h]

/-- The removed kernel is the whole off-diagonal kernel where `χ(x - y) = 0`. -/
theorem properRemainderKernel_eq_offDiagonalKernel (a : Symbol n V W m) {x y : CoordinateSpace n}
    (h : χ (x - y) = 0) : properRemainderKernel a χ x y = offDiagonalKernel a x y := by
  simp [properRemainderKernel_def, h]

/-- **The removed kernel is smooth.** If `χ` is smooth and equal to `1` near `0`, then
`(1 - χ(x - y)) K_a(x, y)` is smooth on `ℝⁿ × ℝⁿ`: it vanishes near the diagonal, and off the
diagonal `K_a` is smooth. -/
theorem contDiff_properRemainderKernel (a : Symbol n V W m) (hχ : ContDiff ℝ ∞ χ)
    (hχ1 : χ =ᶠ[𝓝 0] 1) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ properRemainderKernel a χ p.1 p.2
    := by
  refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
  have hsub : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2 := by fun_prop
  rcases eq_or_ne p.1 p.2 with hp | hp
  · -- Near the diagonal, `χ(x - y) = 1`, so the kernel vanishes.
    have ht : Tendsto (fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) (𝓝 p) (𝓝 0) := by
      simpa [hp] using hsub.tendsto p
    refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [ht.eventually hχ1] with q hq
    exact properRemainderKernel_eq_zero a hq
  · have hopen : IsOpen {q : CoordinateSpace n × CoordinateSpace n | q.1 ≠ q.2} :=
      isOpen_ne_fun continuous_fst continuous_snd
    have hK := (contDiffOn_offDiagonalKernel a).contDiffAt (hopen.mem_nhds hp)
    have hc : ContDiffAt ℝ ∞ (fun q : CoordinateSpace n × CoordinateSpace n ↦ 1 - χ (q.1 - q.2))
        p := (contDiff_const.sub (hχ.comp (contDiff_fst.sub contDiff_snd))).contDiffAt
    exact hc.smul (by simpa only [uncurry_def] using hK)

/-- **The truncation is `Op(a)` modulo a smoothing operator.** If `χ` has temperate growth and
`χ = 1` near `0`, then on a compactly supported input
`Op(a) u (x) = Op_χ(a) u (x) + ∫ (1 - χ(x - y)) K_a(x, y) u(y) dy`, where the kernel of the last
term is smooth (`TauCeti.Symbol.contDiff_properRemainderKernel`). -/
theorem quantizeSchwartzValue_eq_properQuantizeValue_add_integral [CompleteSpace V]
    [CompleteSpace W] (a : Symbol n V W m) (hχ : χ.HasTemperateGrowth) (hχ1 : χ =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient u x =
      properQuantizeValue a χ u x + ∫ y, properRemainderKernel a χ x y (u y) := by
  have hg := hasTemperateGrowth_sub_left hχ x
  have hg' : (fun y ↦ 1 - χ (x - y)).HasTemperateGrowth := by fun_prop
  set w := SchwartzMap.smulLeftCLM V (fun y ↦ 1 - χ (x - y)) u
  have hsplit : u = SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u + w := by
    ext y
    simp only [w, add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
      SchwartzMap.smulLeftCLM_apply_apply hg', sub_smul, one_smul, add_sub_cancel]
  have hwc : HasCompactSupport w :=
    hu.of_isClosed_subset (isClosed_tsupport _)
      ((SchwartzMap.tsupport_smulLeftCLM_subset _ u).trans inter_subset_left)
  -- `w` vanishes near `x`, where `χ(x - y) = 1`.
  have hxw : x ∉ tsupport w := by
    refine notMem_tsupport_iff_eventuallyEq.2 ?_
    have ht : Tendsto (fun y : CoordinateSpace n ↦ x - y) (𝓝 x) (𝓝 0) := by
      simpa using (continuous_sub_left x).tendsto x
    filter_upwards [ht.eventually hχ1] with y hy
    simp [w, SchwartzMap.smulLeftCLM_apply_apply hg', hy]
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  conv_lhs => rw [hsplit]
  rw [quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable hC,
    ← properQuantizeValue_def, a.quantizeSchwartzValue_eq_integral_offDiagonalKernel hwc hxw]
  congr 1
  congr 1 with y
  rw [SchwartzMap.smulLeftCLM_apply_apply hg', properRemainderKernel_def,
    smul_apply, ContinuousLinearMap.map_smul_of_tower]

/-- The removed part `x ↦ ∫ (1 - χ(x - y)) K_a(x, y) u(y) dy` of a compactly supported input is
smooth, since its kernel is smooth (`TauCeti.Symbol.contDiff_properRemainderKernel`). -/
theorem contDiff_integral_properRemainderKernel (a : Symbol n V W m) (hχ : ContDiff ℝ ∞ χ)
    (hχ1 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    ContDiff ℝ ∞ fun x ↦ ∫ y, properRemainderKernel a χ x y (u y) := by
  have hF : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦
      properRemainderKernel a χ p.1 p.2 (u p.2) := by
    -- Apply the kernel as a real-linear map.
    have hR := (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.comp
      (contDiff_properRemainderKernel a hχ hχ1)
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars'] using
      hR.clm_apply ((u.smooth ⊤).comp contDiff_snd)
  have h := ContDiffOn.parametric_integral (𝕜 := ℝ) (μ := volume)
    (f := fun x y ↦ properRemainderKernel a χ x y (u y)) isOpen_univ hu subset_rfl
    hF.contDiffOn hu.isCompact.measure_lt_top.ne
  refine contDiffOn_univ.1 (h.congr fun x _ ↦ ?_)
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_).symm
  rw [image_eq_zero_of_notMem_tsupport hy, map_zero]

/-- **Smoothness.** If `χ` has temperate growth and `χ = 1` near `0`, the truncation of a
compactly supported input is smooth; together with
`TauCeti.Symbol.hasCompactSupport_properQuantizeValue`, a compactly supported cutoff maps
compactly supported inputs to compactly supported smooth functions. -/
theorem contDiff_properQuantizeValue [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hχ : χ.HasTemperateGrowth) (hχ1 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport u) : ContDiff ℝ ∞ (properQuantizeValue a χ u) := by
  have h : properQuantizeValue a χ u = fun x ↦
      quantizeSchwartzValue a.coefficient u x - ∫ y, properRemainderKernel a χ x y (u y) := by
    funext x
    rw [quantizeSchwartzValue_eq_properQuantizeValue_add_integral a hχ hχ1 hu x,
      add_sub_cancel_right]
  rw [h]
  exact (a.contDiff_quantizeSchwartzValue u).sub
    (contDiff_integral_properRemainderKernel a hχ.1 hχ1 hu)

end Symbol

end TauCeti
