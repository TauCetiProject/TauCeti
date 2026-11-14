/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Basic
public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.ContDiff.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Properly supported truncation of a pseudodifferential operator

The Schwartz kernel `K_a(x, y)` of the Kohn–Nirenberg quantization `Op(a)` of a symbol `a` is in
general supported on all of `ℝⁿ × ℝⁿ`, so `Op(a)` does not map compactly supported functions to
compactly supported functions. Cutting the kernel off near the diagonal repairs this. For a cutoff
`χ : ℝⁿ → ℝ`, the *truncation*

`Op_χ(a) u (x) = Op(a) (χ(x - ·) u) (x)`

(`TauCeti.Symbol.quantizeCutoffValue`) is, when `χ` has temperate growth, the quantization of the
amplitude `χ(x - y) a(x, ξ)`, the operator with kernel `χ(x - y) K_a(x, y)`. This kernel vanishes
unless `x - y ∈ support χ`, so for compactly supported `χ` the truncation is *properly supported*:
the output on an input `u` is supported in `tsupport u + tsupport χ`, and the value at `x` only
depends on `u` on `x - support χ`.

If `χ` is smooth and `χ = 1` near `0`, nothing is lost modulo smoothing operators: the removed
kernel `(1 - χ(x - y)) K_a(x, y)` (`TauCeti.Symbol.cutoffRemainderKernel`) vanishes near the
diagonal, and off the diagonal `K_a` is smooth (`TauCeti.Symbol.contDiffOn_offDiagonalKernel`), so
the removed kernel is smooth on all of `ℝⁿ × ℝⁿ`. If moreover `χ` has temperate growth, then on
compactly supported inputs

`Op(a) u (x) = Op_χ(a) u (x) + ∫ (1 - χ(x - y)) K_a(x, y) u(y) dy`.

Consequently a smooth compactly supported cutoff `χ` equal to `1` near `0` maps compactly supported
Schwartz functions to compactly supported smooth functions.

## Main declarations

* `TauCeti.Symbol.quantizeCutoffValue`: the truncation `Op_χ(a) u (x) = Op(a) (χ(x - ·) u) (x)`,
  with `TauCeti.Symbol.quantizeAmplitudeValue_eq_quantizeCutoffValue` identifying it, for `χ` of
  temperate growth, with the quantization of the amplitude `χ(x - y) a(x, ξ)`.
* `TauCeti.Symbol.quantizeCutoffValue_congr_right`: the input-side half of proper support, the
  value at `x` only depends on the input on `x - support χ`.
* `TauCeti.Symbol.support_quantizeCutoffValue_subset`,
  `TauCeti.Symbol.tsupport_quantizeCutoffValue_subset` and
  `TauCeti.Symbol.hasCompactSupport_quantizeCutoffValue`: the output-side half of proper support,
  the output is supported in `support u + support χ`, which has compact closure when `u` and `χ`
  are compactly supported.
* `TauCeti.Symbol.quantizeCutoffValue_eq_integral_offDiagonalKernel`: off the support of the input,
  or for `χ` vanishing near `0`, `Op_χ(a) u (x) = ∫ χ(x - y) K_a(x, y) u(y) dy`.
* `TauCeti.Symbol.cutoffRemainderKernel` and `TauCeti.Symbol.contDiff_cutoffRemainderKernel`: the
  removed kernel `(1 - χ(x - y)) K_a(x, y)`, smooth on `ℝⁿ × ℝⁿ` when `χ` is smooth and `χ = 1`
  near `0`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_quantizeCutoffValue_add_integral`: **the truncation is
  `Op(a)` modulo a smoothing operator**, `Op(a) u = Op_χ(a) u + ∫ R(·, y) u(y) dy` on compactly
  supported inputs, for `χ` of temperate growth with `χ = 1` near `0`.
* `TauCeti.Symbol.contDiff_quantizeCutoffValue`: for `χ` of temperate growth with `χ = 1` near
  `0`, the truncation of an input is smooth when the input or `χ` is compactly supported.

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
`Op_χ(a) u (x) = Op(a) (χ(x - ·) u) (x)`. For `χ` of temperate growth it is the quantization of the
amplitude `χ(x - y) a(x, ξ)` (`TauCeti.Symbol.quantizeAmplitudeValue_eq_quantizeCutoffValue`), with
kernel `χ(x - y) K_a(x, y)`. For a compactly supported `χ` this operator is properly supported
(`TauCeti.Symbol.hasCompactSupport_quantizeCutoffValue`), and if `χ` has temperate growth and
`χ = 1` near `0` it differs from `Op(a)` by an operator with smooth kernel
(`TauCeti.Symbol.quantizeSchwartzValue_eq_quantizeCutoffValue_add_integral`). If `χ` does not have
temperate growth the multiplication `SchwartzMap.smulLeftCLM` has the junk value `0`
(`TauCeti.Symbol.quantizeCutoffValue_of_not_hasTemperateGrowth`). -/
def quantizeCutoffValue (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) : W :=
  quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x

theorem quantizeCutoffValue_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeCutoffValue a χ u x =
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x :=
  (rfl)

/-- Without temperate growth of `χ`, the truncation has the junk value `0`. -/
theorem quantizeCutoffValue_of_not_hasTemperateGrowth (a : Symbol n V W m)
    {χ : CoordinateSpace n → ℝ} (hχ : ¬χ.HasTemperateGrowth) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) : quantizeCutoffValue a χ u x = 0 := by
  simp [quantizeCutoffValue_def, SchwartzMap.smulLeftCLM_of_not_hasTemperateGrowth,
    hasTemperateGrowth_comp_sub_left_iff, hχ]

/-- The truncation by the cutoff `0` vanishes. -/
@[simp]
theorem quantizeCutoffValue_zero_cutoff (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) : quantizeCutoffValue a 0 u x = 0 := by
  simp [quantizeCutoffValue_def]

/-- The truncation by the cutoff `1` is the untruncated quantization `Op(a)`. -/
@[simp]
theorem quantizeCutoffValue_one_cutoff (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) : quantizeCutoffValue a 1 u x = quantizeSchwartzValue a.coefficient u x
    := by
  simp [quantizeCutoffValue_def]

/-- The truncation of the zero input vanishes. -/
@[simp]
theorem quantizeCutoffValue_zero_right (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) : quantizeCutoffValue a χ 0 x = 0 := by
  simp [quantizeCutoffValue_def]

/-- The truncation of the zero symbol vanishes. -/
@[simp]
theorem quantizeCutoffValue_zero_left (χ : CoordinateSpace n → ℝ) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) : quantizeCutoffValue (0 : Symbol n V W m) χ u x = 0 := by
  rw [quantizeCutoffValue_def, coefficient_zero, quantizeSchwartzValue_zero_left]

/-- The truncation is additive in the symbol. -/
theorem quantizeCutoffValue_add_left (a b : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeCutoffValue (a + b) χ u x = quantizeCutoffValue a χ u x + quantizeCutoffValue b χ u x
    := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  obtain ⟨C', -, hC'⟩ := b.exists_bound_coefficient_slice x
  simp only [quantizeCutoffValue_def, coefficient_add]
  exact quantizeSchwartzValue_add_left (a.continuous_coefficient_slice x).aestronglyMeasurable hC
    (b.continuous_coefficient_slice x).aestronglyMeasurable hC' _

/-- The truncation is homogeneous in the symbol. -/
@[simp]
theorem quantizeCutoffValue_smul_left (c : ℂ) (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeCutoffValue (c • a) χ u x = c • quantizeCutoffValue a χ u x := by
  simp only [quantizeCutoffValue_def, coefficient_smul, quantizeSchwartzValue_smul_left]

/-- The truncation does not depend on the order at which the symbol is considered. -/
@[simp]
theorem quantizeCutoffValue_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m)
    (χ : CoordinateSpace n → ℝ) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeCutoffValue (inclusion h a) χ u x = quantizeCutoffValue a χ u x := by
  simp only [quantizeCutoffValue_def, coefficient_inclusion]

/-- The truncation is additive in the input. -/
theorem quantizeCutoffValue_add_right (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeCutoffValue a χ (u + v) x = quantizeCutoffValue a χ u x + quantizeCutoffValue a χ v x
    := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  simp only [quantizeCutoffValue_def, map_add]
  exact quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
    hC _ _

variable {χ : CoordinateSpace n → ℝ}

/-- The truncation is homogeneous in the input. -/
@[simp]
theorem quantizeCutoffValue_smul_right (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ) (c : ℂ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeCutoffValue a χ (c • u) x = c • quantizeCutoffValue a χ u x := by
  by_cases hχ : χ.HasTemperateGrowth
  swap
  · simp [quantizeCutoffValue_of_not_hasTemperateGrowth a hχ]
  have hg := hχ.comp_sub_left x
  have h : SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) (c • u) =
      c • SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply, smul_comm (χ _) c]
  rw [quantizeCutoffValue_def, h, quantizeSchwartzValue_smul_right, quantizeCutoffValue_def]

/-- **The truncation as an amplitude quantization.** For `χ` of temperate growth, the truncation
`Op_χ(a)` is the quantization of the amplitude `χ(x - y) a(x, ξ)`. -/
theorem quantizeAmplitudeValue_eq_quantizeCutoffValue [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχ : χ.HasTemperateGrowth) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeAmplitudeValue (fun p ↦ χ (p.1 - p.2.1) • a.coefficient (p.1, p.2.2)) u x =
      quantizeCutoffValue a χ u x := by
  rw [quantizeCutoffValue_def, ← quantizeAmplitudeValue_eq_quantizeSchwartzValue]
  simp only [quantizeAmplitudeValue_def,
    SchwartzMap.smulLeftCLM_apply_apply (hχ.comp_sub_left x),
    smul_apply, ContinuousLinearMap.map_smul_of_tower]

/-- **Input-side proper support.** The value of the truncation at `x` only depends on the input on
the set `x - support χ` of points `y` with `x - y ∈ support χ`. -/
theorem quantizeCutoffValue_congr_right (a : Symbol n V W m) {u v : 𝓢(CoordinateSpace n, V)}
    {x : CoordinateSpace n} (h : ∀ y, x - y ∈ support χ → u y = v y) :
    quantizeCutoffValue a χ u x = quantizeCutoffValue a χ v x := by
  by_cases hχ : χ.HasTemperateGrowth
  · have hg := hχ.comp_sub_left x
    rw [quantizeCutoffValue_def, quantizeCutoffValue_def]
    congr 1
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg]
    by_cases hy : x - y ∈ support χ
    · rw [h y hy]
    · rw [notMem_support.1 hy, zero_smul, zero_smul]
  · simp only [quantizeCutoffValue_of_not_hasTemperateGrowth a hχ]

/-- **Output-side proper support.** The truncation vanishes at `x` unless `x = y + z` for a point
`y` of `support u` and a point `z` of `support χ`. -/
theorem support_quantizeCutoffValue_subset (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (u : 𝓢(CoordinateSpace n, V)) :
    support (quantizeCutoffValue a χ u) ⊆ support u + support χ := by
  intro x hx
  by_contra hmem
  have h0 : quantizeCutoffValue a χ u x = quantizeCutoffValue a χ 0 x :=
    quantizeCutoffValue_congr_right a fun y hy ↦
      notMem_support.1 fun hyu ↦ hmem ⟨y, hyu, x - y, hy, add_sub_cancel y x⟩
  exact hx (h0.trans (quantizeCutoffValue_zero_right a χ x))

/-- **Output-side proper support.** If the input or the cutoff is compactly supported, the
truncation is supported in `tsupport u + tsupport χ`. -/
theorem tsupport_quantizeCutoffValue_subset (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    {u : 𝓢(CoordinateSpace n, V)} (hc : HasCompactSupport u ∨ HasCompactSupport χ) :
    tsupport (quantizeCutoffValue a χ u) ⊆ tsupport u + tsupport χ :=
  closure_minimal ((support_quantizeCutoffValue_subset a χ u).trans
      (add_subset_add (subset_tsupport u) (subset_tsupport χ)))
    (hc.elim (fun hu ↦ (isClosed_tsupport χ).add_left_of_isCompact hu)
      fun hχc ↦ (isClosed_tsupport u).add_right_of_isCompact hχc)

/-- **Proper support.** For a compactly supported cutoff `χ`, the truncation maps compactly
supported inputs to compactly supported outputs. -/
theorem hasCompactSupport_quantizeCutoffValue (a : Symbol n V W m) (hχc : HasCompactSupport χ)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    HasCompactSupport (quantizeCutoffValue a χ u) :=
  (hu.isCompact.add hχc.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_quantizeCutoffValue_subset a χ (.inl hu))

/-- **The kernel of the truncation off the diagonal.** Let `χ` have temperate growth, and let the
input `u` or the cutoff `χ` be compactly supported. If `u` vanishes near `x`, or `χ` vanishes near
`0`, then `Op_χ(a) u (x) = ∫ χ(x - y) K_a(x, y) u(y) dy`, where `K_a` is the off-diagonal kernel of
`Op(a)`. -/
theorem quantizeCutoffValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (hχ : χ.HasTemperateGrowth) {u : 𝓢(CoordinateSpace n, V)}
    (hc : HasCompactSupport u ∨ HasCompactSupport χ) {x : CoordinateSpace n}
    (hx : x ∉ tsupport u ∨ 0 ∉ tsupport χ) :
    quantizeCutoffValue a χ u x = ∫ y, (χ (x - y) • offDiagonalKernel a x y) (u y) := by
  have hg := hχ.comp_sub_left x
  set w := SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u
  have hsub := SchwartzMap.tsupport_smulLeftCLM_subset (F := V) (fun y ↦ χ (x - y)) u
  have hwc : HasCompactSupport w := hc.elim
    (fun hu ↦ hu.of_isClosed_subset (isClosed_tsupport _) (hsub.trans inter_subset_left))
    fun hχc ↦ (hχc.comp_homeomorph (Homeomorph.subLeft x)).of_isClosed_subset
      (isClosed_tsupport _) (hsub.trans inter_subset_right)
  have hxw : x ∉ tsupport w := fun hxw ↦ hx.elim (fun hxu ↦ hxu (hsub hxw).1) fun h0 ↦
    h0 (by simpa using tsupport_comp_subset_preimage χ (continuous_sub_left x) (hsub hxw).2)
  rw [quantizeCutoffValue_def, a.quantizeSchwartzValue_eq_integral_offDiagonalKernel hwc hxw]
  congr 1 with y
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply,
    ContinuousLinearMap.map_smul_of_tower]

/-! ### The removed kernel -/

/-- The kernel `(1 - χ(x - y)) K_a(x, y)` removed from `Op(a)` by the truncation `Op_χ(a)`, where
`K_a` is the off-diagonal kernel `TauCeti.Symbol.offDiagonalKernel` of `Op(a)`. When `χ` is smooth
and `χ = 1` near `0` it is smooth on `ℝⁿ × ℝⁿ` (`TauCeti.Symbol.contDiff_cutoffRemainderKernel`),
and if moreover `χ` has temperate growth then `Op(a)` and `Op_χ(a)` differ on compactly supported
inputs by the integral operator with this kernel
(`TauCeti.Symbol.quantizeSchwartzValue_eq_quantizeCutoffValue_add_integral`). -/
def cutoffRemainderKernel (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x y : CoordinateSpace n) : V →L[ℂ] W :=
  (1 - χ (x - y)) • offDiagonalKernel a x y

theorem cutoffRemainderKernel_def (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x y : CoordinateSpace n) :
    cutoffRemainderKernel a χ x y = (1 - χ (x - y)) • offDiagonalKernel a x y :=
  (rfl)

/-- The removed kernel vanishes on the diagonal, where the off-diagonal kernel has the junk value
`0`. -/
@[simp]
theorem cutoffRemainderKernel_self (a : Symbol n V W m) (χ : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) : cutoffRemainderKernel a χ x x = 0 := by
  simp [cutoffRemainderKernel_def]

/-- Nothing is truncated by the cutoff `0`: the removed kernel is the whole off-diagonal kernel. -/
@[simp]
theorem cutoffRemainderKernel_zero_cutoff (a : Symbol n V W m) (x y : CoordinateSpace n) :
    cutoffRemainderKernel a 0 x y = offDiagonalKernel a x y := by
  simp [cutoffRemainderKernel_def]

/-- Nothing is removed by the cutoff `1`. -/
@[simp]
theorem cutoffRemainderKernel_one_cutoff (a : Symbol n V W m) (x y : CoordinateSpace n) :
    cutoffRemainderKernel a 1 x y = 0 := by
  simp [cutoffRemainderKernel_def]

/-- The removed kernel vanishes where `χ(x - y) = 1`; in particular near the diagonal when `χ = 1`
near `0`. -/
theorem cutoffRemainderKernel_eq_zero (a : Symbol n V W m) {x y : CoordinateSpace n}
    (h : χ (x - y) = 1) : cutoffRemainderKernel a χ x y = 0 := by
  simp [cutoffRemainderKernel_def, h]

/-- The removed kernel is the whole off-diagonal kernel where `χ(x - y) = 0`. -/
theorem cutoffRemainderKernel_eq_offDiagonalKernel (a : Symbol n V W m) {x y : CoordinateSpace n}
    (h : χ (x - y) = 0) : cutoffRemainderKernel a χ x y = offDiagonalKernel a x y := by
  simp [cutoffRemainderKernel_def, h]

/-- **The removed kernel is smooth.** If `χ` is smooth and equal to `1` near `0`, then
`(1 - χ(x - y)) K_a(x, y)` is smooth on `ℝⁿ × ℝⁿ`: it vanishes near the diagonal, and off the
diagonal `K_a` is smooth. -/
theorem contDiff_cutoffRemainderKernel (a : Symbol n V W m) (hχ : ContDiff ℝ ∞ χ)
    (hχ1 : χ =ᶠ[𝓝 0] 1) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ cutoffRemainderKernel a χ p.1 p.2
    := by
  simp only [cutoffRemainderKernel_def]
  refine contDiffOn_univ.1 <| contDiffOn_smul_of_eventuallyEq_zero
    (g := fun q : CoordinateSpace n × CoordinateSpace n ↦ 1 - χ (q.1 - q.2))
    (u := fun q ↦ offDiagonalKernel a q.1 q.2) (isOpen_ne_fun continuous_fst continuous_snd)
    (fun p _ ↦ (contDiff_const.sub (hχ.comp (contDiff_fst.sub contDiff_snd))).contDiffAt)
    (by simpa only [uncurry_def] using contDiffOn_offDiagonalKernel a) fun p _ hp ↦ ?_
  -- Near the diagonal, `χ(x - y) = 1`, so the cutoff `1 - χ(x - y)` vanishes.
  have hp' : p.1 = p.2 := by simpa using hp
  have hsub : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2 := by fun_prop
  have ht : Tendsto (fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) (𝓝 p) (𝓝 0) := by
    simpa [hp'] using hsub.tendsto p
  filter_upwards [ht.eventually hχ1] with q hq
  simp [hq]

/-- **The truncation is `Op(a)` modulo a smoothing operator.** If `χ` has temperate growth and
`χ = 1` near `0`, then on a compactly supported input
`Op(a) u (x) = Op_χ(a) u (x) + ∫ (1 - χ(x - y)) K_a(x, y) u(y) dy`, where the kernel of the last
term is smooth (`TauCeti.Symbol.contDiff_cutoffRemainderKernel`). -/
theorem quantizeSchwartzValue_eq_quantizeCutoffValue_add_integral [CompleteSpace V]
    [CompleteSpace W] (a : Symbol n V W m) (hχ : χ.HasTemperateGrowth) (hχ1 : χ =ᶠ[𝓝 0] 1)
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient u x =
      quantizeCutoffValue a χ u x + ∫ y, cutoffRemainderKernel a χ x y (u y) := by
  have hχ' : (1 - χ).HasTemperateGrowth := (HasTemperateGrowth.const 1).sub hχ
  -- The complementary cutoff `1 - χ` vanishes near `0`.
  have h0 : 0 ∉ tsupport (1 - χ) := notMem_tsupport_iff_eventuallyEq.2 <| by
    filter_upwards [hχ1] with z hz
    simp [hz]
  have hsplit : u = SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u +
      SchwartzMap.smulLeftCLM V (fun y ↦ (1 - χ) (x - y)) u := by
    ext y
    rw [add_apply, SchwartzMap.smulLeftCLM_apply_apply (hχ.comp_sub_left x),
      SchwartzMap.smulLeftCLM_apply_apply (hχ'.comp_sub_left x), Pi.sub_apply, Pi.one_apply,
      sub_smul, one_smul, add_sub_cancel]
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  conv_lhs => rw [hsplit]
  rw [quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable hC,
    ← quantizeCutoffValue_def a χ, ← quantizeCutoffValue_def a (1 - χ),
    quantizeCutoffValue_eq_integral_offDiagonalKernel a hχ' (.inl hu) (.inr h0)]
  simp only [cutoffRemainderKernel_def, Pi.sub_apply, Pi.one_apply]

/-- The removed part `x ↦ ∫ (1 - χ(x - y)) K_a(x, y) u(y) dy` of a compactly supported input is
smooth when `χ` is smooth and `χ = 1` near `0`, since its kernel is smooth
(`TauCeti.Symbol.contDiff_cutoffRemainderKernel`). -/
theorem contDiff_integral_cutoffRemainderKernel (a : Symbol n V W m) (hχ : ContDiff ℝ ∞ χ)
    (hχ1 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    ContDiff ℝ ∞ fun x ↦ ∫ y, cutoffRemainderKernel a χ x y (u y) := by
  have hF : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦
      cutoffRemainderKernel a χ p.1 p.2 (u p.2) := by
    -- Apply the kernel as a real-linear map.
    have hR := (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.comp
      (contDiff_cutoffRemainderKernel a hχ hχ1)
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars'] using
      hR.clm_apply ((u.smooth ⊤).comp contDiff_snd)
  have h : (fun x ↦ ∫ y, cutoffRemainderKernel a χ x y (u y)) =
      fun x ↦ ∫ y in tsupport u, cutoffRemainderKernel a χ x y (u y) := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, map_zero]
  rw [h]
  exact ContDiff.parametric_integral hu subset_rfl hu.isCompact.measure_lt_top.ne hF

/-- **Smoothness.** If `χ` has temperate growth and `χ = 1` near `0`, the truncation of an input
`u` is smooth whenever `u` or `χ` is compactly supported. Together with
`TauCeti.Symbol.hasCompactSupport_quantizeCutoffValue`, a smooth compactly supported cutoff equal
to `1` near `0` maps compactly supported inputs to compactly supported smooth functions. -/
theorem contDiff_quantizeCutoffValue [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hχ : χ.HasTemperateGrowth) (hχ1 : χ =ᶠ[𝓝 0] 1) {u : 𝓢(CoordinateSpace n, V)}
    (hc : HasCompactSupport u ∨ HasCompactSupport χ) :
    ContDiff ℝ ∞ (quantizeCutoffValue a χ u) := by
  have key : ∀ {u : 𝓢(CoordinateSpace n, V)}, HasCompactSupport u →
      ContDiff ℝ ∞ (quantizeCutoffValue a χ u) := fun {u} hu ↦ by
    have h : quantizeCutoffValue a χ u = fun x ↦
        quantizeSchwartzValue a.coefficient u x - ∫ y, cutoffRemainderKernel a χ x y (u y) := by
      funext x
      rw [quantizeSchwartzValue_eq_quantizeCutoffValue_add_integral a hχ hχ1 hu x,
        add_sub_cancel_right]
    rw [h]
    exact (a.contDiff_quantizeSchwartzValue u).sub
      (contDiff_integral_cutoffRemainderKernel a hχ.1 hχ1 hu)
  rcases hc with hu | hχc
  · exact key hu
  -- Near `x₀` the truncation only sees `u` on a bounded set, where a bump `ψ` equals `1`.
  refine contDiff_iff_contDiffAt.2 fun x₀ ↦ ?_
  obtain ⟨r, hr, hχr⟩ := hχc.isCompact.isBounded.subset_closedBall_lt 0 0
  let ψ : ContDiffBump x₀ := ⟨r + 1, r + 2, by linarith, by linarith⟩
  have hψ : (ψ : CoordinateSpace n → ℝ).HasTemperateGrowth :=
    ψ.hasCompactSupport.hasTemperateGrowth ψ.contDiff
  have hψu : HasCompactSupport (SchwartzMap.smulLeftCLM V (ψ : CoordinateSpace n → ℝ) u) :=
    ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
      ((SchwartzMap.tsupport_smulLeftCLM_subset _ u).trans inter_subset_right)
  refine (key hψu).contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
  refine quantizeCutoffValue_congr_right a fun y hy ↦ ?_
  have hxy : ‖x - y‖ ≤ r := by simpa using hχr (subset_tsupport χ hy)
  have hx' : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
  have hyb : y ∈ Metric.closedBall x₀ (r + 1) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖y - x₀‖ = ‖(x - x₀) - (x - y)‖ := by congr 1; abel
      _ ≤ ‖x - x₀‖ + ‖x - y‖ := norm_sub_le _ _
      _ ≤ r + 1 := by linarith
  rw [SchwartzMap.smulLeftCLM_apply_apply hψ, ψ.one_of_mem_closedBall hyb, one_smul]

end Symbol

end TauCeti
