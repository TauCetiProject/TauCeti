/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
public import TauCeti.Analysis.SpecialFunctions.Integrability.PosLog
import TauCeti.MeasureTheory.Integral.Circle.Average

/-!
# Single-circle properties of the Nevanlinna proximity function

Mathlib develops the arithmetic, inversion, and continuity properties of
`ValueDistribution.proximity` under a global `Meromorphic f` or `Continuous f` hypothesis on `ℂ`.
However, for a fixed radius `r`, `proximity f a r` depends only on the values of `f` along
`sphere 0 |r|`. Functions meromorphic only on an open disc (such as `ball 0 1`, where boundary
singularities prevent any global meromorphic extension) still satisfy
`MeromorphicOn f (sphere 0 |r|)` on every interior circle, and are continuous on a neighbourhood of
`sphere 0 |r|` at every radius whose circle avoids their poles.

This file localizes the single-circle proximity identities, bounds, and radial continuity to
`CircleIntegrable`, `MeromorphicOn · (sphere 0 |r|)`, and `ContinuousOn` on a neighbourhood of
`sphere 0 |r|`:

* `TauCeti.proximity_neg_top`: negation invariance `proximity (-f) ⊤ = proximity f ⊤`.
* `CircleIntegrable.abs_proximity_sub_const_sub_proximity_top_le` and
  `MeromorphicOn.abs_proximity_sub_const_sub_proximity_top_le`: shifting `f` by `a₀` changes
  `proximity · ⊤ r` by at most `log⁺ ‖a₀‖ + log 2`.
* `CircleIntegrable.proximity_sum_top_le`, `TauCeti.proximity_sum_top_le`,
  `CircleIntegrable.proximity_add_top_le`, and `MeromorphicOn.proximity_add_top_le`: subadditivity
  of `proximity · ⊤ r` up to `log #s` / `log 2`.
* `CircleIntegrable.proximity_smul_top_le`, `CircleIntegrable.proximity_mul_top_le`,
  `MeromorphicOn.proximity_smul_top_le`, and `MeromorphicOn.proximity_mul_top_le`: subadditivity of
  `proximity · ⊤ r` under products and scalar multiplication.
* `CircleIntegrable.abs_proximity_top_sub_proximity_const_smul_top_le` and
  `MeromorphicOn.abs_proximity_top_sub_proximity_const_smul_top_le`: scaling by `s ≠ 0` changes
  `proximity · ⊤ r` by at most `log⁺ ‖s‖ + log⁺ ‖s⁻¹‖`.
* `MeromorphicOn.proximity_top_sub_proximity_inv_top_eq_circleAverage`: on `sphere 0 |r|`,
  `proximity f ⊤ r - proximity f⁻¹ ⊤ r = circleAverage (Real.log ‖f ·‖) 0 r`.
* `ContinuousOn.continuousAt_proximity_top`: local radial continuity of
  `ValueDistribution.proximity g ⊤` at `R` when `g` is continuous on a neighbourhood of
  `sphere 0 |R|` (including across interior poles and boundary zeros).

## Implementation notes

The arithmetic and reciprocal statements localize the global theorems in
`Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic` (by Stefan Kebekus) from `Meromorphic`
on `ℂ` to circle integrability and `MeromorphicOn` on `sphere 0 |r|`. Local radial continuity
delegates to `ContinuousOn.continuousAt_circleAverage`.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  **38** (2025), 627–702, §6.1.
* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.2.
-/

open scoped Finset Topology

public section

open Filter MeasureTheory Metric Real Set

namespace TauCeti

/-- Negating a function leaves `ValueDistribution.proximity · ⊤` unchanged. -/
@[to_fun (attr := simp) proximity_fun_neg_top]
theorem proximity_neg_top {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) :
    ValueDistribution.proximity (-f) ⊤ = ValueDistribution.proximity f ⊤ := by
  ext r
  simp [ValueDistribution.proximity_top]

end TauCeti

section CircleIntegrable

variable {E : Type*} [NormedAddCommGroup E] {r : ℝ}

/-- Shifting `f` by a constant `a₀` changes `ValueDistribution.proximity · ⊤ r` by at most
`log⁺ ‖a₀‖ + log 2`, assuming only circle integrability of `log⁺ ‖f‖` and `log⁺ ‖f - a₀‖` on
`sphere 0 |r|`. -/
theorem CircleIntegrable.abs_proximity_sub_const_sub_proximity_top_le {f : ℂ → E} {a₀ : E}
    (hf : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r)
    (hfa : CircleIntegrable (fun z ↦ log⁺ ‖f z - a₀‖) 0 r) :
    |ValueDistribution.proximity (fun z ↦ f z - a₀) ⊤ r - ValueDistribution.proximity f ⊤ r| ≤
      log⁺ ‖a₀‖ + Real.log 2 := by
  simp only [ValueDistribution.proximity_top]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · linarith [hf.circleAverage_posLog_norm_sub_const_le a₀ hfa]
  · have hrev : CircleIntegrable (fun z ↦ log⁺ ‖(f z - a₀) - (-a₀)‖) 0 r := by
      simpa only [sub_neg_eq_add, sub_add_cancel] using hf
    have hbound := hfa.circleAverage_posLog_norm_sub_const_le (-a₀) hrev
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hbound
    linarith

/-- Single-circle finite-sum bound for `ValueDistribution.proximity · ⊤` under circle integrability
of `log⁺` of the sum and of each summand. -/
theorem CircleIntegrable.proximity_sum_top_le {α : Type*} {s : Finset α} {f : α → ℂ → E}
    (hsum : CircleIntegrable (fun z ↦ log⁺ ‖∑ a ∈ s, f a z‖) 0 r)
    (hf : ∀ a ∈ s, CircleIntegrable (fun z ↦ log⁺ ‖f a z‖) 0 r) :
    ValueDistribution.proximity (∑ a ∈ s, f a) ⊤ r ≤
      ∑ a ∈ s, ValueDistribution.proximity (f a) ⊤ r + Real.log #s := by
  simp only [ValueDistribution.proximity_top, Finset.sum_apply]
  calc circleAverage (fun z ↦ log⁺ ‖∑ a ∈ s, f a z‖) 0 r
    _ ≤ circleAverage (fun z ↦ ∑ a ∈ s, log⁺ ‖f a z‖ + Real.log #s) 0 r := by
      refine circleAverage_mono hsum
        ((CircleIntegrable.fun_sum s hf).add (circleIntegrable_const _ 0 r)) fun z _ ↦ ?_
      rw [add_comm]
      exact posLog_norm_sum_le s fun a ↦ f a z
    _ = ∑ a ∈ s, circleAverage (fun z ↦ log⁺ ‖f a z‖) 0 r + Real.log #s := by
      nth_rw 2 [← circleAverage_const (Real.log #s) 0 r]
      rw [← circleAverage_sum hf,
        ← circleAverage_add (CircleIntegrable.sum s hf) (circleIntegrable_const (Real.log #s) 0 r)]
      congr 1
      ext z
      simp

/-- Single-circle binary-sum bound for `ValueDistribution.proximity · ⊤` under circle
integrability. -/
@[to_fun proximity_fun_add_top_le]
theorem CircleIntegrable.proximity_add_top_le {f₁ f₂ : ℂ → E}
    (hf₁ : CircleIntegrable (fun z ↦ log⁺ ‖f₁ z‖) 0 r)
    (hf₂ : CircleIntegrable (fun z ↦ log⁺ ‖f₂ z‖) 0 r)
    (hadd : CircleIntegrable (fun z ↦ log⁺ ‖(f₁ + f₂) z‖) 0 r) :
    ValueDistribution.proximity (f₁ + f₂) ⊤ r ≤
      ValueDistribution.proximity f₁ ⊤ r + ValueDistribution.proximity f₂ ⊤ r + Real.log 2 := by
  have hsum_int : CircleIntegrable (fun z ↦ log⁺ ‖∑ i ∈ (Finset.univ : Finset (Fin 2)),
      ![f₁, f₂] i z‖) 0 r := by
    simpa [Fin.sum_univ_two] using hadd
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      CircleIntegrable (fun z ↦ log⁺ ‖![f₁, f₂] i z‖) 0 r := by
    intro i _
    fin_cases i
    · exact hf₁
    · exact hf₂
  simpa [Fin.sum_univ_two] using hsum_int.proximity_sum_top_le hmem

/-- Single-circle scalar-product bound for `ValueDistribution.proximity · ⊤` under circle
integrability. -/
@[to_fun proximity_fun_smul_top_le]
theorem CircleIntegrable.proximity_smul_top_le [NormedSpace ℂ E] {f₁ : ℂ → ℂ} {f₂ : ℂ → E}
    (hf₁ : CircleIntegrable (fun z ↦ log⁺ ‖f₁ z‖) 0 r)
    (hf₂ : CircleIntegrable (fun z ↦ log⁺ ‖f₂ z‖) 0 r)
    (hsmul : CircleIntegrable (fun z ↦ log⁺ ‖(f₁ • f₂) z‖) 0 r) :
    ValueDistribution.proximity (f₁ • f₂) ⊤ r ≤
      ValueDistribution.proximity f₁ ⊤ r + ValueDistribution.proximity f₂ ⊤ r := by
  simp only [ValueDistribution.proximity_top]
  rw [← circleAverage_add hf₁ hf₂]
  refine circleAverage_mono hsmul (hf₁.add hf₂) fun z _ ↦ ?_
  simp only [Pi.smul_apply', norm_smul, Pi.add_apply]
  exact posLog_mul

/-- Single-circle product bound for `ValueDistribution.proximity · ⊤` under circle integrability. -/
@[to_fun proximity_fun_mul_top_le]
theorem CircleIntegrable.proximity_mul_top_le {f₁ f₂ : ℂ → ℂ}
    (hf₁ : CircleIntegrable (fun z ↦ log⁺ ‖f₁ z‖) 0 r)
    (hf₂ : CircleIntegrable (fun z ↦ log⁺ ‖f₂ z‖) 0 r)
    (hmul : CircleIntegrable (fun z ↦ log⁺ ‖(f₁ * f₂) z‖) 0 r) :
    ValueDistribution.proximity (f₁ * f₂) ⊤ r ≤
      ValueDistribution.proximity f₁ ⊤ r + ValueDistribution.proximity f₂ ⊤ r :=
  hf₁.proximity_smul_top_le hf₂ hmul

/-- Scaling `f` by a nonzero constant `s : ℂ` changes `ValueDistribution.proximity · ⊤ r` by at most
`log⁺ ‖s‖ + log⁺ ‖s⁻¹‖`, assuming circle integrability of `log⁺ ‖f‖` and `log⁺ ‖s • f‖`. -/
@[to_fun abs_proximity_top_sub_proximity_fun_const_smul_top_le]
theorem CircleIntegrable.abs_proximity_top_sub_proximity_const_smul_top_le [NormedSpace ℂ E]
    {f : ℂ → E} {s : ℂ} (hf : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r)
    (hsf : CircleIntegrable (fun z ↦ log⁺ ‖(s • f) z‖) 0 r) (hs : s ≠ 0) :
    |ValueDistribution.proximity f ⊤ r - ValueDistribution.proximity (s • f) ⊤ r| ≤
      log⁺ ‖s‖ + log⁺ ‖s⁻¹‖ := by
  simp only [ValueDistribution.proximity_top, Pi.smul_apply, norm_inv] at hsf ⊢
  rw [← circleAverage_sub hf hsf]
  refine abs_circleAverage_le_circleAverage_abs.trans ?_
  rw [← circleAverage_const (log⁺ ‖s‖ + log⁺ ‖s‖⁻¹) 0 r]
  refine circleAverage_mono (hf.sub hsf).abs (circleIntegrable_const _ 0 r) fun z _ ↦ ?_
  simp only [Pi.abs_apply, Pi.sub_apply, norm_smul]
  rw [abs_sub_comm]
  exact abs_posLog_mul_sub_posLog_le_posLog_add_posLog (norm_ne_zero_iff.2 hs)

end CircleIntegrable

section MeromorphicOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℝ}

/-- Local version of `ValueDistribution.proximity_sum_top_le`: if every `f a` (`a ∈ s`) is
meromorphic on `sphere 0 |r|`, then
`proximity (∑ a ∈ s, f a) ⊤ r ≤ ∑ a ∈ s, proximity (f a) ⊤ r + log #s`. -/
theorem TauCeti.proximity_sum_top_le {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a ∈ s, MeromorphicOn (f a) (sphere 0 |r|)) :
    ValueDistribution.proximity (∑ a ∈ s, f a) ⊤ r ≤
      ∑ a ∈ s, ValueDistribution.proximity (f a) ⊤ r + Real.log #s := by
  have hsum : MeromorphicOn (∑ a ∈ s, f a) (sphere 0 |r|) := MeromorphicOn.sum hf
  have hsum_int : CircleIntegrable (fun z ↦ log⁺ ‖∑ a ∈ s, f a z‖) 0 r := by
    simpa only [Finset.sum_apply] using hsum.circleIntegrable_posLog_norm
  exact hsum_int.proximity_sum_top_le fun a ha ↦ (hf a ha).circleIntegrable_posLog_norm

/-- If `f : ℂ → E` is meromorphic on `sphere 0 |r|`, then
`|proximity (f · - a₀) ⊤ r - proximity f ⊤ r| ≤ log⁺ ‖a₀‖ + log 2`. -/
theorem MeromorphicOn.abs_proximity_sub_const_sub_proximity_top_le {f : ℂ → E}
    (hf : MeromorphicOn f (sphere 0 |r|)) (a₀ : E) :
    |ValueDistribution.proximity (fun z ↦ f z - a₀) ⊤ r - ValueDistribution.proximity f ⊤ r| ≤
      log⁺ ‖a₀‖ + Real.log 2 :=
  hf.circleIntegrable_posLog_norm.abs_proximity_sub_const_sub_proximity_top_le
    (hf.sub (MeromorphicOn.const a₀)).circleIntegrable_posLog_norm

/-- Local version of `ValueDistribution.proximity_add_top_le`: if `f₁` and `f₂` are meromorphic on
`sphere 0 |r|`, then `proximity (f₁ + f₂) ⊤ r ≤ proximity f₁ ⊤ r + proximity f₂ ⊤ r + log 2`. -/
@[to_fun proximity_fun_add_top_le]
theorem MeromorphicOn.proximity_add_top_le {f₁ f₂ : ℂ → E}
    (hf₁ : MeromorphicOn f₁ (sphere 0 |r|)) (hf₂ : MeromorphicOn f₂ (sphere 0 |r|)) :
    ValueDistribution.proximity (f₁ + f₂) ⊤ r ≤
      ValueDistribution.proximity f₁ ⊤ r + ValueDistribution.proximity f₂ ⊤ r + Real.log 2 :=
  hf₁.circleIntegrable_posLog_norm.proximity_add_top_le hf₂.circleIntegrable_posLog_norm
    (hf₁.add hf₂).circleIntegrable_posLog_norm

/-- Local version of `ValueDistribution.proximity_smul_top_le`: if `f₁ : ℂ → ℂ` and `f₂ : ℂ → E` are
meromorphic on `sphere 0 |r|`, then
`proximity (f₁ • f₂) ⊤ r ≤ proximity f₁ ⊤ r + proximity f₂ ⊤ r`. -/
@[to_fun proximity_fun_smul_top_le]
theorem MeromorphicOn.proximity_smul_top_le {f₁ : ℂ → ℂ} {f₂ : ℂ → E}
    (hf₁ : MeromorphicOn f₁ (sphere 0 |r|)) (hf₂ : MeromorphicOn f₂ (sphere 0 |r|)) :
    ValueDistribution.proximity (f₁ • f₂) ⊤ r ≤
      ValueDistribution.proximity f₁ ⊤ r + ValueDistribution.proximity f₂ ⊤ r :=
  hf₁.circleIntegrable_posLog_norm.proximity_smul_top_le hf₂.circleIntegrable_posLog_norm
    (hf₁.smul hf₂).circleIntegrable_posLog_norm

/-- Local version of `ValueDistribution.proximity_mul_top_le`: if `f₁, f₂ : ℂ → ℂ` are meromorphic
on `sphere 0 |r|`, then `proximity (f₁ * f₂) ⊤ r ≤ proximity f₁ ⊤ r + proximity f₂ ⊤ r`. -/
@[to_fun proximity_fun_mul_top_le]
theorem MeromorphicOn.proximity_mul_top_le {f₁ f₂ : ℂ → ℂ}
    (hf₁ : MeromorphicOn f₁ (sphere 0 |r|)) (hf₂ : MeromorphicOn f₂ (sphere 0 |r|)) :
    ValueDistribution.proximity (f₁ * f₂) ⊤ r ≤
      ValueDistribution.proximity f₁ ⊤ r + ValueDistribution.proximity f₂ ⊤ r :=
  hf₁.proximity_smul_top_le hf₂

/-- Local version of `ValueDistribution.proximity_top_sub_proximity_const_smul_top_le`: if
`f : ℂ → E` is meromorphic on `sphere 0 |r|` and `s ≠ 0`, then
`|proximity f ⊤ r - proximity (s • f) ⊤ r| ≤ log⁺ ‖s‖ + log⁺ ‖s⁻¹‖`. -/
@[to_fun abs_proximity_top_sub_proximity_fun_const_smul_top_le]
theorem MeromorphicOn.abs_proximity_top_sub_proximity_const_smul_top_le {f : ℂ → E} {s : ℂ}
    (hf : MeromorphicOn f (sphere 0 |r|)) (hs : s ≠ 0) :
    |ValueDistribution.proximity f ⊤ r - ValueDistribution.proximity (s • f) ⊤ r| ≤
      log⁺ ‖s‖ + log⁺ ‖s⁻¹‖ :=
  hf.circleIntegrable_posLog_norm.abs_proximity_top_sub_proximity_const_smul_top_le
    ((MeromorphicOn.const s).smul hf).circleIntegrable_posLog_norm hs

/-- Local version of `ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage`: if `f` is
meromorphic on `sphere 0 |r|`, then `proximity f ⊤ r - proximity f⁻¹ ⊤ r` equals the circle average
of `Real.log ‖f ·‖` on `sphere 0 |r|`. -/
@[to_fun proximity_top_sub_proximity_fun_inv_top_eq_circleAverage]
theorem MeromorphicOn.proximity_top_sub_proximity_inv_top_eq_circleAverage {f : ℂ → ℂ}
    (hf : MeromorphicOn f (sphere 0 |r|)) :
    ValueDistribution.proximity f ⊤ r - ValueDistribution.proximity f⁻¹ ⊤ r =
      circleAverage (fun z ↦ Real.log ‖f z‖) 0 r := by
  rw [ValueDistribution.proximity_inv, ValueDistribution.proximity_zero,
    ValueDistribution.proximity_top, hf.circleAverage_posLog_inv_norm]
  ring

end MeromorphicOn

/-- If `g : ℂ → E` is continuous on a set `s` that is a neighbourhood of `sphere 0 |R|`, then its
Nevanlinna proximity function `ValueDistribution.proximity g ⊤` is continuous at `R` (including
when `g` has poles inside `ball 0 |R|` or zeros on `sphere 0 |R|`). -/
theorem ContinuousOn.continuousAt_proximity_top {E : Type*} [NormedAddCommGroup E]
    {g : ℂ → E} {s : Set ℂ} {R : ℝ} (hg : ContinuousOn g s) (hs : s ∈ 𝓝ˢ (sphere 0 |R|)) :
    ContinuousAt (ValueDistribution.proximity g ⊤) R := by
  rw [ValueDistribution.proximity_top]
  exact (continuous_posLog.comp_continuousOn hg.norm).continuousAt_circleAverage hs

-- `z ↦ z⁻¹` has an interior pole at `0`, yet `proximity (·⁻¹) ⊤` is continuous at `R = 1`.
example : ContinuousAt (ValueDistribution.proximity (fun z : ℂ ↦ z⁻¹) ⊤) 1 := by
  have hs : ({0}ᶜ : Set ℂ) ∈ 𝓝ˢ (sphere (0 : ℂ) |1|) :=
    isOpen_compl_singleton.mem_nhdsSet.mpr fun z hz ↦ by
      rw [mem_compl_singleton_iff]
      rintro rfl
      simp at hz
  exact continuousOn_inv₀.continuousAt_proximity_top hs
