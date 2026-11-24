/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol

/-!
# Examples: homogeneous symbols and frequency cutoffs

These examples test the conventions of homogeneous symbols (`TauCeti.HomogeneousSymbol`) and
frequency cutoffs (`TauCeti.FrequencyCutoff`), the two ingredients of a classical expansion
`a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)`. Each pins down a condition that a weaker definition would get wrong.

**Homogeneous symbols**, on positions and frequencies in `ℝ` with values in `ℂ`:

* `ξ ²` is homogeneous of degree `2`: rescaling `ξ = 1` by `t = 2` multiplies it by
  `4 = 2 ^ 2`. It is not homogeneous of degree `1`, which would give `2`
  (`not_exists_coefficient_eq_normRpow_two`).
* The degree-`0` term equal to `1` away from `ξ = 0` takes the value `0` at `ξ = 0`, by the
  convention of `HomogeneousSymbol`. It is not continuous there
  (`not_continuousAt_coefficient_id`), while its product with a frequency cutoff is smooth
  (`contDiff_smul_coefficient_id`).
* `|ξ|` is smooth away from `0` and positively homogeneous of degree `1`, with the same value `1`
  at `ξ = 1` and `ξ = -1` (`coefficient_normRpow_one_neg_one`). Positive homogeneity imposes no
  parity condition (`coefficient_normRpow_one_neg_one_ne_neg`).

**Frequency cutoffs**:

* With `h t = exp (-1 / t)` for `t > 0` and `h t = 0` for `t ≤ 0` (`expNegInvGlue`), the function
  `χ ξ = h (‖ξ‖ - 1) / (h (‖ξ‖ - 1) + h (2 - ‖ξ‖))` is the frequency cutoff
  `FrequencyCutoff.ofSmoothTransition` (`ofSmoothTransition_apply_eq_div`). Its values at the
  radii `1`, `3 / 2` and `2` are `0`, `1 / 2` and `1`.
* On `ℝ`, the step `ξ ↦ 0` for `|ξ| < 3 / 2` and `1` otherwise has the right values for
  `|ξ| ≤ 1` and `|ξ| ≥ 2` and lies in `[0, 1]`, but its one-sided limits at `3 / 2` are `0`
  and `1`, so it is not a frequency cutoff (`not_exists_coe_eq_step`).
* The smooth function `χ + 4 χ (1 - χ)` has the same values as `χ` for `‖ξ‖ ≤ 1` and
  `‖ξ‖ ≥ 2`, but equals `3 / 2 > 1` at radius `3 / 2`; the range condition excludes it
  (`not_exists_coe_eq_overshoot`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti.HomogeneousSymbolExample

/-! ### Homogeneous symbols -/

section Homogeneous

/-- Away from `ξ = 0`, `HomogeneousSymbol.normRpow` of degree `2` on `ℝ` is `ξ ^ 2` times the
identity. -/
theorem coefficient_normRpow_two {x ξ : ℝ} (hξ : ξ ≠ 0) :
    (HomogeneousSymbol.normRpow ℝ ℝ ℂ 2).coefficient (x, ξ) =
      (ξ ^ 2 : ℝ) • ContinuousLinearMap.id ℂ ℂ := by
  rw [HomogeneousSymbol.coefficient_normRpow_of_ne_zero _ _ _ hξ, Real.rpow_two, Real.norm_eq_abs,
    sq_abs]

/-- Rescaling `ξ = 1` by `t = 2` multiplies the degree-`2` symbol `ξ ^ 2` by `4`. -/
theorem coefficient_normRpow_two_two (x : ℝ) :
    (HomogeneousSymbol.normRpow ℝ ℝ ℂ 2).coefficient (x, 2) =
      (4 : ℝ) • (HomogeneousSymbol.normRpow ℝ ℝ ℂ 2).coefficient (x, 1) := by
  rw [coefficient_normRpow_two two_ne_zero, coefficient_normRpow_two one_ne_zero]
  norm_num

/-- The symbol `ξ ^ 2` is not homogeneous of degree `1`. -/
theorem not_exists_coefficient_eq_normRpow_two :
    ¬∃ b : HomogeneousSymbol ℝ ℝ ℂ ℂ 1,
      b.coefficient = (HomogeneousSymbol.normRpow ℝ ℝ ℂ 2).coefficient := by
  rintro ⟨b, hb⟩
  have hne : HomogeneousSymbol.normRpow ℝ ℝ ℂ 2 ≠ 0 := fun h ↦ by
    have h1 := coefficient_normRpow_two (x := 0) one_ne_zero
    rw [h, HomogeneousSymbol.coefficient_zero] at h1
    simpa using congr($h1 1)
  have h := HomogeneousSymbol.degree_eq_of_coefficient_eq hb hne
  norm_num at h

/-- The degree-`0` symbol equal to `1` away from `ξ = 0` is not continuous at `ξ = 0`, where its
value is `0`. -/
theorem not_continuousAt_coefficient_id (x : ℝ) :
    ¬ContinuousAt (HomogeneousSymbol.id ℝ ℝ ℂ).coefficient (x, 0) := fun h ↦ by
  have h1 := (HomogeneousSymbol.id ℝ ℝ ℂ).coefficient_eq_zero_of_continuousAt le_rfl h 1
  rw [HomogeneousSymbol.coefficient_id one_ne_zero] at h1
  simpa using congr($h1 1)

/-- The product of the degree-`0` symbol equal to `1` away from `ξ = 0` with a frequency cutoff is
smooth. -/
theorem contDiff_smul_coefficient_id (χ : FrequencyCutoff ℝ) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ χ p.2 • (HomogeneousSymbol.id ℝ ℝ ℂ).coefficient p :=
  (HomogeneousSymbol.id ℝ ℝ ℂ).contDiff_smul_coefficient χ

/-- The degree-`1` symbol `|ξ|` takes the value `1` both at `ξ = 1` and at `ξ = -1`. -/
theorem coefficient_normRpow_one_neg_one (x : ℝ) :
    (HomogeneousSymbol.normRpow ℝ ℝ ℂ 1).coefficient (x, -1) =
      (HomogeneousSymbol.normRpow ℝ ℝ ℂ 1).coefficient (x, 1) := by
  simp [HomogeneousSymbol.coefficient_normRpow_of_ne_zero]

/-- The degree-`1` symbol `|ξ|` is not odd. -/
theorem coefficient_normRpow_one_neg_one_ne_neg (x : ℝ) :
    (HomogeneousSymbol.normRpow ℝ ℝ ℂ 1).coefficient (x, -1) ≠
      -(HomogeneousSymbol.normRpow ℝ ℝ ℂ 1).coefficient (x, 1) := fun h ↦ by
  rw [coefficient_normRpow_one_neg_one, eq_neg_iff_add_eq_zero, ← two_smul ℝ,
    smul_eq_zero] at h
  simpa [HomogeneousSymbol.coefficient_normRpow_of_ne_zero] using congr($(h.resolve_left
    two_ne_zero) 1)

end Homogeneous

/-! ### Frequency cutoffs -/

section Cutoff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The cutoff `FrequencyCutoff.ofSmoothTransition` is
`h (‖ξ‖ - 1) / (h (‖ξ‖ - 1) + h (2 - ‖ξ‖))` for the flat function `h = expNegInvGlue`. -/
theorem ofSmoothTransition_apply_eq_div (ξ : F) :
    FrequencyCutoff.ofSmoothTransition ξ =
      expNegInvGlue (‖ξ‖ - 1) / (expNegInvGlue (‖ξ‖ - 1) + expNegInvGlue (2 - ‖ξ‖)) := by
  rw [FrequencyCutoff.ofSmoothTransition_apply, Real.smoothTransition,
    show (1 : ℝ) - (‖ξ‖ - 1) = 2 - ‖ξ‖ by ring]

/-- `FrequencyCutoff.ofSmoothTransition` is `0` at radius `1`. -/
theorem ofSmoothTransition_apply_of_norm_eq_one {ξ : F} (hξ : ‖ξ‖ = 1) :
    FrequencyCutoff.ofSmoothTransition ξ = 0 :=
  FrequencyCutoff.ofSmoothTransition.apply_eq_zero_of_norm_le_one hξ.le

/-- `FrequencyCutoff.ofSmoothTransition` is `1 / 2` at radius `3 / 2`. -/
theorem ofSmoothTransition_apply_of_norm_eq_three_halves {ξ : F} (hξ : ‖ξ‖ = 3 / 2) :
    FrequencyCutoff.ofSmoothTransition ξ = 1 / 2 := by
  -- Halfway, both terms of the denominator equal `h (1 / 2) > 0`.
  have h := expNegInvGlue.pos_of_pos (one_half_pos (α := ℝ))
  rw [ofSmoothTransition_apply_eq_div, hξ]
  norm_num
  field_simp
  ring

/-- `FrequencyCutoff.ofSmoothTransition` is `1` at radius `2`. -/
theorem ofSmoothTransition_apply_of_norm_eq_two {ξ : F} (hξ : ‖ξ‖ = 2) :
    FrequencyCutoff.ofSmoothTransition ξ = 1 :=
  FrequencyCutoff.ofSmoothTransition.apply_eq_one_of_two_le_norm hξ.ge

/-- The step at radius `3 / 2`: `0` for `|ξ| < 3 / 2` and `1` otherwise. -/
noncomputable def step (ξ : ℝ) : ℝ :=
  if ‖ξ‖ < 3 / 2 then 0 else 1

theorem step_eq_zero_of_norm_le_one {ξ : ℝ} (hξ : ‖ξ‖ ≤ 1) : step ξ = 0 := by
  simp only [step, show ‖ξ‖ < 3 / 2 by linarith, ↓reduceIte]

theorem step_eq_one_of_two_le_norm {ξ : ℝ} (hξ : 2 ≤ ‖ξ‖) : step ξ = 1 := by
  simp only [step, show ¬‖ξ‖ < 3 / 2 by linarith, ↓reduceIte]

theorem step_mem_Icc (ξ : ℝ) : step ξ ∈ Icc (0 : ℝ) 1 := by
  unfold step
  split_ifs <;> norm_num

/-- The step tends to `0` from the left of `3 / 2`. -/
theorem tendsto_step_nhdsLT : Tendsto step (𝓝[<] (3 / 2)) (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 3 / 2 by norm_num)] with ξ hξ
  have h : ‖ξ‖ < 3 / 2 := by rw [Real.norm_of_nonneg hξ.1.le]; exact hξ.2
  simp only [step, h, ↓reduceIte]

/-- The step tends to `1` from the right of `3 / 2`. -/
theorem tendsto_step_nhdsGT : Tendsto step (𝓝[>] (3 / 2)) (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  have h : ¬‖ξ‖ < 3 / 2 := by
    rw [Real.norm_of_nonneg (by linarith [mem_Ioi.1 hξ])]
    exact (mem_Ioi.1 hξ).le.not_gt
  simp only [step, h, ↓reduceIte]

/-- The step is not a frequency cutoff: a cutoff takes the value `1 / 2`, the step only `0`
and `1`. -/
theorem not_exists_coe_eq_step : ¬∃ χ : FrequencyCutoff ℝ, ⇑χ = step := by
  rintro ⟨χ, hχ⟩
  have h : (1 / 2 : ℝ) ∈ range step := by
    rw [← hχ, χ.range_eq_Icc]
    norm_num
  obtain ⟨ξ, hξ⟩ := h
  unfold step at hξ
  split_ifs at hξ <;> norm_num at hξ

/-- The smooth function `χ + 4 χ (1 - χ)` for the cutoff `χ = FrequencyCutoff.ofSmoothTransition`.
-/
noncomputable def overshoot (ξ : F) : ℝ :=
  FrequencyCutoff.ofSmoothTransition ξ +
    4 * FrequencyCutoff.ofSmoothTransition ξ * (1 - FrequencyCutoff.ofSmoothTransition ξ)

theorem contDiff_overshoot : ContDiff ℝ ∞ (overshoot (F := F)) := by
  have h := (FrequencyCutoff.ofSmoothTransition (F := F)).contDiff (n := ⊤)
  exact h.add ((contDiff_const.mul h).mul (contDiff_const.sub h))

theorem overshoot_eq_zero_of_norm_le_one {ξ : F} (hξ : ‖ξ‖ ≤ 1) : overshoot ξ = 0 := by
  simp [overshoot, FrequencyCutoff.ofSmoothTransition.apply_eq_zero_of_norm_le_one hξ]

theorem overshoot_eq_one_of_two_le_norm {ξ : F} (hξ : 2 ≤ ‖ξ‖) : overshoot ξ = 1 := by
  simp [overshoot, FrequencyCutoff.ofSmoothTransition.apply_eq_one_of_two_le_norm hξ]

/-- At radius `3 / 2` the function `χ + 4 χ (1 - χ)` equals `3 / 2`. -/
theorem overshoot_of_norm_eq_three_halves {ξ : F} (hξ : ‖ξ‖ = 3 / 2) : overshoot ξ = 3 / 2 := by
  rw [overshoot, ofSmoothTransition_apply_of_norm_eq_three_halves hξ]
  norm_num

/-- The function `χ + 4 χ (1 - χ)` is not a frequency cutoff on a nontrivial space, since it
exceeds `1`. -/
theorem not_exists_coe_eq_overshoot [Nontrivial F] :
    ¬∃ χ : FrequencyCutoff F, ⇑χ = overshoot := by
  rintro ⟨χ, hχ⟩
  obtain ⟨ξ, hξ⟩ := exists_norm_eq F (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  have h := χ.le_one ξ
  rw [hχ, overshoot_of_norm_eq_three_halves hξ] at h
  norm_num at h

end Cutoff

end TauCeti.HomogeneousSymbolExample
