/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# Checks for lattices and Weil's formula

Worked examples for lattices in locally compact groups and the unfolding formula
`∫_G f = ∫_(G/Γ) ∑_(γ ∈ Γ) f(g γ)`.

* *`θℤ ⊂ ℝ`.* For `θ > 0`, `[t, t + θ)` is a fundamental domain for the right translation action
  of `θℤ` on `ℝ` (`isAddFundamentalDomain_Ico_zmultiples_op`), so the covolume of `θℤ` for
  Lebesgue measure is `θ` (`addCovolume_zmultiples_op`), and that of `ℤ` is `1`
  (`addCovolume_zmultiples_one_op`). Weil's formula reads
  `∫_ℝ f = ∫_0^1 ∑_n f(x + n) dx` (`lintegral_eq_setLIntegral_Ico_tsum_add_intCast`).
  Multiplying Lebesgue measure by `c` multiplies the covolume by `c`
  (`addCovolume_zmultiples_op_smul`, from `MeasureTheory.addCovolume_smul_measure`).
* *The side of the coset sum.* In `S₃`, with `Γ = {1, (0 1)}` (`coe_Γ`) and `f` the indicator of
  `(0 2)` (`indicatorSwap`), the right-translated sum `∑_(γ ∈ Γ) f(g γ)` is `1` at both
  elements `(0 2)` and `(0 2)(0 1)` of the left coset `(0 2) Γ` (`sum_indicator_mul_swap_zero_two`,
  `sum_indicator_mul_swap_zero_two_mul_swap_zero_one`), while the left-translated sum
  `∑_(γ ∈ Γ) f(γ g)` is `1` at `(0 2)` and `0` at `(0 2)(0 1)`
  (`sum_indicator_swap_mul_swap_zero_two`,
  `sum_indicator_swap_mul_swap_zero_two_mul_swap_zero_one`),
  so it is not a function on `G / Γ`. With `1`, `(0 2)`, `(1 2)` representing the three left
  cosets (`image_mul_eq_univ`), the sum of the right-translated sums over them is
  `1 = ∑_g f(g)` (`sum_cosets_sum_indicator_mul`).
-/

public section

noncomputable section

namespace TauCeti.Examples.Lattice

open MeasureTheory Set Function

open scoped ENNReal

/-! ### The lattice `θℤ ⊂ ℝ` -/

/-- **`[t, t + θ)` is a fundamental domain for `θℤ` acting on `ℝ` by right translation.** -/
theorem isAddFundamentalDomain_Ico_zmultiples_op {θ : ℝ} (hθ : 0 < θ) (t : ℝ)
    (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.op <| .zmultiples θ) (Ico t (t + θ)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ico fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • θ) (AddSubgroup.zmultiples θ) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • θ) (zsmul_left_strictMono hθ).injective).bijective
  refine (AddSubgroup.equivOp _).bijective.comp this |>.existsUnique_iff.2 ?_
  simpa using! existsUnique_add_zsmul_mem_Ico hθ x t

/-- **The covolume of `θℤ` in `ℝ` is `θ`**, computed on the fundamental domain `[0, θ)`. -/
theorem addCovolume_zmultiples_op {θ : ℝ} (hθ : 0 < θ) :
    addCovolume (AddSubgroup.op <| .zmultiples θ) ℝ volume = ENNReal.ofReal θ := by
  have h := (isAddFundamentalDomain_Ico_zmultiples_op hθ 0 volume).covolume_eq_volume volume
  rw [h, Real.volume_Ico]
  simp

/-- **The covolume of `ℤ` in `ℝ` is `1`.** -/
theorem addCovolume_zmultiples_one_op :
    addCovolume (AddSubgroup.op <| .zmultiples (1 : ℝ)) ℝ volume = 1 := by
  simp [addCovolume_zmultiples_op one_pos]

/-- **Haar rescaling.** For Haar measure `c • volume` on `ℝ`, the covolume of `θℤ` is `c θ`. -/
theorem addCovolume_zmultiples_op_smul {θ : ℝ} (hθ : 0 < θ) (c : ℝ≥0∞) :
    addCovolume (AddSubgroup.op <| .zmultiples θ) ℝ (c • volume) = c * ENNReal.ofReal θ := by
  rw [addCovolume_smul_measure, addCovolume_zmultiples_op hθ]

/-- **Weil's formula for `ℤ ⊂ ℝ`**: `∫_ℝ f = ∫_0^1 ∑_n f(x + n) dx` for measurable
`f : ℝ → [0, ∞]`. -/
theorem lintegral_eq_setLIntegral_Ico_tsum_add_intCast {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ x in Ico (0 : ℝ) 1, ∑' n : ℤ, f (x + n) := by
  have hD := isAddFundamentalDomain_Ico_zmultiples_op one_pos 0 (volume : Measure ℝ)
  rw [zero_add] at hD
  let F : ℤ → (AddSubgroup.zmultiples (1 : ℝ)).op := fun n =>
    ⟨AddOpposite.op (n : ℝ), AddSubgroup.mem_op.2 (AddSubgroup.mem_zmultiples_iff.2 ⟨n, by simp⟩)⟩
  have hF : Bijective F := by
    refine ⟨fun a b h => ?_, fun g => ?_⟩
    · simpa [F] using congrArg (fun g : (AddSubgroup.zmultiples (1 : ℝ)).op =>
        AddOpposite.unop (g : ℝᵃᵒᵖ)) h
    · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (AddSubgroup.mem_op.1 g.property)
      exact ⟨k, Subtype.ext (AddOpposite.unop_injective (by simpa [F] using hk))⟩
  set e := Equiv.ofBijective F hF
  rw [hD.lintegral_eq_tsum', ← lintegral_tsum
    (f := fun (g : (AddSubgroup.zmultiples (1 : ℝ)).op) x => f (-g +ᵥ x)) fun g =>
      (hf.comp (measurable_const_vadd _)).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [← e.tsum_eq, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  congr 1
  change ((-(e (-n)) : (AddSubgroup.zmultiples (1 : ℝ)).op) : ℝᵃᵒᵖ) +ᵥ x = _
  simp [e, F]

/-! ### The side of the coset sum in `S₃` -/

open Equiv

/-- The subgroup `Γ = {1, (0 1)}` of `S₃ = Perm (Fin 3)`, generated by the transposition `(0 1)`. -/
abbrev Γ : Subgroup (Perm (Fin 3)) := Subgroup.zpowers (swap 0 1)

/-- The elements of `Γ` are `1` and `(0 1)`. -/
theorem coe_Γ : (Γ : Set (Perm (Fin 3))) = {1, swap 0 1} := by
  ext g
  simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [zpow_eq_zpow_emod k (n := 2) (by simp [sq])]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> simp [hk]
  · rintro (rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩]

/-- The indicator `f` of the transposition `(0 2)`. -/
def indicatorSwap (g : Perm (Fin 3)) : ℕ := if g = swap 0 2 then 1 else 0

/-- The right-translated coset sum at `(0 2)` is `1`. -/
theorem sum_indicator_mul_swap_zero_two :
    ∑ γ ∈ ({1, swap 0 1} : Finset (Perm (Fin 3))), indicatorSwap (swap 0 2 * γ) = 1 := by
  decide

/-- The right-translated coset sum at `(0 2)(0 1)`, in the same left coset `(0 2) Γ`, is also
`1`. -/
theorem sum_indicator_mul_swap_zero_two_mul_swap_zero_one :
    ∑ γ ∈ ({1, swap 0 1} : Finset (Perm (Fin 3))), indicatorSwap (swap 0 2 * swap 0 1 * γ) = 1 := by
  decide

/-- The left-translated sum at `(0 2)` is `1`. -/
theorem sum_indicator_swap_mul_swap_zero_two :
    ∑ γ ∈ ({1, swap 0 1} : Finset (Perm (Fin 3))), indicatorSwap (γ * swap 0 2) = 1 := by
  decide

/-- The left-translated sum at `(0 2)(0 1)` is `0`, so the left-translated sum is not constant on
the left coset `(0 2) Γ`. -/
theorem sum_indicator_swap_mul_swap_zero_two_mul_swap_zero_one :
    ∑ γ ∈ ({1, swap 0 1} : Finset (Perm (Fin 3))),
      indicatorSwap (γ * (swap 0 2 * swap 0 1)) = 0 := by
  decide

/-- `1`, `(0 2)` and `(1 2)` represent the three left cosets of `Γ`: the products `g γ` exhaust
`S₃`. -/
theorem image_mul_eq_univ :
    ((({1, swap 0 2, swap 1 2} : Finset (Perm (Fin 3))) ×ˢ
      ({1, swap 0 1} : Finset (Perm (Fin 3)))).image fun p => p.1 * p.2) = Finset.univ := by
  decide

/-- **Weil's formula in `S₃`**: summing the right-translated sums over the three left cosets gives
`1 = ∑_g f(g)`. -/
theorem sum_cosets_sum_indicator_mul :
    ∑ g ∈ ({1, swap 0 2, swap 1 2} : Finset (Perm (Fin 3))),
        ∑ γ ∈ ({1, swap 0 1} : Finset (Perm (Fin 3))), indicatorSwap (g * γ) = 1 ∧
      ∑ g, indicatorSwap g = 1 := by
  decide

end TauCeti.Examples.Lattice
