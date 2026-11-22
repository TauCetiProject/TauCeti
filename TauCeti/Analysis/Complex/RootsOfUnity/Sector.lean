/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The power map `z ↦ z ^ d` is `d`-to-one up to a null set

For `d ≠ 0` the map `z ↦ z ^ d` of the complex plane is, away from a set of measure zero, a
`d`-sheeted map onto the slit plane `Complex.slitPlane`. Its sheets are the sectors

`S k = {z | z ^ d ∈ slitPlane ∧ ζ ^ k * (z ^ d) ^ (1 / d) = z}`, `k < d`,

where `ζ = exp (2 π i / d)` and `(z ^ d) ^ (1 / d)` is the principal `d`-th root. On each sector
the power map is injective with image the whole slit plane, the sectors are pairwise disjoint and
measurable, and together they contain every `z` with `z ^ d ∈ slitPlane`
(`TauCeti.exists_pairwise_disjoint_injOn_pow_image_eq_slitPlane`). The remaining points, those with
`z ^ d` a nonpositive real number, lie on the real lines through `0` spanned by
`exp (π i / d) * ζ ^ k`, `k < d`, so they form a null set
(`TauCeti.volume_setOf_pow_notMem_slitPlane`).

This is the decomposition behind the change of variables formula for the branched cover
`z ↦ z ^ d`: an integral over the preimage of a set `t` is `d` times an integral over `t`, one
copy for each sheet.

## Main results

* `TauCeti.volume_setOf_pow_notMem_slitPlane`: the points `z` with `z ^ d ∉ slitPlane` form a null
  set.
* `TauCeti.exists_pairwise_disjoint_injOn_pow_image_eq_slitPlane`: the sector decomposition.
-/

public section

open Function Set MeasureTheory Complex
open scoped Real ComplexOrder

namespace TauCeti

/-- The points `z` of the complex plane at which `z ^ d` is a nonpositive real number form a null
set: for `d ≠ 0` they lie on finitely many real lines through `0`, and for `d = 0` there are
none. -/
theorem volume_setOf_pow_notMem_slitPlane (d : ℕ) :
    volume {z : ℂ | z ^ d ∉ slitPlane} = 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have : NeZero d := ⟨hd⟩
  set c : ℂ := exp (π * I / d)
  set ζ : ℂ := exp (2 * π * I / d)
  have hζ : IsPrimitiveRoot ζ d := isPrimitiveRoot_exp d hd
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hcd : c ^ d = -1 := by
    rw [← exp_natCast_mul, mul_div_cancel₀ _ hd', exp_pi_mul_I]
  -- Each point with `z ^ d ≤ 0` is a real multiple of `c * ζ ^ k` for some `k < d`.
  have hsub : {z : ℂ | z ^ d ∉ slitPlane} ⊆
      ⋃ k ∈ Finset.range d, ((ℝ ∙ (c * ζ ^ k) : Submodule ℝ ℂ) : Set ℂ) := by
    intro z hz
    replace hz : z ^ d ≤ 0 := by simpa [mem_slitPlane_iff_not_le_zero] using hz
    simp only [Finset.mem_range, mem_iUnion, SetLike.mem_coe, Submodule.mem_span_singleton,
      exists_prop]
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨0, Nat.pos_of_ne_zero hd, 0, zero_smul _ _⟩
    obtain ⟨hre, him⟩ := (Complex.le_def.1 hz)
    simp only [zero_re, zero_im] at hre him
    set s : ℝ := -(z ^ d).re
    have hzd : z ^ d = -(s : ℂ) := by
      apply Complex.ext <;> simp [s, him]
    have hs : 0 < s := by
      have hne : z ^ d ≠ 0 := pow_ne_zero _ hz0
      have hre' : (z ^ d).re ≠ 0 := fun h ↦ hne (Complex.ext (by simpa using h) him)
      exact neg_pos.2 (lt_of_le_of_ne hre hre')
    set b : ℝ := s ^ ((d : ℝ)⁻¹)
    have hb : 0 < b := Real.rpow_pos_of_pos hs _
    have hbd : (b : ℂ) ^ d = s := by
      rw [← ofReal_pow, Real.rpow_inv_natCast_pow hs.le hd]
    have hv : (z / (c * b)) ^ d = 1 := by
      rw [div_pow, mul_pow, hcd, hbd, hzd]
      have : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
      field_simp
    obtain ⟨k, hk, hζk⟩ := hζ.eq_pow_of_pow_eq_one hv
    refine ⟨k, hk, b, ?_⟩
    have hc : c ≠ 0 := exp_ne_zero _
    have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
    rw [Complex.real_smul, hζk]
    field_simp
  refine measure_mono_null hsub ((measure_biUnion_null_iff (Finset.range d).countable_toSet).2
    fun k _ ↦ Measure.addHaar_submodule volume _ fun h ↦ ?_)
  -- A line is not the whole plane, which has real dimension two.
  have h₁ := finrank_span_le_card (R := ℝ) ({c * ζ ^ k} : Set ℂ)
  rw [h, finrank_top, Complex.finrank_real_complex] at h₁
  simp at h₁

/-- **The sheets of `z ↦ z ^ d`.** For `d ≠ 0` there are `d` pairwise disjoint measurable sets
`S k`, on each of which `z ↦ z ^ d` is injective with image the slit plane, which together contain
every `z` with `z ^ d` in the slit plane. By `TauCeti.volume_setOf_pow_notMem_slitPlane` the
points they miss form a null set. -/
theorem exists_pairwise_disjoint_injOn_pow_image_eq_slitPlane {d : ℕ} (hd : d ≠ 0) :
    ∃ S : Fin d → Set ℂ, (∀ k, MeasurableSet (S k)) ∧ Pairwise (Disjoint on S) ∧
      (∀ k, InjOn (· ^ d) (S k)) ∧ (∀ k, (· ^ d) '' S k = slitPlane) ∧
      {z : ℂ | z ^ d ∈ slitPlane} ⊆ ⋃ k, S k := by
  have : NeZero d := ⟨hd⟩
  set ζ : ℂ := exp (2 * π * I / d)
  have hζ : IsPrimitiveRoot ζ d := isPrimitiveRoot_exp d hd
  -- The `k`-th sheet is the image of the slit plane under the `k`-th branch of the `d`-th root.
  let S : Fin d → Set ℂ := fun k ↦
    {z | z ^ d ∈ slitPlane ∧ ζ ^ (k : ℕ) * (z ^ d) ^ ((d : ℂ)⁻¹) = z}
  have hroot (w : ℂ) : ((w ^ ((d : ℂ)⁻¹)) ^ d) = w := cpow_nat_inv_pow w hd
  refine ⟨S, fun k ↦ ?_, fun i j hij ↦ ?_, fun k z hz z' hz' h ↦ ?_, fun k ↦ ?_, fun z hz ↦ ?_⟩
  · simp only [S, ofPred_and]
    refine MeasurableSet.inter ?_ ?_
    · exact (continuous_pow d).measurable isOpen_slitPlane.measurableSet
    exact measurableSet_eq_fun (measurable_const.mul
      ((measurable_id.pow_const d).pow_const _)) measurable_id
  · refine Set.disjoint_left.2 fun z hi hj ↦ hij (Fin.ext (hζ.pow_inj i.isLt j.isLt ?_))
    have hne : (z ^ d) ^ ((d : ℂ)⁻¹) ≠ 0 :=
      fun h ↦ slitPlane_ne_zero hi.1 ((cpow_eq_zero_iff _ _).1 h).1
    exact mul_right_cancel₀ hne (hi.2.trans hj.2.symm)
  · simp only at h
    rw [← hz.2, ← hz'.2, h]
  · ext w
    refine ⟨?_, fun hw ↦ ⟨ζ ^ (k : ℕ) * w ^ ((d : ℂ)⁻¹), ?_⟩⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · have hpow : (ζ ^ (k : ℕ) * w ^ ((d : ℂ)⁻¹)) ^ d = w := by
        rw [mul_pow, ← pow_mul, mul_comm (k : ℕ), pow_mul, hζ.pow_eq_one, one_pow, one_mul,
          hroot]
      exact ⟨⟨by rw [hpow]; exact hw, by rw [hpow]⟩, hpow⟩
  · have hz : z ^ d ∈ slitPlane := hz
    set a : ℂ := (z ^ d) ^ ((d : ℂ)⁻¹)
    have ha : a ≠ 0 := fun h ↦ slitPlane_ne_zero hz ((cpow_eq_zero_iff _ _).1 h).1
    have hv : (z / a) ^ d = 1 := by
      rw [div_pow, hroot, div_self (slitPlane_ne_zero hz)]
    obtain ⟨k, hk, hζk⟩ := hζ.eq_pow_of_pow_eq_one hv
    exact mem_iUnion.2 ⟨⟨k, hk⟩, hz, by rw [hζk, div_mul_cancel₀ _ ha]⟩

end TauCeti
