/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct
import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt
import TauCeti.Data.ZMod.Count

/-!
# Cotangent expression for odd Dirichlet L-values

For an odd Dirichlet character, the continued value at one is a finite cotangent sum.
The identity uses ordered partial sums, not an unconditionally convergent Dirichlet series
at one. The form `DirichletCharacter.two_mul_LFunction_one_eq_sum_range_mul_cot` sums over the
natural residue representatives, for explicit finite computations. It allows the nonvanishing of
the L-value to be applied to the constant terms of
weight-one Eisenstein series. The analytic inputs are the regularized partial-fraction
expansion `TauCeti.hasSum_one_div_sub_intCast_add_one_div_intCast` and the ordered convergence
`DirichletCharacter.tendsto_sum_Icc_div_LFunction_one`.

When every unit is `1` or `-1`, the sum reduces to `π / N * cot (π / N)`.
The public level-three and level-four evaluations specialize this identity with the canonical
tangent values; oddness supplies the nonprincipal condition and excludes the degenerate levels.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4.
-/

public noncomputable section

open Complex Finset Filter
open scoped Topology Real

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

private lemma tendsto_sum_symmetric (hχ : χ.Odd) :
    Tendsto (fun K : ℕ ↦ ∑ n ∈ Ico (-((K * N : ℕ) : ℤ)) ((K * N : ℕ) : ℤ), χ n / (n : ℂ))
      atTop (𝓝 (2 * χ.LFunction 1)) := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    exact Odd.not_even 1 hχ even_one
  have hlim := (χ.tendsto_sum_Icc_div_LFunction_one hχ1).comp
    (tendsto_id.atTop_mul_const' (NeZero.pos N))
  refine (hlim.const_mul 2).congr fun K ↦ ?_
  dsimp only [Function.comp_apply, id_eq]
  symm
  have heven : (fun n : ℤ ↦ χ n / (n : ℂ)).Even := by
    intro n
    simp [hχ.eval_neg]
  have hN1 : N ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hendpoint : χ ((K * N : ℕ) : ℤ) / (((K * N : ℕ) : ℤ) : ℂ) = 0 := by
    simp [Nat.cast_mul, χ.map_zero' hN1]
  have hIcc := sum_Icc_eq_sum_Ico_add (fun n : ℤ ↦ χ n / (n : ℂ))
    (l := -((K * N : ℕ) : ℤ)) (u := ((K * N : ℕ) : ℤ)) (by omega)
  rw [hendpoint, add_zero] at hIcc
  rw [← hIcc, sum_Icc_of_even_eq_range heven]
  simp only [Int.cast_zero, div_zero, sub_zero, two_nsmul]
  rw [sum_range_eq_add_Ico _ (by omega : 1 ≤ K * N + 1)]
  simp [Ico_add_one_right_eq_Icc, two_mul]

/-- An odd character's continued L-value at one is its finite cotangent sum divided by `2N`.
No primitivity hypothesis is needed. -/
theorem two_mul_LFunction_one_eq_sum_mul_cot (hχ : χ.Odd) :
    2 * χ.LFunction 1 =
      ∑ a : ZMod N, χ a / N * (π * cot (π * (a.val / N))) := by
  classical
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    exact Odd.not_even 1 hχ even_one
  have hN1 : N ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Regularization makes each residue series absolutely summable.
  have hs (a : ZMod N) : HasSum
      (fun z : ℤ ↦ χ a / N * (1 / (a.val / N + z) - 1 / (z : ℂ)))
      (χ a / N * (π * cot (π * (a.val / N)))) := by
    by_cases ha : a = 0
    · simp [ha, χ.map_zero' hN1]
    have hw : (a.val / (N : ℂ)) ∈ integerComplement := by
      rw [mem_integerComplement_iff]
      rintro ⟨z, hz⟩
      have hzre := congrArg Complex.re hz
      have ha0 : 0 < a.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
      have haN := a.val_lt
      simp only [div_natCast_re, natCast_re, intCast_re] at hzre
      have : (a.val : ℝ) / N < 1 :=
        (div_lt_one (Nat.cast_pos.mpr (NeZero.pos N))).mpr (by exact_mod_cast haN)
      have : (0 : ℝ) < (z : ℝ) ∧ (z : ℝ) < 1 := by
        constructor
        · rw [hzre]
          exact div_pos (by exact_mod_cast ha0) (Nat.cast_pos.mpr (NeZero.pos N))
        · simpa [hzre] using this
      norm_cast at this
      omega
    have ht := (TauCeti.hasSum_one_div_sub_intCast_add_one_div_intCast hw)
    have ht' := (Equiv.neg ℤ).hasSum_iff.mpr ht
    convert ht'.mul_left (χ a / N) using 1
    simp [sub_eq_add_neg]
  have hsum := hasSum_sum (s := univ) fun a _ ↦ hs a
  -- The regularizing terms cancel by the zero sum of a nonprincipal character.
  have hterm (z : ℤ) :
      (∑ a : ZMod N, χ a / N * (1 / (a.val / N + z) - 1 / (z : ℂ))) =
        ∑ a : ZMod N, χ a / ((a.val : ℂ) + N * z) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, ← sum_div,
      MulChar.sum_eq_zero_of_ne_one hχ1, zero_div, zero_mul, sub_zero]
    apply sum_congr rfl
    intro a _
    rw [div_add' _ _ _ hN, one_div, inv_div]
    field_simp
  -- Regroup only finite intervals; the unregularized Dirichlet series is conditional.
  have hlim := SummationFilter.hasSum_symmetricIco_int_iff.mp
    ((hsum.congr_fun fun z ↦ (hterm z).symm).mono_left
      (SummationFilter.symmetricIco ℤ).le_atTop)
  refine tendsto_nhds_unique (tendsto_sum_symmetric χ hχ) ?_
  refine hlim.congr fun K ↦ ?_
  simpa [Nat.cast_mul, mul_comm] using
    (ZMod.sum_Ico_mul (n := N) (-(K : ℤ)) K (fun k ↦ χ k / (k : ℂ)))

/-- The finite cotangent formula for an odd character, summed over the natural residue
representatives `0, …, N - 1`. -/
theorem two_mul_LFunction_one_eq_sum_range_mul_cot (hχ : χ.Odd) :
    2 * χ.LFunction 1 =
      ∑ a ∈ range N, χ a / N * (π * cot (π * ((a : ℂ) / N))) := by
  rw [χ.two_mul_LFunction_one_eq_sum_mul_cot hχ]
  simpa only [ZMod.natCast_zmod_val] using
    ZMod.sum_val_eq_sum_range (n := N)
      (fun a ↦ χ a / N * (π * cot (π * ((a : ℂ) / N))))

/-- If every unit at a nonzero level is `1` or `-1`, the cotangent sum for an odd
character has only those two equal contributions. Oddness excludes the degenerate levels. -/
theorem LFunction_one_eq_pi_div_mul_cot_of_units_eq_one_or_neg_one (hχ : χ.Odd)
    (hunits : ∀ u : (ZMod N)ˣ, (u : ZMod N) = 1 ∨ (u : ZMod N) = -1) :
    χ.LFunction 1 = π / N * cot (π / N) := by
  classical
  have hχ1 : χ ≠ 1 := fun h ↦ Odd.not_even 1 (h ▸ hχ) even_one
  have hN1 : N ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hneg : χ (-1) = -1 := hχ
  have hdistinct : (1 : ZMod N) ≠ -1 := by
    intro heq
    have := congrArg χ heq
    rw [map_one, hneg] at this
    norm_num at this
  have hval : (((-1 : ZMod N).val : ℕ) : ℂ) = N - 1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
    simp only [ZMod.val_neg_one, Nat.cast_succ, add_sub_cancel_right]
  have hangle : π * (((N : ℂ) - 1) / N) = π - π / N := by
    field_simp
  have hsum := Finset.sum_subset (s₁ := {1, -1}) (s₂ := univ)
    (f := fun a : ZMod N ↦ χ a / N * (π * cot (π * (a.val / N))))
    (by simp) (by
      intro a _ ha
      have hnonunit : ¬ IsUnit a := by
        intro hu
        have h := hunits hu.unit
        rw [IsUnit.unit_spec] at h
        exact ha (by simpa only [Finset.mem_insert, Finset.mem_singleton] using h)
      simp only [χ.map_nonunit hnonunit, zero_div, zero_mul])
  have h := χ.two_mul_LFunction_one_eq_sum_mul_cot hχ
  rw [← hsum, sum_pair hdistinct] at h
  simp only [map_one, hneg, ZMod.val_one'' hN1, Nat.cast_one, hval, mul_one_div,
    hangle, cot_pi_sub] at h
  linear_combination h / 2

/-- Every odd character modulo four has continued L-value `π / 4` at one. -/
theorem LFunction_one_eq_pi_div_four (χ : DirichletCharacter ℂ 4) (hχ : χ.Odd) :
    χ.LFunction 1 = Real.pi / 4 := by
  have h := χ.LFunction_one_eq_pi_div_mul_cot_of_units_eq_one_or_neg_one hχ (by decide)
  have ht : tan ((Real.pi : ℂ) / 4) = 1 := by exact_mod_cast Real.tan_pi_div_four
  have hc : cot ((Real.pi : ℂ) / 4) = 1 := by
    simpa only [tan_inv_eq_cot, inv_one] using congrArg Inv.inv ht
  simpa only [Nat.cast_ofNat, hc, mul_one] using h

/-- Every odd character modulo three has continued L-value `π / (3√3)` at one. -/
theorem LFunction_one_eq_pi_div_three_mul_sqrt_three (χ : DirichletCharacter ℂ 3)
    (hχ : χ.Odd) : χ.LFunction 1 = Real.pi / (3 * (Real.sqrt 3 : ℂ)) := by
  have h := χ.LFunction_one_eq_pi_div_mul_cot_of_units_eq_one_or_neg_one hχ (by decide)
  have ht : tan ((Real.pi : ℂ) / 3) = (Real.sqrt 3 : ℂ) := by
    exact_mod_cast Real.tan_pi_div_three
  have hc : cot ((Real.pi : ℂ) / 3) = (Real.sqrt 3 : ℂ)⁻¹ := by
    simpa only [tan_inv_eq_cot] using congrArg Inv.inv ht
  rw [h]
  norm_num only [Nat.cast_ofNat]
  rw [hc]
  ring

end DirichletCharacter
