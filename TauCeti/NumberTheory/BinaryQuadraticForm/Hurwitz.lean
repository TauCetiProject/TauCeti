/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.PrimitiveReduced
import Mathlib.NumberTheory.Divisors
import TauCeti.Algebra.QuadraticDiscriminant

/-!
# Hurwitz class numbers and primitive reduced forms

Separating a reduced form into its content and primitive part decomposes the Hurwitz class
number into primitive class counts over square divisors of the discriminant. Positive scaling
preserves the boundary convention for reduction and the Hurwitz weight. Primitive forms have
weight one except at discriminants `-3` and `-4`, where their weights are `1/3` and `1/2`.

The primitive counts are the unweighted proper class numbers by
`BinaryQuadraticForm.nat_card_posDefProperClass`. Thus the square-divisor formula separates
both the imprimitive forms and the exceptional automorphisms from the ordinary class count.

## References

* D. Zagier, *Nombres de classes et formes modulaires de poids 3/2*, C. R. Acad. Sci. Paris
  Sér. A-B **281** (1975).
* D. A. Cox, *Primes of the Form x² + ny²*, §2.
-/

public section

open Finset

namespace TauCeti

/-- The Hurwitz weight on primitive reduced forms depends only on the discriminant. The only
exceptions to weight one are `-3` and `-4`. -/
theorem reducedFormWeight_of_mem_primitiveReducedForms {D : ℕ} (hD : D ≠ 0)
    {f : BinaryQuadraticForm ℤ} (hf : f ∈ primitiveReducedForms D) :
    reducedFormWeight f = if D = 4 then 1 / 2 else if D = 3 then 1 / 3 else 1 := by
  obtain ⟨hdisc, hred, hprim⟩ := (mem_primitiveReducedForms hD).mp hf
  obtain ⟨u, v, w, huv⟩ := hprim.exists_linearCombination_eq_one
  have ha : 0 ≤ f.a := le_trans (abs_nonneg _) hred.1
  -- At the two smallest negative discriminants the reduction inequalities force a = c = 1.
  have hsmall (h : D ≤ 4) : f.a = 1 ∧ f.c = 1 := by
    have hb := sq_le_sq' (abs_le.mp hred.1).1 (abs_le.mp hred.1).2
    have hac := mul_le_mul_of_nonneg_left hred.2.1 ha
    have heq := hdisc
    rw [BinaryQuadraticForm.discrim_def, discrim] at heq
    have hapos : 0 < f.a := pos_of_nonneg_of_discrim_lt_zero ha (by
      simpa only [BinaryQuadraticForm.discrim_def] using hdisc.trans_lt (by omega))
    have halt : f.a < 2 := by nlinarith
    have ha1 : f.a = 1 := by omega
    refine ⟨ha1, ?_⟩
    rw [ha1] at heq hb
    nlinarith [hred.2.1]
  -- Primitivity forces an exceptional shape to have scale one; the converse uses reduction.
  have h₄ : f.b = 0 ∧ f.a = f.c ↔ D = 4 := by
    constructor
    · rintro ⟨hb, hac⟩
      have hunit : IsUnit f.a := isUnit_iff_dvd_one.mpr ⟨u + w, by
        rw [hb, ← hac] at huv
        nlinarith [huv]⟩
      have ha1 : f.a = 1 := by rcases Int.isUnit_iff.mp hunit with h | h <;> omega
      simp [BinaryQuadraticForm.discrim_def, discrim, hb, ← hac, ha1] at hdisc
      omega
    · intro h
      obtain ⟨ha1, hc1⟩ := hsmall (by omega)
      refine ⟨?_, ha1.trans hc1.symm⟩
      rw [BinaryQuadraticForm.discrim_def, discrim, ha1, hc1] at hdisc
      nlinarith
  have h₃ : f.a = f.b ∧ f.b = f.c ↔ D = 3 := by
    constructor
    · rintro ⟨hab, hbc⟩
      have hunit : IsUnit f.a := isUnit_iff_dvd_one.mpr ⟨u + v + w, by
        rw [← hbc, ← hab] at huv
        nlinarith [huv]⟩
      have ha1 : f.a = 1 := by rcases Int.isUnit_iff.mp hunit with h | h <;> omega
      simp [BinaryQuadraticForm.discrim_def, discrim, ← hbc, ← hab, ha1] at hdisc
      omega
    · intro h
      obtain ⟨ha1, hc1⟩ := hsmall (by omega)
      have hb0 := hred.2.2 (Or.inr (ha1.trans hc1.symm))
      rw [BinaryQuadraticForm.discrim_def, discrim, ha1, hc1] at hdisc
      have hb1 : f.b = 1 := by nlinarith
      exact ⟨ha1.trans hb1.symm, hb1.trans hc1.symm⟩
  simp only [reducedFormWeight, h₄, h₃]

/-- The total weight of primitive reduced forms is their unweighted class count divided by
three at discriminant `-3`, by two at `-4`, and by one otherwise. -/
theorem sum_primitiveReducedForms_weight {D : ℕ} (hD : D ≠ 0) :
    ∑ f ∈ primitiveReducedForms D, reducedFormWeight f =
      (#(primitiveReducedForms D) : ℚ) / (if D = 3 then 3 else if D = 4 then 2 else 1) := by
  calc
    _ = ∑ _f ∈ primitiveReducedForms D,
        (if D = 4 then (1 / 2 : ℚ) else if D = 3 then 1 / 3 else 1) :=
      sum_congr rfl fun _ hf => reducedFormWeight_of_mem_primitiveReducedForms hD hf
    _ = _ := by
      by_cases h₄ : D = 4 <;> by_cases h₃ : D = 3 <;>
        simp [h₄, h₃, nsmul_eq_mul, div_eq_mul_inv]

/-- **The square-divisor formula for Hurwitz class numbers.** Each content `d` with `d² ∣ D`
contributes the primitive proper class number at discriminant `-(D / d²)`, with the exceptional
unit weights at `-3` and `-4`. In particular this includes all imprimitive forms. -/
theorem hurwitzClassNumber_eq_sum_primitiveReducedForms {D : ℕ} (hD : D ≠ 0) :
    hurwitzClassNumber D =
      ∑ d ∈ D.divisors with d ^ 2 ∣ D,
        (#(primitiveReducedForms (D / d ^ 2)) : ℚ) /
          (if D / d ^ 2 = 3 then 3 else if D / d ^ 2 = 4 then 2 else 1) := by
  have hmaps (f : BinaryQuadraticForm ℤ) (hf : f ∈ reducedForms D) :
      f.content ∈ D.divisors.filter (fun d => d ^ 2 ∣ D) := by
    have hdisc := (mem_reducedForms hD).mp hf |>.1
    have hdiv : f.content ^ 2 ∣ D := by
      have hi : (f.content : ℤ) ^ 2 ∣ (D : ℤ) := by
        refine ⟨-f.primPart.discrim, ?_⟩
        linear_combination -(hdisc.symm.trans f.discrim_eq_content_sq_mul)
      exact_mod_cast hi
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(dvd_mul_right f.content f.content).trans (by simpa [pow_two] using hdiv), hD⟩, hdiv⟩
  rw [hurwitzClassNumber_of_ne_zero hD, ← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro d hd
  have hdiv := (mem_filter.mp hd).2
  have hd0 : d ≠ 0 := by rintro rfl; simp [hD] at hdiv
  have hpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hquot : D / d ^ 2 ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hdiv)
    (pow_pos hpos _)).ne'
  rw [reducedForms_filter_content_eq_image hD hpos hdiv, sum_image]
  · simp_rw [← natCast_zsmul, reducedFormWeight_zsmul (r := (d : ℤ)) (by exact_mod_cast hd0)]
    exact sum_primitiveReducedForms_weight hquot
  · intro f hf g hg heq
    exact smul_right_injective (M := BinaryQuadraticForm ℤ) (r := (d : ℤ))
      (by exact_mod_cast hd0) (by simpa only [natCast_zsmul] using heq)

end TauCeti
