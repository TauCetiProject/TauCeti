/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Triangular representatives of split proper classes

For nonzero square discriminant `s²`, primitive forms admit triangular representatives
`sxy + cy²`, with `s` positive and `s` coprime to `c`. These are norm forms of explicit
integer lattices inside the existing product algebra. Proper equivalence between two
representatives with the same nonzero `s` is exactly congruence of `c` modulo `s`.

This is the elementary form-side classification for the separate split branch. Composition
is constructed from these classes and the actual product-order lattices in subsequent results.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (proper-equivalence conventions).
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- The triangular split form `sxy + cy²`. -/
def splitTriangularForm (s c : ℤ) : BinaryQuadraticForm ℤ := ⟨0, s, c⟩

/-- The triangular form's coefficients. -/
theorem splitTriangularForm_def (s c : ℤ) : splitTriangularForm s c = ⟨0, s, c⟩ := by
  rfl

/-- The triangular split form has square discriminant. -/
@[simp] theorem discrim_splitTriangularForm (s c : ℤ) :
    (splitTriangularForm s c).discrim = s ^ 2 := by
  simp [splitTriangularForm, discrim_def, discrim]

/-- Primitivity is precisely coprimality of the two remaining coefficients. -/
@[simp] theorem isPrimitive_splitTriangularForm (s c : ℤ) :
    (splitTriangularForm s c).IsPrimitive ↔ IsCoprime s c := by
  simp [splitTriangularForm, isPrimitive_iff, content_def, Int.isCoprime_iff_gcd_eq_one]

/-- The triangular form evaluates as the product of its two linear factors. -/
theorem eval_splitTriangularForm (s c x y : ℤ) :
    (splitTriangularForm s c).eval x y = (s * x + c * y) * y := by
  simp only [splitTriangularForm, eval_def]
  ring

/-- The triangular form is the product-algebra norm on the lattice spanned by `(s, 0)`
and `(c, 1)`. -/
theorem eval_splitTriangularForm_eq_norm (s c x y : ℤ) :
    (splitTriangularForm s c).eval x y =
      Algebra.norm ℤ ((s * x + c * y, y) : ℤ × ℤ) := by
  rw [eval_splitTriangularForm, ← eval_splitPrincipalForm_eq_norm, eval_splitPrincipalForm]

private theorem exists_smul_neg_splitTriangularForm (s c : ℤ) (hc : IsCoprime s c) :
    ∃ γ : SL(2, ℤ), ∃ d : ℤ, γ • splitTriangularForm (-s) c = splitTriangularForm s d := by
  obtain ⟨ρ, hp, hr⟩ := hc.symm.exists_SL2_col 0
  refine ⟨ρ⁻¹, ρ 1 1, ?_⟩
  have hdet : c * ρ 1 1 - ρ 0 1 * s = 1 := by
    have h := ρ.det_coe
    rw [Matrix.det_fin_two] at h
    simpa only [hp, hr] using h
  apply BinaryQuadraticForm.ext
  · rw [smul_a]
    simp [splitTriangularForm, Matrix.SpecialLinearGroup.SL2_inv_expl, hp, hr]
    ring
  · rw [smul_b]
    simp [splitTriangularForm, Matrix.SpecialLinearGroup.SL2_inv_expl, hp, hr]
    linear_combination s * hdet
  · rw [smul_c]
    simp [splitTriangularForm, Matrix.SpecialLinearGroup.SL2_inv_expl, hp, hr]
    linear_combination (ρ 1 1) * hdet

/-- Every primitive form of square discriminant has a triangular proper representative
with coprime coefficients. -/
theorem exists_smul_eq_splitTriangularForm (f : BinaryQuadraticForm ℤ) (s : ℤ)
    (hf : f.discrim = s ^ 2) (hp : f.IsPrimitive) :
    ∃ γ : SL(2, ℤ), ∃ c : ℤ, γ • f = splitTriangularForm s c ∧ IsCoprime s c := by
  obtain ⟨ρ, ha⟩ := exists_smul_a_eq_zero_of_discrim_eq_sq f s hf
  let g := ρ • f
  have hga : g.a = 0 := ha
  have hg : g.discrim = s ^ 2 := (discrim_smul ρ f).trans hf
  have hb2 : g.b ^ 2 = s ^ 2 := by simpa [discrim_def, discrim, hga] using hg
  have hprim : g.IsPrimitive := (isPrimitive_smul_iff f ρ).mpr hp
  have hform : g = splitTriangularForm g.b g.c := by
    ext <;> simp [splitTriangularForm, hga]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb2 with hb | hb
  · refine ⟨ρ, g.c, ?_, ?_⟩
    · simpa only [hb] using hform
    · rw [hform] at hprim
      simpa only [isPrimitive_splitTriangularForm, hb] using hprim
  · have hshape : ρ • f = splitTriangularForm (-s) g.c := by
      simpa only [hb] using hform
    have hcneg : IsCoprime (-s) g.c :=
      (isPrimitive_splitTriangularForm (-s) g.c).mp (hshape ▸ hprim)
    have hc : IsCoprime s g.c := by simpa only [neg_neg] using hcneg.neg_left
    obtain ⟨τ, d, hτ⟩ := exists_smul_neg_splitTriangularForm s g.c hc
    have hγ : (τ * ρ) • f = splitTriangularForm s d := by
      rw [mul_smul, hshape, hτ]
    refine ⟨τ * ρ, d, hγ, ?_⟩
    exact (isPrimitive_splitTriangularForm s d).mp
      (hγ ▸ (isPrimitive_smul_iff f (τ * ρ)).mpr hp)

/-- For a fixed nonzero square root, triangular forms are properly equivalent exactly
when their last coefficients are congruent modulo that root. -/
theorem exists_smul_splitTriangularForm_eq_iff (s c d : ℤ) (hs : s ≠ 0) :
    (∃ γ : SL(2, ℤ), γ • splitTriangularForm s c = splitTriangularForm s d) ↔
      s ∣ c - d := by
  constructor
  · rintro ⟨γ, hγ⟩
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    have ha := congrArg BinaryQuadraticForm.a hγ
    have hb := congrArg BinaryQuadraticForm.b hγ
    have hc := congrArg BinaryQuadraticForm.c hγ
    simp only [smul_a, smul_b, smul_c, splitTriangularForm, zero_mul, zero_sub] at ha hb hc
    have hr : γ 1 0 = 0 := by
      by_contra hr
      have hmul₁ : γ 1 0 * (c * γ 1 0 - s * γ 1 1) = 0 := by
        linear_combination ha
      have hrel₁ : c * γ 1 0 = s * γ 1 1 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hmul₁).resolve_left hr)
      have hmul₂ : (2 * γ 1 0) * (s * γ 0 1 - c * γ 0 0) = 0 := by
        linear_combination hb - s * hdet
      have hrel₂ : s * γ 0 1 = c * γ 0 0 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hmul₂).resolve_left
          (mul_ne_zero (by decide) hr))
      apply hs
      linear_combination -s * hdet - γ 0 0 * hrel₁ - γ 1 0 * hrel₂
    have hpt : γ 0 0 * γ 1 1 = 1 := by simpa only [hr, mul_zero, sub_zero] using hdet
    have hp2 : γ 0 0 ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hpt with hp | hp <;> simp [hp]
    refine ⟨γ 0 0 * γ 0 1, ?_⟩
    linear_combination hc - c * hp2
  · rintro ⟨n, hn⟩
    refine ⟨ModularGroup.T ^ n, ?_⟩
    ext <;> simp [splitTriangularForm, smul_a, smul_b, smul_c, ModularGroup.coe_T_zpow]
    linear_combination hn

/-- Equality in the existing proper-class quotient is the same congruence criterion. -/
theorem properClass_splitTriangularForm_eq_iff (s c d : ℤ) (hs : s ≠ 0) :
    (Quotient.mk'' (splitTriangularForm s c) :
        MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ)) =
      Quotient.mk'' (splitTriangularForm s d) ↔ s ∣ c - d := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    exists_smul_splitTriangularForm_eq_iff s d c hs]
  constructor <;> intro h <;> simpa only [neg_sub] using h.neg_right

end TauCeti.BinaryQuadraticForm
