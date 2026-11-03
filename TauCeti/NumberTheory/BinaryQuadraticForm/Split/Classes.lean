/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Triangular representatives of split proper classes

For nonzero square discriminant `s²`, primitive forms admit triangular representatives
`sxy + cy²`, with the specified integer square root `s` coprime to `c`. These are norm forms
of explicit integer lattices inside the existing product algebra. Proper equivalence between two
representatives with the same nonzero `s` is exactly congruence of `c` modulo `s`. Every form
of discriminant `s²`, primitive or not, is properly equivalent to `sxy + cy²` with `0 ≤ c < |s|`.
A proper equivalence between two representatives fixes the line `y = 0`, so the only
automorphisms of `sxy + cy²` are `±1`, and every form of nonzero square discriminant has a
stabiliser of order `2`.

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
@[simp] theorem eval_splitTriangularForm (s c x y : ℤ) :
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

/-- A proper equivalence between two triangular forms with the same nonzero `s` fixes the
isotropic line `y = 0` of both: its lower left entry vanishes. -/
theorem apply_one_zero_eq_zero_of_smul_splitTriangularForm_eq {s c d : ℤ} (hs : s ≠ 0)
    {γ : SL(2, ℤ)} (hγ : γ • splitTriangularForm s c = splitTriangularForm s d) : γ 1 0 = 0 := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have ha := congrArg BinaryQuadraticForm.a hγ
  have hb := congrArg BinaryQuadraticForm.b hγ
  simp only [smul_a, smul_b, splitTriangularForm, zero_mul, zero_sub] at ha hb
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

/-- For a fixed nonzero square root, triangular forms are properly equivalent exactly
when their last coefficients are congruent modulo that root. -/
theorem exists_smul_splitTriangularForm_eq_iff (s c d : ℤ) (hs : s ≠ 0) :
    (∃ γ : SL(2, ℤ), γ • splitTriangularForm s c = splitTriangularForm s d) ↔
      s ∣ c - d := by
  constructor
  · rintro ⟨γ, hγ⟩
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    have hc := congrArg BinaryQuadraticForm.c hγ
    simp only [smul_c, splitTriangularForm, zero_mul, zero_sub] at hc
    have hr := apply_one_zero_eq_zero_of_smul_splitTriangularForm_eq hs hγ
    have hpt : γ 0 0 * γ 1 1 = 1 := by simpa only [hr, mul_zero, sub_zero] using hdet
    have hp2 : γ 0 0 ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hpt with hp | hp <;> simp [hp]
    refine ⟨γ 0 0 * γ 0 1, ?_⟩
    linear_combination hc - c * hp2
  · rintro ⟨n, hn⟩
    refine ⟨ModularGroup.T ^ n, ?_⟩
    ext <;> simp [splitTriangularForm]
    linear_combination hn

/-- **The automorphisms of a triangular form are `±1`**: for `s ≠ 0`, the only proper changes of
variables fixing `s x y + c y²` are `1` and `-1`. -/
theorem smul_splitTriangularForm_eq_self_iff {s : ℤ} (hs : s ≠ 0) (c : ℤ) {γ : SL(2, ℤ)} :
    γ • splitTriangularForm s c = splitTriangularForm s c ↔ γ = 1 ∨ γ = -1 := by
  refine ⟨fun hγ ↦ ?_, by rintro (rfl | rfl) <;> ext <;> simp [splitTriangularForm]⟩
  have hr := apply_one_zero_eq_zero_of_smul_splitTriangularForm_eq hs hγ
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hr, mul_zero, sub_zero] at hdet
  have hc := congrArg BinaryQuadraticForm.c hγ
  simp only [smul_c, splitTriangularForm, zero_mul, zero_sub] at hc
  -- the diagonal entries are both `1` or both `-1`, and then `s γ₀₁ = 0` forces `γ₀₁ = 0`
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with hp | hp <;>
    have hq : γ 1 1 = γ 0 0 := by grind
  · have hb : γ 0 1 = 0 := by simpa [hp, hs] using hc
    left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hb, hr]
  · have hb : γ 0 1 = 0 := by simpa [hp, hs] using hc
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hb, hr]

/-- **Triangular representatives of every form of square discriminant.** An integral binary
quadratic form of discriminant `s²`, with `s ≠ 0`, is properly equivalent to the triangular form
`s x y + c y²` for some `0 ≤ c < |s|`. The form need not be primitive. -/
theorem exists_smul_eq_splitTriangularForm_of_discrim_eq_sq (f : BinaryQuadraticForm ℤ) {s : ℤ}
    (hs : s ≠ 0) (hf : f.discrim = s ^ 2) :
    ∃ γ : SL(2, ℤ), ∃ c : ℤ, 0 ≤ c ∧ c < |s| ∧ γ • f = splitTriangularForm s c := by
  obtain ⟨γ, c, hγ⟩ : ∃ γ : SL(2, ℤ), ∃ c : ℤ, γ • f = splitTriangularForm s c := by
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact pow_ne_zero 2 hs (by simpa [discrim_def, discrim] using hf.symm)
    have hn : (f.content : ℤ) ≠ 0 := by exact_mod_cast (f.content_pos_iff.mpr hf0).ne'
    -- the square of the content divides `s ^ 2`, so the content divides `s`
    obtain ⟨t, rfl⟩ : (f.content : ℤ) ∣ s := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero, ← hf, discrim_eq_content_sq_mul]
      exact dvd_mul_right _ _
    have hg : f.primPart.discrim = t ^ 2 := by
      have h := f.discrim_eq_content_sq_mul
      rw [hf, mul_pow] at h
      exact (mul_left_cancel₀ (pow_ne_zero 2 hn) h).symm
    obtain ⟨γ, e, hγ, -⟩ :=
      exists_smul_eq_splitTriangularForm f.primPart t hg (f.isPrimitive_primPart hf0)
    refine ⟨γ, f.content * e, ?_⟩
    rw [← f.content_smul_primPart, smul_comm, hγ]
    ext <;> simp [splitTriangularForm]
  obtain ⟨τ, hτ⟩ := (exists_smul_splitTriangularForm_eq_iff s c (c % s) hs).mpr
    Int.dvd_self_sub_emod
  exact ⟨τ * γ, c % s, Int.emod_nonneg c hs, Int.emod_lt_abs c hs, by rw [mul_smul, hγ, hτ]⟩

/-- The triangular form `s x y + c y²` with `s ≠ 0` has exactly the two automorphisms `±1`. -/
theorem card_stabilizer_splitTriangularForm {s : ℤ} (hs : s ≠ 0) (c : ℤ) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) (splitTriangularForm s c)) = 2 := by
  have h : (MulAction.stabilizer SL(2, ℤ) (splitTriangularForm s c) : Set SL(2, ℤ)) =
      ↑({1, -1} : Finset SL(2, ℤ)) := by
    ext γ
    simp [MulAction.mem_stabilizer_iff, smul_splitTriangularForm_eq_self_iff hs]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

/-- **Forms of nonzero square discriminant have only the automorphisms `±1`**: if
`f.discrim = s²` with `s ≠ 0`, the stabiliser of `f` in `SL(2, ℤ)` has order `2`. -/
theorem card_stabilizer_of_discrim_eq_sq {f : BinaryQuadraticForm ℤ} {s : ℤ} (hs : s ≠ 0)
    (hf : f.discrim = s ^ 2) : Nat.card (MulAction.stabilizer SL(2, ℤ) f) = 2 := by
  obtain ⟨γ, c, -, -, hγ⟩ := exists_smul_eq_splitTriangularForm_of_discrim_eq_sq f hs hf
  rw [← card_stabilizer_smul γ f, hγ, card_stabilizer_splitTriangularForm hs]

/-- Equality in the existing proper-class quotient is the same congruence criterion. -/
@[simp] theorem properClass_splitTriangularForm_eq_iff (s c d : ℤ) (hs : s ≠ 0) :
    (Quotient.mk'' (splitTriangularForm s c) :
        MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ)) =
      Quotient.mk'' (splitTriangularForm s d) ↔ s ∣ c - d := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    exists_smul_splitTriangularForm_eq_iff s d c hs]
  constructor <;> intro h <;> simpa only [neg_sub] using h.neg_right

end TauCeti.BinaryQuadraticForm
