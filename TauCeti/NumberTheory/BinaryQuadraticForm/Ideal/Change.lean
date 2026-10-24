/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Proper
public import Mathlib.RingTheory.QuadraticAlgebra
public import Mathlib.RingTheory.ClassGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.Linarith

/-!
# Form ideals under proper changes of variables

For the left action `γ • f = f ∘ γ⁻¹`, write `γ = !![p,q;r,s]` and
`β = (-b + √D)/2`. The transformed ideal is the original ideal multiplied by
`star (a s + r β) / a`. This factor has norm `a'/a`, where `a'` is the transformed
leading coefficient. The two basis-vector identities require a nonzero original leading
coefficient and also cover square discriminants and a zero transformed leading coefficient.
The norm formula holds even when the original leading coefficient is zero, when both sides vanish.
Positivity of the norm is equivalent to positivity of `a * a'`, the comparison needed for
the oriented narrow class. The canonical norm statements use `QuadraticAlgebra.norm`;
the existing algebra-norm bridge also simplifies `Algebra.norm` expressions. The factor is
nonzero whenever the original leading coefficient is nonzero, at any quadratic parameter.
The native fractional-ideal statements use the nonsquare hypothesis.

Conversely, a positive-norm homothety between the fractional ideals of positive-leading
forms gives a proper equivalence, for either sign of nonsquare discriminant
(`exists_smul_eq_of_fractionalIdeal_eq_of_norm_pos`). The orientation of their two ideal
bases determines the sign of the integral change-of-basis determinant, independently of
any Picard-class construction.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra FractionalIdeal
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

/-- The ideal-scaling factor for the left proper-equivalence action, defined using the
rational inverse of the leading coefficient at any discriminant. -/
def idealChangeFactor (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (γ : SL(2, ℤ)) : QuadraticAlgebra ℚ (D : ℚ) 0 :=
  ((f.a : ℚ)⁻¹) •
    star (γ 1 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + γ 1 0 • f.idealGenerator D)

/-- Scaling the first changed basis vector gives the new leading coefficient. -/
@[simp] theorem idealChangeFactor_mul_first (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) (γ : SL(2, ℤ)) :
    f.idealChangeFactor D γ *
      ((γ 1 1 : QuadraticAlgebra ℚ (D : ℚ) 0) * f.a +
        (γ 1 0 : QuadraticAlgebra ℚ (D : ℚ) 0) * f.idealGenerator D) =
        (γ • f).a := by
  have haQ : (f.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  ext <;> simp [idealChangeFactor, smul_a, pow_two]
  · field_simp [haQ]
    nlinarith [congrArg (fun z : ℚ ↦ (γ 1 0 : ℚ) ^ 2 * z) hd]
  · ring

/-- Scaling the second changed basis vector gives the new second ideal generator. -/
@[simp] theorem idealChangeFactor_mul_second (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (ha : f.a ≠ 0) (γ : SL(2, ℤ)) :
    f.idealChangeFactor D γ *
      ((γ 0 1 : QuadraticAlgebra ℚ (D : ℚ) 0) * f.a +
        (γ 0 0 : QuadraticAlgebra ℚ (D : ℚ) 0) * f.idealGenerator D) =
        (γ • f).idealGenerator D := by
  have haQ : (f.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hd : (f.b : ℚ) ^ 2 - 4 * (f.a : ℚ) * (f.c : ℚ) = (D : ℚ) := by
    exact_mod_cast hf
  have hdet : (γ 0 0 : ℚ) * (γ 1 1 : ℚ) - (γ 0 1 : ℚ) * (γ 1 0 : ℚ) = 1 := by
    exact Matrix.SpecialLinearGroup.intCast_fin_two_mul_sub_mul_eq_one γ
  ext <;> simp [idealChangeFactor, smul_b]
  · field_simp [haQ]
    nlinarith [congrArg (fun z : ℚ ↦ (γ 0 0 : ℚ) * (γ 1 0 : ℚ) * z) hd]
  · field_simp [haQ]
    nlinarith [congrArg (fun z : ℚ ↦ (f.a : ℚ) * z) hdet]

/-- The scaling factor has norm equal to the ratio of leading coefficients, including a zero
original leading coefficient, when both sides vanish. -/
@[simp] theorem norm_idealChangeFactor (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (γ : SL(2, ℤ)) :
    QuadraticAlgebra.norm (f.idealChangeFactor D γ) = ((γ • f).a : ℚ) / (f.a : ℚ) := by
  by_cases ha : f.a = 0
  · simp [idealChangeFactor, ha]
  have haQ : (f.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hnorm : QuadraticAlgebra.norm
      (γ 1 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + γ 1 0 • f.idealGenerator D) =
        (f.a : ℚ) * ((γ • f).a : ℚ) := by
    rw [norm_idealGenerators f D hf]
    simp only [eval_def, smul_a, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_neg]
    ring
  rw [idealChangeFactor]
  calc
    _ = ((f.a : ℚ)⁻¹) ^ 2 * QuadraticAlgebra.norm
        (star (γ 1 1 • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) +
          γ 1 0 • f.idealGenerator D)) := by
      simp only [QuadraticAlgebra.norm_def, re_smul, im_smul, smul_eq_mul]
      ring
    _ = _ := by
      rw [QuadraticAlgebra.norm_star, hnorm]
      field_simp [haQ]

/-- The change factor has positive norm exactly when the old and new leading coefficients
have positive product. -/
theorem norm_idealChangeFactor_pos_iff (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) (γ : SL(2, ℤ)) :
    0 < QuadraticAlgebra.norm (f.idealChangeFactor D γ) ↔ 0 < f.a * (γ • f).a := by
  rw [norm_idealChangeFactor f D hf γ, ← Int.cast_pos (R := ℚ), Int.cast_mul,
    div_pos_iff, mul_pos_iff]
  exact or_congr and_comm and_comm

/-- The change factor is nonzero when the original leading coefficient is nonzero,
for every quadratic parameter. -/
theorem idealChangeFactor_ne_zero (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (ha : f.a ≠ 0) (γ : SL(2, ℤ)) :
    f.idealChangeFactor D γ ≠ 0 := by
  unfold idealChangeFactor
  apply smul_ne_zero (inv_ne_zero (by exact_mod_cast ha))
  apply star_ne_zero.mpr
  intro hz
  obtain ⟨hs, hr⟩ := (LinearIndependent.pair_iff.mp
    (linearIndependent_idealGenerators f D ha)) (γ 1 1) (γ 1 0) hz
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  simp [hs, hr] at hdet

/-- Properly equivalent forms have fractional ideals differing by the explicit principal factor. -/
theorem fractionalIdeal_smul (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hf : f.discrim = D) [Fact (¬ IsSquare D)] (γ : SL(2, ℤ)) :
    (γ • f).fractionalIdeal D ((discrim_smul γ f).trans hf) =
      FractionalIdeal.spanSingleton _ (f.idealChangeFactor D γ) * f.fractionalIdeal D hf := by
  have hfa : f.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)
  have h₀ := idealChangeFactor_mul_first f D hf hfa γ
  have h₁ := idealChangeFactor_mul_second f D hf hfa γ
  apply le_antisymm
  · intro z hz
    obtain ⟨m, n, rfl⟩ := (mem_fractionalIdeal_iff _ _ _ _).mp hz
    apply FractionalIdeal.mem_singleton_mul.mpr
    refine ⟨(m * γ 1 1 + n * γ 0 1) • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) +
      (m * γ 1 0 + n * γ 0 0) • f.idealGenerator D, ?_, ?_⟩
    · exact (mem_fractionalIdeal_iff f D hf _).mpr ⟨_, _, rfl⟩
    · simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul]
      linear_combination -(m : QuadraticAlgebra ℚ (D : ℚ) 0) * h₀ -
        (n : QuadraticAlgebra ℚ (D : ℚ) 0) * h₁
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
    obtain ⟨m, n, rfl⟩ := (mem_fractionalIdeal_iff f D hf y).mp hy
    have hdet : (γ 0 0 : QuadraticAlgebra ℚ (D : ℚ) 0) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      exact Matrix.SpecialLinearGroup.intCast_fin_two_mul_sub_mul_eq_one γ
    apply (mem_fractionalIdeal_iff _ _ _ _).mpr
    refine ⟨γ 0 0 * m - γ 0 1 * n, -(γ 1 0 * m) + γ 1 1 * n, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg]
    linear_combination -((γ 0 0 : QuadraticAlgebra ℚ (D : ℚ) 0) * m - γ 0 1 * n) * h₀ -
      (-(γ 1 0 * m) + γ 1 1 * n : QuadraticAlgebra ℚ (D : ℚ) 0) * h₁ +
      f.idealChangeFactor D γ * ((m : QuadraticAlgebra ℚ (D : ℚ) 0) * f.a +
        (n : QuadraticAlgebra ℚ (D : ℚ) 0) * f.idealGenerator D) * hdet

/-- The native invertible form ideals differ by the explicit proper-change principal factor. -/
theorem invertibleFractionalIdeal_smul (f : BinaryQuadraticForm ℤ) (D : ℤ)
    [Fact (¬ IsSquare D)] (hf : f.discrim = D) (hprim : f.IsPrimitive)
    (γ : SL(2, ℤ)) :
    (γ • f).invertibleFractionalIdeal D ((discrim_smul γ f).trans hf)
      ((isPrimitive_smul_iff f γ).mpr hprim) =
      toPrincipalIdeal _ _
        (Units.mk0 (f.idealChangeFactor D γ) (idealChangeFactor_ne_zero f D
          (a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)) γ)) *
          f.invertibleFractionalIdeal D hf hprim := by
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, coe_invertibleFractionalIdeal,
    coe_invertibleFractionalIdeal]
  exact fractionalIdeal_smul f D hf γ

/-! ### The orientation of a pair of ideal elements -/

/-- The square-root coordinate of `u · star v`, for integral combinations `u = x a + y β` and
`v = z a + w β` of the generators `a, β = (-b + √D)/2`, is `-(x w - y z) a / 2`. -/
private theorem im_mul_star_idealGenerators (f : BinaryQuadraticForm ℤ) (D : ℤ) (x y z w : ℤ) :
    ((x • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + y • f.idealGenerator D) *
        star (z • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + w • f.idealGenerator D)).im =
      -((x * w - y * z : ℤ) : ℚ) * f.a / 2 := by
  simp only [zsmul_eq_mul, im_mul, re_mul, re_add, im_add, re_star, im_star, re_intCast,
    im_intCast, idealGenerator_re, idealGenerator_im, Int.cast_sub, Int.cast_mul]
  ring

/-- If `μ` sends the ideal generators of `f` to the integral combinations `x a' + y β'` and
`z a' + w β'` of the ideal generators of `g`, then `N(μ) a = (x w - y z) a'`. -/
private theorem norm_mul_a_eq (f g : BinaryQuadraticForm ℤ) (D : ℤ)
    (μ : QuadraticAlgebra ℚ (D : ℚ) 0) (x y z w : ℤ)
    (h₁ : μ * f.a = x • (g.a : QuadraticAlgebra ℚ (D : ℚ) 0) + y • g.idealGenerator D)
    (h₂ : μ * f.idealGenerator D =
      z • (g.a : QuadraticAlgebra ℚ (D : ℚ) 0) + w • g.idealGenerator D) :
    QuadraticAlgebra.norm μ * f.a = ((x * w - y * z : ℤ) : ℚ) * g.a := by
  -- Multiplying both entries of `u · star v` by `μ` multiplies it by `μ · star μ = N(μ)`.
  have h : ((μ * f.a) * star (μ * f.idealGenerator D)).im =
      QuadraticAlgebra.norm μ * ((f.a : QuadraticAlgebra ℚ (D : ℚ) 0) *
        star (f.idealGenerator D)).im := by
    rw [← smul_eq_mul (QuadraticAlgebra.norm μ), ← im_smul, Algebra.smul_def,
      algebraMap_norm_eq_mul_star, star_mul]
    congr 1
    ring
  have hf := im_mul_star_idealGenerators f D 1 0 0 1
  have hg := im_mul_star_idealGenerators g D x y z w
  simp only [one_smul, zero_smul, add_zero, zero_add] at hf
  rw [h₁, h₂, hg, hf] at h
  push_cast at h ⊢
  linarith

/-- If `μ` carries the ideal basis `a, β` of `f` to the ideal basis of `g` by a matrix of
determinant `1`, then `g` is the corresponding proper transform of `f`. -/
private theorem exists_smul_eq_of_mul_eq {D : ℤ} {f g : BinaryQuadraticForm ℤ}
    (hfD : f.discrim = D) (hgD : g.discrim = D) (hfa : f.a ≠ 0) (hga : g.a ≠ 0)
    (μ : QuadraticAlgebra ℚ (D : ℚ) 0) {x y z w : ℤ} (hdet : x * w - y * z = 1)
    (ha : (g.a : QuadraticAlgebra ℚ (D : ℚ) 0) =
      μ * (x • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + y • f.idealGenerator D))
    (hβ : g.idealGenerator D =
      μ * (z • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + w • f.idealGenerator D)) :
    ∃ γ : SL(2, ℤ), γ • f = g := by
  let γ : SL(2, ℤ) := ⟨!![w, z; y, x], by rw [Matrix.det_fin_two_of]; linarith⟩
  refine ⟨γ, (eq_of_idealGenerator_mul_a_eq hgD ((discrim_smul γ f).trans hfD) hga ?_).symm⟩
  have hfirst := idealChangeFactor_mul_first f D hfD hfa γ
  have hsecond := idealChangeFactor_mul_second f D hfD hfa γ
  simp only [γ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hfirst hsecond
  rw [← hfirst, ← hsecond, ha, hβ]
  simp only [zsmul_eq_mul]
  ring

/-- Positive-leading forms with homothetic ideals are properly equivalent when the
scaling factor has positive norm. This applies to either sign of nonsquare discriminant. -/
theorem exists_smul_eq_of_fractionalIdeal_eq_of_norm_pos
    (f g : BinaryQuadraticForm ℤ) (D : ℤ) [Fact (¬ IsSquare D)]
    (hfD : f.discrim = D) (hgD : g.discrim = D) (hfa : 0 < f.a) (hga : 0 < g.a)
    (μ : QuadraticAlgebra ℚ (D : ℚ) 0) (hμ : 0 < Algebra.norm ℚ μ)
    (hI : g.fractionalIdeal D hgD = spanSingleton _ μ * f.fractionalIdeal D hfD) :
    ∃ γ : SL(2, ℤ), γ • f = g := by
  have hμ₀ : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  -- `μ` maps the generators of `I_f` into `I_g`, with integral coefficients `x, y, z, w`.
  have hfg : ∀ u ∈ f.fractionalIdeal D hfD, μ * u ∈ g.fractionalIdeal D hgD := fun u hu ↦ by
    rw [hI]
    exact FractionalIdeal.mem_singleton_mul.mpr ⟨u, hu, rfl⟩
  obtain ⟨x, y, hxy⟩ := (mem_fractionalIdeal_iff g D hgD _).mp
    (hfg _ (a_mem_fractionalIdeal f D hfD))
  obtain ⟨z, w, hzw⟩ := (mem_fractionalIdeal_iff g D hgD _).mp
    (hfg _ (idealGenerator_mem_fractionalIdeal f D hfD))
  -- The generators of `I_g` are `μ` times elements of `I_f`, with coefficients `x', y', z', w'`.
  obtain ⟨u, hu, hua⟩ := FractionalIdeal.mem_singleton_mul.mp
    (hI ▸ a_mem_fractionalIdeal g D hgD)
  obtain ⟨v, hv, hvβ⟩ := FractionalIdeal.mem_singleton_mul.mp
    (hI ▸ idealGenerator_mem_fractionalIdeal g D hgD)
  obtain ⟨x', y', rfl⟩ := (mem_fractionalIdeal_iff f D hfD u).mp hu
  obtain ⟨z', w', rfl⟩ := (mem_fractionalIdeal_iff f D hfD v).mp hv
  refine exists_smul_eq_of_mul_eq hfD hgD hfa.ne' hga.ne' μ ?_ hua hvβ
  -- Both changes of basis scale the leading coefficients by a norm and a determinant.
  have h₁ := norm_mul_a_eq f g D μ x y z w hxy.symm hzw.symm
  have h₂ := norm_mul_a_eq g f D μ⁻¹ x' y' z' w'
    (by rw [hua, ← mul_assoc, inv_mul_cancel₀ hμ₀, one_mul])
    (by rw [hvβ, ← mul_assoc, inv_mul_cancel₀ hμ₀, one_mul])
  have hNinv : QuadraticAlgebra.norm μ * QuadraticAlgebra.norm μ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hμ₀, map_one]
  have hfaQ : (0 : ℚ) < f.a := by exact_mod_cast hfa
  have hgaQ : (0 : ℚ) < g.a := by exact_mod_cast hga
  -- The determinants multiply to `1`.
  have hprod : (x' * w' - y' * z') * (x * w - y * z) = 1 := by
    have hprodQ : ((x' * w' - y' * z' : ℤ) : ℚ) * ((x * w - y * z : ℤ) : ℚ) = 1 := by
      refine mul_right_cancel₀ (mul_pos hfaQ hgaQ).ne' ?_
      linear_combination -(congrArg₂ (· * ·) h₁ h₂) + (f.a : ℚ) * g.a * hNinv
    exact_mod_cast hprodQ
  -- Positive norm fixes the sign of the unimodular change of basis.
  refine Int.eq_one_of_mul_eq_one_right ?_ hprod
  have hN : 0 ≤ QuadraticAlgebra.norm μ⁻¹ := by
    rw [← Algebra.norm_quadraticAlgebra_apply, Algebra.norm_inv]
    exact (inv_pos.mpr hμ).le
  have hdet : (0 : ℚ) ≤ ((x' * w' - y' * z' : ℤ) : ℚ) :=
    nonneg_of_mul_nonneg_left (h₂ ▸ mul_nonneg hN hgaQ.le) hfaQ
  exact_mod_cast hdet

end TauCeti.BinaryQuadraticForm
