/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.QuadraticOrder.Split
public import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.RingTheory.NormTrace.Prod
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The principal split proper class at discriminant one

The principal form is `xy`, the norm of the full integer product order. An integral
form of discriminant one has a primitive isotropic vector. Completing it to an oriented
basis, then using a unipotent change and possibly `S`, puts the form in this normal form.
Thus all such forms have one proper class under the existing left `SL(2, ℤ)` action.

The order and its norm are the existing split product order. The proof is elementary
and does not use a field ideal-class carrier.

## Main results

* `exists_isCoprime_eval_eq_zero_of_discrim_eq_one` gives a primitive isotropic vector.
* `exists_smul_a_eq_zero_of_discrim_eq_one` moves it to a zero leading coefficient by a
  proper change of variables.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (proper-equivalence conventions).
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- The principal form of the integer product order, `xy`. -/
def splitPrincipalForm : BinaryQuadraticForm ℤ := ⟨0, 1, 0⟩

/-- The principal split form has coefficients `(0, 1, 0)`. -/
theorem splitPrincipalForm_def : splitPrincipalForm = ⟨0, 1, 0⟩ := by
  rfl

/-- Evaluation of the principal split form is the product of the coordinates. -/
@[simp] theorem eval_splitPrincipalForm (x y : ℤ) : splitPrincipalForm.eval x y = x * y := by
  simp [splitPrincipalForm, eval_def]

/-- The principal split form has discriminant one. -/
@[simp] theorem discrim_splitPrincipalForm : splitPrincipalForm.discrim = 1 := by
  norm_num [splitPrincipalForm, discrim_def, discrim]

/-- The principal split form is primitive. -/
@[simp] theorem isPrimitive_splitPrincipalForm : splitPrincipalForm.IsPrimitive := by
  norm_num [splitPrincipalForm, isPrimitive_iff, content_def]

/-- The principal split form is the norm of the actual integer product algebra. -/
theorem eval_splitPrincipalForm_eq_norm (x y : ℤ) :
    splitPrincipalForm.eval x y = Algebra.norm ℤ ((x, y) : ℤ × ℤ) := by
  simp only [eval_splitPrincipalForm, TauCeti.Algebra.norm_prod, Algebra.norm_self,
    MonoidHom.id_apply]

/-- The form computes the norm on the canonical discriminant-one order through its
existing equivalence with the full integer product. -/
theorem eval_splitPrincipalForm_eq_order_norm
    (z : QuadraticOrder.toSubalgebra 1 (by decide)) :
    splitPrincipalForm.eval (QuadraticOrder.equivProdOfOne z).1
      (QuadraticOrder.equivProdOfOne z).2 = Algebra.norm ℤ z := by
  rw [eval_splitPrincipalForm_eq_norm]
  exact Algebra.norm_eq_of_algEquiv QuadraticOrder.equivProdOfOne z

/-- Every integral form of discriminant one has a primitive integral isotropic vector. -/
theorem exists_isCoprime_eval_eq_zero_of_discrim_eq_one
    (f : BinaryQuadraticForm ℤ) (hf : f.discrim = 1) :
    ∃ x y : ℤ, IsCoprime x y ∧ f.eval x y = 0 := by
  by_cases ha : f.a = 0
  · exact ⟨1, 0, isCoprime_one_left, by simpa using ha⟩
  have hval : f.eval (1 - f.b) (2 * f.a) = 0 := by
    have hdisc : f.b ^ 2 - 4 * f.a * f.c = 1 := by
      simpa only [discrim_def, _root_.discrim] using hf
    rw [eval_def]
    linear_combination -f.a * hdisc
  obtain ⟨x, y, hxy, _, _, hscale⟩ :=
    exists_isCoprime_eval_eq_gcd_sq_mul f (1 - f.b) (2 * f.a)
      (Or.inr (mul_ne_zero (by decide) ha))
  refine ⟨x, y, hxy, ?_⟩
  have hg0 : (Int.gcd (1 - f.b) (2 * f.a) : ℤ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (1 - f.b)
      (mul_ne_zero (by decide) ha)).ne'
  exact (mul_eq_zero.mp (hscale.symm.trans hval)).resolve_left (pow_ne_zero 2 hg0)

/-- Every integral form of discriminant one has a proper representative with zero leading
coefficient. -/
theorem exists_smul_a_eq_zero_of_discrim_eq_one
    (f : BinaryQuadraticForm ℤ) (hf : f.discrim = 1) :
    ∃ γ : SL(2, ℤ), (γ • f).a = 0 := by
  obtain ⟨x, y, hxy, hzero⟩ := exists_isCoprime_eval_eq_zero_of_discrim_eq_one f hf
  obtain ⟨γ, hγ⟩ := exists_smul_a_eq_eval f hxy
  exact ⟨γ, hγ.trans hzero⟩

/-- Every integral form of discriminant one is properly equivalent to the principal split form.
No primitivity assumption is needed. -/
theorem exists_smul_eq_splitPrincipalForm_of_discrim_eq_one
    (f : BinaryQuadraticForm ℤ) (hf : f.discrim = 1) :
    ∃ γ : SL(2, ℤ), γ • f = splitPrincipalForm := by
  obtain ⟨ρ, ha⟩ := exists_smul_a_eq_zero_of_discrim_eq_one f hf
  let g := ρ • f
  have hga : g.a = 0 := ha
  have hg : g.discrim = 1 := (discrim_smul ρ f).trans hf
  have hb2 : g.b ^ 2 = 1 := by simpa [discrim_def, discrim, hga] using hg
  have hb : g.b = 1 ∨ g.b = -1 := sq_eq_one_iff.mp hb2
  have hT : (ModularGroup.T ^ (g.b * g.c)) • g = ⟨0, g.b, 0⟩ := by
    ext <;> simp [smul_a, smul_b, smul_c, ModularGroup.coe_T_zpow, hga]
    linear_combination -g.c * hb2
  rcases hb with hb | hb
  · refine ⟨(ModularGroup.T ^ (g.b * g.c)) * ρ, ?_⟩
    rw [mul_smul, hT, hb, splitPrincipalForm_def]
  · refine ⟨ModularGroup.S * ((ModularGroup.T ^ (g.b * g.c)) * ρ), ?_⟩
    rw [mul_smul, mul_smul, hT, hb, splitPrincipalForm_def]
    ext <;> simp [smul_a, smul_b, smul_c, ModularGroup.coe_S]

/-- The existing proper-class quotient has only the principal class in discriminant one. -/
theorem properClass_eq_splitPrincipalForm_of_discrim_eq_one
    (f : BinaryQuadraticForm ℤ) (hf : f.discrim = 1) :
    (Quotient.mk'' f : MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ)) =
      Quotient.mk'' splitPrincipalForm := by
  obtain ⟨γ, hγ⟩ := exists_smul_eq_splitPrincipalForm_of_discrim_eq_one f hf
  rw [← hγ]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq.symm

end TauCeti.BinaryQuadraticForm
