/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.QuadraticOrder.Split
public import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.Algebra.QuadraticAlgebra.NormTrace
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The principal split proper class at discriminant one

The principal form is `xy`, the norm of the full integer product order. An integral
form of discriminant one has a primitive isotropic vector. Completing it to an oriented
basis, then using a unipotent change and possibly `S`, puts the form in this normal form.
Thus all such forms have one proper class under the existing left `SL(2, ℤ)` action.

The order and its norm are the existing split product order. The proof is elementary
and does not use a field ideal-class carrier.

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
theorem isPrimitive_splitPrincipalForm : splitPrincipalForm.IsPrimitive := by
  norm_num [splitPrincipalForm, isPrimitive_iff, content_def]

/-- The principal split form is the norm of the actual integer product algebra. -/
theorem eval_splitPrincipalForm_eq_norm (x y : ℤ) :
    splitPrincipalForm.eval x y = Algebra.norm ℤ ((x, y) : ℤ × ℤ) := by
  let e := TauCeti.QuadraticAlgebra.algEquivProdOfIdempotent (R := ℤ)
  have he : e (⟨y, x - y⟩ : QuadraticAlgebra ℤ 0 1) = (x, y) := by
    rw [QuadraticAlgebra.algEquivProdOfIdempotent_apply]
    ext <;> simp
  have h := Algebra.norm_eq_of_algEquiv e (⟨y, x - y⟩ : QuadraticAlgebra ℤ 0 1)
  rw [he] at h
  rw [eval_splitPrincipalForm, h, QuadraticAlgebra.algebraNorm_eq_norm]
  simp only [QuadraticAlgebra.norm_def]
  ring

/-- The form computes the norm on the canonical discriminant-one order through its
existing equivalence with the full integer product. -/
theorem eval_splitPrincipalForm_eq_order_norm
    (z : QuadraticOrder.toSubalgebra 1 (by decide)) :
    splitPrincipalForm.eval (QuadraticOrder.equivProdOfOne z).1
      (QuadraticOrder.equivProdOfOne z).2 = Algebra.norm ℤ z := by
  rw [eval_splitPrincipalForm_eq_norm]
  exact Algebra.norm_eq_of_algEquiv QuadraticOrder.equivProdOfOne z

private theorem exists_isCoprime_eval_eq_zero_of_discrim_eq_one
    (f : BinaryQuadraticForm ℤ) (hf : f.discrim = 1) :
    ∃ x y : ℤ, IsCoprime x y ∧ f.eval x y = 0 := by
  by_cases ha : f.a = 0
  · exact ⟨1, 0, isCoprime_one_left, by simpa using ha⟩
  have hval : f.eval (1 - f.b) (2 * f.a) = 0 := by
    have hdisc : f.b ^ 2 - 4 * f.a * f.c = 1 := hf
    rw [eval_def]
    linear_combination -f.a * hdisc
  have hgcd : 0 < Int.gcd (1 - f.b) (2 * f.a) := by
    apply Nat.pos_of_ne_zero
    intro h
    exact ha (by have := (Int.gcd_eq_zero_iff.mp h).2; omega)
  obtain ⟨g, x, y, hg, hxy, hx, hy⟩ := Int.exists_gcd_one' hgcd
  refine ⟨x, y, Int.isCoprime_iff_gcd_eq_one.mpr hxy, ?_⟩
  have hscale : f.eval (1 - f.b) (2 * f.a) = (g : ℤ) ^ 2 * f.eval x y := by
    rw [hx, hy]
    simp only [eval_def]
    ring
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  exact (mul_eq_zero.mp (hscale.symm.trans hval)).resolve_left (pow_ne_zero 2 hg0)

private theorem exists_smul_a_eq_zero_of_discrim_eq_one
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
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, by
    rw [← hγ, inv_smul_smul]⟩)

end TauCeti.BinaryQuadraticForm
