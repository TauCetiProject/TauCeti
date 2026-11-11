/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination

/-!
# Splitting from the degrees of irreducible factors, and evaluating split polynomials

A polynomial over a field splits as soon as each of its irreducible factors has degree at most
one. This is the converse of Mathlib's `Polynomial.Splits.natDegree_le_one_of_irreducible`, read
through divisibility; it is the form in which splitting is detected when only the irreducible
factors of a polynomial are under control, as in Kummer's theorem on the places above a place of
a function field.

## Main results

* `Polynomial.Splits.of_forall_irreducible_dvd_natDegree_le_one`: a polynomial whose irreducible
  factors all have degree at most one splits.
* `Polynomial.Splits.eval₂_eq_prod_roots`: evaluated along any ring homomorphism, a split
  polynomial is its leading coefficient times the product of the linear factors over its roots.
* `Polynomial.Splits.eq_prod_roots_of_coeff_zero_eq_one`: a split polynomial with constant
  coefficient `1` is the product of the factors `1 - α⁻¹ X` over its roots `α`.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- **A polynomial whose irreducible factors are linear splits.** -/
theorem Splits.of_forall_irreducible_dvd_natDegree_le_one {f : K[X]}
    (h : ∀ g : K[X], Irreducible g → g ∣ f → g.natDegree ≤ 1) : f.Splits := by
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact Splits.zero
  | unit u hu =>
    obtain ⟨c, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
    exact Splits.C c
  | mul a i _ hi ih =>
    exact (Splits.of_natDegree_le_one (h i hi (dvd_mul_right i a))).mul
      (ih fun g hg hga ↦ h g hg (hga.mul_left i))

/-- **Evaluating a split polynomial along a ring homomorphism**: the value at `x` is the image of
the leading coefficient times the product of `x - φ a` over the roots `a`. This is
`Polynomial.Splits.eval_eq_prod_roots` with the evaluation taking place in another ring. -/
theorem Splits.eval₂_eq_prod_roots {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    {f : R[X]} (hf : f.Splits) (φ : R →+* S) (x : S) :
    f.eval₂ φ x = φ f.leadingCoeff * (f.roots.map fun a ↦ x - φ a).prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval₂_multiset_prod]

/-- **A split polynomial with constant coefficient `1`** is the product of the factors
`1 - α⁻¹ X` over its roots `α`, counted with multiplicity. This is the normalisation of
`Polynomial.Splits.eq_prod_roots` at `0` rather than at the leading coefficient. -/
theorem Splits.eq_prod_roots_of_coeff_zero_eq_one {f : K[X]} (hf : f.Splits)
    (h0 : f.coeff 0 = 1) : f = (f.roots.map fun α ↦ 1 - C α⁻¹ * X).prod := by
  have hne : ∀ α ∈ f.roots, α ≠ 0 := by
    rintro α hα rfl
    have h := (mem_roots'.mp hα).2
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, h0] at h
    exact one_ne_zero h
  -- `1 - α⁻¹ X = (-α⁻¹) (X - α)`, and evaluating `f` at `0` determines the leading coefficient.
  have hfac : (f.roots.map fun α ↦ 1 - C α⁻¹ * X) =
      f.roots.map fun α ↦ C (-α)⁻¹ * (X - C α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      have h : C α⁻¹ * C α = 1 := by
        rw [← C_mul]
        simp [hne α hα]
      rw [inv_neg, C_neg]
      linear_combination -h
  have hlc : f.leadingCoeff = (f.roots.map fun α ↦ (-α)⁻¹).prod := by
    have h := hf.eval_eq_prod_roots 0
    rw [← coeff_zero_eq_eval_zero, h0] at h
    simp only [zero_sub] at h
    rw [Multiset.prod_map_inv]
    exact eq_inv_of_mul_eq_one_left h.symm
  rw [hfac, Multiset.prod_map_mul, Multiset.prod_hom' _ C, ← hlc]
  exact hf.eq_prod_roots

end Polynomial
