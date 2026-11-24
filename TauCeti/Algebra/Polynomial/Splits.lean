/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Prime

/-!
# Splitting from the degrees of irreducible factors, and evaluating split polynomials

A polynomial over a field splits as soon as each of its irreducible factors has degree at most
one. This is the converse of Mathlib's `Polynomial.Splits.natDegree_le_one_of_irreducible`, read
through divisibility; it is the form in which splitting is detected when only the irreducible
factors of a polynomial are under control, as in Kummer's theorem on the places above a place of
a function field.

Divisors over a domain of a mapped split polynomial descend up to a unit constant when the
mapped leading coefficient is a unit. This classifies units after polynomial localization
and scalar extension.

## Main results

* `Polynomial.Splits.of_forall_irreducible_dvd_natDegree_le_one`: a polynomial whose irreducible
  factors all have degree at most one splits.
* `Polynomial.Splits.eval₂_eq_prod_roots`: evaluated along any ring homomorphism, a split
  polynomial is its leading coefficient times the product of the linear factors over its roots.
* `Polynomial.Splits.eq_C_mul_prod_roots_of_coeff_zero_ne_zero`: a split polynomial with nonzero
  constant coefficient is that coefficient times the product of the factors `1 - α⁻¹ X` over its
  roots `α`.
* `Polynomial.Splits.eq_prod_roots_of_coeff_zero_eq_one`: the case of constant coefficient `1`,
  where the polynomial is the product of the factors `1 - α⁻¹ X` alone.
* `Polynomial.Splits.exists_eq_C_mul_map_of_dvd_map`: descent up to a unit constant of divisors
  of mapped split polynomials whose mapped leading coefficient is a unit.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- **A polynomial whose irreducible factors are linear splits.** -/
theorem Splits.of_forall_irreducible_dvd_natDegree_le_one {f : K[X]}
    (h : ∀ g : K[X], Irreducible g → g ∣ f → g.natDegree ≤ 1) : f.Splits := by
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact .zero
  | unit u hu => exact hu.splits
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

/-- **A split polynomial with nonzero constant coefficient** is that coefficient times the product
of the factors `1 - α⁻¹ X` over its roots `α`, counted with multiplicity. This is the
normalisation of `Polynomial.Splits.eq_prod_roots` at `0` rather than at the leading
coefficient. -/
theorem Splits.eq_C_mul_prod_roots_of_coeff_zero_ne_zero {f : K[X]} (hf : f.Splits)
    (h0 : f.coeff 0 ≠ 0) : f = C (f.coeff 0) * (f.roots.map fun α ↦ 1 - C α⁻¹ * X).prod := by
  have hne : ∀ α ∈ f.roots, α ≠ 0 := by
    rintro α hα rfl
    simp_all [coeff_zero_eq_eval_zero]
  have hlc : f.coeff 0 = f.leadingCoeff * (f.roots.map (-·)).prod := by
    simpa [coeff_zero_eq_eval_zero] using hf.eval_eq_prod_roots 0
  -- `1 - α⁻¹ X = (-α)⁻¹ (X - α)`, and the value of `f` at `0` absorbs the factors `(-α)⁻¹`.
  have hfac : (f.roots.map fun α ↦ 1 - C α⁻¹ * X) =
      f.roots.map fun α ↦ C (-α)⁻¹ * (X - C α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      simp [mul_sub, ← C_mul, hne α hα, inv_neg, neg_add_eq_sub]
  rw [hfac, Multiset.prod_map_mul, Multiset.prod_hom' _ C, Multiset.prod_map_inv, ← mul_assoc,
    ← C_mul, hlc, mul_inv_cancel_right₀ (right_ne_zero_of_mul (hlc ▸ h0))]
  exact hf.eq_prod_roots

/-- **A split polynomial with constant coefficient `1`** is the product of the factors
`1 - α⁻¹ X` over its roots `α`, counted with multiplicity. -/
theorem Splits.eq_prod_roots_of_coeff_zero_eq_one {f : K[X]} (hf : f.Splits)
    (h0 : f.coeff 0 = 1) : f = (f.roots.map fun α ↦ 1 - C α⁻¹ * X).prod := by
  simpa [h0] using hf.eq_C_mul_prod_roots_of_coeff_zero_ne_zero (by simp [h0])

end Polynomial

open Polynomial

/-- A divisor of a split polynomial mapped to a domain descends up to a unit constant when
its mapped leading coefficient is a unit. -/
theorem Polynomial.Splits.exists_eq_C_mul_map_of_dvd_map
    {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    {i : R →+* A} {f : R[X]} (hsplit : f.Splits) (hu : IsUnit (i f.leadingCoeff))
    {p : A[X]} (hp : p ∣ f.map i) :
    ∃ u : Aˣ, ∃ factor : R[X], factor ∣ f ∧ p = C (u : A) * factor.map i := by
  classical
  obtain ⟨roots, hroots⟩ := splits_iff_exists_multiset.mp hsplit
  let l := roots.toList
  have hlist : (List.ofFn fun j : Fin l.length ↦ X - C (l.get j)) =
      l.map (fun x ↦ X - C x) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map fun x : R ↦ X - C x) (List.ofFn_get l)
  have hf : f = C f.leadingCoeff * ∏ j : Fin l.length, (X - C (l.get j)) := by
    rw [← List.prod_ofFn, hlist]
    simpa [l, ← Multiset.prod_coe, ← Multiset.map_coe] using hroots
  have hmap : f.map i = C (i f.leadingCoeff) *
      ∏ j : Fin l.length, (X - C (i (l.get j))) := by
    conv_lhs => rw [hf]
    simp only [Polynomial.map_mul, map_C, Polynomial.map_prod, Polynomial.map_sub, map_X]
  obtain ⟨q, hq⟩ := hp
  obtain ⟨t, u, b, c, _, _, hbc, hp, _⟩ :=
    mul_eq_mul_prime_prod (s := Finset.univ)
      (p := fun j : Fin l.length ↦ X - C (i (l.get j)))
      (fun j _ ↦ prime_X_sub_C _) (by simpa [hmap] using hq.symm)
  have hb : IsUnit b := isUnit_of_dvd_unit ⟨c, hbc⟩ (hu.map C)
  obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.mp hb
  refine ⟨ha.unit, ∏ j ∈ t, (X - C (l.get j)), ?_, ?_⟩
  · rw [hf]
    exact (Finset.prod_dvd_prod_of_subset t Finset.univ _ (Finset.subset_univ t)).mul_left _
  · simpa only [Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, IsUnit.unit_spec] using hp
