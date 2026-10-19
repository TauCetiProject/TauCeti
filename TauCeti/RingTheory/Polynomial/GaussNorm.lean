/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# Gauss norms of primitive and split polynomials

At a nonarchimedean absolute value `v`, the Gauss norm `Polynomial.gaussNorm v c` is
multiplicative (`Polynomial.gaussNorm_mul`). This file evaluates it on the polynomials that occur
when a primitive integer polynomial is factored into linear factors.

Let `φ : A →+* R` satisfy `v (φ a) ≤ 1` for every `a : A`. A polynomial over `A` whose
coefficients generate the unit ideal has Gauss norm of radius one equal to `1` after mapping along
`φ`: Bézout writes `1` as a combination of the coefficients, and the ultrametric inequality bounds
`v 1 = 1` by the largest coefficient.
Every nonarchimedean absolute value is at most `1` on the integers, so this applies to every
primitive `P ∈ ℤ[X]` and every nonarchimedean absolute value, in any characteristic. The finite
places of a number field are the main instance; over `ℤ` itself the Dedekind-domain form is
Mathlib's `Polynomial.isPrimitive_iff_forall_gaussNorm_eq_one`.

The Gauss norm of radius `c ≥ 0` of a linear factor `X - C b` is `max c (v b)`. Combining these
with multiplicativity: if a primitive `P ∈ ℤ[X]` splits as `a ∏_{b ∈ s} (X - b)`, with roots
counted with multiplicity, then `v a * ∏_{b ∈ s} max 1 (v b) = 1`. For the primitive minimal
polynomial of an algebraic number this is the finite-place factor in the identity between the
Mahler measure and the absolute Weil height; the leading coefficient must be kept, because the
monic rational minimal polynomial does not satisfy the identity.

## Main results

* `Polynomial.gaussNorm_eq_iSup`: the Gauss norm is the supremum over all weighted coefficients.
* `Polynomial.gaussNorm_map_eq_one_of_contentIdeal_eq_top`: a polynomial whose content ideal is
  the unit ideal has Gauss norm of radius one equal to `1` after mapping along `φ : A →+* R`, at a
  nonarchimedean absolute value `v` with `v (φ a) ≤ 1` for every `a : A`.
* `Polynomial.IsPrimitive.gaussNorm_map_eq_one`: a primitive integer polynomial has Gauss norm `1`
  at every nonarchimedean absolute value.
* `Polynomial.gaussNorm_X_sub_C`: the Gauss norm of `X - C b` is `max c (v b)`.
* `Polynomial.gaussNorm_multiset_prod`: the Gauss norm is multiplicative over finite products.
* `Polynomial.IsPrimitive.mul_multiset_prod_max_one_eq_one`: if a primitive integer polynomial
  factors as `C a * ∏_{b ∈ s} (X - C b)`, then `v a * ∏_{b ∈ s} max 1 (v b) = 1`.
* `Polynomial.IsPrimitive.leadingCoeff_mul_prod_roots_max_one_eq_one`: the same identity over a
  domain in which the mapped polynomial splits, stated with its leading coefficient and roots.

## References

* C. J. Smyth, *The Mahler measure of algebraic numbers: a survey*, §1.
* J. Wu, *Heights of algebraic numbers*, §3, Lemma 3.1.
-/

public section

namespace Polynomial

/-- A polynomial Gauss norm is the supremum over all weighted coefficients, including the
zero coefficients outside its support. -/
theorem gaussNorm_eq_iSup {R F : Type*} [Semiring R] [FunLike F R ℝ]
    [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (p : R[X]) (v : F) {c : ℝ}
    (hc : 0 ≤ c) : p.gaussNorm v c = ⨆ i : ℕ, v (p.coeff i) * c ^ i := by
  rw [← gaussNorm_coe_powerSeries v p hc, PowerSeries.gaussNorm_eq]
  simp only [coeff_coe]

section Semiring

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] [ZeroHomClass F R ℝ] (v : F) (c : ℝ)

/-- The Gauss norm of `X` is the value of the radius, scaled by `v 1`. -/
@[simp]
theorem gaussNorm_X : (X : R[X]).gaussNorm v c = v 1 * c := by
  rw [← monomial_one_one_eq_X, gaussNorm_monomial, pow_one]

end Semiring

section AbsoluteValueSemiring

variable {R : Type*} [Semiring R] [Nontrivial R] {v : AbsoluteValue R ℝ}

/-- Let `φ : A →+* R` and let `v` be a nonarchimedean absolute value on `R` with `v (φ a) ≤ 1` for
all `a`. If the coefficients of `p ∈ A[X]` generate the unit ideal, then the Gauss norm of radius
one of the image of `p` is `1`. -/
theorem gaussNorm_map_eq_one_of_contentIdeal_eq_top {A : Type*} [Semiring A]
    (hna : IsNonarchimedean v) (φ : A →+* R) (hφ : ∀ a, v (φ a) ≤ 1) {p : A[X]}
    (hp : p.contentIdeal = ⊤) :
    (p.map φ).gaussNorm v 1 = 1 := by
  have hg : 0 ≤ (p.map φ).gaussNorm v 1 := gaussNorm_nonneg v _ zero_le_one
  refine le_antisymm ?_ ?_
  · rw [gaussNorm_eq_iSup _ _ zero_le_one]
    exact ciSup_le fun i ↦ by simpa using hφ (p.coeff i)
  -- The elements `a` with `v (φ a)` at most the Gauss norm contain the coefficients and are
  -- closed under the ideal operations, so they contain `1`.
  have key : ∀ a ∈ p.contentIdeal, v (φ a) ≤ (p.map φ).gaussNorm v 1 := fun a ha ↦ by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hx
      simpa using le_gaussNorm v (p.map φ) zero_le_one n
    | zero => simpa using hg
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (hna _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, map_mul]
      simpa using mul_le_mul (hφ r) hx (v.nonneg _) zero_le_one
  simpa using key 1 (hp ▸ Submodule.mem_top)

end AbsoluteValueSemiring

section Ring

variable {R : Type*} [Ring R] [Nontrivial R] {v : AbsoluteValue R ℝ} {c : ℝ}

/-- At any absolute value, the Gauss norm of radius `c ≥ 0` of the linear polynomial
`X - C b` is `max c (v b)`. -/
@[simp]
theorem gaussNorm_X_sub_C (hc : 0 ≤ c) (b : R) :
    (X - C b).gaussNorm v c = max c (v b) := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c (X - C b)
    rw [hi]
    rcases i with _ | (_ | i) <;> simp [coeff_sub, coeff_X]
  · have h := le_gaussNorm v (X - C b) hc 1
    simp only [coeff_sub] at h
    simpa using h
  · have h := le_gaussNorm v (X - C b) hc 0
    simp only [coeff_sub] at h
    simpa using h

/-- **Gauss's lemma at a nonarchimedean absolute value.** A primitive polynomial with integer
coefficients has Gauss norm of radius one equal to `1` at every nonarchimedean absolute value,
in any characteristic. -/
theorem IsPrimitive.gaussNorm_map_eq_one (hna : IsNonarchimedean v) {p : ℤ[X]}
    (hp : p.IsPrimitive) :
    (p.map (Int.castRingHom R)).gaussNorm v 1 = 1 :=
  gaussNorm_map_eq_one_of_contentIdeal_eq_top hna _
    (fun _ ↦ IsNonarchimedean.apply_intCast_le_one (by simp) v.map_one v.map_neg hna)
    ((isPrimitive_iff_contentIdeal_eq_top p).mp hp)

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : AbsoluteValue R ℝ} {c : ℝ}

/-- At a nonarchimedean absolute value, the Gauss norm of nonnegative radius of a finite product is
the product of the Gauss norms. -/
theorem gaussNorm_multiset_prod [Nontrivial R] (hna : IsNonarchimedean v) (hc : 0 ≤ c)
    (s : Multiset R[X]) :
    s.prod.gaussNorm v c = (s.map (gaussNorm v c)).prod := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa [gaussNorm_zero_right, coeff_zero_multiset_prod, Multiset.map_map,
      Function.comp_def] using
      map_multiset_prod v.toMonoidHom (s.map fun p ↦ p.coeff 0)
  · have := gaussNorm_isAbsoluteValue hna hc
    exact map_multiset_prod (IsAbsoluteValue.abvHom (gaussNorm v c)) s

/-- If a primitive integer polynomial factors as `C a * ∏_{b ∈ s} (X - C b)` over `R`, roots
counted with multiplicity, then `v a * ∏_{b ∈ s} max 1 (v b) = 1` at every nonarchimedean
absolute value `v` on `R`. -/
theorem IsPrimitive.mul_multiset_prod_max_one_eq_one [Nontrivial R] (hna : IsNonarchimedean v)
    {p : ℤ[X]} (hp : p.IsPrimitive) {a : R} {s : Multiset R}
    (h : p.map (Int.castRingHom R) = C a * (s.map fun b ↦ X - C b).prod) :
    v a * (s.map fun b ↦ max 1 (v b)).prod = 1 := by
  simpa [h, gaussNorm_mul hna one_pos, gaussNorm_multiset_prod hna zero_le_one, Function.comp_def,
    gaussNorm_X_sub_C zero_le_one] using hp.gaussNorm_map_eq_one hna

/-- Let `P` be a primitive integer polynomial whose image in `R[X]` splits, with leading coefficient
`a` and roots `b` in the domain `R`, counted with multiplicity. Then `v a * ∏_b max 1 (v b) = 1` at
every nonarchimedean absolute value `v` on `R`. -/
theorem IsPrimitive.leadingCoeff_mul_prod_roots_max_one_eq_one [IsDomain R]
    (hna : IsNonarchimedean v) {p : ℤ[X]} (hp : p.IsPrimitive)
    (hs : (p.map (Int.castRingHom R)).Splits) :
    v (p.map (Int.castRingHom R)).leadingCoeff *
      ((p.map (Int.castRingHom R)).roots.map fun b ↦ max 1 (v b)).prod = 1 :=
  hp.mul_multiset_prod_max_one_eq_one hna hs.eq_prod_roots

end CommRing

end Polynomial
