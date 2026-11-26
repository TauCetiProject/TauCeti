/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The eta-quotient criterion

Let `N ≥ 1`, let `r δ ∈ ℤ` for the positive divisors `δ ∣ N`, and let
`f(τ) = ∏_{δ ∣ N} η(δ τ) ^ r δ` be the eta quotient `TauCeti.ModularForm.etaQuotient N r`. If

* `∑_δ r δ = 2 k` for an integer `k`,
* `∑_δ δ r δ ≡ 0 (mod 24)` and `∑_δ (N / δ) r δ ≡ 0 (mod 24)`,

then `f ∣[k] γ = χ(d) f` for every `γ = (a b; c d) ∈ Γ₀(N)`, where
`χ(d) = ((-1) ^ k ∏_δ δ ^ r δ / d) = (-1 / d) ^ k ∏_δ (δ / d) ^ r δ` is the Kronecker symbol
`TauCeti.kroneckerSym`. Hence `χ` is a character modulo `N`, and if moreover the order of `f` at
every cusp is nonnegative (positive), then `f` is a modular form (cusp form) of weight `k` on
`Γ₁(N)` with nebentypus `χ`. The orders at the cusps are computed in
`TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient`; they depend only on `gcd(N, c)` for a
cusp `a / c`, so it suffices to check them at the divisors of `N`.

For example, the criterion applies to `η(τ) η(23 τ)` (`N = 23`, `k = 1`, character `(-23 / ·)`)
and to `η(τ)² η(11 τ)²` (`N = 11`, `k = 2`, trivial character), whose orders at both cusps are
positive.

## Implementation notes

By `TauCeti.ModularForm.etaQuotient_slash`, `f ∣[k] γ = (∏_δ ε(γ_δ) ^ r δ) f`, where
`γ_δ = (a, δ b; c / δ, d)` is the conjugate `TauCeti.conjScaleGamma0` of `γ` by `diag(δ, 1)`.
For `c ≥ 0` each `ε(γ_δ)` is evaluated by its Kronecker form
(`TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker`): for odd `d` by the even-`c` form,
which holds for all `c ≥ 0` when `d` is odd; for even `d`, when `c`, `N` and every `δ` are odd, by
the odd-`c` form. The two congruences make the exponents of `e(x / 24)` sum to a multiple of `24`,
up to `6 k (d - 1)` for odd `d`, and multiplicativity and quadratic reciprocity collect the
symbols into `χ(d)`. For `c < 0` we pass to `-γ = (-1) γ`, using that the multiplier
`TauCeti.ModularForm.etaQuotientMultiplier` is a character of `Γ₀(N)`.

The character `etaQuotientChar` is built from the multiplier itself: evaluating
`TauCeti.ModularForm.etaQuotientMultiplier_mul` at matrices with bottom row `(N, d)`, and using
that the multiplier of `Tʲ` is `1` (`TauCeti.ModularForm.etaQuotientMultiplier_T_zpow`), shows
that `χ(d)` is periodic modulo `N` and multiplicative on integers prime to `N`.

## Main definitions

* `TauCeti.ModularForm.etaQuotientChar`: the character `d ↦ ((-1) ^ k ∏_δ δ ^ r δ / d)` modulo `N`.
* `TauCeti.ModularForm.etaQuotientModularForm`, `TauCeti.ModularForm.etaQuotientCuspForm`: the eta
  quotient as a modular form, respectively cusp form, on `Γ₁(N)`.

## Main results

* `TauCeti.ModularForm.etaQuotient_slash_eq_smul`: `f ∣[k] γ = χ(d) f` on `Γ₀(N)`.
* `TauCeti.ModularForm.etaQuotientChar_apply`: the values of the character.
* `TauCeti.ModularForm.etaQuotientModularForm_mem_modFormCharSpace`,
  `TauCeti.ModularForm.etaQuotientCuspForm_mem_cuspFormCharSpace`: `f ∈ M_k(N, χ)`, respectively
  `f ∈ S_k(N, χ)`.

## References

* K. Ono, *The Web of Modularity*, Theorem 1.64 (the criterion) and Theorem 1.65 (Ligozat's
  orders at the cusps).
* B. Gordon and K. Hughes, *Multiplicative properties of η-products II*, Contemp. Math. **143**
  (1993).
* M. Newman, *Construction and application of a class of modular functions II*, Proc. London
  Math. Soc. (3) **9** (1959).
* G. Ligozat, *Courbes modulaires de genre 1*, Bull. Soc. Math. France Mém. **43** (1975).
-/

public section

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup ModularGroup
open UpperHalfPlane (IsBoundedAtImInfty IsZeroAtImInfty)
open scoped Real ModularForm MatrixGroups UpperHalfPlane Manifold

namespace TauCeti.ModularForm

/-! ### The conjugates `γ_δ` -/

private theorem natCast_mul_natCast_div {N δ : ℕ} (hδ : δ ∈ N.divisors) :
    (δ : ℤ) * (N / δ : ℕ) = N := by
  exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hδ)

/-- The entries of `γ_δ = (a, δ b; (N / δ) t, d)` when `c = N t` and `δ ∣ N`. -/
private theorem conjScaleGamma0_apply_of_eq {N δ : ℕ} (hδ : δ ∈ N.divisors) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t) :
    conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 0 0 = γ 0 0 ∧
      conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 0 1 = γ 0 1 * δ ∧
      conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 1 0 = (N / δ : ℕ) * t ∧
      conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩ 1 1 = γ 1 1 := by
  have hc : γ 1 0 = δ * ((N / δ : ℕ) * t) := by
    rw [ht, ← mul_assoc, natCast_mul_natCast_div hδ]
  have hδ0 : (δ : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne'
  refine ⟨by simp, by simp [mul_comm], by simp [hc, Int.mul_ediv_cancel_left _ hδ0], by simp⟩

/-- The multiplier `∏_δ ε(γ_δ) ^ r δ`, from the values `F δ` of the eta multipliers at the
conjugates `γ_δ`. -/
private theorem etaQuotientMultiplier_eq_prod {N : ℕ} (r : ℕ → ℤ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {F : ℕ → ℂ} (hF : ∀ δ (hδ : δ ∈ N.divisors),
      etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) = F δ) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ = ∏ δ ∈ N.divisors, F δ ^ r δ := by
  rw [etaQuotientMultiplier_def, ← Finset.prod_attach N.divisors (fun δ ↦ F δ ^ r δ)]
  exact Finset.prod_congr rfl fun δ _ ↦ by rw [hF δ δ.property]

/-! ### The Kronecker-symbol value of the multiplier -/

/-- The value `((-1) ^ k ∏_δ δ ^ (r δ) / d) = (-1 / d) ^ k ∏_{δ ∣ N} (δ / d) ^ (r δ)`. -/
private noncomputable def symb (N : ℕ) (r : ℕ → ℤ) (k d : ℤ) : ℂ :=
  (kroneckerSym (-1) d : ℂ) ^ k * ∏ δ ∈ N.divisors, (kroneckerSym δ d : ℂ) ^ r δ

/-- The sum over `δ ∣ N` of `r δ` times the even-`c` exponent of `γ_δ = (a, b δ; (N / δ) t, d)`,
regrouped along the three sums of the congruence conditions. -/
private theorem sum_mul_evenExp (N : ℕ) (r : ℕ → ℤ) (a b d t : ℤ) :
    ∑ δ ∈ N.divisors, r δ * ((a + d) * ((N / δ : ℕ) * t) -
      b * δ * d * (((N / δ : ℕ) * t) ^ 2 - 1) + 3 * d - 3 - 3 * ((N / δ : ℕ) * t) * d) =
      (∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) * ((a + d) * t - b * d * N * t ^ 2 - 3 * t * d) +
        (∑ δ ∈ N.divisors, (δ : ℤ) * r δ) * (b * d) + (∑ δ ∈ N.divisors, r δ) * (3 * d - 3) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun δ hδ ↦ by
    linear_combination (-(r δ * b * d * (N / δ : ℕ) * t ^ 2)) * natCast_mul_natCast_div hδ

/-- The sum over `δ ∣ N` of `r δ` times the odd-`c` exponent of `γ_δ = (a, b δ; (N / δ) t, d)`,
regrouped along the two sums of the congruence conditions. -/
private theorem sum_mul_oddExp (N : ℕ) (r : ℕ → ℤ) (a b d t : ℤ) :
    ∑ δ ∈ N.divisors, r δ * ((a + d) * ((N / δ : ℕ) * t) -
      b * δ * d * (((N / δ : ℕ) * t) ^ 2 - 1) - 3 * ((N / δ : ℕ) * t)) =
      (∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) * ((a + d) * t - b * d * N * t ^ 2 - 3 * t) +
        (∑ δ ∈ N.divisors, (δ : ℤ) * r δ) * (b * d) := by
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun δ hδ ↦ by
    linear_combination (-(r δ * b * d * (N / δ : ℕ) * t ^ 2)) * natCast_mul_natCast_div hδ

/-- For `c = N t ≥ 0`: `∏_δ ((c / δ) / d) ^ r δ = ∏_δ (δ / d) ^ r δ`, as `∑_δ r δ` is even. -/
private theorem prod_kroneckerSym_div_left {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (γ : SL(2, ℤ)) {t : ℤ} (ht : γ 1 0 = N * t)
    (ht0 : 0 ≤ t) :
    ∏ δ ∈ N.divisors, (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) ^ r δ =
      ∏ δ ∈ N.divisors, (kroneckerSym δ (γ 1 1) : ℂ) ^ r δ := by
  have hcop := γ.isCoprime_row 1
  -- Each factor is `(c / d) ^ r δ (δ / d) ^ r δ`, and the factors `(c / d) ^ r δ` cancel.
  refine (Finset.prod_congr rfl fun δ hδ ↦ ?_).trans (Finset.prod_zpow_mul_eq_prod_of_sq_eq_one _
    (sq_intCast_kroneckerSym_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hcop)) (hk ▸ even_two_mul k) _)
  have hc : (N / δ : ℕ) * t * δ = γ 1 0 := by
    linear_combination t * natCast_mul_natCast_div hδ - ht
  have hx : 0 ≤ ((N / δ : ℕ) : ℤ) * t := mul_nonneg (Int.natCast_nonneg _) ht0
  have hδ0 : (0 : ℤ) < δ := by exact_mod_cast Nat.pos_of_mem_divisors hδ
  have hmul : kroneckerSym ((N / δ : ℕ) * t * δ) (γ 1 1) =
      kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) * kroneckerSym δ (γ 1 1) := by
    rcases eq_or_ne (γ 1 1) (-1) with hd | hd
    · rw [hd, kroneckerSym_neg_one_right, kroneckerSym_neg_one_right, kroneckerSym_neg_one_right,
        ite_eq_right (mul_nonneg hx hδ0.le).not_gt, ite_eq_right hx.not_gt,
        ite_eq_right hδ0.not_gt, one_mul]
    · exact kroneckerSym_mul_left_of_ne_neg_one hd _ _
  rw [← hc, hmul, Int.cast_mul, ← mul_zpow, mul_assoc, ← sq, sq_intCast_kroneckerSym_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_left (hc ▸ dvd_mul_left _ _))),
    mul_one]

/-- For `c = N t > 0`: `∏_δ (d / (c / δ)) ^ r δ = ∏_δ (d / δ) ^ r δ`, as `∑_δ r δ` is even. -/
private theorem prod_kroneckerSym_div_right {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (γ : SL(2, ℤ)) {t : ℤ} (ht : γ 1 0 = N * t)
    (ht0 : 0 < t) :
    ∏ δ ∈ N.divisors, (kroneckerSym (γ 1 1) ((N / δ : ℕ) * t) : ℂ) ^ r δ =
      ∏ δ ∈ N.divisors, (kroneckerSym (γ 1 1) δ : ℂ) ^ r δ := by
  have hcop := (γ.isCoprime_row 1).symm
  -- Each factor is `(d / c) ^ r δ (d / δ) ^ r δ`, and the factors `(d / c) ^ r δ` cancel.
  refine (Finset.prod_congr rfl fun δ hδ ↦ ?_).trans (Finset.prod_zpow_mul_eq_prod_of_sq_eq_one _
    (sq_intCast_kroneckerSym_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hcop)) (hk ▸ even_two_mul k) _)
  have hc : (N / δ : ℕ) * t * δ = γ 1 0 := by
    linear_combination t * natCast_mul_natCast_div hδ - ht
  have hm : (0 : ℤ) < (N / δ : ℕ) := by
    exact_mod_cast Nat.div_pos (Nat.divisor_le hδ) (Nat.pos_of_mem_divisors hδ)
  rw [← hc, kroneckerSym_mul_right _ (mul_pos hm ht0).ne'
    (by exact_mod_cast (Nat.pos_of_mem_divisors hδ).ne'), Int.cast_mul, ← mul_zpow, mul_assoc,
    ← sq, sq_intCast_kroneckerSym_eq_one
      (Int.isCoprime_iff_gcd_eq_one.mp (hcop.of_isCoprime_of_dvd_right (hc ▸ dvd_mul_left _ _))),
    mul_one]

/-- For odd `N`, quadratic reciprocity gives `((-1) ^ k ∏_δ δ ^ r δ / d) = ∏_δ (d / δ) ^ r δ`: the
signs `(-1 / d) ^ ((δ - 1) / 2)` multiply to `(-1 / d) ^ k` since `∑_δ δ r δ ≡ 0 (mod 4)`. -/
private theorem symb_eq_prod_of_odd {N : ℕ} {r : ℕ → ℤ} {k : ℤ} (hNo : Odd N)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) {A : ℤ} (hA : ∑ δ ∈ N.divisors, (δ : ℤ) * r δ = 24 * A)
    (d : ℤ) : symb N r k d = ∏ δ ∈ N.divisors, (kroneckerSym d δ : ℂ) ^ r δ := by
  have hsq : (kroneckerSym (-1) d : ℂ) ^ 2 = 1 := sq_intCast_kroneckerSym_eq_one (by simp)
  have hs0 : (kroneckerSym (-1) d : ℂ) ≠ 0 := fun h ↦ by simp [h] at hsq
  have hδo (δ : ℕ) (hδ : δ ∈ N.divisors) : Odd δ :=
    hNo.of_dvd_nat (Nat.dvd_of_mem_divisors hδ)
  have hsum : k + ∑ δ ∈ N.divisors, ((δ / 2 : ℕ) : ℤ) * r δ = 2 * (6 * A) := by
    have h : ∑ δ ∈ N.divisors, (δ : ℤ) * r δ =
        ∑ δ ∈ N.divisors, (2 * (((δ / 2 : ℕ) : ℤ) * r δ) + r δ) :=
      Finset.sum_congr rfl fun δ hδ ↦ by
        have h2 : (δ : ℤ) = 2 * ((δ / 2 : ℕ) : ℤ) + 1 := by
          exact_mod_cast (Nat.two_mul_div_two_add_one_of_odd (hδo δ hδ)).symm
        rw [h2]
        ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hk, hA] at h
    linarith
  have hR : ∏ δ ∈ N.divisors, (kroneckerSym δ d : ℂ) ^ r δ =
      (∏ δ ∈ N.divisors, (kroneckerSym d δ : ℂ) ^ r δ) *
        (kroneckerSym (-1) d : ℂ) ^ (∑ δ ∈ N.divisors, ((δ / 2 : ℕ) : ℤ) * r δ) := by
    rw [← Finset.prod_zpow_eq_zpow_sum_of_isUnit _ hs0.isUnit, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun δ hδ ↦ ?_
    have hrec : (kroneckerSym δ d : ℂ) =
        kroneckerSym d δ * (kroneckerSym (-1) d : ℂ) ^ (δ / 2) := by
      exact_mod_cast kroneckerSym_quadratic_reciprocity (hδo δ hδ) d
    rw [hrec, mul_zpow, ← zpow_natCast, ← zpow_mul]
  rw [symb, hR, mul_left_comm, ← zpow_add₀ hs0, hsum, zpow_mul, zpow_ofNat, hsq, one_zpow, mul_one]

/-- **The multiplier of an eta quotient, for `c ≥ 0` and odd `d`.** Each `ε(γ_δ)` is given by the
even-`c` Kronecker form; the exponents sum to `6 k (d - 1)` modulo `24`. -/
private theorem etaQuotientMultiplier_eq_symb_of_odd {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t) (ht0 : 0 ≤ t) (hdo : Odd (γ 1 1)) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ = symb N r k (γ 1 1) := by
  obtain ⟨A, hA⟩ := h24
  obtain ⟨B, hB⟩ := h24'
  obtain ⟨v, hv⟩ := hdo
  let E : ℕ → ℤ := fun δ ↦ (γ 0 0 + γ 1 1) * ((N / δ : ℕ) * t) -
    γ 0 1 * δ * γ 1 1 * (((N / δ : ℕ) * t) ^ 2 - 1) + 3 * γ 1 1 - 3 - 3 * ((N / δ : ℕ) * t) * γ 1 1
  have hε (δ : ℕ) (hδ : δ ∈ N.divisors) : etaMultiplier
      (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) =
      (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) * e24 (E δ) := by
    obtain ⟨h00, h01, h10, h11⟩ := conjScaleGamma0_apply_of_eq hδ hγ ht
    rw [etaMultiplier_eq_kroneckerSym_mul_of_c_nonneg_of_odd_d _
      (by rw [h10]; exact mul_nonneg (Int.natCast_nonneg _) ht0) (by rw [h11]; exact ⟨v, hv⟩),
      h00, h01, h10, h11, e24_def]
  -- The exponents sum to `k (12 v)` modulo `24`, and `e(12 v k / 24) = χ₄(d) ^ k = (-1 / d) ^ k`.
  have hsum : ∑ δ ∈ N.divisors, r δ * E δ ≡ k * (12 * v) [ZMOD 24] := by
    refine Int.modEq_iff_dvd.mpr ⟨-(B * ((γ 0 0 + γ 1 1) * t - γ 0 1 * γ 1 1 * N * t ^ 2 -
      3 * t * γ 1 1) + A * (γ 0 1 * γ 1 1)), ?_⟩
    rw [sum_mul_evenExp, hA, hB, hk, hv]
    ring
  rw [etaQuotientMultiplier_eq_prod r hγ hε, prod_mul_e24_zpow,
    e24_congr hsum, e24_mul, e24_twelve_mul_eq_χ₄, prod_kroneckerSym_div_left hk γ ht ht0, symb,
    kroneckerSym_neg_one_left_of_odd ⟨v, hv⟩, hv, mul_comm]

/-- **The multiplier of an eta quotient, for `c ≥ 0` and even `d`.** Then `c`, `N` and every
`δ ∣ N` are odd, each `ε(γ_δ)` is given by the odd-`c` Kronecker form, and the exponents sum to a
multiple of `24`. -/
private theorem etaQuotientMultiplier_eq_symb_of_even {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t) (ht0 : 0 ≤ t) (hde : Even (γ 1 1)) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ = symb N r k (γ 1 1) := by
  obtain ⟨A, hA⟩ := h24
  obtain ⟨B, hB⟩ := h24'
  have hco : Odd (γ 1 0) := Int.not_even_iff_odd.mp fun hce ↦ by
    have := (γ.isCoprime_row 1).isUnit_of_dvd' (even_iff_two_dvd.mp hce) (even_iff_two_dvd.mp hde)
    norm_num [Int.isUnit_iff] at this
  have hNt : Odd ((N : ℤ) * t) := ht ▸ hco
  have hto : Odd t := (Int.odd_mul.mp hNt).2
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 fun h ↦ Int.not_odd_zero (h ▸ hto)
  have hNo : Odd N := (Int.odd_natCast N).mp (Int.odd_mul.mp hNt).1
  let O : ℕ → ℤ := fun δ ↦ (γ 0 0 + γ 1 1) * ((N / δ : ℕ) * t) -
    γ 0 1 * δ * γ 1 1 * (((N / δ : ℕ) * t) ^ 2 - 1) - 3 * ((N / δ : ℕ) * t)
  have hε (δ : ℕ) (hδ : δ ∈ N.divisors) : etaMultiplier
      (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) =
      (kroneckerSym (γ 1 1) ((N / δ : ℕ) * t) : ℂ) * e24 (O δ) := by
    obtain ⟨h00, h01, h10, h11⟩ := conjScaleGamma0_apply_of_eq hδ hγ ht
    have hm : Odd (N / δ) := hNo.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hδ))
    rw [etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c _
      (by rw [h10]; exact mul_pos (by exact_mod_cast hm.pos) ht_pos)
      (by rw [h10]; exact Int.odd_mul.mpr ⟨(Int.odd_natCast _).mpr hm, hto⟩), h00, h01, h10, h11,
      e24_def]
  -- The exponents sum to a multiple of `24`.
  have hsum : ∑ δ ∈ N.divisors, r δ * O δ ≡ 0 [ZMOD 24] := by
    refine Int.modEq_zero_iff_dvd.mpr ⟨B * ((γ 0 0 + γ 1 1) * t - γ 0 1 * γ 1 1 * N * t ^ 2 -
      3 * t) + A * (γ 0 1 * γ 1 1), ?_⟩
    rw [sum_mul_oddExp, hA, hB]
    ring
  rw [etaQuotientMultiplier_eq_prod r hγ hε, prod_mul_e24_zpow,
    e24_congr hsum, e24_zero, mul_one, prod_kroneckerSym_div_right hk γ ht ht_pos,
    symb_eq_prod_of_odd hNo hk hA]

/-- **The multiplier of an eta quotient, for `c ≥ 0`.** If `c = N t` with `t ≥ 0`, then
`∏_δ ε(γ_δ) ^ r δ = (-1 / d) ^ k ∏_δ (δ / d) ^ r δ`. -/
private theorem etaQuotientMultiplier_eq_symb_of_nonneg {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t) (ht0 : 0 ≤ t) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ = symb N r k (γ 1 1) := by
  rcases Int.even_or_odd (γ 1 1) with hde | hdo
  · exact etaQuotientMultiplier_eq_symb_of_even hk h24 h24' hγ ht ht0 hde
  · exact etaQuotientMultiplier_eq_symb_of_odd hk h24 h24' hγ ht ht0 hdo

/-- `((-1) ^ k ∏_δ δ ^ r δ / -d) = (-1) ^ k ((-1) ^ k ∏_δ δ ^ r δ / d)` for `d ≠ 0`. -/
private theorem symb_neg (N : ℕ) (r : ℕ → ℤ) (k : ℤ) {d : ℤ} (hd : d ≠ 0) :
    symb N r k (-d) = (-1) ^ k * symb N r k d := by
  have h1 : kroneckerSym (-1) (-d) = -kroneckerSym (-1) d := by
    rw [neg_eq_neg_one_mul d, kroneckerSym_mul_right _ (by norm_num) hd]
    simp
  have h2 (δ : ℕ) : kroneckerSym δ (-d) = kroneckerSym δ d := by
    rw [neg_eq_neg_one_mul d, kroneckerSym_mul_right _ (by norm_num) hd]
    simp
  simp only [symb, h1, h2, Int.cast_neg]
  rw [neg_eq_neg_one_mul (kroneckerSym (-1) d : ℂ), mul_zpow]
  ring

/-- **The multiplier of an eta quotient on `Γ₀(N)`**:
`∏_δ ε(γ_δ) ^ r δ = (-1 / d) ^ k ∏_δ (δ / d) ^ r δ`. For `c < 0` we pass to `-γ = (-1) γ`, whose
multiplier is `(-i) ^ (2 k) = (-1) ^ k` times that of `γ`. -/
private theorem etaQuotientMultiplier_eq_symb {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ = symb N r k (γ 1 1) := by
  obtain ⟨t, ht⟩ := mem_Gamma0_iff_dvd.mp hγ
  rcases le_or_gt 0 t with ht0 | ht0
  · exact etaQuotientMultiplier_eq_symb_of_nonneg hk h24 h24' hγ ht ht0
  have hneg : (-γ) 1 0 = N * (-t) := by simp [ht]
  have hγ' : -γ ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr ⟨-t, hneg⟩
  have h := etaQuotientMultiplier_eq_symb_of_nonneg hk h24 h24' hγ' hneg (by omega)
  rw [show (⟨-γ, hγ'⟩ : Gamma0 N) = Gamma0.negOne N * ⟨γ, hγ⟩ from
      Subtype.ext (by simp [Gamma0.coe_negOne]),
    etaQuotientMultiplier_mul N r (by rw [hk]; exact even_two_mul k), etaQuotientMultiplier_negOne,
    hk, zpow_mul, show (-I) ^ (2 : ℤ) = (-1 : ℂ) by simp,
    show (-γ) 1 1 = -γ 1 1 by simp] at h
  have hsymb : (-1 : ℂ) ^ k * symb N r k (-γ 1 1) = symb N r k (γ 1 1) := by
    by_cases hd : γ 1 1 = 0
    · -- `d = 0` forces `c = -1`, so `N = 1` and `24 ∣ 2 k`: then `(-1) ^ k = 1`.
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have := γ.det_coe
        rwa [Matrix.det_fin_two] at this
      rw [hd] at hdet
      have hN : (N : ℤ) ∣ 1 := ⟨-(γ 0 1 * t), by linear_combination -hdet - γ 0 1 * ht⟩
      have hN1 : N = 1 := Nat.dvd_one.mp (by exact_mod_cast hN)
      subst hN1
      simp only [Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, one_mul] at hk h24
      obtain ⟨j, hj⟩ := h24
      rw [hd, neg_zero, Even.neg_one_zpow ⟨6 * j, by omega⟩, one_mul]
    · rw [symb_neg N r k hd, ← mul_assoc, ← mul_zpow, neg_one_mul, neg_neg, one_zpow, one_mul]
  rw [← hsymb, ← h, ← mul_assoc, ← mul_zpow, neg_one_mul, neg_neg, one_zpow, one_mul]

/-- **The transformation law of an eta quotient on `Γ₀(N)`** (Ono, Theorem 1.64). Let
`f = ∏_{δ ∣ N} η(δ τ) ^ r δ` with `∑_δ r δ = 2 k`, `∑_δ δ r δ ≡ 0` and `∑_δ (N / δ) r δ ≡ 0`
modulo `24`. Then for `γ = (a b; c d) ∈ Γ₀(N)`, `f ∣[k] γ = χ(d) f`, where
`χ(d) = ((-1) ^ k ∏_δ δ ^ r δ / d) = (-1 / d) ^ k ∏_δ (δ / d) ^ r δ` is the Kronecker symbol. -/
theorem etaQuotient_slash_eq_smul {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    (fun τ : ℍ ↦ etaQuotient N r τ) ∣[k] γ =
      ((kroneckerSym (-1) (γ 1 1) : ℂ) ^ k * ∏ δ ∈ N.divisors, (kroneckerSym δ (γ 1 1) : ℂ) ^ r δ)
        • fun τ : ℍ ↦ etaQuotient N r τ := by
  -- The scalar is `symb N r k (γ 1 1)` by definition.
  change _ = symb N r k (γ 1 1) • _
  rw [← etaQuotientMultiplier_eq_symb hk h24 h24' hγ]
  exact etaQuotient_slash N r hk ⟨γ, hγ⟩

/-! ### The character of an eta quotient -/

/-- The Kronecker-symbol value is periodic modulo `N` on integers prime to `N`: the multipliers
of `(a b; N d)` and `(a b; N d) Tʲ` are `χ(d)` and `χ(d + N j)`, and that of `Tʲ` is `1`. -/
private theorem symb_eq_of_intCast_eq {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {d d' : ℤ}
    (hd : IsCoprime d N) (h : (d : ZMod N) = d') : symb N r k d = symb N r k d' := by
  obtain ⟨γ, hc, hdγ⟩ := hd.symm.exists_SL2_row 1
  have hγ : γ ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by rw [hc])
  obtain ⟨j, hj⟩ := Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  have hT : T ^ j ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by simp [coe_T_zpow])
  have h11 : (γ * T ^ j) 1 1 = d' := by
    rw [Matrix.SpecialLinearGroup.coe_mul_T_zpow, hc, hdγ]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    linear_combination -hj
  have hTj : etaQuotientMultiplier N r ⟨T ^ j, hT⟩ = 1 := by
    obtain ⟨m, hm⟩ := h24
    have hm' : (∑ δ ∈ N.divisors, ((δ * r δ : ℤ) : ℂ)) = 24 * m := by exact_mod_cast hm
    rw [etaQuotientMultiplier_T_zpow, ← Complex.exp_int_mul_two_pi_mul_I (j * m)]
    push_cast at hm' ⊢
    rw [hm']
    ring_nf
  calc symb N r k d = etaQuotientMultiplier N r ⟨γ, hγ⟩ := by
        rw [etaQuotientMultiplier_eq_symb hk h24 h24' hγ, hdγ]
    _ = etaQuotientMultiplier N r (⟨γ, hγ⟩ * ⟨T ^ j, hT⟩) := by
        rw [etaQuotientMultiplier_mul N r (by rw [hk]; exact even_two_mul k), hTj, mul_one]
    _ = symb N r k ((γ * T ^ j) 1 1) :=
        etaQuotientMultiplier_eq_symb hk h24 h24' (Subgroup.mul_mem _ hγ hT)
    _ = symb N r k d' := by rw [h11]

/-- The Kronecker-symbol value is multiplicative on integers prime to `N`, since the multiplier
is. -/
private theorem symb_mul {N : ℕ} {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) {d₁ d₂ : ℤ}
    (h₁ : IsCoprime d₁ N) (h₂ : IsCoprime d₂ N) :
    symb N r k (d₁ * d₂) = symb N r k d₁ * symb N r k d₂ := by
  obtain ⟨γ₁, hc₁, hd₁⟩ := h₁.symm.exists_SL2_row 1
  obtain ⟨γ₂, hc₂, hd₂⟩ := h₂.symm.exists_SL2_row 1
  have hγ₁ : γ₁ ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by rw [hc₁])
  have hγ₂ : γ₂ ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by rw [hc₂])
  have h11 : (γ₁ * γ₂) 1 1 = N * γ₂ 0 1 + d₁ * d₂ := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc₁, hd₁, hd₂]
  calc symb N r k (d₁ * d₂) = symb N r k ((γ₁ * γ₂) 1 1) :=
        symb_eq_of_intCast_eq hk h24 h24' (h₁.mul_left h₂) (by simp [h11])
    _ = etaQuotientMultiplier N r (⟨γ₁, hγ₁⟩ * ⟨γ₂, hγ₂⟩) :=
        (etaQuotientMultiplier_eq_symb hk h24 h24' (Subgroup.mul_mem _ hγ₁ hγ₂)).symm
    _ = symb N r k d₁ * symb N r k d₂ := by
        rw [etaQuotientMultiplier_mul N r (by rw [hk]; exact even_two_mul k),
          etaQuotientMultiplier_eq_symb hk h24 h24' hγ₁,
          etaQuotientMultiplier_eq_symb hk h24 h24' hγ₂, hd₁, hd₂]

private theorem symb_ne_zero {N : ℕ} (r : ℕ → ℤ) (k : ℤ) {d : ℤ} (hd : IsCoprime d N) :
    symb N r k d ≠ 0 := by
  refine mul_ne_zero (zpow_ne_zero _ (Int.cast_ne_zero.mpr
    (kroneckerSym_eq_zero_iff.not.mpr (by simp)))) (Finset.prod_ne_zero_iff.mpr fun δ hδ ↦
      zpow_ne_zero _ (Int.cast_ne_zero.mpr (kroneckerSym_eq_zero_iff.not.mpr ?_)))
  rw [not_not, ← Int.isCoprime_iff_gcd_eq_one]
  exact (hd.symm.of_isCoprime_of_dvd_left
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors hδ)))

/-- **The character of an eta quotient**: the character `d ↦ ((-1) ^ k ∏_δ δ ^ r δ / d)` modulo
`N`, under the congruence conditions of `etaQuotient_slash_eq_smul`, which make the Kronecker
symbol periodic modulo `N` on integers prime to `N`. Its values are `etaQuotientChar_apply`. -/
noncomputable def etaQuotientChar (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) : (ZMod N)ˣ →* ℂˣ where
  toFun u := Units.mk0 (symb N r k ((u : ZMod N).val : ℕ))
    (symb_ne_zero r k (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u)))
  map_one' := Units.ext <| by
    rw [Units.val_mk0, symb_eq_of_intCast_eq hk h24 h24'
      (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime 1)) (d' := 1) (by simp)]
    simp [symb]
  map_mul' u v := Units.ext <| by
    simp only [Units.val_mul, Units.val_mk0]
    rw [← symb_mul hk h24 h24'
      (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u))
      (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime v))]
    exact symb_eq_of_intCast_eq hk h24 h24'
      (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime (u * v))) (by simp)

/-- The value of the character of an eta quotient at the class of an integer `d` prime to `N`:
`χ(d) = (-1 / d) ^ k ∏_δ (δ / d) ^ r δ`. -/
theorem etaQuotientChar_apply {N : ℕ} [NeZero N] {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) (u : (ZMod N)ˣ) {d : ℤ}
    (hd : (d : ZMod N) = u) :
    (etaQuotientChar N r k hk h24 h24' u : ℂ) =
      (kroneckerSym (-1) d : ℂ) ^ k * ∏ δ ∈ N.divisors, (kroneckerSym δ d : ℂ) ^ r δ :=
  symb_eq_of_intCast_eq hk h24 h24' (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u))
    (by simp [hd])

/-- **An eta quotient is `χ`-invariant on `Γ₀(N)`** for its character `χ = etaQuotientChar`. -/
theorem etaQuotient_mem_functionCharSpace {N : ℕ} [NeZero N] {r : ℕ → ℤ} {k : ℤ}
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) :
    (fun τ : ℍ ↦ etaQuotient N r τ) ∈ functionCharSpace k (etaQuotientChar N r k hk h24 h24') := by
  rw [mem_functionCharSpace_iff]
  intro g
  rw [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
    etaQuotient_slash_eq_smul hk h24 h24' g.property, etaQuotientChar_apply hk h24 h24' _
      (by rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply])]

/-! ### Eta quotients as modular forms -/

/-- **The eta-quotient criterion, modular forms** (Ono, Theorem 1.64). Under the congruence
conditions of `etaQuotient_slash_eq_smul`, an eta quotient whose order at every cusp is
nonnegative is a modular form of weight `k` on `Γ₁(N)`; it lies in `M_k(N, χ)` for its character
`χ = etaQuotientChar` (`etaQuotientModularForm_mem_modFormCharSpace`). Since the order at a cusp
`a / c` depends only on `gcd(N, c)` (`etaQuotientOrder_gcd`), the orders at the divisors of `N`
suffice. -/
noncomputable def etaQuotientModularForm (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ)
    (hord : ∀ d ∈ N.divisors, 0 ≤ etaQuotientOrder N r d) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun τ := etaQuotient N r τ
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    exact slash_mapGL_eq_self_of_mem_functionCharSpace_of_mem_Gamma1
      (etaQuotient_mem_functionCharSpace hk h24 h24') hA
  holo' := mdifferentiable_etaQuotient N r
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))]
    exact fun γ _ ↦ (isBoundedAtImInfty_etaQuotient_slash_iff N r hk γ).mpr
      ((forall_etaQuotientOrder_iff N r).mpr hord _)

/-- The underlying function of `etaQuotientModularForm` is the eta quotient. -/
@[simp]
theorem coe_etaQuotientModularForm (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ)
    (hord : ∀ d ∈ N.divisors, 0 ≤ etaQuotientOrder N r d) :
    ⇑(etaQuotientModularForm N r k hk h24 h24' hord) = fun τ : ℍ ↦ etaQuotient N r τ :=
  (rfl)

/-- The eta quotient lies in `M_k(N, χ)` for its character `χ = etaQuotientChar`. -/
theorem etaQuotientModularForm_mem_modFormCharSpace (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ)
    (hord : ∀ d ∈ N.divisors, 0 ≤ etaQuotientOrder N r d) :
    etaQuotientModularForm N r k hk h24 h24' hord ∈
      modFormCharSpace k (etaQuotientChar N r k hk h24 h24') :=
  (coe_mem_functionCharSpace_iff _ _ _).mp (etaQuotient_mem_functionCharSpace hk h24 h24')

/-- **The eta-quotient criterion, cusp forms** (Ono, Theorem 1.64). Under the congruence
conditions of `etaQuotient_slash_eq_smul`, an eta quotient whose order at every cusp is positive
is a cusp form of weight `k` on `Γ₁(N)`; it lies in `S_k(N, χ)` for its character
`χ = etaQuotientChar` (`etaQuotientCuspForm_mem_cuspFormCharSpace`). -/
noncomputable def etaQuotientCuspForm (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ)
    (hord : ∀ d ∈ N.divisors, 0 < etaQuotientOrder N r d) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun τ := etaQuotient N r τ
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    exact slash_mapGL_eq_self_of_mem_functionCharSpace_of_mem_Gamma1
      (etaQuotient_mem_functionCharSpace hk h24 h24') hA
  holo' := mdifferentiable_etaQuotient N r
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))]
    exact fun γ _ ↦ (isZeroAtImInfty_etaQuotient_slash_iff N r hk γ).mpr
      ((forall_etaQuotientOrder_iff N r).mpr hord _)

/-- The underlying function of `etaQuotientCuspForm` is the eta quotient. -/
@[simp]
theorem coe_etaQuotientCuspForm (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ)
    (hord : ∀ d ∈ N.divisors, 0 < etaQuotientOrder N r d) :
    ⇑(etaQuotientCuspForm N r k hk h24 h24' hord) = fun τ : ℍ ↦ etaQuotient N r τ :=
  (rfl)

/-- The eta quotient lies in `S_k(N, χ)` for its character `χ = etaQuotientChar`. -/
theorem etaQuotientCuspForm_mem_cuspFormCharSpace (N : ℕ) [NeZero N] (r : ℕ → ℤ) (k : ℤ)
    (hk : ∑ δ ∈ N.divisors, r δ = 2 * k) (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ)
    (hord : ∀ d ∈ N.divisors, 0 < etaQuotientOrder N r d) :
    etaQuotientCuspForm N r k hk h24 h24' hord ∈
      cuspFormCharSpace k (etaQuotientChar N r k hk h24 h24') :=
  (coe_mem_functionCharSpace_iff_mem_cuspFormCharSpace _ _ _).mp
    (etaQuotient_mem_functionCharSpace hk h24 h24')

end TauCeti.ModularForm
