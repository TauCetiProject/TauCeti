/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
public import TauCeti.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform

/-!
# The Fourier coefficients and the Euler product of a normalized eigenform

Let `f ∈ S_k(N, χ)` be a full Hecke eigenform (`HeckeRing.GL2.Eigenform`: an eigenvector of
`T_n` at *every* positive index, the primes dividing the level included), normalized by
`a₁(f) = 1`. Its eigenvalues are then its Fourier coefficients, and the divisor-sum formula for
the coefficients of `T_n f` becomes a relation among the coefficients alone:

`a_m a_n = ∑_{d ∣ gcd(m, n)} χ(d) d^{k-1} a_{mn/d²}`,

with `χ` zero-extended to a Dirichlet character modulo `N` by `MulChar.ofUnitHom`. Its two
special cases are the coefficient conditions of Diamond–Shurman's Proposition 5.8.5, now at
every index and every prime:

* `a_{mn} = a_m a_n` for coprime `m`, `n`;
* `a_{p^{r+2}} = a_p a_{p^{r+1}} - χ(p) p^{k-1} a_{p^r}` for every prime `p`, which at a prime
  dividing the level reads `a_{p^{r+2}} = a_p a_{p^{r+1}}`, since `χ(p) = 0` there.

These are exactly the hypotheses of the degree-two Euler product
`TauCeti.LSeries_eulerProduct_hasProd_of_recurrence`, so on the half-plane `Re s > k/2 + 1`
where the coefficient series converges absolutely,

`L(s, f) = ∏_p (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹`.

## Main results

* `HeckeRing.GL2.Eigenform.qExpansion_coeff_mul_qExpansion_coeff_eq_sum_divisors_gcd`: the
  Hecke relation among the coefficients of a normalized eigenform.
* `HeckeRing.GL2.Eigenform.qExpansion_coeff_mul`: the coefficients are multiplicative.
* `HeckeRing.GL2.Eigenform.qExpansion_coeff_prime_pow_add_two`: the prime-power recurrence at
  every prime.
* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`: the Euler product.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5 and Theorem 5.9.2.

## Provenance

The AINTLIB `LeanModularForms` project (<https://github.com/CBirkbeck/AINTLIB>, Apache-2.0) has
an Euler product for its newforms (`lSeries_eulerProduct`, `Modularforms/LFunctionEuler.lean`).
The statements and proofs here are not ported from it: they are read off Tau Ceti's full
eigenform API and the divisor-sum formula `HeckeSlash/Nebentypus/CoefficientFormula.lean`.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup LSeries

open scoped MatrixGroups

namespace HeckeRing.GL2.Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Eigenform N k)

/-- **The Hecke relation among the coefficients of a normalized eigenform.** If `a₁(f) = 1`,
then for all `m` and `n`,

`a_m a_n = ∑_{d ∣ gcd(m, n)} χ(d) d^{k-1} a_{mn/d²}`,

where `χ(d)` is the zero extension `MulChar.ofUnitHom f.χ`, vanishing at every `d` sharing a
factor with the level. -/
theorem qExpansion_coeff_mul_qExpansion_coeff_eq_sum_divisors_gcd
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (m n : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff m * (qExpansion 1 f.toCuspForm).coeff n =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) d * (d : ℂ) ^ (k - 1) *
          (qExpansion 1 f.toCuspForm).coeff (m * n / d ^ 2) := by
  have hzero : (qExpansion 1 f.toCuspForm).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero _ one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hzero]
  have hcoeff := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 hn
    (⟨f.toCuspForm, f.mem_charSpace⟩ : cuspFormCharSpace k f.χ) m
  -- `f.isEigen` indexes by `ℕ+`; at `⟨n, _⟩` its Hecke element is `T_n` by definition.
  have heigen : heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N n)
      ⟨f.toCuspForm, f.mem_charSpace⟩ =
        f.eigenvalue ⟨n, Nat.pos_of_ne_zero hn⟩ • ⟨f.toCuspForm, f.mem_charSpace⟩ :=
    f.isEigen ⟨n, Nat.pos_of_ne_zero hn⟩
  have han := f.qExpansion_coeff_eq_eigenvalue_mul_coeff_one ⟨n, Nat.pos_of_ne_zero hn⟩
  rw [h₁, mul_one, PNat.mk_coe] at han
  rw [heigen, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, smul_eq_mul, ← han] at hcoeff
  rw [mul_comm, ← hcoeff]

/-- **The coefficients of a normalized eigenform are multiplicative**: `a_{mn} = a_m a_n`
whenever `m` and `n` are coprime, with no condition relating them to the level (Diamond–Shurman
Proposition 5.8.5 (3)). -/
theorem qExpansion_coeff_mul (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {m n : ℕ}
    (hmn : m.Coprime n) :
    (qExpansion 1 f.toCuspForm).coeff (m * n) =
      (qExpansion 1 f.toCuspForm).coeff m * (qExpansion 1 f.toCuspForm).coeff n := by
  rw [f.qExpansion_coeff_mul_qExpansion_coeff_eq_sum_divisors_gcd h₁, Nat.Coprime.gcd_eq_one hmn,
    Nat.divisors_one, Finset.sum_singleton]
  simp

/-- **The prime-power recurrence of a normalized eigenform, at every prime**:
`a_{p^{r+2}} = a_p a_{p^{r+1}} - χ(p) p^{k-1} a_{p^r}` (Diamond–Shurman Proposition 5.8.5 (2)).
At a prime dividing the level the zero-extended `χ(p)` vanishes and the recurrence says
`a_{p^{r+2}} = a_p a_{p^{r+1}}`. -/
theorem qExpansion_coeff_prime_pow_add_two (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1)
    {p : ℕ} (hp : p.Prime) (r : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff (p ^ (r + 2)) =
      (qExpansion 1 f.toCuspForm).coeff p * (qExpansion 1 f.toCuspForm).coeff (p ^ (r + 1)) -
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 f.toCuspForm).coeff (p ^ r) := by
  have hrel := f.qExpansion_coeff_mul_qExpansion_coeff_eq_sum_divisors_gcd h₁ (p ^ (r + 1)) p
  have hgcd : Nat.gcd (p ^ (r + 1)) p = p :=
    Nat.gcd_eq_right (dvd_pow_self p (Nat.succ_ne_zero r))
  have hpow : p ^ (r + 1) * p = p ^ (r + 2) := (pow_succ p (r + 1)).symm
  have hdiv : p ^ (r + 2) / p ^ 2 = p ^ r := by
    rw [Nat.pow_div (by omega) hp.pos, Nat.add_sub_cancel]
  rw [hgcd, hp.divisors, Finset.sum_pair (Ne.symm hp.one_lt.ne'), hpow, hdiv] at hrel
  simp only [Nat.cast_one, map_one, one_zpow, one_pow, Nat.div_one, one_mul] at hrel
  linear_combination -hrel

/-- **The Euler product of a normalized eigenform.** For `f ∈ S_k(N, χ)` a full Hecke eigenform
with `a₁(f) = 1`, and `Re s > k/2 + 1`,

`L(s, f) = ∏_p (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹`,

the product converging unconditionally over the primes. The character is zero-extended, so the
factor at a prime dividing the level is `(1 - a_p p^{-s})⁻¹`. -/
theorem LSeries_eulerProduct_hasProd (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) := by
  have hsum : LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    have habs := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le f.toCuspForm
    rw [strictWidthInfty_Gamma1] at habs
    exact habs.trans_lt (by exact_mod_cast hs)
  have hprod := TauCeti.LSeries_eulerProduct_hasProd_of_recurrence
    (d := fun p ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)) h₁
    (f.qExpansion_coeff_mul h₁) (fun p hp r ↦ f.qExpansion_coeff_prime_pow_add_two h₁ hp r) hsum
  -- Merge `p ^ (k - 1) * p ^ (-2 s)` into the single power `p ^ (k - 1 - 2 s)`.
  have hfactor (p : Nat.Primes) :
      (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s) = (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
    rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hp0]
    push_cast
    ring_nf
  simp_rw [mul_assoc, hfactor] at hprod
  simpa only [mul_assoc] using hprod

end HeckeRing.GL2.Eigenform
