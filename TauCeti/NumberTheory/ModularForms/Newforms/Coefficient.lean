/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
public import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-!
# The Fourier coefficients of a good Hecke eigenform, and of a newform

For an `EigenformAwayFromLevel` the coefficients are the eigenvalues *scaled by* `a₁`, and only
for a normalised `Newform`, where `a₁ = 1`, are they the eigenvalues themselves.

`Newforms/RingEigenvalue.lean` reads the eigenvalue system `λ` of an `EigenformAwayFromLevel` off
the multiplication table of the `Γ₀(N)` Hecke ring, touching no Fourier coefficient. This file
supplies the missing half: the composite Hecke element reads the coefficient at `m n` from the
coefficient at `m`, for `m` coprime to `n`
(`HeckeSlash/Nebentypus/Composite.lean`), so at `m = 1` the eigenvector equation becomes

`a_n(f) = λ_n · a_1(f)`   for every good index `n`,

and for a normalised newform, where `a_1 = 1`, simply `a_n(f) = λ_n`. That is the form in which
strong multiplicity one is classically stated — Miyake's Theorem 4.6.12 compares the `a_n`, not
the `λ_n` — and the identity that turns the eigenvalue identities of `RingEigenvalue.lean`
(`eigenvalue_mul`, `eigenvalue_prime_pow_add_two`) into the Fourier-coefficient conditions of
Diamond–Shurman's Proposition 5.8.5.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue_mul_coeff_one`:
  `a_n(f) = λ_n a_1(f)` at a good index.
* `HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue`: `a_n(f) = λ_n` for a newform, and with
  it the two classical coefficient identities of a normalised eigenform at the good indices,
  `HeckeRing.GL2.Newform.qExpansion_coeff_mul` and
  `HeckeRing.GL2.Newform.qExpansion_coeff_prime_pow_add_two`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean` —
`eigenvalue_eq_fourierCoeff_one` (`λ_n = a_n` for a normalised eigenform) and
`eigenform_coeff_multiplicative_one` (the divisor-sum form of the coefficient identities). The
source states them for its `IsNormalisedEigenform_one` predicate and derives them from the
divisor-sum coefficient formula; here they are statements about `EigenformAwayFromLevel` and
`Newform`, read off the eigenvector equation through the coprime-index formula of
`HeckeSlash/Nebentypus/Composite.lean` and the eigenvalue identities of
`Newforms/RingEigenvalue.lean`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace EigenformAwayFromLevel

variable (f : EigenformAwayFromLevel N k)

/-- **The coefficients of a good Hecke eigenform are its eigenvalues, scaled by `a₁`**:
`a_n(f) = λ_n a_1(f)` at every index `n` coprime to the level. The eigenvector equation at `n`,
read on the first coefficient: the Hecke element multiplies `a_1` by `λ_n` and reads `a_n`. -/
theorem qExpansion_coeff_eq_eigenvalue_mul_coeff_one (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff (n : ℕ) =
      f.eigenvalue n hn * (qExpansion 1 f.toCuspForm).coeff 1 := by
  have h := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime
    (N := N) (k := k) (χ := f.χ)
    n.pos.ne' hn ⟨f.toCuspForm, f.mem_charSpace⟩ (m := 1) (Nat.coprime_one_left _)
  rw [f.isEigen n hn, one_mul, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul] at h
  exact h.symm

end EigenformAwayFromLevel

namespace Newform

variable (f : Newform N k)

/-- **The `q`-expansion coefficients of a newform are its eigenvalues**: `a_n(f) = λ_n` at every
index `n` coprime to the level, the normalisation `a_1 = 1` pinning the scalar. -/
theorem qExpansion_coeff_eq_eigenvalue (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = f.eigenvalue n hn := by
  rw [f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue_mul_coeff_one n hn, f.isNorm,
    mul_one]

/-- **Multiplicativity of the coefficients at coprime good indices**: `a_{mn} = a_m a_n`
(Diamond–Shurman Proposition 5.8.5 (3)), the image of `eigenvalue_mul`. -/
theorem qExpansion_coeff_mul {m n : ℕ+} (hmn : Nat.Coprime (m : ℕ) (n : ℕ))
    (hm : Nat.Coprime (m : ℕ) N) (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff ((m : ℕ) * (n : ℕ)) =
      (qExpansion 1 f.toCuspForm).coeff (m : ℕ) * (qExpansion 1 f.toCuspForm).coeff (n : ℕ) := by
  rw [← PNat.mul_coe, f.qExpansion_coeff_eq_eigenvalue (m * n)
      (PNat.mul_coe m n ▸ Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩),
    f.qExpansion_coeff_eq_eigenvalue m hm, f.qExpansion_coeff_eq_eigenvalue n hn,
    f.toEigenformAwayFromLevel.eigenvalue_mul hmn hm hn]

/-- **The recurrence along the powers of a good prime**:
`a_{p^{r+2}} = a_p a_{p^{r+1}} − χ(p) p^{k−1} a_{p^r}` (Diamond–Shurman
Proposition 5.8.5 (2)), the image of `eigenvalue_prime_pow_add_two`. -/
theorem qExpansion_coeff_prime_pow_add_two {p : ℕ+} (hp : (p : ℕ).Prime)
    (hpN : Nat.Coprime (p : ℕ) N) (r : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff ((p : ℕ) ^ (r + 2)) =
      (qExpansion 1 f.toCuspForm).coeff (p : ℕ) *
          (qExpansion 1 f.toCuspForm).coeff ((p : ℕ) ^ (r + 1)) -
        (f.χ (ZMod.unitOfCoprime (p : ℕ) hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 f.toCuspForm).coeff ((p : ℕ) ^ r) := by
  have hc (v : ℕ) : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N := PNat.pow_coe p v ▸ hpN.pow_left v
  rw [← PNat.pow_coe p (r + 2), ← PNat.pow_coe p (r + 1), ← PNat.pow_coe p r,
    f.qExpansion_coeff_eq_eigenvalue (p ^ (r + 2)) (hc (r + 2)),
    f.qExpansion_coeff_eq_eigenvalue (p ^ (r + 1)) (hc (r + 1)),
    f.qExpansion_coeff_eq_eigenvalue (p ^ r) (hc r), f.qExpansion_coeff_eq_eigenvalue p hpN,
    f.toEigenformAwayFromLevel.eigenvalue_prime_pow_add_two hp hpN r]

end Newform

end HeckeRing.GL2
