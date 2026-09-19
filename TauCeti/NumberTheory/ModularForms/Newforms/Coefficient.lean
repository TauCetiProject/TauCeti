/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ArithmeticFunction.PrimeRecurrence
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Eigenvector
import TauCeti.NumberTheory.ModularForms.Newforms.EigenFromPrimes
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
public import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-!
# The Fourier coefficients of a good Hecke eigenform, and of a newform

For an `EigenformAwayFromLevel` the coefficients are the eigenvalues *scaled by* `a₁`; when
`a₁ = 1` they are the eigenvalues themselves, as for a `Newform` (via `Newform.isNorm`).

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

Conversely, the coefficient recurrence at every good prime characterises the existence of an
`EigenformAwayFromLevel` with a prescribed underlying cusp form. In particular, nonvanishing,
coprime multiplicativity, and the prime-power recurrence imply the good-prime recurrence and
hence produce a bundled good Hecke eigenform. This is the away-from-the-level part of the
coefficient characterisation in Diamond–Shurman, Proposition 5.8.5.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue_mul_coeff_one`:
  `a_n(f) = λ_n a_1(f)` at a good index.
* `exists_toCuspForm_eq_and_χ_eq_iff_ne_zero_and_forall_prime_qExpansion_coeff_prime_mul`:
  a nonzero cusp form of nebentypus `χ` underlies a good Hecke eigenform exactly when its
  coefficients satisfy a scalar Hecke recurrence at every good prime.
* `exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two`:
  nonvanishing, coprime multiplicativity, and the prime-power recurrences produce a good Hecke
  eigenform.
* `HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue`: `a_n(f) = λ_n` for a
  normalised good eigenform (e.g. a newform, via `Newform.isNorm`), and with it the two classical
  coefficient identities at the good indices,
  `HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_mul` and
  `HeckeRing.GL2.EigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two`.
* `HeckeRing.GL2.Eigenform.qExpansion_coeff_mul_qExpansion_coeff_eq_sum_divisors_gcd`: the
  Hecke relation among the coefficients of a normalised full eigenform, with its multiplicative
  and prime-power specialisations at every index and every prime.

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
`Newforms/RingEigenvalue.lean`. The full-eigenform relation is read directly from Tau Ceti's
divisor-sum formula
`qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0`.

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
    n.pos.ne' ⟨f.toCuspForm, f.mem_charSpace⟩ (m := 1) (Nat.coprime_one_left _)
  rw [f.isEigen n hn, one_mul, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
    smul_eq_mul] at h
  exact h.symm

/-- **The coefficients of a normalised good eigenform are its eigenvalues**: `a_n(f) = λ_n` at
every index `n` coprime to the level, when `a_1(f) = 1`. For a `Newform` the normalisation is
`Newform.isNorm`. -/
theorem qExpansion_coeff_eq_eigenvalue (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (n : ℕ+)
    (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff (n : ℕ) = f.eigenvalue n hn := by
  rw [f.qExpansion_coeff_eq_eigenvalue_mul_coeff_one n hn, h₁, mul_one]

/-- **Multiplicativity of the coefficients of a normalised good eigenform, at good indices**:
`a_{mn} = a_m a_n` when `m` and `n` are coprime to each other and to the level
(Diamond–Shurman Proposition 5.8.5 (3)). This is the image of `eigenvalue_mul`; newness is not
used. -/
theorem qExpansion_coeff_mul (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {m n : ℕ+}
    (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) (hm : Nat.Coprime (m : ℕ) N)
    (hn : Nat.Coprime (n : ℕ) N) :
    (qExpansion 1 f.toCuspForm).coeff ((m : ℕ) * (n : ℕ)) =
      (qExpansion 1 f.toCuspForm).coeff (m : ℕ) *
        (qExpansion 1 f.toCuspForm).coeff (n : ℕ) := by
  rw [← PNat.mul_coe, f.qExpansion_coeff_eq_eigenvalue h₁ (m * n)
      (PNat.mul_coe m n ▸ Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩),
    f.qExpansion_coeff_eq_eigenvalue h₁ m hm, f.qExpansion_coeff_eq_eigenvalue h₁ n hn,
    f.eigenvalue_mul hmn hm hn]

/-- **The prime-power recurrence for a normalised good eigenform, at a good prime**:
`a_{p^{r+2}} = a_p a_{p^{r+1}} - χ(p) p^{k-1} a_{p^r}` (Diamond–Shurman
Proposition 5.8.5 (2)). This is the image of `eigenvalue_prime_pow_add_two`; newness is not
used. -/
theorem qExpansion_coeff_prime_pow_add_two (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1)
    {p : ℕ+} (hp : (p : ℕ).Prime) (hpN : Nat.Coprime (p : ℕ) N) (r : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff ((p : ℕ) ^ (r + 2)) =
      (qExpansion 1 f.toCuspForm).coeff (p : ℕ) *
          (qExpansion 1 f.toCuspForm).coeff ((p : ℕ) ^ (r + 1)) -
        (f.χ (ZMod.unitOfCoprime (p : ℕ) hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 f.toCuspForm).coeff ((p : ℕ) ^ r) := by
  have hc (v : ℕ) : Nat.Coprime ((p ^ v : ℕ+) : ℕ) N := PNat.pow_coe p v ▸ hpN.pow_left v
  rw [← PNat.pow_coe p (r + 2), ← PNat.pow_coe p (r + 1), ← PNat.pow_coe p r,
    f.qExpansion_coeff_eq_eigenvalue h₁ (p ^ (r + 2)) (hc (r + 2)),
    f.qExpansion_coeff_eq_eigenvalue h₁ (p ^ (r + 1)) (hc (r + 1)),
    f.qExpansion_coeff_eq_eigenvalue h₁ (p ^ r) (hc r),
    f.qExpansion_coeff_eq_eigenvalue h₁ p hpN, f.eigenvalue_prime_pow_add_two hp hpN r]

/-- **The coefficient recurrence characterises bundled eigen-ness away from the level.** A cusp
form `f ∈ S_k(N, χ)` underlies an `EigenformAwayFromLevel` exactly when it is nonzero and, at
every prime `p ∤ N`, its coefficients satisfy
`a_{pm} = c_p a_m - χ(p) p^{k-1} a_{m/p}` for some scalar `c_p` and every `m`.

The scalar is not required to be named as `a_p` here: that identification needs the separate
normalisation `a₁ = 1`. -/
theorem exists_toCuspForm_eq_and_χ_eq_iff_ne_zero_and_forall_prime_qExpansion_coeff_prime_mul
    {f : CuspForm
    ((Gamma1 N).map (mapGL ℝ)) k} {χ : (ZMod N)ˣ →* ℂˣ} (hχ : f ∈ cuspFormCharSpace k χ) :
    (∃ F : EigenformAwayFromLevel N k, F.toCuspForm = f ∧ F.χ = χ) ↔
      f ≠ 0 ∧ ∀ (p : ℕ) (_hp : p.Prime) (hpN : Nat.Coprime p N), ∃ c : ℂ, ∀ m : ℕ,
        (qExpansion 1 f).coeff (p * m) = c * (qExpansion 1 f).coeff m -
          if p ∣ m then (χ (ZMod.unitOfCoprime p hpN) : ℂ) *
            (p : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m / p) else 0 := by
  constructor
  · rintro ⟨F, rfl, rfl⟩
    refine ⟨F.ne_zero, fun p hp hpN ↦ ⟨F.eigenvalue ⟨p, hp.pos⟩ hpN, fun m ↦ ?_⟩⟩
    exact qExpansion_coeff_prime_mul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul
      hp hpN (F.isEigen ⟨p, hp.pos⟩ hpN) m
  · rintro ⟨hf, hrec⟩
    refine ⟨ofForallPrime hχ hf (fun p hp hpN ↦ ?_), ofForallPrime_toCuspForm _ _ _,
      ofForallPrime_χ _ _ _⟩
    obtain ⟨c, hc⟩ := hrec p hp hpN
    refine ⟨c, ?_⟩
    rw [heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp]
    apply Subtype.ext
    exact (heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul hp hpN hχ c).2 hc

/-- **Diamond–Shurman's coefficient relations produce a good Hecke eigenform.** Let
`f ∈ S_k(N, χ)` be nonzero. If its coefficients are multiplicative at coprime indices and
satisfy the Hecke recurrence along the powers of every good prime, then `f` underlies an
`EigenformAwayFromLevel`. (Diamond–Shurman state this for normalised `f`, `a₁ = 1`, which
implies `f ≠ 0`.)

Multiplicativity is needed at all coprime indices, rather than only indices prime to `N`: to prove
the `T_p` eigen-relation at a good prime, its coefficient recurrence must also hold at indices
containing prime factors of the level. -/
theorem exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two
    {f : CuspForm
    ((Gamma1 N).map (mapGL ℝ)) k} {χ : (ZMod N)ˣ →* ℂˣ} (hχ : f ∈ cuspFormCharSpace k χ)
    (hf : f ≠ 0)
    (hmul : ∀ u v : ℕ, Nat.Coprime u v →
      (qExpansion 1 f).coeff (u * v) =
        (qExpansion 1 f).coeff u * (qExpansion 1 f).coeff v)
    (hpow : ∀ (p : ℕ) (_hp : p.Prime) (hpN : Nat.Coprime p N) (r : ℕ),
      (qExpansion 1 f).coeff (p ^ (r + 2)) =
        (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p ^ (r + 1)) -
          (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
            (qExpansion 1 f).coeff (p ^ r)) :
    ∃ F : EigenformAwayFromLevel N k, F.toCuspForm = f ∧ F.χ = χ := by
  rw [exists_toCuspForm_eq_and_χ_eq_iff_ne_zero_and_forall_prime_qExpansion_coeff_prime_mul hχ]
  refine ⟨hf, fun p hp hpN ↦ ⟨(qExpansion 1 f).coeff p, fun m ↦ ?_⟩⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [mul_zero]
    simp [CuspFormClass.qExpansion_coeff_zero f one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  · exact TauCeti.prime_mul_eq_of_prime_pow_recurrence_of_coprime_mul_eq
      (a := fun n ↦ (qExpansion 1 f).coeff n) (L := 1)
      (d := (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) hp
      (Nat.coprime_one_right p) (fun u v huv _ _ ↦ hmul u v huv) (hpow p hp hpN) m hm
      (Nat.coprime_one_right m)

end EigenformAwayFromLevel

namespace Eigenform

variable (f : Eigenform N k)

/-- **The Hecke relation among the coefficients of a normalised full eigenform.** If `a₁(f) = 1`,
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
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  -- The eigenvector equation `T_n f = λ_n f`, read on the `m`-th coefficient.
  -- (`f.isEigen` indexes by `ℕ+`; at `⟨n, _⟩` its Hecke element is `T_n` by definition.)
  have hT : (qExpansion 1 (heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N n)
      ⟨f.toCuspForm, f.mem_charSpace⟩ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
        f.eigenvalue ⟨n, hn'⟩ * (qExpansion 1 f.toCuspForm).coeff m := by
    have heigen : heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N n)
        ⟨f.toCuspForm, f.mem_charSpace⟩ = f.eigenvalue ⟨n, hn'⟩ • ⟨f.toCuspForm, f.mem_charSpace⟩ :=
      f.isEigen ⟨n, hn'⟩
    rw [heigen]
    simp only [SetLike.mk_smul_mk, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_smul,
      smul_eq_mul]
  have han := f.qExpansion_coeff_eq_eigenvalue_mul_coeff_one ⟨n, hn'⟩
  rw [h₁, mul_one, PNat.mk_coe] at han
  rw [han, mul_comm, ← hT]
  exact qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 hn _ m

/-- **The coefficients of a normalised full eigenform are multiplicative**: `a_{mn} = a_m a_n`
whenever `m` and `n` are coprime, with no condition relating them to the level (Diamond–Shurman
Proposition 5.8.5 (3)). -/
theorem qExpansion_coeff_mul (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {m n : ℕ}
    (hmn : m.Coprime n) :
    (qExpansion 1 f.toCuspForm).coeff (m * n) =
      (qExpansion 1 f.toCuspForm).coeff m * (qExpansion 1 f.toCuspForm).coeff n := by
  rw [f.qExpansion_coeff_mul_qExpansion_coeff_eq_sum_divisors_gcd h₁, Nat.Coprime.gcd_eq_one hmn,
    Nat.divisors_one, Finset.sum_singleton]
  simp

/-- **The prime-power recurrence of a normalised full eigenform, at every prime**:
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

end Eigenform

end HeckeRing.GL2
