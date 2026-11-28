/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.PrincipalGenus
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.NarrowClassGroup
import TauCeti.NumberTheory.FundamentalDiscriminant.SumTwoSquares
import TauCeti.NumberTheory.NumberField.Quadratic.Norm

/-!
# The class of the different in a real quadratic field

For a real quadratic field presented by `θ² = d` with squarefree `d`, let `J` be the narrow
class of `(θ)`, which is the class of the different. The genus character of a subset of the
prime-discriminant factors takes on `J` the sign of their product. The class `J` belongs to the
principal genus exactly when the field discriminant is a sum of two integer squares, or
equivalently when no prime congruent to `3` modulo `4` divides it.

The singleton character at `P` is evaluated using `x = 1 + 2θ`, of norm `1 - 4d`. This norm is
negative and coprime to the discriminant, so `(x)` is in the same narrow class as `(θ)`
and the character on it is `χ_P(-1) = sign P`. Multiplying the singleton values gives
the subset formula.

See Duke, Imamoglu and Toth, *Geometric invariants for real quadratic fields*, §§2, 4 and 7.
-/

public section

open NumberField Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-! ### Genus characters of principal classes -/

/-- **The genus character of a principal class is the character at the sign of the norm.** Let
`K = ℚ(√d)` with a prime-discriminant factorization `s` of its discriminant, and let `x` be a
nonzero algebraic integer whose norm `n` is coprime to `P ∈ s`. Then the genus character at `P` of
the narrow class of `(x)` is `χ_P(sign n)`: it is `1` when `n > 0` and `χ_P(-1)` when `n < 0`. -/
theorem genusCharFunNarrowClassGroupHom_mkPrincipal {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {P : ℤ} (hP : P ∈ s) {x : 𝓞 K} (hx : x ≠ 0)
    (hcop : IsCoprime (Algebra.norm ℤ x) P) :
    ((genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr hP)
        (NarrowClassGroup.mkPrincipal
          (Units.mk0 (x : K) (RingOfIntegers.coe_ne_zero_iff.mpr hx))) : ℤˣ) : ℤ) =
      primeDiscriminantCharFun P (Algebra.norm ℤ x).sign := by
  have hI : Ideal.span {x} ∈ (Ideal (𝓞 K))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  have habs : (Ideal.absNorm (Ideal.span {x}) : ℤ) = ((Algebra.norm ℤ x).natAbs : ℤ) := by
    rw [Ideal.absNorm_span_singleton]
  rw [NarrowClassGroup.mkPrincipal_coe_eq_mk0 hx (I := ⟨Ideal.span {x}, hI⟩) rfl,
    genusCharFunNarrowClassGroupHom_mk0_eq_primeDiscriminantCharFun_absNorm hs heven hprod hmin
      hgen hsf _ hI P hP (by rw [habs, Int.natCast_natAbs]; exact hcop.abs_left), habs,
    ← Int.sign_mul_self_eq_natAbs, primeDiscriminantCharFun_mul_right,
    primeDiscriminantCharFun_norm_eq_one hs heven hprod hmin hgen hsf hP x hcop, mul_one]

/-- **The genus characters of `[θ]⁺` are the signs of the prime discriminants.** For a real
quadratic field `K = ℚ(√d)`, `d > 0`, presented by `θ² = d`, the genus character at each prime
discriminant `P ∈ s` takes the value `sign P` on the narrow class of the principal ideal `(θ)`. -/
theorem genusCharFunNarrowClassGroupHom_mkPrincipal_gen {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) {P : ℤ} (hP : P ∈ s) :
    ((genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr hP)
        (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin))) : ℤˣ) : ℤ) =
      P.sign := by
  set x : 𝓞 K := 1 + 2 * θ with hxdef
  have hnorm : Algebra.norm ℤ x = 1 - 4 * d := by
    have h := TauCeti.NumberField.norm_int_add_mul_gen hmin hgen 2 1
    push_cast at h
    rw [hxdef, h]
    ring
  have hnormQ : Algebra.norm ℚ (x : K) = 1 - 4 * (d : ℚ) := by
    rw [← Algebra.coe_norm_int, hnorm]
    push_cast
    ring
  have hx : x ≠ 0 := by
    intro h0
    rw [h0] at hnormQ
    simp only [map_zero, Algebra.norm_zero] at hnormQ
    have h1 : (1 : ℤ) = 4 * d := by exact_mod_cast (by linarith : (1 : ℚ) = 4 * d)
    omega
  -- `P` divides `D`, which divides `4d`, and `1 - 4d` is coprime to `4d`.
  have hdvd : P ∣ 4 * d := by
    refine (Finset.dvd_prod_of_mem (fun P => P) hP).trans ?_
    rw [hprod]
    by_cases h4 : d % 4 = 1
    · rw [fundamentalDiscriminant_of_mod_four_eq_one h4]
      exact Dvd.intro_left 4 rfl
    · rw [fundamentalDiscriminant_of_mod_four_ne_one h4]
  have hcop : IsCoprime (Algebra.norm ℤ x) P := by
    rw [hnorm]
    exact IsCoprime.of_isCoprime_of_dvd_right ⟨1, 1, by ring⟩ hdvd
  have hclass : NarrowClassGroup.mkPrincipal
      (Units.mk0 (x : K) (RingOfIntegers.coe_ne_zero_iff.mpr hx)) =
      NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin)) := by
    refine mkPrincipal_eq_mkPrincipal_gen_of_norm_neg hmin hgen ?_
    have hd1 : (1 : ℚ) ≤ d := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
    rw [Units.val_mk0, hnormQ]
    linarith
  rw [← hclass,
    genusCharFunNarrowClassGroupHom_mkPrincipal hs heven hprod hmin hgen hsf hP hx hcop, hnorm,
    Int.sign_eq_neg_one_of_neg (by omega), primeDiscriminantCharFun_neg_one (hs P hP)]

/-- The genus character indexed by `t` takes on the narrow class of the quadratic generator
the sign of the product of the factors in `t`. -/
theorem genusCharFunNarrowClassGroupHom_mkPrincipal_gen_eq_sign_prod {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) (hts : t ⊆ s) :
    (↑(genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts
      (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin)))) : ℤ) =
      (∏ P ∈ t, P).sign := by
  classical
  rw [genusCharFunNarrowClassGroupHom_eq_prod_singleton, MonoidHom.finsetProd_apply, Units.coe_prod]
  calc
    _ = ∏ P : ↥t, (P : ℤ).sign :=
      Finset.prod_congr rfl fun P _ =>
        genusCharFunNarrowClassGroupHom_mkPrincipal_gen hs heven hprod hmin hgen hsf hd
          (hts P.property)
    _ = (∏ P ∈ t, P).sign := by
      rw [Finset.prod_coe_sort (f := Int.sign),
        ← genusCharFun_neg_one_eq_sign_prod (fun P hP => hs P (hts hP)), genusCharFun_def]
      exact Finset.prod_congr rfl fun P hP =>
        (primeDiscriminantCharFun_neg_one (hs P (hts hP))).symm

/-- The same genus character value on the narrow class of the quadratic generator is the sign
of the complementary prime-discriminant product. -/
theorem genusCharFunNarrowClassGroupHom_mkPrincipal_gen_eq_sign_prod_sdiff {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) (hts : t ⊆ s) :
    (↑(genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts
      (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin)))) : ℤ) =
      (∏ P ∈ s \ t, P).sign := by
  classical
  rw [genusCharFunNarrowClassGroupHom_mkPrincipal_gen_eq_sign_prod hs heven hprod hmin hgen hsf hd]
  have hpos := fundamentalDiscriminant_pos_iff.mpr hd
  have hmul : 0 < (∏ P ∈ s \ t, P) * ∏ P ∈ t, P := by
    rwa [Finset.prod_sdiff hts, hprod]
  rcases mul_pos_iff.mp hmul with ⟨hc, ht⟩ | ⟨hc, ht⟩
  · rw [Int.sign_eq_one_of_pos ht, Int.sign_eq_one_of_pos hc]
  · rw [Int.sign_eq_neg_one_of_neg ht, Int.sign_eq_neg_one_of_neg hc]

/-! ### The distinguished class in the principal genus -/

/-- **`[θ]⁺` is a square exactly when every prime discriminant is positive.** For a real quadratic
field `K = ℚ(√d)` with prime-discriminant factorization `s`, the narrow class of `(θ)` lies in
`Cl⁺(K)²` if and only if every `P ∈ s` is positive. -/
theorem isSquare_mkPrincipal_gen_iff {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) :
    IsSquare (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin))) ↔
      ∀ P ∈ s, 0 < P := by
  have heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P' := fun _ hP _ hP' hPe hPe' =>
    eq_of_isEvenPrimeDiscriminant_of_prod_eq (isFundamentalDiscr_fundamentalDiscriminant hsf) hprod
      hP hP' hPe hPe'
  rw [isSquare_iff_forall_genusCharFunNarrowClassGroupHom_eq_one hs heven hprod hmin hgen hsf]
  refine forall₂_congr fun P hP => ?_
  rw [Units.ext_iff, Units.val_one,
    genusCharFunNarrowClassGroupHom_mkPrincipal_gen hs heven hprod hmin hgen hsf hd hP,
    Int.sign_eq_one_iff_pos]

/-- The narrow class of the quadratic generator is square exactly when the field
discriminant has no prime divisor congruent to `3` modulo `4`. -/
theorem isSquare_mkPrincipal_gen_iff_forall_prime_dvd_mod_four_ne_three
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) :
    IsSquare (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin))) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr K → p % 4 ≠ 3 := by
  have hD := isFundamentalDiscr_fundamentalDiscriminant hsf
  obtain ⟨s, hs, heven, hprod⟩ := hD.exists_finset_primeDiscriminant
  have hpos := fundamentalDiscriminant_pos_iff.mpr hd
  rw [discr_eq_fundamentalDiscriminant hmin hgen hsf,
    isSquare_mkPrincipal_gen_iff hs hprod hmin hgen hsf hd, ← hprod]
  exact forall_pos_iff_forall_prime_dvd_mod_four_ne_three hs heven (hprod.symm ▸ hpos)

/-- The narrow class of the quadratic generator belongs to the principal genus if and only if
the field discriminant is a sum of two integer squares. -/
theorem isSquare_mkPrincipal_gen_iff_exists_sq_add_sq
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) :
    IsSquare (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin))) ↔
      ∃ x y : ℤ, discr K = x ^ 2 + y ^ 2 := by
  rw [isSquare_mkPrincipal_gen_iff_forall_prime_dvd_mod_four_ne_three hmin hgen hsf hd,
    discr_eq_fundamentalDiscriminant hmin hgen hsf]
  have hpos := fundamentalDiscriminant_pos_iff.mpr hd
  exact ((isFundamentalDiscr_fundamentalDiscriminant hsf).exists_sq_add_sq_iff hpos).symm

end TauCeti.Multiquadratic
