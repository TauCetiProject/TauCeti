/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.OrdinaryTwoRank
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Positivity
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant

/-!
# The class of the different in a real quadratic field

For a real quadratic field presented by `θ² = d` with squarefree `d`, let `J` be the narrow
class of `(θ)`, which is the class of the different. The genus character of a subset of the
prime-discriminant factors takes on `J` the sign of their product. The class `J` belongs to the
principal genus exactly when the field discriminant is a sum of two integer squares, or
equivalently when no prime congruent to `3` modulo `4` divides it. Such a prime divisor also
forces the narrow class number to be twice the ordinary class number.

See Duke, Imamoglu and Toth, *Geometric invariants for real quadratic fields*, §§2, 4 and 7.
-/

public section

open NumberField Polynomial
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

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
  have hpos : 0 < fundamentalDiscriminant d := by
    rw [fundamentalDiscriminant_def]
    split_ifs <;> positivity
  have hmul : 0 < (∏ P ∈ s \ t, P) * ∏ P ∈ t, P := by
    rwa [Finset.prod_sdiff hts, hprod]
  rcases mul_pos_iff.mp hmul with ⟨hc, ht⟩ | ⟨hc, ht⟩
  · rw [Int.sign_eq_one_of_pos ht, Int.sign_eq_one_of_pos hc]
  · rw [Int.sign_eq_neg_one_of_neg ht, Int.sign_eq_neg_one_of_neg hc]

/-- The narrow class of the quadratic generator is square exactly when the field
discriminant has no prime divisor congruent to `3` modulo `4`. -/
theorem isSquare_mkPrincipal_gen_iff_forall_prime_dvd_mod_four_ne_three
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) :
    IsSquare (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin))) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr K → p % 4 ≠ 3 := by
  have hD := isFundamentalDiscr_fundamentalDiscriminant hsf
  obtain ⟨s, hs, heven, hprod⟩ := hD.exists_finset_primeDiscriminant
  have hpos : 0 < fundamentalDiscriminant d := by
    rw [fundamentalDiscriminant_def]
    split_ifs <;> positivity
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
  have hpos : 0 < fundamentalDiscriminant d := by
    rw [fundamentalDiscriminant_def]
    split_ifs <;> positivity
  exact ((isFundamentalDiscr_fundamentalDiscriminant hsf).exists_sq_add_sq_iff hpos).symm

/-- A prime divisor of the field discriminant congruent to `3` modulo `4` forces the
narrow class of the quadratic generator to be nontrivial. -/
theorem mkPrincipal_gen_ne_one_of_prime_dvd_discr_of_mod_four_eq_three
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) {p : ℕ}
    (hp : p.Prime) (hpd : (p : ℤ) ∣ discr K) (hp3 : p % 4 = 3) :
    NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin)) ≠ 1 := by
  intro h
  have hsq :
      IsSquare (NarrowClassGroup.mkPrincipal (Units.mk0 (θ : K) (coe_gen_ne_zero hmin))) :=
    h.symm ▸ IsSquare.one
  exact (isSquare_mkPrincipal_gen_iff_forall_prime_dvd_mod_four_ne_three hmin hgen hsf hd).mp
    hsq p hp hpd hp3

/-- The narrow class number is twice the ordinary class number if the field discriminant
has a prime divisor congruent to `3` modulo `4`. -/
theorem card_eq_two_mul_card_classGroup_of_prime_dvd_discr_of_mod_four_eq_three
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 0 < d) {p : ℕ}
    (hp : p.Prime) (hpd : (p : ℤ) ∣ discr K) (hp3 : p % 4 = 3) :
    Nat.card (NarrowClassGroup K) = 2 * Nat.card (ClassGroup (𝓞 K)) := by
  apply
    TauCeti.NumberField.NarrowClassGroup.card_eq_two_mul_card_classGroup_of_forall_norm_ne_neg_one
      hmin hgen hd
  intro u hu
  exact mkPrincipal_gen_ne_one_of_prime_dvd_discr_of_mod_four_eq_three hmin hgen hsf hd hp hpd hp3
    ((NarrowClassGroup.mkPrincipal_gen_eq_one_iff_exists_norm_eq_neg_one hmin hgen hd).mpr ⟨u, hu⟩)

end TauCeti.Multiquadratic
