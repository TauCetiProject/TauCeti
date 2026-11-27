/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.GenusCharacter
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reflection
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Dirichlet
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Subfactorization
import TauCeti.NumberTheory.QuadraticOrder.Basic

/-!
# Genus characters attached to fundamental divisors

A product of prime-discriminant characters defines a genus character for forms whose
discriminant is the product of those factors and a cofactor congruent to `0` or `1` modulo four,
provided at most one factor is even. Its value on a form is the character at any represented
integer coprime to the product. It vanishes precisely when the content obstructs such a
representation. This applies to imprimitive forms and to square or zero discriminants.
Invertible substitutions preserve the character, and scaling a form multiplies its character by
the character of the scalar.

`binaryFormGenusChar` gives a total integer-valued character with the same evaluation rule on
that domain. Its definition gives precedence to a represented value with character `1`.

## References

* B. Gross, W. Kohnen, and D. Zagier, *Heegner points and derivatives of L-series. II*,
  Ch. I §2, pp. 508–509.
-/

public section

open scoped MatrixGroups

namespace TauCeti.Multiquadratic

open BinaryQuadraticForm

/-- A prime-discriminant character is trivial on coprime values of the principal form
when its complementary factor satisfies the dyadic congruence. -/
private theorem primeDiscriminantCharFun_principalForm_eq_one {P e : ℤ}
    (hP : IsPrimeDiscriminant P) (he : IsEvenPrimeDiscriminant P → e % 4 = 0 ∨ e % 4 = 1)
    (hD : (P * e) % 4 = 0 ∨ (P * e) % 4 = 1) (x y : ℤ)
    (hcop : IsCoprime ((principalForm (P * e)).eval x y) P) :
    primeDiscriminantCharFun P ((principalForm (P * e)).eval x y) = 1 := by
  by_cases hzero : IsEvenPrimeDiscriminant P ∧ e % 4 = 0
  · obtain ⟨hPe, he₀⟩ := hzero
    have hunit : IsUnit (((principalForm (P * e)).eval x y : ℤ) : ZMod P.natAbs) :=
      (ZMod.isUnit_intCast_iff_isCoprime _ _).mpr (by
        simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hcop.symm)
    -- An even prime discriminant with a cofactor divisible by four reduces to the
    -- already established genus-character laws for the principal form of discriminant `4N`.
    rcases hPe with rfl | rfl | rfl
    · have h : (-4 : ℤ) * e = 4 * (-e) := by ring
      rw [h] at hunit ⊢
      rw [primeDiscriminantCharFun_neg_four]
      exact isGenusChar_iff.mp (isGenusChar_χ₄ (N := -e) (Or.inl (by omega))) x y hunit
    · have h : (8 : ℤ) * e = 4 * (2 * e) := by ring
      rw [h] at hunit ⊢
      rw [primeDiscriminantCharFun_eight]
      exact isGenusChar_iff.mp
        (isGenusChar_of_emod_eight_eq_zero (N := 2 * e) (by omega) ZMod.χ₈) x y hunit
    · have h : (-8 : ℤ) * e = 4 * (-2 * e) := by ring
      rw [h] at hunit ⊢
      rw [primeDiscriminantCharFun_neg_eight]
      exact isGenusChar_iff.mp
        (isGenusChar_of_emod_eight_eq_zero (N := -2 * e) (by omega) ZMod.χ₈') x y hunit
  · exact primeDiscriminantCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq hP
      (fun hPe => (he hPe).resolve_left (fun h => hzero ⟨hPe, h⟩)) hcop
      (four_mul_eval_principalForm hD x y)

/-- The product of the characters of the prime discriminants in `t` is a genus character
for a form of discriminant `(∏ P ∈ t, P) * e` if at most one factor is even and the cofactor
`e` is a discriminant modulo four. -/
theorem isGenusChar_genusChar {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ t, ∀ P' ∈ t, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {e : ℤ} (he : e % 4 = 0 ∨ e % 4 = 1) :
    IsGenusChar ((∏ P ∈ t, P) * e) (genusChar t ht) := by
  rw [isGenusChar_iff]
  intro x y hunit
  have hcop : IsCoprime ((principalForm ((∏ P ∈ t, P) * e)).eval x y) (∏ P ∈ t, P) := by
    simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using
      ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hunit).symm
  rw [genusChar_apply_int, genusCharFun_def]
  refine Finset.prod_eq_one fun P hP => ?_
  have hfactor : (∏ P' ∈ t, P') * e = P * ((∏ P' ∈ t.erase P, P') * e) := by
    rw [← mul_assoc, Finset.mul_prod_erase t (fun n => n) hP]
  have hmod : ((∏ P' ∈ t, P') * e) % 4 = 0 ∨ ((∏ P' ∈ t, P') * e) % 4 = 1 := by
    have hδ : (∏ P' ∈ t, P') % 4 = 0 ∨ (∏ P' ∈ t, P') % 4 = 1 :=
      (isFundamentalDiscr_prod (D := id) ht (Set.injOn_id _) heven).emod_four_eq_zero_or_one
    rw [Int.mul_emod]
    rcases hδ with hδ | hδ <;> rcases he with he | he <;> norm_num [hδ, he]
  rw [hfactor] at hmod ⊢
  refine primeDiscriminantCharFun_principalForm_eq_one (ht P hP) ?_ hmod x y ?_
  · intro hPe
    have hrest : (∏ P' ∈ t.erase P, P') % 4 = 1 :=
      prod_primeDiscriminant_mod_four_eq_one (fun P' hP' => ht P' (Finset.mem_of_mem_erase hP'))
        (fun P' hP' hP'e => Finset.ne_of_mem_erase hP'
          (heven P hP P' (Finset.mem_of_mem_erase hP') hPe hP'e).symm)
    rwa [Int.mul_emod, hrest, one_mul, Int.emod_emod]
  · rw [← hfactor]
    exact hcop.of_prod_right _ hP

/-- The form character associated to `t` is `1` if the form represents an integer coprime to
the product with character `1`, `-1` if it represents a coprime integer but none with character
`1`, and `0` if it represents no coprime integer. -/
noncomputable def binaryFormGenusChar (t : Finset ℤ) (Q : BinaryQuadraticForm ℤ) : ℤ := by
  classical
  exact if ∃ x y : ℤ, IsCoprime (Q.eval x y) (∏ P ∈ t, P) ∧ genusCharFun t (Q.eval x y) = 1 then 1
    else if ∃ x y : ℤ, IsCoprime (Q.eval x y) (∏ P ∈ t, P) then -1 else 0

open scoped Classical in
/-- The three branches of the total form character, expressed through represented integers. -/
theorem binaryFormGenusChar_def (t : Finset ℤ) (Q : BinaryQuadraticForm ℤ) :
    binaryFormGenusChar t Q =
      if ∃ x y : ℤ, IsCoprime (Q.eval x y) (∏ P ∈ t, P) ∧ genusCharFun t (Q.eval x y) = 1 then 1
      else if ∃ x y : ℤ, IsCoprime (Q.eval x y) (∏ P ∈ t, P) then -1 else 0 := by
  rfl

/-- For a fundamental divisor of the form's discriminant, evaluate the form character at any
represented integer coprime to the product of the prime discriminants. -/
theorem binaryFormGenusChar_eq_of_represents {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ t, ∀ P' ∈ t, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {Q : BinaryQuadraticForm ℤ} {e : ℤ} (he : e % 4 = 0 ∨ e % 4 = 1)
    (hD : Q.discrim = (∏ P ∈ t, P) * e) {x y : ℤ}
    (hcop : IsCoprime (Q.eval x y) (∏ P ∈ t, P)) :
    binaryFormGenusChar t Q = genusCharFun t (Q.eval x y) := by
  classical
  rw [binaryFormGenusChar_def]
  by_cases hone : ∃ u v : ℤ, IsCoprime (Q.eval u v) (∏ P ∈ t, P) ∧
      genusCharFun t (Q.eval u v) = 1
  · rw [ite_eq_left hone]
    obtain ⟨u, v, huv, hval⟩ := hone
    have isUnit_of_coprime {n : ℤ} (hn : IsCoprime n (∏ P ∈ t, P)) :
        IsUnit (n : ZMod (∏ P ∈ t, P).natAbs) :=
      (ZMod.isUnit_intCast_iff_isCoprime _ _).mpr (by
        simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hn.symm)
    have hχ : IsGenusChar Q.discrim (genusChar t ht) := hD ▸ isGenusChar_genusChar ht heven he
    simpa only [genusChar_apply_int, hval] using
      hχ.apply_eval_eq_apply_eval (isUnit_of_coprime huv) (isUnit_of_coprime hcop)
  · have hex : ∃ u v, IsCoprime (Q.eval u v) (∏ P ∈ t, P) := ⟨x, y, hcop⟩
    rw [ite_eq_right hone, ite_eq_left hex]
    exact ((genusCharFun_eq_one_or_eq_neg_one ht hcop).resolve_left
      (fun h => hone ⟨x, y, hcop, h⟩)).symm

/-- The total form character vanishes exactly when there is no represented integer coprime
to the product of the indices. -/
theorem binaryFormGenusChar_eq_zero_iff_not_exists (t : Finset ℤ) (Q : BinaryQuadraticForm ℤ) :
    binaryFormGenusChar t Q = 0 ↔ ¬ ∃ x y : ℤ, IsCoprime (Q.eval x y) (∏ P ∈ t, P) := by
  classical
  rw [binaryFormGenusChar_def]
  split_ifs with hpos hcop
  · obtain ⟨x, y, h, -⟩ := hpos
    have hex : ∃ u v, IsCoprime (Q.eval u v) (∏ P ∈ t, P) := ⟨x, y, h⟩
    simp [hex]
  · simp [hcop]
  · simp [hcop]

/-- For a nonzero product of indices the total form character vanishes exactly when the
content and that product have a common nonunit factor. -/
theorem binaryFormGenusChar_eq_zero_iff {t : Finset ℤ}
    (hprod : (∏ P ∈ t, P) ≠ 0) (Q : BinaryQuadraticForm ℤ) :
    binaryFormGenusChar t Q = 0 ↔ ¬ IsCoprime (Q.content : ℤ) (∏ P ∈ t, P) := by
  rw [binaryFormGenusChar_eq_zero_iff_not_exists, Q.exists_isCoprime_eval_iff hprod]

/-- The empty product gives the trivial character on all forms. -/
@[simp] theorem binaryFormGenusChar_empty (Q : BinaryQuadraticForm ℤ) :
    binaryFormGenusChar ∅ Q = 1 := by
  classical
  rw [binaryFormGenusChar_def, ite_eq_left]
  exact ⟨0, 0, by simp [isCoprime_one_right]⟩

/-- For a fundamental divisor, the total character agrees with the form character of the
bundled Dirichlet character. -/
theorem binaryFormGenusChar_eq_genusChar {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ t, ∀ P' ∈ t, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {Q : BinaryQuadraticForm ℤ} {e : ℤ} (he : e % 4 = 0 ∨ e % 4 = 1)
    (hD : Q.discrim = (∏ P ∈ t, P) * e) :
    binaryFormGenusChar t Q = BinaryQuadraticForm.genusChar (genusChar t ht) Q := by
  have hunit (x y : ℤ) :
      IsUnit (Q.eval x y : ZMod (∏ P ∈ t, P).natAbs) ↔
        IsCoprime (Q.eval x y) (∏ P ∈ t, P) := by
    rw [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]
    simp only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
  by_cases hex : ∃ x y, IsCoprime (Q.eval x y) (∏ P ∈ t, P)
  · obtain ⟨x, y, hxy⟩ := hex
    have hχ : IsGenusChar Q.discrim (genusChar t ht) := hD ▸ isGenusChar_genusChar ht heven he
    rw [binaryFormGenusChar_eq_of_represents ht heven he hD hxy,
      hχ.genusChar_eq ((hunit x y).2 hxy), genusChar_apply_int]
  · rw [(binaryFormGenusChar_eq_zero_iff_not_exists t Q).2 hex,
      genusChar_eq_zero (fun x y hu => hex ⟨x, y, (hunit x y).1 hu⟩)]

private theorem binaryFormGenusChar_congr_of_exists_eval_iff (t : Finset ℤ)
    {Q Q' : BinaryQuadraticForm ℤ}
    (h : ∀ p : ℤ → Prop, (∃ x y, p (Q'.eval x y)) ↔ ∃ x y, p (Q.eval x y)) :
    binaryFormGenusChar t Q' = binaryFormGenusChar t Q := by
  classical
  rw [binaryFormGenusChar_def, binaryFormGenusChar_def]
  exact if_congr (h (fun m => IsCoprime m (∏ P ∈ t, P) ∧ genusCharFun t m = 1)) rfl
    (if_congr (h (fun m => IsCoprime m (∏ P ∈ t, P))) rfl rfl)

/-- Invertible substitutions preserve the total form character. -/
theorem binaryFormGenusChar_eq_of_eval_comp_equiv (t : Finset ℤ) {Q Q' : BinaryQuadraticForm ℤ}
    (g : (ℤ × ℤ) ≃ (ℤ × ℤ))
    (h : ∀ v : ℤ × ℤ, Q'.eval v.1 v.2 = Q.eval (g v).1 (g v).2) :
    binaryFormGenusChar t Q' = binaryFormGenusChar t Q := by
  refine binaryFormGenusChar_congr_of_exists_eval_iff t fun p => ?_
  simpa only [Prod.exists] using g.exists_congr
    (p := fun v => p (Q'.eval v.1 v.2)) (q := fun v => p (Q.eval v.1 v.2))
    (fun v => iff_of_eq (congrArg p (h v)))

/-- The total form character is invariant under proper changes of variables. -/
@[simp] theorem binaryFormGenusChar_sl2_smul (t : Finset ℤ) (γ : SL(2, ℤ))
    (Q : BinaryQuadraticForm ℤ) : binaryFormGenusChar t (γ • Q) = binaryFormGenusChar t Q :=
  binaryFormGenusChar_congr_of_exists_eval_iff t (exists_eval_smul_iff γ Q)

/-- Changing the sign of the middle coefficient preserves the total form character. -/
@[simp] theorem binaryFormGenusChar_reflected (t : Finset ℤ) (Q : BinaryQuadraticForm ℤ) :
    binaryFormGenusChar t Q.reflected = binaryFormGenusChar t Q :=
  binaryFormGenusChar_eq_of_eval_comp_equiv t
    (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) (fun v => Q.eval_reflected v.1 v.2)

/-- Scaling a form multiplies its character by the character of the scalar, when the product
of the prime discriminants is a fundamental divisor of the original discriminant. -/
theorem binaryFormGenusChar_smul {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ t, ∀ P' ∈ t, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {Q : BinaryQuadraticForm ℤ} {e : ℤ} (he : e % 4 = 0 ∨ e % 4 = 1)
    (hD : Q.discrim = (∏ P ∈ t, P) * e) (μ : ℤ) :
    binaryFormGenusChar t (μ • Q) = genusCharFun t μ * binaryFormGenusChar t Q := by
  have hscaled :
      (∃ x y, IsCoprime ((μ • Q).eval x y) (∏ P ∈ t, P)) ↔
        IsCoprime μ (∏ P ∈ t, P) ∧ ∃ x y, IsCoprime (Q.eval x y) (∏ P ∈ t, P) := by
    simp only [eval_smul', IsCoprime.mul_left_iff]
    exact ⟨fun ⟨x, y, hμ, hxy⟩ => ⟨hμ, x, y, hxy⟩, fun ⟨hμ, x, y, hxy⟩ => ⟨x, y, hμ, hxy⟩⟩
  by_cases hc : IsCoprime μ (∏ P ∈ t, P) ∧ ∃ x y, IsCoprime (Q.eval x y) (∏ P ∈ t, P)
  · obtain ⟨hμ, x, y, hxy⟩ := hc
    have hD' : (μ • Q).discrim = (∏ P ∈ t, P) * (μ ^ 2 * e) := by
      rw [discrim_smul', hD, mul_left_comm]
    have hxy' : IsCoprime ((μ • Q).eval x y) (∏ P ∈ t, P) := by
      rw [eval_smul']
      exact hμ.mul_left hxy
    rw [binaryFormGenusChar_eq_of_represents ht heven
        (QuadraticOrder.sq_mul_emod_four_eq_zero_or_one he μ) hD' hxy',
      binaryFormGenusChar_eq_of_represents ht heven he hD hxy, eval_smul', genusCharFun_mul_right]
  · rw [(binaryFormGenusChar_eq_zero_iff_not_exists t (μ • Q)).2 (hc ∘ hscaled.mp)]
    rcases not_and_or.mp hc with hμ | hQ
    · rw [(genusCharFun_eq_zero_iff ht).2 hμ, zero_mul]
    · rw [(binaryFormGenusChar_eq_zero_iff_not_exists t Q).2 hQ, mul_zero]

/-- Negating a form multiplies its character by the sign of the fundamental divisor. -/
theorem binaryFormGenusChar_neg {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ t, ∀ P' ∈ t, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {Q : BinaryQuadraticForm ℤ} {e : ℤ} (he : e % 4 = 0 ∨ e % 4 = 1)
    (hD : Q.discrim = (∏ P ∈ t, P) * e) :
    binaryFormGenusChar t (-Q) = (∏ P ∈ t, P).sign * binaryFormGenusChar t Q := by
  simpa only [neg_one_smul, genusCharFun_neg_one_eq_sign_prod ht] using
    binaryFormGenusChar_smul ht heven he hD (-1)

end TauCeti.Multiquadratic
