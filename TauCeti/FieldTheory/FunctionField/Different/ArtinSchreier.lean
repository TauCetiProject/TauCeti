/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Hilbert
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Place.ArtinSchreier
public import TauCeti.FieldTheory.FunctionField.Place.Extension.ArtinSchreier.Displacement
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.TotallyRamified

import TauCeti.FieldTheory.ArtinSchreier.Basic

/-!
# Ramification from a reduced Artin--Schreier representative

Let `F' = F(y)` with `y ^ p - y = u` in characteristic `p`.  Replacing `y` by `y - w`
replaces `u` by the equivalent representative `u - (w ^ p - w)`.  This file proves the
ramification dichotomy for a representative reduced at a place `P`:

* if the representative is regular at `P`, every place above `P` has different exponent zero
  and ramification index one;
* if it has a pole of order `m` not divisible by `p`, every place above `P` is totally ramified
  and its different exponent is `(p - 1) * (m + 1)`.

The regular case follows from the derivative `-1` of `X ^ p - X - u`.  In the pole case, a
Bezout construction supplies a generating uniformizer `z` such that every nonidentity Galois
automorphism satisfies `ord (σ z - z) = m + 1`.  Its powers form an integral basis at the totally
ramified place, so the derivative formula for the different turns these displacements into the
exact exponent.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (k F) {P' : Place k' F'}

/-- An Artin--Schreier generator whose right-hand side is regular has different exponent zero.

This is the `m_P = -1` case of the Artin--Schreier different formula. -/
theorem differentExponent_eq_zero_of_pow_sub_self_eq_of_mem_integers
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {a : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' a)
    (ha : a ∈ (P'.restrict k F).integers) :
    differentExponent k F P' = 0 := by
  let ψ : F[X] := X ^ p - (X + C a)
  have hmonic : ψ.Monic := by
    apply monic_X_pow_sub
    rw [degree_X_add_C]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers := by
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
    intro i
    simp only [ψ, coeff_sub, coeff_X_pow, coeff_add, coeff_X, coeff_C]
    split_ifs <;> simp_all
  have hroot : aeval y ψ = 0 := by
    simp only [ψ, map_sub, map_pow, aeval_X, map_add, aeval_C]
    rw [sub_add_eq_sub_sub, hy, sub_self]
  have hder : aeval y (derivative ψ) = -1 := by
    simp [ψ, derivative_X_pow, CharP.cast_eq_zero]
  apply differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one k F hgen hmonic
    hcoeff hroot
  rw [hder, P'.valuation.map_neg]
  exact P'.valuation.map_one

/-- An Artin--Schreier generator whose right-hand side is regular has ramification index one at
every place above the given place. -/
theorem ramificationIdx_eq_one_of_pow_sub_self_eq_of_mem_integers
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {a : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' a)
    (ha : a ∈ (P'.restrict k F).integers) :
    ramificationIdx F P' = 1 := by
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  rw [differentExponent_eq_zero_of_pow_sub_self_eq_of_mem_integers k F p hgen hy ha] at hle
  exact le_antisymm hle (ramificationIdx_pos F P')

/-- If an Artin--Schreier class has a representative regular at the place below `P'`, then the
different exponent at `P'` is zero. -/
theorem differentExponent_eq_zero_of_exists_sub_pow_sub_self_mem_integers
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hreg : ∃ w : F, u - (w ^ p - w) ∈ (P'.restrict k F).integers) :
    differentExponent k F P' = 0 := by
  obtain ⟨w, hw⟩ := hreg
  have hadj : F⟮y - algebraMap F F' w⟯ = F⟮y⟯ := by
    simpa [sub_eq_add_neg] using IntermediateField.adjoin_simple_add_algebraMap y (-w)
  have : CharP F' p := charP_of_injective_algebraMap (algebraMap F F').injective p
  apply differentExponent_eq_zero_of_pow_sub_self_eq_of_mem_integers k F p (hadj.trans hgen)
  · rw [sub_algebraMap_pow_sub_self_eq, hy, ← map_sub]
  · exact hw

/-- If an Artin--Schreier class has a representative regular at the place below `P'`, then `P'`
has ramification index one over that place. -/
theorem ramificationIdx_eq_one_of_exists_sub_pow_sub_self_mem_integers
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hreg : ∃ w : F, u - (w ^ p - w) ∈ (P'.restrict k F).integers) :
    ramificationIdx F P' = 1 := by
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  rw [differentExponent_eq_zero_of_exists_sub_pow_sub_self_mem_integers k F p hgen hy hreg]
    at hle
  exact le_antisymm hle (ramificationIdx_pos F P')

/-- At an Artin--Schreier pole of order `m` prime to `p`, the different exponent is
`(p - 1) * (m + 1)`. No perfection hypothesis on the residue field is needed. -/
theorem differentExponent_eq_of_pow_sub_self_eq_of_ord_eq_neg
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (p m : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u = -(m : ℤ))
    (hprime : ¬ (p : ℤ) ∣ (P'.restrict k F).ord u) :
    differentExponent k F P' = (p - 1) * (m + 1) := by
  classical
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  let _ : Algebra.IsIntegral k k' := Algebra.IsIntegral.of_finite k k'
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  let _ : IsGalois F F' := ArtinSchreier.isGalois hy hgen
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp only [Nat.cast_zero, neg_zero] at hu
    apply hprime
    rw [hu]
    exact dvd_zero _
  have huneg : (P'.restrict k F).ord u < 0 := by rw [hu]; omega
  have hcop : Int.gcd p ((P'.restrict k F).ord u) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      ((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr hprime)
  obtain ⟨z, hzgen, hzord, hdisp⟩ :=
    exists_uniformizer_ord_aut_sub_of_artinSchreier_pole k F p hgen hy huneg hcop
  have htot := isTotallyRamified_of_pow_sub_self_eq_of_gcd_ord_eq_one k F
    (Fact.out : p.Prime).one_lt hgen hy huneg hcop
  have hzint : IsIntegral (P'.restrict k F).integers z :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' (P'.restrict k F)).mpr fun Q hQ ↦ by
      rw [eq_of_isTotallyRamified k F htot hQ]
      exact P'.mem_integers_iff_ord_nonneg.mpr (by rw [hzord]; omega)
  let x : integralClosure (P'.restrict k F).integers F' := ⟨z, hzint⟩
  have hxord : P'.ord
      (algebraMap (integralClosure (P'.restrict k F).integers F') F' x) = 1 := hzord
  have hxgen := algebra_adjoin_integralClosure_eq_top_of_isTotallyRamified
    k F htot hxord
  have hd := differentExponent_eq_sum_ord_sub_aut_of_algebra_adjoin_eq_top k F hxgen
  have hxcoe : algebraMap (integralClosure (P'.restrict k F).integers F') F' x = z := rfl
  rw [hxcoe] at hd
  have hterm : ∀ σ ∈ (Finset.univ : Finset (F' ≃ₐ[F] F')).erase 1,
      P'.ord (z - σ z) = 1 - (P'.restrict k F).ord u := by
    intro σ hσ
    rw [← P'.ord_neg, neg_sub]
    exact hdisp σ (Finset.ne_of_mem_erase hσ)
  have hcard : Fintype.card (F' ≃ₐ[F] F') = p := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      finrank_eq_of_pow_sub_self_eq_of_gcd_ord_eq_one k F
        (Fact.out : p.Prime).one_lt hgen hy huneg hcop]
  have herase : ((Finset.univ : Finset (F' ≃ₐ[F] F')).erase 1).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, hcard]
  have hd' : (differentExponent k F P' : ℤ) =
      (((p - 1) * (m + 1) : ℕ) : ℤ) := by
    calc
      (differentExponent k F P' : ℤ) =
          ∑ σ ∈ (Finset.univ : Finset (F' ≃ₐ[F] F')).erase 1, P'.ord (z - σ z) := by
            exact hd
      _ = ∑ _σ ∈ (Finset.univ : Finset (F' ≃ₐ[F] F')).erase 1,
          (1 - (P'.restrict k F).ord u) := Finset.sum_congr rfl hterm
      _ = (((p - 1) * (m + 1) : ℕ) : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, herase, hu]
        push_cast
        ring
  exact_mod_cast hd'

/-- The exact different formula for a supplied reduced representative of an Artin--Schreier
class. Translating the generator does not change the extension. -/
theorem differentExponent_eq_of_sub_pow_sub_self_ord_eq_neg
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (p m : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u w : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hu : (P'.restrict k F).ord (u - (w ^ p - w)) = -(m : ℤ))
    (hprime : ¬ (p : ℤ) ∣ (P'.restrict k F).ord (u - (w ^ p - w))) :
    differentExponent k F P' = (p - 1) * (m + 1) := by
  have hadj : F⟮y - algebraMap F F' w⟯ = ⊤ := by
    simpa [sub_eq_add_neg] using
      (IntermediateField.adjoin_simple_add_algebraMap y (-w)).trans hgen
  let _ : CharP F' p := charP_of_injective_algebraMap (algebraMap F F').injective p
  apply differentExponent_eq_of_pow_sub_self_eq_of_ord_eq_neg
    k F hF hF' p m hadj _ hu hprime
  rw [sub_algebraMap_pow_sub_self_eq, hy, ← map_sub]

/-- A reduced Artin--Schreier pole is wildly ramified.  Indeed, its ramification index is `p`,
which vanishes in the residue field of the place below. -/
theorem isWild_of_exists_reduced_artinSchreier_pole
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - (w ^ p - w)) < 0 ∧
      ¬ (p : ℤ) ∣ (P'.restrict k F).ord (u - (w ^ p - w))) :
    IsWild k F P' := by
  let _ : CharP k p := (algebraMap k F).charP (algebraMap k F).injective p
  let _ : CharP (((P'.restrict k F).integers) ⧸
      IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) p :=
    charP_of_injective_algebraMap
      (algebraMap k (((P'.restrict k F).integers) ⧸
        IsLocalRing.maximalIdeal ((P'.restrict k F).integers))).injective p
  rw [isWild_iff]
  right
  rw [ramificationIdx_eq_of_exists_reduced_artinSchreier_pole k F p hgen hy hpole]
  exact CharP.cast_eq_zero _ p

/-- At a reduced Artin--Schreier pole the different exponent is at least `p`.  This is the wild
lower bound; the exact exponent additionally requires the upper bound
`d(P' | P) ≤ (p - 1) * (m + 1)`. -/
theorem p_le_differentExponent_of_exists_reduced_artinSchreier_pole
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - (w ^ p - w)) < 0 ∧
      ¬ (p : ℤ) ∣ (P'.restrict k F).ord (u - (w ^ p - w))) :
    p ≤ differentExponent k F P' := by
  rw [← ramificationIdx_eq_of_exists_reduced_artinSchreier_pole k F p hgen hy hpole]
  exact (ramificationIdx_le_differentExponent_iff k F P').mpr
    (isWild_of_exists_reduced_artinSchreier_pole k F p hgen hy hpole)

/-- For a supplied reduced Artin--Schreier representative, a place is either unramified with
different exponent zero, or is totally ramified and satisfies the wild lower bound for the
different exponent.  This statement does not require the residue field to be perfect. -/
theorem differentExponent_eq_zero_and_ramificationIdx_eq_one_or_p_le_differentExponent
    (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hred : ∃ w : F, u - (w ^ p - w) ∈ (P'.restrict k F).integers ∨
      ((P'.restrict k F).ord (u - (w ^ p - w)) < 0 ∧
        ¬ (p : ℤ) ∣ (P'.restrict k F).ord (u - (w ^ p - w)))) :
    (differentExponent k F P' = 0 ∧ ramificationIdx F P' = 1) ∨
      (p ≤ differentExponent k F P' ∧ ramificationIdx F P' = p) := by
  obtain ⟨w, hw | hw⟩ := hred
  · exact Or.inl ⟨
      differentExponent_eq_zero_of_exists_sub_pow_sub_self_mem_integers k F p hgen hy ⟨w, hw⟩,
      ramificationIdx_eq_one_of_exists_sub_pow_sub_self_mem_integers k F p hgen hy ⟨w, hw⟩⟩
  · exact Or.inr ⟨
      p_le_differentExponent_of_exists_reduced_artinSchreier_pole
        k F p hgen hy ⟨w, hw⟩,
      ramificationIdx_eq_of_exists_reduced_artinSchreier_pole k F p hgen hy ⟨w, hw⟩⟩

/-- Over a perfect residue field, an Artin--Schreier place is either unramified with different
exponent zero, or is totally ramified and satisfies the wild lower bound.  The reduced
representative is produced inside `F`, without passing to a completion. -/
theorem
    differentExponent_eq_zero_and_ramificationIdx_eq_one_or_p_le_differentExponent_of_perfectField
    (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectField (P'.restrict k F).ResidueField]
    {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u) :
    (differentExponent k F P' = 0 ∧ ramificationIdx F P' = 1) ∨
      (p ≤ differentExponent k F P' ∧ ramificationIdx F P' = p) := by
  apply differentExponent_eq_zero_and_ramificationIdx_eq_one_or_p_le_differentExponent
    k F p hgen hy
  exact (P'.restrict k F).exists_reduced_artinSchreier_representative p u

end TauCeti.Place
