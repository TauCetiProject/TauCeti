/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Hilbert
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Place.Extension.ArtinSchreier.Additive
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.TotallyRamified

import TauCeti.FieldTheory.ArtinSchreier.Additive

/-!
# The different of an elementary abelian Artin–Schreier extension

Let `V` be a finite additive subgroup of `F` consisting of constants, with additive polynomial
`a_V = ∏_{c ∈ V} (X - c)`, and let `F' = F(y)` with `a_V (y) = u`. Replacing `y` by `y - w`
replaces `u` by the representative `u - a_V (w)` of its class. This file computes the different
exponent at a place `P'` of `F'` from a representative reduced at the place `P` below:

* if the representative is regular at `P`, then `d(P' ∣ P) = 0` and `e(P' ∣ P) = 1`;
* if it has a pole of order `m` prime to `|V|`, then `P'` is totally ramified and
  `d(P' ∣ P) = (|V| - 1) (m + 1)`.

This is Stichtenoth's Proposition 3.7.10(c) and (d). For `V` the prime field these are the
Artin–Schreier formulas of `TauCeti.FieldTheory.FunctionField.Different.ArtinSchreier.Basic`.

In the regular case the derivative of `a_V - u` is the nonzero constant `∏_{c ≠ 0} (-c)`
(`AddSubgroup.derivative_additivePolynomial`), a unit at `P'`. In the pole case a generating
uniformizer `z` has displacement `ord (σ z - z) = m + 1` under every nonidentity automorphism
(`TauCeti.Place.exists_uniformizer_ord_aut_sub_of_aeval_additivePolynomial_eq`), its powers form an
integral basis at the totally ramified place, and the different exponent is the sum of the
`|V| - 1` displacements.

## Main results

* `TauCeti.Place.differentExponent_eq_zero_of_exists_sub_aeval_additivePolynomial_mem_integers`
  and `TauCeti.Place.ramificationIdx_eq_one_of_exists_sub_aeval_additivePolynomial_mem_integers`:
  a place with a regular representative is unramified, with different exponent zero.
* `TauCeti.Place.isWild_of_exists_reduced_additivePolynomial_pole`: for nontrivial `V`, a reduced
  pole of order prime to `|V|` is wildly ramified.
* `TauCeti.Place.differentExponent_eq_of_sub_aeval_additivePolynomial_ord_eq_neg`: at a reduced
  pole of order `m` prime to `|V|`, `d(P' ∣ P) = (|V| - 1) (m + 1)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.10.
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

variable (k F) (V : AddSubgroup F) [Fintype V] {P' : Place k' F'}

/-- If `a_V (y) = a` with `a` regular below `P'` and `V` consisting of constants, then the different
exponent at `P'` is zero. -/
theorem differentExponent_eq_zero_of_aeval_additivePolynomial_eq_of_mem_integers
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {a : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' a)
    (ha : a ∈ (P'.restrict k F).integers) :
    differentExponent k F P' = 0 := by
  classical
  have hint (c : V) : (c : F) ∈ (P'.restrict k F).integers := by
    rw [mem_integers_iff_ord_nonneg, ord_eq_zero_of_isAlgebraic _ (hV c c.2)]
  -- `a_V` is the image of a polynomial over the valuation ring.
  have hcoeff (i : ℕ) : V.additivePolynomial.coeff i ∈ (P'.restrict k F).integers := by
    have hmap : V.additivePolynomial =
        (∏ c : V, (X - C (⟨c, hint c⟩ : (P'.restrict k F).integers))).map
          (P'.restrict k F).integers.subtype := by
      simp [V.additivePolynomial_eq_prod, Polynomial.map_prod]
    rw [hmap, coeff_map]
    exact Subtype.prop _
  have hder : P'.valuation (aeval y (derivative (V.additivePolynomial - C a))) = 1 := by
    rw [derivative_sub, derivative_C, sub_zero, V.derivative_additivePolynomial, aeval_C,
      finprod_eq_prod_of_fintype, map_prod, map_prod]
    refine Finset.prod_eq_one fun c _ ↦ ?_
    have hc0 : algebraMap F F' c ≠ 0 :=
      (_root_.map_ne_zero _).mpr (by simpa using c.2)
    rw [map_neg, Valuation.map_neg]
    exact P'.valuation_eq_one_of_isAlgebraic (((hV _ c.1.2).algebraMap (A := F')).tower_top k') hc0
  refine differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one k F hgen
    (V.monic_additivePolynomial_sub_C a) (fun i ↦ ?_) (by rw [map_sub, hy, aeval_C, sub_self])
    hder
  rw [coeff_sub, coeff_C]
  exact sub_mem (hcoeff i) (by split_ifs <;> simp [ha])

/-- If `a_V (y) = a` with `a` regular below `P'` and `V` consisting of constants, then `P'` is
unramified. -/
theorem ramificationIdx_eq_one_of_aeval_additivePolynomial_eq_of_mem_integers
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {a : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' a)
    (ha : a ∈ (P'.restrict k F).integers) :
    ramificationIdx F P' = 1 := by
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  rw [differentExponent_eq_zero_of_aeval_additivePolynomial_eq_of_mem_integers k F V hV hgen hy
    ha] at hle
  exact le_antisymm hle (ramificationIdx_pos F P')

/-- If the class of `u` has a representative `u - a_V (w)` regular below `P'`, where `a_V (y) = u`
and `V` consists of constants, then the different exponent at `P'` is zero (Stichtenoth,
Proposition 3.7.10(c)). -/
theorem differentExponent_eq_zero_of_exists_sub_aeval_additivePolynomial_mem_integers
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hreg : ∃ w : F, u - aeval w V.additivePolynomial ∈ (P'.restrict k F).integers) :
    differentExponent k F P' = 0 := by
  obtain ⟨w, hw⟩ := hreg
  -- Translating the generator by `-w` does not change the field it generates.
  have hadj : F⟮y - algebraMap F F' w⟯ = ⊤ := by
    simpa [sub_eq_add_neg] using
      (IntermediateField.adjoin_simple_add_algebraMap y (-w)).trans hgen
  refine differentExponent_eq_zero_of_aeval_additivePolynomial_eq_of_mem_integers k F V hV hadj
    ?_ hw
  rw [AddSubgroup.aeval_additivePolynomial_sub, hy, aeval_algebraMap_apply, map_sub]

/-- If the class of `u` has a representative `u - a_V (w)` regular below `P'`, where `a_V (y) = u`
and `V` consists of constants, then `P'` is unramified (Stichtenoth, Proposition 3.7.10(c)). -/
theorem ramificationIdx_eq_one_of_exists_sub_aeval_additivePolynomial_mem_integers
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hreg : ∃ w : F, u - aeval w V.additivePolynomial ∈ (P'.restrict k F).integers) :
    ramificationIdx F P' = 1 := by
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  rw [differentExponent_eq_zero_of_exists_sub_aeval_additivePolynomial_mem_integers k F V hV hgen
    hy hreg] at hle
  exact le_antisymm hle (ramificationIdx_pos F P')

/-- A reduced pole of order prime to `|V|`, for a nontrivial `V` consisting of constants, is wildly
ramified: its ramification index `|V|` vanishes in the residue field of the place below. -/
theorem isWild_of_exists_reduced_additivePolynomial_pole [Nontrivial V]
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) ((P'.restrict k F).ord (u - aeval w V.additivePolynomial)) = 1) :
    IsWild k F P' := by
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  -- `|V|` kills a nonzero element of `F`, so it vanishes in `F`.
  obtain ⟨c, hc⟩ := exists_ne (0 : V)
  have hcard : (Fintype.card V : F) = 0 := by
    have h := congrArg ((↑) : V → F) (card_nsmul_eq_zero (x := c))
    rw [AddSubgroup.coe_nsmul, nsmul_eq_mul, AddSubgroup.coe_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (by simpa using hc)
  have hcard' : (Fintype.card V : (P'.restrict k F).integers) = 0 :=
    Subtype.ext (by simpa using hcard)
  rw [isWild_iff, ramificationIdx_eq_card_of_exists_reduced_additivePolynomial_pole k F V hV hgen
    hy hpole, ← map_natCast (Ideal.Quotient.mk _), hcard', map_zero]
  exact Or.inr rfl

/-- At a pole of `u` of order `m` prime to `|V|`, where `a_V (y) = u` and `V` consists of
constants, the different exponent is `(|V| - 1) (m + 1)`. No hypothesis on the residue field is
needed. -/
theorem differentExponent_eq_of_aeval_additivePolynomial_eq_of_ord_eq_neg
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (hV : ∀ c ∈ V, IsAlgebraic k c)
    (m : ℕ) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u = -(m : ℤ)) (hm : 0 < m) (hcop : (Fintype.card V).Coprime m) :
    differentExponent k F P' = (Fintype.card V - 1) * (m + 1) := by
  classical
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  let _ : Algebra.IsIntegral k k' := Algebra.IsIntegral.of_finite k k'
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  let _ : IsGalois F F' := V.isGalois_of_aeval_additivePolynomial_eq hy hgen
  have huneg : (P'.restrict k F).ord u < 0 := by
    rw [hu]
    omega
  have hgcd : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1 := by
    rwa [hu, Int.gcd_neg, Int.gcd_natCast_natCast]
  obtain ⟨z, -, hzord, hdisp⟩ :=
    exists_uniformizer_ord_aut_sub_of_aeval_additivePolynomial_eq k F V hV hgen hy huneg hgcd
  have htot :=
    isTotallyRamified_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy huneg hgcd
  -- The uniformizer `z` is integral over the valuation ring below and generates it.
  have hzint : IsIntegral (P'.restrict k F).integers z :=
    (isIntegral_iff_forall_restrict_eq_mem_integers hF' (P'.restrict k F)).mpr fun Q hQ ↦ by
      rw [eq_of_isTotallyRamified k F htot hQ]
      exact P'.mem_integers_iff_ord_nonneg.mpr (by rw [hzord]; omega)
  let x : integralClosure (P'.restrict k F).integers F' := ⟨z, hzint⟩
  have hd := differentExponent_eq_sum_ord_sub_aut_of_algebra_adjoin_eq_top k F
    (algebra_adjoin_integralClosure_eq_top_of_isTotallyRamified k F htot (z := x) hzord)
  have hcard : Fintype.card (F' ≃ₐ[F] F') = Fintype.card V := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank,
      finrank_eq_card_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy huneg hgcd]
  -- Each of the `|V| - 1` nonidentity automorphisms contributes `m + 1`.
  have hd' : (differentExponent k F P' : ℤ) = (((Fintype.card V - 1) * (m + 1) : ℕ) : ℤ) := by
    calc
      (differentExponent k F P' : ℤ) =
          ∑ σ ∈ (Finset.univ : Finset (F' ≃ₐ[F] F')).erase 1, P'.ord (z - σ z) := hd
      _ = ∑ _σ ∈ (Finset.univ : Finset (F' ≃ₐ[F] F')).erase 1, (m + 1 : ℤ) :=
          Finset.sum_congr rfl fun σ hσ ↦ by
            rw [← P'.ord_neg, neg_sub, hdisp σ (Finset.ne_of_mem_erase hσ), hu]
            ring
      _ = (((Fintype.card V - 1) * (m + 1) : ℕ) : ℤ) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
          hcard, nsmul_eq_mul]
        push_cast
        ring
  exact_mod_cast hd'

/-- **The different exponent at a reduced pole** (Stichtenoth, Proposition 3.7.10(d)): if
`a_V (y) = u`, `V` consists of constants, and some representative `u - a_V (w)` has a pole of
order `m` prime to `|V|` below `P'`, then `d(P' ∣ P) = (|V| - 1) (m + 1)`. -/
theorem differentExponent_eq_of_sub_aeval_additivePolynomial_ord_eq_neg
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (hV : ∀ c ∈ V, IsAlgebraic k c)
    (m : ℕ) {y : F'} {u w : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord (u - aeval w V.additivePolynomial) = -(m : ℤ)) (hm : 0 < m)
    (hcop : (Fintype.card V).Coprime m) :
    differentExponent k F P' = (Fintype.card V - 1) * (m + 1) := by
  -- Translating the generator by `-w` does not change the field it generates.
  have hadj : F⟮y - algebraMap F F' w⟯ = ⊤ := by
    simpa [sub_eq_add_neg] using
      (IntermediateField.adjoin_simple_add_algebraMap y (-w)).trans hgen
  refine differentExponent_eq_of_aeval_additivePolynomial_eq_of_ord_eq_neg k F V hF hF' hV m hadj
    ?_ hu hm hcop
  rw [AddSubgroup.aeval_additivePolynomial_sub, hy, aeval_algebraMap_apply, map_sub]

end TauCeti.Place
