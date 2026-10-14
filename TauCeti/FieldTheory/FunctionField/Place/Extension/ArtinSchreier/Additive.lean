/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.AdditivePolynomial
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein

import TauCeti.FieldTheory.ArtinSchreier.Additive
import TauCeti.RingTheory.Valuation.PowSubPow

/-!
# Total ramification at a reduced pole of an additive Artin–Schreier equation

Let `V` be a finite additive subgroup of `F` consisting of constants, i.e. of elements algebraic
over `k`, with additive polynomial `a_V = ∏_{c ∈ V} (X - c)`. Suppose `F' = F(y)` with
`a_V (y) = u`. Constants have order zero at every place, so at a pole of `y` each factor `y - c`
has the order of `y`, and

`ord_{P'} (a_V (y)) = |V| · ord_{P'} y`.

If `u` has a pole at the place `P` below `P'`, so does `y`, and taking orders gives
`|V| · ord_{P'} y = e(P' ∣ P) · ord_P u`. When `ord_P u` is prime to `|V|`, this makes `|V|`
divide `e(P' ∣ P)`. The equation bounds `[F' : F]` by `|V|`, and the fundamental inequality
bounds `e(P' ∣ P)` by `[F' : F]`. Hence `[F' : F] = e(P' ∣ P) = |V|`: the place is totally
ramified and the degree is proved, not assumed.

Additivity of `a_V` turns `y - w`, for `w ∈ F`, into a root of `a_V - (u - a_V (w))`, so the same
holds when only some representative `u - a_V (w)` has a pole of order prime to `|V|`. In
characteristic `p`, `|V|` is a power of `p`, so the condition is that the pole order is prime to
`p`: this is the totally ramified case of Stichtenoth's Proposition 3.7.10(d), with the reduced
representative supplied as input. For `V` the prime field, `a_V = X ^ p - X` and this is the
Artin–Schreier case of `TauCeti/FieldTheory/FunctionField/Place/Extension/ArtinSchreier/Basic.lean`.

At such a pole the Bezout identity `|V| α + ord_P u · β = 1` gives a uniformizer
`z = y ^ β · t ^ α`, with `t` a uniformizer of `P`, which generates `F' / F`. A nonidentity
automorphism translates `y` by a nonzero constant `c ∈ V`, and `|V| = 0` in `F` forces `β ≠ 0` in
`F'`, so the displacement `σ z - z = ((y + c) ^ β - y ^ β) · t ^ α` has order
`ord z - ord y = 1 - ord_P u`. These displacements compute the different exponent of the
extension.

## Main results

* `TauCeti.Place.ord_aeval_additivePolynomial_of_ord_neg`: `ord (a_V (y)) = |V| · ord y` at a
  pole of `y`; `TauCeti.Place.ord_aeval_additivePolynomial_neg_iff`: `a_V (y)` has a pole exactly
  where `y` has one.
* `TauCeti.Place.finrank_eq_card_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one` and
  `TauCeti.Place.isTotallyRamified_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one`: at a pole of
  `u` of order prime to `|V|`, `[F' : F] = |V|` and the place is totally ramified.
* `TauCeti.Place.isTotallyRamified_of_exists_reduced_additivePolynomial_pole`: the same for a
  supplied representative `u - a_V (w)`.
* `TauCeti.Place.exists_uniformizer_ord_aut_sub_of_aeval_additivePolynomial_eq`: the Bezout
  uniformizer `y ^ β · t ^ α` generates `F' / F`, and its displacement by every nonidentity
  automorphism has order `1 - ord_P u`.

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
variable (k F) [Algebra.IsIntegral F F'] {P' : Place k' F'}

/-- At a pole of `y`, subtracting a constant does not change the order. -/
private theorem ord_sub_algebraMap_of_ord_neg {c : F} (hc : IsAlgebraic k c) {y : F'}
    (hy : P'.ord y < 0) : P'.ord (y - algebraMap F F' c) = P'.ord y := by
  rcases eq_or_ne c 0 with rfl | h0
  · rw [map_zero, sub_zero]
  have hc' : P'.ord (algebraMap F F' c) = 0 := by
    rw [ord_algebraMap_restrict k F P', ord_eq_zero_of_isAlgebraic _ hc, mul_zero]
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  rw [sub_eq_add_neg, P'.ord_add_eq_min_of_ord_ne hy0
    (neg_ne_zero.mpr ((map_ne_zero_iff _ (algebraMap F F').injective).mpr h0))
    (by rw [ord_neg, hc']; exact hy.ne), ord_neg, hc', min_eq_left hy.le]

variable (V : AddSubgroup F) [Fintype V]

/-- **The order of `a_V (y)` at a pole of `y`.** If `V` consists of constants, then
`ord_{P'} (a_V (y)) = |V| · ord_{P'} y` whenever `ord_{P'} y < 0`. -/
theorem ord_aeval_additivePolynomial_of_ord_neg (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'}
    (hy : P'.ord y < 0) :
    P'.ord (aeval y V.additivePolynomial) = Fintype.card V * P'.ord y := by
  rw [AddSubgroup.aeval_additivePolynomial, P'.ord_prod _ fun c _ ↦ ?_]
  · simp [ord_sub_algebraMap_of_ord_neg k F (hV _ (Subtype.prop _)) hy]
  intro h
  have := ord_sub_algebraMap_of_ord_neg k F (hV c c.2) hy
  rw [h, ord_zero] at this
  exact hy.ne this.symm

/-- If `V` consists of constants, then `a_V (y)` has a pole exactly where `y` has one. -/
theorem ord_aeval_additivePolynomial_neg_iff (hV : ∀ c ∈ V, IsAlgebraic k c) (y : F') :
    P'.ord (aeval y V.additivePolynomial) < 0 ↔ P'.ord y < 0 := by
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · by_contra! hnonneg
    rw [← mem_integers_iff_ord_nonneg] at hnonneg
    have hmem : aeval y V.additivePolynomial ∈ P'.integers := by
      rw [AddSubgroup.aeval_additivePolynomial]
      refine prod_mem fun c _ ↦ sub_mem hnonneg ?_
      rw [mem_integers_iff_ord_nonneg, ord_algebraMap_restrict k F P',
        ord_eq_zero_of_isAlgebraic _ (hV c c.2), mul_zero]
    rw [mem_integers_iff_ord_nonneg] at hmem
    omega
  · rw [ord_aeval_additivePolynomial_of_ord_neg k F V hV hy]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast Fintype.card_pos) hy

/-- Orders in `a_V (y) = u` at a pole of `u`: `|V| · ord_{P'} y = e(P' ∣ P) · ord_P u`. -/
theorem natCast_card_mul_ord_eq_ramificationIdx_mul_ord_of_aeval_additivePolynomial_eq
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F}
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0) :
    (Fintype.card V : ℤ) * P'.ord y = ramificationIdx F P' * (P'.restrict k F).ord u := by
  have hneg : P'.ord (aeval y V.additivePolynomial) < 0 := by
    rw [hy, ord_algebraMap_restrict k F P']
    exact mul_neg_of_pos_of_neg (by exact_mod_cast ramificationIdx_pos F P') hu
  rw [← ord_aeval_additivePolynomial_of_ord_neg k F V hV
    ((ord_aeval_additivePolynomial_neg_iff k F V hV y).mp hneg), hy,
    ord_algebraMap_restrict k F P']

private theorem finrank_eq_card_and_ramificationIdx_eq_card_of_aeval_additivePolynomial_eq
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    Module.finrank F F' = Fintype.card V ∧ ramificationIdx F P' = Fintype.card V := by
  have hint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hfr : Module.finrank F F' = (minpoly F y).natDegree := by
    rw [← IntermediateField.finrank_top', ← hgen, IntermediateField.adjoin.finrank hint]
  have hle : Module.finrank F F' ≤ Fintype.card V := by
    rw [hfr, ← V.natDegree_additivePolynomial_sub_C u]
    exact natDegree_le_natDegree (minpoly.min F y (V.monic_additivePolynomial_sub_C u)
      (by rw [map_sub, hy, aeval_C, sub_self]))
  have hkey :=
    natCast_card_mul_ord_eq_ramificationIdx_mul_ord_of_aeval_additivePolynomial_eq k F V hV hy hu
  have hdvd : (Fintype.card V : ℤ) ∣ (ramificationIdx F P' : ℤ) :=
    Int.dvd_of_dvd_mul_left_of_gcd_one ⟨P'.ord y, hkey.symm⟩ hcop
  have hlow : Fintype.card V ≤ ramificationIdx F P' :=
    Nat.le_of_dvd (ramificationIdx_pos F P') (Int.natCast_dvd_natCast.mp hdvd)
  have hfin : FiniteDimensional F F' := FiniteDimensional.of_finrank_pos (by
    rw [hfr]
    exact minpoly.natDegree_pos hint)
  have he : ramificationIdx F P' ≤ Module.finrank F F' := ramificationIdx_le_finrank F P'
  omega

/-- A generator with `a_V (y) = u` has degree `|V|` if `u` has a pole of order prime to `|V|`
and `V` consists of constants. -/
theorem finrank_eq_card_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    Module.finrank F F' = Fintype.card V :=
  (finrank_eq_card_and_ramificationIdx_eq_card_of_aeval_additivePolynomial_eq k F V hV hgen hy hu
    hcop).1

/-- A pole of `u` of order prime to `|V|` has ramification index `|V|` in `F(y) / F`. -/
theorem ramificationIdx_eq_card_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    ramificationIdx F P' = Fintype.card V :=
  (finrank_eq_card_and_ramificationIdx_eq_card_of_aeval_additivePolynomial_eq k F V hV hgen hy hu
    hcop).2

/-- A pole of `u` of order prime to `|V|` is totally ramified in `F(y) / F`. -/
theorem isTotallyRamified_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    IsTotallyRamified F P' := by
  have h :=
    finrank_eq_card_and_ramificationIdx_eq_card_of_aeval_additivePolynomial_eq k F V hV hgen hy hu
      hcop
  rw [isTotallyRamified_iff, h.1, h.2]

/-- At a pole of `u` of order prime to `|V|`, the generator `y` has the order of `u`:
`ord_{P'} y = ord_P u`. -/
theorem ord_eq_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    P'.ord y = (P'.restrict k F).ord u := by
  have hkey :=
    natCast_card_mul_ord_eq_ramificationIdx_mul_ord_of_aeval_additivePolynomial_eq k F V hV hy hu
  rw [ramificationIdx_eq_card_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy hu
    hcop] at hkey
  exact mul_left_cancel₀ (by exact_mod_cast Fintype.card_ne_zero) hkey

/-- Translating the generator by `-w` turns a pole of the representative `u - a_V (w)` into the
pole case of `finrank_eq_card_and_ramificationIdx_eq_card_of_aeval_additivePolynomial_eq`. -/
private theorem finrank_eq_card_and_ramificationIdx_eq_card_of_exists_reduced_pole
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) ((P'.restrict k F).ord (u - aeval w V.additivePolynomial)) = 1) :
    Module.finrank F F' = Fintype.card V ∧ ramificationIdx F P' = Fintype.card V := by
  obtain ⟨w, hwneg, hwcop⟩ := hpole
  -- Translating the generator by `-w` does not change the field it generates.
  have hadj : F⟮y - algebraMap F F' w⟯ = ⊤ := by
    simpa [sub_eq_add_neg] using
      (IntermediateField.adjoin_simple_add_algebraMap y (-w)).trans hgen
  refine finrank_eq_card_and_ramificationIdx_eq_card_of_aeval_additivePolynomial_eq k F V hV hadj
    ?_ hwneg hwcop
  rw [AddSubgroup.aeval_additivePolynomial_sub, hy, aeval_algebraMap_apply, map_sub]

/-- **Total ramification at a reduced pole** (Stichtenoth, Proposition 3.7.10(d)): if `V`
consists of constants and some representative `u - a_V (w)` has a pole of order prime to `|V|`
below `P'`, then `P'` is totally ramified over that place. No hypothesis on the residue field is
needed. -/
theorem isTotallyRamified_of_exists_reduced_additivePolynomial_pole
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) ((P'.restrict k F).ord (u - aeval w V.additivePolynomial)) = 1) :
    IsTotallyRamified F P' := by
  have h := finrank_eq_card_and_ramificationIdx_eq_card_of_exists_reduced_pole k F V hV hgen hy
    hpole
  rw [isTotallyRamified_iff, h.1, h.2]

/-- A reduced pole of order prime to `|V|` forces `[F(y) : F] = |V|`. -/
theorem finrank_eq_card_of_exists_reduced_additivePolynomial_pole
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) ((P'.restrict k F).ord (u - aeval w V.additivePolynomial)) = 1) :
    Module.finrank F F' = Fintype.card V :=
  (finrank_eq_card_and_ramificationIdx_eq_card_of_exists_reduced_pole k F V hV hgen hy hpole).1

/-- A reduced pole of order prime to `|V|` has ramification index `|V|`. -/
theorem ramificationIdx_eq_card_of_exists_reduced_additivePolynomial_pole
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hpole : ∃ w : F, (P'.restrict k F).ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) ((P'.restrict k F).ord (u - aeval w V.additivePolynomial)) = 1) :
    ramificationIdx F P' = Fintype.card V :=
  (finrank_eq_card_and_ramificationIdx_eq_card_of_exists_reduced_pole k F V hV hgen hy hpole).2

/-- At a pole of `u` of order prime to `|V|`, where `V` consists of constants and `a_V (y) = u`
generates `F' / F`, a Bezout combination `z = y ^ β · t ^ α` of the generator and a uniformizer `t`
of the place below, with `|V| α + ord_P u · β = 1`, is a uniformizer at `P'` that still generates
`F' / F`. -/
private theorem exists_eq_zpow_mul_adjoin_eq_top_ord_eq_one_of_aeval_additivePolynomial_eq
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    ∃ (z : F') (t : F) (α β : ℤ),
      (P'.restrict k F).ord t = 1 ∧
      (Fintype.card V : ℤ) * α + (P'.restrict k F).ord u * β = 1 ∧
      z = y ^ β * algebraMap F F' t ^ α ∧ F⟮z⟯ = ⊤ ∧ P'.ord z = 1 := by
  have := V.finiteDimensional_of_aeval_additivePolynomial_eq hy hgen
  set α := Int.gcdA (Fintype.card V) ((P'.restrict k F).ord u)
  set β := Int.gcdB (Fintype.card V) ((P'.restrict k F).ord u)
  have hab : (Fintype.card V : ℤ) * α + (P'.restrict k F).ord u * β = 1 := by
    rw [← Int.gcd_eq_gcd_ab, hcop, Nat.cast_one]
  obtain ⟨t, ht0, ht⟩ := (P'.restrict k F).exists_ne_zero_ord_eq 1
  have hyo := ord_eq_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy hu hcop
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [P'.ord_zero] at hyo
    omega
  have ht0' : algebraMap F F' t ≠ 0 := (_root_.map_ne_zero _).mpr ht0
  have hzo : P'.ord (y ^ β * algebraMap F F' t ^ α) = 1 := by
    rw [P'.ord_mul (zpow_ne_zero _ hy0) (zpow_ne_zero _ ht0'), P'.ord_zpow, P'.ord_zpow, hyo,
      ord_algebraMap_restrict k F P', ht,
      ramificationIdx_eq_card_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy hu
        hcop]
    linarith
  exact ⟨_, t, α, β, ht, hab, rfl, adjoin_eq_top_of_isTotallyRamified_of_ord_eq_one F
    (isTotallyRamified_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy hu hcop)
    hzo, hzo⟩

/-- **A generating uniformizer with constant Galois displacements** at a pole of `u` of order
prime to `|V|`, where `V` consists of constants and `a_V (y) = u` generates `F' / F`: some
uniformizer `z` at `P'` generates `F' / F`, and `ord_{P'} (σ z - z) = 1 - ord_P u` for every
nonidentity `F`-automorphism `σ` of `F'`. No hypothesis on the residue field is needed. -/
theorem exists_uniformizer_ord_aut_sub_of_aeval_additivePolynomial_eq
    (hV : ∀ c ∈ V, IsAlgebraic k c) {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd (Fintype.card V) ((P'.restrict k F).ord u) = 1) :
    ∃ z : F', F⟮z⟯ = ⊤ ∧ P'.ord z = 1 ∧
      ∀ σ : Gal(F'/F), σ ≠ 1 → P'.ord (σ z - z) = 1 - (P'.restrict k F).ord u := by
  obtain ⟨z, t, α, β, -, hab, hz, hzg, hzo⟩ :=
    exists_eq_zpow_mul_adjoin_eq_top_ord_eq_one_of_aeval_additivePolynomial_eq
      k F V hV hgen hy hu hcop
  have hyo := ord_eq_of_aeval_additivePolynomial_eq_of_gcd_ord_eq_one k F V hV hgen hy hu hcop
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [P'.ord_zero] at hyo
    omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzo
  refine ⟨z, hzg, hzo, fun σ hσ ↦ ?_⟩
  -- A nonidentity automorphism translates `y` by a nonzero constant `c ∈ V`.
  set c : V := (V.artinSchreierTranslationHom hy σ).toAdd with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hσ
    apply V.artinSchreierTranslationHom_injective hy hgen
    apply Multiplicative.toAdd.injective
    simpa [c] using h
  have hcF : (c : F) ≠ 0 := by simpa using hc0
  have hcF' : algebraMap F F' c ≠ 0 := (_root_.map_ne_zero _).mpr hcF
  have hcval : P'.valuation (algebraMap F F' c) = 1 :=
    P'.valuation_eq_one_of_isAlgebraic (((hV c c.2).algebraMap (A := F')).tower_top k') hcF'
  -- `|V|` vanishes in `F`, so the Bezout identity forces `β ≠ 0` in `F'`.
  have hcard : (Fintype.card V : F) = 0 := by
    have h := congrArg ((↑) : V → F) (card_nsmul_eq_zero (x := c))
    rw [AddSubgroup.coe_nsmul, nsmul_eq_mul, AddSubgroup.coe_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hcF
  have hbcast : (β : F') ≠ 0 := by
    have hq : (Fintype.card V : F') = 0 := by rw [← map_natCast (algebraMap F F'), hcard, map_zero]
    have h := congrArg (fun a : ℤ ↦ (a : F')) hab
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one, hq, zero_mul,
      zero_add] at h
    intro hb
    simp [hb] at h
  have hbval : P'.valuation (β : F') = 1 :=
    P'.valuation_eq_one_of_isAlgebraic (isAlgebraic_intCast β) hbcast
  have hσz : σ z - z = (y + algebraMap F F' c) ^ β * algebraMap F F' t ^ α -
      y ^ β * algebraMap F F' t ^ α := by
    rw [hz, map_mul, map_zpow₀, map_zpow₀, AlgEquiv.commutes,
      V.aut_apply_eq_add_artinSchreierTranslationHom hy σ]
  have hygt : 1 < P'.valuation y := by
    rw [P'.valuation_eq_exp_neg_ord hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  -- Translation lowers the power of the pole `y` by one; the factor `t ^ α` is fixed.
  have hval : P'.valuation (σ z - z) = P'.valuation z / P'.valuation y := by
    rw [hσz, ← sub_mul, P'.valuation.map_mul,
      P'.valuation.map_add_zpow_sub_zpow (hcval.trans_lt hygt) β hbval, hcval, mul_one, hz,
      P'.valuation.map_mul, map_zpow₀, map_zpow₀, zpow_sub₀ (P'.valuation.ne_zero_iff.mpr hy0),
      zpow_one, div_mul_eq_mul_div]
  calc
    P'.ord (σ z - z) = P'.ord z - P'.ord y := by
      rw [P'.ord_def, hval, WithZero.log_div (P'.valuation.ne_zero_iff.mpr hz0)
        (P'.valuation.ne_zero_iff.mpr hy0), P'.ord_def, P'.ord_def]
      ring
    _ = 1 - (P'.restrict k F).ord u := by rw [hzo, hyo]

end TauCeti.Place
