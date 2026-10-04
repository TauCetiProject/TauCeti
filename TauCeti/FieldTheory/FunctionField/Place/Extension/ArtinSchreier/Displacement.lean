/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.ArtinSchreier.Basic

import TauCeti.FieldTheory.ArtinSchreier.Basic
import TauCeti.RingTheory.Valuation.PowSubPow

/-!
# Galois displacements at a reduced Artin--Schreier pole

Let `F' = F(y)` with `y ^ p - y = u` in characteristic `p`, and suppose `u` has a pole
of order `m` prime to `p`. There is a uniformizer `z` at every place above that pole
which generates `F' / F` and satisfies

`ord (σ z - z) = m + 1` for every nonidentity `F`-automorphism `σ`.

This is the local calculation used to evaluate the derivative of the uniformizer's minimal
polynomial, and hence the different exponent of an Artin--Schreier extension. The uniformizer
is the Bezout product supplied by
`TauCeti.Place.exists_eq_zpow_mul_adjoin_eq_top_ord_eq_one_of_pow_sub_self_eq_of_gcd_ord_eq_one`;
its integer exponent on `y` is nonzero in the prime field. Nonidentity automorphisms translate
`y` by a nonzero prime-field constant, so the valuation of the displacement follows from
`Valuation.map_add_zpow_sub_zpow`. Both positive and negative Bezout exponents are allowed.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

open scoped IntermediateField

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

variable (k F)

/-- At a prime-to-characteristic Artin--Schreier pole, there is a generating uniformizer
whose displacement by every nonidentity automorphism has order one greater than the pole
order. No hypothesis on perfection of the residue field is needed. -/
theorem exists_uniformizer_ord_aut_sub_of_artinSchreier_pole
    {P' : Place k' F'} (p : ℕ) [Fact p.Prime] [CharP F p] {y : F'} {u : F}
    (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
    (hu : (P'.restrict k F).ord u < 0)
    (hcop : Int.gcd p ((P'.restrict k F).ord u) = 1) :
    ∃ z : F', F⟮z⟯ = ⊤ ∧ P'.ord z = 1 ∧
      ∀ σ : Gal(F'/F), σ ≠ 1 → P'.ord (σ z - z) = 1 - (P'.restrict k F).ord u := by
  obtain ⟨z, t, α, β, -, hab, hz, hzg, hzo⟩ :=
    exists_eq_zpow_mul_adjoin_eq_top_ord_eq_one_of_pow_sub_self_eq_of_gcd_ord_eq_one
      k F (Fact.out : p.Prime).one_lt hgen hy hu hcop
  have hyo := ord_eq_of_pow_sub_self_eq_of_gcd_ord_eq_one
    k F (Fact.out : p.Prime).one_lt hgen hy hu hcop
  have : CharP F' p := charP_of_injective_algebraMap (algebraMap F F').injective p
  -- The Bezout relation forces the exponent β to be nonzero in characteristic p.
  have hbcast : (β : F') ≠ 0 := by
    have h := congrArg (fun a : ℤ ↦ (a : F')) hab
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      CharP.cast_eq_zero, zero_mul, zero_add] at h
    intro hb
    simp [hb] at h
  have hbval : P'.valuation (β : F') = 1 :=
    P'.valuation_eq_one_of_isAlgebraic (isAlgebraic_intCast β) hbcast
  refine ⟨z, hzg, hzo, ?_⟩
  intro σ hσ
  -- Nonidentity automorphisms translate the root by a nonzero prime-field constant.
  let c : ZMod p := (ArtinSchreier.translationHom hy σ).toAdd
  have hc0 : c ≠ 0 := by
    intro hc
    apply hσ
    apply ArtinSchreier.translationHom_injective hy hgen
    apply Multiplicative.toAdd.injective
    simpa [c] using hc
  have hcF : (ZMod.cast c : F') ≠ 0 := by
    simpa using (ZMod.castHom (m := p) dvd_rfl F').injective.ne hc0
  have hcval : P'.valuation (ZMod.cast c : F') = 1 := by
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective c
    rw [← hn, ZMod.cast_intCast dvd_rfl] at hcF ⊢
    exact P'.valuation_eq_one_of_isAlgebraic (isAlgebraic_intCast n) hcF
  have hσz : σ z - z =
      (y + ZMod.cast c) ^ β * (algebraMap F F' t) ^ α - y ^ β * (algebraMap F F' t) ^ α := by
    rw [hz, map_mul, map_zpow₀, map_zpow₀, AlgEquiv.commutes,
      ArtinSchreier.aut_apply_eq_add_translationHom hy σ]
  have hy0 : y ≠ 0 := by intro h; simp [h] at hyo; omega
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzo
  have hygt : 1 < P'.valuation y := by
    rw [P'.valuation_eq_exp_neg_ord hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  -- Translation lowers the pole-generator power by one; the remaining factor is fixed.
  have hval : P'.valuation (σ z - z) = P'.valuation z / P'.valuation y := by
    rw [hσz, ← sub_mul, P'.valuation.map_mul,
      P'.valuation.map_add_zpow_sub_zpow (hcval.trans_lt hygt) β hbval,
      hcval, mul_one, hz, P'.valuation.map_mul,
      map_zpow₀, map_zpow₀, zpow_sub₀ (P'.valuation.ne_zero_iff.mpr hy0), zpow_one]
    rw [div_mul_eq_mul_div]
  calc
    P'.ord (σ z - z) = P'.ord z - P'.ord y := by
      rw [P'.ord_def, hval, WithZero.log_div (P'.valuation.ne_zero_iff.mpr hz0)
        (P'.valuation.ne_zero_iff.mpr hy0), P'.ord_def, P'.ord_def]
      ring
    _ = 1 - (P'.restrict k F).ord u := by rw [hzo, hyo]

end TauCeti.Place
