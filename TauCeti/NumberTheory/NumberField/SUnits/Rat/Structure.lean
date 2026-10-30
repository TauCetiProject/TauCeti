/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.NumberTheory.SmoothNumbers
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

import TauCeti.NumberTheory.NumberField.SUnits.Rat.Basic

/-!
# Rational `S`-units

For a finite set `S` of natural numbers, the rational `S`-units are Mathlib's `Set.unit S' ℚ`,
where `S'` is the set of height-one primes `v` of `𝓞 ℚ` whose rational prime
`Rat.HeightOneSpectrum.primesEquiv v` lies in `S`. Thus `x ∈ U_S` exactly when `x` is a unit at
every prime outside `S`. This file makes the group explicit.

## Main results

* `TauCeti.mem_sUnits_rat_iff_num_den`: `x ∈ U_S` iff `|num x|` and `den x` have all their prime
  factors in `S`.
* `TauCeti.mem_sUnits_rat_iff_eq_sign_mul_prod`: if `S` consists of primes, `x ∈ U_S` iff
  `x = ε ∏_{p ∈ S} p ^ z_p` for a sign `ε` and integer exponents `z`.
* `TauCeti.sUnitsRatMulEquiv`: if `S` consists of primes,
  `x ↦ (sign x, (v_p(x))_{p ∈ S})` is an isomorphism `U_S ≃* ℤˣ × Multiplicative (S → ℤ)`.
* `TauCeti.sUnits_rat_fg` and `TauCeti.finrank_sUnits_rat`: `U_S` is finitely generated, and
  it has rank `|S|` when `S` consists of primes.
* `TauCeti.mulHeight₁_sUnits_rat`: the height of `x ∈ U_S` is
  `max (∏_{p ∈ S} p ^ max(v_p(x), 0)) (∏_{p ∈ S} p ^ max(-v_p(x), 0))`.

The sign, product and height descriptions need `S` to consist of primes: for `S = {4}` the set
`S'` is empty, so `U_S = {±1}`, while `4 = ∏_{p ∈ S} p ^ 1`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes for the Leiden/Mastermath course,
  2019 edition, Chapter 5, Theorem 5.17 and the rational `S`-units it concerns.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

open Rat.HeightOneSpectrum

/-- A nonzero rational number is an `S`-unit exactly when its `p`-adic valuation vanishes at
every prime `p ∉ S`. Here `S` is an arbitrary set of natural numbers. -/
theorem mem_sUnits_rat_iff_forall_padicValRat_eq_zero {S : Set ℕ} {x : ℚˣ} :
    x ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ ↔
      ∀ p : ℕ, p.Prime → p ∉ S → padicValRat p x = 0 := by
  rw [Set.mem_unit_iff]
  refine ⟨fun h p hp hpS ↦ ?_, fun h v hv ↦ ?_⟩
  · obtain ⟨v, hv⟩ := (primesEquiv (R := 𝓞 ℚ)).surjective (⟨p, hp⟩ : Nat.Primes)
    have := h v (by simpa [hv] using hpS)
    rwa [valuation_eq_one_iff_padicValRat_eq_zero _ x.ne_zero, hv] at this
  · rw [valuation_eq_one_iff_padicValRat_eq_zero _ x.ne_zero]
    exact h _ (primesEquiv v).2 hv

variable {S : Finset ℕ}

/-- **Rational `S`-units through numerator and denominator.** A rational number is an `S`-unit
exactly when the absolute value of its numerator and its denominator are `S`-factored, i.e. have
all their prime factors in `S`. -/
theorem mem_sUnits_rat_iff_num_den {x : ℚˣ} :
    x ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ ↔
      (x : ℚ).num.natAbs ∈ Nat.factoredNumbers S ∧ (x : ℚ).den ∈ Nat.factoredNumbers S := by
  have h := mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ)) (x := x)
  simp only [Finset.mem_coe] at h
  exact h.trans (forall_padicValRat_eq_zero_iff_mem_factoredNumbers x.ne_zero)

/-- Only finitely many height-one primes of `𝓞 ℚ` correspond to rational primes in a finite set
`S`, so the rational `S`-units are those of a finite set of places. -/
instance finite_setOf_primesEquiv_mem :
    Finite {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} :=
  (S.finite_toSet.preimage
    (Subtype.val_injective.comp (primesEquiv (R := 𝓞 ℚ)).injective).injOn).to_subtype

/-- **The rational `S`-units are finitely generated.** This holds for every finite set `S` of
natural numbers; only the primes in `S` contribute. -/
theorem sUnits_rat_fg :
    Group.FG (Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ) :=
  inferInstance

private theorem intCast_mem_sUnits_rat (ε : ℤˣ) :
    Units.map (Int.castRingHom ℚ).toMonoidHom ε ∈
      Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ := by
  refine (mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).2 fun p hp _ ↦ ?_
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

private theorem natCast_mem_sUnits_rat {p : ℕ} (hp : p.Prime) (hpS : p ∈ S) :
    Units.mk0 (p : ℚ) (Nat.cast_ne_zero.2 hp.ne_zero) ∈
      Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ := by
  refine (mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).2 fun q hq hqS ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  rw [Units.val_mk0, padicValRat.of_nat, Nat.cast_eq_zero]
  exact padicValNat_primes fun h ↦ hqS (h ▸ hpS)

variable (hS : ∀ p ∈ S, p.Prime)

/-- The sign and the exponents at the primes of `S` of a rational `S`-unit. -/
private noncomputable def signExponents :
    Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ →*
      ℤˣ × Multiplicative (S → ℤ) :=
  ((Units.map ((SignType.castHom : SignType →*₀ ℤ).comp signHom : ℚ →*₀ ℤ).toMonoidHom).comp
    (Subgroup.subtype _)).prod
  { toFun x := .ofAdd fun p ↦ padicValRat p ((x : ℚˣ) : ℚ)
    map_one' := by simp [Pi.zero_def]
    map_mul' x y := by
      rw [← ofAdd_add]
      congr 1
      funext p
      have : Fact (p : ℕ).Prime := ⟨hS p p.2⟩
      simp [padicValRat.mul (x : ℚˣ).ne_zero (y : ℚˣ).ne_zero] }

/-- The rational `S`-unit `ε ∏ p ^ z_p` with prescribed sign and exponents. -/
private noncomputable def ofSignExponents (w : ℤˣ × Multiplicative (S → ℤ)) :
    Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ :=
  ⟨_, intCast_mem_sUnits_rat w.1⟩ *
    ∏ p : S, ⟨_, natCast_mem_sUnits_rat (hS p p.2) p.2⟩ ^ w.2.toAdd p

private theorem coe_ofSignExponents (w : ℤˣ × Multiplicative (S → ℤ)) :
    ((ofSignExponents hS w : ℚˣ) : ℚ) = (w.1 : ℚ) * ∏ p : S, ((p : ℕ) : ℚ) ^ w.2.toAdd p := by
  simp [ofSignExponents]

private theorem coe_signExponents_fst
    (x : Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ) :
    ((signExponents hS x).1 : ℤ) = SignType.sign ((x : ℚˣ) : ℚ) := rfl

private theorem toAdd_signExponents_snd
    (x : Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ) (p : S) :
    (signExponents hS x).2.toAdd p = padicValRat p ((x : ℚˣ) : ℚ) := rfl

private theorem signExponents_ofSignExponents (w : ℤˣ × Multiplicative (S → ℤ)) :
    signExponents hS (ofSignExponents hS w) = w := by
  have hε : signExponents hS ⟨_, intCast_mem_sUnits_rat w.1⟩ = (w.1, 1) := by
    refine Prod.ext (Units.ext ?_) (Multiplicative.toAdd.injective (funext fun p ↦ ?_))
    · rw [coe_signExponents_fst]
      rcases Int.units_eq_one_or w.1 with h | h <;> simp [h]
    · rw [toAdd_signExponents_snd]
      have : Fact (p : ℕ).Prime := ⟨hS p p.2⟩
      rcases Int.units_eq_one_or w.1 with h | h <;> simp [h]
  have hp : ∀ p : S, signExponents hS ⟨_, natCast_mem_sUnits_rat (hS p p.2) p.2⟩ =
      (1, .ofAdd (Pi.single p 1)) := by
    intro p
    refine Prod.ext (Units.ext ?_) (Multiplicative.toAdd.injective (funext fun q ↦ ?_))
    · rw [coe_signExponents_fst]
      simp [(hS p p.2).pos]
    · rw [toAdd_signExponents_snd]
      have : Fact (q : ℕ).Prime := ⟨hS q q.2⟩
      have : Fact (p : ℕ).Prime := ⟨hS p p.2⟩
      rcases eq_or_ne q p with rfl | hqp
      · simp [padicValRat.self (hS q q.2).one_lt]
      · simp only [Units.val_mk0, padicValRat.of_nat, toAdd_ofAdd, Pi.single_eq_of_ne hqp,
          Nat.cast_eq_zero]
        exact padicValNat_primes fun h ↦ hqp (Subtype.ext h)
  rw [ofSignExponents, map_mul, map_prod]
  simp only [map_zpow, hε, hp]
  refine Prod.ext (by simp [Prod.fst_prod]) ?_
  simp only [Prod.snd_mul, Prod.snd_prod, Prod.pow_snd, one_mul]
  refine Multiplicative.toAdd.injective (funext fun q ↦ ?_)
  simp [Finset.sum_apply, Pi.single_apply]

private theorem signExponents_injective : Function.Injective (signExponents hS) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  have hq : ((x : ℚˣ) : ℚ) ≠ 0 := (x : ℚˣ).ne_zero
  have hsign : SignType.sign ((x : ℚˣ) : ℚ) = 1 := by
    have := congrArg (fun w ↦ ((w.1 : ℤˣ) : ℤ)) hx
    simp only [coe_signExponents_fst, Prod.fst_one, Units.val_one] at this
    exact (by decide : ∀ s : SignType, (s : ℤ) = 1 → s = 1) _ this
  have hval : ∀ p : ℕ, p.Prime → p ∉ (∅ : Finset ℕ) → padicValRat p ((x : ℚˣ) : ℚ) = 0 := by
    intro p hp _
    by_cases hpS : p ∈ S
    · have := congrArg (fun w ↦ w.2.toAdd ⟨p, hpS⟩) hx
      simpa [toAdd_signExponents_snd] using this
    · exact (mem_sUnits_rat_iff_forall_padicValRat_eq_zero (S := (S : Set ℕ))).1 x.2 p hp hpS
  obtain ⟨hnum, hden⟩ := (forall_padicValRat_eq_zero_iff_mem_factoredNumbers hq).1 hval
  rw [Nat.factoredNumbers_empty, Set.mem_singleton_iff] at hnum hden
  have hpos : 0 < ((x : ℚˣ) : ℚ).num := Rat.num_pos.2 (sign_eq_one_iff.1 hsign)
  have hone : ((x : ℚˣ) : ℚ).num = 1 := by omega
  ext
  rw [← Rat.coe_int_num_of_den_eq_one hden, hone]
  simp

/-- **The structure of the rational `S`-units.** If `S` consists of primes, the map
`x ↦ (sign x, (v_p(x))_{p ∈ S})` is an isomorphism from the rational `S`-units to
`ℤˣ × Multiplicative (S → ℤ)`; its inverse sends `(ε, z)` to `ε ∏_{p ∈ S} p ^ z_p`
(`TauCeti.coe_sUnitsRatMulEquiv_symm_apply`). -/
noncomputable def sUnitsRatMulEquiv :
    Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ ≃*
      ℤˣ × Multiplicative (S → ℤ) :=
  MulEquiv.ofBijective (signExponents hS)
    ⟨signExponents_injective hS, fun w ↦ ⟨_, signExponents_ofSignExponents hS w⟩⟩

/-- The first component of `sUnitsRatMulEquiv` is the sign. -/
@[simp]
theorem coe_sUnitsRatMulEquiv_apply_fst
    (x : Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ) :
    ((sUnitsRatMulEquiv hS x).1 : ℤ) = SignType.sign ((x : ℚˣ) : ℚ) :=
  coe_signExponents_fst hS x

/-- The second component of `sUnitsRatMulEquiv` records the `p`-adic valuations at `p ∈ S`. -/
@[simp]
theorem toAdd_sUnitsRatMulEquiv_apply_snd
    (x : Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ) (p : S) :
    (sUnitsRatMulEquiv hS x).2.toAdd p = padicValRat p ((x : ℚˣ) : ℚ) :=
  toAdd_signExponents_snd hS x p

/-- The inverse of `sUnitsRatMulEquiv` sends `(ε, z)` to `ε ∏_{p ∈ S} p ^ z_p`. -/
@[simp]
theorem coe_sUnitsRatMulEquiv_symm_apply (w : ℤˣ × Multiplicative (S → ℤ)) :
    (((sUnitsRatMulEquiv hS).symm w : ℚˣ) : ℚ) =
      (w.1 : ℚ) * ∏ p : S, ((p : ℕ) : ℚ) ^ w.2.toAdd p := by
  have h : (sUnitsRatMulEquiv hS).symm w = ofSignExponents hS w :=
    (sUnitsRatMulEquiv hS).symm_apply_eq.2 (signExponents_ofSignExponents hS w).symm
  rw [h, coe_ofSignExponents]

include hS in
/-- **Rational `S`-units as signed products of prime powers.** If `S` consists of primes, a
rational number is an `S`-unit exactly when it is `ε ∏_{p ∈ S} p ^ z_p` for a sign `ε ∈ ℤˣ`
and integer exponents `z`. -/
theorem mem_sUnits_rat_iff_eq_sign_mul_prod {x : ℚˣ} :
    x ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ ↔
      ∃ (ε : ℤˣ) (z : S → ℤ), (x : ℚ) = ε * ∏ p : S, ((p : ℕ) : ℚ) ^ z p := by
  refine ⟨fun hx ↦ ?_, fun ⟨ε, z, hx⟩ ↦ ?_⟩
  · have h := coe_sUnitsRatMulEquiv_symm_apply hS (sUnitsRatMulEquiv hS ⟨x, hx⟩)
    rw [MulEquiv.symm_apply_apply] at h
    exact ⟨_, _, h⟩
  · have : x = ofSignExponents hS (ε, .ofAdd z) :=
      Units.ext (by rw [coe_ofSignExponents]; simpa using hx)
    exact this ▸ (ofSignExponents hS _).2

include hS in
/-- **The rank of the rational `S`-units.** If `S` consists of primes, the group of rational
`S`-units has rank `|S|`. -/
theorem finrank_sUnits_rat :
    Module.finrank ℤ (Additive (Set.unit {v : HeightOneSpectrum (𝓞 ℚ) |
      (primesEquiv v : ℕ) ∈ S} ℚ)) = S.card := by
  rw [NumberField.SUnit.finrank_unit_rat, ← Nat.card_eq_finsetCard]
  calc Nat.card {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S}
      = Nat.card {p : Nat.Primes // (p : ℕ) ∈ S} :=
        Nat.card_congr (primesEquiv.subtypeEquiv fun _ ↦ Iff.rfl)
    _ = Nat.card S :=
        Nat.card_congr ⟨fun p ↦ ⟨p.1, p.2⟩, fun p ↦ ⟨⟨p, hS p p.2⟩, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

include hS in
/-- **The height of a rational `S`-unit.** If `S` consists of primes and `x` is an `S`-unit,
then `H(x) = max (∏_{p ∈ S} p ^ max(v_p(x), 0)) (∏_{p ∈ S} p ^ max(-v_p(x), 0))`: the two
products are the absolute value of the numerator and the denominator of `x`. -/
theorem mulHeight₁_sUnits_rat {x : ℚˣ}
    (hx : x ∈ Set.unit {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) ∈ S} ℚ) :
    Height.mulHeight₁ (x : ℚ) =
      max (∏ p ∈ S, (p : ℝ) ^ (padicValRat p (x : ℚ)).toNat)
        (∏ p ∈ S, (p : ℝ) ^ (-padicValRat p (x : ℚ)).toNat) := by
  obtain ⟨hnum, hden⟩ := mem_sUnits_rat_iff_num_den.1 hx
  -- at each prime, one of the numerator and the denominator has valuation zero
  have hv : ∀ p ∈ S, (padicValRat p (x : ℚ)).toNat = padicValNat p (x : ℚ).num.natAbs ∧
      (-padicValRat p (x : ℚ)).toNat = padicValNat p (x : ℚ).den := by
    intro p hp
    rw [padicValRat_def]
    rcases Rat.num_or_den_zero_padicVal (x : ℚ) (hS p hp) with h | h <;>
      simp only [padicValInt] at h ⊢ <;> omega
  have hnum' : ((x : ℚ).num.natAbs : ℝ) = ∏ p ∈ S, (p : ℝ) ^ (padicValRat p (x : ℚ)).toNat := by
    conv_lhs => rw [← prod_pow_padicValNat_eq_self_of_mem_factoredNumbers hS hnum]
    push_cast
    exact Finset.prod_congr rfl fun p hp ↦ by rw [(hv p hp).1]
  have hden' : ((x : ℚ).den : ℝ) = ∏ p ∈ S, (p : ℝ) ^ (-padicValRat p (x : ℚ)).toNat := by
    conv_lhs => rw [← prod_pow_padicValNat_eq_self_of_mem_factoredNumbers hS hden]
    push_cast
    exact Finset.prod_congr rfl fun p hp ↦ by rw [(hv p hp).2]
  rw [Rat.mulHeight₁_eq_max, Nat.cast_max, hnum', hden']

end TauCeti
