/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.RingTheory.DiscreteValuationRing.Basic
-- Proof-only: the valuation of a valuative extension extends that of the base.
import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# The normalized valuation of a natural number in a local field

Let `K` be a nonarchimedean local field. The image of a natural number `n` under the canonical
map `ℕ → K` lies in the ring of integers `𝒪[K]`, so its normalized valuation is a natural
number as soon as it is defined, that is as soon as `(n : K) ≠ 0`. This file introduces that
natural number,

`natCastValuation K n hn : ℕ`,

and its basic API.

It is the quantity that measures how far `n` is from being invertible in `𝒪[K]`: it vanishes
exactly when `(n : 𝒪[K])` is a unit, equivalently when the residue characteristic of `K` does
not divide `n`. In particular it vanishes identically when `K` has positive characteristic, so
it carries information only in mixed characteristic; there its value at the residue
characteristic is the absolute ramification index of `K`.

## Main definitions

* `TauCeti.natCastValuation`: the normalized valuation of the image of a natural number in a
  nonarchimedean local field, as a natural number.

## Main results

* `TauCeti.natCast_ne_zero_of_coprime_ringChar`: a natural number prime to the residue
  characteristic is nonzero in `K`.
* `TauCeti.natCast_ne_zero_of_residueField_natCast_ne_zero`: a natural number nonzero in the
  residue field is nonzero in every nontrivial `K`-algebra.
* `TauCeti.valuation_natCast_eq_one_of_residueField_natCast_ne_zero`: such a natural number has
  valuation `1` in every valuative extension of `K`.
* `TauCeti.normalizedValuation_natCast`: the characteristic equation, which also records that
  the value is nonnegative.
* `TauCeti.toAdd_normalizedValuation_natCast` and `TauCeti.valuation_natCast_eq_pow`: the
  characteristic equation in the additive and multiplicative valuation conventions.
* `TauCeti.natCastValuation_eq_zero_iff`: the vanishing criterion, in terms of invertibility in
  `𝒪[K]`.
* `TauCeti.natCastValuation_eq_zero_iff_not_dvd`: the vanishing criterion read off the residue
  characteristic.
* `TauCeti.natCastValuation_ne_zero_iff_ringChar_eq`: at a prime, the invariant is nonzero
  exactly when that prime is the residue characteristic.
* `TauCeti.natCastValuation_eq_zero_of_ringChar_ne_zero`: in equal characteristic the invariant
  is identically zero.
* `TauCeti.natCastValuation_eq_padicValNat_mul`: `v_K(n) = v_p(n) v_K(p)` for the residue
  characteristic `p`.
* `TauCeti.natCastValuation_le_div_log_mul_log`: the logarithmic bound
  `v_K(n) ≤ v_K(p) / log p * log n`.
* `TauCeti.natCastValuation_lt_sub_one_mul_natCastValuation_ringChar_add_one`: the depth
  condition of the deep-unit power lemmas holds at depth `v_K(p) + 1` for every prime.
* `TauCeti.normalizedAbsoluteValue_natCast`: the normalized absolute value of `n` is
  `q ^ (-natCastValuation K n hn)`.
* `TauCeti.IsDiscreteValuationRing.addVal_natCast`: the same valuation in the
  discrete-valuation-ring convention.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

open scoped NNRat WithZero

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

/-- A natural number prime to the residue characteristic is nonzero in the field. -/
theorem natCast_ne_zero_of_coprime_ringChar {n : ℕ} (hn : n.Coprime (ringChar 𝓀[K])) :
    (n : K) ≠ 0 :=
  natCast_ne_zero_of_isUnit <| IsLocalRing.isUnit_natCast_iff_not_dvd.2 fun h ↦
    CharP.ringChar_ne_one (hn.symm.eq_one_of_dvd h)

/-- A natural number that is nonzero in the residue field is nonzero in every nontrivial algebra
over the field, such as an algebraic closure: a prime different from the residue characteristic
stays invertible there. -/
theorem natCast_ne_zero_of_residueField_natCast_ne_zero {A : Type*} [Semiring A] [Nontrivial A]
    [Algebra K A] {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0) : (n : A) ≠ 0 :=
  IsUnit.natCast_ne_zero_of_algebra (K := K) (natCast_ne_zero_of_isUnit
    ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rwa [map_natCast]))).isUnit

/-- A natural number that is nonzero in the residue field of `K` has valuation `1` in every
valuative extension `L` of `K`, being a unit of `𝒪[K]`. So it lies outside the maximal ideal of
the valuation ring of `L`. -/
theorem valuation_natCast_eq_one_of_residueField_natCast_ne_zero {L : Type*} [Field L]
    [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0) :
    valuation L (n : L) = 1 := by
  have hu : IsUnit (n : 𝒪[K]) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rwa [map_natCast])
  rw [← map_natCast (algebraMap K L),
    Valuation.HasExtension.val_map_eq_one_iff (vR := valuation K) (vA := valuation L)]
  simpa using (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp hu

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The normalized valuation `v_K((n : K))` of the image of a natural number `n` in a
nonarchimedean local field `K`, as a natural number. The proof `hn` that the image is nonzero
is part of the input: in positive characteristic the image can vanish, and no junk value is
assigned there. -/
def natCastValuation (n : ℕ) (hn : (n : K) ≠ 0) : ℕ :=
  (Multiplicative.toAdd (normalizedValuation K (Units.mk0 (n : K) hn))).toNat

variable (K) in
/-- The characteristic equation of `natCastValuation`: it decodes the normalized valuation of
`(n : K)`. The right-hand side expresses the valuation as the image of a natural number, so the
equation also records that the image of `n` lies in `𝒪[K]`. -/
@[simp]
theorem normalizedValuation_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    normalizedValuation K (Units.mk0 (n : K) hn)
      = Multiplicative.ofAdd (natCastValuation K n hn : ℤ) := by
  have h : (0 : ℤ) ≤ Multiplicative.toAdd (normalizedValuation K (Units.mk0 (n : K) hn)) :=
    (mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 (n : K) hn)).mp
      (by simp)
  rw [natCastValuation, Int.toNat_of_nonneg h, ofAdd_toAdd]

variable (K) in
/-- The additive normalized valuation of a nonzero natural-number cast is its
`natCastValuation`. -/
theorem toAdd_normalizedValuation_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    (normalizedValuation K (Units.mk0 (n : K) hn)).toAdd =
      (natCastValuation K n hn : ℤ) := by
  rw [← toAdd_ofAdd (natCastValuation K n hn : ℤ)]
  exact congrArg Multiplicative.toAdd (normalizedValuation_natCast K n hn)

variable (K) in
/-- The zero-preserving form of the characteristic equation of `natCastValuation`. -/
@[simp]
theorem normalizedValuationWithZero_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    normalizedValuationWithZero K (n : K) = WithZero.exp (natCastValuation K n hn : ℤ) := by
  have h := normalizedValuationWithZero_coe (Units.mk0 (n : K) hn)
  rwa [Units.val_mk0, normalizedValuation_natCast K n hn,
    ← WithZero.exp_eq_coe_ofAdd] at h

variable (K) in
/-- The vanishing criterion: the normalized valuation of `n` is zero exactly when `n` is
invertible in the ring of integers. -/
@[simp]
theorem natCastValuation_eq_zero_iff (n : ℕ) (hn : (n : K) ≠ 0) :
    natCastValuation K n hn = 0 ↔ IsUnit (n : 𝒪[K]) := by
  rw [isUnit_iff_normalizedValuationWithZero_eq_one, Subring.coe_natCast,
    normalizedValuationWithZero_natCast K n hn, ← WithZero.exp_zero, WithZero.exp_inj,
    Nat.cast_eq_zero]

variable (K) in
/-- If `n` is invertible in the ring of integers then its normalized valuation vanishes. -/
theorem natCastValuation_eq_zero_of_isUnit {n : ℕ} (hn : (n : K) ≠ 0)
    (hn' : IsUnit (n : 𝒪[K])) : natCastValuation K n hn = 0 :=
  (natCastValuation_eq_zero_iff K n hn).mpr hn'

variable (K) in
/-- The vanishing criterion read off the residue field: the normalized valuation of `n` is zero
exactly when the residue characteristic of `K` does not divide `n`. -/
theorem natCastValuation_eq_zero_iff_not_dvd (n : ℕ) (hn : (n : K) ≠ 0) :
    natCastValuation K n hn = 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  rw [natCastValuation_eq_zero_iff, IsLocalRing.isUnit_natCast_iff_not_dvd]

variable (K) in
/-- For a prime `p`, the normalized valuation of `p` is nonzero exactly when `p` is the residue
characteristic of `K`, that is, exactly when `K` is `p`-adic. -/
theorem natCastValuation_ne_zero_iff_ringChar_eq {p : ℕ} (hp : p.Prime) (hn : (p : K) ≠ 0) :
    natCastValuation K p hn ≠ 0 ↔ ringChar 𝓀[K] = p := by
  rw [ne_eq, natCastValuation_eq_zero_iff_not_dvd, not_not]
  refine ⟨fun h ↦ (hp.eq_one_or_self_of_dvd _ h).resolve_left ?_, fun h ↦ h ▸ dvd_rfl⟩
  exact CharP.char_ne_one 𝓀[K] _

variable (K) in
/-- In equal characteristic the normalized valuation of a nonzero natural-number cast always
vanishes: a natural number whose image in `K` is nonzero is prime to the characteristic, hence
invertible in `𝒪[K]`. The invariant therefore carries information only in mixed characteristic,
which is why the absolute ramification index is defined only there. -/
theorem natCastValuation_eq_zero_of_ringChar_ne_zero (hK : ringChar K ≠ 0) (n : ℕ)
    (hn : (n : K) ≠ 0) : natCastValuation K n hn = 0 := by
  have hp : (ringChar K).Prime := CharP.char_prime_of_ne_zero K hK
  have hcop : IsCoprime ((ringChar K : ℕ) : 𝒪[K]) ((n : ℕ) : 𝒪[K]) := by
    simpa using (Nat.isCoprime_iff_coprime.mpr
      (hp.coprime_iff_not_dvd.mpr fun h ↦ hn ((ringChar.spec K n).mpr h))).map
        (Int.castRingHom 𝒪[K])
  have h0 : ((ringChar K : ℕ) : 𝒪[K]) = 0 :=
    Subtype.ext (by push_cast; exact ringChar.Nat.cast_ringChar (R := K))
  rw [h0] at hcop
  exact (natCastValuation_eq_zero_iff K n hn).mpr (isCoprime_zero_left.mp hcop)

variable (K) in
/-- The normalized valuation of `1` vanishes. -/
@[simp]
theorem natCastValuation_one :
    natCastValuation K 1 (by simpa only [Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)) = 0 := by
  have h1 : ((1 : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)
  exact (natCastValuation_eq_zero_iff K 1 h1).mpr (by simp)

variable (K) in
/-- The normalized valuation of a product of natural numbers is the sum of their valuations. -/
@[simp]
theorem natCastValuation_mul {m n : ℕ} (hm : (m : K) ≠ 0) (hn : (n : K) ≠ 0) :
    natCastValuation K (m * n) (by simpa only [Nat.cast_mul] using mul_ne_zero hm hn) =
      natCastValuation K m hm + natCastValuation K n hn := by
  have hmn : ((m * n : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_mul] using mul_ne_zero hm hn
  have h : normalizedValuationWithZero K ((m * n : ℕ) : K)
      = normalizedValuationWithZero K (m : K) * normalizedValuationWithZero K (n : K) := by
    push_cast
    exact map_mul _ _ _
  rw [normalizedValuationWithZero_natCast K _ hmn, normalizedValuationWithZero_natCast K m hm,
    normalizedValuationWithZero_natCast K n hn, ← WithZero.exp_add, WithZero.exp_inj] at h
  exact_mod_cast h

variable (K) in
/-- The normalized valuation of a natural number is monotone for divisibility. -/
theorem natCastValuation_le_of_dvd {m n : ℕ} (hm : (m : K) ≠ 0) (hn : (n : K) ≠ 0) (h : m ∣ n) :
    natCastValuation K m hm ≤ natCastValuation K n hn := by
  obtain ⟨k, rfl⟩ := h
  have hk : (k : K) ≠ 0 := right_ne_zero_of_mul (by simpa only [Nat.cast_mul] using hn)
  rw [natCastValuation_mul K hm hk]
  exact Nat.le_add_right _ _

/-- **The depth condition beyond `v_K(n)`.** If `v_K(n) < i`, then every prime `p ∣ n` satisfies
`v_K(p) < (p - 1) * i`, the depth condition of the deep-unit power lemmas
`map_powMonoidHom_unitFiltration` and `disjoint_rootsOfUnity_unitFiltration` of
`TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Basic`. -/
theorem natCastValuation_lt_sub_one_mul_of_lt_of_dvd {n i : ℕ} (hn : (n : K) ≠ 0)
    (hi : natCastValuation K n hn < i) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) (hpn : p ∣ n) :
    natCastValuation K p hpK < (p - 1) * i :=
  (natCastValuation_le_of_dvd K hpK hn hpn).trans_lt <|
    hi.trans_le (Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt hp.one_lt))

/-- **The depth condition at `v_K(p) + 1`.** With `p` the residue characteristic, every prime
`ℓ` satisfies `v_K(ℓ) < (ℓ - 1) * (v_K(p) + 1)`: at `ℓ = p` because `ℓ - 1 ≥ 1`, and at `ℓ ≠ p`
because `v_K(ℓ) = 0`. So the deep-unit power lemmas apply at depth `v_K(p) + 1` for every
exponent. -/
theorem natCastValuation_lt_sub_one_mul_natCastValuation_ringChar_add_one
    (hp : (ringChar 𝓀[K] : K) ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    natCastValuation K ℓ hℓK < (ℓ - 1) * (natCastValuation K (ringChar 𝓀[K]) hp + 1) := by
  rcases eq_or_ne ℓ (ringChar 𝓀[K]) with rfl | hℓp
  · exact Nat.lt_succ_self _ |>.trans_le (Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt hℓ.one_lt))
  · rw [(natCastValuation_eq_zero_iff_not_dvd K ℓ hℓK).mpr fun h ↦
      hℓp ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hℓ).mp h).symm]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hℓ.one_lt) (Nat.succ_pos _)

variable (K) in
/-- The normalized valuation of a power of a natural number. -/
@[simp]
theorem natCastValuation_pow {n : ℕ} (k : ℕ) (hn : (n : K) ≠ 0) :
    natCastValuation K (n ^ k) (by simpa only [Nat.cast_pow] using pow_ne_zero k hn) =
      k * natCastValuation K n hn := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.zero_mul]
    exact natCastValuation_one K
  | succ k ih =>
    have hk : ((n ^ k : ℕ) : K) ≠ 0 := by
      simpa only [Nat.cast_pow] using pow_ne_zero k hn
    simpa only [pow_succ, ih, Nat.succ_mul] using natCastValuation_mul K hk hn

variable (K) in
/-- The normalized valuation of a natural number is its `p`-adic valuation times the normalized
valuation of `p`, where `p` is the residue characteristic of `K`. -/
theorem natCastValuation_eq_padicValNat_mul {n : ℕ} (hn : (n : K) ≠ 0)
    (hp : (ringChar 𝓀[K] : K) ≠ 0) :
    natCastValuation K n hn =
      padicValNat (ringChar 𝓀[K]) n * natCastValuation K (ringChar 𝓀[K]) hp := by
  have hp' : (ringChar 𝓀[K]).Prime := CharP.char_is_prime 𝓀[K] _
  have : Fact (ringChar 𝓀[K]).Prime := ⟨hp'⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  -- Split off the prime-to-`p` part, whose valuation vanishes.
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 _ hp'.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero _)
  have hpk : (((ringChar 𝓀[K]) ^ k : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_pow] using pow_ne_zero k hp
  have hmK : (m : K) ≠ 0 := right_ne_zero_of_mul (by simpa only [Nat.cast_mul] using hn)
  rw [natCastValuation_mul K hpk hmK, natCastValuation_pow K k hp,
    (natCastValuation_eq_zero_iff_not_dvd K m hmK).mpr hm]
  simp [padicValNat.mul (pow_ne_zero _ hp'.ne_zero) hm0, padicValNat.eq_zero_of_not_dvd hm]

/-- Writing `p` for the residue characteristic, the normalized valuation of a natural number `n`
is at most `v_K(p) / log p * log n`, because `v_K(n) = v_p(n) v_K(p)` and `p ^ v_p(n) ≤ n`. -/
theorem natCastValuation_le_div_log_mul_log {n : ℕ} (hn : (n : K) ≠ 0)
    (hp : (ringChar 𝓀[K] : K) ≠ 0) :
    (natCastValuation K n hn : ℝ) ≤
      natCastValuation K (ringChar 𝓀[K]) hp / Real.log (ringChar 𝓀[K]) * Real.log n := by
  have hp' : (ringChar 𝓀[K]).Prime := CharP.char_is_prime 𝓀[K] _
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hlogp : 0 < Real.log (ringChar 𝓀[K]) := Real.log_pos (by exact_mod_cast hp'.one_lt)
  have hv : (padicValNat (ringChar 𝓀[K]) n : ℝ) * Real.log (ringChar 𝓀[K]) ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos (by exact_mod_cast hp'.pos) _)
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) pow_padicValNat_dvd)
  rw [natCastValuation_eq_padicValNat_mul K hn hp, div_mul_eq_mul_div, le_div_iff₀ hlogp]
  push_cast
  nlinarith [(Nat.cast_nonneg (natCastValuation K (ringChar 𝓀[K]) hp) : (0 : ℝ) ≤ _)]

variable (K) in
/-- The ideal generated by a nonzero natural-number cast is the corresponding power of the
maximal ideal, with exponent its normalized valuation. -/
theorem span_natCast_eq_maximalIdeal_pow (n : ℕ) (hn : (n : K) ≠ 0) :
    Ideal.span {(n : 𝒪[K])} = 𝓂[K] ^ natCastValuation K n hn := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hv : Ring.ordFrac 𝒪[K] ((π : K) ^ natCastValuation K n hn) =
      Ring.ordFrac 𝒪[K] (n : K) := by
    have hπv : Ring.ordFrac 𝒪[K] (π : K) = WithZero.exp 1 :=
      Ring.ordFrac_irreducible (K := K) hπ
    rw [map_pow, hπv, ← normalizedValuationWithZero_eq_ordFrac,
      normalizedValuationWithZero_natCast K n hn]
    simp [← WithZero.exp_nsmul]
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq _ _ hv
  have hu' : (u : 𝒪[K]) * π ^ natCastValuation K n hn = (n : 𝒪[K]) := by
    apply Subtype.ext
    simpa only [Units.smul_def, Algebra.smul_def, Algebra.algebraMap_ofSubsemiring_apply,
      Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] using hu
  rw [← hu', Ideal.span_singleton_mul_left_unit u.isUnit, hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow]

namespace IsDiscreteValuationRing

variable (K) in
/-- The additive valuation of a nonzero natural-number cast in the integer ring agrees with
`natCastValuation` of its image in the field. -/
@[simp] theorem addVal_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    _root_.IsDiscreteValuationRing.addVal 𝒪[K] (n : 𝒪[K]) =
      (natCastValuation K n hn : ℕ∞) := by
  have hn' : (n : 𝒪[K]) ≠ 0 := fun h => hn (by
    simpa only [Subring.coe_natCast, Subring.coe_zero] using
      congrArg (fun x : 𝒪[K] => (x : K)) h)
  rw [TauCeti.IsDiscreteValuationRing.addVal_eq_multiplicity_span_singleton hn',
    span_natCast_eq_maximalIdeal_pow K n hn,
    multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field 𝒪[K]) inferInstance)]

end IsDiscreteValuationRing

/-- The multiplicative valuation of a nonzero natural-number cast is the corresponding power of
the valuation of any uniformizer. -/
theorem valuation_natCast_eq_pow {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)
    (hn : (n : K) ≠ 0) :
    valuation K (n : K) = valuation K (π : K) ^ natCastValuation K n hn := by
  have h := (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
    (normalizedValuation_irreducible hπ) ((natCastValuation K n hn : ℕ) : ℤ)
    (Units.mk0 (n : K) hn)).mp (by simp)
  simpa only [Units.val_mk0, zpow_natCast] using h

variable (K) in
/-- The normalized absolute value of a natural number is `q ^ (-natCastValuation K n hn)`, where
`q` is the cardinality of the residue field. -/
@[simp]
theorem normalizedAbsoluteValue_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    normalizedAbsoluteValue K (n : K)
      = ((Nat.card 𝓀[K] : ℚ≥0)⁻¹) ^ natCastValuation K n hn := by
  rw [normalizedAbsoluteValue_apply_ne_zero (n : K) hn, normalizedValuation_natCast K n hn,
    toAdd_ofAdd, zpow_neg, zpow_natCast, inv_pow]

end TauCeti
