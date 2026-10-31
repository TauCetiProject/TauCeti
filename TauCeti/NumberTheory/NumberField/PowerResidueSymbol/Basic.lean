/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.NumberField.Ideal.RootsOfUnity
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The `n`-th power residue symbol at a prime of a number field

Let `K` be a number field whose ring of integers contains a primitive `n`-th root of unity, and
let `P` be a maximal ideal of `𝓞 K` whose absolute norm `N P` is prime to `n`. Then
`n ∣ N P - 1` (`NumberField.dvd_absNorm_sub_one`), and reduction modulo `P` identifies the
`n`-th roots of unity of `𝓞 K` with those of the residue field (`Ideal.rootsOfUnityEquivQuot`).
For `x ≠ 0` in `𝓞 K ⧸ P` the power `x ^ ((N P - 1) / n)` is an `n`-th root of unity of the
residue field; the `n`-th power residue symbol `(x / P)_n` is its unique lift to an `n`-th root
of unity of `𝓞 K`. Together with `(0 / P)_n = 0` this is a multiplicative character
`Ideal.powerResidueSymbol P n` of the residue field with values in `𝓞 K`, of order exactly `n`.

At primes whose norm is not prime to `n` the symbol is, by convention, the trivial character; the
lemmas below that describe its values all assume `N P` prime to `n`. The symbol is the basic
object of the higher (cubic, quartic and Eisenstein) reciprocity laws.

## Main definitions and results

* `Ideal.powerResidueSymbol P n`: the `n`-th power residue symbol at `P`.
* `Ideal.mk_powerResidueSymbol`: `(x / P)_n ≡ x ^ ((N P - 1) / n) (mod P)` for `x ≠ 0`.
* `Ideal.powerResidueSymbol_pow_eq_one`: `(x / P)_n` is an `n`-th root of unity for `x ≠ 0`.
* `Ideal.powerResidueSymbol_eq_iff`: `(x / P)_n` is the only `n`-th root of unity of `𝓞 K`
  congruent to `x ^ ((N P - 1) / n)`.
* `Ideal.powerResidueSymbol_mk_of_pow_eq_one`: `(ζ / P)_n = ζ ^ ((N P - 1) / n)` for an `n`-th
  root of unity `ζ` of `𝓞 K`.
* `Ideal.powerResidueSymbol_pow_div`: `((x / P)_n) ^ (n / d) = (x / P)_d` for `d ∣ n`.
* `Ideal.orderOf_powerResidueSymbol`: the symbol has order `n`.
* `Ideal.powerResidueSymbol_intCast_eq_one`: `(m / P)_n = 1` for an integer `m` prime to the
  rational prime `q ∈ P` when `n (q - 1) ∣ N P - 1`.
* `Ideal.map_powerResidueSymbol`: Galois equivariance, `σ ((α / P)_n) = (σ α / σ P)_n` for a ring
  isomorphism `σ : 𝓞 K ≃+* 𝓞 L`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Proposition 4.1.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2.
-/

public section

open NumberField

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {P : Ideal (𝓞 K)} [P.IsMaximal] {n : ℕ} [NeZero n]
  [HasEnoughRootsOfUnity (𝓞 K) n]

variable (P n) in
/-- **The `n`-th power residue symbol** `(· / P)_n` at a maximal ideal `P` of `𝓞 K`, as a
multiplicative character of the residue field `𝓞 K ⧸ P` with values in `𝓞 K`. If `N P` is prime
to `n`, it sends `x ≠ 0` to the unique `n`-th root of unity of `𝓞 K` congruent to
`x ^ ((N P - 1) / n)` modulo `P`. If `N P` is not prime to `n`, it is the trivial character by
convention. -/
noncomputable def powerResidueSymbol : MulChar (𝓞 K ⧸ P) (𝓞 K) :=
  if hP : (absNorm P).Coprime n then
    MulChar.ofUnitHom <| (rootsOfUnity n (𝓞 K)).subtype.comp <|
      (rootsOfUnityEquivQuot P n hP).symm.toMonoidHom.comp <|
        (powMonoidHom ((absNorm P - 1) / n)).codRestrict _ fun u ↦ by
          rw [powMonoidHom_apply]
          exact pow_absNorm_sub_one_div_mem_rootsOfUnity hP u
  else 1

/-- At a prime whose norm is not prime to `n`, the `n`-th power residue symbol is trivial by
convention. -/
theorem powerResidueSymbol_of_not_coprime (hP : ¬(absNorm P).Coprime n) :
    powerResidueSymbol P n = 1 :=
  dite_eq_right hP

/-- The value of the power residue symbol at a unit `u`: the lift to `𝓞 K` of the root of unity
`u ^ ((N P - 1) / n)`. -/
private theorem powerResidueSymbol_coe_unit (hP : (absNorm P).Coprime n) (u : (𝓞 K ⧸ P)ˣ) :
    powerResidueSymbol P n u = (((rootsOfUnityEquivQuot P n hP).symm
      ⟨u ^ ((absNorm P - 1) / n), pow_absNorm_sub_one_div_mem_rootsOfUnity hP u⟩ :
        (𝓞 K)ˣ) : 𝓞 K) := by
  rw [powerResidueSymbol, dite_eq_left hP, MulChar.ofUnitHom_coe]
  simp [MonoidHom.codRestrict_apply]

/-- **The defining congruence of the power residue symbol.** If `N P` is prime to `n` and
`x ≠ 0`, then `(x / P)_n ≡ x ^ ((N P - 1) / n) (mod P)`. -/
theorem mk_powerResidueSymbol (hP : (absNorm P).Coprime n) {x : 𝓞 K ⧸ P} (hx : x ≠ 0) :
    Ideal.Quotient.mk P (powerResidueSymbol P n x) = x ^ ((absNorm P - 1) / n) := by
  let _ := Ideal.Quotient.field P
  lift x to (𝓞 K ⧸ P)ˣ using hx.isUnit
  rw [powerResidueSymbol_coe_unit hP, mk_coe_rootsOfUnityEquivQuot_symm_apply,
    Units.val_pow_eq_pow_val]

/-- If `N P` is prime to `n` and `x ≠ 0`, then `(x / P)_n` is an `n`-th root of unity. -/
theorem powerResidueSymbol_pow_eq_one (hP : (absNorm P).Coprime n) {x : 𝓞 K ⧸ P} (hx : x ≠ 0) :
    powerResidueSymbol P n x ^ n = 1 := by
  let _ := Ideal.Quotient.field P
  lift x to (𝓞 K ⧸ P)ˣ using hx.isUnit
  rw [powerResidueSymbol_coe_unit hP, ← Units.val_pow_eq_pow_val,
    (mem_rootsOfUnity _ _).mp (SetLike.coe_mem _), Units.val_one]

/-- **Characterisation of the power residue symbol.** If `N P` is prime to `n` and `x ≠ 0`, then
`(x / P)_n` is the unique `n`-th root of unity of `𝓞 K` congruent to `x ^ ((N P - 1) / n)`
modulo `P`. -/
theorem powerResidueSymbol_eq_iff (hP : (absNorm P).Coprime n) {x : 𝓞 K ⧸ P} (hx : x ≠ 0)
    {μ : 𝓞 K} (hμ : μ ^ n = 1) :
    powerResidueSymbol P n x = μ ↔ Ideal.Quotient.mk P μ = x ^ ((absNorm P - 1) / n) := by
  refine ⟨fun h ↦ h ▸ mk_powerResidueSymbol hP hx, fun h ↦ ?_⟩
  exact eq_of_pow_eq_one_of_mk_eq IsPrime.ne_top' hP (powerResidueSymbol_pow_eq_one hP hx) hμ
    (by rw [mk_powerResidueSymbol hP hx, h])

/-- **The power residue symbol of a root of unity.** If `N P` is prime to `n` and `ζ` is an
`n`-th root of unity of `𝓞 K`, then `(ζ / P)_n = ζ ^ ((N P - 1) / n)`. -/
theorem powerResidueSymbol_mk_of_pow_eq_one (hP : (absNorm P).Coprime n) {ζ : 𝓞 K}
    (hζ : ζ ^ n = 1) :
    powerResidueSymbol P n (Ideal.Quotient.mk P ζ) = ζ ^ ((absNorm P - 1) / n) := by
  have hx : Ideal.Quotient.mk P ζ ≠ 0 :=
    ((IsUnit.of_pow_eq_one hζ (NeZero.ne n)).map (Ideal.Quotient.mk P)).ne_zero
  rw [powerResidueSymbol_eq_iff hP hx (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]),
    map_pow]

/-- **Compatibility with divisors of `n`.** If `d ∣ n` and `N P` is prime to `n`, then
`((x / P)_n) ^ (n / d) = (x / P)_d`. -/
theorem powerResidueSymbol_pow_div (hP : (absNorm P).Coprime n) {d : ℕ} [NeZero d]
    [HasEnoughRootsOfUnity (𝓞 K) d] (hd : d ∣ n) (x : 𝓞 K ⧸ P) :
    powerResidueSymbol P n x ^ (n / d) = powerResidueSymbol P d x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [MulChar.map_zero, MulChar.map_zero,
      zero_pow (Nat.div_ne_zero_iff_of_dvd hd |>.mpr ⟨NeZero.ne n, NeZero.ne d⟩)]
  have hPd : (absNorm P).Coprime d := hP.coprime_dvd_right hd
  refine ((powerResidueSymbol_eq_iff hPd hx ?_).mpr ?_).symm
  · rw [← pow_mul, Nat.div_mul_cancel hd, powerResidueSymbol_pow_eq_one hP hx]
  · rw [map_pow, mk_powerResidueSymbol hP hx, ← pow_mul,
      Nat.div_mul_div (dvd_absNorm_sub_one hP) hd]

/-- **The power residue symbol has order `n`** when `N P` is prime to `n`. -/
theorem orderOf_powerResidueSymbol (hP : (absNorm P).Coprime n) :
    orderOf (powerResidueSymbol P n) = n := by
  let _ := Ideal.Quotient.field P
  have hdvd := dvd_absNorm_sub_one hP
  have hN : absNorm P - 1 ≠ 0 := by
    rw [absNorm_eq_natCard, ← Nat.card_units]
    exact Nat.card_pos.ne'
  -- The symbol takes a primitive `n`-th root of unity as value at a generator of `(𝓞 K ⧸ P)ˣ`.
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 K ⧸ P)ˣ)
  have hg' : IsPrimitiveRoot g (absNorm P - 1) := by
    rw [absNorm_eq_natCard, ← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact IsPrimitiveRoot.orderOf g
  have hξ : IsPrimitiveRoot (powerResidueSymbol P n g) n := by
    have h := hg'.pow_of_dvd (Nat.div_ne_zero_iff_of_dvd hdvd |>.mpr ⟨hN, NeZero.ne n⟩)
      (Nat.div_dvd_of_dvd hdvd)
    rw [Nat.div_div_self hdvd hN] at h
    rw [powerResidueSymbol_coe_unit hP, IsPrimitiveRoot.coe_units_iff,
      IsPrimitiveRoot.coe_submonoidClass_iff]
    refine IsPrimitiveRoot.map_of_injective ?_ (rootsOfUnityEquivQuot P n hP).symm.injective
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff]
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) (hξ.dvd_of_pow_eq_one _ ?_)
  · ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe,
      powerResidueSymbol_pow_eq_one hP u.ne_zero]
  · rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

/-- The first power residue symbol is the trivial character. -/
@[simp]
theorem powerResidueSymbol_one : powerResidueSymbol P 1 = 1 :=
  orderOf_eq_one_iff.mp (orderOf_powerResidueSymbol (Nat.coprime_one_right _))

/-- **Rational integers at a prime of large residue degree.** Let `q` be a rational prime in `P`
with `n (q - 1) ∣ N P - 1`. Then `(m / P)_n = 1` for every integer `m` prime to `q`, since
`m ^ (q - 1) ≡ 1 (mod q)`. For instance, this applies with `n = 4` at a rational prime
`q ≡ 3 (mod 4)` of norm `N P = q²` in `ℤ[i]`. -/
theorem powerResidueSymbol_intCast_eq_one {q : ℕ} (hq : q.Prime)
    (hqP : (q : 𝓞 K) ∈ P) (hdvd : n * (q - 1) ∣ absNorm P - 1) {m : ℤ} (hm : IsCoprime m q) :
    powerResidueSymbol P n (m : 𝓞 K ⧸ P) = 1 := by
  let _ := Ideal.Quotient.field P
  -- Fermat's little theorem `q ∣ m ^ (q - 1) - 1`, read modulo `P ∋ q`.
  obtain ⟨t, ht⟩ := (Int.ModEq.pow_card_sub_one_eq_one hq hm).symm.dvd
  have hq0 : (q : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Quotient.mk P)]
    exact Quotient.eq_zero_iff_mem.mpr hqP
  have hpow : (m : 𝓞 K ⧸ P) ^ (q - 1) = 1 := by
    have h := congrArg (Int.cast : ℤ → 𝓞 K ⧸ P) ht
    rwa [Int.cast_mul, Int.cast_natCast, hq0, zero_mul, Int.cast_sub, Int.cast_pow, Int.cast_one,
      sub_eq_zero] at h
  have hm0 : (m : 𝓞 K ⧸ P) ≠ 0 := by
    rintro h
    rw [h, zero_pow (Nat.sub_ne_zero_of_lt hq.one_lt)] at hpow
    exact zero_ne_one hpow
  by_cases hP : (absNorm P).Coprime n
  · obtain ⟨k, hk⟩ := hdvd
    rw [powerResidueSymbol_eq_iff hP hm0 (one_pow n), map_one, hk, mul_assoc,
      Nat.mul_div_cancel_left _ (NeZero.pos n), pow_mul, hpow, one_pow]
  · rw [powerResidueSymbol_of_not_coprime hP, MulChar.one_apply hm0.isUnit]

variable {L : Type*} [Field L] [NumberField L] [HasEnoughRootsOfUnity (𝓞 L) n]

/-- **Galois equivariance of the power residue symbol.** A ring isomorphism `σ : 𝓞 K ≃+* 𝓞 L`
carries the symbol at `P` to the symbol at `σ P`: `σ ((α / P)_n) = (σ α / σ P)_n`. Taking `L = K`,
this applies to every ring automorphism of `𝓞 K`, the restrictions of the automorphisms of `K`.
No coprimality is assumed: since `N (σ P) = N P`, if `N P` is not prime to `n` then both
symbols are the trivial character. -/
theorem map_powerResidueSymbol (P : Ideal (𝓞 K)) [P.IsMaximal] (σ : 𝓞 K ≃+* 𝓞 L) (α : 𝓞 K) :
    σ (powerResidueSymbol P n (Quotient.mk P α)) =
      powerResidueSymbol (P.map σ) n (Quotient.mk (P.map σ) (σ α)) := by
  -- Transport the residue class of `α` along the induced isomorphism of residue fields.
  let τ := quotientEquiv P (P.map σ) σ rfl
  rw [← quotientEquiv_mk P (P.map σ) σ rfl]
  generalize Quotient.mk P α = x
  have hN : absNorm (P.map σ) = absNorm P := absNorm_map_of_ringEquiv σ P
  by_cases hP : (absNorm P).Coprime n
  · obtain rfl | hx := eq_or_ne x 0
    · rw [MulChar.map_zero, map_zero, map_zero, MulChar.map_zero]
    -- `σ ((x / P)_n)` is an `n`-th root of unity congruent to `τ x ^ ((N P - 1) / n)`.
    refine ((powerResidueSymbol_eq_iff (hN ▸ hP) (τ.map_ne_zero_iff.mpr hx) ?_).mpr ?_).symm
    · rw [← map_pow, powerResidueSymbol_pow_eq_one hP hx, map_one]
    · rw [← quotientEquiv_mk P (P.map σ) σ rfl, mk_powerResidueSymbol hP hx, map_pow, hN]
  · rw [powerResidueSymbol_of_not_coprime hP, powerResidueSymbol_of_not_coprime (hN ▸ hP),
      MulChar.map_one_apply σ τ]

/-- If an automorphism `σ` of `𝓞 K` raises the `n`-th root of unity `ζ` to the power `k`, then
both sides of `map_powerResidueSymbol` at `ζ`, computed directly, are `ζ ^ (k (N P - 1) / n)`,
because `N (σ P) = N P`. -/
example (σ : 𝓞 K ≃+* 𝓞 K) (hP : (absNorm P).Coprime n) {ζ : 𝓞 K} (hζ : ζ ^ n = 1) {k : ℕ}
    (hσ : σ ζ = ζ ^ k) :
    σ (powerResidueSymbol P n (Quotient.mk P ζ)) = ζ ^ (k * ((absNorm P - 1) / n)) ∧
      powerResidueSymbol (P.map σ) n (Quotient.mk (P.map σ) (σ ζ)) =
        ζ ^ (k * ((absNorm P - 1) / n)) := by
  have hζk : (ζ ^ k) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine ⟨by rw [powerResidueSymbol_mk_of_pow_eq_one hP hζ, map_pow, hσ, ← pow_mul], ?_⟩
  rw [hσ, powerResidueSymbol_mk_of_pow_eq_one (by rwa [absNorm_map_of_ringEquiv]) hζk,
    absNorm_map_of_ringEquiv, ← pow_mul]

end Ideal
