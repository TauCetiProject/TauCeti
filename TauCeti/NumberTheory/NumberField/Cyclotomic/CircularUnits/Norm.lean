/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.CircularUnits.Generators
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm compatibility of prime-power circular units

This file establishes field-norm compatibility across a single prime-power step
`K = ℚ(ζ_{p ^ (k + 1)}) ⊆ L = ℚ(ζ_{p ^ (k + 2)})` with compatible primitive roots
`algebraMap K L ζK = ζL ^ p`, providing the transition formulas needed for norm-compatible
circular-unit systems in cyclotomic `ℤ_p`-towers.

We compute `Algebra.norm K ζL` (`ζK` for odd `p` and `-ζK` for `p = 2`), show
`Algebra.norm K (1 - ζL ^ b) = 1 - ζK ^ b` and
`Algebra.norm K (cyclotomicRatio ζL b) = cyclotomicRatio ζK b` whenever `p ∤ b`, and deduce strict
norm compatibility for odd-prime `smoothedCyclotomicUnit`s together with the explicit sign
`(-1) ^ ((1 - b) / 2)` for dyadic `dyadicSmoothedCyclotomicUnit`s.

## Main results

* `TauCeti.norm_zeta_of_prime_pow`: `Algebra.norm K ζL = if Odd p then ζK else -ζK`.
* `TauCeti.norm_one_sub_zpow_of_prime_pow`: `Algebra.norm K (1 - ζL ^ b) = 1 - ζK ^ b` for
  `¬ (p : ℤ) ∣ b`.
* `TauCeti.norm_cyclotomicRatio`: `Algebra.norm K (cyclotomicRatio ζL b) = cyclotomicRatio ζK b`.
* `TauCeti.norm_smoothedCyclotomicUnit`: norm compatibility of `smoothedCyclotomicUnit` for odd `p`.
* `TauCeti.norm_dyadicSmoothedCyclotomicUnit`: norm formula with sign `(-1) ^ ((1 - b) / 2)` for
  `p = 2` and `a ≥ 2`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 8.
* R. Sharifi, *Iwasawa Theory*, §§4.2–4.3, 4.7.
-/

public section

open NumberField

open scoped NumberField

namespace TauCeti

section FieldNorms

variable {p k : ℕ} [hp : Fact p.Prime] {K L : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] [Field L] [CharZero L]
  [IsCyclotomicExtension {p ^ (k + 2)} ℚ L] [Algebra K L] [IsScalarTower ℚ K L]

/-- Existence of a bijection `Gal(L / K) ≃ Fin p` sending `σ` to the unique `j < p` with
`σ ζL = (ζL ^ (p ^ (k + 1))) ^ j * ζL`. -/
private theorem exists_primeStepGalEquiv {ζK : K} {ζL : L}
    (hζL : IsPrimitiveRoot ζL (p ^ (k + 2))) (hcompat : algebraMap K L ζK = ζL ^ p) :
    ∃ e : Gal(L/K) ≃ Fin p, ∀ σ, σ ζL = (ζL ^ (p ^ (k + 1))) ^ (e σ : ℕ) * ζL := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hp.out.ne_zero⟩
  have : NeZero (p ^ (k + 2)) := ⟨pow_ne_zero (k + 2) hp.out.ne_zero⟩
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  have : NumberField L := IsCyclotomicExtension.numberField {p ^ (k + 2)} ℚ L
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {p ^ (k + 2)} ℚ L
  have : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  have hξ : IsPrimitiveRoot (ζL ^ (p ^ (k + 1))) p :=
    IsPrimitiveRoot.pow (pow_pos hp.out.pos (k + 2)) hζL (by rw [pow_succ])
  have hζL0 : ζL ≠ 0 := hζL.ne_zero (pow_ne_zero _ hp.out.ne_zero)
  have hex (σ : Gal(L/K)) : ∃ j : Fin p, σ ζL = (ζL ^ (p ^ (k + 1))) ^ (j : ℕ) * ζL := by
    have hpow : (σ ζL / ζL) ^ p = 1 := by
      rw [div_pow, ← map_pow, ← hcompat, AlgEquiv.commutes, hcompat,
        div_self (pow_ne_zero p hζL0)]
    obtain ⟨j, hj_lt, hj_eq⟩ := hξ.eq_pow_of_pow_eq_one hpow
    exact ⟨⟨j, hj_lt⟩, by simp only [hj_eq, div_mul_cancel₀ _ hζL0]⟩
  choose φ hφ using hex
  have hφ_inj : Function.Injective φ := fun σ₁ σ₂ h12 ↦ by
    have hζeq : σ₁ ζL = σ₂ ζL := by rw [hφ σ₁, hφ σ₂, h12]
    have htop : Algebra.adjoin ℚ {ζL} = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζL
    have hq_eq : σ₁.toAlgHom.restrictScalars ℚ = σ₂.toAlgHom.restrictScalars ℚ :=
      AlgHom.ext_of_adjoin_eq_top htop fun y hy ↦ by
        rcases Set.mem_singleton_iff.mp hy with rfl; exact hζeq
    exact AlgEquiv.ext fun x ↦ AlgHom.congr_fun hq_eq x
  have hfin : Module.finrank K L = p := by
    have hmul := Module.finrank_mul_finrank ℚ K L
    rw [IsCyclotomicExtension.Rat.finrank (p ^ (k + 1)) K,
      IsCyclotomicExtension.Rat.finrank (p ^ (k + 2)) L,
      Nat.totient_prime_pow_succ hp.out, Nat.totient_prime_pow_succ hp.out] at hmul
    have hpos : 0 < p ^ k * (p - 1) :=
      Nat.mul_pos (pow_pos hp.out.pos k) (Nat.sub_pos_of_lt hp.out.one_lt)
    have hrhs : p ^ (k + 1) * (p - 1) = (p ^ k * (p - 1)) * p := by rw [pow_succ]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos (hrhs ▸ hmul)
  have hcard : Fintype.card Gal(L/K) = Fintype.card (Fin p) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L,
      hfin, Nat.card_fin]
  exact ⟨Equiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, hcard⟩), hφ⟩

/-- Across one prime-power step `ℚ(ζ_{p ^ (k + 1)}) ⊆ ℚ(ζ_{p ^ (k + 2)})` with `ζK = ζL ^ p`, the
norm of `ζL` is `ζK` for odd `p` and `-ζK` for `p = 2`. -/
theorem norm_zeta_of_prime_pow {ζK : K} {ζL : L} (hζL : IsPrimitiveRoot ζL (p ^ (k + 2)))
    (hcompat : algebraMap K L ζK = ζL ^ p) :
    Algebra.norm K ζL = if Odd p then ζK else -ζK := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  have : NumberField L := IsCyclotomicExtension.numberField {p ^ (k + 2)} ℚ L
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {p ^ (k + 2)} ℚ L
  have : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  set ξ : L := ζL ^ (p ^ (k + 1))
  have hξ : IsPrimitiveRoot ξ p :=
    IsPrimitiveRoot.pow (pow_pos hp.out.pos (k + 2)) hζL (by rw [pow_succ])
  obtain ⟨e, he⟩ := exists_primeStepGalEquiv hζL hcompat
  apply FaithfulSMul.algebraMap_injective K L
  rw [Algebra.norm_eq_prod_automorphisms K ζL]
  have hprod : ∏ σ : Gal(L/K), σ ζL = ∏ j : Fin p, (ξ ^ (j : ℕ) * ζL) :=
    Fintype.prod_equiv e _ _ he
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.prod_univ_eq_prod_range (fun j ↦ ξ ^ j), Finset.prod_pow_eq_pow_sum, ← hcompat]
  split_ifs with hodd
  · obtain ⟨m, hm⟩ := hodd
    have hsum : ∑ j ∈ Finset.range p, j = p * m := by
      have h2 := Finset.sum_range_id_mul_two p
      have hp1 : p - 1 = 2 * m := by omega
      rw [hp1] at h2
      exact Nat.mul_right_cancel two_pos (by linarith)
    rw [hsum, pow_mul, hξ.pow_eq_one, one_pow, one_mul]
  · have hp2 : p = 2 := hp.out.eq_two_or_odd.resolve_right fun h1 ↦ hodd (Nat.odd_iff.mpr h1)
    subst hp2
    simp [Finset.sum_range_succ, hξ.eq_neg_one_of_two_right]

/-- Across one prime-power step `ℚ(ζ_{p ^ (k + 1)}) ⊆ ℚ(ζ_{p ^ (k + 2)})` with `ζK = ζL ^ p`, for
every integer `b` not divisible by `p`, `Algebra.norm K (1 - ζL ^ b) = 1 - ζK ^ b`. -/
theorem norm_one_sub_zpow_of_prime_pow {ζK : K} {ζL : L} (hζL : IsPrimitiveRoot ζL (p ^ (k + 2)))
    (hcompat : algebraMap K L ζK = ζL ^ p) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    Algebra.norm K (1 - ζL ^ b) = 1 - ζK ^ b := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  have : NumberField L := IsCyclotomicExtension.numberField {p ^ (k + 2)} ℚ L
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {p ^ (k + 2)} ℚ L
  have : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  set ξ : L := ζL ^ (p ^ (k + 1))
  have hξ : IsPrimitiveRoot ξ p :=
    IsPrimitiveRoot.pow (pow_pos hp.out.pos (k + 2)) hζL (by rw [pow_succ])
  have hξb : IsPrimitiveRoot (ξ ^ b) p :=
    hξ.zpow_of_gcd_eq_one b
      ((hp.out.coprime_iff_not_dvd.mpr fun h ↦ hb (Int.natCast_dvd.mpr h)).symm.gcd_eq_one)
  obtain ⟨e, he⟩ := exists_primeStepGalEquiv hζL hcompat
  apply FaithfulSMul.algebraMap_injective K L
  rw [Algebra.norm_eq_prod_automorphisms K (1 - ζL ^ b)]
  have hprod : ∏ σ : Gal(L/K), σ (1 - ζL ^ b) =
      ∏ j ∈ Finset.range p, (1 - (ξ ^ b) ^ j * ζL ^ b) := by
    calc ∏ σ : Gal(L/K), σ (1 - ζL ^ b)
        = ∏ j : Fin p, (1 - (ξ ^ (j : ℕ) * ζL) ^ b) :=
          Fintype.prod_equiv e _ _ fun σ ↦ by rw [map_sub, map_one, map_zpow₀, he σ]
      _ = ∏ j ∈ Finset.range p, (1 - (ξ ^ j * ζL) ^ b) :=
          Fin.prod_univ_eq_prod_range (fun j ↦ 1 - (ξ ^ j * ζL) ^ b) p
      _ = ∏ j ∈ Finset.range p, (1 - (ξ ^ b) ^ j * ζL ^ b) :=
          Finset.prod_congr rfl fun j _ ↦ by
            rw [mul_zpow, ← zpow_natCast ξ j, ← zpow_mul, mul_comm (j : ℤ) b,
              zpow_mul, zpow_natCast]
  rw [hprod]
  have heval := congrArg (Polynomial.eval 1)
    (X_pow_sub_C_eq_prod hξb hp.out.pos (rfl : (ζL ^ b) ^ p = _))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    one_pow, Polynomial.eval_prod] at heval
  rw [← heval, ← zpow_natCast, ← zpow_mul, mul_comm b (p : ℤ), zpow_mul, zpow_natCast,
    ← hcompat, map_sub, map_one, map_zpow₀]

/-- **Norm compatibility of cyclotomic ratios.** For EVERY prime `p`, `k : ℕ`, and `b : ℤ` not
divisible by `p`, `Algebra.norm K (cyclotomicRatio ζL b) = cyclotomicRatio ζK b`. -/
theorem norm_cyclotomicRatio {ζK : K} {ζL : L} (hζL : IsPrimitiveRoot ζL (p ^ (k + 2)))
    (hcompat : algebraMap K L ζK = ζL ^ p) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    Algebra.norm K (cyclotomicRatio ζL b) = cyclotomicRatio ζK b := by
  have : NumberField L := IsCyclotomicExtension.numberField {p ^ (k + 2)} ℚ L
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hp_ndvd_one : ¬ (p : ℤ) ∣ (1 : ℤ) := fun hdvd ↦ by
    have := Int.le_of_dvd one_pos hdvd; have := hp.out.two_le; omega
  have hL : cyclotomicRatio ζL b = (1 - ζL ^ b) * (1 - ζL)⁻¹ := by
    rw [cyclotomicRatio_def, ← neg_div_neg_eq, div_eq_mul_inv]; ring_nf
  have hK : cyclotomicRatio ζK b = (1 - ζK ^ b) * (1 - ζK)⁻¹ := by
    rw [cyclotomicRatio_def, ← neg_div_neg_eq, div_eq_mul_inv]; ring_nf
  have h1 : Algebra.norm K (1 - ζL) = 1 - ζK := by
    simpa using norm_one_sub_zpow_of_prime_pow hζL hcompat hp_ndvd_one
  rw [hL, hK, map_mul, Algebra.norm_inv, norm_one_sub_zpow_of_prime_pow hζL hcompat hb, h1]

end FieldNorms

section SmoothedNorms

/-- **Norm compatibility of odd-prime smoothed circular units.** Across a prime-power step
`ℚ(ζ_{p ^ (k + 1)}) ⊆ ℚ(ζ_{p ^ (k + 2)})` for odd `p`, the norm of `smoothedCyclotomicUnit` at
level `p ^ (k + 2)` is `smoothedCyclotomicUnit` at level `p ^ (k + 1)` with the same `b`. -/
theorem norm_smoothedCyclotomicUnit {p k : ℕ} [hp : Fact p.Prime] {K L : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ (k + 2)} ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    (hodd : Odd p) {ζK : K} {ζL : L}
    (hζK : IsPrimitiveRoot ζK (p ^ (k + 1))) (hζL : IsPrimitiveRoot ζL (p ^ (k + 2)))
    (hcompat : algebraMap K L ζK = ζL ^ p)
    {b : ℤ} (hbL : Int.gcd b (p ^ (k + 2)) = 1) (hbK : Int.gcd b (p ^ (k + 1)) = 1) :
    Algebra.norm K
        (((smoothedCyclotomicUnit hodd hζL hbL : 𝓞 (maximalRealSubfield L)) :
          maximalRealSubfield L) : L) =
      (((smoothedCyclotomicUnit hodd hζK hbK : 𝓞 (maximalRealSubfield K)) :
        maximalRealSubfield K) : K) := by
  obtain ⟨m, hm⟩ := hodd.pow (n := k + 2)
  set h : ℤ := ((m + 1 : ℕ) : ℤ)
  have h2hL : 2 * h ≡ 1 [ZMOD (p ^ (k + 2) : ℕ)] :=
    Int.modEq_iff_dvd.mpr ⟨-1, by simp only [h]; omega⟩
  have h2hK : 2 * h ≡ 1 [ZMOD (p ^ (k + 1) : ℕ)] :=
    h2hL.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow p (Nat.le_succ (k + 1))))
  have hp_ndvd_b : ¬ (p : ℤ) ∣ b := fun hpb ↦ by
    have hgcd : p ∣ Int.gcd b (p ^ (k + 2)) :=
      Int.dvd_gcd hpb (Int.natCast_dvd_natCast.mpr (dvd_pow_self p (by omega)))
    rw [hbL] at hgcd
    exact absurd (Nat.le_of_dvd one_pos hgcd) (not_le.mpr hp.out.one_lt)
  rw [coe_smoothedCyclotomicUnit hodd hζL hbL h2hL, coe_smoothedCyclotomicUnit hodd hζK hbK h2hK,
    map_mul, Algebra.norm_zpow, norm_zeta_of_prime_pow hζL hcompat, ite_eq_left hodd,
    norm_cyclotomicRatio hζL hcompat hp_ndvd_b]

/-- **Dyadic norm formula with explicit sign.** Across a dyadic step
`ℚ(ζ_{2 ^ (k + 2)}) ⊆ ℚ(ζ_{2 ^ (k + 3)})` with `ζK = ζL ^ 2`, for every odd integer `b`, the norm
of `dyadicSmoothedCyclotomicUnit` acquires the sign `(-1) ^ ((1 - b) / 2)`. -/
theorem norm_dyadicSmoothedCyclotomicUnit {k : ℕ} {K L : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] [Field L] [NumberField L]
    [IsCyclotomicExtension {2 ^ (k + 3)} ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    {ζK : K} {ζL : L} (hζK : IsPrimitiveRoot ζK (2 ^ (k + 2)))
    (hζL : IsPrimitiveRoot ζL (2 ^ (k + 3)))
    (hcompat : algebraMap K L ζK = ζL ^ 2) {b : ℤ} (hb : Odd b) :
    Algebra.norm K
        (((dyadicSmoothedCyclotomicUnit hζL hb : 𝓞 (maximalRealSubfield L)) :
          maximalRealSubfield L) : L) =
      (-1 : K) ^ ((1 - b) / 2) *
        (((dyadicSmoothedCyclotomicUnit hζK hb : 𝓞 (maximalRealSubfield K)) :
          maximalRealSubfield K) : K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2_ndvd : ¬ (2 : ℤ) ∣ b := by obtain ⟨m, rfl⟩ := hb; omega
  rw [coe_dyadicSmoothedCyclotomicUnit hζL hb, coe_dyadicSmoothedCyclotomicUnit hζK hb,
    map_mul, Algebra.norm_zpow, norm_zeta_of_prime_pow (p := 2) (k := k + 1) hζL hcompat,
    ite_eq_right (by decide : ¬ Odd 2),
    norm_cyclotomicRatio (p := 2) (k := k + 1) hζL hcompat h2_ndvd,
    neg_eq_neg_one_mul, mul_zpow, mul_assoc]

end SmoothedNorms

end TauCeti
