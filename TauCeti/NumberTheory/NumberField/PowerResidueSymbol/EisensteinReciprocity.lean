/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Ideal.Int
import TauCeti.NumberTheory.NumberField.Ideal.Norm
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime and `K = ℚ(ζ_p)` a `p`-th cyclotomic extension of `ℚ`, with ring of
integers `𝓞 K = ℤ[ζ_p]`. Write `(x / 𝔞)_p` for the `p`-th power residue symbol
`Ideal.powerResidueSymbolIdeal 𝔞 p (Ideal.Quotient.mk 𝔞 x)`. This file proves **Eisenstein's
reciprocity law**: for every primary integer `α ∈ 𝓞 K` (`TauCeti.IsEisensteinPrimary`) and every
rational integer `a ∈ ℤ` not divisible by `p`,

`(α / a 𝓞 K)_p = (a / α 𝓞 K)_p`.

The proof proceeds in three stages:

1. **Residue symbol of the Stickelberger product.** At any level `m ≥ 2` and any ideal `B` of
   `𝓞 K` in an `m`-th cyclotomic field, evaluating `(· / B)_m` on
   `TauCeti.stickelbergerProduct m α = ∏_σ (σ⁻¹ α) ^ c(σ)` uses Galois equivariance of the power
   residue symbol (`Ideal.map_powerResidueSymbolIdeal`), the action `σ ξ = ξ ^ c(σ)` on `m`-th
   roots of unity, and the Galois norm-ideal identity `∏_σ σ • B = (N B) 𝓞 K`
   (`Ideal.prod_smul_eq_span_absNorm`) to give `(α ^ γ / B)_m = (α / (N B) 𝓞 K)_m`.
2. **Reciprocity at the norm of an ideal.** When `p` is an odd prime, `α` is primary, and `B` has
   norm prime to `p`, Stickelberger's normalized relation gives `Φ((α)) = ±α ^ γ`
   (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`). Since `(-1 / B)_p = 1`
   for odd `p`, combining `(Φ((α)) / B)_p = (N B / (α))_p`
   (`Ideal.powerResidueSymbolIdeal_stickelbergerPhi`) with stage 1 yields
   `(α / (N B) 𝓞 K)_p = (N B / α 𝓞 K)_p`.
3. **Descent to rational integers.** For a rational prime `q ≠ p` and a prime `P` of `𝓞 K` above
   `q`, `N P = q ^ f` where the inertia degree `f` divides `p - 1` and is therefore prime to `p`.
   Stage 2 gives `(α / q 𝓞 K)_p ^ f = (q / α 𝓞 K)_p ^ f`, and two `p`-th roots of unity with equal
   `f`-th powers coincide because `gcd(f, p) = 1`. Multiplicativity in `a` and `(-1 / ·)_p = 1`
   extend the identity to all `a ∈ ℤ` with `p ∤ a`.

Neither `¬ IsUnit α`, `a ≠ ±1`, nor coprimality of `a` and `α` is assumed: units give `1 = 1`, and
when `(a)` and `(α)` are not coprime both residue classes are nonunits so both symbols vanish.
The primary hypothesis on `α`, by contrast, is essential: replacing `α` by `ζ_p α` multiplies
`(α / n 𝓞 K)_p` by `ζ_p ^ ((n ^ (p - 1) - 1) / p)` while leaving `(n / α 𝓞 K)_p` unchanged, so for
coprime `α` and `n` (`p ∤ n`) the unnormalized equality holds if and only if `n` satisfies the
Wieferich congruence `n ^ (p - 1) ≡ 1 (mod p²)`.

## Main results

* `Ideal.powerResidueSymbolIdeal_stickelbergerProduct`,
  `Ideal.powerResidueSymbol_stickelbergerProduct`: `(α ^ γ / B)_m = (α / (N B) 𝓞 K)_m` for `m ≥ 2`.
* `IsPrimitiveRoot.eisenstein_reciprocity_absNorm`: `(α / (N B) 𝓞 K)_p = (N B / α 𝓞 K)_p` for odd
  prime `p`, primary `α`, and `(absNorm B).Coprime p`.
* `IsPrimitiveRoot.eisenstein_reciprocity_natCast`, `IsPrimitiveRoot.eisenstein_reciprocity`,
  `IsPrimitiveRoot.eisenstein_reciprocity_intCast`: `(α / a 𝓞 K)_p = (a / α 𝓞 K)_p` for odd prime
  `p`, primary `α`, and `n : ℕ` (`p ∤ n`) or `a : ℤ` (`(p : ℤ) ∤ a`).
* `IsPrimitiveRoot.powerResidueSymbolIdeal_toInteger_mul_natCast`,
  `IsPrimitiveRoot.eisenstein_reciprocity_toInteger_mul_natCast_iff`: the root-of-unity shift on
  `ζ_p α` and its characterization by the Wieferich congruence `n ^ (p - 1) ≡ 1 (mod p²)`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25).
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2,
  Theorem 1.
-/

public section

open NumberField Ideal IsCyclotomicExtension.Rat UniqueFactorizationMonoid
open scoped Pointwise

/-! ### The power residue symbol of the Stickelberger product -/

namespace Ideal

section StickelbergerProduct

variable {m : ℕ} {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]

/-- Transporting coprimality of a principal ideal along the pointwise Galois action on `𝓞 K`. -/
private theorem isCoprime_span_smul_iff (σ : Gal(K/ℚ)) (α : 𝓞 K) (B : Ideal (𝓞 K)) :
    IsCoprime (span {σ • α}) B ↔ IsCoprime (span {α}) (σ⁻¹ • B) := by
  rw [isCoprime_iff_sup_eq, isCoprime_iff_sup_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [smul_sup, smul_closure, Set.smul_set_singleton, inv_smul_smul] using
      congr_arg (σ⁻¹ • ·) h
  · simpa [smul_sup, smul_closure, Set.smul_set_singleton, smul_inv_smul] using
      congr_arg (σ • ·) h

/-- Coprimality of the Stickelberger product `α ^ γ` to `B` is equivalent to coprimality of `α`
to `(N B) 𝓞 K = ∏_σ σ • B`, since every exponent `c(σ)` in `[1, m)` is positive when `m ≥ 2`. -/
private theorem isCoprime_span_stickelbergerProduct_iff (hm : 2 ≤ m) [NeZero m] (B : Ideal (𝓞 K))
    (α : 𝓞 K) :
    IsCoprime (span {TauCeti.stickelbergerProduct m α}) B ↔
      IsCoprime (span {α}) (span {(absNorm B : 𝓞 K)}) := by
  classical
  have : Fact (1 < m) := ⟨by omega⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have hspan : span {TauCeti.stickelbergerProduct m α} =
      ∏ σ : Gal(K/ℚ), span {σ⁻¹ • α} ^ (galEquivZMod m K σ : ZMod m).val := by
    rw [TauCeti.stickelbergerProduct_def, ← prod_span_singleton]
    simp only [span_singleton_pow]
  rw [hspan, ← prod_smul_eq_span_absNorm B, IsCoprime.prod_left_iff, IsCoprime.prod_right_iff]
  refine ⟨fun h σ hσ ↦ ?_, fun h σ hσ ↦ ?_⟩
  · have hc : 0 < (galEquivZMod m K σ : ZMod m).val :=
      Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (Units.ne_zero _))
    have h1 := (IsCoprime.pow_left_iff hc).mp (h σ hσ)
    rwa [isCoprime_span_smul_iff, inv_inv] at h1
  · have hc : 0 < (galEquivZMod m K σ : ZMod m).val :=
      Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (Units.ne_zero _))
    rw [IsCoprime.pow_left_iff hc, isCoprime_span_smul_iff, inv_inv]
    exact h σ hσ

/-- **The residue symbol of the Stickelberger product at an ideal.** In the `m`-th cyclotomic
field with `m ≥ 2`, for every ideal `B` of `𝓞 K` and every `α : 𝓞 K`,
`(α ^ γ / B)_m = (α / (N B) 𝓞 K)_m`. The bound `2 ≤ m` is sharp: at `m = 1`, `α ^ γ = 1` for
`α = 0`, whereas `(0 / (N B) 𝓞 K)_1 = 0` at any proper nonzero ideal `B`. -/
theorem powerResidueSymbolIdeal_stickelbergerProduct (hm : 2 ≤ m) [NeZero m] (B : Ideal (𝓞 K))
    (α : 𝓞 K) :
    powerResidueSymbolIdeal B m (Quotient.mk B (TauCeti.stickelbergerProduct m α)) =
      powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) m
        (Quotient.mk (span {(absNorm B : 𝓞 K)}) α) := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm B : 𝓞 K)})
  · obtain rfl | hB := eq_or_ne B ⊥
    · -- At `⊥`, coprimality forces `α` and `α ^ γ` to be units of `𝓞 K ⧸ ⊥`, so both give `1`.
      have hcop' : IsCoprime (span {TauCeti.stickelbergerProduct m α}) ⊥ :=
        (isCoprime_span_stickelbergerProduct_iff hm ⊥ α).mpr hcop
      have hu1 : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) (TauCeti.stickelbergerProduct m α)) :=
        Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop')
      have hu2 : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) α) :=
        Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp (by simpa using hcop))
      rw [absNorm_bot, Nat.cast_zero, span_singleton_zero, powerResidueSymbolIdeal_bot,
        MulChar.one_apply hu1, MulChar.one_apply hu2]
    · have hsmul_ne (σ : Gal(K/ℚ)) : σ • B ≠ ⊥ := by
        rw [pointwise_smul_def]
        exact (map_eq_bot_iff_of_injective
          (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ).injective).not.mpr hB
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [← prod_smul_eq_span_absNorm B] at hcop ⊢
      rw [TauCeti.stickelbergerProduct_def, map_prod, map_prod,
        powerResidueSymbolIdeal_prod_right Finset.univ (fun σ : Gal(K/ℚ) ↦ σ • B)
          (fun σ _ ↦ hsmul_ne σ) α]
      refine Finset.prod_congr rfl fun σ _ ↦ ?_
      have hcopσ : IsCoprime (span {σ⁻¹ • α}) B := by
        rw [isCoprime_span_smul_iff, inv_inv]
        exact (IsCoprime.prod_right_iff.mp hcop) σ (Finset.mem_univ σ)
      have hu : IsUnit (Quotient.mk B (σ⁻¹ • α)) :=
        Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcopσ)
      have hpow1 : powerResidueSymbolIdeal B m (Quotient.mk B (σ⁻¹ • α)) ^ m = 1 :=
        powerResidueSymbolIdeal_pow_eq_one hu
      have hsmul : σ • powerResidueSymbolIdeal B m (Quotient.mk B (σ⁻¹ • α)) =
          powerResidueSymbolIdeal B m (Quotient.mk B (σ⁻¹ • α)) ^
            (galEquivZMod m K σ : ZMod m).val := by
        subst hk
        exact galEquivZMod_smul_of_pow_eq (k + 1) K σ hpow1
      let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
      have hmap := map_powerResidueSymbolIdeal (n := m) B τ (σ⁻¹ • α)
      have hmapB : B.map τ = σ • B := by rw [pointwise_smul_def]; rfl
      rw [map_pow, map_pow, ← hsmul]
      rw [show τ (powerResidueSymbolIdeal B m (Quotient.mk B (σ⁻¹ • α))) =
          σ • powerResidueSymbolIdeal B m (Quotient.mk B (σ⁻¹ • α)) from rfl,
        show τ (σ⁻¹ • α) = α from smul_inv_smul σ α, hmapB] at hmap
      exact hmap
  · have hcop' : ¬ IsCoprime (span {TauCeti.stickelbergerProduct m α}) B :=
      mt (isCoprime_span_stickelbergerProduct_iff hm B α).mp hcop
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop',
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop]

/-- **The residue symbol of the Stickelberger product at a maximal ideal.** -/
theorem powerResidueSymbol_stickelbergerProduct (hm : 2 ≤ m) [NeZero m] (P : Ideal (𝓞 K))
    [P.IsMaximal] (α : 𝓞 K) :
    powerResidueSymbol P m (Quotient.mk P (TauCeti.stickelbergerProduct m α)) =
      powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) m
        (Quotient.mk (span {(absNorm P : 𝓞 K)}) α) := by
  rw [← powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_stickelbergerProduct hm P α]

end StickelbergerProduct

end Ideal

/-! ### Eisenstein reciprocity at the norm of an ideal and at rational integers -/

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `α ∈ 𝓞 K` a
primary integer of `ℚ(ζ_p)`, and `B` an ideal of `𝓞 K` whose norm is prime to `p`. Then
`(α / (N B) 𝓞 K)_p = (N B / α 𝓞 K)_p`. -/
theorem eisenstein_reciprocity_absNorm (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {B : Ideal (𝓞 K)}
    (hB : (absNorm B).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(absNorm B : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p
        (Ideal.Quotient.mk (span {α}) (absNorm B : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm B : 𝓞 K)})
  · have hAB : (absNorm (span {α})).Coprime (absNorm B) :=
      absNorm_coprime_of_isCoprime_span_natCast hcop
    have hΦ := powerResidueSymbolIdeal_stickelbergerPhi (span {α}) B hB hAB hp.two_le
    have hprod := powerResidueSymbolIdeal_stickelbergerProduct hp.two_le B α
    rcases hζ.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα with hsign | hsign
    · rw [hsign] at hΦ
      exact hprod.symm.trans hΦ
    · rw [hsign, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)] at hΦ
      exact hprod.symm.trans hΦ
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]

/-- Two elements of a commutative ring whose `p`-th powers are `1` and whose `f`-th powers agree
are equal whenever `gcd(f, p) = 1`. -/
private theorem eq_of_pow_eq_of_coprime {R : Type*} [CommRing R] {x y : R} {f : ℕ}
    (hfp : f.Coprime p) (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x ^ f = y ^ f) :
    x = y := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let ux : Rˣ := Units.ofPowEqOne x p hx hp0
  let uy : Rˣ := Units.ofPowEqOne y p hy hp0
  have hxy_u : ux ^ f = uy ^ f := Units.ext (by simpa [ux, uy] using hxy)
  have hx_u : ux ^ p = 1 := Units.ext (by simp [ux])
  have hy_u : uy ^ p = 1 := Units.ext (by simp [uy])
  have huf : (ux * uy⁻¹) ^ f = 1 := by
    rw [mul_pow, inv_pow, hxy_u, mul_inv_cancel]
  have hup : (ux * uy⁻¹) ^ p = 1 := by
    rw [mul_pow, inv_pow, hx_u, hy_u, inv_one, mul_one]
  have hu1 : ux * uy⁻¹ = 1 := by
    simpa [hfp.gcd_eq_one] using pow_gcd_eq_one.mpr ⟨huf, hup⟩
  exact congr_arg Units.val (mul_inv_eq_one.mp hu1)

/-- Eisenstein reciprocity for a primary integer `α` and a natural prime `q` not divisible by
`p`. -/
private theorem eisenstein_reciprocity_natCast_prime (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {q : ℕ} (hq : q.Prime) (hqp : ¬ p ∣ q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have : Fact q.Prime := ⟨hq⟩
  have hqp_not_dvd : ¬ q ∣ p := fun h ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h ▸ dvd_rfl)
  let 𝔮 : Ideal ℤ := span {(q : ℤ)}
  have : 𝔮.IsMaximal := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ := (inferInstance : Nonempty (𝔮.primesOver (𝓞 K)))
  have h𝔮0 : 𝔮 ≠ ⊥ := by simp [𝔮, hq.ne_zero]
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮0 P
  have : P.IsMaximal := hPprime.isMaximal hP0
  set f := inertiaDeg P ℤ
  have hf_pos : 0 < f := inertiaDeg_pos P ℤ
  have hNP : absNorm P = q ^ f := (pow_inertiaDeg q P).symm
  have hPcop : (absNorm P).Coprime p := by
    rw [hNP]
    exact (hq.coprime_iff_not_dvd.mpr hqp_not_dvd).pow_left f
  -- `f = orderOf (q : ZMod p)` divides `#(ZMod p)ˣ = p - 1`, hence is `< p` and coprime to `p`.
  have hf_cop : f.Coprime p := by
    have hf_ord : f = orderOf (q : ZMod p) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P hqp_not_dvd
    let u : (ZMod p)ˣ := ZMod.unitOfCoprime q (hq.coprime_iff_not_dvd.mpr hqp_not_dvd)
    have hu : orderOf (q : ZMod p) = orderOf u := by
      simpa [u] using orderOf_units (y := u)
    have hdvd : f ∣ p - 1 := by
      rw [hf_ord, hu, ← Nat.totient_prime hp, ← ZMod.card_units_eq_totient]
      exact orderOf_dvd_card
    have hlt : f < p :=
      lt_of_le_of_lt (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hdvd)
        (Nat.sub_lt hp.pos zero_lt_one)
    exact (hp.coprime_iff_not_dvd.mpr fun hpf ↦ not_le_of_gt hlt (Nat.le_of_dvd hf_pos hpf)).symm
  have hrec := hζ.eisenstein_reciprocity_absNorm hp2 hα hPcop
  rw [hNP, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right, map_pow, map_pow]
    at hrec
  by_cases hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  · have hux : IsUnit (Ideal.Quotient.mk (span {(q : 𝓞 K)}) α) :=
      Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop)
    have huy : IsUnit (Ideal.Quotient.mk (span {α}) (q : 𝓞 K)) :=
      Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm)
    exact eq_of_pow_eq_of_coprime hf_cop (powerResidueSymbolIdeal_pow_eq_one hux)
      (powerResidueSymbolIdeal_pow_eq_one huy) hrec
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]

/-- **Eisenstein reciprocity for natural numbers.** Let `p` be an odd prime, `α ∈ 𝓞 K` a primary
integer of `ℚ(ζ_p)`, and `n : ℕ` not divisible by `p`. Then `(α / n 𝓞 K)_p = (n / α 𝓞 K)_p`. -/
theorem eisenstein_reciprocity_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk (span {(n : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (n : 𝓞 K)) := by
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hnu =>
    rw [Nat.isUnit_iff.mp hnu, Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top,
      map_one, MulChar.map_one]
  | h₃ m q hm0 hq ih =>
    have hqp : q.Prime := Nat.prime_iff.mpr hq
    have hqm : ¬ p ∣ q ∧ ¬ p ∣ m :=
      ⟨fun h ↦ hn (dvd_mul_of_dvd_left h m), fun h ↦ hn (dvd_mul_of_dvd_right h q)⟩
    have hq_ne : span {(q : 𝓞 K)} ≠ ⊥ := by simp [hqp.ne_zero]
    have hm_ne : span {(m : 𝓞 K)} ≠ ⊥ := by simp [hm0]
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq_ne hm_ne,
      hζ.eisenstein_reciprocity_natCast_prime hp2 hα hqp hqm.1, ih hqm.2, map_mul, map_mul]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `α ∈ 𝓞 K` a primary integer of
`ℚ(ζ_p)`, and `a ∈ ℤ` an integer not divisible by `p`. Then `(α / a 𝓞 K)_p = (a / α 𝓞 K)_p`,
where the `p`-th power residue symbols are taken at the principal ideals `a 𝓞 K` and `α 𝓞 K`.
The integer `a` may be `±1`, negative, or composite, and if `(a)` and `(α)` are not coprime then
both sides vanish. -/
theorem eisenstein_reciprocity (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk (span {(a : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk (span {α}) (a : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have hna : ¬ p ∣ a.natAbs := by
    rwa [← Int.natCast_dvd]
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hna
  · rw [h, Int.cast_neg, Int.cast_natCast, span_singleton_neg, map_neg,
      powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2)]
    exact hζ.eisenstein_reciprocity_natCast hp2 hα hna

/-- **The Eisenstein reciprocity law**, with `a : ℤ` cast directly into `𝓞 K ⧸ span {α}` (matching
`Ideal.powerResidueSymbolIdeal_mul_right_intCast`). -/
theorem eisenstein_reciprocity_intCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk (span {(a : 𝓞 K)}) α) =
      powerResidueSymbolIdeal (span {α}) p (a : 𝓞 K ⧸ span {α}) := by
  simpa using hζ.eisenstein_reciprocity hp2 hα ha

/-! ### Shift under multiplication by `ζ_p` and the Wieferich criterion -/

/-- **Root-of-unity shift of Eisenstein reciprocity.** Replacing a primary element `α` by its
associate `ζ_p α` leaves `(n / (ζ_p α) 𝓞 K)_p = (n / α 𝓞 K)_p` unchanged while multiplying
`((ζ_p α) / n 𝓞 K)_p` by `(ζ_p / n 𝓞 K)_p = ζ_p ^ ((n ^ (p - 1) - 1) / p)` whenever `p ∤ n`. -/
theorem powerResidueSymbolIdeal_toInteger_mul_natCast (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(n : 𝓞 K)}) (hζ.toInteger * α)) =
      hζ.toInteger ^ ((n ^ (p - 1) - 1) / p) *
        powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
          (Ideal.Quotient.mk (span {hζ.toInteger * α}) (n : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have hnorm : absNorm (span {(n : 𝓞 K)}) = n ^ (p - 1) := by
    rw [absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.pos),
      Nat.totient_prime hp]
  have hncop : (absNorm (span {(n : 𝓞 K)})).Coprime p := by
    rw [hnorm]
    exact ((hp.coprime_iff_not_dvd.mpr hn).symm).pow_left (p - 1)
  have hspan : span {hζ.toInteger * α} = span {α} :=
    (span_singleton_eq_span_singleton.mpr
      ⟨(hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero).unit, by simp [mul_comm]⟩).symm
  rw [map_mul, map_mul,
    powerResidueSymbolIdeal_mk_of_pow_eq_one hncop hζ.toInteger_isPrimitiveRoot.pow_eq_one,
    hnorm, hζ.eisenstein_reciprocity_natCast hp2 hα hn]
  congr 1
  rw [hspan]

/-- **Wieferich criterion for the non-primary associate `ζ_p α`.** Let `p` be an odd prime, `α` a
primary integer of `ℚ(ζ_p)`, and `n : ℕ` with `p ∤ n` and `(α)` coprime to `(n)`. Then naive
reciprocity holds for the non-primary associate `ζ_p α` against `n` if and only if
`n ^ (p - 1) ≡ 1 (mod p²)`. In particular, the primary hypothesis in
`IsPrimitiveRoot.eisenstein_reciprocity` cannot be omitted. -/
theorem eisenstein_reciprocity_toInteger_mul_natCast_iff (hp2 : p ≠ 2) {α : 𝓞 K}
    (hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) {n : ℕ} (hn : ¬ p ∣ n)
    (hcop : IsCoprime (span {α}) (span {(n : 𝓞 K)})) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p
        (Ideal.Quotient.mk (span {(n : 𝓞 K)}) (hζ.toInteger * α)) =
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
        (Ideal.Quotient.mk (span {hζ.toInteger * α}) (n : 𝓞 K)) ↔
      n ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp : p.Prime := Fact.out
  have hn0 : n ≠ 0 := fun h ↦ hn (h ▸ dvd_zero p)
  have h1le : 1 ≤ n ^ (p - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn0)
  have hspan : span {hζ.toInteger * α} = span {α} :=
    (span_singleton_eq_span_singleton.mpr
      ⟨(hζ.toInteger_isPrimitiveRoot.isUnit hp.ne_zero).unit, by simp [mul_comm]⟩).symm
  have huy : IsUnit (Ideal.Quotient.mk (span {hζ.toInteger * α}) (n : 𝓞 K)) := by
    rw [hspan]
    exact Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm)
  have hypow :
      powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
        (Ideal.Quotient.mk (span {hζ.toInteger * α}) (n : 𝓞 K)) ^ p = 1 :=
    powerResidueSymbolIdeal_pow_eq_one huy
  have hyunit :
      IsUnit (powerResidueSymbolIdeal (span {hζ.toInteger * α}) p
        (Ideal.Quotient.mk (span {hζ.toInteger * α}) (n : 𝓞 K))) :=
    IsUnit.of_pow_eq_one hypow hp.ne_zero
  -- Fermat's little theorem: `p ∣ n ^ (p - 1) - 1`.
  have hfermat : p ∣ n ^ (p - 1) - 1 := by
    rw [← Nat.modEq_iff_dvd' h1le]
    simpa [Nat.totient_prime hp] using
      (Nat.ModEq.pow_totient (hp.coprime_iff_not_dvd.mpr hn).symm).symm
  rw [hζ.powerResidueSymbolIdeal_toInteger_mul_natCast hp2 hα hn, hyunit.mul_eq_right,
    hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd, Nat.ModEq.comm, Nat.modEq_iff_dvd' h1le, sq]
  exact ⟨fun h ↦ by
    obtain ⟨k, hk⟩ := hfermat
    rw [hk, Nat.mul_div_right _ hp.pos] at h
    obtain ⟨m, rfl⟩ := h
    exact ⟨m, by rw [hk]; ring⟩,
    fun ⟨m, hm⟩ ↦ ⟨m, by rw [hm, mul_assoc, Nat.mul_div_right _ hp.pos]⟩⟩

end IsPrimitiveRoot

/-! ### Explicit cubic instances and negative control -/

section Examples

open NumberField Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- In `ℤ[ω]`, `-1 - 3ω` is Eisenstein-primary (of norm `7`). -/
private theorem isEisensteinPrimary_neg_one_sub_three_mul {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    TauCeti.IsEisensteinPrimary hζ.toInteger (-1 - 3 * hζ.toInteger) := by
  have hdvd3 : (hζ.toInteger - 1) ^ 2 ∣ ((3 : ℤ) : 𝓞 K) :=
    (hζ.toInteger_sub_one_sq_dvd_intCast_iff (by decide)).mpr (dvd_refl 3)
  apply TauCeti.isEisensteinPrimary_iff.mpr
  refine ⟨hζ.isCoprime_toInteger_sub_one_iff.mpr fun h ↦ ?_, -1, ?_⟩
  · have h3ω : hζ.toInteger - 1 ∣ 3 * hζ.toInteger :=
      ((dvd_pow_self _ two_ne_zero).trans (by simpa using hdvd3)).mul_right hζ.toInteger
    have h1 : hζ.toInteger - 1 ∣ (-1 : 𝓞 K) := by
      convert dvd_add h h3ω using 1
      ring
    exact hζ.zeta_sub_one_prime'.not_isUnit (isUnit_of_dvd_unit h1 isUnit_neg_one)
  · obtain ⟨c, hc⟩ := hdvd3
    refine ⟨-c * hζ.toInteger, ?_⟩
    push_cast at hc ⊢
    linear_combination -hζ.toInteger * hc

/-- For `p = 3`, `π = -1 - 3ω` (primary of norm `7`), and `a = 2`, both cubic symbols `(π / 2)_3`
and `(2 / π)_3` equal `ω²`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    let π : 𝓞 K := -1 - 3 * hζ.toInteger
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) = hζ.toInteger ^ 2 ∧
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) = hζ.toInteger ^ 2 := by
  intro π
  have hprim := isEisensteinPrimary_neg_one_sub_three_mul hζ
  have hcyc : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 := by
    simpa [Polynomial.cyclotomic_three] using
      hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic (by decide)
  have hmk : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) π =
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (hζ.toInteger ^ 2) := by
    refine Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨-hζ.toInteger, ?_⟩)
    dsimp [π]
    linear_combination -hcyc
  have hnorm : absNorm (span {(2 : 𝓞 K)}) = 4 := by
    rw [show (2 : 𝓞 K) = ((2 : ℕ) : 𝓞 K) by norm_num, absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.finrank (n := 3) K
        (Polynomial.cyclotomic.irreducible_rat (n := 3) (by decide)),
      Nat.totient_prime Nat.prime_three]
    rfl
  have hval : powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
      hζ.toInteger ^ 2 := by
    rw [hmk, powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hnorm]; decide)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]),
      hnorm]
    norm_num
  refine ⟨hval, ?_⟩
  have hrec := hζ.eisenstein_reciprocity_natCast (by decide) hprim (n := 2) (by decide)
  rw [Nat.cast_ofNat] at hrec
  exact hrec.symm.trans hval

/-- At the ideal `B = 2 𝓞 K` of norm `4`, Eisenstein reciprocity at the norm gives
`(π / 4 𝓞 K)_3 = (4 / π 𝓞 K)_3 = ω` for `π = -1 - 3ω`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    let π : 𝓞 K := -1 - 3 * hζ.toInteger
    let B : Ideal (𝓞 K) := span {(2 : 𝓞 K)}
    powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ (absNorm B : 𝓞 K)) ∧
      powerResidueSymbolIdeal (span {(absNorm B : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) =
        hζ.toInteger := by
  intro π B
  have hprim := isEisensteinPrimary_neg_one_sub_three_mul hζ
  have hnorm : absNorm B = 4 := by
    dsimp [B]
    rw [show (2 : 𝓞 K) = ((2 : ℕ) : 𝓞 K) by norm_num, absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.finrank (n := 3) K
        (Polynomial.cyclotomic.irreducible_rat (n := 3) (by decide)),
      Nat.totient_prime Nat.prime_three]
    rfl
  refine ⟨hζ.eisenstein_reciprocity_absNorm (by decide) hprim (by rw [hnorm]; decide), ?_⟩
  have hcyc : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 := by
    simpa [Polynomial.cyclotomic_three] using
      hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic (by decide)
  have hmk : Ideal.Quotient.mk (span {(2 : 𝓞 K)}) π =
      Ideal.Quotient.mk (span {(2 : 𝓞 K)}) (hζ.toInteger ^ 2) := by
    refine Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨-hζ.toInteger, ?_⟩)
    dsimp [π]
    linear_combination -hcyc
  have h4 : (4 : 𝓞 K) = (2 : 𝓞 K) ^ 2 := by norm_num
  rw [hnorm, Nat.cast_ofNat, h4, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right, hmk,
    powerResidueSymbolIdeal_mk_of_pow_eq_one (by dsimp [B] at hnorm; rw [hnorm]; decide)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow])]
  dsimp [B] at hnorm
  rw [hnorm]
  norm_num
  calc (hζ.toInteger ^ 2) ^ 2 = hζ.toInteger ^ 3 * hζ.toInteger := by ring
    _ = hζ.toInteger := by rw [hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_mul]

/-- **Negative control: the primary hypothesis cannot be omitted.** Replacing the primary prime
`π = -1 - 3ω` by its non-primary associate `ω π` breaks reciprocity at `2`, because
`2 ^ (3 - 1) = 4 ≢ 1 (mod 9)`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    let π : 𝓞 K := -1 - 3 * hζ.toInteger
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ (hζ.toInteger * π)) ≠
      powerResidueSymbolIdeal (span {hζ.toInteger * π}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  intro π
  have hprim := isEisensteinPrimary_neg_one_sub_three_mul hζ
  have hcyc : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 := by
    simpa [Polynomial.cyclotomic_three] using
      hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic (by decide)
  -- `(2 + 3ω) π - 3 · 2 = 1` in `ℤ[ω]`, since `(2 + 3ω)(-1 - 3ω) = 7`.
  have hcop : IsCoprime (span {π}) (span {((2 : ℕ) : 𝓞 K)}) := by
    rw [isCoprime_span_singleton_iff]
    refine ⟨2 + 3 * hζ.toInteger, -3, ?_⟩
    dsimp [π]
    linear_combination -9 * hcyc
  have hiff := hζ.eisenstein_reciprocity_toInteger_mul_natCast_iff (by decide) hprim (by decide)
    hcop
  rw [Nat.cast_ofNat] at hiff
  rw [ne_eq, hiff]
  decide

/-- At the units `a = 1` and `a = -1`, both sides of Eisenstein reciprocity equal `1`. -/
example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {p} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ p) {α : 𝓞 L}
    (_hα : TauCeti.IsEisensteinPrimary hζ.toInteger α) :
    powerResidueSymbolIdeal (span {((1 : ℤ) : 𝓞 L)}) p (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ ((1 : ℤ) : 𝓞 L)) = 1 ∧
      powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 L)}) p (Ideal.Quotient.mk _ α) = 1 ∧
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ ((-1 : ℤ) : 𝓞 L)) = 1 := by
  have hp : p.Prime := Fact.out
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.cast_one, span_singleton_one, powerResidueSymbolIdeal_top]
  · rw [Int.cast_one, map_one, MulChar.map_one]
  · rw [Int.cast_neg, Int.cast_one, span_singleton_neg, span_singleton_one,
      powerResidueSymbolIdeal_top]
  · rw [Int.cast_neg, Int.cast_one, map_neg, powerResidueSymbolIdeal_neg (hp.odd_of_ne_two hp2),
      map_one, MulChar.map_one]

end Examples
