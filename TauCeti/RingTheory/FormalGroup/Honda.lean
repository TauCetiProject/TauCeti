/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
public import TauCeti.RingTheory.FormalGroup.Height.Classification
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
import TauCeti.RingTheory.FormalGroup.Hazewinkel.HeightIdeal
import TauCeti.RingTheory.FormalGroup.Hazewinkel.NSMul
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Honda's formal group law of height `h`

Fix a prime `p` and a positive integer `h : ℕ+`. **Honda's formal group law** of height `h`
(`TauCeti.hondaFormalGroup p h R`) is the specialization of Hazewinkel's integral formal group law
at `v_h = 1` and `v_i = 0` for `i ≠ h` (`Pi.single h 1`).

Over a `ℚ`-algebra `K`, its logarithm (`TauCeti.hondaLog p h K`) has the closed-form expansion

  `f_(p, h)(X) = ∑_{k ≥ 0} p⁻ᵏ X^(p^(k h))`,

characterized by Honda's functional equation `f_(p, h)(X) - p⁻¹ f_(p, h)(X^(p^h)) = X`.

Over an arbitrary commutative ring `R`, specializing Ravenel's modulo-`p` `[p]`-series formula to
the singleton support `{h}` gives

  `[p]_(H_h)(X) ≡ X^(p^h)  (mod p R⟦X⟧)`.

Consequently, over any commutative ring `R` of characteristic `p`:
* `[p]_(H_h)(X) = X^(p^h)`, and more generally `[p^k]_(H_h)(X) = X^(p^(k h))`.
* Because `H_h` has integer coefficients, it is fixed by every ring homomorphism, and in particular
  by iterated Frobenius; hence `X^(p^k)` defines an endomorphism
  `TauCeti.hondaIterateFrobeniusEnd p h R k` of `H_h` whose `h`-th iterate (`k = h`) is `[p]`.
* Over any field `K` of characteristic `p`, `H_h` has height `h`, so every nonzero height in `ℕ∞`
  is realized by a commutative formal group law over `K` (`FormalGroup.exists_height_eq`). Over a
  separably closed field `K` of characteristic `p`, Lazard's classification identifies `H_h` as the
  unique commutative formal group law of height `h` up to isomorphism
  (`FormalGroup.nonempty_formalGroupIso_hondaFormalGroup_iff`).

## Main definitions

* `TauCeti.hondaLog p h K`: the strict formal coordinate `∑_{k ≥ 0} p⁻ᵏ X^(p^(k h))` over a
  `ℚ`-algebra `K`.
* `TauCeti.hondaFormalGroup p h R`: Honda's commutative formal group law of height `h` over `R`.
* `TauCeti.hondaIterateFrobeniusEnd p h R k`, `TauCeti.hondaFrobeniusEnd p h R`: the Frobenius
  endomorphisms `X^(p^k)` and `X^p` of `hondaFormalGroup p h R` in characteristic `p`.

## Main results

* `TauCeti.hazewinkelLogCoeff_single_eq`, `TauCeti.coeff_hondaLog_pow_mul`: closed form `p⁻ᵏ` for
  the logarithm coefficients in degrees `p^(k h)`, and vanishing in all other degrees.
* `TauCeti.hondaLog_sub_inv_smul_expand`: `f_(p, h)(X) - p⁻¹ f_(p, h)(X^(p^h)) = X`.
* `TauCeti.natCast_dvd_nsmulSeries_hondaFormalGroup_sub`:
  `p ∣ [p]_(H_h)(X) - X^(p^h)` in `R⟦X⟧`.
* `TauCeti.nsmulSeries_hondaFormalGroup_of_charP`,
  `TauCeti.nsmulSeries_pow_hondaFormalGroup_of_charP`: in characteristic `p`,
  `[p]_(H_h)(X) = X^(p^h)` and `[p^k]_(H_h)(X) = X^(p^(k h))`.
* `TauCeti.hondaIterateFrobeniusEnd_self`: the `h`-fold Frobenius endomorphism of `H_h` in
  characteristic `p` equals `[p]`.
* `TauCeti.heightIdeal_hondaFormalGroup_of_le`, `TauCeti.heightIdeal_hondaFormalGroup_of_lt`:
  `I_n(H_h) = (p)` for `1 ≤ n ≤ h` and `I_n(H_h) = ⊤` for `h < n`.
* `TauCeti.height_hondaFormalGroup`: over a field of characteristic `p`, `H_h` has height `h`.
* `FormalGroup.exists_height_eq`, `FormalGroup.nonempty_formalGroupIso_hondaFormalGroup_iff`:
  realization of every height `1 ≤ h ≤ ⊤`, and classification of height-`h` laws over separably
  closed fields by isomorphism to `H_h`.

## References

* T. Honda, *On the theory of commutative formal groups*, J. Math. Soc. Japan 22 (1970), 213–246.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §5 and Chapter IV.
* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.2.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Honda's logarithm -/

section Logarithm

variable {K L : Type*} [CommRing K] [Algebra ℚ K] [CommRing L] [Algebra ℚ L]

/-- **Honda's logarithm** of height `h` over a `ℚ`-algebra `K`: Hazewinkel's logarithm specialized
at `v_h = 1` and `v_i = 0` for `i ≠ h`. -/
def hondaLog (p : ℕ) (h : ℕ+) (K : Type*) [CommRing K] [Algebra ℚ K] : FormalCoordinate K :=
  hazewinkelLog p (Pi.single h (1 : K))

/-- Honda's logarithm is Hazewinkel's logarithm at `Pi.single h 1`. -/
theorem hondaLog_def (p : ℕ) (h : ℕ+) (K : Type*) [CommRing K] [Algebra ℚ K] :
    hondaLog p h K = hazewinkelLog p (Pi.single h (1 : K)) :=
  (rfl)

/-- Honda's logarithm is preserved by ring homomorphisms of `ℚ`-algebras. -/
@[simp]
theorem map_hondaLog (p : ℕ) (h : ℕ+) (φ : K →+* L) :
    FormalCoordinate.map φ (hondaLog p h K) = hondaLog p h L := by
  rw [hondaLog_def, hondaLog_def, map_hazewinkelLog]
  congr 1
  ext i
  simpa using Pi.apply_single (fun _ ↦ φ) (fun _ ↦ map_zero φ) h (1 : K) i

private theorem sum_hazewinkelLogCoeff_single_mul_pow {p : ℕ} (hp : p ≠ 0) (h : ℕ+) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), hazewinkelLogCoeff p (Pi.single h (1 : K)) i *
        (Pi.single h (1 : K) : ℕ+ → K) (n - i).succPNat ^ p ^ i =
      if (h : ℕ) ≤ n + 1 then hazewinkelLogCoeff p (Pi.single h (1 : K)) (n + 1 - (h : ℕ))
      else 0 := by
  by_cases hge : (h : ℕ) ≤ n + 1
  · rw [ite_eq_left hge, Finset.sum_eq_single (n + 1 - (h : ℕ))]
    · have heq : (n - (n + 1 - (h : ℕ))).succPNat = h := by
        apply PNat.eq
        rw [Nat.succPNat_coe]
        have := h.pos
        omega
      rw [heq, Pi.single_eq_same, one_pow, mul_one]
    · intro i hi hine
      rw [Finset.mem_range] at hi
      have hne : (n - i).succPNat ≠ h := by
        intro heq
        apply hine
        have hcoe := congrArg PNat.val heq
        rw [Nat.succPNat_coe] at hcoe
        omega
      rw [Pi.single_eq_of_ne hne, zero_pow (pow_ne_zero i hp), mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_range]
      have := h.pos
      omega
  · rw [ite_eq_right hge]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hne : (n - i).succPNat ≠ h := by
      intro heq
      have hcoe := congrArg PNat.val heq
      rw [Nat.succPNat_coe] at hcoe
      omega
    rw [Pi.single_eq_of_ne hne, zero_pow (pow_ne_zero i hp), mul_zero]

/-- Closed form for Hazewinkel's logarithm coefficients at `Pi.single h 1`: for `p ≠ 0`, `mₙ` is
`p⁻ᵏ` when `n = k h`, and `0` otherwise. -/
theorem hazewinkelLogCoeff_single_eq {p : ℕ} (hp : p ≠ 0) (h : ℕ+) (m : ℕ) :
    hazewinkelLogCoeff p (Pi.single h (1 : K)) m =
      if (h : ℕ) ∣ m then ((p : ℚ) ^ (m / (h : ℕ)))⁻¹ • (1 : K) else 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | n
    · simp
    · rw [hazewinkelLogCoeff_succ, sum_hazewinkelLogCoeff_single_mul_pow hp h n]
      rcases lt_or_ge (n + 1) (h : ℕ) with hlt | hge
      · rw [ite_eq_right (not_le_of_gt hlt), smul_zero,
          ite_eq_right (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hlt)]
      · rw [ite_eq_left hge, ih (n + 1 - (h : ℕ)) (by have := h.pos; omega)]
        have hdvd_iff : (h : ℕ) ∣ n + 1 ↔ (h : ℕ) ∣ n + 1 - (h : ℕ) := by
          conv_lhs => rw [← Nat.sub_add_cancel hge]
          exact Nat.dvd_add_self_right
        by_cases hdvd : (h : ℕ) ∣ n + 1
        · rw [ite_eq_left hdvd, ite_eq_left (hdvd_iff.mp hdvd), smul_smul]
          have hdiv : (n + 1) / (h : ℕ) = (n + 1 - (h : ℕ)) / (h : ℕ) + 1 := by
            conv_lhs => rw [← Nat.sub_add_cancel hge]
            exact Nat.add_div_right _ h.pos
          rw [hdiv, pow_succ, mul_inv_rev]
        · rw [ite_eq_right hdvd, ite_eq_right (mt hdvd_iff.mpr hdvd), smul_zero]

/-- For `p ≠ 0`, the `(k h)`-th Hazewinkel logarithm coefficient of `Pi.single h 1` is `p⁻ᵏ`. -/
@[simp]
theorem hazewinkelLogCoeff_single_mul {p : ℕ} (hp : p ≠ 0) (h : ℕ+) (k : ℕ) :
    hazewinkelLogCoeff p (Pi.single h (1 : K)) (k * (h : ℕ)) = ((p : ℚ) ^ k)⁻¹ • (1 : K) := by
  rw [hazewinkelLogCoeff_single_eq hp, ite_eq_left (dvd_mul_left _ _),
    Nat.mul_div_cancel k h.pos]

/-- For `p ≠ 0`, the `m`-th Hazewinkel logarithm coefficient of `Pi.single h 1` vanishes when
`h ∤ m`. -/
theorem hazewinkelLogCoeff_single_of_not_dvd {p : ℕ} (hp : p ≠ 0) (h : ℕ+) {m : ℕ}
    (hm : ¬ (h : ℕ) ∣ m) :
    hazewinkelLogCoeff p (Pi.single h (1 : K)) m = 0 := by
  rw [hazewinkelLogCoeff_single_eq hp, ite_eq_right hm]

/-- For `p > 1`, the coefficient of `X^(p^(k h))` in Honda's logarithm is `p⁻ᵏ`. -/
@[simp]
theorem coeff_hondaLog_pow_mul {p : ℕ} (hp : 1 < p) (h : ℕ+) (k : ℕ) :
    PowerSeries.coeff (p ^ (k * (h : ℕ))) (hondaLog p h K).toPowerSeries =
      ((p : ℚ) ^ k)⁻¹ • (1 : K) := by
  rw [hondaLog_def, coeff_hazewinkelLog_pow _ hp, hazewinkelLogCoeff_single_mul (by omega)]

/-- For `p > 1`, the coefficient of `X^m` in Honda's logarithm vanishes unless `m = p^(k h)` for
some `k`. -/
theorem coeff_hondaLog_eq_zero {p : ℕ} (hp : 1 < p) (h : ℕ+) {m : ℕ}
    (hm : ∀ k, p ^ (k * (h : ℕ)) ≠ m) :
    PowerSeries.coeff m (hondaLog p h K).toPowerSeries = 0 := by
  rw [hondaLog_def]
  by_cases hpow : ∃ n, p ^ n = m
  · obtain ⟨n, rfl⟩ := hpow
    rw [coeff_hazewinkelLog_pow _ hp]
    refine hazewinkelLogCoeff_single_of_not_dvd (by omega) h fun hdvd ↦ ?_
    obtain ⟨k, rfl⟩ := hdvd
    exact hm k (mul_comm (h : ℕ) k ▸ rfl)
  · push Not at hpow
    exact coeff_hazewinkelLog_eq_zero _ hpow

/-- **Honda's functional equation**: for `p > 1`,
`f_(p, h)(X) - p⁻¹ f_(p, h)(X^(p^h)) = X`. -/
theorem hondaLog_sub_inv_smul_expand {p : ℕ} (hp : 1 < p) (h : ℕ+) :
    (hondaLog p h K).toPowerSeries -
        (p : ℚ)⁻¹ • PowerSeries.expand (p ^ (h : ℕ)) (pow_ne_zero _ (by omega))
          (hondaLog p h K).toPowerSeries =
      PowerSeries.X := by
  ext m
  rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_X]
  by_cases hpow : ∃ k, p ^ (k * (h : ℕ)) = m
  · obtain ⟨k, rfl⟩ := hpow
    rcases k with _ | k
    · have hndvd : ¬ p ^ (h : ℕ) ∣ 1 :=
        Nat.not_dvd_of_pos_of_lt one_pos (Nat.one_lt_pow h.ne_zero hp)
      simp [hondaLog_def, PowerSeries.coeff_expand_of_not_dvd _ _ _ hndvd]
    · have hmul : p ^ ((k + 1) * (h : ℕ)) = p ^ (h : ℕ) * p ^ (k * (h : ℕ)) := by
        rw [← pow_add, add_mul, one_mul, add_comm]
      have hne1 : p ^ ((k + 1) * (h : ℕ)) ≠ 1 :=
        (Nat.one_lt_pow (Nat.mul_ne_zero (Nat.succ_ne_zero k) h.ne_zero) hp).ne'
      rw [ite_eq_right hne1, coeff_hondaLog_pow_mul hp, hmul, PowerSeries.coeff_expand_mul,
        coeff_hondaLog_pow_mul hp, smul_smul, pow_succ, mul_inv_rev, sub_self]
  · push Not at hpow
    have hne1 : m ≠ 1 := fun hm1 ↦ hpow 0 (by simp [hm1])
    rw [ite_eq_right hne1, coeff_hondaLog_eq_zero hp h hpow]
    by_cases hdvd : p ^ (h : ℕ) ∣ m
    · obtain ⟨q, rfl⟩ := hdvd
      rw [PowerSeries.coeff_expand_mul, coeff_hondaLog_eq_zero hp h, smul_zero, sub_zero]
      intro k hk
      refine hpow (k + 1) ?_
      rw [add_mul, one_mul, add_comm, pow_add, hk]
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hdvd, smul_zero, sub_zero]

end Logarithm

/-! ### Honda's integral formal group law -/

section FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [hp : Fact p.Prime] (h : ℕ+)

/-- **Honda's formal group law** of height `h` at `p` over a commutative ring `R`: the
specialization of Hazewinkel's integral formal group law at `v_h = 1` and `v_i = 0` for `i ≠ h`. -/
def hondaFormalGroup (R : Type*) [CommRing R] : FormalGroup R :=
  hazewinkelIntegralFormalGroup p (Pi.single h (1 : R))

/-- Honda's formal group law is `hazewinkelIntegralFormalGroup p (Pi.single h 1)`. -/
theorem hondaFormalGroup_def (R : Type*) [CommRing R] :
    hondaFormalGroup p h R = hazewinkelIntegralFormalGroup p (Pi.single h (1 : R)) :=
  (rfl)

/-- Honda's formal group law is commutative. -/
instance : (hondaFormalGroup p h R).IsComm := by
  rw [hondaFormalGroup_def]
  infer_instance

/-- Honda's formal group law commutes with arbitrary ring homomorphisms; in particular, when `R = S`
it is invariant under every ring endomorphism of `R`. -/
@[simp]
theorem map_hondaFormalGroup (φ : R →+* S) :
    (hondaFormalGroup p h R).map φ = hondaFormalGroup p h S := by
  rw [hondaFormalGroup_def, hondaFormalGroup_def, map_hazewinkelIntegralFormalGroup]
  congr 1
  ext i
  simpa using Pi.apply_single (fun _ ↦ φ) (fun _ ↦ map_zero φ) h (1 : R) i

/-- Over a `ℚ`-algebra, Honda's integral formal group law agrees with `hazewinkelFormalGroup` at
`Pi.single h 1`. -/
theorem hondaFormalGroup_eq_hazewinkelFormalGroup {K : Type*} [CommRing K] [Algebra ℚ K] :
    hondaFormalGroup p h K = hazewinkelFormalGroup p (Pi.single h (1 : K)) := by
  rw [hondaFormalGroup_def, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]

/-- Over a `ℚ`-algebra, the logarithm of Honda's formal group law is `hondaLog p h K`. -/
@[simp]
theorem log_hondaFormalGroup {K : Type*} [CommRing K] [Algebra ℚ K] :
    (hondaFormalGroup p h K).log = (hondaLog p h K).toPowerSeries := by
  rw [hondaFormalGroup_eq_hazewinkelFormalGroup, log_hazewinkelFormalGroup, ← hondaLog_def]

/-- **The `[p]`-series of Honda's formal group law modulo `p`.** Over any commutative ring `R`,
`p` divides `[p]_(H_h)(X) - X^(p^h)` in `R⟦X⟧`. -/
theorem natCast_dvd_nsmulSeries_hondaFormalGroup_sub :
    ((p : ℕ) : PowerSeries R) ∣
      (hondaFormalGroup p h R).nsmulSeries p - PowerSeries.X ^ p ^ (h : ℕ) := by
  have hv : ∀ i ∉ ({h} : Finset ℕ+), (Pi.single h (1 : R) : ℕ+ → R) i = 0 := fun _ hi ↦ by
    rw [Pi.single_eq_of_ne (Finset.notMem_singleton.mp hi)]
  have hdvd := natCast_dvd_nsmulSeries_hazewinkelIntegralFormalGroup_sub_of_support p hv
  simpa only [hondaFormalGroup_def, Finset.sum_singleton, Pi.single_eq_same,
    FormalGroup.toPowerSeries_monomialCurve, one_smul] using hdvd

/-- **The `[p]`-series of Honda's formal group law in characteristic `p`.** Over any commutative
ring `R` of characteristic `p`, `[p]_(H_h)(X) = X^(p^h)`. -/
@[simp]
theorem nsmulSeries_hondaFormalGroup_of_charP [CharP R p] :
    (hondaFormalGroup p h R).nsmulSeries p = PowerSeries.X ^ p ^ (h : ℕ) := by
  have hdvd := natCast_dvd_nsmulSeries_hondaFormalGroup_sub (R := R) p h
  have hp0 : ((p : ℕ) : PowerSeries R) = 0 := by
    rw [← map_natCast PowerSeries.C, CharP.cast_eq_zero R p, map_zero]
  rwa [hp0, zero_dvd_iff, sub_eq_zero] at hdvd

/-- Over any commutative ring `R` of characteristic `p`, `[p^k]_(H_h)(X) = X^(p^(k h))` for every
`k : ℕ`. -/
@[simp]
theorem nsmulSeries_pow_hondaFormalGroup_of_charP [CharP R p] (k : ℕ) :
    (hondaFormalGroup p h R).nsmulSeries (p ^ k) = PowerSeries.X ^ p ^ (k * (h : ℕ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hXp : PowerSeries.HasSubst (PowerSeries.X ^ p ^ (h : ℕ) : PowerSeries R) :=
      PowerSeries.HasSubst.of_constantCoeff_zero'
        (by rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ hp.out.ne_zero)])
    rw [pow_succ, (hondaFormalGroup p h R).nsmulSeries_mul, ih,
      nsmulSeries_hondaFormalGroup_of_charP, PowerSeries.subst_pow hXp, PowerSeries.subst_X hXp,
      ← pow_mul, ← pow_add, add_mul, one_mul, add_comm (h : ℕ)]

/-- **Iterated Frobenius endomorphism of Honda's formal group law**: in characteristic `p`, the
endomorphism of `hondaFormalGroup p h R` with underlying power series `X^(p^k)`. -/
def hondaIterateFrobeniusEnd (R : Type*) [CommRing R] [CharP R p] (k : ℕ) :
    FormalGroupHom (hondaFormalGroup p h R) (hondaFormalGroup p h R) where
  toPowerSeries := PowerSeries.X ^ (p ^ k)
  zero_constantCoeff := by simp [hp.out.ne_zero]
  hom := by
    have hhom := ((hondaFormalGroup p h R).iterateFrobeniusHom p k).hom
    rwa [FormalGroup.iterateFrobeniusHom_toPowerSeries, map_hondaFormalGroup] at hhom

/-- The underlying power series of `hondaIterateFrobeniusEnd p h R k` is `X^(p^k)`. -/
@[simp]
theorem hondaIterateFrobeniusEnd_toPowerSeries [CharP R p] (k : ℕ) :
    (hondaIterateFrobeniusEnd p h R k).toPowerSeries = PowerSeries.X ^ (p ^ k) :=
  (rfl)

/-- The `0`-th iterated Frobenius endomorphism of `hondaFormalGroup p h R` is the identity. -/
@[simp]
theorem hondaIterateFrobeniusEnd_zero [CharP R p] :
    hondaIterateFrobeniusEnd p h R 0 = FormalGroupHom.id (hondaFormalGroup p h R) := by
  ext : 1
  simp

/-- Iterated Frobenius endomorphisms of `hondaFormalGroup p h R` compose by adding exponents. -/
theorem hondaIterateFrobeniusEnd_add [CharP R p] (j k : ℕ) :
    hondaIterateFrobeniusEnd p h R (j + k) =
      (hondaIterateFrobeniusEnd p h R j).comp (hondaIterateFrobeniusEnd p h R k) := by
  ext : 1
  have hX : PowerSeries.HasSubst (PowerSeries.X ^ p ^ k : PowerSeries R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (by rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ hp.out.ne_zero)])
  rw [hondaIterateFrobeniusEnd_toPowerSeries, FormalGroupHom.comp_toPowerSeries,
    hondaIterateFrobeniusEnd_toPowerSeries, hondaIterateFrobeniusEnd_toPowerSeries,
    PowerSeries.subst_pow hX, PowerSeries.subst_X hX, ← pow_mul, ← pow_add, add_comm]

/-- **Frobenius endomorphism `S` of Honda's formal group law** in characteristic `p`, with
underlying power series `X^p`. -/
def hondaFrobeniusEnd (R : Type*) [CommRing R] [CharP R p] :
    FormalGroupHom (hondaFormalGroup p h R) (hondaFormalGroup p h R) :=
  hondaIterateFrobeniusEnd p h R 1

/-- `hondaFrobeniusEnd` is the first iterated Frobenius endomorphism. -/
theorem hondaFrobeniusEnd_def (R : Type*) [CommRing R] [CharP R p] :
    hondaFrobeniusEnd p h R = hondaIterateFrobeniusEnd p h R 1 :=
  (rfl)

/-- The underlying power series of `hondaFrobeniusEnd p h R` is `X^p`. -/
@[simp]
theorem hondaFrobeniusEnd_toPowerSeries [CharP R p] :
    (hondaFrobeniusEnd p h R).toPowerSeries = PowerSeries.X ^ p := by
  rw [hondaFrobeniusEnd_def, hondaIterateFrobeniusEnd_toPowerSeries, pow_one]

/-- In characteristic `p`, the `h`-fold Frobenius endomorphism `X^(p^h)` of `hondaFormalGroup p h R`
equals multiplication by `p` (`S^h = [p]`). -/
theorem hondaIterateFrobeniusEnd_self [CharP R p] :
    hondaIterateFrobeniusEnd p h R (h : ℕ) = (hondaFormalGroup p h R).nsmulHom p := by
  ext : 1
  simp

/-! ### Height ideals, height, and Lazard classification -/

/-- For `1 ≤ n ≤ h`, the `n`-th height ideal of `hondaFormalGroup p h R` is `(p)`. -/
theorem heightIdeal_hondaFormalGroup_of_le {n : ℕ} (hn : 0 < n) (hnh : n ≤ (h : ℕ)) :
    (hondaFormalGroup p h R).heightIdeal p n = Ideal.span {(p : R)} := by
  rw [hondaFormalGroup_def, heightIdeal_hazewinkelIntegralFormalGroup p _ hn]
  have hbot : Ideal.span ((Pi.single h (1 : R) : ℕ+ → R) '' {i : ℕ+ | (i : ℕ) < n}) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_ofPred_eq] at hi
    refine Pi.single_eq_of_ne ?_ _
    intro heq
    subst heq
    omega
  rw [hbot, sup_bot_eq]

/-- For `h < n`, the `n`-th height ideal of `hondaFormalGroup p h R` is the unit ideal `⊤`. -/
@[simp]
theorem heightIdeal_hondaFormalGroup_of_lt {n : ℕ} (hhn : (h : ℕ) < n) :
    (hondaFormalGroup p h R).heightIdeal p n = ⊤ := by
  rw [hondaFormalGroup_def, heightIdeal_hazewinkelIntegralFormalGroup p _ (h.pos.trans hhn),
    Ideal.eq_top_iff_one]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨h, hhn, by simp⟩)

/-- **Height of Honda's formal group law.** Over any field `K` of characteristic `p`,
`hondaFormalGroup p h K` has height `h`. -/
@[simp]
theorem height_hondaFormalGroup {K : Type*} [Field K] [CharP K p] :
    (hondaFormalGroup p h K).height p = (h : ℕ) := by
  rw [hondaFormalGroup_def, height_hazewinkelIntegralFormalGroup_eq_natCast_iff]
  exact ⟨fun i hi ↦ Pi.single_eq_of_ne hi.ne _, by simp⟩

end FormalGroup

end TauCeti

namespace FormalGroup

/-- **Every positive height is realized.** Over any field `K` of prime characteristic `p`, for
every `h : ℕ∞` with `1 ≤ h` there exists a commutative formal group law over `K` of height `h`
(namely `𝔾ₐ` for `h = ⊤` and `TauCeti.hondaFormalGroup p h K` for finite `h ≥ 1`). -/
theorem exists_height_eq {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] {h : ℕ∞}
    (hh : 1 ≤ h) :
    ∃ F : FormalGroup K, ∃ (_ : F.IsComm), F.height p = h := by
  cases h with
  | top => exact ⟨𝔾ₐ, inferInstance, height_𝔾ₐ⟩
  | coe m =>
    have hm : 0 < m := by exact_mod_cast hh
    let m' : ℕ+ := (m - 1).succPNat
    have hm' : (m' : ℕ) = m := by
      rw [Nat.succPNat_coe]
      omega
    exact ⟨TauCeti.hondaFormalGroup p m' K, inferInstance,
      by rw [TauCeti.height_hondaFormalGroup, hm']⟩

/-- **Classification by Honda's formal group laws.** Over a separably closed field `K` of prime
characteristic `p`, a commutative formal group law `F` has finite height `h : ℕ+` if and only if
`F` is isomorphic to `TauCeti.hondaFormalGroup p h K`. -/
theorem nonempty_formalGroupIso_hondaFormalGroup_iff {K : Type*} [Field K] [IsSepClosed K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (F : FormalGroup K) [F.IsComm] (h : ℕ+) :
    Nonempty (TauCeti.FormalGroupIso F (TauCeti.hondaFormalGroup p h K)) ↔
      F.height p = (h : ℕ) := by
  rw [← height_eq_height_iff_nonempty_formalGroupIso (p := p),
    TauCeti.height_hondaFormalGroup]

end FormalGroup
