/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Lemmas
public import TauCeti.RingTheory.DividedPowers.PDFiltration

import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# PD-nilpotent divided power ideals and ordinary nilpotence

A divided power ideal `(I, hI)` of a commutative semiring `R` is *PD-nilpotent*
(`DividedPowers.IsPDNilpotent hI`) if its divided power filtration vanishes at some positive stage:
`hI.pdFiltration n = ⊥` for some `n > 0` (equivalently, for some `n : ℕ`, since `F⁰ = ⊤ = ⊥`
already implies `F¹ = ⊥`).

Because `I ^ n ≤ hI.pdFiltration n`, the chain of implications
`hI.IsPDNilpotent → IsNilpotent I → I ≤ nilradical R` holds unconditionally. Over a `ℚ`-algebra
(and more generally whenever `hI.dpow m x ∈ I ^ m` for all `m` and `x ∈ I`), PD-nilpotence
coincides with ordinary nilpotence `IsNilpotent I`. In particular, the divided power structures
`dividedPowersBot`, `OfInvertibleFactorial.dividedPowers`, `OfSquareZero.dividedPowers`,
`DividedPowers.IsNilpotent.dividedPowers`, and `DividedPowers.CharP.dividedPowers` are all
PD-nilpotent.

Unlike `IsNilpotent I`, PD-nilpotence can strictly fail even when `I ^ 2 = ⊥`: see
`TauCeti.RingTheory.DividedPowers.Padic` for the example `(2) ⊂ ZMod 4` with the divided power
structure induced from `PadicInt.dividedPowers 2`.

This file also develops a factorial-annihilation nilpotence criterion
(`DividedPowers.pow_eq_zero_of_factorial_eq_zero`, assuming `(n ! : R) = 0`, related to
`DividedPowers.nilpotent_of_mem_dpIdeal`, which assumes `∀ {y}, y ∈ I → n • y = 0`) and the
nilradical criterion: if `m ≠ 0` is a natural number that is nilpotent modulo `I` (or has some
power in `I`), then `I ≤ nilradical R` if and only if `(m : R)` is nilpotent in `R`. No primality
assumption on `m` is required.

## Main definitions

* `DividedPowers.IsPDNilpotent`: a divided power ideal `(I, hI)` is PD-nilpotent if
  `hI.pdFiltration n = ⊥` for some `n > 0`.

## Main results

* `DividedPowers.isPDNilpotent_iff`: unfolding characterization of `IsPDNilpotent`.
* `DividedPowers.isPDNilpotent_iff_exists_eq_bot`: equivalence with `∃ n, hI.pdFiltration n = ⊥`.
* `DividedPowers.IsPDNilpotent.isNilpotent`: PD-nilpotence implies ordinary nilpotence
  `IsNilpotent I`.
* `DividedPowers.IsPDNilpotent.le_nilradical`: PD-nilpotence implies `I ≤ nilradical R`.
* `DividedPowers.isPDNilpotent_of_eq_bot` and `DividedPowers.isPDNilpotent_iff_eq_bot`: any
  divided power structure on `⊥` is PD-nilpotent, and over a reduced ring `IsPDNilpotent ↔ I = ⊥`.
* `DividedPowers.IsPDNilpotent.map` and
  `DividedPowers.IsDPMorphism.isPDNilpotent_iff_of_injective`: functoriality along divided power
  morphisms with `I.map f = J` (no surjectivity needed; equivalence when `f` is injective).
* `DividedPowers.isPDNilpotent_iff_isNilpotent_of_pdFiltration_eq_pow` and
  `DividedPowers.isPDNilpotent_iff_isNilpotent_of_dpow_mem_pow`: general equivalence with
  `IsNilpotent I`.
* `DividedPowers.isPDNilpotent_iff_isNilpotent`: over a `ℚ`-algebra,
  `hI.IsPDNilpotent ↔ IsNilpotent I`.
* `DividedPowers.pow_eq_zero_of_factorial_eq_zero`: if `(n ! : R) = 0`, then `x ^ n = 0` for
  every `x ∈ I`.
* `DividedPowers.pow_eq_zero_of_natCast_pow_eq_zero`: if `m ≠ 0` and `(m : R) ^ k = 0`, then
  `x ^ (m * k) = 0` for every `x ∈ I`.
* `DividedPowers.le_nilradical_of_isNilpotent_natCast`: if `m ≠ 0` and `(m : R)` is nilpotent,
  then `I ≤ nilradical R`.
* `DividedPowers.le_nilradical_iff_isNilpotent_natCast` and
  `DividedPowers.le_nilradical_iff_isNilpotent_of_quotient`: if `m ≠ 0` has a power in `I` (or is
  nilpotent in `R ⧸ I`), then `I ≤ nilradical R ↔ IsNilpotent (m : R)`.

## References

* Mathlib's `DividedPowers` formalization by A. Chambert-Loir and M. I. de Frutos-Fernández.
* [Stacks Project, Section 60.5 (Tag 07HL)](https://stacks.math.columbia.edu/tag/07HL),
  Definition 60.5.2 (Tag 07HM).
* [Stacks Project, Section 60.7 (Tag 07I1)](https://stacks.math.columbia.edu/tag/07I1),
  observation before Situation 60.7.5 (Tag 07MF).
* [Stacks Project, Section 23.2 (Tag 07GR)](https://stacks.math.columbia.edu/tag/07GR),
  Lemma 23.2.6.
-/

public section

namespace DividedPowers

section PDNilpotent

variable {R : Type*} [CommSemiring R] {I : Ideal R} (hI : DividedPowers I)

/-- A divided power ideal `(I, hI)` is *PD-nilpotent* if its divided power filtration vanishes at
some positive stage `n > 0`. -/
def IsPDNilpotent : Prop :=
  ∃ n : ℕ, 0 < n ∧ hI.pdFiltration n = ⊥

/-- Unfolding characterization of `DividedPowers.IsPDNilpotent`. -/
theorem isPDNilpotent_iff : hI.IsPDNilpotent ↔ ∃ n : ℕ, 0 < n ∧ hI.pdFiltration n = ⊥ :=
  (Iff.rfl)

/-- A divided power ideal is PD-nilpotent if and only if *some* filtration step (including possibly
step `0`, in the zero ring) vanishes. -/
theorem isPDNilpotent_iff_exists_eq_bot :
    hI.IsPDNilpotent ↔ ∃ n : ℕ, hI.pdFiltration n = ⊥ := by
  rw [isPDNilpotent_iff]
  constructor
  · rintro ⟨n, -, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    rcases eq_or_ne n 0 with rfl | hne
    · refine ⟨1, Nat.one_pos, eq_bot_iff.mpr ?_⟩
      exact (hI.pdFiltration_antitone (Nat.zero_le 1)).trans hn.le
    · exact ⟨n, Nat.pos_of_ne_zero hne, hn⟩

/-- If `hI.pdFiltration n = ⊥`, then the ordinary ideal power `I ^ n` vanishes. -/
theorem pow_eq_bot_of_pdFiltration_eq_bot {n : ℕ} (h : hI.pdFiltration n = ⊥) : I ^ n = ⊥ :=
  eq_bot_iff.mpr ((hI.pow_le_pdFiltration n).trans h.le)

/-- A PD-nilpotent divided power ideal is nilpotent as an ideal. -/
theorem IsPDNilpotent.isNilpotent {hI : DividedPowers I} (h : hI.IsPDNilpotent) :
    _root_.IsNilpotent I := by
  obtain ⟨n, -, hn⟩ := hI.isPDNilpotent_iff.mp h
  exact ⟨n, by rw [Ideal.zero_eq_bot, hI.pow_eq_bot_of_pdFiltration_eq_bot hn]⟩

/-- Every element of a PD-nilpotent divided power ideal is nilpotent: `I ≤ nilradical R`. -/
theorem IsPDNilpotent.le_nilradical {hI : DividedPowers I} (h : hI.IsPDNilpotent) :
    I ≤ nilradical R := by
  obtain ⟨n, hn⟩ := h.isNilpotent
  intro x hx
  refine mem_nilradical.mpr ⟨n, ?_⟩
  rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hn]
  exact Ideal.pow_mem_pow hx n

/-- Every divided power ideal in a subsingleton ring is PD-nilpotent. -/
@[simp]
theorem isPDNilpotent_of_subsingleton [Subsingleton R] : hI.IsPDNilpotent :=
  hI.isPDNilpotent_iff.mpr ⟨1, Nat.one_pos, Subsingleton.elim _ _⟩

/-- Any divided power structure on the zero ideal is PD-nilpotent (with bound `1`). -/
theorem isPDNilpotent_of_eq_bot (h : I = ⊥) : hI.IsPDNilpotent :=
  hI.isPDNilpotent_iff.mpr ⟨1, Nat.one_pos, by rw [pdFiltration_one, h]⟩

/-- The zero ideal equipped with `dividedPowersBot` is PD-nilpotent (with bound `1`). -/
@[simp]
theorem isPDNilpotent_bot (R : Type*) [CommSemiring R] :
    (dividedPowersBot R).IsPDNilpotent :=
  (dividedPowersBot R).isPDNilpotent_of_eq_bot rfl

/-- Over a reduced commutative semiring, a divided power ideal is PD-nilpotent if and only if it is
the zero ideal. -/
theorem isPDNilpotent_iff_eq_bot [IsReduced R] : hI.IsPDNilpotent ↔ I = ⊥ := by
  refine ⟨fun h ↦ eq_bot_iff.mpr ?_, hI.isPDNilpotent_of_eq_bot⟩
  simpa [Ideal.zero_eq_bot, nilradical_eq_zero R] using h.le_nilradical

section Map

variable {S : Type*} [CommSemiring S] {J : Ideal S} {hI : DividedPowers I} {hJ : DividedPowers J}

/-- PD-nilpotence pushes forward along a divided power morphism `f` satisfying `I.map f = J`.
No surjectivity hypothesis on `f` is required. -/
theorem IsPDNilpotent.map (h : hI.IsPDNilpotent) {f : R →+* S} (hf : IsDPMorphism hI hJ f)
    (hIJ : I.map f = J) : hJ.IsPDNilpotent := by
  obtain ⟨n, hnpos, hn⟩ := hI.isPDNilpotent_iff.mp h
  refine hJ.isPDNilpotent_iff.mpr ⟨n, hnpos, ?_⟩
  rw [← hf.map_pdFiltration_eq hIJ n, hn, Ideal.map_bot]

/-- Along an injective divided power morphism `f` with `I.map f = J`, PD-nilpotence of `(J, hJ)`
is equivalent to PD-nilpotence of `(I, hI)`. -/
theorem IsDPMorphism.isPDNilpotent_iff_of_injective {f : R →+* S} (hf : IsDPMorphism hI hJ f)
    (hIJ : I.map f = J) (hinj : Function.Injective f) :
    hJ.IsPDNilpotent ↔ hI.IsPDNilpotent := by
  simp only [isPDNilpotent_iff, ← hf.map_pdFiltration_eq hIJ,
    Ideal.map_eq_bot_iff_of_injective hinj]

/-- PD-nilpotence is invariant under transfer along a ring equivalence. -/
theorem isPDNilpotent_ofRingEquiv {e : R ≃+* S} (h : I.map e = J) (hI : DividedPowers I) :
    (ofRingEquiv h hI).IsPDNilpotent ↔ hI.IsPDNilpotent := by
  simp only [isPDNilpotent_iff, pdFiltration_ofRingEquiv h hI,
    Ideal.map_eq_bot_iff_of_injective e.injective]

end Map

section SpecialCases

/-- If the divided power filtration coincides with the ordinary ideal power filtration, then
PD-nilpotence is equivalent to ordinary ideal nilpotence. -/
theorem isPDNilpotent_iff_isNilpotent_of_pdFiltration_eq_pow
    (h : ∀ n : ℕ, hI.pdFiltration n = I ^ n) :
    hI.IsPDNilpotent ↔ _root_.IsNilpotent I := by
  constructor
  · exact IsPDNilpotent.isNilpotent
  · rintro ⟨n, hn⟩
    rw [isPDNilpotent_iff_exists_eq_bot]
    exact ⟨n, by rw [h n, ← Ideal.zero_eq_bot, hn]⟩

/-- If `hI.dpow m x ∈ I ^ m` for every `m ≥ 2` and `x ∈ I`, then `hI` is PD-nilpotent if and only
if `I` is nilpotent as an ideal. -/
theorem isPDNilpotent_iff_isNilpotent_of_dpow_mem_pow
    (h : ∀ m ≥ 2, ∀ x ∈ I, hI.dpow m x ∈ I ^ m) :
    hI.IsPDNilpotent ↔ _root_.IsNilpotent I :=
  hI.isPDNilpotent_iff_isNilpotent_of_pdFiltration_eq_pow
    (hI.pdFiltration_eq_pow_of_dpow_mem_pow h)

/-- Over a `ℚ`-algebra, PD-nilpotence is equivalent to ordinary ideal nilpotence. -/
theorem isPDNilpotent_iff_isNilpotent [Algebra ℚ R] :
    hI.IsPDNilpotent ↔ _root_.IsNilpotent I :=
  hI.isPDNilpotent_iff_isNilpotent_of_pdFiltration_eq_pow hI.pdFiltration_eq_pow

/-- For `OfInvertibleFactorial.dividedPowers`, the divided power ideal is PD-nilpotent. -/
theorem OfInvertibleFactorial.isPDNilpotent [DecidablePred (fun x : R ↦ x ∈ I)] {k : ℕ}
    (hk_fac : IsUnit ((k - 1).factorial : R)) (hkI : I ^ k = 0) :
    (OfInvertibleFactorial.dividedPowers hk_fac hkI).IsPDNilpotent :=
  (OfInvertibleFactorial.dividedPowers hk_fac hkI).isPDNilpotent_iff_exists_eq_bot.mpr
    ⟨k, OfInvertibleFactorial.pdFiltration_eq_bot hk_fac hkI le_rfl⟩

/-- For `OfSquareZero.dividedPowers` on a square-zero ideal `I`, the divided power ideal is
PD-nilpotent. -/
theorem OfSquareZero.isPDNilpotent [DecidablePred (fun x : R ↦ x ∈ I)] (hI2 : I ^ 2 = 0) :
    (OfSquareZero.dividedPowers hI2).IsPDNilpotent :=
  OfInvertibleFactorial.isPDNilpotent (by simp) hI2

/-- For `DividedPowers.IsNilpotent.dividedPowers`, the divided power ideal is PD-nilpotent. -/
theorem IsNilpotent.isPDNilpotent {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime]
    (hp : _root_.IsNilpotent (p : A)) {J : Ideal A} [DecidablePred (fun x ↦ x ∈ J)]
    (hJp : J ^ p = 0) :
    (DividedPowers.IsNilpotent.dividedPowers hp hJp).IsPDNilpotent :=
  OfInvertibleFactorial.isPDNilpotent _ hJp

/-- For `DividedPowers.CharP.dividedPowers`, the divided power ideal is PD-nilpotent. -/
theorem CharP.isPDNilpotent (A : Type*) [CommRing A] (p : ℕ) [_root_.CharP A p] [Fact p.Prime]
    {J : Ideal A} [DecidablePred (fun x ↦ x ∈ J)] (hJp : J ^ p = 0) :
    (DividedPowers.CharP.dividedPowers A p hJp).IsPDNilpotent :=
  IsNilpotent.isPDNilpotent _ hJp

end SpecialCases

end PDNilpotent

section NilradicalCriterion

variable {R : Type*} [CommSemiring R] {I : Ideal R}

/-- Factorial-annihilation nilpotence criterion: if `(n.factorial : R) = 0`, then `x ^ n = 0` for
every `x ∈ I`. This holds for all `n : ℕ` (including `n = 0`, where `R` is a subsingleton) and is
a related criterion to `DividedPowers.nilpotent_of_mem_dpIdeal` (which instead assumes
`∀ {y}, y ∈ I → n • y = 0`). -/
theorem pow_eq_zero_of_factorial_eq_zero (hI : DividedPowers I) {n : ℕ}
    (hn : (n.factorial : R) = 0) {x : R} (hx : x ∈ I) : x ^ n = 0 := by
  rw [← hI.factorial_mul_dpow_eq_pow hx, hn, zero_mul]

/-- If `m ≠ 0` and `(m : R) ^ k = 0`, then `x ^ (m * k) = 0` for every `x ∈ I`. -/
theorem pow_eq_zero_of_natCast_pow_eq_zero (hI : DividedPowers I) {m k : ℕ} (hm : m ≠ 0)
    (hk : (m : R) ^ k = 0) {x : R} (hx : x ∈ I) : x ^ (m * k) = 0 := by
  have hdvd : m ^ k ∣ (m * k).factorial := by
    calc m ^ k ∣ m.factorial ^ k :=
          pow_dvd_pow_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero hm) le_rfl) k
      _ = ∏ _ ∈ Finset.range k, m.factorial := by simp
      _ ∣ (∑ _ ∈ Finset.range k, m).factorial := Nat.prod_factorial_dvd_factorial_sum ..
      _ = (m * k).factorial := by simp [mul_comm]
  obtain ⟨c, hc⟩ := hdvd
  refine hI.pow_eq_zero_of_factorial_eq_zero ?_ hx
  rw [hc, Nat.cast_mul, Nat.cast_pow, hk, zero_mul]

/-- If a nonzero natural number `m` is nilpotent in `R`, then every divided power ideal of `R` is
contained in the nilradical of `R`. -/
theorem le_nilradical_of_isNilpotent_natCast (hI : DividedPowers I) {m : ℕ} (hm : m ≠ 0)
    (h : _root_.IsNilpotent (m : R)) : I ≤ nilradical R := by
  obtain ⟨k, hk⟩ := h
  intro x hx
  exact mem_nilradical.mpr ⟨m * k, hI.pow_eq_zero_of_natCast_pow_eq_zero hm hk hx⟩

/-- Let `(I, hI)` be a divided power ideal of a commutative semiring `R` and `m ≠ 0` a natural
number with some power `(m : R) ^ r ∈ I`. Then `I ≤ nilradical R` if and only if `(m : R)` is
nilpotent in `R` (Stacks Project, Tag 07GR). -/
theorem le_nilradical_iff_isNilpotent_natCast (hI : DividedPowers I) {m : ℕ} (hm : m ≠ 0)
    (hmem : ∃ r : ℕ, (m : R) ^ r ∈ I) :
    I ≤ nilradical R ↔ _root_.IsNilpotent (m : R) := by
  constructor
  · intro hle
    obtain ⟨r, hr⟩ := hmem
    exact (mem_nilradical.mp (hle hr)).of_pow
  · exact hI.le_nilradical_of_isNilpotent_natCast hm

/-- Quotient form of the nilradical criterion: if `(I, hI)` is a divided power ideal of a
commutative ring `R` and `m ≠ 0` is nilpotent in `R ⧸ I`, then `I ≤ nilradical R` if and only if
`(m : R)` is nilpotent in `R` (Stacks Project, Tag 07GR). -/
theorem le_nilradical_iff_isNilpotent_of_quotient {A : Type*} [CommRing A] {J : Ideal A}
    (hJ : DividedPowers J) {m : ℕ} (hm : m ≠ 0)
    (hq : _root_.IsNilpotent (Ideal.Quotient.mk J (m : A))) :
    J ≤ nilradical A ↔ _root_.IsNilpotent (m : A) := by
  refine hJ.le_nilradical_iff_isNilpotent_natCast hm ?_
  obtain ⟨r, hr⟩ := hq
  refine ⟨r, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hr
  exact hr

end NilradicalCriterion

end DividedPowers
