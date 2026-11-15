/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Separable
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Ore's conditions on the wild exponent of a totally ramified extension

Let `K` be a nonarchimedean local field and let `σ_K(n) = totallyRamifiedOfDegree K n` be the set
of totally ramified extensions of `K` of degree `n` inside a fixed separable closure. Every
`E ∈ σ_K(n)` has discriminant exponent `d(E) = n - 1 + c(E)`, where `c(E) = E.wildExponent` is the
wild exponent. Not every natural number `j` occurs as `c(E)`: Ore's conditions characterize the
admissible values of `j` in terms of Euclidean division `j = (j / n) * n + j % n` and the
normalized valuation on `𝒪[K]`.

Writing `a = j / n` and `b = j % n`, a wild exponent `j` is *Ore-admissible* in positive degree `n`
when either:
* `b = 0` and `a = v_K(n)` in `ℕ∞` (so `(n : K) ≠ 0` and `j = n * v_K(n)`), or
* `0 < b`, `v_K(b) ≤ a` and `a + 1 ≤ v_K(n)` in `ℕ∞`.

Using the discrete valuation `IsDiscreteValuationRing.addVal 𝒪[K]` valued in `ℕ∞` handles mixed
and equal characteristic uniformly: an integer vanishing in `K` has valuation `⊤`, so when
`(n : K) = 0` the first branch is impossible while the upper bound `a + 1 ≤ ⊤` of the second
branch is vacuous, leaving `((j % n : ℕ) : K) ≠ 0` as the sole condition (`p ∤ j` in characteristic
`p` when `p ∣ n`). Including `0 < n` in `TauCeti.IsOreAdmissible` excludes `n = 0`, where
`σ_K(0) = ∅`, so `TauCeti.ore_realizability` holds for every `n` and `j` without side conditions.

## Main definitions

* `TauCeti.IsOreAdmissible K n j`: Ore's admissibility predicate on degree `n` and wild exponent
  `j`.
* `TauCeti.oreCoefficientDepth K n j h`: the minimal valuation depth `ν_h` imposed on the `h`-th
  Eisenstein coefficient by wild exponent at least `j`.

## Main results

* `TauCeti.isOreAdmissible_iff_min_le_and_le`: Ore's double-inequality form
  `min (n • v_K(j % n)) (n • v_K(n)) ≤ j ≤ n • v_K(n)` in `ℕ∞`.
* `TauCeti.isOreAdmissible_iff_of_natCast_eq_zero`: in equal characteristic `p` with `p ∣ n`, `j`
  is admissible if and only if `(j % n : K) ≠ 0`.
* `TauCeti.iInf_eisenstein_derivative_eq_iff`: characterizes when the derivative-term valuation
  minimum of an Eisenstein polynomial equals `n - 1 + j` in terms of `IsOreAdmissible` and
  `oreCoefficientDepth`.
* `TauCeti.separable_map_iff_iInf_eisenstein_derivative_ne_top`: an Eisenstein polynomial of
  positive degree maps to a separable polynomial over `K` if and only if its derivative-term
  valuation minimum is finite.
* `TauCeti.ore_realizability`: some `E ∈ totallyRamifiedOfDegree K n` has `E.wildExponent = j` if
  and only if `IsOreAdmissible K n j`.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8; *Newtonsche
  Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928), 84–117.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `p`-adique*, Colloq. Internat.
  CNRS **143** (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing TauCeti.Polynomial
open scoped IntermediateField

namespace TauCeti

section DiscreteValuation

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **Ore's conditions** on degree `n` and wild exponent `j`. Writing `a = j / n` and `b = j % n`,
`j` is admissible when `0 < n` and either `b = 0` with `a = v_K(n)`, or `0 < b` with `v_K(b) ≤ a`
and `a + 1 ≤ v_K(n)` in `ℕ∞`. -/
def IsOreAdmissible (n j : ℕ) : Prop :=
  0 < n ∧
    ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] n) ∨
      (0 < j % n ∧ addVal 𝒪[K] (j % n : ℕ) ≤ ((j / n : ℕ) : ℕ∞) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] n))

variable (K) in
/-- Explicit definition of `IsOreAdmissible`. -/
theorem isOreAdmissible_def (n j : ℕ) :
    IsOreAdmissible K n j ↔
      0 < n ∧
        ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] n) ∨
          (0 < j % n ∧ addVal 𝒪[K] (j % n : ℕ) ≤ ((j / n : ℕ) : ℕ∞) ∧
            ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] n)) :=
  Iff.rfl

/-- An Ore-admissible degree is positive. -/
theorem IsOreAdmissible.pos {n j : ℕ} (h : IsOreAdmissible K n j) : 0 < n := h.1

/-- Degree zero has no Ore-admissible wild exponents. -/
@[simp]
theorem not_isOreAdmissible_zero (j : ℕ) : ¬ IsOreAdmissible K 0 j := fun h ↦ h.pos.false

/-- Unfolding `IsOreAdmissible` in positive degree. -/
theorem isOreAdmissible_iff_of_pos {n : ℕ} (hn : 0 < n) {j : ℕ} :
    IsOreAdmissible K n j ↔
      (j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] n) ∨
        (0 < j % n ∧ addVal 𝒪[K] (j % n : ℕ) ≤ ((j / n : ℕ) : ℕ∞) ∧
          ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] n) :=
  and_iff_right hn

/-- In degree `1`, only wild exponent `0` is Ore-admissible. -/
@[simp]
theorem isOreAdmissible_one_iff {j : ℕ} : IsOreAdmissible K 1 j ↔ j = 0 := by
  simp [isOreAdmissible_iff_of_pos zero_lt_one, Nat.mod_one]

/-- If `j` is Ore-admissible for `n` and `j % n = 0`, then `n` is nonzero in `K`. -/
theorem IsOreAdmissible.natCast_ne_zero_of_mod_eq_zero {n j : ℕ} (h : IsOreAdmissible K n j)
    (hb : j % n = 0) : (n : K) ≠ 0 := by
  rcases h.2 with ⟨_, ha⟩ | ⟨hb', -⟩
  · intro hn0
    rw [show (n : 𝒪[K]) = 0 from Subtype.ext (by simpa using hn0), addVal_zero] at ha
    exact ENat.natCast_ne_top _ ha
  · exact absurd hb hb'.ne'

/-- If `j` is Ore-admissible for `n` and `j % n ≠ 0`, then `j % n` is nonzero in `K`. -/
theorem IsOreAdmissible.natCast_mod_ne_zero {n j : ℕ} (h : IsOreAdmissible K n j)
    (hb : j % n ≠ 0) : ((j % n : ℕ) : K) ≠ 0 := by
  rcases h.2 with ⟨hb0, _⟩ | ⟨_, hle, _⟩
  · exact absurd hb0 hb
  · intro hb0
    rw [show ((j % n : ℕ) : 𝒪[K]) = 0 from Subtype.ext (by simpa using hb0), addVal_zero] at hle
    exact ENat.natCast_ne_top _ (top_le_iff.mp hle)

/-- **Ore's double-inequality characterization**: `IsOreAdmissible K n j` is equivalent to `0 < n`
together with `min (n • v_K(j % n)) (n • v_K(n)) ≤ j ≤ n • v_K(n)` in `ℕ∞`. Because `v_K(0) = ⊤`,
the case `j % n = 0` collapses to `j = n • v_K(n)`. -/
theorem isOreAdmissible_iff_min_le_and_le {n j : ℕ} :
    IsOreAdmissible K n j ↔
      0 < n ∧
        min (n • addVal 𝒪[K] (j % n : ℕ)) (n • addVal 𝒪[K] n) ≤ (j : ℕ∞) ∧
          (j : ℕ∞) ≤ n • addVal 𝒪[K] n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hntop : n • (⊤ : ℕ∞) = ⊤ := by rw [nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.mpr hn.ne')]
  rw [isOreAdmissible_iff_of_pos hn, and_iff_right hn]
  have hjdiv : (j / n) * n + j % n = j := Nat.div_add_mod' j n
  have hbmod : j % n < n := Nat.mod_lt j hn
  rcases (j % n).eq_zero_or_pos with hb0 | hbpos
  · rw [hb0, Nat.cast_zero, addVal_zero, hntop, min_top_left]
    simp only [true_and, lt_irrefl, false_and, or_false, ← le_antisymm_iff]
    rw [hb0, add_zero] at hjdiv
    induction addVal 𝒪[K] n with
    | top => simp [hntop]
    | coe v =>
      rw [nsmul_eq_mul, ← ENat.natCast_mul, Nat.cast_inj, Nat.cast_inj]
      exact ⟨fun h ↦ by rw [← hjdiv, h, mul_comm],
        fun h ↦ Nat.eq_of_mul_eq_mul_left hn (by linarith)⟩
  · have hvn_iff : ((j : ℕ∞) ≤ n • addVal 𝒪[K] n ↔ ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] n) ∧
        (((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] n → (j : ℕ∞) < n • addVal 𝒪[K] n) := by
      induction addVal 𝒪[K] n with
      | top => simp [hntop]
      | coe v =>
        rw [nsmul_eq_mul, ← ENat.natCast_mul, ← ENat.natCast_one, ← ENat.natCast_add,
          Nat.cast_le, Nat.cast_le, Nat.cast_lt]
        exact ⟨⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩, fun h ↦ by nlinarith⟩
    simp only [hbpos.ne', false_and, hbpos, true_and, false_or, hvn_iff.1]
    refine ⟨fun ⟨hbv, hnv⟩ ↦ ⟨min_le_of_left_le ?_, hnv⟩, fun ⟨hmin, hnv⟩ ↦ ⟨?_, hnv⟩⟩
    · refine (nsmul_le_nsmul_right hbv n).trans ?_
      rw [nsmul_eq_mul, ← ENat.natCast_mul, Nat.cast_le]
      nlinarith
    · have hble : n • addVal 𝒪[K] (j % n : ℕ) ≤ (j : ℕ∞) := by
        rcases min_cases (n • addVal 𝒪[K] (j % n : ℕ)) (n • addVal 𝒪[K] n) with ⟨h, _⟩ | ⟨h, _⟩
        · rwa [h] at hmin
        · exact absurd (h ▸ hmin) (hvn_iff.2 hnv).not_ge
      induction hvb : addVal 𝒪[K] (j % n : ℕ) with
      | top => rw [hvb, hntop] at hble; exact absurd hble (not_le_of_gt (ENat.natCast_lt_top j))
      | coe u =>
        rw [hvb, nsmul_eq_mul, ← ENat.natCast_mul, Nat.cast_le] at hble
        exact_mod_cast (by nlinarith : u ≤ j / n)

/-- In positive characteristic `p` when `p ∣ n` (that is, `0 < n` and `(n : K) = 0`), a wild
exponent `j` is Ore-admissible if and only if `(j % n : K) ≠ 0`. -/
theorem isOreAdmissible_iff_of_natCast_eq_zero {n j : ℕ} (hn : 0 < n) (hnK : (n : K) = 0) :
    IsOreAdmissible K n j ↔ ((j % n : ℕ) : K) ≠ 0 := by
  have hn𝒪 : (n : 𝒪[K]) = 0 := Subtype.ext (by simpa using hnK)
  have hchar : ringChar K ≠ 0 := fun h0 ↦ by
    have : CharZero K := @CharP.charP_to_charZero K _ (h0 ▸ ringChar.of_eq rfl)
    exact hn.ne' (Nat.cast_eq_zero.mp hnK)
  have hp : (ringChar K).Prime := CharP.char_prime_of_ne_zero K hchar
  refine ⟨fun h hb0 ↦ ?_, fun hbK ↦ ?_⟩
  · rcases (j % n).eq_zero_or_pos with hb | hb
    · exact h.natCast_ne_zero_of_mod_eq_zero hb hnK
    · exact h.natCast_mod_ne_zero hb.ne' hb0
  · rw [isOreAdmissible_iff_of_pos hn]
    set b := j % n
    have hbpos : 0 < b := Nat.pos_of_ne_zero fun h0 ↦ hbK (by simp [h0])
    have hcop : IsCoprime ((ringChar K : ℕ) : 𝒪[K]) ((b : ℕ) : 𝒪[K]) := by
      simpa only [map_natCast] using (Nat.isCoprime_iff_coprime.mpr
        (hp.coprime_iff_not_dvd.mpr fun hd ↦ hbK ((ringChar.spec K b).mpr hd))).map
          (Int.castRingHom 𝒪[K])
    have hp0 : ((ringChar K : ℕ) : 𝒪[K]) = 0 :=
      Subtype.ext (by push_cast; exact ringChar.Nat.cast_ringChar (R := K))
    rw [hp0] at hcop
    have hu : IsUnit ((b : ℕ) : 𝒪[K]) := isCoprime_zero_left.mp hcop
    exact .inr ⟨hbpos, by rw [addVal_eq_zero_iff.mpr hu]; exact zero_le,
      by rw [hn𝒪, addVal_zero]; exact le_top⟩

variable (K) in
/-- **Ore's coefficient depth** `ν_h = max 1 (a + 1 + [h < b] - v_K(h))` at index `h`, where
`a = j / n` and `b = j % n`. The subtraction takes place in `ℕ∞`, so when `(h : K) = 0` we have
`v_K(h) = ⊤` and the depth is `1`, reflecting that `X ^ h` has zero derivative. -/
def oreCoefficientDepth (n j h : ℕ) : ℕ :=
  max 1 (((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal 𝒪[K] h).toNat

variable (K) in
/-- Explicit definition of `oreCoefficientDepth`. -/
theorem oreCoefficientDepth_def (n j h : ℕ) :
    oreCoefficientDepth K n j h =
      max 1 (((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal 𝒪[K] h).toNat :=
  (rfl)

/-- Every Ore coefficient depth is at least `1`. -/
theorem one_le_oreCoefficientDepth {n j h : ℕ} : 1 ≤ oreCoefficientDepth K n j h := le_max_left _ _

/-- Every Ore coefficient depth is positive. -/
theorem oreCoefficientDepth_pos {n j h : ℕ} : 0 < oreCoefficientDepth K n j h :=
  one_le_oreCoefficientDepth

/-- Cast to `ℕ∞`, `oreCoefficientDepth` is `max 1 ((j / n + 1 + [h < j % n]) - v_K(h))`. -/
theorem natCast_oreCoefficientDepth {n j h : ℕ} :
    (oreCoefficientDepth K n j h : ℕ∞) =
      max 1 (((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal 𝒪[K] h) := by
  set d : ℕ∞ := ((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) - addVal 𝒪[K] h
  have hd : d ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) tsub_le_self
  rcases le_total 1 d.toNat with hle | hle
  · have hle' : (1 : ℕ∞) ≤ d := by rw [← ENat.natCast_toNat hd]; exact_mod_cast hle
    rw [oreCoefficientDepth, max_eq_right hle, max_eq_right hle', ENat.natCast_toNat hd]
  · have hle' : d ≤ 1 := by rw [← ENat.natCast_toNat hd]; exact_mod_cast hle
    rw [oreCoefficientDepth, max_eq_left hle, max_eq_left hle', Nat.cast_one]

/-- When `(h : K) = 0`, the `h`-th monomial contributes nothing to the derivative and its
coefficient depth is `1`. -/
@[simp]
theorem oreCoefficientDepth_of_natCast_eq_zero {n j h : ℕ} (hh : (h : K) = 0) :
    oreCoefficientDepth K n j h = 1 := by
  simp [oreCoefficientDepth, show (h : 𝒪[K]) = 0 from Subtype.ext (by simpa using hh)]

/-- At the remainder index `b = j % n` of an Ore-admissible pair `(n, j)` with `0 < b`, the
coefficient depth is `j / n + 1 - v_K(b)` without truncation below `1`. -/
theorem natCast_oreCoefficientDepth_mod {n j : ℕ} (h : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    (oreCoefficientDepth K n j (j % n) : ℕ∞) =
      ((j / n + 1 : ℕ) : ℕ∞) - addVal 𝒪[K] (j % n : ℕ) := by
  rcases h.2 with ⟨hb0, _⟩ | ⟨_, hbv, _⟩
  · exact absurd hb0 hb.ne'
  rw [natCast_oreCoefficientDepth, ite_eq_right (lt_irrefl _), add_zero]
  refine max_eq_right ?_
  induction hvb : addVal 𝒪[K] (j % n : ℕ) with
  | top => rw [hvb] at hbv; exact absurd hbv (not_le_of_gt (ENat.natCast_lt_top _))
  | coe v =>
    have hv : v ≤ j / n := by rw [hvb] at hbv; exact_mod_cast hbv
    rw [← ENat.natCast_sub, ← ENat.natCast_one, Nat.cast_le]
    omega

/-- Lower-bound comparison for a single non-leading Eisenstein derivative term: for `1 ≤ h < n` and
`c ∈ 𝓂[K]`, the term `n • v_K(c * h) + (h - 1)` is at least `n - 1 + j` if and only if
`oreCoefficientDepth K n j h ≤ v_K(c)`. -/
private theorem le_eisenstein_derivative_term_iff {n j h : ℕ} (hn : 0 < n) (hh0 : 0 < h)
    (hhn : h < n) {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    ((n - 1 + j : ℕ) : ℕ∞) ≤ n • addVal 𝒪[K] (c * h) + ((h - 1 : ℕ) : ℕ∞) ↔
      (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] c := by
  have hc1 : (1 : ℕ∞) ≤ addVal 𝒪[K] c := by
    simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
      (n := 1)).mp (by simpa using hc)
  have hntop : n • (⊤ : ℕ∞) = ⊤ := by rw [nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.mpr hn.ne')]
  rw [natCast_oreCoefficientDepth, max_le_iff, and_iff_right hc1, tsub_le_iff_right, addVal_mul]
  have hjdiv : (j / n) * n + j % n = j := Nat.div_add_mod' j n
  have hbmod : j % n < n := Nat.mod_lt j hn
  induction hvc : addVal 𝒪[K] c with
  | top => simp [hntop]
  | coe u =>
    induction hvh : addVal 𝒪[K] (h : 𝒪[K]) with
    | top => simp [hntop]
    | coe v =>
      have : 1 ≤ u := by rw [hvc] at hc1; exact_mod_cast hc1
      have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
      have hh1 : h - 1 + 1 = h := Nat.sub_add_cancel hh0
      rw [nsmul_eq_mul, ← ENat.natCast_add, ← ENat.natCast_mul, ← ENat.natCast_add,
        Nat.cast_le, Nat.cast_le]
      split_ifs with hlt
      · exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
      · have : j % n ≤ h := le_of_not_gt hlt
        refine ⟨fun h ↦ ?_, fun h ↦ by nlinarith⟩
        by_contra! hlt'
        have hmul := Nat.mul_le_mul_left n (by omega : u + v ≤ j / n)
        rw [Nat.mul_comm n (j / n)] at hmul
        linarith [Nat.zero_le (j % n)]

/-- Equality comparison for a single non-leading Eisenstein derivative term: for `1 ≤ h < n` and
`c ∈ 𝓂[K]`, the term `n • v_K(c * h) + (h - 1)` equals `n - 1 + j` if and only if `h = j % n`,
`v_K(h) ≤ j / n`, and `v_K(c) = j / n + 1 - v_K(h)`. -/
private theorem eisenstein_derivative_term_eq_iff {n j h : ℕ} (hn : 0 < n) (hh0 : 0 < h)
    (hhn : h < n) {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    n • addVal 𝒪[K] (c * h) + ((h - 1 : ℕ) : ℕ∞) = ((n - 1 + j : ℕ) : ℕ∞) ↔
      h = j % n ∧ addVal 𝒪[K] (h : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
        addVal 𝒪[K] c = ((j / n + 1 : ℕ) : ℕ∞) - addVal 𝒪[K] (h : 𝒪[K]) := by
  have hc1 : (1 : ℕ∞) ≤ addVal 𝒪[K] c := by
    simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
      (n := 1)).mp (by simpa using hc)
  have hntop : n • (⊤ : ℕ∞) = ⊤ := by rw [nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.mpr hn.ne')]
  have hjdiv : (j / n) * n + j % n = j := Nat.div_add_mod' j n
  have hbmod : j % n < n := Nat.mod_lt j hn
  rw [addVal_mul]
  induction hvc : addVal 𝒪[K] c with
  | top =>
    rw [top_add, hntop, top_add]
    exact ⟨fun h ↦ absurd h (ENat.top_ne_natCast _),
      fun ⟨_, _, h⟩ ↦ absurd h (ne_top_of_le_ne_top (ENat.natCast_ne_top _) tsub_le_self).symm⟩
  | coe u =>
    induction hvh : addVal 𝒪[K] (h : 𝒪[K]) with
    | top =>
      rw [add_top, hntop, top_add]
      exact ⟨fun h ↦ absurd h (ENat.top_ne_natCast _),
        fun ⟨_, h, _⟩ ↦ absurd h (not_le_of_gt (ENat.natCast_lt_top _))⟩
    | coe v =>
      have hu1 : 1 ≤ u := by rw [hvc] at hc1; exact_mod_cast hc1
      have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
      have hh1 : h - 1 + 1 = h := Nat.sub_add_cancel hh0
      rw [nsmul_eq_mul, ← ENat.natCast_add, ← ENat.natCast_mul, ← ENat.natCast_add,
        ← ENat.natCast_sub, Nat.cast_inj, Nat.cast_le, Nat.cast_inj]
      refine ⟨fun heq ↦ ?_, fun ⟨hh, _, _⟩ ↦ ?_⟩
      · have huv1 : u + v - 1 + 1 = u + v := by omega
        have hj' : (u + v - 1) * n + h = (j / n) * n + j % n := by nlinarith
        have hrem : h = j % n := by
          simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hhn, Nat.mod_eq_of_lt hbmod] using
            congrArg (· % n) hj'
        have hquot : u + v - 1 = j / n := Nat.eq_of_mul_eq_mul_right hn (by omega)
        exact ⟨hrem, by omega, by omega⟩
      · subst hh
        rw [show u + v = j / n + 1 by omega]
        nlinarith

/-- Valuation of the leading derivative term `f_n * n` of an Eisenstein polynomial of degree `n`. -/
private theorem eisenstein_leading_derivative_term {n : ℕ} {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n) :
    n • addVal 𝒪[K] (f.coeff (n - 1 + 1) * (((n - 1 : ℕ) : 𝒪[K]) + 1)) + ((n - 1 : ℕ) : ℕ∞) =
      n • addVal 𝒪[K] n + ((n - 1 : ℕ) : ℕ∞) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hlc : addVal 𝒪[K] (f.coeff n) = 0 := by
    rw [← hdeg, coeff_natDegree]
    exact addVal_eq_zero_iff.mpr (IsLocalRing.notMem_maximalIdeal.mp hf.leading)
  rw [hsub, ← Nat.cast_add_one, hsub, addVal_mul, hlc, zero_add]

/-- Forward implication of `iInf_eisenstein_derivative_eq_iff`. -/
private theorem iInf_eisenstein_derivative_eq_imp {n j : ℕ} {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n)
    (hinf : (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) =
      ((n - 1 + j : ℕ) : ℕ∞)) :
    IsOreAdmissible K n j ∧
      (∀ h, 0 < h → h < n → (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h)) ∧
        (0 < j % n →
          addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set T : Fin n → ℕ∞ := fun i ↦ n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)
  have hlast : T ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ =
      n • addVal 𝒪[K] n + ((n - 1 : ℕ) : ℕ∞) := eisenstein_leading_derivative_term hf hdeg hn
  have hle_all (i : Fin n) : ((n - 1 + j : ℕ) : ℕ∞) ≤ T i := hinf ▸ iInf_le T i
  have hle_last : (j : ℕ∞) ≤ n • addVal 𝒪[K] n := by
    have h1 := hle_all ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
    rw [hlast, add_comm (n • _), ENat.natCast_add] at h1
    exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp h1
  have hdepth (h : ℕ) (hh0 : 0 < h) (hhn : h < n) :
      (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h) := by
    have hsub : h - 1 + 1 = h := Nat.sub_add_cancel hh0
    have h1 := hle_all ⟨h - 1, by omega⟩
    simpa only [T, hsub, ← Nat.cast_add_one,
      le_eisenstein_derivative_term_iff hn hh0 hhn (hf.mem (hdeg ▸ hhn))] using h1
  obtain ⟨i₀, hi₀⟩ := ENat.exists_eq_iInf T
  rw [hinf] at hi₀
  rcases (Nat.succ_le_of_lt i₀.isLt).lt_or_eq with hi₀lt | hi₀eq
  · have hsub : (i₀ : ℕ) + 1 - 1 = i₀ := Nat.add_sub_cancel _ _
    have heq : n • addVal 𝒪[K] (f.coeff ((i₀ : ℕ) + 1) * (((i₀ : ℕ) + 1 : ℕ) : 𝒪[K])) +
        (((i₀ : ℕ) + 1 - 1 : ℕ) : ℕ∞) = ((n - 1 + j : ℕ) : ℕ∞) := by
      simpa only [T, hsub, Nat.cast_add_one] using hi₀
    obtain ⟨hmod, hbv, hcv⟩ := (eisenstein_derivative_term_eq_iff hn (Nat.succ_pos _) hi₀lt
      (hf.mem (hdeg ▸ hi₀lt))).mp heq
    have hbpos : 0 < j % n := hmod ▸ Nat.succ_pos _
    have hadm : IsOreAdmissible K n j := by
      refine isOreAdmissible_iff_min_le_and_le.mpr ⟨hn, min_le_of_left_le ?_, hle_last⟩
      refine (nsmul_le_nsmul_right (hmod ▸ hbv) n).trans ?_
      rw [nsmul_eq_mul, ← ENat.natCast_mul, Nat.cast_le]
      exact Nat.mul_div_le j n
    exact ⟨hadm, hdepth, fun _ ↦ by
      rw [← hmod, hcv, hmod, natCast_oreCoefficientDepth_mod hadm hbpos]⟩
  · have hi₀' : i₀ = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := Fin.ext (by simp; omega)
    rw [hi₀', hlast, add_comm (n • _), ENat.natCast_add] at hi₀
    have hjeq : n • addVal 𝒪[K] n = (j : ℕ∞) :=
      le_antisymm ((ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).mp hi₀.le) hle_last
    induction hvn : addVal 𝒪[K] n with
    | top =>
      rw [hvn, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.mpr hn.ne')] at hjeq
      exact absurd hjeq (ENat.top_ne_natCast j)
    | coe v =>
      rw [hvn, nsmul_eq_mul, ← ENat.natCast_mul, Nat.cast_inj] at hjeq
      have hb0 : j % n = 0 := by simp [← hjeq]
      have ha : j / n = v := by simp [← hjeq, hn]
      exact ⟨⟨hn, .inl ⟨hb0, by simp [hvn, ha]⟩⟩, hdepth, fun hb ↦ absurd hb0 hb.ne'⟩

/-- **Derivative-minimum characterization on Eisenstein polynomials.** Let `f : 𝒪[K][X]` be
Eisenstein at `𝓂[K]` of degree `n`. Then the minimum valuation of the derivative terms
`n • v_K(f_h * h) + (h - 1)` (`1 ≤ h ≤ n`) equals `n - 1 + j` if and only if `(n, j)` is
Ore-admissible, every coefficient `f_h` (`1 ≤ h < n`) has valuation at least
`oreCoefficientDepth K n j h`, and when `0 < j % n` the coefficient `f_{j % n}` has valuation
exactly `oreCoefficientDepth K n j (j % n)`. -/
theorem iInf_eisenstein_derivative_eq_iff {n j : ℕ} {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) :
    (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) =
      ((n - 1 + j : ℕ) : ℕ∞) ↔
      IsOreAdmissible K n j ∧
        (∀ h, 0 < h → h < n → (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h)) ∧
          (0 < j % n →
            addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [ENat.top_ne_natCast]
  refine ⟨iInf_eisenstein_derivative_eq_imp hf hdeg hn, ?_⟩
  rintro ⟨hadm, hdepth, hbeq⟩
  set T : Fin n → ℕ∞ := fun i ↦ n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)
  have hlast : T ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ =
      n • addVal 𝒪[K] n + ((n - 1 : ℕ) : ℕ∞) := eisenstein_leading_derivative_term hf hdeg hn
  have hle_last : ((n - 1 + j : ℕ) : ℕ∞) ≤ T ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
    rw [hlast, add_comm (n • _), ENat.natCast_add,
      ENat.add_le_add_iff_left (ENat.natCast_ne_top _)]
    exact ((isOreAdmissible_iff_min_le_and_le.mp hadm).2).2
  refine le_antisymm ?_ (le_iInf fun i ↦ ?_)
  · rcases hadm.2 with ⟨hb0, ha⟩ | ⟨hbpos, hbv, _⟩
    · refine iInf_le_of_le ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ ?_
      have hjdiv : (j / n) * n = j := by have := Nat.div_add_mod' j n; omega
      rw [hlast, ← ha, nsmul_eq_mul, ← ENat.natCast_mul, ← ENat.natCast_add]
      exact le_of_eq (congrArg Nat.cast (by linarith))
    · have hbmod : j % n < n := Nat.mod_lt j hn
      refine iInf_le_of_le ⟨j % n - 1, by omega⟩ ?_
      have hsub : j % n - 1 + 1 = j % n := Nat.sub_add_cancel hbpos
      have heq := (eisenstein_derivative_term_eq_iff hn hbpos hbmod
        (hf.mem (n := j % n) (by omega))).mpr
          ⟨rfl, hbv, by rw [hbeq hbpos, natCast_oreCoefficientDepth_mod hadm hbpos]⟩
      have hT : T ⟨j % n - 1, by omega⟩ =
          n • addVal 𝒪[K] (f.coeff (j % n) * (j % n : ℕ)) + ((j % n - 1 : ℕ) : ℕ∞) := by
        simp only [T, hsub, ← Nat.cast_add_one]
      exact (hT.trans heq).le
  · rcases (Nat.succ_le_of_lt i.isLt).lt_or_eq with hilt | hieq
    · have hsub : (i : ℕ) + 1 - 1 = i := Nat.add_sub_cancel _ _
      have h1 := (le_eisenstein_derivative_term_iff hn (Nat.succ_pos _) hilt
        (hf.mem (n := (i : ℕ) + 1) (by omega))).mpr (hdepth ((i : ℕ) + 1) (Nat.succ_pos _) hilt)
      simpa only [T, hsub, Nat.cast_add_one] using h1
    · have hi' : i = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := Fin.ext (by simp; omega)
      exact hi' ▸ hle_last

/-- **Separability criterion for Eisenstein polynomials via the derivative minimum.** Let
`f : 𝒪[K][X]` be Eisenstein at `𝓂[K]` of positive degree `n`. Its image in `K[X]` is separable if
and only if the infimum of `n • v_K(f_h * h) + (h - 1)` over `i : Fin n` is not `⊤`. -/
theorem separable_map_iff_iInf_eisenstein_derivative_ne_top {n : ℕ} {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n) :
    (f.map (algebraMap 𝒪[K] K)).Separable ↔
      (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) ≠ ⊤ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hprim : f.IsPrimitive := fun r ⟨q, hq⟩ ↦
    isUnit_of_dvd_unit ⟨q.coeff f.natDegree, by rw [← coeff_C_mul, ← hq, coeff_natDegree]⟩
      (IsLocalRing.notMem_maximalIdeal.mp hf.leading)
  have hirr : Irreducible (f.map (algebraMap 𝒪[K] K)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp
      (hf.irreducible (Ideal.IsMaximal.isPrime inferInstance) hprim (hdeg ▸ hn))
  rw [separable_iff_derivative_ne_zero hirr, derivative_map, ne_eq,
    Polynomial.map_eq_zero_iff (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
  refine ⟨fun hder htop ↦ hder ?_, fun hne hder ↦ hne ?_⟩
  · ext1; ext1 k
    rw [coeff_zero, coeff_derivative]
    rcases lt_or_ge k n with hk | hk
    · have hi := iInf_le (fun i : Fin n ↦
        n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) ⟨k, hk⟩
      rw [htop, top_le_iff, ENat.add_eq_top] at hi
      dsimp only at hi
      have hmul := hi.resolve_right (ENat.natCast_ne_top k)
      induction hv : addVal 𝒪[K] (f.coeff (k + 1) * (k + 1)) with
      | top => exact addVal_eq_top_iff.mp hv
      | coe v =>
        rw [hv, nsmul_eq_mul, ← ENat.natCast_mul] at hmul
        exact absurd hmul (ENat.top_ne_natCast _).symm
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  · refine iInf_eq_top.mpr fun i ↦ ?_
    have hi := congrArg (fun p : 𝒪[K][X] ↦ p.coeff i) hder
    rw [coeff_derivative, coeff_zero] at hi
    rw [hi, addVal_zero, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.mpr hn.ne'), top_add]

/-- Explicit monic Eisenstein coefficient tuple realizing an Ore-admissible `(n, j)`. -/
private theorem exists_monicOfCoeff_eisenstein_of_isOreAdmissible {n j : ℕ}
    (hadm : IsOreAdmissible K n j) :
    ∃ c : Fin n → 𝒪[K],
      (monicOfCoeff c).IsEisensteinAt 𝓂[K] ∧
        (⨅ i : Fin n,
          n • addVal 𝒪[K] ((monicOfCoeff c).coeff (i + 1) * (i + 1)) + (i : ℕ)) =
          ((n - 1 + j : ℕ) : ℕ∞) := by
  have hn := hadm.pos
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[K]
  have hϖm : ϖ ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hϖ2 : ϖ ∉ 𝓂[K] ^ 2 := by
    rw [TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, addVal_uniformizer hϖ]
    simp
  let i₀ : Fin n := ⟨0, hn⟩
  let c₀ : Fin n → 𝒪[K] := Function.update 0 i₀ ϖ
  let c : Fin n → 𝒪[K] :=
    if 0 < j % n then
      Function.update c₀ ⟨j % n, Nat.mod_lt j hn⟩ (ϖ ^ oreCoefficientDepth K n j (j % n))
    else c₀
  have hc0 : c i₀ = ϖ := by
    dsimp only [c, c₀]; split_ifs with hb
    · rw [Function.update_of_ne (Fin.ne_of_val_ne hb.ne), Function.update_self]
    · rw [Function.update_self]
  have hc₀_mem (i : Fin n) : c₀ i ∈ 𝓂[K] := by by_cases hi : i = i₀ <;> simp [c₀, hi, hϖm]
  have hcmem (i : Fin n) : c i ∈ 𝓂[K] := by
    dsimp only [c]; split_ifs
    · by_cases hi : i = ⟨j % n, Nat.mod_lt j hn⟩ <;>
        simp [hi, hc₀_mem, Ideal.pow_mem_of_mem _ hϖm _ oreCoefficientDepth_pos]
    · exact hc₀_mem i
  have heis : (monicOfCoeff c).IsEisensteinAt 𝓂[K] := by
    refine (monic_monicOfCoeff c).isEisensteinAt_of_mem_of_notMem
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top (fun {k} hk ↦ ?_) ?_
    · rw [natDegree_monicOfCoeff] at hk
      simpa [coeff_monicOfCoeff c ⟨k, hk⟩] using hcmem ⟨k, hk⟩
    · rw [coeff_monicOfCoeff c i₀, hc0]; exact hϖ2
  refine ⟨c, heis, (iInf_eisenstein_derivative_eq_iff heis (natDegree_monicOfCoeff c)).mpr
    ⟨hadm, fun h hh0 hhn ↦ ?_, fun hb ↦ ?_⟩⟩
  · rw [coeff_monicOfCoeff c ⟨h, hhn⟩]
    dsimp only [c, c₀]
    split_ifs with hb
    · by_cases hhb : h = j % n
      · subst hhb; rw [Function.update_self, hϖ.addVal_pow]
      · rw [Function.update_of_ne (Fin.ne_of_val_ne hhb),
          Function.update_of_ne (Fin.ne_of_val_ne hh0.ne')]; simp
    · rw [Function.update_of_ne (Fin.ne_of_val_ne hh0.ne')]; simp
  · rw [coeff_monicOfCoeff c ⟨j % n, Nat.mod_lt j hn⟩]
    simp [c, hb, hϖ.addVal_pow]

end DiscreteValuation

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- When `(h : K) ≠ 0`, `oreCoefficientDepth` is expressed directly in terms of
`natCastValuation`. -/
theorem oreCoefficientDepth_of_natCast_ne_zero {n j h : ℕ} (hh : (h : K) ≠ 0) :
    oreCoefficientDepth K n j h =
      max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh) := by
  rw [oreCoefficientDepth, TauCeti.IsDiscreteValuationRing.addVal_natCast K h hh,
    ← ENat.natCast_sub, ENat.toNat_natCast]

/-- Over a local field where `(n : K) ≠ 0`, Ore's conditions take the finite-valuation form in
terms of `natCastValuation`. -/
theorem isOreAdmissible_iff_natCastValuation {n : ℕ} (hnK : (n : K) ≠ 0) {j : ℕ} :
    IsOreAdmissible K n j ↔
      (j % n = 0 ∧ j / n = natCastValuation K n hnK) ∨
        ∃ hbK : ((j % n : ℕ) : K) ≠ 0,
          0 < j % n ∧ natCastValuation K (j % n) hbK ≤ j / n ∧
            j / n + 1 ≤ natCastValuation K n hnK := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ hnK (by simp [h0])
  constructor
  · intro hadm
    rcases hadm.2 with ⟨hb0, ha⟩ | ⟨hbpos, hbv, hnv⟩
    · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, Nat.cast_inj] at ha
      exact .inl ⟨hb0, ha⟩
    · have hbK : ((j % n : ℕ) : K) ≠ 0 := hadm.natCast_mod_ne_zero hbpos.ne'
      rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K (j % n) hbK, Nat.cast_le] at hbv
      rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK,
        ← ENat.natCast_one, ← ENat.natCast_add, Nat.cast_le] at hnv
      exact .inr ⟨hbK, hbpos, hbv, hnv⟩
  · rintro (⟨hb0, ha⟩ | ⟨hbK, hbpos, hbv, hnv⟩)
    · exact ⟨hn, .inl ⟨hb0, by rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, ha]⟩⟩
    · refine ⟨hn, .inr ⟨hbpos, ?_, ?_⟩⟩
      · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K (j % n) hbK]; exact_mod_cast hbv
      · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK]; exact_mod_cast hnv

/-- **Ore's realizability theorem** for totally ramified separable extensions of a nonarchimedean
local field, in either characteristic: some `E ∈ totallyRamifiedOfDegree K n` has wild exponent `j`
(equivalently, discriminant exponent `n - 1 + j`) if and only if `IsOreAdmissible K n j`. -/
theorem ore_realizability (n j : ℕ) :
    (∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j) ↔ IsOreAdmissible K n j := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [totallyRamifiedOfDegree_zero]
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨f, x, _, hf, hdeg, hx, rfl⟩ :=
      exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hE
    have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein hf hx
    have hw := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hE
    have hdeq : (K⟮x⟯).discriminantExponent = n - 1 + (K⟮x⟯).wildExponent := by omega
    rw [hdeg, hdeq] at hd
    exact ((iInf_eisenstein_derivative_eq_iff hf hdeg).mp hd.symm).1
  · intro hadm
    obtain ⟨c, heis, hinf⟩ := exists_monicOfCoeff_eisenstein_of_isOreAdmissible hadm
    have hsep : ((monicOfCoeff c).map (algebraMap 𝒪[K] K)).Separable :=
      (separable_map_iff_iInf_eisenstein_derivative_ne_top heis
        (natDegree_monicOfCoeff c) hn).mpr (hinf ▸ ENat.natCast_ne_top _)
    let P := ((monicOfCoeff c).map (algebraMap 𝒪[K] K)).map (algebraMap K (SeparableClosure K))
    have hdeg_ne : P.degree ≠ 0 := degree_ne_of_natDegree_ne (n := 0) (by simp [P, hn.ne'])
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root P hdeg_ne hsep.map
    have hx' : aeval x ((monicOfCoeff c).map (algebraMap 𝒪[K] K)) = 0 := by
      rwa [IsRoot, eval_map, ← aeval_def] at hx
    have hmem : K⟮x⟯ ∈ totallyRamifiedOfDegree K n :=
      adjoin_mem_totallyRamifiedOfDegree_of_eisenstein heis (natDegree_monicOfCoeff c) hx'
    refine ⟨K⟮x⟯, hmem, ?_⟩
    have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein heis hx'
    rw [natDegree_monicOfCoeff c, hinf] at hd
    have hd' : (K⟮x⟯).discriminantExponent = n - 1 + j := by exact_mod_cast hd
    have hw := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
    omega

end LocalField

end TauCeti
