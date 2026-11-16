/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Ore's conditions and realizability for wild exponents

Let `K` be a nonarchimedean local field with integer ring `𝒪[K]`, maximal ideal `𝓂[K]`, and
additive valuation `v_K = IsDiscreteValuationRing.addVal 𝒪[K] : 𝒪[K] → ℕ∞`. For a positive degree
`n` and wild exponent `j = a * n + b` (`0 ≤ b < n`), Ore's conditions `TauCeti.IsOreAdmissible`
require `a = v_K(n)` when `b = 0`, and `v_K(b) ≤ a` and `a + 1 ≤ v_K(n)` when `b > 0`—equivalently
`min (n • v_K(b)) (n • v_K(n)) ≤ j ≤ n • v_K(n)` in both mixed and equal characteristic.

Reading the wild exponent of an Eisenstein extension from
`TauCeti.natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein` yields the exact
coefficient-valuation characterization (`TauCeti.wildExponent_adjoin_eq_iff_of_eisenstein`) in
terms of `TauCeti.oreCoefficientDepth K n j h = max 1 (a + 1 + [h < b] - v_K(h))`, and hence Ore's
realizability theorem (`TauCeti.exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff`).

## Main definitions

* `TauCeti.IsOreAdmissible K n j`: Ore's realizability condition for degree `n`, wild exponent `j`.
* `TauCeti.oreCoefficientDepth K n j h`: the coefficient lower bound `ν_h` on `v_K(f.coeff h)`.

## Main results

* `TauCeti.isOreAdmissible_iff_le_nsmul`, `TauCeti.isOreAdmissible_iff_of_natCast_eq_zero`:
  inequality and equal-characteristic forms of Ore's conditions.
* `TauCeti.sum_oreCoefficientDepth_le`, `TauCeti.sum_oreCoefficientDepth_add_one_le`: upper bounds
  on `∑_{h=1}^{n-1} ν_h`.
* `TauCeti.wildExponent_adjoin_eq_iff_of_eisenstein`: exact coefficient-valuation characterization
  of `(K⟮x⟯).wildExponent = j` for a root `x` of a monic Eisenstein polynomial.
* `TauCeti.exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff`: **Ore's realizability theorem**.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing TauCeti.Polynomial
open scoped IntermediateField

namespace TauCeti

section DiscreteValuation

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

omit [IsDiscreteValuationRing 𝒪[K]] in
/-- A natural number vanishes in `𝒪[K]` exactly when it vanishes in `K`. -/
private theorem natCast_integerRing_eq_zero_iff (m : ℕ) : (m : 𝒪[K]) = 0 ↔ (m : K) = 0 :=
  ⟨fun h ↦ by simpa using congrArg Subtype.val h, fun h ↦ Subtype.ext (by simpa using h)⟩

/-! ### Ore's conditions -/

variable (K) in
/-- **Ore's conditions** for degree `n` and wild exponent `j`: `0 < n`, and writing `j = a * n + b`
with `0 ≤ b < n`, either `b = 0` and `a = v_K(n)`, or `b > 0`, `v_K(b) ≤ a` and `a + 1 ≤ v_K(n)`,
where `v_K` is `IsDiscreteValuationRing.addVal 𝒪[K]` (equal to `⊤` on elements vanishing in `K`). -/
def IsOreAdmissible (n j : ℕ) : Prop :=
  0 < n ∧
    ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K])) ∨
      (0 < j % n ∧ addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K])))

/-- Unfolded characterization of `IsOreAdmissible`. -/
theorem isOreAdmissible_iff {n j : ℕ} :
    IsOreAdmissible K n j ↔
      0 < n ∧
        ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K])) ∨
          (0 < j % n ∧ addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
            ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]))) :=
  Iff.rfl

/-- An Ore-admissible degree is positive. -/
theorem IsOreAdmissible.pos {n j : ℕ} (h : IsOreAdmissible K n j) : 0 < n := h.1

/-- Degree zero has no Ore-admissible wild exponents. -/
@[simp]
theorem not_isOreAdmissible_zero_left (j : ℕ) : ¬ IsOreAdmissible K 0 j := fun h ↦ (lt_irrefl 0) h.1

/-- In degree one, only wild exponent `0` is Ore-admissible. -/
@[simp]
theorem isOreAdmissible_one_left {j : ℕ} : IsOreAdmissible K 1 j ↔ j = 0 := by
  simp [isOreAdmissible_iff, Nat.mod_one, Nat.div_one]

/-- For positive `n` dividing `j`, Ore admissibility is `j / n = v_K(n)`. -/
theorem isOreAdmissible_iff_of_mod_eq_zero {n j : ℕ} (hn : 0 < n) (hb : j % n = 0) :
    IsOreAdmissible K n j ↔ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K]) := by
  simp [isOreAdmissible_iff, hn, hb]

/-- For positive `n` with `0 < j % n`, Ore admissibility is `v_K(j % n) ≤ j / n` and
`j / n + 1 ≤ v_K(n)`. -/
theorem isOreAdmissible_iff_of_mod_pos {n j : ℕ} (hn : 0 < n) (hb : 0 < j % n) :
    IsOreAdmissible K n j ↔
      addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]) := by
  simp [isOreAdmissible_iff, hn, hb, hb.ne']

/-- **Inequality form of Ore's conditions**: for `0 < n`, in either characteristic,
`IsOreAdmissible K n j` holds exactly when
`min (n • v_K(j % n)) (n • v_K(n)) ≤ j ≤ n • v_K(n)`. -/
theorem isOreAdmissible_iff_le_nsmul {n j : ℕ} (hn : 0 < n) :
    IsOreAdmissible K n j ↔
      min (n • addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K])) (n • addVal 𝒪[K] (n : 𝒪[K])) ≤ (j : ℕ∞) ∧
        (j : ℕ∞) ≤ n • addVal 𝒪[K] (n : 𝒪[K]) := by
  have hdiv : n * (j / n) + j % n = j := Nat.div_add_mod j n
  have hmod : j % n < n := Nat.mod_lt j hn
  have htop : n • (⊤ : ℕ∞) = ⊤ := by simp [nsmul_eq_mul, hn.ne']
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · rw [isOreAdmissible_iff_of_mod_eq_zero hn hb, hb, Nat.cast_zero, addVal_zero, htop,
      min_top_left, ← le_antisymm_iff]
    cases addVal 𝒪[K] (n : 𝒪[K]) with
    | top => simp [htop]
    | coe k =>
      simp only [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_inj]
      exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
  · rw [isOreAdmissible_iff_of_mod_pos hn hb]
    have hupper : ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]) ↔
        (j : ℕ∞) ≤ n • addVal 𝒪[K] (n : 𝒪[K]) := by
      cases addVal 𝒪[K] (n : 𝒪[K]) with
      | top => simp [htop]
      | coe k =>
        rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add_one, Nat.cast_le, Nat.cast_le]
        exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
    have hlower : addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ↔
        n • addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ (j : ℕ∞) := by
      cases addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) with
      | top => simp [htop]
      | coe r =>
        rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le, Nat.cast_le]
        exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨min_le_of_left_le (hlower.1 h1), hupper.1 h2⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
    have h2' := hupper.2 h2
    refine ⟨hlower.2 ((min_le_iff.1 h1).resolve_right fun hr ↦ ?_), h2'⟩
    cases hv : addVal 𝒪[K] (n : 𝒪[K]) with
    | top => rw [hv, htop] at hr; exact ENat.top_ne_natCast j (top_unique hr).symm
    | coe k =>
      rw [hv, ← Nat.cast_add_one, Nat.cast_le] at h2'
      rw [hv, nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le] at hr
      nlinarith

/-! ### Coefficient depths of the discriminant box -/

variable (K) in
/-- The coefficient lower bound `ν_h = max 1 (j / n + 1 + [h < j % n] - v_K(h))` for the `h`-th
coefficient of an Eisenstein polynomial of degree `n` with wild exponent `j`. When `(h : K) = 0`,
`v_K(h) = ⊤` and truncated subtraction in `ℕ∞` yields `ν_h = 1`. -/
def oreCoefficientDepth (n j h : ℕ) : ℕ :=
  max 1 ((((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) -
    addVal 𝒪[K] (h : 𝒪[K])).toNat)

/-- Definitional unfolding of `oreCoefficientDepth`. -/
theorem oreCoefficientDepth_def (n j h : ℕ) :
    oreCoefficientDepth K n j h =
      max 1 ((((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) -
        addVal 𝒪[K] (h : 𝒪[K])).toNat) :=
  (rfl)

/-- Every coefficient depth is at least `1`. -/
theorem one_le_oreCoefficientDepth (n j h : ℕ) : 1 ≤ oreCoefficientDepth K n j h := le_max_left ..

/-- Every coefficient depth is positive. -/
theorem oreCoefficientDepth_pos (n j h : ℕ) : 0 < oreCoefficientDepth K n j h :=
  one_le_oreCoefficientDepth n j h

/-- Upper bound on the coefficient depth, obtained by dropping the `- v_K(h)` term. -/
theorem oreCoefficientDepth_le (n j h : ℕ) :
    oreCoefficientDepth K n j h ≤ j / n + 1 + if h < j % n then 1 else 0 :=
  max_le (Nat.le_add_right_of_le (Nat.le_add_left 1 _)) (ENat.toNat_le_of_le_natCast tsub_le_self)

/-- An index vanishing in `K` imposes no derivative constraint, so its coefficient depth is `1`. -/
theorem oreCoefficientDepth_of_natCast_eq_zero {n j h : ℕ} (hh : (h : K) = 0) :
    oreCoefficientDepth K n j h = 1 := by
  simp [oreCoefficientDepth_def, (natCast_integerRing_eq_zero_iff h).2 hh]

/-- For an element `c ∈ 𝓂[K]` (`1 ≤ v_K(c)`), the depth bound `ν_h ≤ v_K(c)` is equivalent to the
derivative-term lower bound `j / n + 1 + [h < j % n] ≤ v_K(c) + v_K(h)`. -/
theorem oreCoefficientDepth_le_addVal_iff {n j h : ℕ} {c : 𝒪[K]}
    (hc : 1 ≤ addVal 𝒪[K] c) :
    (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] c ↔
      ((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) ≤
        addVal 𝒪[K] c + addVal 𝒪[K] (h : 𝒪[K]) := by
  rw [oreCoefficientDepth_def]
  have hne : (((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) -
      addVal 𝒪[K] (h : 𝒪[K])) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) tsub_le_self
  cases hc' : addVal 𝒪[K] c with
  | top => simp
  | coe k =>
    rw [hc'] at hc
    rw [Nat.cast_le, max_le_iff, and_iff_right (by exact_mod_cast hc), ← Nat.cast_le (α := ℕ∞),
      ENat.natCast_toNat hne, tsub_le_iff_right]

/-- For an Ore-admissible wild exponent with `0 < j % n`, the depth at index `b = j % n` satisfies
`v_K(b) + ν_b = j / n + 1`. -/
theorem addVal_add_oreCoefficientDepth_of_mod_pos {n j : ℕ}
    (hO : IsOreAdmissible K n j) (hb : 0 < j % n) :
    addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) + (oreCoefficientDepth K n j (j % n) : ℕ∞) =
      ((j / n + 1 : ℕ) : ℕ∞) := by
  have hvb := ((isOreAdmissible_iff_of_mod_pos hO.pos hb).1 hO).1
  cases hv : addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) with
  | top => simp [hv] at hvb
  | coe r =>
    rw [hv, Nat.cast_le] at hvb
    have hdepth : oreCoefficientDepth K n j (j % n) = j / n + 1 - r := by
      rw [oreCoefficientDepth_def, hv, ite_eq_right (lt_irrefl _), add_zero,
        ENat.toNat_sub (ENat.natCast_ne_top _), ENat.toNat_natCast, ENat.toNat_natCast]
      omega
    rw [hdepth, ← Nat.cast_add]
    exact_mod_cast Nat.add_sub_of_le (by omega : r ≤ j / n + 1)

/-- Unified upper bound on the sum of coefficient depths over `1 ≤ h < n`. -/
private theorem sum_oreCoefficientDepth_le_aux {n j : ℕ} (hn : 0 < n) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤
      n + j - 1 - if 0 < j % n then 1 else 0 := by
  have hle : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤
      ∑ h ∈ Finset.Ico 1 n, (j / n + 1 + if h < j % n then 1 else 0) :=
    Finset.sum_le_sum fun h _ ↦ oreCoefficientDepth_le n j h
  have hcard_lt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
    ext h; simp only [Finset.mem_filter, Finset.mem_Ico]; have := Nat.mod_lt j hn; omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Finset.sum_boole,
    Nat.cast_id, hcard_lt, Nat.card_Ico] at hle
  have hdiv : n * (j / n) + j % n = j := Nat.div_add_mod j n
  have hmul : (n - 1) * (j / n + 1) ≤ n * (j / n) + (n - 1) := by
    cases n with
    | zero => omega
    | succ m =>
      simpa only [Nat.add_sub_cancel] using (Nat.le_add_right _ (j / (m + 1))).trans_eq (by ring)
  split_ifs <;> omega

/-- The sum of the coefficient depths over `1 ≤ h < n` never exceeds `n + j - 1`. -/
theorem sum_oreCoefficientDepth_le {n j : ℕ} (hn : 0 < n) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ n + j - 1 :=
  le_trans (sum_oreCoefficientDepth_le_aux hn) (Nat.sub_le ..)

/-- When `0 < j % n`, the sum of the coefficient depths over `1 ≤ h < n` is at most `n + j - 2`,
so the Krasner exponent `(n + j - 1) - ∑ ν_h` is at least `1`. -/
theorem sum_oreCoefficientDepth_add_one_le {n j : ℕ} (hn : 0 < n) (hb : 0 < j % n) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h + 1 ≤ n + j - 1 := by
  have h := sum_oreCoefficientDepth_le_aux (K := K) (j := j) hn
  rw [ite_eq_left hb] at h
  have : 0 < j := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hb
  omega

end DiscreteValuation

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- When `(n : K) ≠ 0`, every Ore-admissible wild exponent satisfies `j ≤ n * v_K(n)`. -/
theorem IsOreAdmissible.le_mul_natCastValuation {n j : ℕ} (h : IsOreAdmissible K n j)
    (hnK : (n : K) ≠ 0) : j ≤ n * natCastValuation K n hnK := by
  have hle := ((isOreAdmissible_iff_le_nsmul h.pos).1 h).2
  rw [IsDiscreteValuationRing.addVal_natCast K n hnK, nsmul_eq_mul, ← Nat.cast_mul] at hle
  exact Nat.cast_le.1 hle

/-- In equal characteristic with `p ∣ n` (equivalently `0 < n` and `(n : K) = 0`), a wild exponent
`j` is Ore-admissible exactly when the residue characteristic does not divide `j`. -/
theorem isOreAdmissible_iff_of_natCast_eq_zero {n j : ℕ} (hn : 0 < n) (hnK : (n : K) = 0) :
    IsOreAdmissible K n j ↔ ¬ ringChar 𝓀[K] ∣ j := by
  have hchar := (natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hn).1 hnK
  have hvn : addVal 𝒪[K] (n : 𝒪[K]) = ⊤ :=
    addVal_eq_top_iff.2 ((natCast_integerRing_eq_zero_iff n).2 hnK)
  have htop : n • (⊤ : ℕ∞) = ⊤ := by simp [nsmul_eq_mul, hn.ne']
  have hdvd : ringChar 𝓀[K] ∣ j ↔ ringChar 𝓀[K] ∣ j % n := by
    conv_lhs => rw [← Nat.div_add_mod j n]
    exact Nat.dvd_add_right (dvd_mul_of_dvd_left hchar.2 _)
  rw [isOreAdmissible_iff_le_nsmul hn, hvn, htop, min_top_right, and_iff_left le_top, hdvd]
  by_cases hbK : ((j % n : ℕ) : K) = 0
  · have hpb : ringChar 𝓀[K] ∣ j % n := by rwa [← hchar.1, ← ringChar.spec K]
    simp [addVal_eq_top_iff.2 ((natCast_integerRing_eq_zero_iff _).2 hbK), htop, hpb]
  · have hpb : ¬ ringChar 𝓀[K] ∣ j % n := fun h ↦ hbK ((ringChar.spec K _).2 (hchar.1.symm ▸ h))
    rw [IsDiscreteValuationRing.addVal_natCast K (j % n) hbK,
      (natCastValuation_eq_zero_iff_not_dvd K (j % n) hbK).2 hpb]
    simp [hpb]

/-- In the tame case (`¬ ringChar 𝓀[K] ∣ n` and `0 < n`), only wild exponent `0` is
Ore-admissible. -/
theorem isOreAdmissible_iff_of_not_dvd {n j : ℕ} (hn : 0 < n) (hp : ¬ ringChar 𝓀[K] ∣ n) :
    IsOreAdmissible K n j ↔ j = 0 := by
  have hnK : (n : K) ≠ 0 := fun h ↦
    hp ((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hn).1 h).2
  rw [isOreAdmissible_iff_le_nsmul hn, IsDiscreteValuationRing.addVal_natCast K n hnK,
    (natCastValuation_eq_zero_iff_not_dvd K n hnK).2 hp]
  simp

/-- When `(h : K) ≠ 0`, `oreCoefficientDepth` uses `natCastValuation K h hh`. -/
theorem oreCoefficientDepth_of_natCast_ne_zero {n j h : ℕ} (hh : (h : K) ≠ 0) :
    oreCoefficientDepth K n j h =
      max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh) := by
  rw [oreCoefficientDepth_def, IsDiscreteValuationRing.addVal_natCast K h hh,
    ENat.toNat_sub (ENat.natCast_ne_top _), ENat.toNat_natCast, ENat.toNat_natCast]

/-! ### Wild exponent of an Eisenstein generator -/

/-- Exact arithmetic comparison between a derivative term `n • v + i` and `n * q + r` in `ℕ∞`
for `i, r < n`. -/
private theorem le_nsmul_add_iff {n q r i : ℕ} (hi : i < n) (hr : r < n) (v : ℕ∞) :
    ((n * q + r : ℕ) : ℕ∞) ≤ n • v + (i : ℕ) ↔
      ((q + if i < r then 1 else 0 : ℕ) : ℕ∞) ≤ v := by
  cases v with
  | top => simp [nsmul_eq_mul, (show n ≠ 0 by omega)]
  | coe k =>
    simp only [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_le]
    split_ifs <;> exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩

/-- Exact arithmetic equality between a derivative term `n • v + i` and `n * q + r` in `ℕ∞`
for `i, r < n`: both residues and quotients must match. -/
private theorem nsmul_add_eq_iff {n q r i : ℕ} (hi : i < n) (hr : r < n) (v : ℕ∞) :
    n • v + (i : ℕ) = ((n * q + r : ℕ) : ℕ∞) ↔ i = r ∧ v = (q : ℕ∞) := by
  cases v with
  | top =>
    rw [nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 (by omega)), top_add]
    exact iff_of_false (ENat.top_ne_natCast _) (by simp)
  | coe k =>
    simp only [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj]
    refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ by rw [h1, h2]⟩
    have hmod : i = r := by
      have := congrArg (· % n) h
      simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hr] using this
    exact ⟨hmod, Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) (by omega)⟩

/-- On a finite nonempty index type, `⨅ i, t i = d` iff `d` is a lower bound attained at some
index. -/
private theorem iInf_eq_iff_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    (t : ι → ℕ∞) (d : ℕ∞) :
    (⨅ i, t i) = d ↔ (∀ i, d ≤ t i) ∧ ∃ i, t i = d := by
  refine ⟨fun h ↦ ⟨fun i ↦ h ▸ iInf_le t i, ?_⟩, fun ⟨hle, i, hi⟩ ↦
    le_antisymm (iInf_le_of_le i hi.le) (le_iInf hle)⟩
  obtain ⟨i, hi⟩ := Finite.exists_min t
  exact ⟨i, le_antisymm (le_trans (le_iInf hi) h.le) (h ▸ iInf_le t i)⟩

/-- **Wild exponent of an Eisenstein generator in terms of coefficient valuations**: for a root `x`
in `SeparableClosure K` of a monic Eisenstein polynomial `f : 𝒪[K][X]` of degree `n`, the
extension `K⟮x⟯` has wild exponent `j` if and only if `IsOreAdmissible K n j`, every intermediate
coefficient `f.coeff h` (`0 < h < n`) has valuation at least `oreCoefficientDepth K n j h`, and
when `0 < j % n` equality holds at `h = j % n`. -/
theorem wildExponent_adjoin_eq_iff_of_eisenstein {n j : ℕ} {f : 𝒪[K][X]}
    (hfM : f.Monic) (hfE : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n)
    {x : SeparableClosure K} (hx : aeval x (f.map (algebraMap 𝒪[K] K)) = 0) :
    (K⟮x⟯).wildExponent = j ↔
      IsOreAdmissible K n j ∧
        (∀ h : Fin n, 0 < (h : ℕ) →
          (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h)) ∧
        (0 < j % n → addVal 𝒪[K] (f.coeff (j % n)) = oreCoefficientDepth K n j (j % n)) := by
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hfE hdeg hx
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0, totallyRamifiedOfDegree_zero] at hmem
  have hwc := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein hfE hx
  subst hdeg
  have hwild_iff : (K⟮x⟯).wildExponent = j ↔
      (⨅ i : Fin f.natDegree,
        f.natDegree • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) =
        ((f.natDegree - 1 + j : ℕ) : ℕ∞) := by rw [← hd, Nat.cast_inj]; omega
  have : Nonempty (Fin f.natDegree) := ⟨⟨0, hn⟩⟩
  rw [hwild_iff, iInf_eq_iff_of_finite]
  have hmul (i : Fin f.natDegree) :
      addVal 𝒪[K] (f.coeff ((i : ℕ) + 1) * ((i : ℕ) + 1 : 𝒪[K])) =
        addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) + addVal 𝒪[K] (((i : ℕ) + 1 : ℕ) : 𝒪[K]) := by
    rw [addVal_mul, Nat.cast_add, Nat.cast_one]
  have hlead : addVal 𝒪[K] (f.coeff f.natDegree) = 0 := by rw [hfM.coeff_natDegree, addVal_one]
  have heis {h : ℕ} (hh : h < f.natDegree) : 1 ≤ addVal 𝒪[K] (f.coeff h) := by
    have hmem : f.coeff h ∈ 𝓂[K] ^ 1 := by rw [pow_one]; exact hfE.mem hh
    exact_mod_cast (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.1 hmem)
  have hdiv : f.natDegree * (j / f.natDegree) + j % f.natDegree = j :=
    Nat.div_add_mod j f.natDegree
  have hmod : j % f.natDegree < f.natDegree := Nat.mod_lt j hn
  let q : ℕ := j / f.natDegree + if 0 < j % f.natDegree then 1 else 0
  let r : ℕ := (if 0 < j % f.natDegree then j % f.natDegree else f.natDegree) - 1
  have hr : r < f.natDegree := by dsimp [r]; split_ifs <;> omega
  have hD : f.natDegree - 1 + j = f.natDegree * q + r := by
    dsimp [q, r]; split_ifs
    · rw [Nat.mul_succ]; omega
    · simp only [add_zero]; omega
  have hshift {k : ℕ} (hk : k + 1 < f.natDegree) :
      q + (if k < r then 1 else 0) =
        j / f.natDegree + 1 + if k + 1 < j % f.natDegree then 1 else 0 := by
    dsimp [q, r]; split_ifs <;> omega
  rw [hD]
  constructor
  · rintro ⟨hle, i, hi⟩
    rw [hmul, nsmul_add_eq_iff i.isLt hr] at hi
    have hdepth : ∀ h : Fin f.natDegree, 0 < (h : ℕ) →
        (oreCoefficientDepth K f.natDegree j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h) := fun h hh0 ↦ by
      have hstep := hle ⟨(h : ℕ) - 1, by omega⟩
      rw [hmul, le_nsmul_add_iff (by omega) hr] at hstep; dsimp only at hstep
      rw [hshift (by omega), show (h : ℕ) - 1 + 1 = h by omega] at hstep
      exact (oreCoefficientDepth_le_addVal_iff (heis h.isLt)).2 hstep
    rcases Nat.eq_zero_or_pos (j % f.natDegree) with hb | hb
    · have hi1 : (i : ℕ) + 1 = f.natDegree := by
        dsimp [r] at hi; rw [ite_eq_right (by omega)] at hi; omega
      have hvn : ((j / f.natDegree : ℕ) : ℕ∞) = addVal 𝒪[K] (f.natDegree : 𝒪[K]) := by
        have hv := hi.2; rw [hi1, hlead, zero_add] at hv; simpa [q, hb] using hv.symm
      exact ⟨(isOreAdmissible_iff_of_mod_eq_zero hn hb).2 hvn, hdepth, fun h0 ↦ absurd hb h0.ne'⟩
    · have hi1 : (i : ℕ) + 1 = j % f.natDegree := by
        dsimp [r] at hi; rw [ite_eq_left hb] at hi; omega
      have hvb_eq : addVal 𝒪[K] (f.coeff (j % f.natDegree)) +
          addVal 𝒪[K] ((j % f.natDegree : ℕ) : 𝒪[K]) = ((j / f.natDegree + 1 : ℕ) : ℕ∞) := by
        simpa [q, hb, hi1] using hi.2
      have hvb_le : addVal 𝒪[K] ((j % f.natDegree : ℕ) : 𝒪[K]) ≤ ((j / f.natDegree : ℕ) : ℕ∞) := by
        have h1 : addVal 𝒪[K] ((j % f.natDegree : ℕ) : 𝒪[K]) + 1 ≤
            ((j / f.natDegree : ℕ) : ℕ∞) + 1 := by
          rw [add_comm, ← Nat.cast_add_one, ← hvb_eq]; exact add_le_add (heis hmod) le_rfl
        exact (WithTop.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).1 h1
      have hvn_le : ((j / f.natDegree : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (f.natDegree : 𝒪[K]) := by
        have htop := hle ⟨f.natDegree - 1, by omega⟩
        rw [hmul, le_nsmul_add_iff (by omega) hr] at htop; dsimp only at htop
        rw [ite_eq_right (by omega), add_zero, show f.natDegree - 1 + 1 = f.natDegree by omega,
          hlead, zero_add] at htop
        simpa [q, hb] using htop
      have hO : IsOreAdmissible K f.natDegree j :=
        (isOreAdmissible_iff_of_mod_pos hn hb).2 ⟨hvb_le, hvn_le⟩
      refine ⟨hO, hdepth, fun _ ↦ ?_⟩
      have hsum := addVal_add_oreCoefficientDepth_of_mod_pos hO hb
      rw [add_comm] at hsum
      exact WithTop.add_right_cancel (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hvb_le)
        (hvb_eq.trans hsum.symm)
  · rintro ⟨hO, hdepth, hbeq⟩
    refine ⟨fun i ↦ ?_, ⟨r, hr⟩, ?_⟩
    · rw [hmul, le_nsmul_add_iff i.isLt hr]
      rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt i.isLt) with hilt | hieq
      · rw [hshift (by omega)]
        exact (oreCoefficientDepth_le_addVal_iff (heis (by omega))).1
          (hdepth ⟨(i : ℕ) + 1, by omega⟩ (Nat.succ_pos _))
      · rw [ite_eq_right (by omega), add_zero, show (i : ℕ) + 1 = f.natDegree by omega,
          hlead, zero_add]
        rcases Nat.eq_zero_or_pos (j % f.natDegree) with hb | hb
        · simpa [q, hb] using ((isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO).le
        · simpa [q, hb] using ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).2
    · rw [hmul, nsmul_add_eq_iff hr hr]
      refine ⟨rfl, ?_⟩
      rcases Nat.eq_zero_or_pos (j % f.natDegree) with hb | hb
      · have hr1 : r + 1 = f.natDegree := by dsimp [r]; rw [ite_eq_right (by omega)]; omega
        rw [hr1, hlead, zero_add]
        simpa [q, hb] using ((isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO).symm
      · have hr1 : r + 1 = j % f.natDegree := by dsimp [r]; rw [ite_eq_left hb]; omega
        rw [hr1, hbeq hb, add_comm]
        simpa [q, hb] using addVal_add_oreCoefficientDepth_of_mod_pos hO hb

/-- Every member of `σ_K(n)` has an Ore-admissible wild exponent. -/
theorem isOreAdmissible_wildExponent {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    IsOreAdmissible K n L.wildExponent := by
  obtain ⟨f, x, hfM, hfE, hdeg, hx, rfl⟩ :=
    exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hL
  exact ((wildExponent_adjoin_eq_iff_of_eisenstein hfM hfE hdeg hx).1 rfl).1

/-- **Ore's realizability theorem**: for any degree `n` and wild exponent `j`, some totally ramified
subextension of degree `n` in `SeparableClosure K` has wild exponent `j` if and only if
`IsOreAdmissible K n j`. This holds in both mixed and equal characteristic, including at `n = 0`. -/
theorem exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff (n j : ℕ) :
    (∃ L ∈ totallyRamifiedOfDegree K n, L.wildExponent = j) ↔ IsOreAdmissible K n j := by
  refine ⟨fun ⟨L, hL, hLj⟩ ↦ hLj ▸ isOreAdmissible_wildExponent hL, fun hO ↦ ?_⟩
  have hn := hO.pos
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπm : π ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  have hπm2 : π ∉ 𝓂[K] ^ 2 := by
    rw [TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, addVal_uniformizer hπ]
    simp
  let c : Fin n → 𝒪[K] := fun i ↦
    if (i : ℕ) = 0 then π
    else if 0 < j % n ∧ (i : ℕ) = j % n then π ^ oreCoefficientDepth K n j (j % n)
    else 0
  let f : 𝒪[K][X] := monicOfCoeff c
  have hfM : f.Monic := monic_monicOfCoeff c
  have hdeg : f.natDegree = n := natDegree_monicOfCoeff c
  have hfE : f.IsEisensteinAt 𝓂[K] := by
    refine hfM.isEisensteinAt_of_mem_of_notMem (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
      (fun {i} hi ↦ ?_) ?_
    · rw [hdeg] at hi; rw [show f.coeff i = c ⟨i, hi⟩ from coeff_monicOfCoeff c ⟨i, hi⟩]; dsimp [c]
      split_ifs
      · exact hπm
      · exact Ideal.pow_mem_of_mem _ hπm _ (oreCoefficientDepth_pos ..)
      · exact Ideal.zero_mem _
    · rw [show f.coeff 0 = c ⟨0, hn⟩ from coeff_monicOfCoeff c ⟨0, hn⟩]; simpa [c] using hπm2
  have hirr : Irreducible (f.map (algebraMap 𝒪[K] K)) := by
    have ha : (fun i : Fin n ↦ (c i : K)) ∈ eisensteinSet K n :=
      mem_eisensteinSet_iff_exists_isEisensteinAt.2
        ⟨f, by simp [f, Algebra.algebraMap_ofSubsemiring_apply], hfE⟩
    simpa [f, Algebra.algebraMap_ofSubsemiring_apply] using
      irreducible_monicOfCoeff_of_mem_eisensteinSet hn ha
  have hsep : (f.map (algebraMap 𝒪[K] K)).Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hirr]
    intro hder
    rcases Nat.eq_zero_or_pos (j % n) with hb | hb
    · have hvn := (isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO
      have hnK : (n : K) ≠ 0 := fun h0 ↦ by
        rw [(natCast_integerRing_eq_zero_iff n).2 h0, addVal_zero] at hvn
        exact ENat.natCast_ne_top _ hvn
      have hlead : f.coeff n = 1 := hdeg ▸ hfM.coeff_natDegree
      have hc := congrArg (fun p : K[X] ↦ p.coeff (n - 1)) hder
      rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel hn, coeff_map, hlead, map_one, one_mul,
        Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] at hc
      exact hnK hc
    · have hvb := ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).1
      have hbK : ((j % n : ℕ) : K) ≠ 0 := fun h0 ↦ by
        rw [(natCast_integerRing_eq_zero_iff _).2 h0, addVal_zero] at hvb; simp at hvb
      have hc := congrArg (fun p : K[X] ↦ p.coeff (j % n - 1)) hder
      rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel hb, coeff_map,
        coeff_monicOfCoeff c ⟨j % n, Nat.mod_lt j hn⟩,
        show c ⟨j % n, Nat.mod_lt j hn⟩ = π ^ oreCoefficientDepth K n j (j % n) by
          simp [c, hb, hb.ne'],
        map_pow, Algebra.algebraMap_ofSubsemiring_apply, Nat.cast_sub hb, Nat.cast_one,
        sub_add_cancel] at hc
      exact mul_ne_zero (pow_ne_zero _ (Subtype.coe_ne_coe.2 hπ.ne_zero)) hbK hc
  have hroots : ((f.map (algebraMap 𝒪[K] K)).aroots (SeparableClosure K)).card = n := by
    rw [aroots_def, ← (IsSepClosed.splits_codomain _ hsep).natDegree_eq_card_roots, natDegree_map,
      natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hdeg]
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (hroots ▸ hn)
  have hx0 : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := (mem_aroots.1 hx).2
  refine ⟨K⟮x⟯, adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hfE hdeg hx0,
    (wildExponent_adjoin_eq_iff_of_eisenstein hfM hfE hdeg hx0).2 ⟨hO, fun h hh0 ↦ ?_, fun hb ↦ ?_⟩⟩
  · rw [coeff_monicOfCoeff c h]; dsimp [c]; rw [ite_eq_right hh0.ne']
    split_ifs with hmatch
    · rw [hmatch.2, addVal_pow, addVal_uniformizer hπ, nsmul_eq_mul, mul_one]
    · simp
  · rw [coeff_monicOfCoeff c ⟨j % n, Nat.mod_lt j hn⟩]; simp [c, hb, hb.ne', addVal_uniformizer hπ]

end LocalField

end TauCeti
