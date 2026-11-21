/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.FieldTheory.Separable
import TauCeti.Data.ENat.Basic
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
import TauCeti.Order.CompleteLattice.Basic
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
* `TauCeti.sum_oreCoefficientDepth_le`, `TauCeti.sum_oreCoefficientDepth_add_one_le`,
  `TauCeti.sum_oreCoefficientDepth_add_sum_saving`: upper bounds and saving identity on
  `∑_{h=1}^{n-1} ν_h`.
* `TauCeti.separable_monicOfCoeff_of_isOreAdmissible`: separability of irreducible
  `monicOfCoeff a` under Ore admissibility.
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
      rw [hv, nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le] at hr; nlinarith

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

/-- Pointwise saving identity: `ν_h + min (j / n + [h < j % n], v_K(h)) = j / n + 1 + [h < j % n]`.
-/
private theorem oreCoefficientDepth_add_saving (n j h : ℕ) :
    oreCoefficientDepth K n j h +
        (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
          (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
      j / n + 1 + if h < j % n then 1 else 0 := by
  rw [oreCoefficientDepth_def]
  cases addVal 𝒪[K] (h : 𝒪[K]) with
  | top => simp only [ENat.sub_top, ENat.toNat_zero, min_top_right, ENat.toNat_natCast]; omega
  | coe v =>
    rw [ENat.toNat_sub (ENat.natCast_ne_top _), ENat.toNat_natCast, ENat.toNat_natCast,
      ← ENat.natCast_min, ENat.toNat_natCast]
    omega

/-- Sum of coefficient depths and valuation savings over `1 ≤ h < n`:
`∑ ν_h + ∑ min (j / n + [h < j % n], v_K(h)) = (n - 1) * (j / n + 1) + (j % n - 1)`. -/
theorem sum_oreCoefficientDepth_add_sum_saving {n j : ℕ} (hn : 0 < n) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
        ∑ h ∈ Finset.Ico 1 n,
          (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
            (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
      (n - 1) * (j / n + 1) + (j % n - 1) := by
  rw [← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun h _ ↦ oreCoefficientDepth_add_saving n j h,
    Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Finset.sum_boole,
    Nat.cast_id, Finset.Ico_filter_lt_of_le_right (Nat.mod_lt j hn).le, Nat.card_Ico]

/-- Unified upper bound on the sum of coefficient depths over `1 ≤ h < n`. -/
private theorem sum_oreCoefficientDepth_le_aux {n j : ℕ} (hn : 0 < n) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤
      n + j - 1 - if 0 < j % n then 1 else 0 := by
  have hle : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤
      (n - 1) * (j / n + 1) + (j % n - 1) :=
    le_self_add.trans_eq (sum_oreCoefficientDepth_add_sum_saving hn)
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
  rw [ite_eq_left hb] at h; have : 0 < j := hb.trans_le (Nat.mod_le j n); omega

/-- An irreducible monic polynomial `monicOfCoeff a` of degree `n` over `K` is separable when
`(n, j)` is Ore-admissible and, if `0 < j % n`, the coefficient `a ⟨j % n, _⟩` is nonzero. -/
theorem separable_monicOfCoeff_of_isOreAdmissible {n j : ℕ} {a : Fin n → K}
    (hirr : Irreducible (monicOfCoeff a)) (hO : IsOreAdmissible K n j)
    (hb : 0 < j % n → a ⟨j % n, Nat.mod_lt j hO.pos⟩ ≠ 0) :
    (monicOfCoeff a).Separable := by
  have hn := hO.pos; rw [Polynomial.separable_iff_derivative_ne_zero hirr]; intro hder
  rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
  · have hvn := (isOreAdmissible_iff_of_mod_eq_zero hn hb0).1 hO
    have hnK : (n : K) ≠ 0 := fun h0 ↦ by
      rw [(natCast_integerRing_eq_zero_iff n).2 h0, addVal_zero] at hvn
      exact ENat.natCast_ne_top _ hvn
    have hc := congrArg (fun p : K[X] ↦ p.coeff (n - 1)) hder
    rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel hn, coeff_monicOfCoeff_self, one_mul,
      Nat.cast_sub hn, Nat.cast_one, sub_add_cancel] at hc
    exact hnK hc
  · have hvb := ((isOreAdmissible_iff_of_mod_pos hn hbpos).1 hO).1
    have hbK : ((j % n : ℕ) : K) ≠ 0 := fun h0 ↦ by
      rw [(natCast_integerRing_eq_zero_iff _).2 h0, addVal_zero] at hvb; simp at hvb
    have hmod := Nat.mod_lt j hn; have hc := congrArg (fun p : K[X] ↦ p.coeff (j % n - 1)) hder
    rw [coeff_derivative, coeff_zero, Nat.sub_add_cancel hbpos, coeff_monicOfCoeff a ⟨j % n, hmod⟩,
      Nat.cast_sub hbpos, Nat.cast_one, sub_add_cancel] at hc
    exact mul_ne_zero (hb hbpos) hbK hc

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

/-- Minimum-attainment characterization for `⨅ i : Fin n, n • v i + i = n - 1 + j` in `ℕ∞`.
Writing `n - 1 + j = n * q + r` with `r < n` (where `r + 1 = j % n` if `0 < j % n` and
`r + 1 = n` otherwise), the infimum equals `n - 1 + j` iff each `v i` satisfies the shifted
quotient lower bound and `v r = q`. -/
private theorem iInf_nsmul_add_eq_sub_add_iff {n j : ℕ} (hn : 0 < n) (v : Fin n → ℕ∞) :
    (⨅ i : Fin n, n • v i + (i : ℕ)) = ((n - 1 + j : ℕ) : ℕ∞) ↔
      (∀ i : Fin n, (i : ℕ) + 1 < n →
        ((j / n + 1 + (if (i : ℕ) + 1 < j % n then 1 else 0) : ℕ) : ℕ∞) ≤ v i) ∧
      ((j / n + (if 0 < j % n then 1 else 0) : ℕ) : ℕ∞) ≤
        v ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ ∧
      v ⟨(if 0 < j % n then j % n else n) - 1,
          by have := Nat.mod_lt j hn; split_ifs <;> omega⟩ =
        ((j / n + (if 0 < j % n then 1 else 0) : ℕ) : ℕ∞) := by
  have hdiv : n * (j / n) + j % n = j := Nat.div_add_mod j n
  have hmod : j % n < n := Nat.mod_lt j hn
  let q := j / n + if 0 < j % n then 1 else 0; let r := (if 0 < j % n then j % n else n) - 1
  have hr : r < n := by dsimp [r]; split_ifs <;> omega
  have hD : n - 1 + j = n * q + r := by
    dsimp [q, r]; split_ifs <;> [rw [Nat.mul_succ]; simp only [add_zero]] <;> omega
  have hshift {k : ℕ} (hk : k + 1 < n) :
      q + (if k < r then 1 else 0) = j / n + 1 + if k + 1 < j % n then 1 else 0 := by
    dsimp [q, r]; split_ifs <;> omega
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hD, iInf_eq_iff_of_finite]
  refine ⟨fun ⟨hle, i, hi⟩ ↦ ?_, fun ⟨hle, htop, heq⟩ ↦ ?_⟩
  · rw [nsmul_add_eq_iff i.isLt hr] at hi
    refine ⟨fun k hk ↦ ?_, ?_, ?_⟩
    · have hkstep := hle k; rw [le_nsmul_add_iff k.isLt hr, hshift hk] at hkstep; exact hkstep
    · have htopstep := hle ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩
      rw [le_nsmul_add_iff (Nat.sub_lt hn Nat.one_pos) hr] at htopstep
      rwa [ite_eq_right (by omega), add_zero] at htopstep
    · have hir : i = ⟨r, hr⟩ := Fin.ext hi.1; rw [hir] at hi; simpa [r, q] using hi.2
  · refine ⟨fun i ↦ ?_, ⟨r, hr⟩, ?_⟩
    · rw [le_nsmul_add_iff i.isLt hr]
      rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt i.isLt) with hilt | hieq
      · rw [hshift (by omega)]; exact hle i (by omega)
      · rw [ite_eq_right (by omega), add_zero, show i = ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ from
          Fin.ext hieq]; exact htop
    · rw [nsmul_add_eq_iff hr hr]; exact ⟨rfl, by simpa [r, q] using heq⟩

/-- Helper for Eisenstein polynomials: every lower coefficient has valuation ≥ 1. -/
private theorem one_le_addVal_coeff_of_eisenstein {f : 𝒪[K][X]}
    (hfE : f.IsEisensteinAt 𝓂[K]) {h : ℕ} (hh : h < f.natDegree) :
    1 ≤ addVal 𝒪[K] (f.coeff h) := by
  have hmem : f.coeff h ∈ 𝓂[K] ^ 1 := by rw [pow_one]; exact hfE.mem hh
  exact_mod_cast (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.1 hmem)

/-- Forward direction of `wildExponent_adjoin_eq_iff_of_eisenstein`: the shifted infimum
bounds on coefficient valuations force Ore admissibility, all coefficient depths `ν_h`, and
equality at `h = j % f.natDegree` when `0 < j % f.natDegree`. -/
private theorem wildExponent_adjoin_eq_mp {j : ℕ} {f : 𝒪[K][X]}
    (hfM : f.Monic) (hfE : f.IsEisensteinAt 𝓂[K]) (hn : 0 < f.natDegree)
    (hinf : (⨅ i : Fin f.natDegree, f.natDegree • (addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) +
      addVal 𝒪[K] (((i : ℕ) + 1 : ℕ) : 𝒪[K])) + (i : ℕ)) =
        ((f.natDegree - 1 + j : ℕ) : ℕ∞)) :
    IsOreAdmissible K f.natDegree j ∧
      (∀ h : Fin f.natDegree, 0 < (h : ℕ) →
        (oreCoefficientDepth K f.natDegree j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h)) ∧
      (0 < j % f.natDegree →
        addVal 𝒪[K] (f.coeff (j % f.natDegree)) =
          oreCoefficientDepth K f.natDegree j (j % f.natDegree)) := by
  have hlead : addVal 𝒪[K] (f.coeff f.natDegree) = 0 := by rw [hfM.coeff_natDegree, addVal_one]
  obtain ⟨hle, htop, heq⟩ := (iInf_nsmul_add_eq_sub_add_iff hn _).1 hinf
  have hdepth : ∀ h : Fin f.natDegree, 0 < (h : ℕ) →
      (oreCoefficientDepth K f.natDegree j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h) := fun h hh0 ↦ by
    have hstep := hle ⟨(h : ℕ) - 1, by omega⟩ (by dsimp; omega)
    dsimp only at hstep; rw [Nat.sub_add_cancel hh0] at hstep
    exact (oreCoefficientDepth_le_addVal_iff (one_le_addVal_coeff_of_eisenstein hfE h.isLt)).2
      hstep
  rcases Nat.eq_zero_or_pos (j % f.natDegree) with hb | hb
  · have hvn : ((j / f.natDegree : ℕ) : ℕ∞) = addVal 𝒪[K] (f.natDegree : 𝒪[K]) := by
      simp only [hb, lt_self_iff_false, ↓reduceIte, add_zero] at heq
      rw [Nat.sub_add_cancel hn, hlead, zero_add] at heq; exact heq.symm
    exact ⟨(isOreAdmissible_iff_of_mod_eq_zero hn hb).2 hvn, hdepth, fun h0 ↦ absurd hb h0.ne'⟩
  · have hvb_eq : addVal 𝒪[K] (f.coeff (j % f.natDegree)) +
        addVal 𝒪[K] ((j % f.natDegree : ℕ) : 𝒪[K]) = ((j / f.natDegree + 1 : ℕ) : ℕ∞) := by
      simpa [hb, Nat.sub_add_cancel hb] using heq
    have hvb_le : addVal 𝒪[K] ((j % f.natDegree : ℕ) : 𝒪[K]) ≤ ((j / f.natDegree : ℕ) : ℕ∞) := by
      have h1 : addVal 𝒪[K] ((j % f.natDegree : ℕ) : 𝒪[K]) + 1 ≤
          ((j / f.natDegree : ℕ) : ℕ∞) + 1 := by
        rw [add_comm, ← Nat.cast_add_one, ← hvb_eq]
        exact add_le_add (one_le_addVal_coeff_of_eisenstein hfE (Nat.mod_lt j hn)) le_rfl
      exact (WithTop.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).1 h1
    have hvn_le : ((j / f.natDegree : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (f.natDegree : 𝒪[K]) := by
      dsimp only at htop; rw [Nat.sub_add_cancel hn, hlead, zero_add] at htop; simpa [hb] using htop
    have hO := (isOreAdmissible_iff_of_mod_pos hn hb).2 ⟨hvb_le, hvn_le⟩
    refine ⟨hO, hdepth, fun _ ↦ ?_⟩
    have hsum := addVal_add_oreCoefficientDepth_of_mod_pos hO hb; rw [add_comm] at hsum
    exact WithTop.add_right_cancel (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hvb_le)
      (hvb_eq.trans hsum.symm)

/-- Backward direction of `wildExponent_adjoin_eq_iff_of_eisenstein`: Ore admissibility, the
coefficient depth bounds `ν_h`, and equality at `j % f.natDegree` give the shifted infimum. -/
private theorem wildExponent_adjoin_eq_mpr {j : ℕ} {f : 𝒪[K][X]}
    (hfM : f.Monic) (hfE : f.IsEisensteinAt 𝓂[K]) (hn : 0 < f.natDegree)
    (hO : IsOreAdmissible K f.natDegree j)
    (hdepth : ∀ h : Fin f.natDegree, 0 < (h : ℕ) →
      (oreCoefficientDepth K f.natDegree j h : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h))
    (hbeq : 0 < j % f.natDegree →
      addVal 𝒪[K] (f.coeff (j % f.natDegree)) =
        oreCoefficientDepth K f.natDegree j (j % f.natDegree)) :
    (⨅ i : Fin f.natDegree, f.natDegree • (addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) +
      addVal 𝒪[K] (((i : ℕ) + 1 : ℕ) : 𝒪[K])) + (i : ℕ)) =
        ((f.natDegree - 1 + j : ℕ) : ℕ∞) := by
  have hlead : addVal 𝒪[K] (f.coeff f.natDegree) = 0 := by rw [hfM.coeff_natDegree, addVal_one]
  rw [iInf_nsmul_add_eq_sub_add_iff hn]
  refine ⟨fun i hi ↦ (oreCoefficientDepth_le_addVal_iff
    (one_le_addVal_coeff_of_eisenstein hfE hi)).1 (hdepth ⟨(i : ℕ) + 1, hi⟩ (Nat.succ_pos _)),
    ?_, ?_⟩
  · dsimp only; rw [Nat.sub_add_cancel hn, hlead, zero_add]
    rcases Nat.eq_zero_or_pos (j % f.natDegree) with hb | hb
    · simpa [hb] using ((isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO).le
    · simpa [hb] using ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).2
  · dsimp only
    rcases Nat.eq_zero_or_pos (j % f.natDegree) with hb | hb
    · simp only [hb, lt_self_iff_false, ↓reduceIte, add_zero]
      rw [Nat.sub_add_cancel hn, hlead, zero_add]
      exact ((isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO).symm
    · simp only [hb, ↓reduceIte, Nat.sub_add_cancel hb]
      rw [hbeq hb, add_comm]; exact_mod_cast addVal_add_oreCoefficientDepth_of_mod_pos hO hb

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
  -- Express `wildExponent = j` as `discriminantExponent = n - 1 + j`, rewrite via the Eisenstein
  -- `⨅` formula and factor `v_K(f.coeff (i + 1) * (i + 1))`, then delegate to `mp` / `mpr`.
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hfE hdeg hx
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0, totallyRamifiedOfDegree_zero] at hmem
  have hwc := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein hfE hx
  subst hdeg
  rw [show (K⟮x⟯).wildExponent = j ↔
      ((K⟮x⟯).discriminantExponent : ℕ∞) = ((f.natDegree - 1 + j : ℕ) : ℕ∞) from
      by rw [Nat.cast_inj]; omega,
    hd, show (⨅ i : Fin f.natDegree, f.natDegree • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) +
      (i : ℕ)) = ⨅ i : Fin f.natDegree, f.natDegree • (addVal 𝒪[K] (f.coeff ((i : ℕ) + 1)) +
        addVal 𝒪[K] (((i : ℕ) + 1 : ℕ) : 𝒪[K])) + (i : ℕ) from
      iInf_congr fun i ↦ by rw [addVal_mul, Nat.cast_add, Nat.cast_one]]
  exact ⟨wildExponent_adjoin_eq_mp hfM hfE hn,
    fun ⟨hO, hdepth, hbeq⟩ ↦ wildExponent_adjoin_eq_mpr hfM hfE hn hO hdepth hbeq⟩

/-- Every member of `σ_K(n)` has an Ore-admissible wild exponent. -/
theorem isOreAdmissible_wildExponent {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    IsOreAdmissible K n L.wildExponent := by
  obtain ⟨f, x, hfM, hfE, hdeg, hx, rfl⟩ :=
    exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hL
  exact ((wildExponent_adjoin_eq_iff_of_eisenstein hfM hfE hdeg hx).1 rfl).1

/-- Witness coefficient vector `c : Fin n → 𝒪[K]` whose monic polynomial `monicOfCoeff c` is
Eisenstein, achieves the minimal Ore coefficient depths `oreCoefficientDepth K n j h` for all
`0 < h < n`, and has nonzero `(j % n)`-th coefficient with exact valuation `ν_{j % n}` when
`0 < j % n`. -/
private theorem exists_eisenstein_coeff_of_pos {n j : ℕ} (hn : 0 < n) :
    ∃ c : Fin n → 𝒪[K], (monicOfCoeff c).IsEisensteinAt 𝓂[K] ∧
      (∀ h : Fin n, 0 < (h : ℕ) →
        (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] (c h)) ∧
      (0 < j % n → c ⟨j % n, Nat.mod_lt j hn⟩ ≠ 0 ∧
        addVal 𝒪[K] (c ⟨j % n, Nat.mod_lt j hn⟩) = oreCoefficientDepth K n j (j % n)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπm : π ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  have hπm2 : π ∉ 𝓂[K] ^ 2 := by
    rw [TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, addVal_uniformizer hπ]
    simp
  let c : Fin n → 𝒪[K] := fun i ↦ if (i : ℕ) = 0 then π
    else if 0 < j % n ∧ (i : ℕ) = j % n then π ^ oreCoefficientDepth K n j (j % n) else 0
  refine ⟨c, ?_, fun h hh0 ↦ ?_, fun hb ↦ ?_⟩
  · refine (monic_monicOfCoeff c).isEisensteinAt_of_mem_of_notMem
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top (fun {i} hi ↦ ?_) ?_
    · rw [natDegree_monicOfCoeff] at hi; rw [coeff_monicOfCoeff c ⟨i, hi⟩]; dsimp [c]
      split_ifs
      exacts [hπm, Ideal.pow_mem_of_mem _ hπm _ (one_le_oreCoefficientDepth ..), Ideal.zero_mem _]
    · rw [coeff_monicOfCoeff c ⟨0, hn⟩]; simpa [c] using hπm2
  · dsimp [c]; rw [ite_eq_right hh0.ne']
    split_ifs with hmatch
    · rw [hmatch.2, addVal_pow, addVal_uniformizer hπ, nsmul_eq_mul, mul_one]
    · simp
  · exact ⟨by simp [c, hb, hb.ne', pow_ne_zero _ hπ.ne_zero],
      by simp [c, hb, hb.ne', addVal_uniformizer hπ]⟩

/-- **Ore's realizability theorem**: for any degree `n` and wild exponent `j`, some totally ramified
subextension of degree `n` in `SeparableClosure K` has wild exponent `j` if and only if
`IsOreAdmissible K n j`. This holds in both mixed and equal characteristic, including at `n = 0`. -/
theorem exists_mem_totallyRamifiedOfDegree_wildExponent_eq_iff (n j : ℕ) :
    (∃ L ∈ totallyRamifiedOfDegree K n, L.wildExponent = j) ↔ IsOreAdmissible K n j := by
  -- Forward direction follows from `isOreAdmissible_wildExponent`. For the converse, build an
  -- Eisenstein witness via `exists_eisenstein_coeff_of_pos`, deduce separability from Ore
  -- admissibility, pick a root in `SeparableClosure K`, and apply the valuation criterion.
  refine ⟨fun ⟨L, hL, hLj⟩ ↦ hLj ▸ isOreAdmissible_wildExponent hL, fun hO ↦ ?_⟩
  obtain ⟨c, hcE, hdepth, hcmod⟩ := exists_eisenstein_coeff_of_pos (K := K) (j := j) hO.pos
  let a : Fin n → K := fun i ↦ (c i : K)
  have hmap : (monicOfCoeff c).map (algebraMap 𝒪[K] K) = monicOfCoeff a := by
    simp [a, Algebra.algebraMap_ofSubsemiring_apply]
  have hsep := separable_monicOfCoeff_of_isOreAdmissible
    (irreducible_monicOfCoeff_of_mem_eisensteinSet hO.pos
      (mem_eisensteinSet_iff_exists_isEisensteinAt.2 ⟨monicOfCoeff c, hmap, hcE⟩))
    hO fun hb ↦ Subtype.coe_ne_coe.2 (hcmod hb).1
  obtain ⟨x, hx⟩ := exists_root_of_separable_of_natDegree_pos hsep
    ((natDegree_monicOfCoeff a).symm ▸ hO.pos)
  have hx0 : aeval x ((monicOfCoeff c).map (algebraMap 𝒪[K] K)) = 0 := hmap ▸ hx
  refine ⟨K⟮x⟯, adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hcE (natDegree_monicOfCoeff c) hx0,
    (wildExponent_adjoin_eq_iff_of_eisenstein (monic_monicOfCoeff c) hcE
      (natDegree_monicOfCoeff c) hx0).2 ⟨hO, fun h hh0 ↦ ?_, fun hb ↦ ?_⟩⟩
  · rw [coeff_monicOfCoeff c h]; exact hdepth h hh0
  · rw [coeff_monicOfCoeff c ⟨j % n, Nat.mod_lt j hO.pos⟩]; exact (hcmod hb).2

end LocalField

end TauCeti
