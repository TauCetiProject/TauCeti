/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
import TauCeti.Algebra.CharP.LocalRing

/-!
# Ore's admissibility conditions and coefficient depths

Let `K` be a field equipped with a discrete valuation ring `𝒪[K]`, maximal ideal `𝓂[K]`, and
additive valuation `v_K = IsDiscreteValuationRing.addVal 𝒪[K]` (which takes the value `⊤` on
natural numbers vanishing in `K`). For a positive degree `n` and a candidate wild exponent `j`,
writing `j = a n + b` with `0 ≤ b < n`, **Ore's admissibility conditions**
(`TauCeti.IsOreAdmissible K n j`) require:

* if `b = 0`, then `a = v_K(n)`;
* if `b > 0`, then `v_K(b) ≤ a` and `a + 1 ≤ v_K(n)`.

Notice that in equal characteristic `p` with `p ∣ n`, `v_K(n) = ⊤`, so the `b = 0` branch is
impossible and the `b > 0` branch reduces to `p ∤ b` (equivalently `p ∤ j`), allowing
arbitrarily large wild exponents; in mixed characteristic, every admissible `j` satisfies
`j ≤ n v_K(n)`.

Associated to `(n, j)` are the **coefficient valuation depths**
`TauCeti.oreCoefficientDepth K n j h = max 1 (j / n + 1 + [h < j % n] - v_K(h))` for `h : ℕ`.
They specify the exact ideal-power bounds defining Krasner's discriminant box in Eisenstein
coefficient space.

## Main definitions

* `TauCeti.IsOreAdmissible K n j`: Ore's admissibility predicate on degree `n` and wild exponent
  `j`.
* `TauCeti.oreCoefficientDepth K n j h`: the coefficient valuation lower bound `ν_h`.

## Main results

* `TauCeti.isOreAdmissible_iff_eq_zero_of_not_dvd`: in the tame case (`¬ ringChar 𝓀[K] ∣ n`),
  only wild exponent `0` is admissible.
* `TauCeti.IsOreAdmissible.le_mul_addVal` and `TauCeti.IsOreAdmissible.le_mul_natCastValuation`:
  the Ore upper bound `j ≤ n · v_K(n)`.
* `TauCeti.oreCoefficientDepth_le_addVal_iff_of_one_le`: characterization of `ν_h ≤ v_K(c)` as
  `j / n + 1 + [h < j % n] ≤ v_K(c) + v_K(h)`.
* `TauCeti.oreCoefficientDepth_mod_add_addVal_of_isOreAdmissible`: for admissible `(n, j)` with
  `b = j % n > 0`, `ν_b + v_K(b) = j / n + 1`.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, CNRS, Paris (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section
noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

section DiscreteValuationRing

variable [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **Ore's admissibility conditions** on a degree `n` and a wild exponent `j`: writing
`j = a n + b` with `0 ≤ b < n`, `n` is positive and either `b = 0` and `a = v_K(n)`, or `b > 0`,
`v_K(b) ≤ a` and `a + 1 ≤ v_K(n)`, where `v_K` is the additive valuation `addVal 𝒪[K]` (which
takes the value `⊤` on natural numbers vanishing in `K`). -/
def IsOreAdmissible (n j : ℕ) : Prop :=
  0 < n ∧ ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K])) ∨
    (0 < j % n ∧ addVal 𝒪[K] (j % n : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
      ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K])))

/-- Unfolded characterization of `IsOreAdmissible`. -/
theorem isOreAdmissible_def {n j : ℕ} :
    IsOreAdmissible K n j ↔
      0 < n ∧ ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K])) ∨
        (0 < j % n ∧ addVal 𝒪[K] (j % n : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
          ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]))) :=
  Iff.rfl

/-- An Ore-admissible pair `(n, j)` has positive degree `n`. -/
theorem IsOreAdmissible.pos {n j : ℕ} (h : IsOreAdmissible K n j) : 0 < n :=
  h.1

/-- Degree zero has no Ore-admissible wild exponent. -/
@[simp]
theorem not_isOreAdmissible_zero_left (j : ℕ) : ¬ IsOreAdmissible K 0 j :=
  fun h ↦ h.1.ne' rfl

/-- In degree one, only wild exponent `0` is Ore-admissible. -/
@[simp]
theorem isOreAdmissible_one_iff {j : ℕ} : IsOreAdmissible K 1 j ↔ j = 0 := by
  simp only [IsOreAdmissible, Nat.zero_lt_one, true_and, Nat.mod_one, Nat.div_one,
    lt_self_iff_false, false_and, or_false, Nat.cast_one, addVal_one]
  exact Nat.cast_eq_zero

/-- Wild exponent `0` is Ore-admissible in degree `n` exactly when `0 < n` and `n` is a unit of
`𝒪[K]`. -/
theorem isOreAdmissible_zero_right_iff {n : ℕ} :
    IsOreAdmissible K n 0 ↔ 0 < n ∧ IsUnit (n : 𝒪[K]) := by
  simp only [IsOreAdmissible, Nat.zero_mod, Nat.zero_div, Nat.cast_zero, lt_self_iff_false,
    false_and, or_false, true_and]
  exact and_congr_right fun _ ↦ eq_comm.trans addVal_eq_zero_iff

/-- If `n` is a unit of `𝒪[K]` and `0 < n`, only wild exponent `0` is Ore-admissible. -/
theorem isOreAdmissible_iff_eq_zero_of_isUnit {n j : ℕ} (hn : 0 < n) (hu : IsUnit (n : 𝒪[K])) :
    IsOreAdmissible K n j ↔ j = 0 := by
  have hvn : addVal 𝒪[K] (n : 𝒪[K]) = 0 := addVal_eq_zero_iff.mpr hu
  simp only [IsOreAdmissible, hn, true_and, hvn]
  constructor
  · rintro (⟨hmod, hdiv⟩ | ⟨-, -, hle⟩)
    · have hdiv0 : j / n = 0 := by exact_mod_cast hdiv
      rw [← Nat.div_add_mod j n, hdiv0, hmod, mul_zero, add_zero]
    · norm_cast at hle
  · rintro rfl
    exact Or.inl (by simp)

/-- In the tame case (`¬ ringChar 𝓀[K] ∣ n`, `0 < n`), only wild exponent `0` is
Ore-admissible. -/
theorem isOreAdmissible_iff_eq_zero_of_not_dvd {n j : ℕ} (hn : 0 < n)
    (hp : ¬ ringChar 𝓀[K] ∣ n) : IsOreAdmissible K n j ↔ j = 0 :=
  isOreAdmissible_iff_eq_zero_of_isUnit hn (IsLocalRing.isUnit_natCast_iff_not_dvd.2 hp)

/-- Every Ore-admissible wild exponent satisfies `j ≤ n • v_K(n)` in `ℕ∞`. -/
theorem IsOreAdmissible.le_mul_addVal {n j : ℕ} (h : IsOreAdmissible K n j) :
    (j : ℕ∞) ≤ n • addVal 𝒪[K] (n : 𝒪[K]) := by
  rcases h with ⟨hn, ⟨hmod, hdiv⟩ | ⟨_, _, hle⟩⟩
  · rw [← hdiv, nsmul_eq_mul]
    exact_mod_cast (by have := Nat.div_add_mod j n; omega : j ≤ n * (j / n))
  · have hstep : (j : ℕ∞) ≤ ((n * (j / n + 1) : ℕ) : ℕ∞) := by
      have h1 := Nat.div_add_mod j n
      have h2 := Nat.mod_lt j hn
      rw [mul_add_one]
      exact_mod_cast (by omega : j ≤ n * (j / n) + n)
    refine hstep.trans ?_
    rw [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_right hle _

variable (K) in
/-- The coefficient valuation lower bound `ν_h = max 1 (j / n + 1 + [h < j % n] - v_K(h))` at
index `h` for the discriminant box of degree `n` and wild exponent `j`. When `(h : 𝒪[K]) = 0`,
`addVal 𝒪[K] (h : 𝒪[K]) = ⊤`, so the truncated subtraction in `ℕ∞` yields `0` and the depth
is `1`. -/
def oreCoefficientDepth (n j h : ℕ) : ℕ :=
  max 1 (((j / n + 1 + (if h < j % n then 1 else 0) : ℕ) : ℕ∞) -
    addVal 𝒪[K] (h : 𝒪[K])).toNat

/-- Unfolded defining equation of `oreCoefficientDepth`. -/
theorem oreCoefficientDepth_def (n j h : ℕ) :
    oreCoefficientDepth K n j h =
      max 1 (((j / n + 1 + (if h < j % n then 1 else 0) : ℕ) : ℕ∞) -
        addVal 𝒪[K] (h : 𝒪[K])).toNat := by
  rfl

/-- Every coefficient depth is at least `1`. -/
theorem one_le_oreCoefficientDepth (n j h : ℕ) : 1 ≤ oreCoefficientDepth K n j h :=
  le_max_left _ _

/-- At index `0`, the coefficient depth is `1`. -/
@[simp]
theorem oreCoefficientDepth_zero (n j : ℕ) : oreCoefficientDepth K n j 0 = 1 := by
  simp [oreCoefficientDepth]

/-- If `h` vanishes in `𝒪[K]`, its coefficient depth is `1`. -/
theorem oreCoefficientDepth_of_natCast_eq_zero {n j h : ℕ} (hh : (h : 𝒪[K]) = 0) :
    oreCoefficientDepth K n j h = 1 := by
  simp [oreCoefficientDepth, hh]

/-- For an element `c ∈ 𝒪[K]` with `1 ≤ v_K(c)`, requiring `ν_h ≤ v_K(c)` is equivalent to
requiring `j / n + 1 + [h < j % n] ≤ v_K(c) + v_K(h)` in `ℕ∞`. -/
theorem oreCoefficientDepth_le_addVal_iff_of_one_le {n j h : ℕ} {c : 𝒪[K]}
    (hc : (1 : ℕ∞) ≤ addVal 𝒪[K] c) :
    (oreCoefficientDepth K n j h : ℕ∞) ≤ addVal 𝒪[K] c ↔
      ((j / n + 1 + (if h < j % n then 1 else 0) : ℕ) : ℕ∞) ≤
        addVal 𝒪[K] c + addVal 𝒪[K] (h : 𝒪[K]) := by
  rw [oreCoefficientDepth_def]
  cases hv : addVal 𝒪[K] (h : 𝒪[K]) with
  | top => simp [hc]
  | coe v =>
    rw [ENat.toNat_sub (ENat.natCast_ne_top v), ENat.toNat_natCast, ENat.toNat_natCast]
    cases hcv : addVal 𝒪[K] c with
    | top => simp
    | coe w =>
      rw [hcv] at hc
      have hw : 1 ≤ w := by exact_mod_cast hc
      norm_cast
      omega

/-- For an Ore-admissible pair `(n, j)` with `b = j % n > 0`, the coefficient depth at index `b`
satisfies `ν_b + v_K(b) = j / n + 1` in `ℕ∞`. -/
theorem oreCoefficientDepth_mod_add_addVal_of_isOreAdmissible {n j : ℕ}
    (h : IsOreAdmissible K n j) (hb : 0 < j % n) :
    (oreCoefficientDepth K n j (j % n) : ℕ∞) + addVal 𝒪[K] (j % n : 𝒪[K]) =
      ((j / n + 1 : ℕ) : ℕ∞) := by
  rcases h.2 with ⟨h0, _⟩ | ⟨_, hvb, _⟩
  · omega
  cases hv : addVal 𝒪[K] (j % n : 𝒪[K]) with
  | top => rw [hv] at hvb; simp at hvb
  | coe v =>
    rw [hv] at hvb
    have hvle : v ≤ j / n := by exact_mod_cast hvb
    rw [oreCoefficientDepth_def, ite_eq_right (lt_irrefl _), add_zero, hv,
      ENat.toNat_sub (ENat.natCast_ne_top v), ENat.toNat_natCast, ENat.toNat_natCast]
    norm_cast
    omega

/-- For `0 < n` and `j % n = 0`, the coefficient depths sum to at most `n + j - 1`. -/
theorem sum_oreCoefficientDepth_le_of_mod_eq_zero {n j : ℕ} (hn : 0 < n) (hmod : j % n = 0) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ n + j - 1 := by
  have hle : ∀ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ j / n + 1 := fun h _ ↦ by
    rw [oreCoefficientDepth_def, hmod, ite_eq_right (Nat.not_lt_zero h), add_zero]
    refine max_le (Nat.le_add_left 1 _) ?_
    cases hv : addVal 𝒪[K] (h : 𝒪[K]) with
    | top => simp
    | coe v =>
      rw [ENat.toNat_sub (ENat.natCast_ne_top v), ENat.toNat_natCast, ENat.toNat_natCast]
      exact Nat.sub_le _ _
  calc ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
      ≤ ∑ _ ∈ Finset.Ico 1 n, (j / n + 1) := Finset.sum_le_sum hle
    _ = (n - 1) * (j / n + 1) := by simp
    _ ≤ n + j - 1 := by
        have hdiv := Nat.div_add_mod j n
        have hmul : (n - 1) * (j / n + 1) + (j / n + 1) = n * (j / n) + n := by
          rw [← add_one_mul, ← mul_add_one]
          congr 1
          omega
        have := Nat.zero_le (j / n)
        omega

/-- For `0 < n` and `0 < j % n`, the coefficient depths sum to at most `n + j - 2`. -/
theorem sum_oreCoefficientDepth_le_of_mod_pos {n j : ℕ} (hn : 0 < n) (hb : 0 < j % n) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ n + j - 2 := by
  have hblt : j % n < n := Nat.mod_lt j hn
  have hle : ∀ h ∈ Finset.Ico 1 n,
      oreCoefficientDepth K n j h ≤ j / n + 1 + (if h < j % n then 1 else 0) := fun h _ ↦ by
    rw [oreCoefficientDepth_def]
    refine max_le (Nat.le_add_right_of_le (Nat.le_add_left 1 _)) ?_
    cases hv : addVal 𝒪[K] (h : 𝒪[K]) with
    | top => simp
    | coe v =>
      rw [ENat.toNat_sub (ENat.natCast_ne_top v), ENat.toNat_natCast, ENat.toNat_natCast]
      exact Nat.sub_le _ _
  have hcard : ((Finset.Ico 1 n).filter (· < j % n)).card = j % n - 1 := by
    have hfilt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hfilt, Nat.card_Ico]
  calc ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
      ≤ ∑ h ∈ Finset.Ico 1 n, (j / n + 1 + (if h < j % n then 1 else 0)) :=
          Finset.sum_le_sum hle
    _ = (n - 1) * (j / n + 1) + (j % n - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
          Finset.sum_boole, Nat.cast_id, hcard]
    _ ≤ n + j - 2 := by
        have hdiv := Nat.div_add_mod j n
        have hmul : (n - 1) * (j / n + 1) + (j / n + 1) = n * (j / n) + n := by
          rw [← add_one_mul, ← mul_add_one]
          congr 1
          omega
        have := Nat.zero_le (j / n)
        omega

end DiscreteValuationRing

section LocalField

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- In a nonarchimedean local field, if `(h : K) ≠ 0`, `oreCoefficientDepth K n j h` is
`max 1 (j / n + 1 + [h < j % n] - natCastValuation K h hh)`. -/
theorem oreCoefficientDepth_eq_of_natCast_ne_zero {n j h : ℕ} (hh : (h : K) ≠ 0) :
    oreCoefficientDepth K n j h =
      max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh) := by
  rw [oreCoefficientDepth_def, TauCeti.IsDiscreteValuationRing.addVal_natCast K h hh,
    ENat.toNat_sub (ENat.natCast_ne_top _), ENat.toNat_natCast, ENat.toNat_natCast]

/-- When `(n : K) ≠ 0`, every Ore-admissible wild exponent satisfies `j ≤ n * v_K(n)`. -/
theorem IsOreAdmissible.le_mul_natCastValuation {n j : ℕ} (h : IsOreAdmissible K n j)
    (hnK : (n : K) ≠ 0) : j ≤ n * natCastValuation K n hnK := by
  have hle := h.le_mul_addVal
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, nsmul_eq_mul] at hle
  exact_mod_cast hle

end LocalField

end TauCeti
