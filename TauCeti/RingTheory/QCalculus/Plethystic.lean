/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.LaurentSeries.Ramified
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Combined Adams dilation and the elementary plethystic exponential

This file develops the elementary plethystic toolkit on power series with Laurent-series
coefficients `(A⸨X⸩)⟦X⟧` (writing `q` for the inner Laurent variable and `t` for the outer
power-series variable):

* `PowerSeries.adamsExpand R n`: the combined Adams substitution `ψ ^ n` on `(R⸨X⸩)⟦X⟧` sending
  `q ↦ q ^ n` (via `LaurentSeries.expand`) and `t ↦ t ^ n` (via `PowerSeries.expand`).
* `PowerSeries.plethysticLogSum F`: the plethystic logarithmic sum
  `∑_{n ≥ 1} ψ ^ n (F) / n`, whose `t ^ k` coefficient only involves `1 ≤ n ≤ k`.
* `PowerSeries.plethysticExp F`: the plethystic exponential
  `PE(F) = exp (∑_{n ≥ 1} ψ ^ n (F) / n)`.

The construction operates directly by formal power-series substitution without general
`λ`-ring theory.

## Main results

* `PowerSeries.adamsExpand_one`, `PowerSeries.adamsExpand_adamsExpand`: functoriality
  `ψ ^ 1 = id` and `ψ ^ m ∘ ψ ^ n = ψ ^ (m * n)`.
* `PowerSeries.adamsExpand_C_const`, `PowerSeries.adamsExpand_C_single_mul_X_pow`: `ψ ^ n` fixes
  constants and sends `r q ^ i t ^ j` to `r q ^ (n i) t ^ (n j)`.
* `PowerSeries.plethysticExp_zero`, `PowerSeries.constantCoeff_plethysticExp`,
  `PowerSeries.plethysticExp_add`, `PowerSeries.plethysticExp_neg_mul`: `PE(0) = 1`,
  `constantCoeff (PE(F)) = 1`, `PE(F + G) = PE(F) PE(G)`, and `PE(-F) PE(F) = 1`.
* `PowerSeries.adamsExpand_plethysticExp`: Adams compatibility
  `ψ ^ m (PE(F)) = PE(ψ ^ m (F))`.
* `PowerSeries.plethysticExp_single_mul_X_pow_mul`,
  `PowerSeries.plethysticExp_neg_single_mul_X_pow`: for `j ≠ 0`,
  `PE(q ^ i t ^ j) * (1 - q ^ i t ^ j) = 1` and `PE(-q ^ i t ^ j) = 1 - q ^ i t ^ j`.
* `PowerSeries.exists_map_eq_plethysticExp`, `PowerSeries.existsUnique_map_eq_plethysticExp`:
  integrality of `PE(F)` for `F ∈ (ℤ⸨X⸩)⟦X⟧`, proved by reducing to finite products at each
  pair of `q`-adic and `t`-adic precisions.

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*
  (winter 2024/25), Definitions 5.4–5.5 and the monomial product calculation, pp. 26–27.
-/

public section

open Finset HahnSeries
open scoped LaurentSeries PowerSeries

namespace PowerSeries

/-! ### Combined Adams substitution on `(R⸨X⸩)⟦X⟧` -/

section AdamsExpand

variable (R : Type*) [CommRing R]

/-- The **combined Adams substitution** `ψ ^ n` on `(R⸨X⸩)⟦X⟧`, dilating both the Laurent variable
`q ↦ q ^ n` (via `LaurentSeries.expand`) and the power-series variable `t ↦ t ^ n` (via
`PowerSeries.expand`). -/
noncomputable def adamsExpand (n : ℕ+) : (R⸨X⸩)⟦X⟧ →ₐ[R] (R⸨X⸩)⟦X⟧ where
  toRingHom :=
    (PowerSeries.expand (n : ℕ) n.ne_zero).toRingHom.comp
      (PowerSeries.map (LaurentSeries.expand R n).toRingHom)
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      algebraMap_apply, map_C, expand_C]
    exact congrArg C ((LaurentSeries.expand R n).commutes r)

variable {R}

/-- Unfolding formula for `PowerSeries.adamsExpand`. -/
theorem adamsExpand_apply (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    adamsExpand R n F =
      PowerSeries.expand (n : ℕ) n.ne_zero
        (PowerSeries.map (LaurentSeries.expand R n).toRingHom F) :=
  (rfl)

/-- The `t ^ (n * k)` coefficient of `ψ ^ n (F)` is `LaurentSeries.expand R n (coeff k F)`. -/
@[simp]
theorem coeff_adamsExpand_mul (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) (k : ℕ) :
    coeff ((n : ℕ) * k) (adamsExpand R n F) = LaurentSeries.expand R n (coeff k F) := by
  rw [adamsExpand_apply, coeff_expand_mul, coeff_map]
  rfl

/-- Coefficients of `ψ ^ n (F)` at `t`-exponents not divisible by `n` vanish. -/
theorem coeff_adamsExpand_of_not_dvd (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) {k : ℕ} (hk : ¬ (n : ℕ) ∣ k) :
    coeff k (adamsExpand R n F) = 0 := by
  rw [adamsExpand_apply, coeff_expand_of_not_dvd (n : ℕ) n.ne_zero _ hk]

/-- The `[q ^ (n * i) t ^ (n * k)]` coefficient of `ψ ^ n (F)` equals `[q ^ i t ^ k] F`. -/
theorem coeff_coeff_adamsExpand_mul (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) (k : ℕ) (i : ℤ) :
    (coeff ((n : ℕ) * k) (adamsExpand R n F)).coeff ((n : ℤ) * i) = (coeff k F).coeff i := by
  rw [coeff_adamsExpand_mul, LaurentSeries.coeff_expand_mul]

/-- `ψ ^ n` acts on `t`-constants by `LaurentSeries.expand R n`. -/
@[simp]
theorem adamsExpand_C (n : ℕ+) (c : R⸨X⸩) :
    adamsExpand R n (C c) = C (LaurentSeries.expand R n c) := by
  rw [adamsExpand_apply, map_C, expand_C]
  rfl

/-- `ψ ^ n` fixes scalar constants `C (HahnSeries.C r)`. -/
theorem adamsExpand_C_const (n : ℕ+) (r : R) :
    adamsExpand R n (C (HahnSeries.C r)) = C (HahnSeries.C r) := by
  rw [adamsExpand_C, HahnSeries.C_apply, LaurentSeries.expand_single, mul_zero]

/-- `ψ ^ n` sends `t` to `t ^ n`. -/
@[simp]
theorem adamsExpand_X (n : ℕ+) :
    adamsExpand R n (X : (R⸨X⸩)⟦X⟧) = X ^ (n : ℕ) := by
  rw [adamsExpand_apply, map_X, expand_X]

/-- `ψ ^ n` sends the monomial `r q ^ i t ^ j` to `r q ^ (n i) t ^ (n j)`. -/
@[simp]
theorem adamsExpand_C_single_mul_X_pow (n : ℕ+) (i : ℤ) (r : R) (j : ℕ) :
    adamsExpand R n (C (single i r) * X ^ j) =
      C (single ((n : ℤ) * i) r) * X ^ ((n : ℕ) * j) := by
  rw [map_mul, adamsExpand_C, LaurentSeries.expand_single, map_pow, adamsExpand_X, ← pow_mul]

/-- The `t`-constant term of `ψ ^ n (F)` is `LaurentSeries.expand R n (constantCoeff F)`. -/
@[simp]
theorem constantCoeff_adamsExpand (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    constantCoeff (adamsExpand R n F) = LaurentSeries.expand R n (constantCoeff F) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← mul_zero (n : ℕ), coeff_adamsExpand_mul,
    coeff_zero_eq_constantCoeff_apply]

variable (R) in
/-- `ψ ^ 1` is the identity algebra homomorphism. -/
@[simp]
theorem adamsExpand_one : adamsExpand R 1 = AlgHom.id R (R⸨X⸩)⟦X⟧ := by
  ext F k i
  simpa using coeff_coeff_adamsExpand_mul 1 F k i

/-- Functoriality of combined Adams dilation: `ψ ^ m (ψ ^ n (F)) = ψ ^ (m * n) (F)`. -/
theorem adamsExpand_adamsExpand (m n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    adamsExpand R m (adamsExpand R n F) = adamsExpand R (m * n) F := by
  have hcomp :
      (LaurentSeries.expand R m).toRingHom.comp (LaurentSeries.expand R n).toRingHom =
        (LaurentSeries.expand R (m * n)).toRingHom :=
    RingHom.ext fun x ↦ LaurentSeries.expand_expand m n x
  rw [adamsExpand_apply, adamsExpand_apply, adamsExpand_apply,
    map_expand (n : ℕ) n.ne_zero (LaurentSeries.expand R m).toRingHom,
    ← expand_mul (m : ℕ) m.ne_zero (n : ℕ) n.ne_zero, ← RingHom.comp_apply,
    ← PowerSeries.map_comp, hcomp]
  rfl

/-- Coefficientwise ring homomorphisms commute with `LaurentSeries.expand`. -/
private theorem mapRingHom_laurentExpand {S : Type*} [CommSemiring S] (φ : R →+* S) (n : ℕ+)
    (x : R⸨X⸩) :
    HahnSeries.mapRingHom φ (LaurentSeries.expand R n x) =
      LaurentSeries.expand S n (HahnSeries.mapRingHom φ x) := by
  ext k
  rw [coeff_mapRingHom]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := hk
    rw [LaurentSeries.coeff_expand_mul, LaurentSeries.coeff_expand_mul, coeff_mapRingHom]
  · rw [LaurentSeries.coeff_expand_of_not_dvd n _ hk,
      LaurentSeries.coeff_expand_of_not_dvd n _ hk, map_zero]

/-- Coefficientwise ring homomorphisms commute with `PowerSeries.adamsExpand`. -/
theorem map_adamsExpand {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    PowerSeries.map (HahnSeries.mapRingHom φ) (adamsExpand R n F) =
      adamsExpand S n (PowerSeries.map (HahnSeries.mapRingHom φ) F) := by
  have hcomp :
      (HahnSeries.mapRingHom φ).comp (LaurentSeries.expand R n).toRingHom =
        (LaurentSeries.expand S n).toRingHom.comp (HahnSeries.mapRingHom φ) :=
    RingHom.ext fun x ↦ mapRingHom_laurentExpand φ n x
  rw [adamsExpand_apply, adamsExpand_apply, map_expand, ← RingHom.comp_apply,
    ← PowerSeries.map_comp, ← RingHom.comp_apply, ← PowerSeries.map_comp, hcomp]

/-- Combined Adams dilation commutes with substitution into `PowerSeries.exp`. -/
theorem adamsExpand_subst_exp {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ+)
    {G : (A⸨X⸩)⟦X⟧} (hG : HasSubst G) :
    adamsExpand A n ((PowerSeries.exp A⸨X⸩).subst G) =
      (PowerSeries.exp A⸨X⸩).subst (adamsExpand A n G) := by
  have hsub' : HasSubst (PowerSeries.map (LaurentSeries.expand A n).toRingHom G) := by
    obtain ⟨m, hm⟩ := hG
    refine ⟨m, ?_⟩
    have hm' : constantCoeff G ^ m = 0 := hm
    have hpow : constantCoeff (PowerSeries.map (LaurentSeries.expand A n).toRingHom G) ^ m = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        ← map_pow, hm', map_zero]
    exact hpow
  have hmap : PowerSeries.map (LaurentSeries.expand A n).toRingHom
        ((PowerSeries.exp A⸨X⸩).subst G) =
      (PowerSeries.map (LaurentSeries.expand A n).toRingHom (PowerSeries.exp A⸨X⸩)).subst
        (PowerSeries.map (LaurentSeries.expand A n).toRingHom G) :=
    PowerSeries.map_subst hG (PowerSeries.exp A⸨X⸩)
  have hexp : PowerSeries.expand (n : ℕ) n.ne_zero
        ((PowerSeries.exp A⸨X⸩).subst (PowerSeries.map (LaurentSeries.expand A n).toRingHom G)) =
      (PowerSeries.exp A⸨X⸩).subst
        (PowerSeries.expand (n : ℕ) n.ne_zero
          (PowerSeries.map (LaurentSeries.expand A n).toRingHom G)) :=
    PowerSeries.expand_subst (n : ℕ) n.ne_zero hsub' (PowerSeries.exp A⸨X⸩)
  rw [adamsExpand_apply, hmap, PowerSeries.map_exp, hexp, ← adamsExpand_apply]

end AdamsExpand

/-! ### Plethystic logarithmic sum and plethystic exponential -/

section Plethystic

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

/-- The **plethystic logarithmic sum** `∑_{n ≥ 1} ψ ^ n (F) / n` on `(A⸨X⸩)⟦X⟧`. Its `t ^ k`
coefficient only depends on `1 ≤ n ≤ k`, and its constant coefficient is always `0`. -/
noncomputable def plethysticLogSum (F : (A⸨X⸩)⟦X⟧) : (A⸨X⸩)⟦X⟧ :=
  PowerSeries.mk fun k ↦
    ∑ n ∈ range k, ((n + 1 : ℕ) : ℚ)⁻¹ • coeff k (adamsExpand A n.succPNat F)

/-- Coefficient formula for `PowerSeries.plethysticLogSum`. -/
@[simp]
theorem coeff_plethysticLogSum (F : (A⸨X⸩)⟦X⟧) (k : ℕ) :
    coeff k (plethysticLogSum F) =
      ∑ n ∈ range k, ((n + 1 : ℕ) : ℚ)⁻¹ • coeff k (adamsExpand A n.succPNat F) :=
  coeff_mk k _

/-- The `t`-constant term of `plethysticLogSum F` is `0`. -/
@[simp]
theorem constantCoeff_plethysticLogSum (F : (A⸨X⸩)⟦X⟧) :
    constantCoeff (plethysticLogSum F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_plethysticLogSum]
  simp

/-- For any truncation `N ≥ k`, the `t ^ k` coefficient of `plethysticLogSum F` equals the sum over
`n < N` whenever `k ≠ 0` (or `constantCoeff F = 0`). -/
theorem coeff_plethysticLogSum_eq_sum_range_of_le (F : (A⸨X⸩)⟦X⟧) {k N : ℕ}
    (hk : k ≠ 0 ∨ constantCoeff F = 0) (hN : k ≤ N) :
    coeff k (plethysticLogSum F) =
      ∑ n ∈ range N, ((n + 1 : ℕ) : ℚ)⁻¹ • coeff k (adamsExpand A n.succPNat F) := by
  rw [coeff_plethysticLogSum]
  refine Finset.sum_subset (range_mono hN) fun n _ hn ↦ ?_
  have hkn : k < n + 1 := by simp only [mem_range, not_lt] at hn; omega
  rcases hk with hk | hF
  · have hndvd : ¬ (n.succPNat : ℕ) ∣ k := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk) hkn
    rw [coeff_adamsExpand_of_not_dvd n.succPNat F hndvd, smul_zero]
  · rcases eq_or_ne k 0 with rfl | hk0
    · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_adamsExpand, hF, map_zero, smul_zero]
    · have hndvd : ¬ (n.succPNat : ℕ) ∣ k := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hkn
      rw [coeff_adamsExpand_of_not_dvd n.succPNat F hndvd, smul_zero]

@[simp]
theorem plethysticLogSum_zero : plethysticLogSum (0 : (A⸨X⸩)⟦X⟧) = 0 := by
  apply PowerSeries.ext
  intro k
  simp

theorem plethysticLogSum_add (F G : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (F + G) = plethysticLogSum F + plethysticLogSum G := by
  apply PowerSeries.ext
  intro k
  simp [Finset.sum_add_distrib, smul_add]

theorem plethysticLogSum_neg (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (-F) = -plethysticLogSum F := by
  apply PowerSeries.ext
  intro k
  simp [Finset.sum_neg_distrib]

theorem plethysticLogSum_sub (F G : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (F - G) = plethysticLogSum F - plethysticLogSum G := by
  rw [sub_eq_add_neg, plethysticLogSum_add, plethysticLogSum_neg, ← sub_eq_add_neg]

theorem plethysticLogSum_nsmul (m : ℕ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (m • F) = m • plethysticLogSum F := by
  apply PowerSeries.ext
  intro k
  simp only [coeff_plethysticLogSum, map_nsmul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

theorem plethysticLogSum_zsmul (m : ℤ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (m • F) = m • plethysticLogSum F := by
  apply PowerSeries.ext
  intro k
  simp only [coeff_plethysticLogSum, map_zsmul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

/-- Combined Adams dilation commutes with `plethysticLogSum`. -/
theorem adamsExpand_plethysticLogSum (m : ℕ+) (F : (A⸨X⸩)⟦X⟧) :
    adamsExpand A m (plethysticLogSum F) = plethysticLogSum (adamsExpand A m F) := by
  apply PowerSeries.ext
  intro k
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [coeff_zero_eq_constantCoeff_apply]
  by_cases hmd : (m : ℕ) ∣ k
  · obtain ⟨d, rfl⟩ := hmd
    have hdle : d ≤ (m : ℕ) * d := Nat.le_mul_of_pos_left d m.pos
    rw [coeff_adamsExpand_mul, coeff_plethysticLogSum, map_sum, coeff_plethysticLogSum]
    refine Finset.sum_subset_zero_on_sdiff (range_mono hdle) (fun n hn ↦ ?_) (fun n _ ↦ ?_)
    · simp only [mem_sdiff, mem_range, not_lt] at hn
      have hndvd : ¬ ((n.succPNat * m : ℕ+) : ℕ) ∣ (m : ℕ) * d := by
        have hlt : (m : ℕ) * d < (n + 1) * (m : ℕ) := by
          rw [mul_comm (n + 1)]
          exact Nat.mul_lt_mul_of_pos_left (by omega) m.pos
        exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hlt
      rw [adamsExpand_adamsExpand, coeff_adamsExpand_of_not_dvd (n.succPNat * m) F hndvd,
        smul_zero]
    · rw [map_rat_smul (LaurentSeries.expand A m), ← coeff_adamsExpand_mul m,
        adamsExpand_adamsExpand, adamsExpand_adamsExpand, mul_comm m]
  · rw [coeff_adamsExpand_of_not_dvd m _ hmd, coeff_plethysticLogSum]
    symm
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    have hndvd : ¬ ((n.succPNat * m : ℕ+) : ℕ) ∣ k := fun h ↦
      hmd (dvd_trans (dvd_mul_left _ _) h)
    rw [adamsExpand_adamsExpand, coeff_adamsExpand_of_not_dvd (n.succPNat * m) F hndvd, smul_zero]

/-- Coefficientwise ring homomorphisms between `ℚ`-algebras commute with `plethysticLogSum`. -/
theorem map_plethysticLogSum (φ : A →+* B) (F : (A⸨X⸩)⟦X⟧) :
    PowerSeries.map (HahnSeries.mapRingHom φ) (plethysticLogSum F) =
      plethysticLogSum (PowerSeries.map (HahnSeries.mapRingHom φ) F) := by
  apply PowerSeries.ext
  intro k
  simp only [coeff_map, coeff_plethysticLogSum, map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [map_rat_smul (HahnSeries.mapRingHom φ), ← coeff_map, map_adamsExpand]

/-- The **plethystic exponential** `PE(F) = exp (∑_{n ≥ 1} ψ ^ n (F) / n)` on `(A⸨X⸩)⟦X⟧`. -/
noncomputable def plethysticExp (F : (A⸨X⸩)⟦X⟧) : (A⸨X⸩)⟦X⟧ :=
  (PowerSeries.exp A⸨X⸩).subst (plethysticLogSum F)

@[simp]
theorem plethysticExp_zero : plethysticExp (0 : (A⸨X⸩)⟦X⟧) = 1 := by
  rw [plethysticExp, plethysticLogSum_zero, ← map_zero (C (R := A⸨X⸩))]
  apply PowerSeries.ext
  intro k
  rw [coeff_subst_eq_sum_range _ (by simp)]
  rcases k with _ | k
  · simp
  · rw [coeff_one, ite_eq_right (fun h ↦ absurd h (Nat.succ_ne_zero k))]
    refine Finset.sum_eq_zero fun d _ ↦ ?_
    rcases d with _ | d
    · simp
    · simp [zero_pow (Nat.succ_ne_zero d)]

@[simp]
theorem constantCoeff_plethysticExp (F : (A⸨X⸩)⟦X⟧) :
    constantCoeff (plethysticExp F) = 1 :=
  constantCoeff_subst_exp (constantCoeff_plethysticLogSum F)

/-- The formal logarithm of `PE(F)` is `plethysticLogSum F`. -/
@[simp]
theorem logOf_plethysticExp (F : (A⸨X⸩)⟦X⟧) :
    logOf (plethysticExp F) = plethysticLogSum F :=
  logOf_subst_exp (constantCoeff_plethysticLogSum F)

/-- **Additivity-to-multiplicativity**: `PE(F + G) = PE(F) * PE(G)`. -/
theorem plethysticExp_add (F G : (A⸨X⸩)⟦X⟧) :
    plethysticExp (F + G) = plethysticExp F * plethysticExp G := by
  refine (logOf_inj (constantCoeff_plethysticExp _) (by simp)).mp ?_
  rw [logOf_mul (constantCoeff_plethysticExp F) (constantCoeff_plethysticExp G),
    logOf_plethysticExp, logOf_plethysticExp, logOf_plethysticExp, plethysticLogSum_add]

/-- `PE` converts finite sums into finite products. -/
theorem plethysticExp_sum {ι : Type*} (s : Finset ι) (f : ι → (A⸨X⸩)⟦X⟧) :
    plethysticExp (∑ i ∈ s, f i) = ∏ i ∈ s, plethysticExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, plethysticExp_add, ih]

/-- `PE(-F) * PE(F) = 1`. -/
theorem plethysticExp_neg_mul (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (-F) * plethysticExp F = 1 := by
  rw [← plethysticExp_add, neg_add_cancel, plethysticExp_zero]

/-- `PE(m • F) = PE(F) ^ m` for `m : ℕ`. -/
theorem plethysticExp_nsmul (m : ℕ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (m • F) = plethysticExp F ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, plethysticExp_add, ih, pow_succ]

/-- **Adams compatibility**: `ψ ^ m (PE(F)) = PE(ψ ^ m (F))`. -/
theorem adamsExpand_plethysticExp (m : ℕ+) (F : (A⸨X⸩)⟦X⟧) :
    adamsExpand A m (plethysticExp F) = plethysticExp (adamsExpand A m F) := by
  rw [plethysticExp,
    adamsExpand_subst_exp m (HasSubst.of_constantCoeff_zero' (constantCoeff_plethysticLogSum F)),
    adamsExpand_plethysticLogSum, plethysticExp]

/-- Coefficientwise ring homomorphisms between `ℚ`-algebras commute with `plethysticExp`. -/
theorem map_plethysticExp (φ : A →+* B) (F : (A⸨X⸩)⟦X⟧) :
    PowerSeries.map (HahnSeries.mapRingHom φ) (plethysticExp F) =
      plethysticExp (PowerSeries.map (HahnSeries.mapRingHom φ) F) := by
  have hsub : HasSubst (plethysticLogSum F) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_plethysticLogSum F)
  have hmap : PowerSeries.map (HahnSeries.mapRingHom φ)
        ((PowerSeries.exp A⸨X⸩).subst (plethysticLogSum F)) =
      (PowerSeries.map (HahnSeries.mapRingHom φ) (PowerSeries.exp A⸨X⸩)).subst
        (PowerSeries.map (HahnSeries.mapRingHom φ) (plethysticLogSum F)) :=
    PowerSeries.map_subst hsub (PowerSeries.exp A⸨X⸩)
  rw [plethysticExp, hmap, PowerSeries.map_exp, map_plethysticLogSum, plethysticExp]

/-- The `t ^ k` coefficient of `PE(F)` only depends on the coefficients `coeff j F` for
`1 ≤ j ≤ k`. -/
theorem coeff_plethysticExp_eq_of_coeff_eq {F₁ F₂ : (A⸨X⸩)⟦X⟧} {k : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ k → coeff j F₁ = coeff j F₂) :
    coeff k (plethysticExp F₁) = coeff k (plethysticExp F₂) := by
  have hlog : ∀ j ≤ k, coeff j (plethysticLogSum F₁) = coeff j (plethysticLogSum F₂) := by
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj0
    · simp [coeff_zero_eq_constantCoeff_apply]
    rw [coeff_plethysticLogSum, coeff_plethysticLogSum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hd : (n.succPNat : ℕ) ∣ j
    · obtain ⟨d, rfl⟩ := hd
      have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (right_ne_zero_of_mul hj0)
      have hdk : d ≤ k := le_trans (Nat.le_mul_of_pos_left d n.succPNat.pos) hj
      rw [coeff_adamsExpand_mul n.succPNat, coeff_adamsExpand_mul n.succPNat, h d hd1 hdk]
    · rw [coeff_adamsExpand_of_not_dvd n.succPNat F₁ hd,
        coeff_adamsExpand_of_not_dvd n.succPNat F₂ hd]
  have hdiff : ∀ j ≤ k, coeff j (plethysticLogSum (F₁ - F₂)) = 0 := fun j hj ↦ by
    rw [plethysticLogSum_sub, map_sub, hlog j hj, sub_self]
  obtain ⟨E', hE'⟩ := X_dvd_iff.mpr (by simp : constantCoeff (PowerSeries.exp A⸨X⸩ - 1) = 0)
  have hsub : HasSubst (plethysticLogSum (F₁ - F₂)) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_plethysticLogSum _)
  have hpe_sub : plethysticExp (F₁ - F₂) - 1 =
      plethysticLogSum (F₁ - F₂) * E'.subst (plethysticLogSum (F₁ - F₂)) := by
    rw [plethysticExp, ← subst_one (R := A⸨X⸩) (a := plethysticLogSum (F₁ - F₂)),
      ← subst_sub hsub, hE', subst_mul hsub, subst_X hsub]
  have hpe_zero : ∀ j ≤ k, coeff j (plethysticExp (F₁ - F₂) - 1) = 0 := fun j hj ↦ by
    rw [hpe_sub, coeff_mul]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hle : x.1 ≤ k := le_trans (Nat.le_of_add_right_le (mem_antidiagonal.mp hx).le) hj
    rw [hdiff x.1 hle, zero_mul]
  have hsplit : plethysticExp F₁ =
      plethysticExp F₂ + plethysticExp F₂ * (plethysticExp (F₁ - F₂) - 1) := by
    rw [mul_sub, mul_one, add_sub_cancel, ← plethysticExp_add, add_sub_cancel]
  rw [hsplit, map_add, coeff_mul]
  suffices ∑ x ∈ antidiagonal k, coeff x.1 (plethysticExp F₂) *
      coeff x.2 (plethysticExp (F₁ - F₂) - 1) = 0 by rw [this, add_zero]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  have hle : x.2 ≤ k := Nat.le_of_add_left_le (mem_antidiagonal.mp hx).le
  rw [hpe_zero x.2 hle, mul_zero]

/-! ### Monomial plethystic formulas -/

/-- Logarithmic sum of a positive-degree monomial `q ^ i t ^ j` (`j ≠ 0`) is the `j`-fold
expansion of `∑_{n ≥ 1} (q ^ i) ^ n t ^ n / n`. -/
theorem plethysticLogSum_single_mul_X_pow (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticLogSum (C (single i (1 : A)) * X ^ j) =
      PowerSeries.expand j hj (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • (single i (1 : A)) ^ n) := by
  apply PowerSeries.ext
  intro k
  rw [coeff_plethysticLogSum, coeff_expand]
  by_cases hjk : j ∣ k
  · obtain ⟨d, rfl⟩ := hjk
    rw [ite_eq_left ⟨d, rfl⟩, Nat.mul_div_cancel_left d (Nat.pos_of_ne_zero hj), coeff_mk]
    rcases d with _ | d
    · simp
    · rw [Finset.sum_eq_single d]
      · have hmul : (d.succPNat : ℕ) * j = j * (d + 1) := by
          simp [mul_comm]
        rw [adamsExpand_C_single_mul_X_pow, hmul, coeff_C_mul_X_pow, ite_eq_left rfl,
          HahnSeries.single_pow, one_pow, nsmul_eq_mul]
        simp
      · intro n _ hnd
        have hne : j * (d + 1) ≠ (n.succPNat : ℕ) * j := by
          intro heq
          have : d + 1 = n + 1 :=
            Nat.mul_right_cancel (Nat.pos_of_ne_zero hj) ((mul_comm (d + 1) j).trans heq)
          omega
        rw [adamsExpand_C_single_mul_X_pow, coeff_C_mul_X_pow, ite_eq_right hne, smul_zero]
      · intro hdnot
        exfalso
        apply hdnot
        rw [mem_range]
        exact lt_of_lt_of_le (Nat.lt_succ_self d)
          (Nat.le_mul_of_pos_left (d + 1) (Nat.pos_of_ne_zero hj))
  · rw [ite_eq_right hjk]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    have hne : k ≠ (n.succPNat : ℕ) * j := fun heq ↦ hjk ⟨n + 1, by
      have : k = (n + 1) * j := heq
      linarith⟩
    rw [adamsExpand_C_single_mul_X_pow, coeff_C_mul_X_pow, ite_eq_right hne, smul_zero]

/-- Formal logarithm of `1 - c X ^ j` (`j ≠ 0`) as the `j`-fold expansion of
`-∑ c ^ n X ^ n / n`. -/
private theorem logOf_one_sub_C_mul_X_pow {R : Type*} [CommRing R] [Algebra ℚ R] (c : R)
    {j : ℕ} (hj : j ≠ 0) :
    logOf (1 - C c * X ^ j) =
      PowerSeries.expand j hj (PowerSeries.mk fun n ↦ -(algebraMap ℚ R (n : ℚ)⁻¹ * c ^ n)) := by
  have hsub : HasSubst (-(C c * X) : R⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hbase := congrArg (PowerSeries.expand j hj) (logOf_one_sub_C_mul_X c)
  have hexp : PowerSeries.expand j hj ((PowerSeries.log R).subst (-(C c * X))) =
      (PowerSeries.log R).subst (PowerSeries.expand j hj (-(C c * X))) :=
    PowerSeries.expand_subst j hj hsub (PowerSeries.log R)
  have h1 : (1 - C c * X - 1 : R⟦X⟧) = -(C c * X) := by ring
  have h2 : (1 - C c * X ^ j - 1 : R⟦X⟧) = -(C c * X ^ j) := by ring
  rw [logOf_eq, h1] at hbase
  rw [logOf_eq, h2, ← expand_X j hj, ← expand_C j hj, ← map_mul, ← map_neg, ← hexp, hbase]
  congr 1
  apply PowerSeries.ext
  intro n
  rw [coeff_mk, coeff_mk, Algebra.smul_def, mul_neg]

/-- **Monomial plethystic exponential**: for `j ≠ 0`,
`PE(q ^ i t ^ j) * (1 - q ^ i t ^ j) = 1`. -/
theorem plethysticExp_single_mul_X_pow_mul (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticExp (C (single i (1 : A)) * X ^ j) * (1 - C (single i (1 : A)) * X ^ j) = 1 := by
  let c : A⸨X⸩ := single i (1 : A)
  have h1 : constantCoeff (1 - C c * X ^ j) = 1 := by simp [hj]
  refine (logOf_inj (by simp [hj]) constantCoeff_one).mp ?_
  rw [logOf_mul (constantCoeff_plethysticExp _) h1, logOf_plethysticExp, logOf_one,
    plethysticLogSum_single_mul_X_pow i hj, logOf_one_sub_C_mul_X_pow (R := A⸨X⸩) c hj]
  apply PowerSeries.ext
  intro k
  rw [map_add, coeff_expand, coeff_expand, map_zero]
  split_ifs with hjk
  · rw [coeff_mk, coeff_mk]
    ext r
    rw [HahnSeries.coeff_add, HahnSeries.coeff_zero, HahnSeries.coeff_smul, HahnSeries.coeff_neg,
      HahnSeries.algebraMap_apply', IsScalarTower.algebraMap_apply ℚ A A⟦X⟧,
      ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
      HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
      ← Algebra.smul_def, add_neg_cancel]
  · simp

/-- **Negative monomial plethystic exponential**: for `j ≠ 0`,
`PE(-q ^ i t ^ j) = 1 - q ^ i t ^ j`. -/
theorem plethysticExp_neg_single_mul_X_pow (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticExp (-(C (single i (1 : A)) * X ^ j)) = 1 - C (single i (1 : A)) * X ^ j := by
  have hu : IsUnit (plethysticExp (C (single i (1 : A)) * X ^ j)) :=
    isUnit_iff_constantCoeff.mpr (by simp)
  apply hu.mul_left_cancel
  rw [mul_comm (plethysticExp (C (single i (1 : A)) * X ^ j)),
    plethysticExp_neg_mul, plethysticExp_single_mul_X_pow_mul i hj]

/-- `PE(t) * (1 - t) = 1`. -/
theorem plethysticExp_X_mul :
    plethysticExp (X : (A⸨X⸩)⟦X⟧) * (1 - X) = 1 := by
  simpa using plethysticExp_single_mul_X_pow_mul (A := A) 0 one_ne_zero

/-- `PE(-t) = 1 - t`. -/
theorem plethysticExp_neg_X :
    plethysticExp (-X : (A⸨X⸩)⟦X⟧) = 1 - X := by
  simpa using plethysticExp_neg_single_mul_X_pow (A := A) 0 one_ne_zero

/-- The `t ^ k` coefficient of `plethysticLogSum (-t)` is `-(k : ℚ)⁻¹ • 1`. -/
theorem coeff_plethysticLogSum_neg_X (k : ℕ) :
    coeff k (plethysticLogSum (-X : (A⸨X⸩)⟦X⟧)) = -((k : ℚ)⁻¹ • (1 : A⸨X⸩)) := by
  have h := congrArg (coeff k) (plethysticLogSum_single_mul_X_pow (A := A) 0 one_ne_zero)
  simp only [single_zero_one, map_one, pow_one, one_mul, expand_one_apply, coeff_mk, one_pow] at h
  rw [plethysticLogSum_neg, map_neg, h]

end Plethystic

/-! ### Integrality of `PE(F)` for `F ∈ (ℤ⸨X⸩)⟦X⟧` -/

section Integrality

/-- If `x` vanishes below `M` and `y` vanishes below `N`, then `x * y` vanishes below `M + N`. -/
private theorem coeff_laurent_mul_eq_zero_of_lt {R : Type*} [Semiring R] {x y : R⸨X⸩} {M N r : ℤ}
    (hx : ∀ i < M, x.coeff i = 0) (hy : ∀ i < N, y.coeff i = 0) (hr : r < M + N) :
    (x * y).coeff r = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  simp only [Finset.mem_antidiagonal, HahnSeries.mem_support] at hp
  have hp1 : M ≤ p.1 := not_lt.mp fun h ↦ hp.1 (hx p.1 h)
  have hp2 : N ≤ p.2 := not_lt.mp fun h ↦ hp.2.1 (hy p.2 h)
  omega

/-- Closure of the slope-`m` Laurent support bound under multiplication in `(R⸨X⸩)⟦X⟧`. -/
private theorem slope_bound_mul {R : Type*} [CommRing R] {m : ℤ} {G₁ G₂ : (R⸨X⸩)⟦X⟧}
    (h₁ : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G₁).coeff s = 0)
    (h₂ : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G₂).coeff s = 0) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (G₁ * G₂)).coeff s = 0 := by
  intro a s hs
  rw [coeff_mul, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  have hab : (x.1 : ℤ) * m + (x.2 : ℤ) * m = (a : ℤ) * m := by
    have : x.1 + x.2 = a := mem_antidiagonal.mp hx
    push_cast [← this]
    ring
  exact coeff_laurent_mul_eq_zero_of_lt (h₁ x.1) (h₂ x.2) (hab ▸ hs)

/-- Closure of the slope-`m` Laurent support bound under natural powers in `(R⸨X⸩)⟦X⟧`. -/
private theorem slope_bound_pow {R : Type*} [CommRing R] {m : ℤ} {G : (R⸨X⸩)⟦X⟧}
    (hG : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0) (n : ℕ) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (G ^ n)).coeff s = 0 := by
  induction n with
  | zero =>
    intro a s hs
    rcases a with _ | a
    · simp only [pow_zero, Nat.cast_zero, zero_mul] at hs ⊢
      rw [coeff_zero_eq_constantCoeff_apply, map_one, HahnSeries.coeff_one]
      exact ite_eq_right (ne_of_lt hs)
    · simp
  | succ n ih =>
    rw [pow_succ]
    exact slope_bound_mul ih hG

/-- Integral geometric series `(1 - q ^ i t ^ j)⁻¹` in `(ℤ⸨X⸩)⟦X⟧` matching `PE(q ^ i t ^ j)`
over `ℚ` and satisfying the slope-`m` Laurent support bound. -/
private theorem exists_inv_one_sub_single_mul_X_pow (i : ℤ) {j : ℕ} (hj : j ≠ 0)
    {m : ℤ} (hm : m ≤ 0) (hi : m ≤ i) :
    ∃ U : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) U =
        plethysticExp (C (single i (1 : ℚ)) * X ^ j) ∧
      ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a U).coeff s = 0 := by
  let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
  let U : (ℤ⸨X⸩)⟦X⟧ := PowerSeries.expand j hj (PowerSeries.mk fun d ↦ single ((d : ℤ) * i) (1 : ℤ))
  have hU_mul : U * (1 - C (single i (1 : ℤ)) * X ^ j) = 1 := by
    have h1 : (PowerSeries.mk fun d ↦ single ((d : ℤ) * i) (1 : ℤ)) *
        (1 - C (single i (1 : ℤ)) * X) = 1 := by
      apply PowerSeries.ext
      intro d
      rcases d with _ | d
      · simp
      · simp only [mul_sub, mul_one, map_sub, mul_left_comm _ (C _), coeff_C_mul,
          coeff_mk, coeff_one, Nat.succ_ne_zero, ↓reduceIte]
        rw [mul_comm _ X, coeff_succ_X_mul, coeff_mk, HahnSeries.single_mul_single, one_mul]
        have : i + (d : ℤ) * i = ((d + 1 : ℕ) : ℤ) * i := by push_cast; ring
        rw [this, sub_self]
    simpa [U, map_mul, map_sub, (PowerSeries.expand j hj).map_one, expand_C, expand_X] using
      congrArg (PowerSeries.expand j hj) h1
  refine ⟨U, ?_, ?_⟩
  · have hsing_map : PowerSeries.map ι (C (single i (1 : ℤ)) * X ^ j) =
        C (single i (1 : ℚ)) * X ^ j := by
      rw [map_mul, map_C, map_pow, map_X]
      congr 2
      ext r
      simp [ι, HahnSeries.coeff_single]
    have hunit : IsUnit (1 - C (single i (1 : ℚ)) * X ^ j) :=
      isUnit_iff_constantCoeff.mpr (by simp [hj])
    apply hunit.mul_right_cancel
    have hmap := congrArg (PowerSeries.map ι) hU_mul
    rw [map_mul, map_sub, map_one, hsing_map] at hmap
    rw [hmap, plethysticExp_single_mul_X_pow_mul i hj]
  · intro a s hs
    rw [coeff_expand]
    split_ifs with hd
    · rw [coeff_mk, HahnSeries.coeff_single]
      refine ite_eq_right fun hEq ↦ ?_
      have hda : ((a / j : ℕ) : ℤ) ≤ a := by exact_mod_cast Nat.div_le_self a j
      have h1 : (a : ℤ) * m ≤ ((a / j : ℕ) : ℤ) * m := by nlinarith
      have h2 : ((a / j : ℕ) : ℤ) * m ≤ ((a / j : ℕ) : ℤ) * i := by nlinarith
      omega
    · simp

/-- Integral realization and slope-`m` support bound for `PE(z • (q ^ i t ^ j))`. -/
private theorem exists_plethysticExp_zsmul_single (i : ℤ) {j : ℕ} (hj : j ≠ 0) (z : ℤ)
    {m : ℤ} (hm : m ≤ 0) (hi : m ≤ i) :
    ∃ G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) G =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ))
          (z • (C (single i (1 : ℤ)) * X ^ j))) ∧
      ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0 := by
  let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
  have hsing_map : PowerSeries.map ι (C (single i (1 : ℤ)) * X ^ j) =
      C (single i (1 : ℚ)) * X ^ j := by
    rw [map_mul, map_C, map_pow, map_X]
    congr 2
    ext r
    simp [ι, HahnSeries.coeff_single]
  have hV_bound : ∀ a : ℕ, ∀ s < (a : ℤ) * m,
      (coeff a (1 - C (single i (1 : ℤ)) * X ^ j)).coeff s = 0 := by
    intro a s hs
    rw [map_sub, coeff_one, coeff_C_mul_X_pow, HahnSeries.coeff_sub]
    rcases eq_or_ne a 0 with rfl | h0
    · simp only [Nat.cast_zero, zero_mul] at hs
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hj), HahnSeries.coeff_one,
        ite_eq_right (ne_of_lt hs), HahnSeries.coeff_zero, sub_zero]
    · rw [ite_eq_right h0, HahnSeries.coeff_zero, zero_sub]
      by_cases ha : a = j
      · subst ha
        have hj1 : (1 : ℤ) ≤ a := by exact_mod_cast Nat.pos_of_ne_zero hj
        have hjm : (a : ℤ) * m ≤ i := by nlinarith
        rw [ite_eq_left rfl, HahnSeries.coeff_single, ite_eq_right (by omega), neg_zero]
      · rw [ite_eq_right ha, HahnSeries.coeff_zero, neg_zero]
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · obtain ⟨U, hU_map, hU_bound⟩ := exists_inv_one_sub_single_mul_X_pow i hj hm hi
    refine ⟨U ^ n, ?_, slope_bound_pow hU_bound n⟩
    rw [map_pow, hU_map, ← plethysticExp_nsmul, natCast_zsmul, map_nsmul, hsing_map]
  · refine ⟨(1 - C (single i (1 : ℤ)) * X ^ j) ^ n, ?_, slope_bound_pow hV_bound n⟩
    rw [neg_smul, natCast_zsmul, map_neg, map_nsmul, hsing_map, ← smul_neg, plethysticExp_nsmul,
      plethysticExp_neg_single_mul_X_pow i hj, map_pow, map_sub, map_one, hsing_map]

/-- Integral realization and slope-`m` support bound for a finite integral double polynomial
supported in `1 ≤ j ≤ k` and `m ≤ i < N`. -/
private theorem exists_plethysticExp_lo (F : (ℤ⸨X⸩)⟦X⟧) (k : ℕ) {m N : ℤ} (hm : m ≤ 0) :
    let Flo : (ℤ⸨X⸩)⟦X⟧ :=
      ∑ j ∈ Icc 1 k, C (∑ i ∈ Ico m N, single i ((coeff j F).coeff i)) * X ^ j
    ∃ Glo : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) Glo =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) Flo) ∧
      ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a Glo).coeff s = 0 := by
  intro Flo
  let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
  have hFlo_eq : Flo = ∑ p ∈ Icc 1 k ×ˢ Ico m N,
      ((coeff p.1 F).coeff p.2) • (C (single p.2 (1 : ℤ)) * X ^ p.1) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    symm
    rw [← smul_mul_assoc, ← map_zsmul, zsmul_eq_mul,
      ← map_intCast (HahnSeries.C : ℤ →+* ℤ⸨X⸩), HahnSeries.C_apply,
      HahnSeries.single_mul_single, zero_add, mul_one, Int.cast_id]
  rw [hFlo_eq]
  have hterm : ∀ p ∈ Icc 1 k ×ˢ Ico m N, ∃ G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map ι G =
        plethysticExp (PowerSeries.map ι
          (((coeff p.1 F).coeff p.2) • (C (single p.2 (1 : ℤ)) * X ^ p.1))) ∧
      ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0 := fun p hp ↦ by
    rw [mem_product, mem_Icc, mem_Ico] at hp
    exact exists_plethysticExp_zsmul_single p.2 (by omega) _ hm hp.2.1
  choose Gp hGp using hterm
  refine ⟨∏ p ∈ (Icc 1 k ×ˢ Ico m N).attach, Gp p.1 p.2, ?_, ?_⟩
  · rw [map_prod, map_sum, plethysticExp_sum, ← Finset.prod_attach (Icc 1 k ×ˢ Ico m N)]
    exact Finset.prod_congr rfl fun p _ ↦ (hGp p.1 p.2).1
  · refine Finset.prod_induction (f := fun (p : { x // x ∈ Icc 1 k ×ˢ Ico m N }) ↦ Gp p.1 p.2)
      (fun (G : (ℤ⸨X⸩)⟦X⟧) ↦ ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0)
      (fun _ _ h₁ h₂ ↦ slope_bound_mul h₁ h₂) ?_ fun p _ ↦ (hGp p.1 p.2).2
    intro a s hs
    rcases a with _ | a
    · simp only [Nat.cast_zero, zero_mul] at hs
      rw [coeff_zero_eq_constantCoeff_apply, map_one, HahnSeries.coeff_one]
      exact ite_eq_right (ne_of_lt hs)
    · simp

/-- If every positive `t`-coefficient of `F` vanishes below `q`-degree `N > 0`, then every
positive `t`-coefficient of `plethysticLogSum F` vanishes below `q`-degree `N`. -/
private theorem coeff_plethysticLogSum_eq_zero_of_lt {F : (ℚ⸨X⸩)⟦X⟧} {N : ℤ} (hN : 0 < N)
    (hF : ∀ a, 1 ≤ a → ∀ s < N, (coeff a F).coeff s = 0) :
    ∀ a, 1 ≤ a → ∀ s < N, (coeff a (plethysticLogSum F)).coeff s = 0 := by
  intro a ha s hs
  rw [coeff_plethysticLogSum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [HahnSeries.coeff_smul]
  suffices (coeff a (adamsExpand ℚ n.succPNat F)).coeff s = 0 by rw [this, smul_zero]
  by_cases hda : (n.succPNat : ℕ) ∣ a
  · obtain ⟨d, rfl⟩ := hda
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (right_ne_zero_of_mul (Nat.ne_of_gt ha))
    rw [coeff_adamsExpand_mul n.succPNat]
    by_cases hds : ((n.succPNat : ℕ) : ℤ) ∣ s
    · obtain ⟨u, rfl⟩ := hds
      rw [LaurentSeries.coeff_expand_mul]
      have hn1 : (1 : ℤ) ≤ (n.succPNat : ℕ) := by exact_mod_cast n.succPNat.pos
      exact hF d hd1 u (by nlinarith)
    · exact LaurentSeries.coeff_expand_of_not_dvd n.succPNat _ hds
  · rw [coeff_adamsExpand_of_not_dvd n.succPNat F hda, HahnSeries.coeff_zero]

/-- If every positive `t`-coefficient of `F` vanishes below `q`-degree `N > 0`, then every
positive `t`-coefficient of `PE(F)` vanishes below `q`-degree `N`. -/
private theorem coeff_plethysticExp_eq_zero_of_lt {F : (ℚ⸨X⸩)⟦X⟧} {N : ℤ} (hN : 0 < N)
    (hF : ∀ a, 1 ≤ a → ∀ s < N, (coeff a F).coeff s = 0) :
    ∀ a, 1 ≤ a → ∀ s < N, (coeff a (plethysticExp F)).coeff s = 0 := by
  have hL := coeff_plethysticLogSum_eq_zero_of_lt hN hF
  have hLpow : ∀ d, 1 ≤ d → ∀ a, 1 ≤ a → ∀ s < N,
      (coeff a (plethysticLogSum F ^ d)).coeff s = 0 := by
    intro d hd
    induction d with
    | zero => omega
    | succ d ih =>
      rcases d with _ | d
      · simpa using hL
      · intro a _ s hs
        rw [pow_succ, coeff_mul, HahnSeries.coeff_sum]
        refine Finset.sum_eq_zero fun x _ ↦ ?_
        rcases eq_or_ne x.1 0 with h1 | h1
        · rw [h1, coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_plethysticLogSum,
            zero_pow (Nat.succ_ne_zero d), zero_mul, HahnSeries.coeff_zero]
        · rcases eq_or_ne x.2 0 with h2 | h2
          · rw [h2, coeff_zero_eq_constantCoeff_apply, constantCoeff_plethysticLogSum, mul_zero,
              HahnSeries.coeff_zero]
          · exact coeff_laurent_mul_eq_zero_of_lt (ih (Nat.succ_pos d) x.1 (Nat.pos_of_ne_zero h1))
              (hL x.2 (Nat.pos_of_ne_zero h2)) (by omega)
  intro a ha s hs
  rw [plethysticExp, coeff_subst_eq_sum_range _ (constantCoeff_plethysticLogSum F),
    HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rcases d with _ | d
  · rw [pow_zero, coeff_one, ite_eq_right (Nat.ne_of_gt ha), smul_zero, HahnSeries.coeff_zero]
  · rw [smul_eq_mul, coeff_exp, HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.single_zero_mul_eq_smul,
      HahnSeries.coeff_smul, hLpow (d + 1) (Nat.succ_pos d) a ha s hs, smul_zero]

/-- Subtracting the `q`-window `m ≤ i < N` from the first `k` positive `t`-coefficients of `F`
produces a series whose coefficients all vanish below `q`-degree `N`. -/
private theorem coeff_hiTail_eq_zero_of_lt (F : (ℤ⸨X⸩)⟦X⟧) (k : ℕ) {m N : ℤ}
    (hmle : ∀ j ∈ Icc 1 k, ∀ i < m, (coeff j F).coeff i = 0) :
    let Fhi : (ℤ⸨X⸩)⟦X⟧ :=
      ∑ j ∈ Icc 1 k, C (coeff j F - ∑ i ∈ Ico m N, single i ((coeff j F).coeff i)) * X ^ j
    ∀ a, 1 ≤ a → ∀ s < N,
      (coeff a (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) Fhi)).coeff s = 0 := by
  intro Fhi a _ s hs
  rw [coeff_map, HahnSeries.coeff_mapRingHom]
  suffices (coeff a Fhi).coeff s = 0 by rw [this, map_zero]
  rw [map_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with hja
  · subst hja
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_sum]
    by_cases hsm : s < m
    · rw [hmle a hj s hsm, Finset.sum_eq_zero (fun i hi ↦ by
        rw [HahnSeries.coeff_single, ite_eq_right (by rw [mem_Ico] at hi; omega)]), sub_zero]
    · rw [Finset.sum_eq_single s]
      · simp
      · intro i _ his; rw [HahnSeries.coeff_single, ite_eq_right his.symm]
      · intro hsnot; exact absurd (mem_Ico.mpr ⟨not_lt.mp hsm, hs⟩) hsnot
  · simp

/-- Multiplying a slope-`m` bounded series `G₁` by a series `G₂` with constant term `1` and
positive `t`-coefficients vanishing below `N` preserves `[q ^ r t ^ k]` whenever
`r < k * m + N` and `m ≤ 0`. -/
private theorem coeff_mul_eq_left_of_slope_bound {G₁ G₂ : (ℚ⸨X⸩)⟦X⟧} {k : ℕ} {m N r : ℤ}
    (hm : m ≤ 0) (hr : r < (k : ℤ) * m + N)
    (h₁ : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G₁).coeff s = 0)
    (h₂0 : constantCoeff G₂ = 1)
    (h₂ : ∀ a, 1 ≤ a → ∀ s < N, (coeff a G₂).coeff s = 0) :
    (coeff k (G₁ * G₂)).coeff r = (coeff k G₁).coeff r := by
  rw [coeff_mul, HahnSeries.coeff_sum, Finset.sum_eq_single (k, 0)]
  · rw [coeff_zero_eq_constantCoeff_apply, h₂0, mul_one]
  · intro x hx hne
    have hx2 : 1 ≤ x.2 := by
      have := mem_antidiagonal.mp hx
      rcases eq_or_ne x.2 0 with h0 | h0
      · exfalso; apply hne; ext <;> omega
      · exact Nat.pos_of_ne_zero h0
    have hxa : x.1 ≤ k := Nat.le_of_add_right_le (mem_antidiagonal.mp hx).le
    have hbound : r < (x.1 : ℤ) * m + N := by
      have hkm : (k : ℤ) * m ≤ (x.1 : ℤ) * m := by nlinarith
      linarith
    exact coeff_laurent_mul_eq_zero_of_lt (h₁ x.1) (h₂ x.2 hx2) hbound
  · intro hnot
    exact absurd (mem_antidiagonal.mpr (add_zero k)) hnot

/-- Truncating an integral series `F` to degrees `1 ≤ j ≤ k` preserves the `t ^ k` coefficient of
`PE(F)` over `ℚ`. -/
private theorem coeff_plethysticExp_eq_trunc (F : (ℤ⸨X⸩)⟦X⟧) (k : ℕ) :
    let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
    coeff k (plethysticExp (PowerSeries.map ι F)) =
      coeff k (plethysticExp (PowerSeries.map ι (∑ j ∈ Icc 1 k, C (coeff j F) * X ^ j))) := by
  intro ι
  refine coeff_plethysticExp_eq_of_coeff_eq fun j hj1 hjk ↦ ?_
  rw [coeff_map, coeff_map, map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hlj; simp [hlj.symm]
  · intro hjnot; exact absurd (mem_Icc.mpr ⟨hj1, hjk⟩) hjnot

/-- **Integrality over `ℚ`**: for any `F : (ℤ⸨X⸩)⟦X⟧`, `PE(F)` has integral coefficients, i.e.
lies in the image of `(ℤ⸨X⸩)⟦X⟧ → (ℚ⸨X⸩)⟦X⟧`. -/
private theorem exists_map_eq_plethysticExp_rat (F : (ℤ⸨X⸩)⟦X⟧) :
    ∃ G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) G =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) F) := by
  let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
  suffices hmem : ∀ k : ℕ, coeff k (plethysticExp (PowerSeries.map ι F)) ∈ ι.rangeS by
    choose g hg using hmem
    refine ⟨PowerSeries.mk g, ?_⟩
    apply PowerSeries.ext
    intro k
    rw [coeff_map, coeff_mk, hg k]
  intro k
  rw [HahnSeries.mem_map_rangeS]
  intro r
  rw [coeff_plethysticExp_eq_trunc F k]
  let m : ℤ := ∑ j ∈ Icc 1 k, min 0 (coeff j F).order
  have hm0 : m ≤ 0 := Finset.sum_nonpos fun j _ ↦ min_le_left _ _
  have hmle : ∀ j ∈ Icc 1 k, ∀ i < m, (coeff j F).coeff i = 0 := fun j hj i hi ↦ by
    have hsub : m - min 0 (coeff j F).order ≤ 0 := by
      rw [← Finset.sum_erase_eq_sub hj]
      exact Finset.sum_nonpos fun l _ ↦ min_le_left _ _
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi (by omega))
  let N : ℤ := max 1 (r - (k : ℤ) * m + 1)
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let Flo : (ℤ⸨X⸩)⟦X⟧ :=
    ∑ j ∈ Icc 1 k, C (∑ i ∈ Ico m N, single i ((coeff j F).coeff i)) * X ^ j
  let Fhi : (ℤ⸨X⸩)⟦X⟧ :=
    ∑ j ∈ Icc 1 k, C (coeff j F - ∑ i ∈ Ico m N, single i ((coeff j F).coeff i)) * X ^ j
  have hFsplit : (∑ j ∈ Icc 1 k, C (coeff j F) * X ^ j) = Flo + Fhi := by
    dsimp [Flo, Fhi]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [← add_mul, ← map_add, add_sub_cancel]
  obtain ⟨Glo, hGlo_map, hGlo_bound⟩ := exists_plethysticExp_lo F k (N := N) hm0
  have hEhi_van := coeff_plethysticExp_eq_zero_of_lt hNpos (coeff_hiTail_eq_zero_of_lt F k hmle)
  have hlo_q : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (PowerSeries.map ι Glo)).coeff s = 0 :=
    fun a s hs ↦ by rw [coeff_map, HahnSeries.coeff_mapRingHom, hGlo_bound a s hs, map_zero]
  have hrbound : r < (k : ℤ) * m + N := by
    have := le_max_right (1 : ℤ) (r - (k : ℤ) * m + 1)
    linarith
  rw [hFsplit, map_add, plethysticExp_add, ← hGlo_map,
    coeff_mul_eq_left_of_slope_bound hm0 hrbound hlo_q (constantCoeff_plethysticExp _) hEhi_van,
    coeff_map, HahnSeries.coeff_mapRingHom]
  exact ⟨(coeff k Glo).coeff r, rfl⟩

/-- **Integrality of the plethystic exponential**: for any `F : (ℤ⸨X⸩)⟦X⟧` and any `ℚ`-algebra
`A`, `PE(F)` lies in the image of `(ℤ⸨X⸩)⟦X⟧ → (A⸨X⸩)⟦X⟧`. -/
theorem exists_map_eq_plethysticExp {A : Type*} [CommRing A] [Algebra ℚ A] (F : (ℤ⸨X⸩)⟦X⟧) :
    ∃ G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom A)) G =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom A)) F) := by
  obtain ⟨G, hG⟩ := exists_map_eq_plethysticExp_rat F
  refine ⟨G, ?_⟩
  have hcomp : (algebraMap ℚ A).comp (Int.castRingHom ℚ) = Int.castRingHom A :=
    RingHom.ext fun z ↦ by simp
  have hmap := congrArg (PowerSeries.map (HahnSeries.mapRingHom (algebraMap ℚ A))) hG
  rw [map_plethysticExp, ← RingHom.comp_apply, ← PowerSeries.map_comp,
    ← RingHom.comp_apply, ← PowerSeries.map_comp, ← HahnSeries.mapRingHom_comp, hcomp] at hmap
  exact hmap

/-- Over any nontrivial `ℚ`-algebra, the integral lift `G : (ℤ⸨X⸩)⟦X⟧` of `PE(F)` is unique. -/
theorem existsUnique_map_eq_plethysticExp {A : Type*} [CommRing A] [Algebra ℚ A] [Nontrivial A]
    (F : (ℤ⸨X⸩)⟦X⟧) :
    ∃! G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom A)) G =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom A)) F) := by
  obtain ⟨G, hG⟩ := exists_map_eq_plethysticExp (A := A) F
  refine ⟨G, hG, fun G' hG' ↦ ?_⟩
  have hinjZ : Function.Injective (Int.castRingHom A) := by
    have hcomp : (algebraMap ℚ A).comp (Int.castRingHom ℚ) = Int.castRingHom A :=
      RingHom.ext fun z ↦ by simp
    rw [← hcomp]
    exact (RingHom.injective (algebraMap ℚ A)).comp Int.cast_injective
  have hinj : Function.Injective (HahnSeries.mapRingHom (Int.castRingHom A) : ℤ⸨X⸩ →+* A⸨X⸩) :=
    HahnSeries.mapRingHom_injective hinjZ
  apply PowerSeries.ext
  intro k
  exact hinj (by simpa [coeff_map] using congrArg (coeff k) (hG'.trans hG.symm))

end Integrality

end PowerSeries
