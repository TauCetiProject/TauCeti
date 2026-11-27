/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.PowerSeries.AdamsExpand
import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.QCalculus.Plethystic.SupportBounds
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# The elementary plethystic exponential

This file develops the elementary plethystic toolkit on power series with Laurent-series
coefficients `(A⸨X⸩)⟦X⟧` (writing `q` for the inner Laurent variable and `t` for the outer
power-series variable), directly via formal power-series substitution without general `λ`-rings,
using `PowerSeries.adamsExpand` (`ψ ^ n`) from `TauCeti.RingTheory.PowerSeries.AdamsExpand`:

* `PowerSeries.plethysticLogSum F` and `PowerSeries.plethysticLogSumHom`:
  `∑_{n ≥ 1} ψ ^ n (F - C (constantCoeff F)) / n` (which agrees with `∑_{n ≥ 1} ψ ^ n (F) / n`
  when `constantCoeff F = 0`, and whose `t ^ k` coefficient for `k ≥ 1` depends only on
  `1 ≤ n ≤ k`).
* `PowerSeries.plethysticExp F`, `PowerSeries.plethysticExpMonoidHom`, and
  `PowerSeries.plethysticExpUnitsHom`: `PE(F) = exp (plethysticLogSum F)`, satisfying
  additivity-to-multiplicativity (`_add`, `_neg`, `_sub`, `_nsmul`, `_zsmul`, `_sum`), Adams
  compatibility (`PowerSeries.adamsExpand_subst_exp`, `PowerSeries.adamsExpand_plethysticExp`),
  bidegree congruence (`PowerSeries.coeff_coeff_plethysticExp_eq_of_coeff_eq`),
  monomial product formulas, and integrality over `ℤ⸨X⸩⟦X⟧`.

## References

* W. J. G. Ong, notes of P. Scholze's course *V5A2 – The Habiro Ring of a Number Field*, Bonn,
  winter 2024/25 (6 March 2025 version,
  https://wgabrielong.github.io/academic-writing/notes/bonn-winter-24-25/V5A2-Habiro-Rings/Habiro_Rings_Notes.pdf),
  Definitions 5.4–5.5 and the monomial product calculation, pp. 26–27.
-/

public section

open Finset HahnSeries
open scoped LaurentSeries PowerSeries

namespace PowerSeries

/-! ### Plethystic logarithmic sum and plethystic exponential -/

section Plethystic

variable {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

/-- The **plethystic logarithmic sum** `∑_{n ≥ 1} ψ ^ n (F - C (constantCoeff F)) / n` on
`(A⸨X⸩)⟦X⟧`. Removing the `t`-constant term ensures `constantCoeff (plethysticLogSum F) = 0`, so
this agrees with `∑_{n ≥ 1} ψ ^ n (F) / n` whenever `constantCoeff F = 0`, and its `t ^ k`
coefficient only depends on `1 ≤ n ≤ k`. -/
noncomputable def plethysticLogSum (F : (A⸨X⸩)⟦X⟧) : (A⸨X⸩)⟦X⟧ :=
  PowerSeries.mk fun k ↦
    ∑ n ∈ range k, ((n + 1 : ℕ) : ℚ)⁻¹ • coeff k (adamsExpand A n.succPNat F)

/-- Coefficient formula for `PowerSeries.plethysticLogSum`. -/
@[simp] theorem coeff_plethysticLogSum (F : (A⸨X⸩)⟦X⟧) (k : ℕ) :
    coeff k (plethysticLogSum F) =
      ∑ n ∈ range k, ((n + 1 : ℕ) : ℚ)⁻¹ • coeff k (adamsExpand A n.succPNat F) :=
  coeff_mk k _

/-- The `t`-constant term of `plethysticLogSum F` is `0`. -/
@[simp] theorem constantCoeff_plethysticLogSum (F : (A⸨X⸩)⟦X⟧) :
    constantCoeff (plethysticLogSum F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_plethysticLogSum]; simp

/-- For any truncation `N ≥ k`, the `t ^ k` coefficient of `plethysticLogSum F` equals the sum over
`n < N` whenever `k ≠ 0` (or `constantCoeff F = 0`). -/
theorem coeff_plethysticLogSum_eq_sum_range_of_le (F : (A⸨X⸩)⟦X⟧) {k N : ℕ}
    (hk : k ≠ 0 ∨ constantCoeff F = 0) (hN : k ≤ N) :
    coeff k (plethysticLogSum F) =
      ∑ n ∈ range N, ((n + 1 : ℕ) : ℚ)⁻¹ • coeff k (adamsExpand A n.succPNat F) := by
  rw [coeff_plethysticLogSum]
  refine Finset.sum_subset (range_mono hN) fun n _ hn ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_adamsExpand, hk.resolve_left (by simp),
      map_zero, smul_zero]
  · have hkn : k < n + 1 := by simp only [mem_range, not_lt] at hn; omega
    rw [coeff_adamsExpand_of_not_dvd n.succPNat F
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hkn), smul_zero]

/-- The plethystic logarithmic sum of `0` is `0`. -/
@[simp] theorem plethysticLogSum_zero : plethysticLogSum (0 : (A⸨X⸩)⟦X⟧) = 0 := by ext k; simp

/-- The plethystic logarithmic sum is additive: `plethysticLogSum (F + G) = plethysticLogSum F +
plethysticLogSum G`. This is the additive law behind `plethysticExp` converting sums into
products (`plethysticExp_add`). -/
theorem plethysticLogSum_add (F G : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (F + G) = plethysticLogSum F + plethysticLogSum G := by
  ext k; simp [Finset.sum_add_distrib, smul_add]

/-- `plethysticLogSum` bundled as an additive monoid homomorphism. -/
noncomputable def plethysticLogSumHom : (A⸨X⸩)⟦X⟧ →+ (A⸨X⸩)⟦X⟧ where
  toFun := plethysticLogSum
  map_zero' := plethysticLogSum_zero
  map_add' := plethysticLogSum_add

/-- Applying `plethysticLogSumHom` agrees with `plethysticLogSum`. -/
@[simp] theorem plethysticLogSumHom_apply (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSumHom F = plethysticLogSum F := by
  rfl

/-- The plethystic logarithmic sum commutes with negation. -/
theorem plethysticLogSum_neg (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (-F) = -plethysticLogSum F :=
  (plethysticLogSumHom (A := A)).map_neg F

/-- The plethystic logarithmic sum commutes with subtraction. -/
theorem plethysticLogSum_sub (F G : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (F - G) = plethysticLogSum F - plethysticLogSum G :=
  (plethysticLogSumHom (A := A)).map_sub F G

/-- The plethystic logarithmic sum commutes with `ℕ`-scalar multiplication. -/
theorem plethysticLogSum_nsmul (m : ℕ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (m • F) = m • plethysticLogSum F :=
  (plethysticLogSumHom (A := A)).map_nsmul m F

/-- The plethystic logarithmic sum commutes with `ℤ`-scalar multiplication. -/
theorem plethysticLogSum_zsmul (m : ℤ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (m • F) = m • plethysticLogSum F :=
  (plethysticLogSumHom (A := A)).map_zsmul m F

/-- The plethystic logarithmic sum sends every `t`-constant series to `0`. -/
@[simp] theorem plethysticLogSum_C (c : A⸨X⸩) : plethysticLogSum (C c) = 0 := by
  ext (_ | k)
  · simp [coeff_zero_eq_constantCoeff_apply]
  · simp [coeff_plethysticLogSum]

/-- `plethysticLogSum` is invariant under removing the `t`-constant term. -/
theorem plethysticLogSum_sub_C_constantCoeff (F : (A⸨X⸩)⟦X⟧) :
    plethysticLogSum (F - C (constantCoeff F)) = plethysticLogSum F := by
  rw [plethysticLogSum_sub, plethysticLogSum_C, sub_zero]

/-- Combined Adams dilation commutes with `plethysticLogSum`. -/
theorem adamsExpand_plethysticLogSum (m : ℕ+) (F : (A⸨X⸩)⟦X⟧) :
    adamsExpand A m (plethysticLogSum F) = plethysticLogSum (adamsExpand A m F) := by
  apply PowerSeries.ext; intro k
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [coeff_zero_eq_constantCoeff_apply]
  by_cases hmd : (m : ℕ) ∣ k
  · obtain ⟨d, rfl⟩ := hmd
    rw [coeff_adamsExpand_mul, coeff_plethysticLogSum, map_sum, coeff_plethysticLogSum]
    refine Finset.sum_subset_zero_on_sdiff (range_mono (Nat.le_mul_of_pos_left d m.pos))
      (fun n hn ↦ ?_) (fun n _ ↦ ?_)
    · simp only [mem_sdiff, mem_range, not_lt] at hn
      have hlt : (m : ℕ) * d < (n + 1) * (m : ℕ) := by
        rw [mul_comm (n + 1)]; exact Nat.mul_lt_mul_of_pos_left (by omega) m.pos
      rw [adamsExpand_adamsExpand, coeff_adamsExpand_of_not_dvd (n.succPNat * m) F
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hlt), smul_zero]
    · rw [map_rat_smul (LaurentSeries.expand A m), ← coeff_adamsExpand_mul m,
        adamsExpand_adamsExpand, adamsExpand_adamsExpand, mul_comm m]
  · rw [coeff_adamsExpand_of_not_dvd m _ hmd, coeff_plethysticLogSum]
    symm; refine Finset.sum_eq_zero fun n _ ↦ ?_
    rw [adamsExpand_adamsExpand, coeff_adamsExpand_of_not_dvd (n.succPNat * m) F
      (fun h ↦ hmd (dvd_trans (dvd_mul_left _ _) h)), smul_zero]

/-- Coefficientwise ring homomorphisms between `ℚ`-algebras commute with `plethysticLogSum`. -/
theorem map_plethysticLogSum (φ : A →+* B) (F : (A⸨X⸩)⟦X⟧) :
    PowerSeries.map (HahnSeries.mapRingHom φ) (plethysticLogSum F) =
      plethysticLogSum (PowerSeries.map (HahnSeries.mapRingHom φ) F) := by
  apply PowerSeries.ext; intro k; simp only [coeff_map, coeff_plethysticLogSum, map_sum]
  exact Finset.sum_congr rfl fun n _ ↦ by
    rw [map_rat_smul (HahnSeries.mapRingHom φ), ← coeff_map, map_adamsExpand]

/-- The **plethystic exponential** `PE(F) = exp (∑_{n ≥ 1} ψ ^ n (F - C (constantCoeff F)) / n)`
on `(A⸨X⸩)⟦X⟧`, agreeing with `exp (∑_{n ≥ 1} ψ ^ n (F) / n)` when `constantCoeff F = 0`. -/
noncomputable def plethysticExp (F : (A⸨X⸩)⟦X⟧) : (A⸨X⸩)⟦X⟧ :=
  (PowerSeries.exp A⸨X⸩).subst (plethysticLogSum F)

/-- Unfolding formula for `PowerSeries.plethysticExp`. -/
theorem plethysticExp_def (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp F = (PowerSeries.exp A⸨X⸩).subst (plethysticLogSum F) := by
  rfl

/-- The constant coefficient of `PE(F)` is `1`. -/
@[simp] theorem constantCoeff_plethysticExp (F : (A⸨X⸩)⟦X⟧) :
    constantCoeff (plethysticExp F) = 1 :=
  constantCoeff_subst_exp (constantCoeff_plethysticLogSum F)

/-- The formal logarithm of `PE(F)` is `plethysticLogSum F`. -/
@[simp] theorem logOf_plethysticExp (F : (A⸨X⸩)⟦X⟧) :
    logOf (plethysticExp F) = plethysticLogSum F :=
  logOf_subst_exp (constantCoeff_plethysticLogSum F)

/-- `PE(0) = 1`. -/
@[simp] theorem plethysticExp_zero : plethysticExp (0 : (A⸨X⸩)⟦X⟧) = 1 :=
  (logOf_inj (constantCoeff_plethysticExp 0) constantCoeff_one).mp (by simp)

/-- `PE` sends any `t`-constant series to `1`. -/
@[simp] theorem plethysticExp_C (c : A⸨X⸩) : plethysticExp (C c) = 1 :=
  (logOf_inj (constantCoeff_plethysticExp _) constantCoeff_one).mp (by simp)

/-- `plethysticExp` is invariant under removing the `t`-constant term. -/
theorem plethysticExp_sub_C_constantCoeff (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (F - C (constantCoeff F)) = plethysticExp F := by
  rw [plethysticExp_def, plethysticLogSum_sub_C_constantCoeff, ← plethysticExp_def]

/-- **Additivity-to-multiplicativity**: `PE(F + G) = PE(F) * PE(G)`. -/
theorem plethysticExp_add (F G : (A⸨X⸩)⟦X⟧) :
    plethysticExp (F + G) = plethysticExp F * plethysticExp G := by
  refine (logOf_inj (constantCoeff_plethysticExp _) (by simp)).mp ?_
  rw [logOf_mul (constantCoeff_plethysticExp F) (constantCoeff_plethysticExp G),
    logOf_plethysticExp, logOf_plethysticExp, logOf_plethysticExp, plethysticLogSum_add]

/-- `plethysticExp` bundled as a monoid homomorphism from `Multiplicative ((A⸨X⸩)⟦X⟧)`. -/
noncomputable def plethysticExpMonoidHom :
    Multiplicative (A⸨X⸩)⟦X⟧ →* (A⸨X⸩)⟦X⟧ where
  toFun x := plethysticExp x.toAdd
  map_one' := plethysticExp_zero
  map_mul' x y := plethysticExp_add x.toAdd y.toAdd

/-- Applying `plethysticExpMonoidHom` agrees with `plethysticExp`. -/
@[simp] theorem plethysticExpMonoidHom_apply (x : Multiplicative (A⸨X⸩)⟦X⟧) :
    plethysticExpMonoidHom x = plethysticExp x.toAdd := by
  rfl

/-- `PE` converts finite sums into finite products. -/
theorem plethysticExp_sum {ι : Type*} (s : Finset ι) (f : ι → (A⸨X⸩)⟦X⟧) :
    plethysticExp (∑ i ∈ s, f i) = ∏ i ∈ s, plethysticExp (f i) := by
  have h := map_prod (plethysticExpMonoidHom (A := A)) (fun i ↦ Multiplicative.ofAdd (f i)) s
  simpa only [plethysticExpMonoidHom_apply, toAdd_prod, toAdd_ofAdd] using h

/-- Every plethystic exponential `PE(F)` is a unit in `(A⸨X⸩)⟦X⟧`. -/
theorem isUnit_plethysticExp (F : (A⸨X⸩)⟦X⟧) : IsUnit (plethysticExp F) :=
  isUnit_iff_constantCoeff.mpr (by simp)

/-- `plethysticExp` bundled as a monoid homomorphism into `(A⸨X⸩)⟦X⟧ˣ`. -/
noncomputable def plethysticExpUnitsHom :
    Multiplicative (A⸨X⸩)⟦X⟧ →* (A⸨X⸩)⟦X⟧ˣ where
  toFun x := (isUnit_plethysticExp x.toAdd).unit
  map_one' := Units.ext plethysticExp_zero
  map_mul' x y := Units.ext (plethysticExp_add x.toAdd y.toAdd)

/-- Applying `plethysticExpUnitsHom` gives `(isUnit_plethysticExp x.toAdd).unit`. -/
theorem plethysticExpUnitsHom_apply (x : Multiplicative (A⸨X⸩)⟦X⟧) :
    plethysticExpUnitsHom x = (isUnit_plethysticExp x.toAdd).unit := by
  rfl

/-- Coercing `plethysticExpUnitsHom x` to `(A⸨X⸩)⟦X⟧` yields `plethysticExp x.toAdd`. -/
@[simp] theorem coe_plethysticExpUnitsHom (x : Multiplicative (A⸨X⸩)⟦X⟧) :
    ((plethysticExpUnitsHom x : (A⸨X⸩)⟦X⟧ˣ) : (A⸨X⸩)⟦X⟧) = plethysticExp x.toAdd := by
  rfl

/-- `PE(-F) * PE(F) = 1`. -/
theorem plethysticExp_neg_mul (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (-F) * plethysticExp F = 1 := by
  rw [← plethysticExp_add, neg_add_cancel, plethysticExp_zero]

/-- `PE(-F) = PE(F)⁻¹ʳ`. -/
theorem plethysticExp_neg (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (-F) = Ring.inverse (plethysticExp F) :=
  (isUnit_plethysticExp F).mul_right_cancel
    (by rw [plethysticExp_neg_mul, Ring.inverse_mul_cancel _ (isUnit_plethysticExp F)])

/-- `PE(F - G) = PE(F) * PE(G)⁻¹ʳ`. -/
theorem plethysticExp_sub (F G : (A⸨X⸩)⟦X⟧) :
    plethysticExp (F - G) = plethysticExp F * Ring.inverse (plethysticExp G) := by
  rw [sub_eq_add_neg, plethysticExp_add, plethysticExp_neg]

/-- `PE(m • F) = PE(F) ^ m` for `m : ℕ`. -/
theorem plethysticExp_nsmul (m : ℕ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (m • F) = plethysticExp F ^ m := by
  simpa [ofAdd_nsmul] using
    (plethysticExpMonoidHom (A := A)).map_pow (Multiplicative.ofAdd F) m

/-- `PE(m • F) = (u ^ m : (A⸨X⸩)⟦X⟧ˣ)` for `m : ℤ`, where `u` is the unit `PE(F)`. -/
theorem plethysticExp_zsmul (m : ℤ) (F : (A⸨X⸩)⟦X⟧) :
    plethysticExp (m • F) = ((isUnit_plethysticExp F).unit ^ m : (A⸨X⸩)⟦X⟧ˣ) := by
  have h := congrArg Units.val
    ((plethysticExpUnitsHom (A := A)).map_zpow (Multiplicative.ofAdd F) m)
  rw [plethysticExpUnitsHom_apply, plethysticExpUnitsHom_apply, IsUnit.unit_spec,
    toAdd_zpow, toAdd_ofAdd] at h
  exact h

/-- Combined Adams dilation commutes with substitution into `PowerSeries.exp`. -/
theorem adamsExpand_subst_exp (m : ℕ+) {G : (A⸨X⸩)⟦X⟧} (hG : HasSubst G) :
    adamsExpand A m ((PowerSeries.exp A⸨X⸩).subst G) =
      (PowerSeries.exp A⸨X⸩).subst (adamsExpand A m G) := by
  have hsub' : HasSubst (PowerSeries.map (LaurentSeries.expand A m).toRingHom G) :=
    PowerSeries.hasSubst_iff.mpr (hG.const.map (LaurentSeries.expand A m).toRingHom)
  rw [adamsExpand_apply, map_subst_exp _ hG, adamsExpand_apply]
  exact PowerSeries.expand_subst (m : ℕ) m.ne_zero hsub' (PowerSeries.exp A⸨X⸩)

/-- **Adams compatibility**: `ψ ^ m (PE(F)) = PE(ψ ^ m (F))`. -/
theorem adamsExpand_plethysticExp (m : ℕ+) (F : (A⸨X⸩)⟦X⟧) :
    adamsExpand A m (plethysticExp F) = plethysticExp (adamsExpand A m F) := by
  rw [plethysticExp_def,
    adamsExpand_subst_exp m (HasSubst.of_constantCoeff_zero' (constantCoeff_plethysticLogSum F)),
    adamsExpand_plethysticLogSum, ← plethysticExp_def]

/-- Coefficientwise ring homomorphisms between `ℚ`-algebras commute with `plethysticExp`. -/
theorem map_plethysticExp (φ : A →+* B) (F : (A⸨X⸩)⟦X⟧) :
    PowerSeries.map (HahnSeries.mapRingHom φ) (plethysticExp F) =
      plethysticExp (PowerSeries.map (HahnSeries.mapRingHom φ) F) := by
  rw [plethysticExp_def, plethysticExp_def, ← map_plethysticLogSum]
  exact map_subst_exp (HahnSeries.mapRingHom φ)
    (HasSubst.of_constantCoeff_zero' (constantCoeff_plethysticLogSum F))

/-- The `t ^ k` coefficient of `PE(F)` only depends on the coefficients `coeff j F` for
`1 ≤ j ≤ k`. -/
theorem coeff_plethysticExp_eq_of_coeff_eq {F₁ F₂ : (A⸨X⸩)⟦X⟧} {k : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ k → coeff j F₁ = coeff j F₂) :
    coeff k (plethysticExp F₁) = coeff k (plethysticExp F₂) := by
  have hdiff : ∀ j < k + 1, coeff j (plethysticLogSum (F₁ - F₂)) = 0 := fun j hj ↦ by
    rw [plethysticLogSum_sub, map_sub, sub_eq_zero]
    rcases eq_or_ne j 0 with rfl | hj0
    · simp [coeff_zero_eq_constantCoeff_apply]
    rw [coeff_plethysticLogSum, coeff_plethysticLogSum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hd : (n.succPNat : ℕ) ∣ j
    · obtain ⟨d, rfl⟩ := hd
      rw [coeff_adamsExpand_mul n.succPNat, coeff_adamsExpand_mul n.succPNat,
        h d (Nat.pos_of_ne_zero (right_ne_zero_of_mul hj0))
          (le_trans (Nat.le_mul_of_pos_left d n.succPNat.pos) (Nat.lt_succ_iff.mp hj))]
    · rw [coeff_adamsExpand_of_not_dvd n.succPNat F₁ hd,
        coeff_adamsExpand_of_not_dvd n.succPNat F₂ hd]
  rw [plethysticLogSum_sub] at hdiff
  have hdvd : (X : (A⸨X⸩)⟦X⟧) ^ (k + 1) ∣ plethysticLogSum F₁ - plethysticLogSum F₂ :=
    X_pow_dvd_iff.mpr hdiff
  have hexp : (X : (A⸨X⸩)⟦X⟧) ^ (k + 1) ∣ plethysticExp F₁ - plethysticExp F₂ :=
    X_pow_dvd_subst_sub_subst (constantCoeff_plethysticLogSum F₁) hdvd (PowerSeries.exp A⸨X⸩)
  exact sub_eq_zero.mp (X_pow_dvd_iff.mp hexp k (Nat.lt_succ_self k))

/-- Lower support bound propagation through `adamsExpand`: if positive `t`-coefficients of `F`
vanish below `q`-degree `b` and `bound ≤ n * b` whenever `n ∣ a`, then `[q ^ s t ^ a] ψ ^ n (F) = 0`
for `s < bound`. -/
private theorem coeff_coeff_adamsExpand_eq_zero_of_lt {R : Type*} [CommRing R]
    {F : (R⸨X⸩)⟦X⟧} {b bound : ℤ} (n : ℕ+) {a : ℕ} (ha : 1 ≤ a) {s : ℤ} (hs : s < bound)
    (hbound : (n : ℕ) ∣ a → bound ≤ (n : ℤ) * b)
    (hF : ∀ j, 1 ≤ j → ∀ i < b, (coeff j F).coeff i = 0) :
    (coeff a (adamsExpand R n F)).coeff s = 0 := by
  rw [coeff_coeff_adamsExpand]
  split_ifs with h
  · have ha_div : 1 ≤ a / (n : ℕ) := Nat.div_pos (Nat.le_of_dvd ha h.1) n.pos
    have hs_div : s / (n : ℤ) < b := by
      have hpos : (0 : ℤ) < n := by exact_mod_cast n.pos
      have hmul : (n : ℤ) * (s / (n : ℤ)) = s := Int.mul_ediv_cancel' h.2
      exact lt_of_mul_lt_mul_left (hmul.symm ▸ lt_of_lt_of_le hs (hbound h.1)) hpos.le
    exact hF _ ha_div _ hs_div
  · rfl

/-- If every positive `t`-coefficient of `F` vanishes below `q`-degree `N ≥ 0`, then every
positive `t`-coefficient of `plethysticLogSum F` vanishes below `q`-degree `N`. -/
theorem coeff_plethysticLogSum_eq_zero_of_lt {F : (A⸨X⸩)⟦X⟧} {N : ℤ} (hN : 0 ≤ N)
    (hF : ∀ a, 1 ≤ a → ∀ s < N, (coeff a F).coeff s = 0) :
    ∀ a, 1 ≤ a → ∀ s < N, (coeff a (plethysticLogSum F)).coeff s = 0 := by
  intro a ha s hs
  rw [coeff_plethysticLogSum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [HahnSeries.coeff_smul, coeff_coeff_adamsExpand_eq_zero_of_lt n.succPNat ha hs
    (fun _ ↦ le_mul_of_one_le_left hN (by exact_mod_cast n.succPNat.pos)) hF, smul_zero]

/-- Vanishing of `[q ^ s t ^ a]` on all powers of `plethysticLogSum F` implies vanishing on
`plethysticExp F`. -/
private theorem coeff_coeff_plethysticExp_eq_zero_of_pow {F : (A⸨X⸩)⟦X⟧} {a : ℕ} {s : ℤ}
    (hpow : ∀ d : ℕ, (coeff a ((plethysticLogSum F) ^ d)).coeff s = 0) :
    (coeff a (plethysticExp F)).coeff s = 0 := by
  rw [plethysticExp_def, coeff_subst_eq_sum_range _ (constantCoeff_plethysticLogSum F),
    HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rw [smul_eq_mul, coeff_exp, TauCeti.laurentSeries_algebraMap_mul_eq_smul, HahnSeries.coeff_smul,
    hpow d, smul_zero]

/-- If every positive `t`-coefficient of `F` vanishes below `q`-degree `N ≥ 0`, then every
positive `t`-coefficient of `PE(F)` vanishes below `q`-degree `N`. -/
theorem coeff_plethysticExp_eq_zero_of_lt {F : (A⸨X⸩)⟦X⟧} {N : ℤ} (hN : 0 ≤ N)
    (hF : ∀ a, 1 ≤ a → ∀ s < N, (coeff a F).coeff s = 0) :
    ∀ a, 1 ≤ a → ∀ s < N, (coeff a (plethysticExp F)).coeff s = 0 := by
  have hLpow := coeff_coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero hN
    (constantCoeff_plethysticLogSum F) (coeff_plethysticLogSum_eq_zero_of_lt hN hF)
  intro a ha s hs
  refine coeff_coeff_plethysticExp_eq_zero_of_pow fun d ↦ ?_
  rcases d with _ | d
  · simp [Nat.ne_of_gt ha]
  · exact hLpow (d + 1) (Nat.succ_pos d) a ha s hs

/-- If every positive `t`-coefficient of `F` vanishes below `q`-degree `m ≤ 0`, then
`plethysticLogSum F` satisfies the slope-`m` lower support bound. -/
private theorem coeff_plethysticLogSum_eq_zero_of_lt_mul {F : (A⸨X⸩)⟦X⟧} {m : ℤ} (hm : m ≤ 0)
    (hF : ∀ j, 1 ≤ j → ∀ i < m, (coeff j F).coeff i = 0) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (plethysticLogSum F)).coeff s = 0 := by
  intro a s hs
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [coeff_zero_eq_constantCoeff_apply]
  rw [coeff_plethysticLogSum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [HahnSeries.coeff_smul, coeff_coeff_adamsExpand_eq_zero_of_lt n.succPNat
    (Nat.pos_of_ne_zero ha0) hs
    (fun hd ↦ mul_le_mul_of_nonpos_right
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hd) hm)
    hF, smul_zero]

/-- If every positive `t`-coefficient of `F` vanishes below `q`-degree `m ≤ 0`, then `PE(F)`
satisfies the slope-`m` lower support bound. -/
private theorem coeff_plethysticExp_eq_zero_of_lt_mul {F : (A⸨X⸩)⟦X⟧} {m : ℤ} (hm : m ≤ 0)
    (hF : ∀ j, 1 ≤ j → ∀ i < m, (coeff j F).coeff i = 0) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (plethysticExp F)).coeff s = 0 := by
  have hL := coeff_plethysticLogSum_eq_zero_of_lt_mul hm hF
  exact fun a s hs ↦
    coeff_coeff_plethysticExp_eq_zero_of_pow fun d ↦ coeff_coeff_pow_eq_zero_of_lt_mul hL d a s hs

/-- **Bidegree congruence** for `PE`: `[q ^ r t ^ k] PE(F₁) = [q ^ r t ^ k] PE(F₂)` whenever
`F₁` and `F₂` agree in `t`-degrees `1 ≤ j ≤ k` below `q`-degree `N ≥ 0`, `F₁` vanishes in those
`t`-degrees below `q`-degree `m ≤ 0`, and `r < k * m + N`. -/
theorem coeff_coeff_plethysticExp_eq_of_coeff_eq {F₁ F₂ : (A⸨X⸩)⟦X⟧} {k : ℕ} {m N r : ℤ}
    (hm : m ≤ 0) (hN : 0 ≤ N) (hr : r < (k : ℤ) * m + N)
    (hm₁ : ∀ j, 1 ≤ j → j ≤ k → ∀ i < m, (coeff j F₁).coeff i = 0)
    (h : ∀ j, 1 ≤ j → j ≤ k → ∀ i < N, (coeff j F₁).coeff i = (coeff j F₂).coeff i) :
    (coeff k (plethysticExp F₁)).coeff r = (coeff k (plethysticExp F₂)).coeff r := by
  let truncF (F : (A⸨X⸩)⟦X⟧) : (A⸨X⸩)⟦X⟧ := ∑ j ∈ Icc 1 k, C (coeff j F) * X ^ j
  have htrunc (F : (A⸨X⸩)⟦X⟧) :
      coeff k (plethysticExp F) = coeff k (plethysticExp (truncF F)) :=
    coeff_plethysticExp_eq_of_coeff_eq fun j hj1 hjk ↦ by
      rw [coeff_sum_finset_C_mul_X_pow, ite_eq_left (mem_Icc.mpr ⟨hj1, hjk⟩)]
  have hF₁' : ∀ a, 1 ≤ a → ∀ i < m, (coeff a (truncF F₁)).coeff i = 0 := fun a _ i hi ↦ by
    dsimp [truncF]
    rw [coeff_sum_finset_C_mul_X_pow]
    split_ifs with ha
    · exact hm₁ a (mem_Icc.mp ha).1 (mem_Icc.mp ha).2 i hi
    · simp
  have hdiff : ∀ a, 1 ≤ a → ∀ i < N, (coeff a (truncF F₂ - truncF F₁)).coeff i = 0 :=
    fun a _ i hi ↦ by
      dsimp [truncF]
      rw [map_sub, HahnSeries.coeff_sub, coeff_sum_finset_C_mul_X_pow,
        coeff_sum_finset_C_mul_X_pow, sub_eq_zero]
      split_ifs with ha
      · exact (h a (mem_Icc.mp ha).1 (mem_Icc.mp ha).2 i hi).symm
      · rfl
  have hdecomp : truncF F₂ = truncF F₁ + (truncF F₂ - truncF F₁) := (add_sub_cancel _ _).symm
  rw [htrunc F₁, htrunc F₂, hdecomp, plethysticExp_add]
  exact (coeff_coeff_mul_eq_left_of_lt_mul hm hr
    (coeff_plethysticExp_eq_zero_of_lt_mul hm hF₁') (constantCoeff_plethysticExp _)
    (coeff_plethysticExp_eq_zero_of_lt hN hdiff)).symm

/-! ### Monomial plethystic formulas -/

/-- Logarithmic sum of a positive-degree monomial `q ^ i t ^ j` (`j ≠ 0`) is the `j`-fold
expansion of `∑_{n ≥ 1} (q ^ i) ^ n t ^ n / n`. -/
theorem plethysticLogSum_single_mul_X_pow (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticLogSum (C (single i (1 : A)) * X ^ j) =
      PowerSeries.expand j hj (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • (single i (1 : A)) ^ n) := by
  apply PowerSeries.ext; intro k
  rw [coeff_plethysticLogSum, coeff_expand]
  by_cases hjk : j ∣ k
  · obtain ⟨d, rfl⟩ := hjk
    rw [ite_eq_left ⟨d, rfl⟩, Nat.mul_div_cancel_left d (Nat.pos_of_ne_zero hj), coeff_mk]
    rcases d with _ | d
    · simp
    · rw [Finset.sum_eq_single_of_mem d (mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self d)
          (Nat.le_mul_of_pos_left (d + 1) (Nat.pos_of_ne_zero hj))))]
      · have hmul : (d.succPNat : ℕ) * j = j * (d + 1) := by simp [mul_comm]
        rw [adamsExpand_C_single_mul_X_pow, hmul, coeff_C_mul_X_pow, ite_eq_left rfl,
          HahnSeries.single_pow, one_pow, nsmul_eq_mul]
        simp
      · intro n _ hnd
        have hne : j * (d + 1) ≠ (n.succPNat : ℕ) * j := fun heq ↦ hnd <| by
          have h := Nat.mul_right_cancel (Nat.pos_of_ne_zero hj) ((mul_comm (d + 1) j).trans heq)
          simp only [Nat.succPNat_coe] at h; omega
        rw [adamsExpand_C_single_mul_X_pow, coeff_C_mul_X_pow, ite_eq_right hne, smul_zero]
  · rw [ite_eq_right hjk]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    have hne : k ≠ (n.succPNat : ℕ) * j := fun heq ↦ hjk ⟨n + 1, by simp [heq, mul_comm]⟩
    rw [adamsExpand_C_single_mul_X_pow, coeff_C_mul_X_pow, ite_eq_right hne, smul_zero]

/-- **Negative monomial plethystic exponential**: for `j ≠ 0`,
`PE(-q ^ i t ^ j) = 1 - q ^ i t ^ j`. -/
@[simp] theorem plethysticExp_neg_single_mul_X_pow (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticExp (-(C (single i (1 : A)) * X ^ j)) = 1 - C (single i (1 : A)) * X ^ j := by
  have hlog : plethysticLogSum (-(C (single i (1 : A)) * X ^ j)) =
      logOf (1 - C (single i (1 : A)) * X ^ j) := by
    rw [plethysticLogSum_neg, plethysticLogSum_single_mul_X_pow i hj,
      logOf_one_sub_C_mul_X_pow _ hj, ← map_neg]
    congr 1; apply PowerSeries.ext; intro n
    rw [map_neg, coeff_mk, coeff_mk, ← smul_neg, Algebra.smul_def,
      TauCeti.laurentSeries_algebraMap_mul_eq_smul]
  rw [plethysticExp_def, hlog, subst_exp_logOf (by simp [hj])]

/-- **Monomial plethystic exponential**: for `j ≠ 0`,
`PE(q ^ i t ^ j) * (1 - q ^ i t ^ j) = 1`. -/
theorem plethysticExp_single_mul_X_pow_mul (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticExp (C (single i (1 : A)) * X ^ j) * (1 - C (single i (1 : A)) * X ^ j) = 1 := by
  rw [← plethysticExp_neg_single_mul_X_pow (A := A) i hj, mul_comm, plethysticExp_neg_mul]

/-- **Monomial plethystic exponential**: for `j ≠ 0`,
`PE(q ^ i t ^ j) = (1 - q ^ i t ^ j)⁻¹ʳ`. -/
theorem plethysticExp_single_mul_X_pow (i : ℤ) {j : ℕ} (hj : j ≠ 0) :
    plethysticExp (C (single i (1 : A)) * X ^ j) =
      Ring.inverse (1 - C (single i (1 : A)) * X ^ j) := by
  have hu : IsUnit (1 - C (single i (1 : A)) * X ^ j) :=
    isUnit_iff_constantCoeff.mpr (by simp [hj])
  apply hu.mul_right_cancel
  rw [plethysticExp_single_mul_X_pow_mul i hj, Ring.inverse_mul_cancel _ hu]

/-- `PE(t) = (1 - t)⁻¹ʳ`. -/
theorem plethysticExp_X : plethysticExp (X : (A⸨X⸩)⟦X⟧) = Ring.inverse (1 - X) := by
  simpa using plethysticExp_single_mul_X_pow (A := A) 0 one_ne_zero

/-- `PE(t) * (1 - t) = 1`. -/
theorem plethysticExp_X_mul : plethysticExp (X : (A⸨X⸩)⟦X⟧) * (1 - X) = 1 := by
  simpa using plethysticExp_single_mul_X_pow_mul (A := A) 0 one_ne_zero

/-- `PE(-t) = 1 - t`. -/
@[simp] theorem plethysticExp_neg_X : plethysticExp (-X : (A⸨X⸩)⟦X⟧) = 1 - X := by
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

/-- Integral realization and slope-`m` support bound for `PE(z • (q ^ i t ^ j))`. -/
private theorem exists_plethysticExp_zsmul_single (i : ℤ) {j : ℕ} (hj : j ≠ 0) (z : ℤ)
    {m : ℤ} (hm : m ≤ 0) (hi : m ≤ i) :
    ∃ G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) G =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ))
          (z • (C (single i (1 : ℤ)) * X ^ j))) ∧
      ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0 := by
  let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
  let U : (ℤ⸨X⸩)⟦X⟧ := PowerSeries.expand j hj (PowerSeries.mk fun d ↦ (single i (1 : ℤ)) ^ d)
  let V : (ℤ⸨X⸩)⟦X⟧ := 1 - C (single i (1 : ℤ)) * X ^ j
  have hUV : U * V = 1 := by
    simpa [U, V] using
      PowerSeries.expand_mk_pow_mul_one_sub_C_mul_X_pow_eq_one j hj (single i (1 : ℤ))
  let u : ((ℤ⸨X⸩)⟦X⟧)ˣ := ⟨U, V, hUV, mul_comm U V ▸ hUV⟩
  have hsingle : ι (single i (1 : ℤ)) = single i (1 : ℚ) := by
    rw [HahnSeries.mapRingHom_apply]
    exact (HahnSeries.map_single ((Int.castRingHom ℚ : ℤ →+* ℚ) : ZeroHom ℤ ℚ)).trans (by simp)
  have hcoe (w : ((ℤ⸨X⸩)⟦X⟧)ˣ) :
      ((Units.map (PowerSeries.map ι).toMonoidHom w : ((ℚ⸨X⸩)⟦X⟧)ˣ) : (ℚ⸨X⸩)⟦X⟧) =
        PowerSeries.map ι w :=
    rfl
  have hu_map : Units.map (PowerSeries.map ι).toMonoidHom u =
      (isUnit_plethysticExp (C (single i (1 : ℚ)) * X ^ j)).unit := by
    apply Units.ext
    have hunit : IsUnit (1 - C (single i (1 : ℚ)) * X ^ j) :=
      isUnit_iff_constantCoeff.mpr (by simp [hj])
    apply hunit.mul_right_cancel
    have hmap : PowerSeries.map ι U * (1 - C (single i (1 : ℚ)) * X ^ j) = 1 := by
      simpa only [V, map_mul, map_sub, map_one, map_C, map_pow, map_X, hsingle] using
        congrArg (PowerSeries.map ι) hUV
    rw [hcoe, IsUnit.unit_spec, plethysticExp_single_mul_X_pow_mul i hj]
    exact hmap
  have hU_bound : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a U).coeff s = 0 := fun a s hs ↦ by
    rw [coeff_expand]
    split_ifs with hd
    · rw [coeff_mk, HahnSeries.single_pow, one_pow, nsmul_eq_mul, HahnSeries.coeff_single]
      refine ite_eq_right fun hEq ↦ ?_
      have : ((a / j : ℕ) : ℤ) ≤ a := by exact_mod_cast Nat.div_le_self a j
      nlinarith
    · simp
  have hV_bound : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a V).coeff s = 0 := fun a s hs ↦ by
    rw [map_sub, HahnSeries.coeff_sub, coeff_coeff_one_eq_zero_of_lt_mul a s hs, zero_sub,
      coeff_C_mul_X_pow]
    split_ifs with ha
    · subst ha
      have : (1 : ℤ) ≤ a := by exact_mod_cast Nat.pos_of_ne_zero hj
      rw [HahnSeries.coeff_single, ite_eq_right (by nlinarith), neg_zero]
    · simp
  refine ⟨((u ^ z : ((ℤ⸨X⸩)⟦X⟧)ˣ) : (ℤ⸨X⸩)⟦X⟧), ?_, ?_⟩
  · have hz := congrArg (fun w : ((ℚ⸨X⸩)⟦X⟧)ˣ ↦ (w : (ℚ⸨X⸩)⟦X⟧)) (congrArg (· ^ z) hu_map)
    rw [← map_zpow, hcoe] at hz
    rw [hz, ← plethysticExp_zsmul, map_zsmul, map_mul, map_C, map_pow, map_X, hsingle]
  · cases z with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
      exact coeff_coeff_pow_eq_zero_of_lt_mul hU_bound n
    | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      exact coeff_coeff_pow_eq_zero_of_lt_mul hV_bound (n + 1)

/-- Integral realization and slope-`m` support bound for the `q < N` truncation of the first `k`
positive `t`-coefficients of `F`. -/
private theorem exists_plethysticExp_lo (F : (ℤ⸨X⸩)⟦X⟧) (k : ℕ) {m N : ℤ} (hm : m ≤ 0)
    (hmle : ∀ j ∈ Icc 1 k, ∀ i < m, (coeff j F).coeff i = 0) :
    let Flo : (ℤ⸨X⸩)⟦X⟧ := ∑ j ∈ Icc 1 k, C (HahnSeries.truncLT N (coeff j F)) * X ^ j
    ∃ Glo : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) Glo =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) Flo) ∧
      ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a Glo).coeff s = 0 := by
  intro Flo
  have htrunc (j : ℕ) (hj : j ∈ Icc 1 k) :
      HahnSeries.truncLT N (coeff j F) = ∑ i ∈ Ico m N, single i ((coeff j F).coeff i) := by
    have hmord : m ≤ (coeff j F).order := by
      by_cases h0 : coeff j F = 0
      · simpa [h0, HahnSeries.order_zero] using hm
      · exact not_lt.mp fun hlt ↦ (HahnSeries.coeff_order_eq_zero.not.mpr h0) (hmle j hj _ hlt)
    rw [← LaurentSeries.toLaurentSeries_trunc, LaurentSeries.trunc_eq_sum_Ico, map_sum]
    simp_rw [LaurentPolynomial.toLaurentSeries_single]
    refine Finset.sum_subset (Finset.Ico_subset_Ico_left hmord) fun i hi hi' ↦ ?_
    rw [Finset.mem_Ico] at hi hi'
    rw [HahnSeries.coeff_eq_zero_of_lt_order (by omega), HahnSeries.single_eq_zero]
  have hFlo_eq : Flo = ∑ p ∈ Icc 1 k ×ˢ Ico m N,
      ((coeff p.1 F).coeff p.2) • (C (single p.2 (1 : ℤ)) * X ^ p.1) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [htrunc j hj, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← smul_mul_assoc, ← map_zsmul, zsmul_eq_mul, ← map_intCast (HahnSeries.C : ℤ →+* ℤ⸨X⸩),
      HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one, Int.cast_id]
  rw [hFlo_eq]
  choose Gp hGp using fun p (hp : p ∈ Icc 1 k ×ˢ Ico m N) ↦
    exists_plethysticExp_zsmul_single p.2 (j := p.1)
      (by rw [mem_product, mem_Icc] at hp; omega) ((coeff p.1 F).coeff p.2) hm
      (mem_Ico.mp (mem_product.mp hp).2).1
  refine ⟨∏ p ∈ (Icc 1 k ×ˢ Ico m N).attach, Gp p.val p.property, ?_, ?_⟩
  · rw [map_prod, map_sum, plethysticExp_sum, ← Finset.prod_attach (Icc 1 k ×ˢ Ico m N)]
    exact Finset.prod_congr rfl fun p _ ↦ (hGp p.val p.property).1
  · exact Finset.prod_induction
      (f := fun (p : { x // x ∈ Icc 1 k ×ˢ Ico m N }) ↦ Gp p.val p.property)
      (fun (G : (ℤ⸨X⸩)⟦X⟧) ↦ ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0)
      (fun _ _ h₁ h₂ ↦ coeff_coeff_mul_eq_zero_of_lt_mul h₁ h₂)
      coeff_coeff_one_eq_zero_of_lt_mul fun p _ ↦ (hGp p.val p.property).2

/-- **Integrality over `ℚ`**: for any `F : (ℤ⸨X⸩)⟦X⟧`, `PE(F)` has integral coefficients, i.e.
lies in the image of `(ℤ⸨X⸩)⟦X⟧ → (ℚ⸨X⸩)⟦X⟧`. -/
private theorem exists_map_eq_plethysticExp_rat (F : (ℤ⸨X⸩)⟦X⟧) :
    ∃ G : (ℤ⸨X⸩)⟦X⟧,
      PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) G =
        plethysticExp (PowerSeries.map (HahnSeries.mapRingHom (Int.castRingHom ℚ)) F) := by
  let ι : ℤ⸨X⸩ →+* ℚ⸨X⸩ := HahnSeries.mapRingHom (Int.castRingHom ℚ)
  suffices hmem : ∀ k : ℕ, coeff k (plethysticExp (PowerSeries.map ι F)) ∈ ι.rangeS by
    choose g hg using hmem
    exact ⟨PowerSeries.mk g, PowerSeries.ext fun k ↦ by rw [coeff_map, coeff_mk, hg k]⟩
  intro k
  rw [HahnSeries.mem_map_rangeS]
  intro r
  let m : ℤ := ∑ j ∈ Icc 1 k, min 0 (coeff j F).order
  have hm0 : m ≤ 0 := Finset.sum_nonpos fun j _ ↦ min_le_left _ _
  have hmle : ∀ j ∈ Icc 1 k, ∀ i < m, (coeff j F).coeff i = 0 := fun j hj i hi ↦ by
    have hsub : m - min 0 (coeff j F).order ≤ 0 := by
      rw [← Finset.sum_erase_eq_sub hj]; exact Finset.sum_nonpos fun l _ ↦ min_le_left _ _
    exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi (by omega))
  let N : ℤ := max 0 (r - (k : ℤ) * m + 1)
  have hN0 : 0 ≤ N := le_max_left 0 _
  let Flo : (ℤ⸨X⸩)⟦X⟧ := ∑ j ∈ Icc 1 k, C (HahnSeries.truncLT N (coeff j F)) * X ^ j
  obtain ⟨Glo, hGlo_map, _⟩ := exists_plethysticExp_lo F k (N := N) hm0 hmle
  have hFlo_coeff (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) (i : ℤ) :
      (coeff j (PowerSeries.map ι Flo)).coeff i =
        if i < N then (coeff j (PowerSeries.map ι F)).coeff i else 0 := by
    rw [coeff_map, HahnSeries.coeff_mapRingHom, coeff_map, HahnSeries.coeff_mapRingHom]
    dsimp [Flo]
    rw [coeff_sum_finset_C_mul_X_pow, ite_eq_left (mem_Icc.mpr ⟨hj1, hjk⟩),
      HahnSeries.coeff_truncLT]
    split_ifs <;> simp
  have hFlo_m : ∀ j, 1 ≤ j → j ≤ k → ∀ i < m, (coeff j (PowerSeries.map ι Flo)).coeff i = 0 :=
    fun j hj1 hjk i hi ↦ by
      rw [hFlo_coeff j hj1 hjk i]
      split_ifs
      · rw [coeff_map, HahnSeries.coeff_mapRingHom, hmle j (mem_Icc.mpr ⟨hj1, hjk⟩) i hi,
          map_zero]
      · rfl
  have hFlo_N : ∀ j, 1 ≤ j → j ≤ k → ∀ i < N,
      (coeff j (PowerSeries.map ι Flo)).coeff i = (coeff j (PowerSeries.map ι F)).coeff i :=
    fun j hj1 hjk i hi ↦ by rw [hFlo_coeff j hj1 hjk i, ite_eq_left hi]
  have hrbound : r < (k : ℤ) * m + N := by
    have := le_max_right (0 : ℤ) (r - (k : ℤ) * m + 1); linarith
  rw [← coeff_coeff_plethysticExp_eq_of_coeff_eq hm0 hN0 hrbound hFlo_m hFlo_N, ← hGlo_map,
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
  have hmap := congrArg (PowerSeries.map (HahnSeries.mapRingHom (algebraMap ℚ A))) hG
  rw [map_plethysticExp, ← RingHom.comp_apply, ← PowerSeries.map_comp, ← RingHom.comp_apply,
    ← PowerSeries.map_comp, ← HahnSeries.mapRingHom_comp,
    RingHom.eq_intCast' ((algebraMap ℚ A).comp (Int.castRingHom ℚ))] at hmap
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
    rw [← RingHom.eq_intCast' ((algebraMap ℚ A).comp (Int.castRingHom ℚ))]
    exact (RingHom.injective (algebraMap ℚ A)).comp Int.cast_injective
  exact PowerSeries.map_injective _ (HahnSeries.mapRingHom_injective hinjZ) (hG'.trans hG.symm)

end Integrality

end PowerSeries
