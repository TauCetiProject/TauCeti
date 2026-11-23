/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Rat.Lemmas

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Numerator and denominator of a rational multiplier between integers

If `a' = r * a` with `a, a' ∈ ℤ` and `r ∈ ℚ`, then the denominator of `r` divides `a` and the
numerator of `r` divides `a'`. This is Mathlib's `Rat.den_dvd` and `Rat.num_dvd` for the fraction
`a' /. a`, restated for a rational `r` given by the relation it satisfies rather than as an
explicit quotient, so that it applies with no case split on `a = 0` at the point of use. It is
what turns a rational scaling between two integral objects into integer divisibilities, as for
the scaling `(A, B) ↦ (r⁴A, r⁶B)` between two integral short Weierstrass equations.

Also provides the natural-to-rational coordinatewise embedding `TauCeti.ratEmbed` and clears
denominators simultaneously across a finite family of nonnegative rationals
(`TauCeti.exists_nat_smul_eq_ratEmbed`).

## Main results

* `Rat.den_dvd_of_intCast_eq_mul_intCast`: `a' = r * a` implies `r.den ∣ a`.
* `Rat.num_dvd_of_intCast_eq_mul_intCast`: `a' = r * a` implies `r.num ∣ a'`.
* `Rat.den_dvd_iff_exists_eq_intCast_div`: for `n ≠ 0`, `r.den ∣ n` exactly when `r = k / n` for
  an integer `k`.
* `Rat.den_dvd_iff_exists_mul_intCast_eq`: `r.den ∣ a` exactly when `r * a` is an integer.
* `Rat.den_dvd_iff_exists_mul_natCast_eq`: for `0 ≤ r`, `r.den ∣ n` exactly when `r * n` is a
  natural number.
* `TauCeti.ratEmbed`: additive homomorphism embedding `σ →₀ ℕ` into `σ → ℚ`, together with
  `TauCeti.ratEmbed_mapDomain`.
* `TauCeti.exists_nat_mul_eq_natCast` and `TauCeti.exists_nat_smul_eq_ratEmbed`: nonnegative
  rational families on a `Finset` or a finite type clear denominators simultaneously.
-/

public section

namespace Rat

variable {a a' : ℤ}

/-- A rational `r` with `a' = r * a` for integers `a ≠ 0` and `a'` is the fraction `a' /. a`. -/
private theorem eq_divInt_of_intCast_eq_mul_intCast {r : ℚ} (h : (a' : ℚ) = r * a) (ha : a ≠ 0) :
    r = divInt a' a := by
  rw [divInt_eq_div, eq_div_iff (Int.cast_ne_zero.mpr ha)]
  exact h.symm

/-- **The denominator of a rational multiplier between integers divides the multiplicand**: if
`a' = r * a` with `a, a'` integers, then `r.den ∣ a`. -/
theorem den_dvd_of_intCast_eq_mul_intCast (r : ℚ) (h : (a' : ℚ) = r * a) : (r.den : ℤ) ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero _
  · rw [eq_divInt_of_intCast_eq_mul_intCast h ha]
    exact den_dvd a' a

/-- **The numerator of a rational multiplier between integers divides the result**: if
`a' = r * a` with `a, a'` integers, then `r.num ∣ a'`. -/
theorem num_dvd_of_intCast_eq_mul_intCast (r : ℚ) (h : (a' : ℚ) = r * a) : r.num ∣ a' := by
  rcases eq_or_ne a 0 with rfl | ha
  · have : a' = 0 := by simpa using h
    simp [this]
  · rw [eq_divInt_of_intCast_eq_mul_intCast h ha]
    exact num_dvd a' ha

/-- For `n ≠ 0`, the denominator of `r` divides `n` exactly when `r` is an integer multiple of
`1 / n`. -/
theorem den_dvd_iff_exists_eq_intCast_div {r : ℚ} {n : ℕ} (hn : n ≠ 0) :
    r.den ∣ n ↔ ∃ k : ℤ, r = k / n := by
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨r.num * c, ?_⟩, fun ⟨k, hk⟩ ↦ ?_⟩
  · have hc0 : (c : ℚ) ≠ 0 := by
      rintro h
      exact hn (by simpa [hc] using h)
    rw [hc, Int.cast_mul, Nat.cast_mul, Int.cast_natCast, mul_div_mul_right _ _ hc0,
      num_div_den]
  · have h : ((k : ℤ) : ℚ) = r * (n : ℤ) := by
      rw [hk, Int.cast_natCast, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]
    exact Int.natCast_dvd_natCast.mp (den_dvd_of_intCast_eq_mul_intCast r h)

/-- **A rational multiple of an integer is an integer exactly when the denominator divides it**:
`r.den ∣ a` if and only if `r * a` is an integer. -/
theorem den_dvd_iff_exists_mul_intCast_eq (r : ℚ) (a : ℤ) :
    (r.den : ℤ) ∣ a ↔ ∃ z : ℤ, r * a = z := by
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨r.num * c, ?_⟩, fun ⟨z, hz⟩ ↦ den_dvd_of_intCast_eq_mul_intCast r hz.symm⟩
  rw [hc, Int.cast_mul, Int.cast_natCast, ← mul_assoc, mul_den_eq_num, Int.cast_mul]

/-- **A nonnegative rational multiple of a natural number is a natural number exactly when the
denominator divides it**: for `0 ≤ r`, `r.den ∣ n` if and only if `r * n` is a natural number. -/
theorem den_dvd_iff_exists_mul_natCast_eq {r : ℚ} (hr : 0 ≤ r) (n : ℕ) :
    r.den ∣ n ↔ ∃ k : ℕ, r * n = k := by
  rw [← Int.natCast_dvd_natCast, den_dvd_iff_exists_mul_intCast_eq r (n : ℤ)]
  refine ⟨fun ⟨z, hz⟩ ↦ ⟨z.toNat, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k, by exact_mod_cast hk⟩⟩
  have hz0 : 0 ≤ z := by
    have hq : (0 : ℚ) ≤ (z : ℚ) := by
      rw [← hz]
      exact mul_nonneg hr (by exact_mod_cast Nat.zero_le n)
    exact_mod_cast hq
  rw [← Int.cast_natCast (R := ℚ) z.toNat, Int.toNat_of_nonneg hz0]
  exact_mod_cast hz

end Rat

namespace TauCeti

/-- Embed a finitely supported natural family `σ →₀ ℕ` coordinatewise into `σ → ℚ`. -/
noncomputable def ratEmbed {σ : Type*} : (σ →₀ ℕ) →+ (σ → ℚ) :=
  Finsupp.coeFnAddHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℚ))

@[simp]
theorem ratEmbed_apply {σ : Type*} (d : σ →₀ ℕ) (i : σ) : ratEmbed d i = (d i : ℚ) :=
  (rfl)

/-- `ratEmbed` is injective. -/
theorem ratEmbed_injective {σ : Type*} : Function.Injective (ratEmbed (σ := σ)) :=
  fun _ _ h ↦ Finsupp.ext fun i ↦ Nat.cast_injective (congrFun h i)

/-- Mapping the domain of `d : σ →₀ ℕ` along an equivalence `e : σ ≃ τ` precomposes `ratEmbed d`
with `e.symm`. -/
theorem ratEmbed_mapDomain {σ τ : Type*} (e : σ ≃ τ) (d : σ →₀ ℕ) :
    ratEmbed (d.mapDomain e) = ratEmbed d ∘ e.symm :=
  funext fun i ↦ by
    simp [ratEmbed_apply, ← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]

/-- Any finite subset of a nonnegative rational family `x : ι → ℚ` clears denominators
simultaneously to natural numbers. -/
theorem exists_nat_mul_eq_natCast {ι : Type*} (s : Finset ι) {x : ι → ℚ}
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∃ (D : ℕ) (k : ι → ℕ), 0 < D ∧ ∀ i ∈ s, (D : ℚ) * x i = (k i : ℚ) := by
  classical
  let D : ℕ := ∏ i ∈ s, (x i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (x i).pos
  have hex : ∀ i : s, ∃ m : ℕ, x i.val * D = m := fun i ↦
    (Rat.den_dvd_iff_exists_mul_natCast_eq (hx i.val i.property) D).mp
      (Finset.dvd_prod_of_mem _ i.property)
  choose k hk using hex
  refine ⟨D, fun i ↦ if hi : i ∈ s then k ⟨i, hi⟩ else 0, hD, fun i hi ↦ ?_⟩
  simp only [hi, ↓reduceDIte]
  rw [mul_comm, hk ⟨i, hi⟩]

/-- Any nonnegative rational family `x : σ → ℚ` on a finite type clears denominators to
`ratEmbed d` for some positive natural multiplier `D` and `d : σ →₀ ℕ`. -/
theorem exists_nat_smul_eq_ratEmbed {σ : Type*} [Finite σ] {x : σ → ℚ} (hx : ∀ i, 0 ≤ x i) :
    ∃ (D : ℕ) (d : σ →₀ ℕ), 0 < D ∧ (D : ℚ) • x = ratEmbed d := by
  classical
  cases nonempty_fintype σ
  obtain ⟨D, k, hD, hk⟩ := exists_nat_mul_eq_natCast Finset.univ fun i _ ↦ hx i
  refine ⟨D, Finsupp.equivFunOnFinite.symm k, hD, funext fun i ↦ ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul, ratEmbed_apply,
    Finsupp.equivFunOnFinite_symm_apply_apply] using hk i (Finset.mem_univ i)

end TauCeti

end
