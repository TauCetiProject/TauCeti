/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RealAddValuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded

/-!
# The unit filtration through the real additive valuation

For a nonarchimedean local field `K` with normalized additive valuation
`v_K = TauCeti.realAddValuation K`, this file reads the steps of the unit filtration as
valuation conditions:

```text
U(K,0) = {x : v_K(x) = 0},    U(K,i) = {x : i ≤ v_K(x - 1)}  for i > 0.
```

With `q = #𝓀[K]`, every unit `x` of `𝒪[K]` therefore has its residue-field power
`x ^ ((q - 1) q ^ n)` at valuation distance at least `n + 1` from `1`. This is how the `p`-adic
estimates of the method of linear forms in logarithms apply to arbitrary units: a unit, which may
lie far from `1` (for instance a root of unity, or any unit at `p = 2`, where the exponential
disc is open at radius `1 / 2`), is first powered into the disc on which the `p`-adic exponential
and logarithm are inverse isometries.

## Main results

* `TauCeti.mem_unitFiltration_zero_iff_realAddValuation_eq_zero`: `x ∈ U(K,0)` iff
  `v_K(x) = 0`.
* `TauCeti.mem_unitFiltration_iff_le_realAddValuation_sub_one`: for `i ≠ 0`, `x ∈ U(K,i)` iff
  `i ≤ v_K(x - 1)`.
* `TauCeti.le_realAddValuation_pow_natCard_sub_one_mul_pow_sub_one`: if `v_K(x) = 0`, then
  `n + 1 ≤ v_K(x ^ ((q - 1) q ^ n) - 1)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* Kunrui Yu, *Linear forms in p-adic logarithms II*, Compositio Math. 74 (1990), 15–113, §1.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The units of `𝒪[K]` are the elements of valuation `0`: `x ∈ U(K,0)` iff `v_K(x) = 0`. -/
theorem mem_unitFiltration_zero_iff_realAddValuation_eq_zero (x : Kˣ) :
    x ∈ unitFiltration K 0 ↔ realAddValuation K (x : K) = 0 := by
  rw [mem_unitFiltration_zero, ← normalizedValuation_eq_one_iff, realAddValuation_coe_unit,
    ← WithTop.coe_zero, WithTop.coe_eq_coe, Int.cast_eq_zero, toAdd_eq_zero]

/-- **Positive steps of the unit filtration through the valuation.** For `i ≠ 0`,
`x ∈ U(K,i)` iff `i ≤ v_K(x - 1)`. At `x = 1` both sides hold, the right one because
`v_K(0) = ⊤`. -/
theorem mem_unitFiltration_iff_le_realAddValuation_sub_one {i : ℕ} (hi : i ≠ 0) (x : Kˣ) :
    x ∈ unitFiltration K i ↔ ((i : ℝ) : WithTop ℝ) ≤ realAddValuation K ((x : K) - 1) := by
  rcases eq_or_ne x 1 with rfl | hx
  · simp
  have hx' : (x : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ hx (Units.val_eq_one.mp h)
  rw [mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one hi hx,
    realAddValuation_of_ne_zero hx', WithTop.coe_le_coe]
  exact_mod_cast Iff.rfl

/-- **Powering a unit into a deep step, valuation form.** Let `q = #𝓀[K]`. If `v_K(x) = 0`, then
for every `n`

```text
n + 1 ≤ v_K(x ^ ((q - 1) q ^ n) - 1),
```

since `(q - 1) q ^ n` is the index of `U(K,n+1)` in `U(K,0)`. -/
theorem le_realAddValuation_pow_natCard_sub_one_mul_pow_sub_one {x : K}
    (hx : realAddValuation K x = 0) (n : ℕ) :
    ((n + 1 : ℝ) : WithTop ℝ) ≤
      realAddValuation K (x ^ ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n) - 1) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hu : Units.mk0 x hx0 ∈ unitFiltration K 0 :=
    (mem_unitFiltration_zero_iff_realAddValuation_eq_zero _).mpr hx
  have h := (mem_unitFiltration_iff_le_realAddValuation_sub_one n.succ_ne_zero _).mp
    (pow_natCard_sub_one_mul_pow_mem_unitFiltration_succ hu n)
  simpa using h

end TauCeti
