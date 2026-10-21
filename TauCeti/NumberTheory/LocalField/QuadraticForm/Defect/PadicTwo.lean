/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The quadratic defect over `ℚ_2`

Write `a ∈ ℚ_2ˣ` as `a = 2 ^ α u` with `u` a unit of `ℤ_2`. The defect exponent
`δ(a) = sup_ξ v(a - ξ²)` is

* `α` when `α` is odd;
* `α + 1` when `α` is even and `u ≡ 3 mod 4`, that is `ε(u) = 1`;
* `α + 2` when `α` is even and `u ≡ 5 mod 8`;
* `⊤` when `α` is even and `u ≡ 1 mod 8`, that is when `a` is a square.

Here `ε` and `ω` are Serre's sign functions `TauCeti.serreEps` and `TauCeti.serreOmega`. Since
`v(2) = 1`, the defects of the units of `ℤ_2` are `0`, `4 ℤ_2` and `2 ℤ_2`, attained by `1`, `5`
and `-1`: this is the general list `0`, `𝓂^{2e}`, `𝓂^{2k+1}` (`k < e`) of
`TauCeti.defectExponent_eq_two_mul_natCastValuation_or_odd` at `e = 1`.

On the eight representatives `1, -1, 5, -5, 2, -2, 10, -10` of the square classes of `ℚ_2`
(`TauCeti.padicTwoSquareClassRep`) the defects are `0, 2, 4, 2, 2, 2, 2, 2` times `ℤ_2`. In
particular `𝔡(-5) = 2 ℤ_2`, while `𝔡(-1) 𝔡(5) = 8 ℤ_2`: the defect is not multiplicative.

## Main results

* `TauCeti.defectExponent_padicTwo`: the defect exponent of `2 ^ α u` over `ℚ_2`.
* `TauCeti.defectExponent_padicTwoSquareClassRep` and
  `TauCeti.quadraticDefect_padicTwoSquareClassRep`: the defect exponents and the defects of the
  eight square-class representatives.
* `TauCeti.quadraticDefect_neg_one_mul_five_ne_padicTwo`: `𝔡(-5) ≠ 𝔡(-1) 𝔡(5)` over `ℚ_2`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, 63:2 and 63:3.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3.3.
-/

public section

open ValuativeRel

namespace TauCeti

/-- The `2`-adic valuation of `2 ^ k` is `k`. -/
private theorem valuation_two_pow (k : ℕ) : Padic.valuation ((2 : ℚ_[2]) ^ k) = k := by
  rw [Padic.valuation_pow, Padic.valuation_ofNat, padicValNat_self, Nat.cast_one, mul_one]

/-- The `2`-adic valuation of `2 ^ k m`, for an odd integer `m`, is `k`: the case `p = 2` of
`Padic.valuation_p_zpow_mul`, with `v(m) = 0`. -/
private theorem valuation_two_pow_mul_intCast {k : ℕ} {m : ℤ} (hm : Odd m) :
    Padic.valuation ((2 : ℚ_[2]) ^ k * (m : ℚ_[2])) = k := by
  have h := Padic.valuation_p_zpow_mul (p := 2) k
    (Int.cast_ne_zero.mpr (by rintro rfl; simp at hm) : (m : ℚ_[2]) ≠ 0)
  rw [Padic.valuation_intCast,
    padicValInt.eq_zero_of_not_dvd (by simpa [← even_iff_two_dvd] using hm), Nat.cast_zero,
    add_zero] at h
  exact_mod_cast h

/-- An element `1 + x` of `ℚ_2` with `v(x) = 1` has defect exponent `1`. -/
private theorem defectExponent_padicTwo_of_eq_one_add {a x : ℚ_[2]ˣ}
    (hx : (x : ℚ_[2]).valuation = 1) (ha : (a : ℚ_[2]) = 1 + x) : defectExponent a = 1 := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hxu : IsUniformizer ℚ_[2] x := by
    rw [isUniformizer_def, ← ofAdd_toAdd (normalizedValuation ℚ_[2] x),
      Padic.toAdd_normalizedValuation_eq_valuation, hx]
  obtain ⟨ϖ, hϖ, hϖx⟩ := (isUniformizer_iff_exists_irreducible ℚ_[2] x).mp hxu
  have h := defectExponent_one_add_pow_odd h2 hϖ (k := 0)
    (by rw [Padic.natCastValuation_self (p := 2)]; exact one_pos)
  -- `1 + ϖ ^ (2 * 0 + 1) = 1 + x = a`, whatever the nonvanishing proof carried by `Units.mk0`.
  have hϖa : ∀ h, Units.mk0 (1 + (ϖ : ℚ_[2]) ^ (2 * 0 + 1)) h = a := fun _ ↦
    Units.ext (by simp [ha, hϖx])
  rw [hϖa] at h
  exact_mod_cast h

/-- The defect exponent of `-1` over `ℚ_2` is `1`: `-1 = 1 + (-2)`. -/
private theorem defectExponent_padicTwo_of_coe_eq_neg_one {a : ℚ_[2]ˣ} (ha : (a : ℚ_[2]) = -1) :
    defectExponent a = 1 :=
  defectExponent_padicTwo_of_eq_one_add (x := Units.mk0 (2 ^ 1 * ((-1 : ℤ) : ℚ_[2])) (by simp))
    (valuation_two_pow_mul_intCast (by decide)) (by rw [ha]; norm_num)

/-- The defect exponent of `-5` over `ℚ_2` is `1`: `-5 = 1 + (-6)`. -/
private theorem defectExponent_padicTwo_of_coe_eq_neg_five {a : ℚ_[2]ˣ} (ha : (a : ℚ_[2]) = -5) :
    defectExponent a = 1 :=
  defectExponent_padicTwo_of_eq_one_add (x := Units.mk0 (2 ^ 1 * ((-3 : ℤ) : ℚ_[2])) (by simp))
    (valuation_two_pow_mul_intCast (by decide)) (by rw [ha]; norm_num)

/-- The defect exponent of `5` over `ℚ_2` is `2 = 2 v(2)`: `5 - 1 = 4` gives the lower bound, and
the local square theorem the upper bound. -/
private theorem defectExponent_padicTwo_of_coe_eq_five {a : ℚ_[2]ˣ} (ha : (a : ℚ_[2]) = 5) :
    defectExponent a = 2 := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hsq : ¬IsSquare a := by
    rw [← isSquare_units_val_iff, ha]
    exact Padic.not_isSquare_five
  refine le_antisymm ?_ ?_
  · have hv : valuation ℚ_[2] (a : ℚ_[2]) = 1 := by
      rw [← normalizedValuation_eq_one_iff, ← toAdd_eq_zero,
        Padic.toAdd_normalizedValuation_eq_valuation, ha]
      simp
    simpa [Padic.natCastValuation_self (p := 2)] using
      defectExponent_le_two_mul_natCastValuation h2 hv hsq
  · have h := le_defectExponent a 1 (Units.mk0 (2 ^ 2) (by simp)) (by rw [ha]; norm_num)
    rwa [Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, valuation_two_pow] at h

/-- The defect exponent of a unit `u` of `ℤ_2`, read in `ℚ_2`: it is `1` when `u ≡ 3 mod 4`, `2`
when `u ≡ 5 mod 8`, and `⊤` when `u ≡ 1 mod 8`. -/
private theorem defectExponent_padicTwo_of_coe_eq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) :
    defectExponent a = if serreEps u = 1 then 1 else if serreOmega u = 1 then 2 else ⊤ := by
  -- Write `u = (-1) ^ ε(u) 5 ^ ω(u) w²`; the square `w²` of a unit does not change `δ`.
  obtain ⟨w, hw⟩ := exists_eq_neg_one_pow_mul_five_pow_mul_sq u
  let w' : ℚ_[2]ˣ := Units.mk0 ((w : ℤ_[2]) : ℚ_[2]) (PadicInt.coe_ne_zero.mpr w.ne_zero)
  let b : ℚ_[2]ˣ := Units.mk0 ((-1) ^ (serreEps u).val * 5 ^ (serreOmega u).val) (by simp)
  have hab : a = b * w' ^ 2 := Units.ext <| by
    have h5 : ((5 : ℤ_[2]) : ℚ_[2]) = 5 := by norm_cast
    simp only [ha, hw, b, w', Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    push_cast [h5]
    ring
  have hw' : (normalizedValuation ℚ_[2] w').toAdd = 0 := by
    rw [Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, PadicInt.valuation_coe,
      PadicInt.valuation_eq_zero_of_isUnit w.isUnit, Nat.cast_zero]
  have hb : (b : ℚ_[2]) = (-1) ^ (serreEps u).val * 5 ^ (serreOmega u).val := Units.val_mk0 _
  rw [hab, defectExponent_mul_sq, hw', mul_zero, WithTop.coe_zero, add_zero]
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key (serreEps u) with he | he <;> rcases key (serreOmega u) with ho | ho <;>
    simp only [he, ho, ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, mul_one] at hb <;>
    simp only [he, ho, zero_ne_one, ↓reduceIte]
  · exact defectExponent_eq_top_iff.mpr (isSquare_units_val_iff.mp (hb ▸ IsSquare.one))
  · exact defectExponent_padicTwo_of_coe_eq_five hb
  · exact defectExponent_padicTwo_of_coe_eq_neg_one hb
  · exact defectExponent_padicTwo_of_coe_eq_neg_five (by rw [hb]; ring)

/-- **The defect exponent over `ℚ_2`.** For `a = 2 ^ α u` with `u` a unit of `ℤ_2`, the defect
exponent `δ(a)` is `α` when `α` is odd. When `α` is even it is `α + 1` if `u ≡ 3 mod 4`, that is
`ε(u) = 1`, it is `α + 2` if `u ≡ 5 mod 8`, and it is `⊤`, so that `a` is a square, if
`u ≡ 1 mod 8`. -/
theorem defectExponent_padicTwo {a : ℚ_[2]ˣ} {α : ℤ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = 2 ^ α * u) :
    defectExponent a = if Odd α then (α : WithTop ℤ) else
      if serreEps u = 1 then (α + 1 : ℤ) else if serreOmega u = 1 then (α + 2 : ℤ) else ⊤ := by
  -- The defects of `±1` and `±5` come from the general theory; the square factor and the power
  -- of `2` are moved with `defectExponent_mul_sq` and `defectExponent_of_odd`.
  have hv : (normalizedValuation ℚ_[2] a).toAdd = α := by
    have h := Padic.valuation_p_zpow_mul (p := 2) α (PadicInt.coe_ne_zero.mpr u.ne_zero)
    rw [PadicInt.valuation_coe, PadicInt.valuation_eq_zero_of_isUnit u.isUnit, Nat.cast_zero,
      add_zero] at h
    rw [Padic.toAdd_normalizedValuation_eq_valuation, ha]
    exact_mod_cast h
  by_cases hα : Odd α
  · simp only [hα, ↓reduceIte]
    rw [defectExponent_of_odd (hv ▸ hα), hv]
  -- For `α = 2m`, `a` is the unit `u` times the square of `2 ^ m`.
  obtain ⟨m, rfl⟩ := Int.not_odd_iff_even.mp hα
  let u' : ℚ_[2]ˣ := Units.mk0 ((u : ℤ_[2]) : ℚ_[2]) (PadicInt.coe_ne_zero.mpr u.ne_zero)
  let t : ℚ_[2]ˣ := Units.mk0 (2 ^ m) (zpow_ne_zero _ two_ne_zero)
  have hat : a = u' * t ^ 2 := Units.ext <| by
    simp only [ha, u', t, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [zpow_add₀ two_ne_zero]
    ring
  have ht : (normalizedValuation ℚ_[2] t).toAdd = m := by
    simp [t]
  simp only [hα, ↓reduceIte]
  rw [hat, defectExponent_mul_sq, ht, defectExponent_padicTwo_of_coe_eq rfl]
  split_ifs
  · rw [← WithTop.coe_one, ← WithTop.coe_add]
    congr 1
    ring
  · rw [← WithTop.coe_ofNat, ← WithTop.coe_add]
    congr 1
    ring
  · exact WithTop.top_add _

/-- **The defect exponents of the square classes of `ℚ_2`.** On the representatives
`1, -1, 5, -5, 2, -2, 10, -10` of `TauCeti.padicTwoSquareClassRep`, the defect exponent takes the
values `⊤, 1, 2, 1, 1, 1, 1, 1`. -/
@[simp]
theorem defectExponent_padicTwoSquareClassRep (i : Fin 8) :
    defectExponent (padicTwoSquareClassRep i) = ![⊤, 1, 2, 1, 1, 1, 1, 1] i := by
  have hodd : ∀ {a : ℚ_[2]ˣ} {m : ℤ}, Odd m → (a : ℚ_[2]) = 2 ^ 1 * (m : ℚ_[2]) →
      defectExponent a = 1 := fun {a} {m} hm ha ↦ by
    have hv : (normalizedValuation ℚ_[2] a).toAdd = 1 := by
      rw [Padic.toAdd_normalizedValuation_eq_valuation, ha, valuation_two_pow_mul_intCast hm,
        Nat.cast_one]
    rw [defectExponent_of_odd (hv ▸ odd_one), hv, WithTop.coe_one]
  fin_cases i
  · exact defectExponent_eq_top_iff.mpr (isSquare_units_val_iff.mp ⟨1, by simp⟩)
  · exact defectExponent_padicTwo_of_coe_eq_neg_one (by simp)
  · exact defectExponent_padicTwo_of_coe_eq_five (by simp)
  · exact defectExponent_padicTwo_of_coe_eq_neg_five (by simp)
  · exact hodd (m := 1) odd_one (by simp)
  · exact hodd (m := -1) (by decide) (by simp)
  · exact hodd (m := 5) (by decide) (by simp; norm_num)
  · exact hodd (m := -5) (by decide) (by simp; norm_num)

/-- **The quadratic defects of the square classes of `ℚ_2`.** On the representatives
`1, -1, 5, -5, 2, -2, 10, -10` of `TauCeti.padicTwoSquareClassRep`, the quadratic defect is
`0, 2 ℤ_2, 4 ℤ_2, 2 ℤ_2, 2 ℤ_2, 2 ℤ_2, 2 ℤ_2, 2 ℤ_2`. In particular the units `1`, `5` and `-1`
attain the three defects `0`, `4 ℤ_2` and `2 ℤ_2` of units of `ℤ_2`. -/
@[simp]
theorem quadraticDefect_padicTwoSquareClassRep (i : Fin 8) :
    quadraticDefect (padicTwoSquareClassRep i) =
      FractionalIdeal.spanSingleton _ (![0, 2, 4, 2, 2, 2, 2, 2] i) := by
  -- `2` and `4` as units of `ℚ_2`, with valuations `1` and `2`.
  let c : ℕ → ℚ_[2]ˣ := fun k ↦ Units.mk0 (2 ^ k) (by simp)
  have hc : ∀ k, (normalizedValuation ℚ_[2] (c k)).toAdd = k := fun k ↦ by
    rw [Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, valuation_two_pow]
  fin_cases i
  · simp [quadraticDefect_eq_zero_iff, ← defectExponent_eq_top_iff]
  case «2» =>
    rw [quadraticDefect_eq_spanSingleton_of_defectExponent_eq (c := c 2) (by simp [hc])]
    norm_num [c]
  all_goals
    rw [quadraticDefect_eq_spanSingleton_of_defectExponent_eq (c := c 1) (by simp [hc])]
    norm_num [c]

/-- **The quadratic defect is not multiplicative.** Over `ℚ_2`, `𝔡(-5) = 2 ℤ_2`, while
`𝔡(-1) 𝔡(5) = 2 ℤ_2 · 4 ℤ_2 = 8 ℤ_2`. -/
theorem quadraticDefect_neg_one_mul_five_ne_padicTwo :
    quadraticDefect (-1 * Units.mk0 (5 : ℚ_[2]) (by norm_num)) ≠
      quadraticDefect (-1) * quadraticDefect (Units.mk0 (5 : ℚ_[2]) (by norm_num)) := by
  have h1 : (-1 : ℚ_[2]ˣ) = padicTwoSquareClassRep 1 := Units.ext (by simp)
  have h5 : Units.mk0 (5 : ℚ_[2]) (by norm_num) = padicTwoSquareClassRep 2 := Units.ext (by simp)
  have h15 : (-1 : ℚ_[2]ˣ) * Units.mk0 5 (by norm_num) = padicTwoSquareClassRep 3 :=
    Units.ext (by simp)
  rw [h15, h1, h5, quadraticDefect_padicTwoSquareClassRep, quadraticDefect_padicTwoSquareClassRep,
    quadraticDefect_padicTwoSquareClassRep, ← map_mul]
  intro h
  norm_num at h
  -- Comparing valuations, `2 ℤ_2 = 8 ℤ_2` would give `v(8) ≤ v(2)`.
  have h28 := (toAdd_normalizedValuation_le_iff_valuation_le
    (Units.mk0 ((2 : ℚ_[2]) ^ 3) (by simp)) (Units.mk0 (2 ^ 1) (by simp))).mpr
    (spanSingleton_le_spanSingleton_iff_valuation_le.mp (by norm_num [h.le]))
  rw [Padic.toAdd_normalizedValuation_eq_valuation, Padic.toAdd_normalizedValuation_eq_valuation,
    Units.val_mk0, Units.val_mk0, valuation_two_pow, valuation_two_pow] at h28
  norm_num at h28

end TauCeti
