/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import TauCeti.NumberTheory.NumberField.Units.Basic
public import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic

/-!
# The house of a unit and exponent bounds

Let `K` be a number field of degree `d` and `u` a unit of `𝓞 K`. Since `|N(u)| = 1` and every
conjugate of `u` has absolute value at most `house u`, every conjugate of `u` also has absolute
value at least `house u ^ (-(d - 1))`. Hence `|log ‖σ u‖| ≤ (d - 1) * log (house u)` for every
complex embedding `σ`, and the logarithmic embedding of `u` has sup norm at most
`2 * (d - 1) * log (house u)`. When `d ≥ 2`, some conjugate of `u` is at most
`house u ^ (-1 / (d - 1))` in absolute value.

For a family `u` of `rank K` units of maximal rank, a unit `x = ζ * ∏ j, u j ^ e j` with `ζ` a
root of unity has its exponent vector `e` equal to the coordinates of the logarithmic embedding
of `x` on the basis `basisOfIsMaxRank`
(`TauCeti.NumberField.Units.basisOfIsMaxRank_repr_logEmbedding`). Writing `κ(u)` for the operator
norm of this coordinate map with respect to the sup norms, every exponent is therefore bounded by
`2 * (d - 1) * κ(u) * log (house x)`. This converts upper bounds for the house of a unit into
bounds for its exponents, which is how unit equations are reduced to finitely many cases.

## Main results

* `Units.inv_house_pow_le_norm_embedding`: every conjugate of a unit `u` has absolute value at
  least `(house u ^ (d - 1))⁻¹`.
* `Units.abs_log_norm_embedding_le`: `|log ‖σ u‖| ≤ (d - 1) * log (house u)`.
* `Units.exists_norm_embedding_le_house_rpow`: for `d ≥ 2`, some conjugate of `u` has absolute
  value at most `house u ^ (-1 / (d - 1))`.
* `Units.norm_logEmbedding_le_mul_log_house`: `‖logEmbedding u‖ ≤ 2 * (d - 1) * log (house u)`.
* `TauCeti.NumberField.Units.abs_le_mul_log_house_of_eq_mul_prod_zpow`: the exponent bound
  `|e j| ≤ 2 * (d - 1) * κ(u) * log (house x)`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Lemma 5.9 and the proof of Theorem 5.12, pp. 91–95.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open scoped NumberField

namespace Units

variable {K : Type*} [Field K] [NumberField K]

/-- The house of a unit is at least `1`. -/
theorem one_le_house (u : (𝓞 K)ˣ) : 1 ≤ house (u : K) :=
  one_le_house_of_isIntegral (RingOfIntegers.isIntegral_coe _) (NumberField.Units.coe_ne_zero u)

/-- Every conjugate of a unit `u` of a number field of degree `d` has absolute value at least
`(house u ^ (d - 1))⁻¹`, since `|N(u)| = 1` and the other `d - 1` conjugates are at most
`house u` in absolute value. -/
theorem inv_house_pow_le_norm_embedding (u : (𝓞 K)ˣ) (σ : K →+* ℂ) :
    (house (u : K) ^ (finrank ℚ K - 1))⁻¹ ≤ ‖σ u‖ := by
  have h : 1 ≤ ‖σ u‖ * house (u : K) ^ (finrank ℚ K - 1) := by
    simpa [← Rat.norm_cast_real, ← Rat.cast_abs] using norm_norm_le_norm_mul_house_pow (u : K) σ
  rwa [inv_le_iff_one_le_mul₀ (pow_pos (zero_lt_one.trans_le (one_le_house u)) _)]

/-- For a unit `u` of a number field of degree `d` and every complex embedding `σ`,
`|log ‖σ u‖| ≤ (d - 1) * log (house u)`. -/
theorem abs_log_norm_embedding_le (u : (𝓞 K)ˣ) (σ : K →+* ℂ) :
    |Real.log ‖σ u‖| ≤ (finrank ℚ K - 1 : ℝ) * Real.log (house (u : K)) := by
  have hH := one_le_house u
  have hL : 0 ≤ Real.log (house (u : K)) := Real.log_nonneg hH
  have hpos : 0 < ‖σ u‖ :=
    norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  have hcast : ((finrank ℚ K - 1 : ℕ) : ℝ) = finrank ℚ K - 1 := by
    rw [Nat.cast_sub finrank_pos, Nat.cast_one]
  -- The lower bound `-(d - 1) * log (house u) ≤ log ‖σ u‖`.
  have hlow : -((finrank ℚ K - 1 : ℝ) * Real.log (house (u : K))) ≤ Real.log ‖σ u‖ := by
    have h := Real.log_le_log (_root_.inv_pos.mpr (pow_pos (zero_lt_one.trans_le hH) _))
      (inv_house_pow_le_norm_embedding u σ)
    rwa [Real.log_inv, Real.log_pow, hcast] at h
  -- The upper bound: `log ‖σ u‖ ≤ log (house u)`, and both sides vanish when `d = 1`.
  have hup : Real.log ‖σ u‖ ≤ (finrank ℚ K - 1 : ℝ) * Real.log (house (u : K)) := by
    rcases (Nat.succ_le_of_lt (finrank_pos (R := ℚ) (M := K))).eq_or_lt with h1 | h2
    · -- When `d = 1`, the lower bound for `u⁻¹` gives `‖σ u‖ ≤ 1`.
      have h := inv_house_pow_le_norm_embedding u⁻¹ σ
      simp [← h1] at h
      simpa [← h1] using Real.log_nonpos hpos.le ((one_le_inv₀ hpos).mp h)
    · have h2' : (2 : ℝ) ≤ finrank ℚ K := by exact_mod_cast h2
      calc Real.log ‖σ u‖ ≤ Real.log (house (u : K)) :=
            Real.log_le_log hpos (norm_embedding_le_house _ σ)
        _ ≤ (finrank ℚ K - 1 : ℝ) * Real.log (house (u : K)) :=
            le_mul_of_one_le_left hL (by linarith)
  exact abs_le.mpr ⟨hlow, hup⟩

/-- In a number field of degree `d ≥ 2`, every unit `u` has a conjugate of absolute value at most
`house u ^ (-1 / (d - 1))`: the product of the `d - 1` conjugates other than the largest one is
`(house u)⁻¹`. -/
theorem exists_norm_embedding_le_house_rpow (u : (𝓞 K)ˣ) (hd : 2 ≤ finrank ℚ K) :
    ∃ σ : K →+* ℂ, ‖σ u‖ ≤ house (u : K) ^ (-1 / (finrank ℚ K - 1 : ℝ)) := by
  classical
  -- A conjugate attaining the house.
  obtain ⟨σ₀, -, hσ₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun σ : K →+* ℂ ↦ ‖σ (u : K)‖₊)
  have hσ₀H : ‖σ₀ u‖ = house (u : K) := by
    rw [house_eq_sup', hσ₀, coe_nnnorm]
  set H := house (u : K)
  have hH : 0 < H := zero_lt_one.trans_le (one_le_house u)
  by_contra! hlt
  have hprod := prod_norm_embedding_eq_one u
  have hcard : (Finset.univ.erase σ₀).card = finrank ℚ K - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Embeddings.card]
  have hne : (Finset.univ.erase σ₀).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hcast : ((finrank ℚ K - 1 : ℕ) : ℝ) = finrank ℚ K - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hd1 : (finrank ℚ K - 1 : ℝ) ≠ 0 := by
    rw [← hcast, Nat.cast_ne_zero]
    omega
  -- `(H ^ (-1 / (d - 1))) ^ (d - 1) = H⁻¹`.
  have hpow : (H ^ (-1 / (finrank ℚ K - 1 : ℝ))) ^ (finrank ℚ K - 1) = H⁻¹ := by
    rw [← Real.rpow_mul_natCast hH.le, hcast, div_mul_cancel₀ _ hd1, Real.rpow_neg_one]
  -- If every other conjugate exceeded `H ^ (-1 / (d - 1))`, their product would exceed `H⁻¹`.
  have hrest : H⁻¹ < ∏ σ ∈ Finset.univ.erase σ₀, ‖σ u‖ := by
    calc H⁻¹ = ∏ _σ ∈ Finset.univ.erase σ₀, H ^ (-1 / (finrank ℚ K - 1 : ℝ)) := by
          rw [Finset.prod_const, hcard, hpow]
      _ < ∏ σ ∈ Finset.univ.erase σ₀, ‖σ u‖ :=
          Finset.prod_lt_prod_of_nonempty₀ (fun _ _ ↦ Real.rpow_pos_of_pos hH _)
            (fun σ _ ↦ hlt σ) hne
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ σ₀), hσ₀H] at hprod
  have := mul_lt_mul_of_pos_left hrest hH
  rw [mul_inv_cancel₀ hH.ne', hprod] at this
  exact lt_irrefl _ this

open scoped Classical in
/-- The logarithmic embedding of a unit `u` of a number field of degree `d` has sup norm at most
`2 * (d - 1) * log (house u)`. -/
theorem norm_logEmbedding_le_mul_log_house (u : (𝓞 K)ˣ) :
    ‖logEmbedding K (Additive.ofMul u)‖ ≤
      2 * (finrank ℚ K - 1 : ℝ) * Real.log (house (u : K)) := by
  have hd : (0 : ℝ) ≤ finrank ℚ K - 1 := by
    rw [sub_nonneg]
    exact_mod_cast finrank_pos
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg zero_le_two hd)
    (Real.log_nonneg (one_le_house u)))).mpr fun w ↦ ?_
  have hmult : (mult w.1 : ℝ) ≤ 2 := by
    unfold mult
    split_ifs <;> norm_num
  rw [logEmbedding_component, Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_assoc]
  refine mul_le_mul hmult ?_ (abs_nonneg _) zero_le_two
  rw [← norm_embedding_eq w.1]
  exact abs_log_norm_embedding_le u _

end Units

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Exponent bound for units.** Let `u` be a family of units of maximal rank in a number field
of degree `d`, and let `κ(u)` be the operator norm, for the sup norms, of the coordinate map of
`basisOfIsMaxRank`. If `x = ζ * ∏ j, u j ^ e j` with `ζ` a root of unity, then
`|e j| ≤ 2 * (d - 1) * κ(u) * log (house x)` for every `j`. -/
theorem abs_le_mul_log_house_of_eq_mul_prod_zpow {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) {x ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) {e : Fin (rank K) → ℤ}
    (hx : x = ζ * ∏ j, u j ^ e j) (j : Fin (rank K)) :
    |(e j : ℝ)| ≤ 2 * (finrank ℚ K - 1 : ℝ) *
      ‖((basisOfIsMaxRank hu).equivFunL : logSpace K →L[ℝ] Fin (rank K) → ℝ)‖ *
        Real.log (house (x : K)) := by
  set f : logSpace K →L[ℝ] Fin (rank K) → ℝ := ↑(basisOfIsMaxRank hu).equivFunL
  set v := logEmbedding K (Additive.ofMul x)
  have hfv : f v j = e j := by
    simpa [f] using basisOfIsMaxRank_repr_logEmbedding hu hζ hx j
  calc |(e j : ℝ)| = ‖f v j‖ := by rw [hfv, Real.norm_eq_abs]
    _ ≤ ‖f v‖ := norm_le_pi_norm (f v) j
    _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
    _ ≤ ‖f‖ * (2 * (finrank ℚ K - 1 : ℝ) * Real.log (house (x : K))) :=
        mul_le_mul_of_nonneg_left x.norm_logEmbedding_le_mul_log_house (norm_nonneg f)
    _ = _ := by ring

end TauCeti.NumberField.Units
