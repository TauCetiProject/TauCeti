/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic

/-!
# Bounding the regulator by heights

Hadamard's inequality bounds the regulator of any family of units by the product of twice
their relative logarithmic heights. For a fundamental system this bounds the field regulator.
In absolute logarithmic height the constant is `(2 * [K : ℚ]) ^ rank K`, as in
Bugeaud–Győry, Lemma 1. In particular, the product of the heights of any fundamental system
is positive, including in rank zero, when the product is empty and equals one.

The estimates combine the determinant bounds in `Regulator.Basic` with the comparison between
height and the `ℓ¹` norm of the logarithmic embedding in `Units.Log.Embedding`.

In unit rank one the comparison is an identity. The two infinite places contribute equally to
the height of a unit, so the relative logarithmic height of a fundamental unit is the regulator,
and its absolute logarithmic height is `regulator K / [K : ℚ]`. Hence, at `rank K = 1`, the
constant `(r!)² / (2 ^ (r - 1) d ^ r) = 1 / d` of Bugeaud–Győry's lower bound for the regulator by
the heights of a reduced fundamental system is attained by every fundamental unit.

For Mathlib's canonical `fundSystem K`, positivity specializes to
`prod_absLogHeight₁_pos (closure_fundSystem_sup_torsion_eq_top (K := K))`.
Both this specialization and the regulator bounds are available from the present module.

## References

* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, Lemma 1 (the case of the infinite places).
-/

public section

open Height NumberField NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- Hadamard's bound for any family of units, in relative logarithmic height. No generation
or independence hypothesis is needed. -/
theorem regOfFamily_le_prod_logHeight₁ (u : Fin (rank K) → (𝓞 K)ˣ) :
    regOfFamily u ≤ 2 ^ rank K * ∏ i, logHeight₁ (u i : K) := by
  classical
  calc
    regOfFamily u ≤ ∏ i, ∑ w, |logEmbedding K (Additive.ofMul (u i)) w| :=
      regOfFamily_le_prod_sum_abs_logEmbedding u
    _ ≤ ∏ i, 2 * logHeight₁ (u i : K) := by
      exact Finset.prod_le_prod₀ (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        (fun i _ ↦ sum_abs_logEmbedding_le_two_mul_logHeight₁ (u i))
    _ = 2 ^ rank K * ∏ i, logHeight₁ (u i : K) := by
      simp [Finset.prod_mul_distrib]

/-- Hadamard's bound for any family of units, in absolute logarithmic height. The degree
factor converts each relative height into an absolute height. -/
theorem regOfFamily_le_prod_absLogHeight₁ (u : Fin (rank K) → (𝓞 K)ˣ) :
    regOfFamily u ≤ (2 * Module.finrank ℚ K : ℝ) ^ rank K *
      ∏ i, absLogHeight₁ (u i : K) := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hheight (x : K) : logHeight₁ x = (Module.finrank ℚ K : ℝ) * absLogHeight₁ x := by
    rw [NumberField.absLogHeight₁_eq_div]
    field_simp
  simpa [hheight, Finset.prod_mul_distrib, mul_pow, mul_assoc] using
    regOfFamily_le_prod_logHeight₁ u

/-- Every fundamental system bounds the field regulator by `2 ^ rank K` times the product
of its relative logarithmic heights. -/
theorem regulator_le_prod_logHeight₁ {ε : Fin (rank K) → (𝓞 K)ˣ}
    (hε : Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤) :
    regulator K ≤ 2 ^ rank K * ∏ i, logHeight₁ (ε i : K) :=
  (regOfFamily_eq_regulator_iff.mpr hε).symm.trans_le (regOfFamily_le_prod_logHeight₁ ε)

/-- Every fundamental system bounds the field regulator by `(2d) ^ r` times the product
of its absolute logarithmic heights, where `d` is the degree and `r` the unit rank. -/
theorem regulator_le_prod_absLogHeight₁ {ε : Fin (rank K) → (𝓞 K)ˣ}
    (hε : Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤) :
    regulator K ≤ (2 * Module.finrank ℚ K : ℝ) ^ rank K *
      ∏ i, absLogHeight₁ (ε i : K) :=
  (regOfFamily_eq_regulator_iff.mpr hε).symm.trans_le (regOfFamily_le_prod_absLogHeight₁ ε)

/-- The product of the absolute logarithmic heights of any fundamental system is positive.
This includes rank zero, when the product is one. -/
theorem prod_absLogHeight₁_pos {ε : Fin (rank K) → (𝓞 K)ˣ}
    (hε : Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤) :
    0 < ∏ i, absLogHeight₁ (ε i : K) := by
  have h := (regulator_pos K).trans_le (regulator_le_prod_absLogHeight₁ hε)
  have hd : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  exact (mul_pos_iff_of_pos_left (by positivity)).mp h

/-! ### Unit rank one -/

/-- In unit rank one, the relative logarithmic height of a unit is the index of the subgroup it
generates together with the torsion, times the regulator. -/
theorem logHeight₁_eq_index_mul_regulator (hr : rank K = 1) (u : (𝓞 K)ˣ) :
    logHeight₁ (u : K) = ((Subgroup.closure {u} ⊔ torsion K).index : ℝ) * regulator K := by
  have hplaces : Fintype.card (InfinitePlace K) = 2 := by
    unfold rank at hr
    omega
  have h := two_mul_logHeight₁_eq_sum_mult_mul_abs_log u
  simp only [mult_abs_log_eq_index_mul_regulator hr u, Finset.sum_const, Finset.card_univ,
    hplaces, nsmul_eq_mul, Nat.cast_ofNat] at h
  linarith

/-- In unit rank one, the absolute logarithmic height of a unit is its index times the regulator,
divided by the degree. -/
theorem absLogHeight₁_eq_index_mul_regulator_div_finrank (hr : rank K = 1) (u : (𝓞 K)ˣ) :
    absLogHeight₁ (u : K) =
      ((Subgroup.closure {u} ⊔ torsion K).index : ℝ) * regulator K / Module.finrank ℚ K := by
  rw [NumberField.absLogHeight₁_eq_div, logHeight₁_eq_index_mul_regulator hr]

/-- In unit rank one, the relative logarithmic height of a fundamental unit is the regulator. -/
theorem logHeight₁_eq_regulator_of_rank_eq_one (hr : rank K = 1) {ε : (𝓞 K)ˣ}
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) : logHeight₁ (ε : K) = regulator K := by
  simp [logHeight₁_eq_index_mul_regulator hr, hε]

/-- In unit rank one, the absolute logarithmic height of a fundamental unit is the regulator
divided by the degree. -/
theorem absLogHeight₁_eq_regulator_div_finrank_of_rank_eq_one (hr : rank K = 1) {ε : (𝓞 K)ˣ}
    (hε : Subgroup.closure {ε} ⊔ torsion K = ⊤) :
    absLogHeight₁ (ε : K) = regulator K / Module.finrank ℚ K := by
  simpa [hε] using absLogHeight₁_eq_index_mul_regulator_div_finrank hr ε

end TauCeti.NumberField.Units
