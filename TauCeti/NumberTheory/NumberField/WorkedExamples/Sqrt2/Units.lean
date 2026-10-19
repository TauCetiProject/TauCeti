/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Elimination.Basic
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt2.RealPlace
import TauCeti.NumberTheory.NumberField.Units.Regulator.Height
import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt2.Ramification

/-!
# The fundamental unit, the regulator and the height of `1 + √2`

Let `K` be a number field generated over `ℚ` by an algebraic integer `θ` with
`minpoly ℤ θ = X² − 2`, so that `K = ℚ(√2)`. Then `1 + θ` is a unit, since
`(1 + θ) (θ − 1) = θ² − 1 = 1`, and at the real place where `θ` has the value `√2` it has the value
`1 + √2`. The unit candidates below `1 + √2` are the quadratics `X² + mX ± 1` with `|m| ≤ 3`. All
but `X² − X − 1` have no real root in `(1, 1 + √2)`, and `X² − X − 1` has discriminant `5`, which
is not `8` times a square, so it is not the minimal polynomial of an integral primitive element of
a field of discriminant `8`. This elimination certificate makes `1 + θ` a fundamental unit, and the
regulator of `ℚ(√2)` is `Real.log (1 + √2)`.

In unit rank one the logarithmic height of a fundamental unit is the regulator, so
`absLogHeight₁ (1 + θ) = Real.log (1 + √2) / 2`. This is the test case for the comparison between
the regulator and the heights of a fundamental system at `r = 1`, `d = 2`: Hadamard's upper bound
reads `log (1 + √2) ≤ 4 · log (1 + √2) / 2`, while Bugeaud–Győry's bound
`∏ i, h(ε i) ≤ (r!)² / (2 ^ (r − 1) d ^ r) · regulator K` for a reduced fundamental system holds
with equality, `log (1 + √2) / 2 = (1 / 2) · log (1 + √2)`, so its constant cannot be lowered.

## Main results

* `TauCeti.NumberField.Sqrt2.one_add_mul_sub_one_eq_one`: `(1 + θ) (θ − 1) = 1`, so `1 + θ` is a
  unit (`TauCeti.NumberField.Sqrt2.isUnit_one_add`).
* `TauCeti.NumberField.Sqrt2.unitCandidateEliminationCertificate_one_add_sqrt_two`: the
  elimination certificate at `1 + √2`.
* `TauCeti.NumberField.Sqrt2.closure_sup_torsion_eq_top`: a unit with value `1 + θ` generates the
  units of `ℚ(√2)` modulo torsion.
* `TauCeti.NumberField.Sqrt2.regulator_eq_log_one_add_sqrt_two`:
  `regulator K = Real.log (1 + √2)`.
* `TauCeti.NumberField.Sqrt2.absLogHeight₁_one_add_eq`:
  `absLogHeight₁ (1 + θ) = Real.log (1 + √2) / 2`.
* `TauCeti.NumberField.Sqrt2.absLogHeight₁_one_add_eq_regulator_div_two` and
  `TauCeti.NumberField.Sqrt2.regulator_le_four_mul_absLogHeight₁_one_add`: the two comparisons
  between the regulator and the height of the fundamental unit.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, Lemma 1.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units TauCeti.NumberField
  TauCeti.NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Sqrt2

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- An algebraic integer `θ` with `minpoly ℤ θ = X² − 2` makes `1 + θ` a unit:
`(1 + θ) (θ − 1) = 1`. -/
@[simp]
theorem one_add_mul_sub_one_eq_one (hmin : minpoly ℤ θ = X ^ 2 - 2) :
    (1 + θ) * (θ - 1) = 1 := by
  linear_combination sq_eq_two hmin

omit [NumberField K] in
/-- `1 + θ` is a unit of `𝓞 K`. -/
theorem isUnit_one_add (hmin : minpoly ℤ θ = X ^ 2 - 2) : IsUnit (1 + θ) :=
  IsUnit.of_mul_eq_one _ (one_add_mul_sub_one_eq_one hmin)

/-- **The elimination certificate at `1 + √2`.** In `ℚ(√2)`, every candidate polynomial
`X² + mX ± 1` with `|m| ≤ 2 + √2` either has no real root in `(1, 1 + √2)` or, as for
`X² − X − 1`, has a discriminant that is not `8` times a positive square. -/
theorem unitCandidateEliminationCertificate_one_add_sqrt_two (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    UnitCandidateEliminationCertificate K (1 + √2) := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hs2 : √2 < 2 := by nlinarith
  refine UnitCandidateEliminationCertificate.of_discr fun g hg => ?_
  rw [mem_unitCandidates_iff, finrank_eq_two hmin hgen] at hg
  obtain ⟨hmonic, hdeg, h0, hk⟩ := hg
  -- The candidate is `X² + mX + c` with `c = ±1` and `|m| ≤ 2 + √2`, so `|m| ≤ 3`.
  have hm := hk 1 one_pos one_lt_two
  norm_num at hm
  have hm3 : -4 < g.coeff 1 ∧ g.coeff 1 < 4 := by
    rw [abs_le] at hm
    constructor
    · exact_mod_cast (by linarith : (-4 : ℝ) < g.coeff 1)
    · exact_mod_cast (by linarith : (g.coeff 1 : ℝ) < 4)
  have h2 : g.coeff 2 = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  have heval (x : ℝ) : aeval x g = x ^ 2 + g.coeff 1 * x + g.coeff 0 := by
    rw [aeval_eq_sum_range, hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zsmul_eq_mul, h2, Int.cast_one,
      pow_zero, pow_one, zero_add]
    ring
  have hdiscr : g.discr = g.coeff 1 ^ 2 - 4 * g.coeff 0 := by
    rw [discr_of_degree_eq_two (by rw [degree_eq_natDegree hmonic.ne_zero, hdeg]; rfl), h2,
      mul_one]
  obtain ⟨hm1, hm2⟩ := hm3
  generalize g.coeff 1 = m at hm1 hm2 heval hdiscr
  -- `X² − X − 1` has the root `(1 + √5) / 2` in the interval; its discriminant is `5`.
  by_cases hbad : m = -1 ∧ g.coeff 0 = -1
  · obtain ⟨rfl, hc⟩ := hbad
    refine Or.inr fun n _ h => ?_
    rw [hdiscr, hc, discr_eq_eight hmin hgen] at h
    have : (8 : ℤ) ∣ 5 := ⟨n ^ 2, by linarith⟩
    omega
  -- Every other candidate has no real root in `(1, 1 + √2)`.
  refine Or.inl fun x ⟨hx1, hx2⟩ => ?_
  rw [heval]
  have hA : 0 < (1 + √2 - x) * (x - 1 + √2) := mul_pos (by linarith) (by linarith)
  have hB : 0 < (x - 1) * (1 + √2 - x) := mul_pos (by linarith) (by linarith)
  have hC : 0 < x - 1 := by linarith
  interval_cases m <;> rcases h0 with h0 | h0 <;> rw [h0] <;> push_cast <;>
    first | (exfalso; exact hbad ⟨rfl, h0⟩) | nlinarith

/-- **`1 + √2` is a fundamental unit of `ℚ(√2)`.** A unit `u` with `(u : 𝓞 K) = 1 + θ` generates
the unit group modulo torsion. -/
theorem closure_sup_torsion_eq_top (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ} (hu : (u : 𝓞 K) = 1 + θ) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ := by
  obtain ⟨w, hw, hwu⟩ := exists_isReal_and_apply_eq_one_add_sqrt_two hmin hgen
  rw [← hu] at hwu
  have h1 : 1 < w u := by rw [hwu]; exact lt_add_of_pos_right 1 (by positivity)
  refine UnitCandidateEliminationCertificate.sound ?_ (units_rank_eq_one hmin hgen)
    (finrank_eq_two hmin hgen ▸ Nat.prime_two) hw h1
  rw [hwu]
  exact unitCandidateEliminationCertificate_one_add_sqrt_two hmin hgen

/-- **The regulator of `ℚ(√2)`** is `Real.log (1 + √2)`. -/
theorem regulator_eq_log_one_add_sqrt_two (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : regulator K = Real.log (1 + √2) := by
  obtain ⟨w, hw, hwu⟩ := exists_isReal_and_apply_eq_one_add_sqrt_two hmin hgen
  obtain ⟨u, hu⟩ := isUnit_one_add hmin
  rw [← hu] at hwu
  have h1 : 1 < w u := by rw [hwu]; exact lt_add_of_pos_right 1 (by positivity)
  rw [regulator_eq_mult_log_of_rank_eq_one (units_rank_eq_one hmin hgen) u
    (closure_sup_torsion_eq_top hmin hgen hu) w h1, hwu, hw.mult_eq_one, Nat.cast_one, one_mul]

/-- **The reduced bound is sharp at `ℚ(√2)`.** The absolute logarithmic height of the fundamental
unit `1 + √2` equals `(r!)² / (2 ^ (r - 1) d ^ r) = 1 / 2` times the regulator. -/
theorem absLogHeight₁_one_add_eq_regulator_div_two (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    absLogHeight₁ ((1 + θ : 𝓞 K) : K) = regulator K / 2 := by
  obtain ⟨u, hu⟩ := isUnit_one_add hmin
  rw [← hu, absLogHeight₁_eq_regulator_div_finrank_of_rank_eq_one (units_rank_eq_one hmin hgen)
    (closure_sup_torsion_eq_top hmin hgen hu), finrank_eq_two hmin hgen, Nat.cast_ofNat]

/-- The absolute logarithmic height of the fundamental unit `1 + √2` of `ℚ(√2)` is
`Real.log (1 + √2) / 2`. -/
theorem absLogHeight₁_one_add_eq (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    absLogHeight₁ ((1 + θ : 𝓞 K) : K) = Real.log (1 + √2) / 2 := by
  rw [absLogHeight₁_one_add_eq_regulator_div_two hmin hgen,
    regulator_eq_log_one_add_sqrt_two hmin hgen]

/-- **Hadamard's bound at `ℚ(√2)`.** The regulator is at most `(2d) ^ r = 4` times the absolute
logarithmic height of the fundamental unit; here `log (1 + √2) ≤ 4 · log (1 + √2) / 2`. -/
theorem regulator_le_four_mul_absLogHeight₁_one_add (hmin : minpoly ℤ θ = X ^ 2 - 2)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    regulator K ≤ 4 * absLogHeight₁ ((1 + θ : 𝓞 K) : K) := by
  obtain ⟨u, hu⟩ := isUnit_one_add hmin
  have hr := units_rank_eq_one hmin hgen
  have hε : Subgroup.closure (Set.range fun _ : Fin (rank K) ↦ u) ⊔ torsion K = ⊤ := by
    have : Nonempty (Fin (rank K)) := ⟨⟨0, by omega⟩⟩
    rw [Set.range_const]
    exact closure_sup_torsion_eq_top hmin hgen hu
  have h := regulator_le_prod_absLogHeight₁ hε
  rw [hr, finrank_eq_two hmin hgen, Fin.prod_univ_one, hu] at h
  norm_num at h ⊢
  exact h

end TauCeti.NumberField.Sqrt2
