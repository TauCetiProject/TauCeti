/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity

/-!
# Newton polygon of the quadratic-exponent power series `∑ a^(n²) Xⁿ`

Let `R` be a ring equipped with a real additive valuation `v : AddValuation R (WithTop ℝ)`, and
let `a : R` have finite nonnegative valuation `v a = c ≥ 0`. Because `n ↦ c * n ^ 2` is convex,
the coefficient heights of the formal power series `∑ a^(n²) Xⁿ` already coincide with their lower
convex envelope. Its Newton polygon is therefore `n ↦ c * n ^ 2`, every index `n : ℕ` is a finite
unit edge, and the `n`-th unit slope is `c * (2 * n + 1)`. When `c > 0`, these slopes are strictly
increasing, so each slope `c * (2 * n + 1)` has multiplicity `1` and every other real number has
multiplicity `0`.

Over a normed ring with `‖a‖ < 1` (for instance a normed division ring with
`‖x‖ = b ^ (-(v x).untop₀)` for `b > 1` and `x ≠ 0` when `c > 0`), `PowerSeries.isEntire_mk_pow_sq`
shows that `∑ a^(n²) Xⁿ` is entire, giving the classical nonpolynomial entire series whose Newton
polygon has infinitely many slopes of multiplicity `1` (in particular `∑ p^(n²) Xⁿ` over `ℚ_[p]`
and `ℂ_[p]`).

## Main results

* `PowerSeries.newtonPolygon_mk_pow_sq`: the Newton polygon of `∑ a^(n²) Xⁿ` is `n ↦ c * n ^ 2`.
* `PowerSeries.finiteEdges_newtonPolygon_mk_pow_sq`: every index is a finite unit edge.
* `PowerSeries.unitSlope_newtonPolygon_mk_pow_sq`: the `n`-th unit slope is `c * (2 * n + 1)`.
* `PowerSeries.newtonSlopeMultiplicity_mk_pow_sq_mul`: when `c > 0`, each slope
  `c * (2 * n + 1)` has multiplicity `1`.
* `PowerSeries.newtonSlopeMultiplicity_mk_pow_sq_eq_zero`: every real number outside
  `{c * (2 * n + 1) | n : ℕ}` has multiplicity `0`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

namespace PowerSeries

open TauCeti

section QuadraticPowerSeries

variable {R : Type*} [Ring R] {v : AddValuation R (WithTop ℝ)} {a : R} {c : ℝ}

/-- When `v a = c ≥ 0`, the quadratic-exponent power series `∑ a^(n²) Xⁿ` has convex coefficient
heights `n ↦ c * n ^ 2`, so its Newton polygon equals `n ↦ c * n ^ 2`. -/
theorem newtonPolygon_mk_pow_sq (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ)) :
    (mk fun n ↦ a ^ (n ^ 2)).newtonPolygon v =
      fun n : ℕ ↦ ((c * (n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hcoeff : (fun n : ℕ ↦ v (coeff n (mk fun k ↦ a ^ (k ^ 2)))) =
      fun n : ℕ ↦ ((c * (n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
    ext n
    rw [coeff_mk, AddValuation.map_pow, ha, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_pow,
      mul_comm]
  have hconv : IsConvexSeq (fun n : ℕ ↦ ((c * (n : ℝ) ^ 2 : ℝ) : WithTop ℝ)) := by
    refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun _ _ _ _ _ _ ↦ WithTop.coe_ne_top⟩,
      fun n _ _ ↦ ?_⟩
    simp only [WithTop.untop₀_coe, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    nlinarith
  rw [newtonPolygon_def, hcoeff, hconv.lowerConvexEnvelope_eq]

/-- When `v a = c ≥ 0`, every index is a finite unit edge of the Newton polygon of
`∑ a^(n²) Xⁿ`. -/
theorem finiteEdges_newtonPolygon_mk_pow_sq (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ)) :
    finiteEdges ((mk fun n ↦ a ^ (n ^ 2)).newtonPolygon v) = Set.univ := by
  ext n
  rw [mem_finiteEdges, newtonPolygon_mk_pow_sq hc ha]
  simp only [Set.mem_univ, iff_true]
  exact ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩

/-- When `v a = c ≥ 0`, the `n`-th unit slope of `∑ a^(n²) Xⁿ` is `c * (2 * n + 1)`. -/
theorem unitSlope_newtonPolygon_mk_pow_sq (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ)) (n : ℕ) :
    unitSlope ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) n = c * (2 * (n : ℝ) + 1) := by
  rw [unitSlope_def, newtonPolygon_mk_pow_sq hc ha]
  simp only [WithTop.untop₀_coe, Nat.cast_add, Nat.cast_one]
  ring

/-- When `v a = c > 0`, each slope `c * (2 * n + 1)` of `∑ a^(n²) Xⁿ` has multiplicity `1`. -/
theorem newtonSlopeMultiplicity_mk_pow_sq_mul (hc : 0 < c) (ha : v a = (c : WithTop ℝ)) (n : ℕ) :
    (mk fun k ↦ a ^ (k ^ 2)).newtonSlopeMultiplicity v (c * (2 * (n : ℝ) + 1)) = 1 := by
  have hset : {m | m ∈ finiteEdges ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) ∧
      unitSlope ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) m = c * (2 * (n : ℝ) + 1)} = {n} := by
    ext m
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, finiteEdges_newtonPolygon_mk_pow_sq hc.le ha,
      unitSlope_newtonPolygon_mk_pow_sq hc.le ha]
    simp only [Set.mem_univ, true_and, mul_eq_mul_left_iff, hc.ne', or_false]
    exact ⟨fun h ↦ by exact_mod_cast (by linarith : (m : ℝ) = n), fun h ↦ by subst h; rfl⟩
  rw [newtonSlopeMultiplicity_def, hset, Set.ncard_singleton]

/-- When `v a = c ≥ 0`, any real number outside `{c * (2 * n + 1) | n : ℕ}` has multiplicity `0` in
the Newton polygon of `∑ a^(n²) Xⁿ`. -/
theorem newtonSlopeMultiplicity_mk_pow_sq_eq_zero (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ))
    {σ : ℝ} (hσ : σ ∉ Set.range fun n : ℕ ↦ c * (2 * (n : ℝ) + 1)) :
    (mk fun k ↦ a ^ (k ^ 2)).newtonSlopeMultiplicity v σ = 0 := by
  rw [newtonSlopeMultiplicity_def]
  have hset : {m | m ∈ finiteEdges ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) ∧
      unitSlope ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) m = σ} = ∅ := by
    ext m
    rw [Set.mem_ofPred_eq, finiteEdges_newtonPolygon_mk_pow_sq hc ha,
      unitSlope_newtonPolygon_mk_pow_sq hc ha]
    simp only [Set.mem_univ, true_and, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ hσ ⟨m, h⟩
  rw [hset, Set.ncard_empty]

end QuadraticPowerSeries

end PowerSeries
