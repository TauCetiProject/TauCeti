/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.InvariantFactor
public import TauCeti.NumberTheory.NewtonPolygon.Hodge
import Mathlib.Algebra.BigOperators.WithTop

/-!
# The Hodge polygon of a lattice endomorphism lies below its Newton polygon

Let `A` be an `n × n` matrix over a commutative ring `R` with an additive valuation `v` that is
nonnegative on `R`, for instance a full-rank endomorphism of the lattice `Rⁿ` over a discrete
valuation ring. Let `L * A * Q = diagonal s` be a Smith normal form: `L`, `Q` have unit
determinant and the invariant factors form a divisibility chain `s₀ ∣ s₁ ∣ ⋯ ∣ sₙ₋₁`. The
*Hodge polygon* of `A` is the convex polygon starting at `(0, 0)` with the nondecreasing slopes
`v s₀ ≤ v s₁ ≤ ⋯ ≤ v sₙ₋₁`.

The Hodge polygon lies below the Newton polygon of the Fredholm determinant
`det (1 - X A) = Matrix.charpolyRev A`, and both end at height `v (det A)` at `n`. The proof
bounds every principal `k × k` minor of `A` by the least valuation `v s₀ + ⋯ + v sₖ₋₁` of a
`k × k` minor (`Matrix.prefixSum_le_valuation_principalMinor_of_mul_mul_eq_diagonal`), and then
applies the principal-minor Hodge bound
`Matrix.heights_le_newtonPolygon_charpolyRev_of_principalMinor`. This is the Newton-above-Hodge
theorem for the Fredholm convention, whose polygons start at the origin.

The Hodge polygon depends on the matrix and not only on its Fredholm determinant: with `v p = 1`,
the matrices `[[p, 1], [0, p]]` and `diag(p, p)` have the same Fredholm determinant `(1 - p X) ^ 2`,
with Newton slopes `(1, 1)`, but Hodge slopes `(0, 2)` and `(1, 1)` respectively.

## Main results

* `Matrix.heights_le_newtonPolygon_charpolyRev_of_mul_mul_eq_diagonal`: slope data below the
  partial sums of the valuations of the invariant factors lies below the Newton polygon of
  `det (1 - X A)`.
* `Matrix.prefixSum_le_newtonPolygon_charpolyRev_of_mul_mul_eq_diagonal`: when `det A` has finite
  valuation, the Hodge polygon itself lies below the Newton polygon.
* `Matrix.newtonPolygon_charpolyRev_apply_card_of_mul_mul_eq_diagonal`: the two polygons have the
  same right endpoint `∑ i, v sᵢ`.

## References

* K. S. Kedlaya, [*A little p-adic numerical analysis*](https://kskedlaya.org/18.787/numerical.pdf),
  MIT 18.787 notes (2007), §3, Theorem 16.
-/

public section

open Polynomial TauCeti

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ} {A L Q : Matrix (Fin n) (Fin n) R} {s : Fin n → R}
  {v : AddValuation R (WithTop ℝ)}

/-- **Newton above Hodge.** Let `L * A * Q = diagonal s` be a Smith normal form of `A` and `v` a
valuation which is nonnegative on the whole ring. Finite slope data starting at `0`, of length at
least `n`, whose heights at `k ≤ n` are at most `v s₀ + ⋯ + v sₖ₋₁`, lies below the Newton
polygon of `det (1 - X A)`. -/
theorem heights_le_newtonPolygon_charpolyRev_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (hs : ∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j)
    (h : L * A * Q = diagonal s) {d : FiniteSlopeData ℝ} (hstart : d.start = 0)
    (hlength : n ≤ d.length)
    (hd : ∀ k ≤ n, ((d.initialHeight + prefixSum k d.slope : ℝ) : WithTop ℝ) ≤
      prefixSum k fun i ↦ v (s i)) :
    d.heights ≤ A.charpolyRev.newtonPolygon v :=
  heights_le_newtonPolygon_charpolyRev_of_principalMinor hstart (by simpa using hlength)
    fun t ↦ (hd _ (t.card_le_univ.trans_eq (Fintype.card_fin n))).trans
      (prefixSum_le_valuation_principalMinor_of_mul_mul_eq_diagonal hv hL hQ hs h t)

/-- **The Hodge polygon lies below the Newton polygon.** Let `L * A * Q = diagonal s` be a Smith
normal form of `A`, `v` a valuation which is nonnegative on the whole ring, and suppose that
`det A` has finite valuation. For every `k ≤ n`, the Newton polygon of `det (1 - X A)` at `k` is
at least `v s₀ + ⋯ + v sₖ₋₁`. -/
theorem prefixSum_le_newtonPolygon_charpolyRev_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (hs : ∀ ⦃i j : Fin n⦄, i ≤ j → s i ∣ s j)
    (h : L * A * Q = diagonal s) (hA : v A.det ≠ ⊤) {k : ℕ} (hk : k ≤ n) :
    (prefixSum k fun i ↦ v (s i)) ≤ A.charpolyRev.newtonPolygon v k := by
  -- the invariant factors have finite valuations, the real slopes of the Hodge polygon
  have hfin (i : Fin n) : v (s i) ≠ ⊤ := by
    rw [valuation_det_eq_sum_of_mul_mul_eq_diagonal hv hL hQ h, Ne, WithTop.sum_eq_top] at hA
    exact fun hi ↦ hA ⟨i, Finset.mem_univ _, hi⟩
  set w : Fin n → ℝ := fun i ↦ (v (s i)).untop (hfin i)
  have hw : (fun i ↦ v (s i)) = fun i ↦ ((w i : ℝ) : WithTop ℝ) :=
    funext fun i ↦ (WithTop.coe_untop _ (hfin i)).symm
  have hmono : Monotone w := fun i j hij ↦ WithTop.coe_le_coe.mp <| by
    simpa only [w, WithTop.coe_untop] using AddValuation.map_le_map_of_dvd hv (hs hij)
  have hcoe (k : ℕ) : (prefixSum k fun i ↦ v (s i)) = ((prefixSum k w : ℝ) : WithTop ℝ) := by
    rw [hw, prefixSum_def, prefixSum_def, WithTop.coe_sum]
  have hle := heights_le_newtonPolygon_charpolyRev_of_mul_mul_eq_diagonal hv hL hQ hs h
    (d := ⟨0, 0, n, w, hmono⟩) rfl le_rfl fun k _ ↦ by simp [hcoe]
  simpa [FiniteSlopeData.heights_def, hk, hcoe] using hle k

/-- **The right endpoints agree.** For a Smith normal form `L * A * Q = diagonal s` and a valuation
which is nonnegative on the whole ring, the Newton polygon of `det (1 - X A)` has height
`v s₀ + ⋯ + v sₙ₋₁` at `n`, the endpoint of the Hodge polygon. -/
theorem newtonPolygon_charpolyRev_apply_card_of_mul_mul_eq_diagonal (hv : ∀ x, 0 ≤ v x)
    (hL : IsUnit L.det) (hQ : IsUnit Q.det) (h : L * A * Q = diagonal s) :
    A.charpolyRev.newtonPolygon v n = ∑ i, v (s i) := by
  rw [← valuation_det_eq_sum_of_mul_mul_eq_diagonal hv hL hQ h,
    ← newtonPolygon_charpolyRev_apply_card, Fintype.card_fin]

/-! ### Example -/

/-- A Smith normal form of `[[p, 1], [0, p]]`: its invariant factors are `1` and `-p ^ 2`, so its
Hodge slopes are `0` and `2 v p`. -/
example (p : R) :
    !![1, 0; -p, 1] * !![p, 1; 0, p] * !![0, 1; 1, -p] = diagonal ![1, -p ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq]

/-- The Fredholm determinant of `[[p, 1], [0, p]]` is `(1 - p X) ^ 2`, the same as that of
`diag(p, p)`, whose Hodge slopes are `v p` and `v p`. -/
example (p : R) : (!![p, 1; 0, p] : Matrix (Fin 2) (Fin 2) R).charpolyRev = (1 - C p * X) ^ 2 := by
  simp [charpolyRev, det_fin_two, one_fin_two]
  ring

end Matrix
