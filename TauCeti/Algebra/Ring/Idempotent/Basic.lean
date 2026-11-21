/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Componentwise arithmetic along an idempotent

An idempotent `e` of a commutative ring `R` splits it as `R ≅ e R × (1 - e) R`. Without reference
to the product decomposition, an element `e x + (1 - e) y` has `e`-component `e x` and
`(1 - e)`-component `(1 - e) y`, and since `e² = e` and `e (1 - e) = 0` such elements multiply
componentwise.

For an idempotent `p` of any ring, `2 p - 1` squares to `1`. For a star projection this is the
self-adjoint unitary `IsStarProjection.two_mul_sub_one_mem_unitary`. Conversely, for any element
`u` with `u * u = 1`, `1 + u` squares to `(1 + u) + (1 + u)`, and when `v` anticommutes with `u`
(`u * v + v * u = 0`), the sandwich `(1 + u) * (1 + v) * (1 + u)` also reduces to
`(1 + u) + (1 + u)`.

A finite family `(eᵢ)` with pairwise zero products summing to `1` consists of idempotents, and each
`eᵢ` extracts the `i`-th component of a combination of the family:
`eᵢ (∑ₖ cₖ eₖ) = (∑ₖ cₖ eₖ) eᵢ = cᵢ eᵢ`. For operators these are the spectral projections of a
finite spectral decomposition, and the identity says that each projection commutes with the
operator and restricts it to a scalar.

## Main results

* `IsIdempotentElem.mul_add_one_sub_mul`: elements of the form `e x + (1 - e) y` multiply
  componentwise.
* `IsIdempotentElem.two_mul_sub_one_mul_self`: `(2 p - 1) * (2 p - 1) = 1`.
* `TauCeti.one_add_mul_self_of_mul_self_eq_one`: if `u * u = 1`, then
  `(1 + u) * (1 + u) = (1 + u) + (1 + u)`.
* `TauCeti.one_add_mul_one_add_mul_one_add_of_mul_self_eq_one`: if `u * u = 1` and
  `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u)`.
* `TauCeti.isIdempotentElem_of_pairwise_mul_eq_zero_of_sum_eq_one`: a member of a finite family
  with pairwise zero products summing to `1` is idempotent.
* `TauCeti.mul_sum_smul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one`,
  `TauCeti.sum_smul_mul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one`: in such a family,
  `eᵢ (∑ₖ cₖ eₖ) = cᵢ eᵢ` and `(∑ₖ cₖ eₖ) eᵢ = cᵢ eᵢ`.
-/

public section

namespace IsIdempotentElem

section CommRing

variable {R : Type*} [CommRing R] {e : R}

/-- **Componentwise multiplication**: for an idempotent `e` of a commutative ring, elements of the
form `e x + (1 - e) y` multiply componentwise, as they would in `e R × (1 - e) R`. -/
theorem mul_add_one_sub_mul (he : IsIdempotentElem e) (x y x' y' : R) :
    (e * x + (1 - e) * y) * (e * x' + (1 - e) * y') = e * (x * x') + (1 - e) * (y * y') := by
  linear_combination (x * x' - x * y' - y * x' + y * y') * he.eq

end CommRing

section Ring

variable {R : Type*} [Ring R] {p : R}

/-- For an idempotent `p`, `2 p - 1` squares to `1`. -/
theorem two_mul_sub_one_mul_self (hp : IsIdempotentElem p) : (2 * p - 1) * (2 * p - 1) = 1 := by
  simp only [two_mul, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hp.eq]
  abel

end Ring

end IsIdempotentElem

namespace TauCeti

/-- If `u * u = 1`, then `1 + u` squares to `(1 + u) + (1 + u)` (so after dividing by `2`,
`2⁻¹ • (1 + u)` is idempotent). -/
theorem one_add_mul_self_of_mul_self_eq_one {R : Type*} [NonAssocSemiring R] {u : R}
    (hu : u * u = 1) :
    (1 + u) * (1 + u) = (1 + u) + (1 + u) := by
  rw [add_mul, one_mul, mul_add, mul_one, hu, add_comm u 1]

/-- If `u * u = 1` and `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u)` reduces to
`(1 + u) + (1 + u)`. -/
theorem one_add_mul_one_add_mul_one_add_of_mul_self_eq_one {R : Type*} [Semiring R] {u v : R}
    (hu : u * u = 1) (huv : u * v + v * u = 0) :
    (1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u) := by
  have hv : v + u * v * u = 0 :=
    calc
      v + u * v * u = 1 * v + u * (v * u) := by rw [one_mul, mul_assoc]
      _ = u * u * v + u * (v * u) := by rw [hu]
      _ = u * (u * v + v * u) := by rw [mul_assoc, mul_add]
      _ = 0 := by rw [huv, mul_zero]
  calc
    (1 + u) * (1 + v) * (1 + u)
        = ((1 + u) + (u + u * u)) + (u * v + v * u) + (v + u * v * u) := by
          simp only [add_mul, mul_add, one_mul, mul_one]
          ac_rfl
    _ = (1 + u) + (1 + u) := by
          rw [hu, huv, hv, add_zero, add_zero, add_comm u 1]

section Family

variable {ι K R : Type*} [Semiring R] {s : Finset ι} {e : ι → R} {i : ι}

/-- A member of a finite family with pairwise zero products summing to `1` is idempotent:
`eᵢ = eᵢ (∑ₖ eₖ) = eᵢ eᵢ`. -/
theorem isIdempotentElem_of_pairwise_mul_eq_zero_of_sum_eq_one
    (he : (s : Set ι).Pairwise fun i j ↦ e i * e j = 0) (h1 : ∑ k ∈ s, e k = 1) (hi : i ∈ s) :
    IsIdempotentElem (e i) := by
  calc e i * e i = ∑ k ∈ s, e i * e k :=
        (Finset.sum_eq_single_of_mem i hi fun k hk hki ↦ he hi hk hki.symm).symm
    _ = e i := by rw [← Finset.mul_sum, h1, mul_one]

variable [SMulZeroClass K R]

/-- In a finite family with pairwise zero products summing to `1`, multiplying a combination
`∑ₖ cₖ eₖ` on the left by `eᵢ` extracts its `i`-th term: `eᵢ (∑ₖ cₖ eₖ) = cᵢ eᵢ`. -/
theorem mul_sum_smul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one [SMulCommClass K R R]
    (he : (s : Set ι).Pairwise fun i j ↦ e i * e j = 0) (h1 : ∑ k ∈ s, e k = 1) (c : ι → K)
    (hi : i ∈ s) : e i * ∑ k ∈ s, c k • e k = c i • e i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi fun k hk hki ↦ by
    rw [mul_smul_comm, he hi hk hki.symm, smul_zero], mul_smul_comm,
    (isIdempotentElem_of_pairwise_mul_eq_zero_of_sum_eq_one he h1 hi).eq]

/-- In a finite family with pairwise zero products summing to `1`, multiplying a combination
`∑ₖ cₖ eₖ` on the right by `eᵢ` extracts its `i`-th term: `(∑ₖ cₖ eₖ) eᵢ = cᵢ eᵢ`. -/
theorem sum_smul_mul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one [IsScalarTower K R R]
    (he : (s : Set ι).Pairwise fun i j ↦ e i * e j = 0) (h1 : ∑ k ∈ s, e k = 1) (c : ι → K)
    (hi : i ∈ s) : (∑ k ∈ s, c k • e k) * e i = c i • e i := by
  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem i hi fun k hk hki ↦ by
    rw [smul_mul_assoc, he hk hi hki, smul_zero], smul_mul_assoc,
    (isIdempotentElem_of_pairwise_mul_eq_zero_of_sum_eq_one he h1 hi).eq]

end Family

end TauCeti
