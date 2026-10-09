/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Range
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Product

/-!
# Multiplicativity of the Euler characteristic for products

The `n`-cells of the product `C ×ˢ D` of two finite CW complexes are the pairs of a `p`-cell of
`C` and a `q`-cell of `D` with `p + q = n` (`TauCeti.nat_card_cell_prod`).  Since
`(-1)ⁿ = (-1)ᵖ (-1)^q`, the alternating cell count of the product is the product of the
alternating cell counts (`TauCeti.cwEulerChar_prod`).  A product of spaces of finite CW type is
homotopy equivalent to the product of finite CW models of the factors, so the Euler
characteristic is multiplicative on spaces of finite CW type (`TauCeti.eulerChar_prod`).

## Main results

* `TauCeti.cwEulerChar_prod`: `χ(C ×ˢ D) = χ(C) · χ(D)` for finite CW complexes.
* `TauCeti.eulerChar_prod`: `χ(X × Y) = χ(X) · χ(Y)` for spaces of finite CW type.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44, and Chapter 0, products of CW complexes.
-/

public section

open Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Multiplicativity of the Euler characteristic** for finite CW complexes: the alternating cell
count of the product CW complex `C ×ˢ D` is the product of the alternating cell counts of `C` and
`D`. -/
theorem cwEulerChar_prod (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D]
    [RelCWComplex.Finite C] [RelCWComplex.Finite D] :
    cwEulerChar (C ×ˢ D) = cwEulerChar C * cwEulerChar D := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)).and
      ((FiniteDimensional.eventually_isEmpty_cell (C := D) (D := ∅)).and
        (FiniteDimensional.eventually_isEmpty_cell (C := C ×ˢ D) (D := ∅))))
  -- The alternating cell counts, indexed by the dimensions of the two factors.
  let f : ℕ × ℕ → ℤ := fun pq ↦
    (-1) ^ pq.1 * Nat.card (cell C pq.1) * ((-1) ^ pq.2 * Nat.card (cell D pq.2))
  have hf (p q : ℕ) (h : N ≤ p ∨ N ≤ q) : f (p, q) = 0 := by
    rcases h with h | h
    · have := (hN p h).1
      simp [f]
    · have := (hN q h).2.1
      simp [f]
  have hprod (n : ℕ) (hn : N + N ≤ n) : IsEmpty (cell (C ×ˢ D) n) :=
    (hN n (by omega)).2.2
  rw [cwEulerChar_eq_sum_range (C ×ˢ D) hprod, cwEulerChar_eq_sum_range C fun n hn ↦ (hN n hn).1,
    cwEulerChar_eq_sum_range D fun n hn ↦ (hN n hn).2.1, Finset.sum_mul_sum]
  calc
    _ = ∑ n ∈ Finset.range (N + N), ∑ pq ∈ Finset.antidiagonal n, f pq := by
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [nat_card_cell_prod, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun pq hpq ↦ ?_
      rw [← Finset.mem_antidiagonal.1 hpq]
      push_cast
      ring
    _ = _ := sum_range_add_antidiagonal_of_support N N f hf

/-- **Multiplicativity of the Euler characteristic** for spaces of finite CW type:
`χ(X × Y) = χ(X) · χ(Y)`. -/
theorem eulerChar_prod [hX : FiniteCWType X] [hY : FiniteCWType Y] :
    eulerChar (X × Y) = eulerChar X * eulerChar Y := by
  obtain ⟨X', _, _, C, _, _, ⟨e⟩⟩ := hX.exists_homotopyEquiv
  obtain ⟨Y', _, _, D, _, _, ⟨f⟩⟩ := hY.exists_homotopyEquiv
  rw [eulerChar_eq_cwEulerChar e, eulerChar_eq_cwEulerChar f,
    eulerChar_eq_cwEulerChar ((e.prodCongr f).trans (Homeomorph.Set.prod C D).symm.toHomotopyEquiv),
    cwEulerChar_prod]

end TauCeti
