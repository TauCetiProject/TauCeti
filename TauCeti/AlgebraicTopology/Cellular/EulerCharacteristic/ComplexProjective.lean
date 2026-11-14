/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.ComplexProjective

/-!
# The Euler characteristic of complex projective space

Complex projective space `CPⁿ` has Euler characteristic `n + 1`: its CW structure
(`TauCeti.ComplexProjectiveSpace.cwComplex`) has one cell in each even dimension `0, 2, …, 2n` and
none in odd dimensions, so every cell counts with sign `+1`.

* `TauCeti.ComplexProjectiveSpace.cwEulerChar_cwComplex`: the alternating cell count of the CW
  structure on `CPⁿ`.
* `TauCeti.eulerChar_complexProjectiveSpace`: `χ(CPⁿ) = n + 1`.
* `TauCeti.eulerChar_projectivization_complex`: `χ(ℙ ℂ V) = dim V`, transported along the
  homeomorphism `CPⁿ ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ)`
  (`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`). In particular
  `χ(ℙ ℂ (Fin (n + 1) → ℂ)) = n + 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44, and Example 0.6.
-/

public section

open Set Topology.RelCWComplex

namespace TauCeti

namespace ComplexProjectiveSpace

variable {n : ℕ}

/-- The CW structure on `CPⁿ`, with one cell in each even dimension `m ≤ 2n`, has alternating cell
count `n + 1`. -/
theorem cwEulerChar_cwComplex :
    letI := cwComplex n
    cwEulerChar (univ : Set (ComplexProjectiveSpace n)) = n + 1 := by
  let := cwComplex n
  have := finite_cwComplex (n := n)
  have hEven (N : ℕ) :
      ∑ m ∈ Finset.range (2 * N + 1), (if Even m then (1 : ℤ) else 0) = N + 1 := by
    induction N with
    | zero => rw [Finset.sum_range_one]; simp
    | succ N ih =>
      have hN : 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 := by ring
      rw [hN, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp [Nat.even_add_one, parity_simps]
  rw [cwEulerChar_eq_sum_range (C := (univ : Set (ComplexProjectiveSpace n))) (N := 2 * n + 1)
      fun m hm ↦
      (Nat.card_eq_zero.1 (by rw [nat_card_cell_cwComplex, ite_eq_right (by omega)])).resolve_right
        (not_infinite_iff_finite.2 (FiniteType.finite_cell m)), ← hEven n]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm : m ≤ 2 * n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [nat_card_cell_cwComplex]
  by_cases he : Even m
  · simp [he, hm, he.neg_one_pow]
  · simp [he]

end ComplexProjectiveSpace

open ComplexProjectiveSpace in
/-- **The Euler characteristic of complex projective space.** `χ(CPⁿ) = n + 1`. -/
theorem eulerChar_complexProjectiveSpace (n : ℕ) :
    eulerChar (ComplexProjectiveSpace n) = n + 1 := by
  let := cwComplex n
  have := finite_cwComplex (n := n)
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ _).symm.toHomotopyEquiv,
    cwEulerChar_cwComplex]

open scoped LinearAlgebra.Projectivization in
/-- **The Euler characteristic of complex projective space** on the projectivization carrier:
`χ(ℙ ℂ V) = dim V` for a finite-dimensional Hausdorff complex topological vector space `V`. For
`V = Fin (n + 1) → ℂ` this is `n + 1`; for `V = 0` the projectivization is empty. -/
@[simp]
theorem eulerChar_projectivization_complex {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    [T2Space V] : eulerChar (ℙ ℂ V) = Module.finrank ℂ V := by
  cases h : Module.finrank ℂ V with
  | zero =>
    have := Module.finrank_zero_iff.1 h
    simp [eulerChar_of_discreteTopology]
  | succ n =>
    rw [← ((ComplexProjectiveSpace.homeomorphProjectivization n).trans
      (ContinuousLinearEquiv.ofFinrankEq (E := Fin (n + 1) → ℂ) (F := V)
        (by simp [h])).mapProjectivization).eulerChar_eq,
      eulerChar_complexProjectiveSpace, Nat.cast_succ]

end TauCeti
