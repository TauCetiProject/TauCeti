/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.RealProjective

/-!
# The Euler characteristic of real projective space

Real projective space `RPⁿ` has Euler characteristic `1` for even `n` and `0` for odd `n`: its CW
structure (`TauCeti.RealProjectiveSpace.cwComplex`) has one cell in each dimension `0, 1, …, n`, so
the alternating cell count is `1 - 1 + 1 - ⋯ ± 1`.

* `TauCeti.RealProjectiveSpace.cwEulerChar_cwComplex`: the alternating cell count of the CW
  structure on `RPⁿ`.
* `TauCeti.eulerChar_realProjectiveSpace`: `χ(RPⁿ)` is `1` for even `n` and `0` for odd `n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44, and Example 0.4.
-/

public section

open Set Topology.RelCWComplex

namespace TauCeti

namespace RealProjectiveSpace

variable {n : ℕ}

/-- The CW structure on `RPⁿ`, with one cell in each dimension `m ≤ n`, has alternating cell count
`1` for even `n` and `0` for odd `n`. -/
theorem cwEulerChar_cwComplex :
    letI := cwComplex n
    cwEulerChar (univ : Set (RealProjectiveSpace n)) = if Even n then 1 else 0 := by
  let := cwComplex n
  have := finite_cwComplex (n := n)
  rw [cwEulerChar_eq_sum_range (C := (univ : Set (RealProjectiveSpace n))) (N := n + 1)
      fun m hm ↦ ⟨fun c ↦ by have := le_of_cell_cwComplex c; omega⟩,
    Finset.sum_congr rfl fun m hm ↦ show _ = (-1 : ℤ) ^ m by
      simp [nat_card_cell_cwComplex, Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)],
    neg_one_geom_sum]
  simp [Nat.even_add_one, -Nat.not_even_iff_odd]

end RealProjectiveSpace

open RealProjectiveSpace in
/-- **The Euler characteristic of real projective space.** `χ(RPⁿ)` is `1` for even `n` and `0`
for odd `n`. -/
@[simp]
theorem eulerChar_realProjectiveSpace (n : ℕ) :
    eulerChar (RealProjectiveSpace n) = if Even n then 1 else 0 := by
  let := cwComplex n
  have := finite_cwComplex (n := n)
  rw [eulerChar_eq_cwEulerChar (Homeomorph.Set.univ _).symm.toHomotopyEquiv,
    cwEulerChar_cwComplex]

end TauCeti
