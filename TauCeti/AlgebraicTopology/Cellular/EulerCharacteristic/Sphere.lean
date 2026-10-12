/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Sphere

/-!
# The Euler characteristic of a sphere

The unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space has Euler characteristic
`1 + (-1)ⁿ`: its minimal CW structure (`TauCeti.sphereCWComplex`) has one cell in dimension `0`
and one in dimension `n`.  In particular `χ(S⁰) = 2`, and the Euler characteristic of a sphere is
`2` in even dimensions and `0` in odd ones.

* `TauCeti.cwEulerChar_sphereCWComplex`: the alternating cell count of the CW structure on `Sⁿ`.
* `TauCeti.eulerChar_sphere`: `χ(Sⁿ) = 1 + (-1)ⁿ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Metric Module Topology

universe u

namespace TauCeti

/-- The CW structure on the unit sphere `Sⁿ` of `EuclideanSpace ℝ ι`, with one cell in dimension
`0` and one in dimension `n`, has alternating cell count `1 + (-1)ⁿ`. -/
theorem cwEulerChar_sphereCWComplex {ι : Type u} [Fintype ι] {n : ℕ}
    (h : Fintype.card ι = n + 1) :
    letI := sphereCWComplex h
    cwEulerChar (sphere (0 : EuclideanSpace ℝ ι) 1) = 1 + (-1) ^ n := by
  let _ := sphereCWComplex h
  have hfin (a : ℕ) (b : ℤ) : (Function.support fun m : ℕ ↦ if m = a then b else 0).Finite :=
    (Set.finite_singleton a).subset fun m hm ↦ by_contra fun hma ↦ hm (ite_eq_right hma)
  rw [cwEulerChar_def]
  calc
    _ = ∑ᶠ m : ℕ, ((if m = 0 then 1 else 0) + if m = n then (-1 : ℤ) ^ n else 0) :=
      finsum_congr fun m ↦ by
        rw [nat_card_cell_sphereCWComplex h]
        split_ifs <;> simp_all
    _ = 1 + (-1) ^ n := by
      rw [finsum_add_distrib (hfin 0 1) (hfin n _), finsum_eq_single _ 0 fun m hm ↦ ite_eq_right hm,
        finsum_eq_single _ n fun m hm ↦ ite_eq_right hm]
      simp

/-- **The Euler characteristic of a sphere.**  The unit sphere of an `(n + 1)`-dimensional real
normed space has Euler characteristic `1 + (-1)ⁿ`. -/
theorem eulerChar_sphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ E = n + 1) :
    eulerChar (sphere (0 : E) 1) = 1 + (-1) ^ n := by
  have h : Fintype.card (ULift.{u} (Fin (n + 1))) = n + 1 := by simp
  let _ := sphereCWComplex h
  have := finite_sphereCWComplex h
  rw [eulerChar_eq_cwEulerChar (sphereHomeomorphOfFinrankEq
      (F := EuclideanSpace ℝ (ULift.{u} (Fin (n + 1)))) (by simp [hn])).toHomotopyEquiv,
    cwEulerChar_sphereCWComplex h]

end TauCeti
