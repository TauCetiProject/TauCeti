/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Face.Basic
public import TauCeti.LowDimTopology.Plumbing.SpinC
import TauCeti.LowDimTopology.Plumbing.Weight.Translation

/-!
# Translation invariance of plumbing-lattice cube weights

Shifting a characteristic covector `k` by `2 * A m`, for the intersection matrix `A` and a lattice
point `m`, translates Némethi's weight function by `m` up to a constant,
`χ_{k + 2 A m}(y) = χ_k(y + m) - χ_k(m)`
(`TauCeti.PlumbingGraph.characteristicWeight_addTwoMulVec_eq_sub`).
Taking maxima over the vertices of a cube, the same holds for the cube weights, and the constant
cancels in the face exponents, which are differences of cube weights. So the cube based at `x`
for `k + 2 A m` carries the same face exponents as the cube based at `x + m` for `k`.

## Main results

* `TauCeti.PlumbingGraph.characteristicCubeWeight_addTwoMulVec_eq_sub`: translation invariance
  of the cube weights up to the constant `χ_k(m)`.
* `TauCeti.PlumbingGraph.characteristicLowerFaceExponent_addTwoMulVec`,
  `TauCeti.PlumbingGraph.characteristicUpperFaceExponent_addTwoMulVec`: translation invariance of
  the face exponents.

## References

* A. Némethi, *Lattice cohomology of normal surface singularities*,
  [arXiv:0709.0841](https://arxiv.org/abs/0709.0841), §3 (the weight function and the cube
  weights).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- Shifting a characteristic covector by `2 A m` translates the cube weights by `m`, up to the
constant `χ_k(m)`: the cube based at `x` for `k + 2 A m` has the weight of the cube based at
`x + m` for `k`, minus `χ_k(m)`. -/
theorem characteristicCubeWeight_addTwoMulVec_eq_sub (k : P.characteristicVectors)
    (m x : V → ℤ) (S : Finset V) :
    P.characteristicCubeWeight (P.addTwoMulVec k m) x S =
      P.characteristicCubeWeight k (x + m) S - P.characteristicWeight k m := by
  refine le_antisymm (P.characteristicCubeWeight_le _ fun y hy => ?_) ?_
  · rw [characteristicWeight_addTwoMulVec_eq_sub, sub_le_sub_iff_right]
    exact P.characteristicWeight_le_characteristicCubeWeight k
      (add_mem_cubeVertices_add_iff.mpr hy)
  · obtain ⟨y, hy, hmax⟩ := P.exists_characteristicWeight_eq_characteristicCubeWeight k (x + m) S
    have hy' : y - m ∈ cubeVertices x S := by
      rw [← add_mem_cubeVertices_add_iff (m := m), sub_add_cancel]
      exact hy
    have h := P.characteristicWeight_le_characteristicCubeWeight (P.addTwoMulVec k m) hy'
    rw [characteristicWeight_addTwoMulVec_eq_sub, sub_add_cancel] at h
    linarith

/-- The lower-face exponent is invariant under the translation of
`characteristicCubeWeight_addTwoMulVec_eq_sub`. -/
theorem characteristicLowerFaceExponent_addTwoMulVec (k : P.characteristicVectors)
    (m x : V → ℤ) (S : Finset V) (v : V) :
    P.characteristicLowerFaceExponent (P.addTwoMulVec k m) x S v =
      P.characteristicLowerFaceExponent k (x + m) S v := by
  rw [← Nat.cast_inj (R := ℤ), characteristicLowerFaceExponent_natCast,
    characteristicLowerFaceExponent_natCast, characteristicCubeWeight_addTwoMulVec_eq_sub,
    characteristicCubeWeight_addTwoMulVec_eq_sub, sub_sub_sub_cancel_right]

/-- The upper-face exponent is invariant under the translation of
`characteristicCubeWeight_addTwoMulVec_eq_sub`. -/
theorem characteristicUpperFaceExponent_addTwoMulVec (k : P.characteristicVectors)
    (m x : V → ℤ) {S : Finset V} {v : V} (hv : v ∈ S) :
    P.characteristicUpperFaceExponent (P.addTwoMulVec k m) x S hv =
      P.characteristicUpperFaceExponent k (x + m) S hv := by
  rw [← Nat.cast_inj (R := ℤ), characteristicUpperFaceExponent_natCast,
    characteristicUpperFaceExponent_natCast, characteristicCubeWeight_addTwoMulVec_eq_sub,
    characteristicCubeWeight_addTwoMulVec_eq_sub, sub_sub_sub_cancel_right, add_right_comm]

end PlumbingGraph

end TauCeti
