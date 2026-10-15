/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `pi_eq_sum_univ'`, the expansion of a vector of `ν → R` in the standard basis.
public import Mathlib.Algebra.BigOperators.Pi
-- `PiTensorProduct.tprod` and `MultilinearMap.map_update_sum`.
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Expanding two slots of a pure tensor in the standard basis

A pure tensor `⨂ₜ u` over a constant family `ν → R` is multilinear in its slots, so plugging a
vector into one slot and expanding that vector along the standard basis `Pi.single a 1` turns the
tensor into a sum (`MultilinearMap.map_update_sum`). Doing this at *two* distinct slots at once is
the bookkeeping recorded here: the pure tensor whose slots `i` and `j` carry `x` and `y` is the
double sum over the standard basis with coefficients the products `x a * y b` of the coordinates.
The two slots have to be distinct for the two `Function.update`s to be independent; that is where
`Function.update_comm` enters.

This is the shape that a diagonal expansion at two slots of a tensor power — a Brauer cup, say —
is read through when one wants its coefficients, so it is stated here rather than in any one
consumer.

## Main results

* `TauCeti.tprod_update_pair_expand`: a pure tensor whose slots `i` and `j` carry arbitrary vectors
  of `ν → R` is the standard-basis expansion of those two slots.
-/

public section

namespace TauCeti

/-- **The bilinear expansion at two slots**: a pure tensor over the constant family `ν → R` whose
slots `i` and `j` carry arbitrary vectors is the standard-basis expansion of those two slots, with
the product `x a * y b` of the two coordinates as the coefficient of the `(a, b)` term. -/
theorem tprod_update_pair_expand {ι ν R : Type*} [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    [CommSemiring R] {i j : ι} (hij : i ≠ j) (u : ι → (ν → R)) (x y : ν → R) :
    PiTensorProduct.tprod R (Function.update (Function.update u i x) j y) =
      ∑ a : ν, ∑ b : ν, (x a * y b) • PiTensorProduct.tprod R
        (Function.update (Function.update u i (Pi.single a (1 : R))) j (Pi.single b 1)) := by
  calc PiTensorProduct.tprod R (Function.update (Function.update u i x) j y)
      = PiTensorProduct.tprod R (Function.update (Function.update u i
          (∑ a : ν, x a • Pi.single a (1 : R))) j
            (∑ b : ν, y b • Pi.single b (1 : R))) := by
        rw [← pi_eq_sum_univ' x, ← pi_eq_sum_univ' y]
    _ = ∑ b : ν, ∑ a : ν, (x a * y b) • PiTensorProduct.tprod R
          (Function.update (Function.update u i (Pi.single a (1 : R))) j (Pi.single b 1)) := by
        rw [(PiTensorProduct.tprod R).map_update_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [(PiTensorProduct.tprod R).map_update_smul, Function.update_comm hij,
          (PiTensorProduct.tprod R).map_update_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [(PiTensorProduct.tprod R).map_update_smul, Function.update_comm (Ne.symm hij),
          smul_smul, mul_comm]
    _ = _ := Finset.sum_comm

end TauCeti
