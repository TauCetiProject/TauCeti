/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Normalizing a tuple at a nonzero entry

Over a semifield, dividing the other entries of a tuple `b : Fin (n + 1) → k` by a nonzero entry
`b i` and reinserting `1` in position `i` gives `(b i)⁻¹ • b`. This is the normalization used by
the standard affine charts of projective space and by dehomogenization of polynomials.

## Main results

* `Fin.insertNth_one_div_eq_inv_smul`: reinserting `1` at a nonzero coordinate into the coordinate
  ratios recovers the tuple scaled by the inverse of that coordinate.
-/

public section

namespace Fin

/-- Reinserting one at a nonzero coordinate into the coordinate ratios recovers the
homogeneous coordinates scaled by the inverse of that coordinate. -/
theorem insertNth_one_div_eq_inv_smul {k : Type*} [Semifield k] {n : ℕ} (i : Fin (n + 1))
    (b : Fin (n + 1) → k) (hi : b i ≠ 0) :
    i.insertNth 1 (fun j ↦ b (i.succAbove j) / b i) = (b i)⁻¹ • b := by
  ext l
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) l <;> simp [hi, div_eq_mul_inv, mul_comm]

end Fin
