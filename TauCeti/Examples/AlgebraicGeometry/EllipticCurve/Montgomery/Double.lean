/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of Montgomery doubling

These computations distinguish the `(A + 2)/4` convention from `(A - 2)/4`, exhibit
factor-detecting arithmetic over a composite residue ring, and show why correctness is stated
on nonsingular native points rather than arbitrary pairs. The final examples use the
correctness theorem on singular models and in characteristic three.
-/

namespace TauCeti.Montgomery

-- For A = 0, the scaled constants are N = 2 and D = 4.
example : double (2 : ℚ) 4 ⟨2, 1⟩ = ⟨36, 160⟩ := by
  ext <;> norm_num [double_x, double_z]

-- The opposite convention changes the represented coordinate, not just the scaling.
example : (double (2 : ℚ) 4 ⟨2, 1⟩).cross (double (-2) 4 ⟨2, 1⟩) = -9216 := by
  norm_num [Pair.cross_def, double_x, double_z]

-- Over ZMod 35, the second field detects 5 but not 7.
example : double (2 : ZMod 35) 4 ⟨22, 1⟩ = ⟨21, 25⟩ := by
  ext <;> norm_num [double_x, double_z] <;> decide

-- The two reductions of the same computation have different geometric meanings:
-- infinity modulo 5, but the distinguished point of order two modulo 7.
example : double (2 : ZMod 5) 4 ⟨2, 1⟩ = ⟨1, 0⟩ := by
  ext <;> norm_num [double_x, double_z] <;> decide

example : double (2 : ZMod 7) 4 ⟨1, 1⟩ = ⟨0, 4⟩ := by
  ext <;> norm_num [double_x, double_z]
  decide

-- At the singular point of y² = x(x + 1)², the formula does output (0, 0).
example : double (1 : ℚ) 1 ⟨-1, 1⟩ = 0 := by
  ext <;> norm_num [double_x, double_z]

-- Nevertheless every native point of that singular model has nonzero double output.
example {K : Type*} [Field K] [DecidableEq K]
    (P : (model (2 : K) 1).toAffine.Point) :
    double 1 1 (coordinates 2 1 P) ≠ 0 :=
  (double_coordinates (by simp) (by simp) (by norm_num) P).1

-- Characteristic three requires no modification of the formula or its correctness theorem.
example (P : (model (0 : ZMod 3) 1).toAffine.Point) :
    double 2 4 (coordinates 0 1 P) ≠ 0 ∧
      (double 2 4 (coordinates 0 1 P)).cross (coordinates 0 1 (P + P)) = 0 :=
  double_coordinates (by decide) (by decide) (by decide) P

-- Even in characteristic two the scaled relation is sufficient on native points.
example (P : (model (0 : ZMod 2) 1).toAffine.Point) :
    double 1 1 (coordinates 0 1 P) ≠ 0 ∧
      (double 1 1 (coordinates 0 1 P)).cross (coordinates 0 1 (P + P)) = 0 :=
  double_coordinates (by decide) (by decide) (by decide) P

end TauCeti.Montgomery
