/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The node polynomial of the Chebyshev points

The Chebyshev points of the first kind are `chebyshevRoot n i = cos ((2 i + 1) π / (2 n))`. For
`i < n` they are the `n` zeros of the Chebyshev polynomial `T n`, they are distinct, and they lie
in `[-1, 1]`. This file computes their node polynomial: the node polynomial
`∏ i ≤ n, (X - chebyshevRoot (n + 1) i)` of the `n + 1` points is `T (n + 1) / 2 ^ n`, so its
absolute value is at most `2⁻ⁿ` on `[-1, 1]`. With the interpolation error formula, this bounds
the error of polynomial interpolation at the Chebyshev points.

These points are not Mathlib's `Polynomial.Chebyshev.node n i = cos (i π / n)`, which are the
extreme points of `T n` on `[-1, 1]`.

## Main declarations

* `TauCeti.chebyshevRoot`: the Chebyshev points of the first kind.
* `TauCeti.eval_T_real_chebyshevRoot`: for `n ≠ 0`, every `chebyshevRoot n i` is a zero of
  `T n`.
* `TauCeti.injOn_chebyshevRoot`: the points `chebyshevRoot n i`, `i < n`, are distinct.
* `TauCeti.chebyshevRoot_mem_Icc`: every `chebyshevRoot n i` lies in `[-1, 1]`.
* `TauCeti.roots_T_real_eq_map_chebyshevRoot`: the roots of `T n` over `ℝ` are the points
  `chebyshevRoot n i`, `i < n`, each with multiplicity one.
* `TauCeti.nodal_chebyshevRoot`: the node polynomial of the `n + 1` points
  `chebyshevRoot (n + 1) i`, `i ≤ n`, is `T (n + 1) / 2 ^ n`.
* `TauCeti.abs_eval_nodal_chebyshevRoot_le`: on `[-1, 1]` this node polynomial has absolute
  value at most `2⁻ⁿ`.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial Polynomial.Chebyshev Real

/-- The Chebyshev points of the first kind: `chebyshevRoot n i = cos ((2 i + 1) π / (2 n))`.
For `i < n` these are the `n` zeros of `T n`. -/
def chebyshevRoot (n i : ℕ) : ℝ :=
  cos ((2 * i + 1) * π / (2 * n))

/-- The defining formula of `chebyshevRoot`. -/
theorem chebyshevRoot_def (n i : ℕ) :
    chebyshevRoot n i = cos ((2 * i + 1) * π / (2 * n)) :=
  (rfl)

/-- Every Chebyshev point lies in `[-1, 1]`. -/
theorem chebyshevRoot_mem_Icc (n i : ℕ) : chebyshevRoot n i ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [chebyshevRoot_def]
  exact cos_mem_Icc _

/-- The Chebyshev points `chebyshevRoot n i`, `i < n`, are distinct. -/
theorem injOn_chebyshevRoot (n : ℕ) : Set.InjOn (chebyshevRoot n) (Finset.range n) := by
  rw [funext (chebyshevRoot_def n)]
  exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)

/-- The roots of `T n` over `ℝ` are the Chebyshev points `chebyshevRoot n i`, `i < n`, each with
multiplicity one. -/
theorem roots_T_real_eq_map_chebyshevRoot (n : ℕ) :
    (T ℝ n).roots = (Multiset.range n).map (chebyshevRoot n) := by
  rw [roots_T_real, ← funext (chebyshevRoot_def n),
    Finset.image_val_of_injOn (injOn_chebyshevRoot n), Finset.range_val]

/-- For `n ≠ 0`, every Chebyshev point `chebyshevRoot n i` is a zero of `T n`. -/
theorem eval_T_real_chebyshevRoot {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    (T ℝ n).eval (chebyshevRoot n i) = 0 := by
  rw [chebyshevRoot_def, T_real_cos, cos_eq_zero_iff]
  refine ⟨i, ?_⟩
  field_simp
  push_cast
  ring

/-- The node polynomial of the `n + 1` Chebyshev points `chebyshevRoot (n + 1) i`, `i ≤ n`, is
`T (n + 1) / 2 ^ n`. -/
theorem nodal_chebyshevRoot (n : ℕ) :
    Lagrange.nodal (Finset.range (n + 1)) (chebyshevRoot (n + 1)) =
      C ((2 : ℝ) ^ n)⁻¹ * T ℝ ((n : ℤ) + 1) := by
  have hcard : Multiset.card (T ℝ (n + 1 : ℕ)).roots = (T ℝ (n + 1 : ℕ)).natDegree := by
    rw [roots_T_real_eq_map_chebyshevRoot, natDegree_T, Int.natAbs_natCast, Multiset.card_map,
      Multiset.card_range]
  have key := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [roots_T_real_eq_map_chebyshevRoot, leadingCoeff_T, Int.natAbs_natCast,
    Nat.add_sub_cancel] at key
  have hnodal : Lagrange.nodal (Finset.range (n + 1)) (chebyshevRoot (n + 1)) =
      (((Multiset.range (n + 1)).map (chebyshevRoot (n + 1))).map fun a => X - C a).prod := by
    simp [Lagrange.nodal_eq, ← Finset.prod_map_val]
  rw [hnodal, ← Nat.cast_succ, ← key, ← mul_assoc,
    ← Polynomial.C_mul, inv_mul_cancel₀ (by positivity), C_1, one_mul]

/-- On `[-1, 1]` the node polynomial of the `n + 1` Chebyshev points `chebyshevRoot (n + 1) i`,
`i ≤ n`, has absolute value at most `2⁻ⁿ`. -/
theorem abs_eval_nodal_chebyshevRoot_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Lagrange.nodal (Finset.range (n + 1)) (chebyshevRoot (n + 1))).eval x| ≤
      ((2 : ℝ) ^ n)⁻¹ := by
  rw [nodal_chebyshevRoot, eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (abs_eval_T_real_le_one _ (abs_le.mpr hx))

end TauCeti
