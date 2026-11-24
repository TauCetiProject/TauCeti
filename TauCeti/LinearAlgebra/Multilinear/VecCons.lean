/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Tactic.FinCases

/-!
# Multilinear maps in two arguments on pairs `![a, b]`

Mathlib states the linearity of a multilinear map in one coordinate for tuples built with
`Function.update`, `Fin.cons` or `Fin.snoc` (`MultilinearMap.map_update_add`,
`MultilinearMap.cons_add`, `MultilinearMap.snoc_add`, and their `smul` versions). Multilinear
maps in two arguments, such as Hochschild `2`-cochains, are usually applied to pairs written
`![a, b]`, which `rw` and `simp` do not recognize as any of these. This file restates
`MultilinearMap.map_update_add` and `MultilinearMap.map_update_smul` for such pairs.

## Main results

* `MultilinearMap.apply_vecCons_add_left`, `MultilinearMap.apply_vecCons_add_right`: additivity
  in each argument.
* `MultilinearMap.apply_vecCons_smul_left`, `MultilinearMap.apply_vecCons_smul_right`: linearity
  in each argument.
-/

public section

namespace MultilinearMap

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] (f : (Fin 2 → M) →ₘₗ[R] N)

/-- A multilinear map in two arguments is additive in its first argument. -/
theorem apply_vecCons_add_left (a a' b : M) : f ![a + a', b] = f ![a, b] + f ![a', b] := by
  have e (c : M) : Function.update ![a, b] 0 c = ![c, b] := by
    ext i; fin_cases i <;> rfl
  simpa only [e] using f.map_update_add ![a, b] 0 a a'

/-- A multilinear map in two arguments is additive in its second argument. -/
theorem apply_vecCons_add_right (a b b' : M) : f ![a, b + b'] = f ![a, b] + f ![a, b'] := by
  have e (c : M) : Function.update ![a, b] 1 c = ![a, c] := by
    ext i; fin_cases i <;> rfl
  simpa only [e] using f.map_update_add ![a, b] 1 b b'

/-- A multilinear map in two arguments is linear in its first argument. -/
theorem apply_vecCons_smul_left (c : R) (a b : M) : f ![c • a, b] = c • f ![a, b] := by
  have e (d : M) : Function.update ![a, b] 0 d = ![d, b] := by
    ext i; fin_cases i <;> rfl
  simpa only [e, RingHom.id_apply] using f.map_update_smul ![a, b] 0 c a

/-- A multilinear map in two arguments is linear in its second argument. -/
theorem apply_vecCons_smul_right (c : R) (a b : M) : f ![a, c • b] = c • f ![a, b] := by
  have e (d : M) : Function.update ![a, b] 1 d = ![a, d] := by
    ext i; fin_cases i <;> rfl
  simpa only [e, RingHom.id_apply] using f.map_update_smul ![a, b] 1 c b

end MultilinearMap
