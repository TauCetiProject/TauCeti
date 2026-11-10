/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinear maps in coordinates

The value of a multilinear map `f` on arguments `m i` in a module with a finite basis `b` is the
sum, over all choices `s` of one basis index for each argument, of the products of the coordinates
`b.repr (m i) (s i)` times the value of `f` on the basis vectors `b (s i)`
(`MultilinearMap.apply_eq_sum_prod_repr_smul`). This expresses `f` through finitely many scalar
coefficients, which is how pairings of multilinear maps with families of vectors reduce to scalar
pairings.
-/

public section

namespace MultilinearMap

variable {R ι κ M N : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- **Multilinear maps in coordinates.** For a finite basis `b`,
`f m = ∑ s, (∏ i, b.repr (m i) (s i)) • f (fun i ↦ b (s i))`. -/
theorem apply_eq_sum_prod_repr_smul (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (b : Module.Basis κ R M) (m : ι → M) :
    f m = ∑ s : ι → κ, (∏ i, b.repr (m i) (s i)) • f fun i ↦ b (s i) := by
  conv_lhs => rw [show m = fun i ↦ ∑ j, b.repr (m i) j • b j from
    funext fun i ↦ (b.sum_repr (m i)).symm]
  rw [f.map_sum]
  simp_rw [f.map_smul_univ]

end MultilinearMap
