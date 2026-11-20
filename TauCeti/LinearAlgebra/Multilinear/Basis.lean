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

The value of a multilinear map `f` on arguments `m i`, each in a module `M i` with a finite basis
`b i`, is the sum, over all choices `s` of one basis index for each argument, of the products of
the coordinates `(b i).repr (m i) (s i)` times the value of `f` on the basis vectors `b i (s i)`
(`MultilinearMap.apply_eq_sum_prod_repr_smul`). This expresses `f` through finitely many scalar
coefficients, which is how pairings of multilinear maps with families of vectors reduce to scalar
pairings.
-/

public section

namespace MultilinearMap

variable {R ι N : Type*} {κ M : ι → Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (κ i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N]
  [Module R N]

/-- **Multilinear maps in coordinates.** For finite bases `b i` of the modules `M i`,
`f m = ∑ s, (∏ i, (b i).repr (m i) (s i)) • f (fun i ↦ b i (s i))`. -/
theorem apply_eq_sum_prod_repr_smul (f : MultilinearMap (RingHom.id R) M N)
    (b : ∀ i, Module.Basis (κ i) R (M i)) (m : ∀ i, M i) :
    f m = ∑ s : ∀ i, κ i, (∏ i, (b i).repr (m i) (s i)) • f fun i ↦ b i (s i) := by
  conv_lhs => rw [← funext fun i ↦ (b i).sum_repr (m i)]
  rw [f.map_sum]
  simp_rw [f.map_smul_univ, RingHom.id_apply]

end MultilinearMap
