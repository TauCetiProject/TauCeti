/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Integer coordinates on the lattice spanned by a basis

For a basis `b` of a module over a ring of characteristic zero, the lattice `span ℤ (range b)` is
in bijection with the integer coordinate vectors `n : ι → ℤ`, through `n ↦ ∑ i, n i • b i`. This
file packages that bijection, built from Mathlib's `Module.Basis.restrictScalars`, as a
`ℤ`-linear equivalence, so that sums over the lattice can be reindexed by `ι → ℤ`.

## Main definitions

* `Module.Basis.zspanEquiv`: the `ℤ`-linear equivalence `(ι → ℤ) ≃ₗ[ℤ] span ℤ (range b)`.

## Main statements

* `Module.Basis.coe_zspanEquiv_apply`: the lattice vector with coordinates `n` is
  `∑ i, n i • b i`.
* `Module.Basis.repr_zspanEquiv_apply`: its coordinates in the basis `b` are `n`.
* `Module.Basis.zspanEquiv_symm_apply`: the inverse sends a lattice vector to its coordinates in
  the basis `b`.
-/

public section

open Set Submodule

namespace Module.Basis

variable {ι R M : Type*} [Ring R] [Nontrivial R] [IsTorsionFree ℤ R] [AddCommGroup M]
  [Module R M] (b : Basis ι R M)

/-- The lattice `span ℤ (range b)` spanned by a basis `b`, indexed by the integer coordinate
vectors: the vector `n : ι → ℤ` corresponds to the lattice vector `∑ i, n i • b i`. -/
noncomputable def zspanEquiv [Finite ι] : (ι → ℤ) ≃ₗ[ℤ] span ℤ (range b) :=
  (b.restrictScalars ℤ).equivFun.symm

/-- The lattice vector `b.zspanEquiv n` has coordinates `n` in the basis `b`. -/
@[simp]
theorem repr_zspanEquiv_apply [Finite ι] (n : ι → ℤ) (i : ι) :
    b.repr (zspanEquiv b n) i = n i := by
  rw [← b.restrictScalars_repr_apply ℤ, zspanEquiv, ← Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply, eq_intCast]

/-- The inverse of `b.zspanEquiv` sends a lattice vector to its coordinates in the basis `b`. -/
@[simp]
theorem zspanEquiv_symm_apply [Finite ι] (v : span ℤ (range b)) (i : ι) :
    (b.zspanEquiv.symm v i : R) = b.repr v i := by
  obtain ⟨n, rfl⟩ := b.zspanEquiv.surjective v
  simp

variable [Fintype ι]

/-- The lattice vector with integer coordinates `n` is `∑ i, n i • b i`. -/
@[simp]
theorem coe_zspanEquiv_apply (n : ι → ℤ) : (b.zspanEquiv n : M) = ∑ i, n i • b i := by
  simp [zspanEquiv]

end Module.Basis
