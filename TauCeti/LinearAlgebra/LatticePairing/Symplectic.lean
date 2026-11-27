/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.AdjointBaseChange
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Padic
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors

/-!
# Symplectic lattices with an order action

A symplectic `O`-lattice is a finite free abelian group with a left action of a ring with
involution `O` and a nondegenerate alternating pairing for which `b` is adjoint to `star b`.
We use the integral scalar coordinates of the pairing, identifying the Tate line `ℤ(1)` with
`ℤ` by its generator `2πi`.

The rational dual lattice is an `O`-submodule. The index of the original lattice in the dual
is the absolute Gram determinant of the integral pairing, and the completion at `p` is
self-dual exactly when `p` does not divide this index.

The extended order acts via `BialgebraModule.tensorPairAction`, and the rational dual uses
Mathlib's `LinearMap.BilinForm.dualSubmodule`. The lemmas `SymplecticOLattice.dualIndex_eq_prod_sq`
and `SymplecticOLattice.isSquare_dualIndex` describe the square index, and
`SymplecticOLattice.isSelfDualAt_iff_not_dvd_dualIndex` gives the local criterion.

## References

* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, thesis, §1.2.1
  and Definition 1.4.1.1, where the dual index contributes to the bad primes.
-/

public section

open scoped TensorProduct Padic
open Module

namespace TauCeti

/-- A symplectic lattice on a finite free abelian group `L` with an adjoint action of `O`.
The pairing can have nonunit Gram determinant. Nondegeneracy over `ℤ` is equivalent to
nondegeneracy over `ℚ` by injective localization. -/
@[ext]
structure SymplecticOLattice (O L : Type*) [Ring O] [StarRing O] [AddCommGroup L]
    [Module O L] [Module.Free ℤ L] [Module.Finite ℤ L] where
  /-- The integral alternating pairing, in scalar coordinates. -/
  form : LinearMap.BilinForm ℤ L
  /-- The pairing vanishes on the diagonal. -/
  isAlt : form.IsAlt
  /-- The pairing has zero radical. -/
  nondegenerate : form.Nondegenerate
  /-- The adjoint of the action of `b` is the action of `star b`. -/
  adjoint (b : O) (x y : L) : form (b • x) y = form x (star b • y)

namespace SymplecticOLattice

variable {O L : Type*} [Ring O] [StarRing O] [AddCommGroup L]
  [Module O L] [Module.Free ℤ L] [Module.Finite ℤ L]

variable (S : SymplecticOLattice O L)

/-- The rational pairing is nondegenerate. -/
theorem nondegenerate_rat : (S.form.baseChange ℚ).Nondegenerate :=
  S.nondegenerate.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)

section BaseChange

variable (A : Type*) [CommRing A]

attribute [local instance low] TensorProduct.rightModule

/-- The extended pairing is adjoint for the action of each element of the original order. -/
theorem baseChange_adjoint (b : O) (x y : A ⊗[ℤ] L) :
    S.form.baseChange A (b • x) y = S.form.baseChange A x (star b • y) :=
  S.form.baseChange_rightModule_adjoint b (S.adjoint b) x y

/-- With trivial star on the base ring, the entire scalar-extended order acts
by star-adjoints for the extended pairing. This holds over nonflat base rings as well. -/
theorem baseChange_tensor_adjoint [StarAddMonoid A] [TrivialStar A]
    (c : A ⊗[ℤ] O) (x y : A ⊗[ℤ] L) :
    let ρ := BialgebraModule.tensorPairAction ℤ A L
    S.form.baseChange A (ρ c x) y = S.form.baseChange A x (ρ (star c) y) :=
  S.form.baseChange_tensor_adjoint S.adjoint c x y

end BaseChange

section Dual

attribute [local instance low] TensorProduct.rightModule

/-- The order-linear embedding of the integral lattice into its rational span. -/
noncomputable def toRational : L →ₗ[O] ℚ ⊗[ℤ] L where
  __ := TensorProduct.mk ℤ ℚ L 1
  map_smul' b x := (TensorProduct.rightModule_smul_tmul b (1 : ℚ) x).symm

omit [StarRing O] [Module.Free ℤ L] [Module.Finite ℤ L] in
/-- The rational embedding sends a vector to its unit tensor. -/
@[simp]
theorem toRational_apply (x : L) :
    toRational (O := O) x = (1 : ℚ) ⊗ₜ[ℤ] x := (rfl)

omit [StarRing O] [Module.Free ℤ L] [Module.Finite ℤ L] in
/-- The unit-tensor map is injective on a flat integral module. -/
theorem toRational_injective [Module.Flat ℤ L] :
    Function.Injective (toRational (O := O) (L := L)) :=
  Module.Flat.tensorProduct_mk_injective ℤ L ℚ

/-- The rational dual lattice, with the order action supplied by star-adjointness. -/
noncomputable def dual : Submodule O (ℚ ⊗[ℤ] L) where
  __ := ((S.form.baseChange ℚ).dualSubmodule
    (LinearMap.range (TensorProduct.mk ℤ ℚ L 1))).toAddSubmonoid
  smul_mem' b x hx := by
    refine (LinearMap.BilinForm.mem_dualSubmodule _).2 fun y hy ↦ ?_
    obtain ⟨v, rfl⟩ := hy
    rw [TensorProduct.mk_apply, S.baseChange_adjoint, TensorProduct.rightModule_smul_tmul]
    exact (LinearMap.BilinForm.mem_dualSubmodule _).1 hx _ ⟨star b • v, rfl⟩

/-- Membership in the dual is integral pairing with the original lattice. -/
@[simp]
theorem mem_dual_iff {x : ℚ ⊗[ℤ] L} :
    x ∈ S.dual ↔ ∀ y : L, (S.form.baseChange ℚ) x (toRational (O := O) y) ∈
      (1 : Submodule ℤ ℚ) := by
  rw [dual]
  exact (LinearMap.BilinForm.mem_dualSubmodule _).trans
    ⟨fun h y ↦ h _ ⟨y, rfl⟩, fun h _ ⟨y, hy⟩ ↦ hy ▸ h y⟩

/-- Forgetting the order action recovers Mathlib's dual submodule. -/
theorem dual_restrictScalars :
    S.dual.restrictScalars ℤ = (S.form.baseChange ℚ).dualSubmodule
      (LinearMap.range (TensorProduct.mk ℤ ℚ L 1)) := (rfl)

/-- Integrality of the pairing embeds the original lattice in its dual. -/
theorem le_dual : LinearMap.range (toRational (O := O) (L := L)) ≤ S.dual :=
  S.form.range_mk_one_le_dualSubmodule

/-- The index of the integral lattice in its rational dual. -/
noncomputable def dualIndex : ℕ :=
  (LinearMap.range (toRational (O := O) (L := L))).toAddSubgroup.relIndex S.dual.toAddSubgroup

/-- The dual index is the relative index of the original lattice in its dual. -/
theorem dualIndex_def :
    S.dualIndex =
      (LinearMap.range (toRational (O := O) (L := L))).toAddSubgroup.relIndex
        S.dual.toAddSubgroup := (rfl)

/-- The order-stable dual spans the rational space and is a lattice over the integers. -/
instance instIsFullLatticeDual : (S.dual.restrictScalars ℤ).IsFullLattice ℚ := by
  rw [S.dual_restrictScalars]
  exact (S.form.baseChange ℚ).isFullLattice_dualSubmodule S.nondegenerate_rat
    (LinearMap.range (TensorProduct.mk ℤ ℚ L 1))

/-- The dual index is the absolute Gram determinant in any integral basis. -/
theorem dualIndex_eq_natAbs_det {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    S.dualIndex = (S.form.toMatrix b).det.natAbs :=
  S.form.relIndex_dualSubmodule_range_mk_one_eq_natAbs_det S.nondegenerate_rat b

/-- The rational dual contains the integral lattice with positive finite index. -/
theorem dualIndex_pos : 0 < S.dualIndex :=
  S.form.relIndex_dualSubmodule_range_mk_one_pos S.nondegenerate

/-- Index one characterizes self-duality in the rational span. -/
@[simp]
theorem dualIndex_eq_one_iff :
    S.dualIndex = 1 ↔ S.dual = LinearMap.range (toRational (O := O) (L := L)) := by
  rw [S.dualIndex_def, AddSubgroup.relIndex_eq_one, Submodule.toAddSubgroup_le, S.le_dual.ge_iff_eq]
  exact eq_comm

/-- In a symplectic basis with elementary divisors `d`, the dual index is the square of their
product. The formula also applies to the rank-zero lattice, with empty product one. -/
theorem dualIndex_eq_prod_sq {g : ℕ} {b : Basis (Fin g ⊕ Fin g) ℤ L} {d : Fin g → ℤ}
    (hb : S.form.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d)
      (-Matrix.diagonal d) 0) :
    S.dualIndex = (∏ i, (d i).natAbs) ^ 2 := by
  rw [S.dualIndex_eq_natAbs_det b,
    LinearMap.BilinForm.det_toMatrix_eq_prod_sq_of_toMatrix_eq_fromBlocks hb b,
    Int.natAbs_pow, Int.natAbs_prod]

/-- The dual index of a symplectic lattice is a square. -/
theorem isSquare_dualIndex : IsSquare S.dualIndex := by
  obtain ⟨g, b, d, _, _, hb⟩ :=
    S.isAlt.exists_basis_toMatrix_eq_fromBlocks_pos_of_nondegenerate S.nondegenerate
  exact ⟨∏ i, (d i).natAbs, by rw [S.dualIndex_eq_prod_sq hb, pow_two]⟩

end Dual

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The `p`-adic lattice is equal to its dual in its `ℚ_[p]`-span. -/
def IsSelfDualAt : Prop :=
  let M := ℤ_[p] ⊗[ℤ] L
  let N := LinearMap.range (TensorProduct.mk ℤ_[p] ℚ_[p] M 1)
  ((S.form.baseChange ℤ_[p]).baseChange ℚ_[p]).dualSubmodule N = N

/-- Self-duality at `p` means equality with the dual in the `ℚ_[p]`-span. -/
theorem isSelfDualAt_iff_dualSubmodule_eq :
    let M := ℤ_[p] ⊗[ℤ] L
    let N := LinearMap.range (TensorProduct.mk ℤ_[p] ℚ_[p] M 1)
    S.IsSelfDualAt p ↔ ((S.form.baseChange ℤ_[p]).baseChange ℚ_[p]).dualSubmodule N = N :=
  Iff.rfl

/-- The lattice is self-dual at `p` exactly when the pairing extended to `ℤ_[p]` is perfect. -/
theorem isSelfDualAt_iff_isPerfPair :
    S.IsSelfDualAt p ↔ (S.form.baseChange ℤ_[p]).IsPerfPair :=
  (S.isSelfDualAt_iff_dualSubmodule_eq p).trans
    (S.form.baseChange_padic_dualSubmodule_eq_self_iff_isPerfPair S.nondegenerate p)

/-- A symplectic lattice is self-dual at `p` exactly when `p` does not divide its dual index. -/
theorem isSelfDualAt_iff_not_dvd_dualIndex :
    S.IsSelfDualAt p ↔ ¬p ∣ S.dualIndex :=
  (S.isSelfDualAt_iff_dualSubmodule_eq p).trans
    (S.form.baseChange_padic_dualSubmodule_eq_self_iff_not_dvd_relIndex S.nondegenerate p)

end Padic

end SymplecticOLattice
end TauCeti
