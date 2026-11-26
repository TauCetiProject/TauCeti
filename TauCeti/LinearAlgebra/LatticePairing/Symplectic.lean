/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.TensorProduct.Module
public import TauCeti.Algebra.TensorProduct.Module.RightAction
public import TauCeti.LinearAlgebra.BilinearForm.Dual.PerfectPairing
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Symplectic lattices with an order action

A symplectic `O`-lattice is a finite free abelian group with a left action of a ring with
involution `O` and a nondegenerate alternating pairing for which `b` is adjoint to `star b`.
We use the integral scalar coordinates of the pairing, identifying the Tate line `ℤ(1)` with
`ℤ` by its generator `2πi`.

The rational dual lattice is an `O`-submodule. The index of the original lattice in the dual
is the absolute Gram determinant of the integral pairing, and the completion at `p` is
self-dual exactly when `p` does not divide this index.

## References

* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, thesis, §1.2.1.
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
    S.form.baseChange A (b • x) y = S.form.baseChange A x (star b • y) := by
  have h : S.form.compl₁₂ (Algebra.lsmul ℤ ℤ L b) LinearMap.id =
      S.form.compl₁₂ LinearMap.id (Algebra.lsmul ℤ ℤ L (star b)) :=
    LinearMap.ext fun v ↦ LinearMap.ext fun w ↦ S.adjoint b v w
  have hA := congrArg (LinearMap.BilinForm.baseChange A) h
  simp only [LinearMap.BilinForm.baseChange_compl₁₂, LinearMap.baseChange_id] at hA
  simpa only [TensorProduct.rightModule_smul_eq_lTensor, LinearMap.compl₁₂_apply,
    LinearMap.id_apply, LinearMap.baseChange_eq_lTensor] using congr($hA x y)

/-- With the trivial involution on the base ring, the entire scalar-extended order acts
by star-adjoints for the extended pairing. This holds over nonflat base rings as well. -/
theorem baseChange_tensor_adjoint [StarRing A] [TrivialStar A]
    (c : A ⊗[ℤ] O) (x y : A ⊗[ℤ] L) :
    let ρ := BialgebraModule.tensorPairAction ℤ A L
    S.form.baseChange A (ρ c x) y = S.form.baseChange A x (ρ (star c) y) := by
  intro ρ
  have hsmul (a : A) (b : O) (z : A ⊗[ℤ] L) : ρ (a ⊗ₜ[ℤ] b) z = a • (b • z) := by
    have hmul : a ⊗ₜ[ℤ] b = (a ⊗ₜ[ℤ] (1 : O)) * ((1 : A) ⊗ₜ[ℤ] b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hmul, map_mul, mul_apply_eq_comp, BialgebraModule.tensorPairAction_tmul_one,
      BialgebraModule.tensorPairAction_one_tmul, TensorProduct.rightModule_smul_eq_lTensor]
  induction c using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.star_tmul, star_trivial, hsmul, hsmul,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, S.baseChange_adjoint]
  | add c d hc hd =>
    simp only [star_add, map_add, LinearMap.add_apply, hc, hd]

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
theorem le_dual : LinearMap.range (toRational (O := O) (L := L)) ≤ S.dual := by
  rintro _ ⟨x, rfl⟩
  refine S.mem_dual_iff.2 fun y ↦ Submodule.mem_one.2 ⟨S.form x y, ?_⟩
  simp

/-- The index of the integral lattice in its rational dual. -/
noncomputable def dualIndex : ℕ :=
  (LinearMap.range (toRational (O := O) (L := L))).toAddSubgroup.relIndex S.dual.toAddSubgroup

/-- The order-stable dual spans the rational space and is a lattice over the integers. -/
instance instIsFullLatticeDual : (S.dual.restrictScalars ℤ).IsFullLattice ℚ := by
  rw [S.dual_restrictScalars]
  exact (S.form.baseChange ℚ).isFullLattice_dualSubmodule S.nondegenerate_rat
    (LinearMap.range (TensorProduct.mk ℤ ℚ L 1))

/-- The dual index is the absolute Gram determinant in any integral basis. -/
theorem dualIndex_eq_natAbs_det {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    S.dualIndex = (S.form.toMatrix b).det.natAbs := by
  let bQ := b.baseChange ℚ
  let B := S.form.baseChange ℚ
  let d := B.dualBasis S.nondegenerate_rat bQ
  have hbQ : (LinearMap.range (TensorProduct.mk ℤ ℚ L 1)) =
      Submodule.span ℤ (Set.range bQ) := b.range_mk_one_eq_span
  have hcarrier :
      (LinearMap.range (toRational (O := O))).toAddSubgroup =
        AddSubgroup.closure (Set.range bQ) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure]
    exact hbQ
  have hdual : S.dual.toAddSubgroup = AddSubgroup.closure (Set.range d) := by
    apply AddSubgroup.toIntSubmodule.injective
    rw [AddSubgroup.toIntSubmodule_closure, ← B.dualSubmodule_span_of_basis S.nondegenerate_rat bQ,
      ← hbQ]
    exact S.dual_restrictScalars
  have hindex := AddSubgroup.relIndex_eq_abs_det _ _
    (Submodule.toAddSubgroup_le _ _ |>.mpr S.le_dual) bQ d hcarrier hdual
  have hm : d.toMatrix bQ = ((S.form.toMatrix b).map (algebraMap ℤ ℚ)).transpose := by
    ext i j
    simp [d, bQ, B, Basis.toMatrix_apply]
  rw [Basis.det_apply, hm, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at hindex
  apply (Nat.cast_injective (R := ℚ))
  rw [Nat.cast_natAbs, Int.cast_abs]
  exact hindex

/-- The rational dual contains the integral lattice with positive finite index. -/
theorem dualIndex_pos : 0 < S.dualIndex := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  rw [S.dualIndex_eq_natAbs_det b]
  exact Int.natAbs_pos.mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp S.nondegenerate)

/-- Index one characterizes self-duality in the rational span. -/
@[simp]
theorem dualIndex_eq_one_iff :
    S.dualIndex = 1 ↔ S.dual = LinearMap.range (toRational (O := O) (L := L)) := by
  rw [dualIndex, AddSubgroup.relIndex_eq_one, Submodule.toAddSubgroup_le, S.le_dual.ge_iff_eq]
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

/-- A completed lattice is self-dual exactly when its integral pairing is perfect. -/
theorem isSelfDualAt_iff_isPerfPair :
    S.IsSelfDualAt p ↔ (S.form.baseChange ℤ_[p]).IsPerfPair := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hB : (S.form.baseChange ℤ_[p]).Nondegenerate :=
    (S.form.nondegenerate_baseChange_iff b).2 S.nondegenerate
  exact (S.form.baseChange ℤ_[p]).dualSubmodule_range_mk_eq_self_iff_isPerfPair
    (hB.baseChange_of_isLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]))

/-- A symplectic lattice is self-dual at `p` exactly when `p` does not divide its dual index. -/
theorem isSelfDualAt_iff_not_dvd_dualIndex :
    S.IsSelfDualAt p ↔ ¬p ∣ S.dualIndex := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let bP := b.baseChange ℤ_[p]
  let B := S.form.baseChange ℤ_[p]
  have hdet : B.IsPerfPair ↔ IsUnit (B.toMatrix bP).det :=
    ⟨bP.isUnit_det_of_isPerfPair bP B, bP.isPerfPair_of_isUnit_det bP B⟩
  rw [S.isSelfDualAt_iff_isPerfPair p, hdet, LinearMap.BilinForm.det_toMatrix_baseChange,
    S.dualIndex_eq_natAbs_det b, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  exact PadicInt.isUnit_intCast_iff

end Padic

end SymplecticOLattice
end TauCeti
