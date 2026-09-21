/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.SpecialLinear
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.GraphAutomorphism
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Comparing the type-A standard carrier with special linear matrices

Over a field, the matrix points of the full-weight type-`A_r` carrier are precisely the
determinant-one matrices. This file packages that equality as a multiplicative equivalence with
`SL_{r+1}` and proves that it respects the structures used by the finite groups of Lie type:
the numbered root subgroups, entrywise Frobenius, and signed reverse inverse transpose.

The equivalence is deliberately the identity on underlying matrices. Consequently the comparison
does not merely identify two abstract groups: it identifies their standard representations and
their chosen type-A pinning.

## Main declarations

* `TauCeti.SlStd.specialLinearMulEquiv`: the carrier-point equivalence with `SL_{r+1}`.
* `TauCeti.SlStd.specialLinearMulEquiv_rootSubgroupPoints`: compatibility with the numbered root
  subgroups.
* `TauCeti.SlStd.specialLinearMulEquiv_frobenius`: compatibility with entrywise Frobenius.
* `TauCeti.SlStd.specialLinearMulEquiv_graphAutomorphismPoints`: compatibility with the pinned
  type-A graph automorphism.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
-/

public section

open WithConv

namespace TauCeti.SlStd

universe u

variable (r : ℕ) {K : Type u} [Field K]

/-- **The full-weight type-`A_r` carrier points over a field are multiplicatively equivalent to
`SL_{r+1}`.** Both directions preserve the underlying matrix. -/
noncomputable def specialLinearMulEquiv :
    points r K ≃* Matrix.SpecialLinearGroup (Fin (r + 1)) K where
  toFun g := ⟨g.1.1, by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg Units.val
        ((mem_points_iff_det_eq_one (K := K) r (g :
          Matrix.GeneralLinearGroup (Fin (r + 1)) K)).mp g.property)⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.toGL g, toGL_mem_points r g⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    rfl

/-- Applying the carrier equivalence and then including into `GL` leaves a carrier point
unchanged. -/
@[simp]
theorem specialLinearMulEquiv_toGL (g : points r K) :
    Matrix.SpecialLinearGroup.toGL (specialLinearMulEquiv r g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- The inverse carrier equivalence preserves the underlying general-linear matrix. -/
@[simp]
theorem specialLinearMulEquiv_symm_coe
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
    ((specialLinearMulEquiv r).symm g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) =
      Matrix.SpecialLinearGroup.toGL g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- **The carrier equivalence identifies a numbered root subgroup with the corresponding
determinant-one transvection.** -/
@[simp]
theorem specialLinearMulEquiv_rootSubgroupPoints
    (i : Fin r ⊕ Fin r) (a : Multiplicative K) :
    specialLinearMulEquiv r (rootSubgroupPoints r i K a) =
      Matrix.SpecialLinearGroup.transvection
        (rootTarget_ne_rootSource r i) (Multiplicative.toAdd a) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [specialLinearMulEquiv_toGL, coe_rootSubgroupPoints]
  rw [kostantRootSubgroupMatrix_eq_transvection, MulEquiv.apply_symm_apply,
    ← TauCeti.toGL_transvection_eq_transvectionUnit]

variable (p k : ℕ) [ExpChar K p]

/-- **The carrier equivalence intertwines the carrier Frobenius with entrywise Frobenius on
special linear matrices.** -/
@[simp]
theorem specialLinearMulEquiv_frobenius (g : points r K) :
    specialLinearMulEquiv r (frobenius r p k K g) =
      Matrix.SpecialLinearGroup.map (iterateFrobenius K p k)
        (specialLinearMulEquiv r g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [specialLinearMulEquiv_toGL, coe_frobenius]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- **The carrier equivalence intertwines the carrier graph automorphism with signed reverse
inverse transpose on special linear matrices.** -/
@[simp]
theorem specialLinearMulEquiv_graphAutomorphismPoints
    {F : Type} [Field F] (g : points r F) :
    specialLinearMulEquiv r (graphAutomorphismPoints r F g) =
      Matrix.SpecialLinearGroup.typeAGraphAutomorphism r F
        (specialLinearMulEquiv r g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [specialLinearMulEquiv_toGL, coe_graphAutomorphismPoints,
    Matrix.SpecialLinearGroup.toGL_typeAGraphAutomorphism,
    specialLinearMulEquiv_toGL]

end TauCeti.SlStd
