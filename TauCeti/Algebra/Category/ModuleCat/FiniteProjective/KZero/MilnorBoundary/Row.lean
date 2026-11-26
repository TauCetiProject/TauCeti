/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.MilnorBoundary
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.SemilinearEquiv
public import TauCeti.RingTheory.MilnorSquare.RowPatch

/-!
# The Milnor boundary for left projectives

The left row patch for a transition `a` from the second endpoint to the first represents
the boundary class `[patch(a)] - n[D]` in the split Grothendieck group of left projectives.
The opposite-ring comparison uses transpose on `K₁`. The sign in the comparison to
`RingHom.milnorBoundary` comes from its first-to-second parameter convention.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §§2.9–2.10.
-/

public section

noncomputable section

open CategoryTheory Matrix Matrix.GeneralLinearGroup TauCeti

namespace RingHom

universe u₁ u₂ v

variable {A₁ : Type u₁} {A₂ : Type u₂} {Q : Type v} [Ring A₁] [Ring A₂] [Ring Q]
  (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)

/-- A row patch as an object of the left finite projective category. -/
def rowPatchedFiniteProjective (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {n : Type} [Fintype n] [DecidableEq n] (a : GL n Q) :
    (finiteProjectiveModules (π₁.pullback π₂)).FullSubcategory :=
  ⟨ModuleCat.of _ (π₁.rowPatch π₂ a),
    finiteProjectiveModules_iff.2 ⟨finite_rowPatch h a, projective_rowPatch h a⟩⟩

/-- The row-patched projective has the left row patch as its underlying module. -/
@[simp]
theorem rowPatchedFiniteProjective_obj (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {n : Type} [Fintype n] [DecidableEq n] (a : GL n Q) :
    (rowPatchedFiniteProjective π₁ π₂ h a).obj = ModuleCat.of _ (π₁.rowPatch π₂ a) :=
  (rfl)

/-- The Milnor boundary in left row coordinates. It uses the positive patched-minus-free
class when the transition goes from the second endpoint to the first. -/
def milnorBoundaryLeft (h : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    Additive (AlgebraicK1 Q) →+
      SplitK0.{max u₁ u₂} (finiteProjectiveModules (π₁.pullback π₂)).FullSubcategory :=
  -((SplitK0.map.{max u₁ u₂, max u₁ u₂}
    (π₁.pullbackOpOpEquiv π₂).toRingHom.finiteProjectiveModulesExtendScalars).comp
    ((milnorBoundary π₁.op π₂.op (by simpa using h)).comp
      AlgebraicK1.transposeOp.toAdditive))

/-- Under the opposite-ring comparison, the left boundary of a class is the right boundary
of its transposed class with the transition read from the second endpoint to the first. -/
theorem milnorBoundaryLeft_apply (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (x : AlgebraicK1 Q) :
    milnorBoundaryLeft π₁ π₂ h (Additive.ofMul x) =
      SplitK0.map.{max u₁ u₂, max u₁ u₂}
        (π₁.pullbackOpOpEquiv π₂).toRingHom.finiteProjectiveModulesExtendScalars
        (milnorBoundary π₁.op π₂.op (by simpa using h)
          (Additive.ofMul (AlgebraicK1.transposeOp x)⁻¹)) := by
  simp [milnorBoundaryLeft]

/-- A matrix represents the left row patch minus the free class of the same size. -/
@[simp]
theorem milnorBoundaryLeft_mk (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (n : ℕ) (a : GL (Fin n) Q) :
    milnorBoundaryLeft π₁ π₂ h (Additive.ofMul (AlgebraicK1.mk Q n a)) =
      SplitK0.of.{max u₁ u₂} (rowPatchedFiniteProjective π₁ π₂ h a) -
        n • SplitK0.of.{max u₁ u₂} (finiteProjectiveModulesRegular (π₁.pullback π₂)) := by
  rw [milnorBoundaryLeft_apply, AlgebraicK1.transposeOp_mk, ← map_inv, milnorBoundary_mk, map_sub,
    map_nsmul, SplitK0.map_of, SplitK0.map_of,
    SplitK0.of_extendScalars_obj_finiteProjectiveModulesRegular]
  congr 1
  apply SplitK0.of_extendScalars_obj
  rw [patchedFiniteProjective_obj, rowPatchedFiniteProjective_obj]
  exact (patchedSubgroupOpEquivRowPatch π₁ π₂ a).balancedExtension

/-- The left boundary vanishes on classes extended from the first endpoint. -/
@[simp]
theorem milnorBoundaryLeft_map_fst (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (x : AlgebraicK1 A₁) :
    milnorBoundaryLeft π₁ π₂ h (Additive.ofMul (AlgebraicK1.map π₁ x)) = 0 := by
  simp [milnorBoundaryLeft_apply, AlgebraicK1.transposeOp_map, ← map_inv,
    milnorBoundary_map_fst]

/-- The left boundary vanishes on classes extended from the second endpoint. -/
@[simp]
theorem milnorBoundaryLeft_map_snd (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (x : AlgebraicK1 A₂) :
    milnorBoundaryLeft π₁ π₂ h (Additive.ofMul (AlgebraicK1.map π₂ x)) = 0 := by
  simp [milnorBoundaryLeft_apply, AlgebraicK1.transposeOp_map, ← map_inv,
    milnorBoundary_map_snd]

end RingHom
