/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Products of bilinear forms

The product of two bilinear forms is the block-diagonal form on the product module: each factor
carries its own form and the two factors are orthogonal to each other. It is the bilinear
counterpart of `QuadraticMap.prod`, and it is the form an orthogonal direct sum of bilinear
modules carries.

Symmetry, separation and nondegeneracy are componentwise, flipping is componentwise, and a
product of perfect pairings is a perfect pairing.

## Main declarations

* `LinearMap.BilinForm.prod`: the block-diagonal form on a product module.
* `LinearMap.BilinForm.isSymm_prod_iff`: the product form is symmetric exactly when both factors
  are.
* `LinearMap.BilinForm.flip_prod`: flipping the product form flips both factors.
* `LinearMap.BilinForm.separatingLeft_prod_iff`, `LinearMap.BilinForm.separatingRight_prod_iff`:
  the product form is left (right) separating exactly when both factors are.
* `LinearMap.BilinForm.nondegenerate_prod_iff`: the product form is nondegenerate exactly when
  both factors are.
* `LinearMap.BilinForm.instIsPerfPairProd`: a product of perfect pairings is a perfect pairing.
-/

public section

namespace LinearMap.BilinForm

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The block-diagonal bilinear form on a product module: the two factors keep their own forms
and pair to zero with each other. -/
def prod (B : LinearMap.BilinForm R M) (C : LinearMap.BilinForm R N) :
    LinearMap.BilinForm R (M × N) :=
  B.comp (LinearMap.fst R M N) (LinearMap.fst R M N) +
    C.comp (LinearMap.snd R M N) (LinearMap.snd R M N)

@[simp]
theorem prod_apply (B : LinearMap.BilinForm R M) (C : LinearMap.BilinForm R N) (x y : M × N) :
    B.prod C x y = B x.1 y.1 + C x.2 y.2 :=
  (rfl)

/-- A product of bilinear forms is symmetric exactly when both factors are. -/
@[simp]
theorem isSymm_prod_iff {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N} :
    (B.prod C).IsSymm ↔ B.IsSymm ∧ C.IsSymm := by
  refine ⟨fun h ↦ ⟨⟨fun x y ↦ ?_⟩, ⟨fun x y ↦ ?_⟩⟩, fun ⟨hB, hC⟩ ↦ ⟨fun x y ↦ ?_⟩⟩
  · simpa using h.eq (x, 0) (y, 0)
  · simpa using h.eq (0, x) (0, y)
  · simp [hB.eq x.1, hC.eq x.2]

/-- Curried, the product form is the product of the two curried forms followed by the
identification of a product of duals with the dual of the product. -/
private theorem prod_eq_dualProdDualEquivDual_comp_prodMap (B : LinearMap.BilinForm R M)
    (C : LinearMap.BilinForm R N) :
    B.prod C = (Module.dualProdDualEquivDual R M N).toLinearMap ∘ₗ B.prodMap C := by
  ext <;> simp

/-- Flipping a product of bilinear forms flips each factor. -/
@[simp]
theorem flip_prod (B : LinearMap.BilinForm R M) (C : LinearMap.BilinForm R N) :
    LinearMap.flip (B.prod C) = prod (LinearMap.flip B) (LinearMap.flip C) := by
  ext <;> simp

/-- A product of bilinear forms is left-separating exactly when both factors are. -/
@[simp]
theorem separatingLeft_prod_iff {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N} :
    (B.prod C).SeparatingLeft ↔ B.SeparatingLeft ∧ C.SeparatingLeft := by
  simp [separatingLeft_iff_ker_eq_bot, prod_eq_dualProdDualEquivDual_comp_prodMap,
    LinearMap.ker_prodMap, Submodule.prod_eq_bot_iff]

/-- A product of bilinear forms is right-separating exactly when both factors are. -/
@[simp]
theorem separatingRight_prod_iff {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N} :
    (B.prod C).SeparatingRight ↔ B.SeparatingRight ∧ C.SeparatingRight := by
  simp only [← flip_separatingLeft, flip_prod, separatingLeft_prod_iff]

/-- A product of bilinear forms is nondegenerate exactly when both factors are. -/
@[simp]
theorem nondegenerate_prod_iff {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N} :
    (B.prod C).Nondegenerate ↔ B.Nondegenerate ∧ C.Nondegenerate := by
  simp only [Nondegenerate, LinearMap.Nondegenerate, separatingLeft_prod_iff,
    separatingRight_prod_iff, and_and_and_comm]

/-- The product form identifies the product module with its dual when both factors identify their
modules with their duals. -/
private theorem bijective_prod {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N}
    (hB : Function.Bijective B) (hC : Function.Bijective C) : Function.Bijective (B.prod C) := by
  rw [prod_eq_dualProdDualEquivDual_comp_prodMap, LinearMap.coe_comp, LinearMap.coe_prodMap]
  exact (LinearEquiv.bijective _).comp (hB.prodMap hC)

/-- A product of perfect pairings is a perfect pairing. -/
instance instIsPerfPairProd {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N}
    [B.IsPerfPair] [C.IsPerfPair] : (B.prod C).IsPerfPair where
  bijective_left := bijective_prod (IsPerfPair.bijective_left B) (IsPerfPair.bijective_left C)
  bijective_right := by
    rw [flip_prod]
    exact bijective_prod (IsPerfPair.bijective_right B) (IsPerfPair.bijective_right C)

end LinearMap.BilinForm
