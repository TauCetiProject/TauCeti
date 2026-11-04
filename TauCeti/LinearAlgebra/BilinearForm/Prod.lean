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

Symmetry and nondegeneracy are componentwise. In particular, a vector is in the radical of the
product exactly when both of its components are in the radicals of the factors. A product of
perfect pairings is a perfect pairing.

## Main declarations

* `LinearMap.BilinForm.prod`: the block-diagonal form on a product module.
* `LinearMap.BilinForm.isSymm_prod_iff`: the product form is symmetric exactly when both factors
  are.
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

/-- A product of bilinear forms is nondegenerate exactly when both factors are. -/
@[simp]
theorem nondegenerate_prod_iff {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N} :
    (B.prod C).Nondegenerate ↔ B.Nondegenerate ∧ C.Nondegenerate := by
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨⟨fun x hx ↦ congrArg Prod.fst (hleft (x, 0) fun z ↦ by simp [hx z.1]),
        fun x hx ↦ congrArg Prod.fst (hright (x, 0) fun z ↦ by simp [hx z.1])⟩,
      ⟨fun y hy ↦ congrArg Prod.snd (hleft (0, y) fun z ↦ by simp [hy z.2]),
        fun y hy ↦ congrArg Prod.snd (hright (0, y) fun z ↦ by simp [hy z.2])⟩⟩
  · rintro ⟨⟨hBl, hBr⟩, hCl, hCr⟩
    constructor
    · exact fun x hx ↦ Prod.ext (hBl x.1 fun z ↦ by simpa using hx (z, 0))
        (hCl x.2 fun z ↦ by simpa using hx (0, z))
    · exact fun y hy ↦ Prod.ext (hBr y.1 fun z ↦ by simpa using hy (z, 0))
        (hCr y.2 fun z ↦ by simpa using hy (0, z))

/-- The product form identifies the product module with its dual when both factors identify their
modules with their duals. -/
private theorem bijective_prod {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N}
    (hB : Function.Bijective B) (hC : Function.Bijective C) : Function.Bijective (B.prod C) := by
  have : ⇑(B.prod C) = Module.dualProdDualEquivDual R M N ∘ Prod.map B C :=
    funext fun _ ↦ LinearMap.prod_ext (LinearMap.ext fun _ ↦ by simp)
      (LinearMap.ext fun _ ↦ by simp)
  rw [this]
  exact (Module.dualProdDualEquivDual R M N).bijective.comp (hB.prodMap hC)

/-- A product of perfect pairings is a perfect pairing. -/
instance instIsPerfPairProd {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N}
    [B.IsPerfPair] [C.IsPerfPair] : (B.prod C).IsPerfPair where
  bijective_left := bijective_prod (IsPerfPair.bijective_left B) (IsPerfPair.bijective_left C)
  bijective_right := by
    have : LinearMap.flip (B.prod C) = prod (LinearMap.flip B) (LinearMap.flip C) :=
      LinearMap.ext₂ fun _ _ ↦ by simp
    rw [this]
    exact bijective_prod (IsPerfPair.bijective_right B) (IsPerfPair.bijective_right C)

end LinearMap.BilinForm
