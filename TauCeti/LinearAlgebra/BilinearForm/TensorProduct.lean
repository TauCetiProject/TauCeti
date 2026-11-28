/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Alternation of tensor products of bilinear forms

Tensoring a symmetric bilinear form over a commutative `R`-algebra `A` with an alternating
form over `R` gives an alternating form over `A`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N]

/-- The tensor product of a symmetric form and an alternating form is alternating. -/
theorem IsSymm.tmul_isAlt {B : BilinForm A M} {C : BilinForm R N}
    (hB : B.IsSymm) (hC : C.IsAlt) : (B.tmul C).IsAlt := by
  have hskew : B.tmul C + (B.tmul C).flip = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro x₁ x₂
    apply TensorProduct.AlgebraTensorModule.ext
    intro y₁ y₂
    have halt := congr($(hC.add_flip_eq_zero) x₂ y₂)
    simp only [LinearMap.add_apply, BilinForm.flip_apply, LinearMap.zero_apply] at halt
    simp only [LinearMap.add_apply, LinearMap.flip_apply, LinearMap.zero_apply,
      BilinForm.tensorDistrib_tmul]
    rw [hB.eq y₁ x₁, ← add_smul, halt, zero_smul]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [hC n]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    simpa using congr($hskew y x)

end LinearMap.BilinForm
