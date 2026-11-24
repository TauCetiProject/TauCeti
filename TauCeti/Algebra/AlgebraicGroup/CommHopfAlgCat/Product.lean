/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Factor swap on tensor-square commutative Hopf algebras

For `H : CommHopfAlgCat R`, `CommHopfAlgCat.swapEnd H` swaps the two factors of `H ⊗[R] H`,
representing `(g₁, g₂) ↦ (g₂, g₁)` on `Spec H × Spec H`.

## Main declarations

* `CommHopfAlgCat.swapEnd`, `swapEnd_comp_swapEnd`, `swapEnd_comp_mulBialgHom`: the factor-swap
  endomorphism, its involutivity, and its invariance on multiplication `H ⊗[R] H ⟶ H`.
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] (H : CommHopfAlgCat.{v} R)

/-- The factor-swapping endomorphism `x ⊗ₜ y ↦ y ⊗ₜ x` of `H ⊗[R] H`. -/
noncomputable def swapEnd : CommHopfAlgCat.of R (H ⊗[R] H) ⟶ CommHopfAlgCat.of R (H ⊗[R] H) :=
  CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.comm R H H).toBialgHom

/-- Underlying bialgebra morphism of `swapEnd H`. -/
@[simp]
theorem swapEnd_hom : (swapEnd H).hom = (Bialgebra.TensorProduct.comm R H H).toBialgHom :=
  CommHopfAlgCat.hom_ofHom _

/-- Swapping the two tensor factors twice is the identity. -/
@[reassoc (attr := simp)]
theorem swapEnd_comp_swapEnd : swapEnd H ≫ swapEnd H = 𝟙 (CommHopfAlgCat.of R (H ⊗[R] H)) :=
  CommHopfAlgCat.hom_ext <| BialgHom.coe_toAlgHom_injective <|
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- Multiplication `H ⊗[R] H →ₐc[R] H` is invariant under `swapEnd H`. -/
@[reassoc (attr := simp)]
theorem swapEnd_comp_mulBialgHom :
    swapEnd H ≫ CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) =
      CommHopfAlgCat.ofHom (Bialgebra.mulBialgHom R H) :=
  CommHopfAlgCat.hom_ext <| BialgHom.coe_toAlgHom_injective <|
    Algebra.TensorProduct.ext' fun x y ↦ mul_comm y x

end CommHopfAlgCat
