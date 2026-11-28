/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product
public import Mathlib.RepresentationTheory.Basic

/-!
# Pure tensors acting in a representation of a product

The group-algebra action of a pure tensor is the product of the actions through the two
factor inclusions, even if the representation is not itself an external tensor product.
-/

public section

open Algebra.TensorProduct (tmul_mul_tmul)
open TauCeti.MonoidAlgebra
open scoped TensorProduct

namespace Representation

variable {k G H V : Type*} [CommSemiring k] [Monoid G] [Monoid H]
  [AddCommMonoid V] [Module k V]

/-- The action of a pure tensor in a representation of a product monoid is the composition of
the two restricted actions. -/
@[simp]
theorem asAlgebraHom_prodTensorBialgEquiv_symm_tmul (ρ : Representation k (G × H) V)
    (a : MonoidAlgebra k G) (b : MonoidAlgebra k H) :
    ρ.asAlgebraHom ((prodTensorBialgEquiv k).symm (a ⊗ₜ[k] b)) =
      asAlgebraHom (ρ.comp (MonoidHom.inl G H)) a *
        asAlgebraHom (ρ.comp (MonoidHom.inr G H)) b := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp [TensorProduct.add_tmul, ha, ha', add_mul]
  | single g r =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp [TensorProduct.tmul_add, hb, hb', mul_add]
    | single h s =>
      simp [asAlgebraHom_single, ← map_mul, MonoidHom.inl_apply, MonoidHom.inr_apply,
        smul_smul, mul_comm r s]

/-- The two restricted group-algebra actions in a representation of a product commute. -/
theorem commute_asAlgebraHom_prod_inl_inr (ρ : Representation k (G × H) V)
    (a : MonoidAlgebra k G) (b : MonoidAlgebra k H) :
    Commute (asAlgebraHom (ρ.comp (MonoidHom.inl G H)) a)
      (asAlgebraHom (ρ.comp (MonoidHom.inr G H)) b) := by
  have hl := ρ.asAlgebraHom_prodTensorBialgEquiv_symm_tmul a (1 : MonoidAlgebra k H)
  have hr := ρ.asAlgebraHom_prodTensorBialgEquiv_symm_tmul (1 : MonoidAlgebra k G) b
  rw [map_one, mul_one] at hl
  rw [map_one, one_mul] at hr
  rw [← hl, ← hr]
  have h : Commute (a ⊗ₜ[k] (1 : MonoidAlgebra k H)) ((1 : MonoidAlgebra k G) ⊗ₜ[k] b) := by
    simp [commute_iff_eq, tmul_mul_tmul]
  let e := (prodTensorBialgEquiv k (G := G) (H := H)).symm.toAlgEquiv
  exact h.map (ρ.asAlgebraHom.comp e.toAlgHom)

end Representation
