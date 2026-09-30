/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# The tensor shear of a commutative Hopf algebra

The pullback of `(g, h) ↦ (g, gh)` is an automorphism of `H ⊗[R] H`. It fixes
the left factor and sends the right factor to comultiplication. Its inverse uses
the antipode in the left factor. This is the algebraic change of coordinates used
in the canonical map for a quotient by a closed subgroup.
-/

public section

open scoped TensorProduct
open WithConv Algebra.TensorProduct

namespace TauCeti.HopfAlgebra

variable {R H : Type*} [CommSemiring R] [CommSemiring H] [_root_.HopfAlgebra R H]

/-- The forward algebra map underlying the tensor shear. -/
private noncomputable def tensorShearHom : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  lift includeLeft (Bialgebra.comulAlgHom R H) (fun _ _ ↦ .all _ _)

/-- The inverse algebra map underlying the tensor shear. -/
private noncomputable def tensorShearInv : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  lift includeLeft
    ((toConv (includeLeft : H →ₐ[R] H ⊗[R] H))⁻¹ * toConv includeRight).ofConv
    (fun _ _ ↦ .all _ _)

private theorem tensorShearHom_comp_inv :
    (tensorShearHom (R := R) (H := H)).comp tensorShearInv = AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc, tensorShearHom, tensorShearInv]
  · -- Tensor extensionality restricts scalars from `R` to itself on the second factor.
    change tensorShearHom.comp (tensorShearInv.comp includeRight) = includeRight
    rw [tensorShearInv, lift_comp_includeRight']
    apply toConv_injective
    rw [← AlgHom.mapValue_apply, map_mul, map_inv]
    simp [tensorShearHom, Bialgebra.comulPoint_eq_include_mul]

private theorem tensorShearInv_comp_hom :
    (tensorShearInv (R := R) (H := H)).comp tensorShearHom = AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc, tensorShearHom, tensorShearInv]
  · -- Tensor extensionality inserts the same redundant scalar restriction here.
    change tensorShearInv.comp (tensorShearHom.comp includeRight) = includeRight
    rw [tensorShearHom, lift_comp_includeRight',
      ← ofConv_toConv (Bialgebra.comulAlgHom R H), Bialgebra.comulPoint_eq_include_mul,
      AlgHom.comp_convMul_distrib]
    simp [tensorShearInv]

/-- The coordinate automorphism of `(g, h) ↦ (g, gh)` on the tensor square of a
commutative Hopf algebra. -/
noncomputable def tensorShear : H ⊗[R] H ≃ₐ[R] H ⊗[R] H :=
  AlgEquiv.ofAlgHom tensorShearHom tensorShearInv
    tensorShearHom_comp_inv tensorShearInv_comp_hom

/-- The tensor shear fixes the first coordinate and multiplies the second by it. -/
@[simp]
theorem tensorShear_tmul (a b : H) :
    tensorShear (R := R) (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * Coalgebra.comul (R := R) b := by
  simp [tensorShear, tensorShearHom]

/-- The inverse tensor shear divides the second coordinate by the first. -/
@[simp]
theorem tensorShear_symm_tmul (a b : H) :
    (tensorShear (R := R)).symm (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * TensorProduct.map (HopfAlgebraStruct.antipode R) LinearMap.id
        (Coalgebra.comul (R := R) b) := by
  simp only [tensorShear, AlgEquiv.ofAlgHom_symm_apply, tensorShearInv, lift_tmul,
    includeLeft_apply, AlgHom.convMul_apply]
  congr 1
  induction Coalgebra.comul (R := R) b with
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

end TauCeti.HopfAlgebra
