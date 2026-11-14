/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul

/-!
# Right translation of comultiplication and matrix coefficients

For a commutative Hopf algebra `H` over a commutative ring `R`, pullback along right translation by
a rational point `u : WithConv (H →ₐ[R] R)` is left `H`-colinear for the regular comultiplication
of `H`, and transforms the matrix coefficient of a vector in a right `H`-comodule by acting on that
vector via `TauCeti.Comodule.basePointsRepresentation`. No reducedness, finite-type, or field
assumptions are needed.

## Main declarations

* `TauCeti.HopfAlgebra.comul_rightTranslationAlgHom`: right translation commutes with
  comultiplication in the second tensor factor.
* `TauCeti.HopfAlgebra.rightTranslationAlgHom_matrixCoefficient`: right-translating a matrix
  coefficient evaluates the matrix coefficient on the point-translated vector.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 2.g and 4.b.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 3.1 and 6.7.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [_root_.HopfAlgebra R H]

/-- Right translation by a base-valued point is left `H`-colinear for the regular
comultiplication: `Δ(R_u x) = (id ⊗ R_u)(Δ x)`. -/
theorem comul_rightTranslationAlgHom (u : WithConv (H →ₐ[R] R)) (x : H) :
    Coalgebra.comul (R := R) (rightTranslationAlgHom u x) =
      (rightTranslationAlgHom u).toLinearMap.lTensor H (Coalgebra.comul (R := R) x) := by
  let f : H →ₗ[R] R := u.ofConv.toLinearMap
  let E : (H ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] H :=
    (TensorProduct.rid R (H ⊗[R] H)).toLinearMap ∘ₗ TensorProduct.map LinearMap.id f
  have hleft (z : H ⊗[R] H) :
      E (TensorProduct.map (Coalgebra.comul (R := R) (A := H)) LinearMap.id z) =
        Coalgebra.comul (R := R) (TensorProduct.rid R H (TensorProduct.map LinearMap.id f z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [E]
    | add y w hy hw => simp [hy, hw]
  have hright (z : H ⊗[R] H) :
      E ((TensorProduct.assoc R H H H).symm
          (TensorProduct.map LinearMap.id (Coalgebra.comul (R := R) (A := H)) z)) =
        (rightTranslationAlgHom u).toLinearMap.lTensor H z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul,
        AlgHom.toLinearMap_apply, rightTranslationAlgHom_apply]
      induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
      | tmul b₁ b₂ => simp [E, f, TensorProduct.tmul_smul]
      | add y w hy hw => simp [TensorProduct.tmul_add, hy, hw]
    | add y w hy hw => simp [hy, hw]
  have hcoassoc := congrArg E
    (LinearMap.congr_fun (Coalgebra.coassoc_symm (R := R) (A := H)) x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.rTensor_def, LinearMap.lTensor_def] at hcoassoc
  rw [rightTranslationAlgHom_apply, ← hleft, ← hcoassoc, hright]

/-- Right-translating a matrix coefficient of a vector in a right `H`-comodule by a base-valued
point evaluates the matrix coefficient on the vector acted on by that point. -/
@[simp]
theorem rightTranslationAlgHom_matrixCoefficient {M : Type w} [AddCommMonoid M] [Module R M]
    [Comodule R H M] (u : WithConv (H →ₐ[R] R)) (ψ : Module.Dual R M) (m : M) :
    rightTranslationAlgHom u (Comodule.matrixCoefficient (R := R) (C := H) ψ m) =
      Comodule.matrixCoefficient (R := R) (C := H) ψ
        (Comodule.basePointsRepresentation (H := H) M u m) := by
  rw [rightTranslationAlgHom_apply, Comodule.comul_matrixCoefficient,
    Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, one_smul]
  induction Comodule.coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | tmul v a => simp
  | add x y hx hy => simp [hx, hy]

end TauCeti.HopfAlgebra
