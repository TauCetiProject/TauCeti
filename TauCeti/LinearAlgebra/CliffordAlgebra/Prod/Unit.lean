/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Unit laws of graded tensor products of Clifford modules

When one summand of `Q₁.prod Q₂` is a subsingleton, `R` is a Clifford module over it and
`TensorProduct.lid R F` / `TensorProduct.rid R E` intertwine `AlgHom.cliffordProdTensor` with the
remaining factor (twisting by `CliffordAlgebra.involute` when `R` carries the grading `-1`).

## Main results

* `AlgHom.conjAlgEquiv_cliffordProdTensor_comp_map_inr` and
  `AlgHom.lid_cliffordProdTensor_map_inr`: `TensorProduct.lid R F` intertwines the `(R, 1)`-graded
  product action along `Isometry.inr` with `ρ₂`.
* `AlgHom.conjAlgEquiv_cliffordProdTensor_neg_one_comp_map_inr` and
  `AlgHom.lid_cliffordProdTensor_neg_one_map_inr`: equipping `R` with `-1` twists `ρ₂` by
  `CliffordAlgebra.involute`.
* `AlgHom.conjAlgEquiv_cliffordProdTensor_uniqueProd` and
  `AlgHom.lid_cliffordProdTensor_uniqueProd`: left unit law on `CliffordAlgebra (Q₁.prod Q₂)` for a
  `Unique` left summand.
* `AlgHom.rid_cliffordProdTensor_map_inl`,
  `AlgHom.conjAlgEquiv_cliffordProdTensor_uniqueProd_right`, and
  `AlgHom.rid_cliffordProdTensor_uniqueProd`: right unit laws under `TensorProduct.rid R E`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open CliffordAlgebra TensorProduct

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

section LeftSubsingleton

variable [Subsingleton M₁] (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- Conjugating the graded tensor product with `(R, 1)` on the left by `TensorProduct.lid R F`
along `QuadraticMap.Isometry.inr` recovers `ρ₂`. -/
theorem conjAlgEquiv_cliffordProdTensor_comp_map_inr :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        ((cliffordProdTensor ρ₁ 1 (mul_one 1) (by simp) ρ₂).comp
          (CliffordAlgebra.map (QuadraticMap.Isometry.inr Q₁ Q₂))) =
      ρ₂ := by
  apply CliffordAlgebra.hom_ext; ext w f; simp [LinearEquiv.conjAlgEquiv_apply]

/-- **Left unit law along the second-summand inclusion.** For `[Subsingleton M₁]` and grading `1`
on `R`, `TensorProduct.lid R F` intertwines `map (Isometry.inr Q₁ Q₂) b` with `ρ₂ b`. -/
theorem lid_cliffordProdTensor_map_inr (b : CliffordAlgebra Q₂) (z : R ⊗[R] F) :
    (TensorProduct.lid R F)
        (cliffordProdTensor ρ₁ 1 (mul_one 1) (by simp) ρ₂
          (CliffordAlgebra.map (QuadraticMap.Isometry.inr Q₁ Q₂) b) z) =
      ρ₂ b ((TensorProduct.lid R F) z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun φ ↦ φ b ((TensorProduct.lid R F) z))
    (conjAlgEquiv_cliffordProdTensor_comp_map_inr ρ₁ ρ₂)

/-- Conjugating the graded tensor product with `(R, -1)` on the left by `TensorProduct.lid R F`
along `QuadraticMap.Isometry.inr` twists `ρ₂` by `CliffordAlgebra.involute`. -/
theorem conjAlgEquiv_cliffordProdTensor_neg_one_comp_map_inr :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        ((cliffordProdTensor ρ₁ (-1)
          ((neg_mul_neg (1 : Module.End R R) 1).trans (one_mul 1)) (by simp) ρ₂).comp
          (CliffordAlgebra.map (QuadraticMap.Isometry.inr Q₁ Q₂))) =
      ρ₂.comp (involute : CliffordAlgebra Q₂ →ₐ[R] CliffordAlgebra Q₂) := by
  apply CliffordAlgebra.hom_ext; ext w f; simp [LinearEquiv.conjAlgEquiv_apply]

/-- **Signed left unit law.** Equipping `R` with grading `-1` twists the left unit identification
by `CliffordAlgebra.involute`. -/
theorem lid_cliffordProdTensor_neg_one_map_inr (b : CliffordAlgebra Q₂) (z : R ⊗[R] F) :
    (TensorProduct.lid R F)
        (cliffordProdTensor ρ₁ (-1)
          ((neg_mul_neg (1 : Module.End R R) 1).trans (one_mul 1)) (by simp) ρ₂
          (CliffordAlgebra.map (QuadraticMap.Isometry.inr Q₁ Q₂) b) z) =
      ρ₂ (involute b) ((TensorProduct.lid R F) z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun φ ↦ φ b ((TensorProduct.lid R F) z))
    (conjAlgEquiv_cliffordProdTensor_neg_one_comp_map_inr ρ₁ ρ₂)

end LeftSubsingleton

section LeftUnique

variable [Unique M₁] (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- Conjugating the graded tensor product with a trivial left factor `(R, 1)` by
`TensorProduct.lid R F` recovers `ρ₂` along `QuadraticMap.IsometryEquiv.uniqueProd`. -/
theorem conjAlgEquiv_cliffordProdTensor_uniqueProd :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ 1 (mul_one 1) (by simp) ρ₂) =
      ρ₂.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext; apply LinearMap.ext; rintro ⟨x₁, x₂⟩; ext f
  simp [Subsingleton.elim x₁ 0, LinearEquiv.conjAlgEquiv_apply, equivOfIsometry_apply]

/-- Pointwise left unit law on arbitrary Clifford elements for a `Unique` left summand. -/
theorem lid_cliffordProdTensor_uniqueProd (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    (TensorProduct.lid R F)
        (cliffordProdTensor ρ₁ 1 (mul_one 1) (by simp) ρ₂ a z) =
      ρ₂ (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a)
        ((TensorProduct.lid R F) z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun φ ↦ φ a ((TensorProduct.lid R F) z))
    (conjAlgEquiv_cliffordProdTensor_uniqueProd ρ₁ ρ₂)

end LeftUnique

section RightUnit

variable (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R)

/-- **Right unit law along the first-summand inclusion.** The right unitor `TensorProduct.rid R E`
intertwines the graded tensor action of `map (Isometry.inl Q₁ Q₂) a` with `ρ₁ a`. -/
theorem rid_cliffordProdTensor_map_inl (a : CliffordAlgebra Q₁) (z : E ⊗[R] R) :
    (TensorProduct.rid R E)
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂
          (CliffordAlgebra.map (QuadraticMap.Isometry.inl Q₁ Q₂) a) z) =
      ρ₁ a ((TensorProduct.rid R E) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul e r => simp [cliffordProdTensor_map_inl]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Conjugating the graded tensor product with a trivial right factor by `TensorProduct.rid R E`
recovers `ρ₁` along the projection deleting `M₂`, regardless of the grading `γ` of `E`. -/
theorem conjAlgEquiv_cliffordProdTensor_uniqueProd_right [Unique M₂] :
    ((TensorProduct.rid R E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₁.comp (equivOfIsometry ((QuadraticMap.IsometryEquiv.prodComm Q₁ Q₂).trans
        (QuadraticMap.IsometryEquiv.uniqueProd Q₂ Q₁))).toAlgHom := by
  apply CliffordAlgebra.hom_ext; apply LinearMap.ext; rintro ⟨x₁, x₂⟩; ext e
  simp [Subsingleton.elim x₂ 0, LinearEquiv.conjAlgEquiv_apply, equivOfIsometry_apply]

/-- Pointwise right unit law on arbitrary Clifford elements for a `Unique` right summand. -/
theorem rid_cliffordProdTensor_uniqueProd [Unique M₂] (a : CliffordAlgebra (Q₁.prod Q₂))
    (z : E ⊗[R] R) :
    (TensorProduct.rid R E) (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₁ (equivOfIsometry ((QuadraticMap.IsometryEquiv.prodComm Q₁ Q₂).trans
        (QuadraticMap.IsometryEquiv.uniqueProd Q₂ Q₁)) a) ((TensorProduct.rid R E) z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun φ ↦ φ a ((TensorProduct.rid R E) z))
    (conjAlgEquiv_cliffordProdTensor_uniqueProd_right ρ₁ γ hγ hγρ ρ₂)

end RightUnit

end AlgHom
