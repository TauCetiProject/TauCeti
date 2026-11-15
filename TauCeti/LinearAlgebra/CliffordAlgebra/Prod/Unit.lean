/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Left and right unit laws of the graded Clifford tensor product

Over a commutative ring `R`, the scalar module `R` with the identity grading `1` is the two-sided
unit for the graded tensor product `AlgHom.cliffordProdTensor` over trivial quadratic spaces:

* When `M₁` is a trivial module (`[Unique M₁]`), every vector `v : M₁` vanishes, so `ι Q₁ v = 0`
  and any involution of `R` anticommutes vacuously with `ρ₁ (ι Q₁ v)`. Taking the grading `1` of
  `R`, the left unitor `TensorProduct.lid R F : R ⊗[R] F ≃ₗ[R] F` intertwines
  `cliffordProdTensor ρ₁ 1 _ _ ρ₂` with `ρ₂` along `QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂`.
* By contrast, taking the signed grading `-1` of `R` makes `(0, w)` act on `R ⊗[R] F` by
  `-1 ⊗ c₂(w)`, so `TensorProduct.lid R F` intertwines the product action with `ρ₂` precomposed
  with the grade involution `CliffordAlgebra.involute`: the left unit requires the positive grading
  `1`, not `-1`.
* When `M₂` is a trivial module (`[Unique M₂]`), every vector `w : M₂` vanishes, so `(v, w)` acts
  by `c₁(v) ⊗ 1` regardless of the grading `γ` of `E`, and the right unitor
  `TensorProduct.rid R E : E ⊗[R] R ≃ₗ[R] E` intertwines `cliffordProdTensor ρ₁ γ hγ hγρ ρ₂` with
  `ρ₁` along `QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂`.

## Main results

* `AlgHom.conjAlgEquiv_lid_cliffordProdTensor` and `AlgHom.lid_cliffordProdTensor`: for
  `[Unique M₁]` and grading `1` on `R`, `TensorProduct.lid R F` intertwines `cliffordProdTensor`
  with `ρ₂` along `QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂`.
* `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one` and
  `AlgHom.lid_cliffordProdTensor_neg_one`: for grading `-1` on `R`, `TensorProduct.lid R F` twists
  `ρ₂` by `CliffordAlgebra.involute`.
* `AlgHom.conjAlgEquiv_rid_cliffordProdTensor` and `AlgHom.rid_cliffordProdTensor`: for
  `[Unique M₂]` and any grading `γ` on `E`, `TensorProduct.rid R E` intertwines
  `cliffordProdTensor` with `ρ₁` along `QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open CliffordAlgebra TensorProduct

namespace AlgHom

section LeftUnit

variable {R M₁ M₂ F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [Unique M₁]
  [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup F] [Module R F]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- When `M₁` is trivial and `R` carries the positive grading `1`, conjugating
`cliffordProdTensor` by the left unitor `R ⊗[R] F ≃ₗ[R] F` recovers `ρ₂` transported along
`QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂`. -/
theorem conjAlgEquiv_lid_cliffordProdTensor
    (h1ρ : ∀ v, (1 : Module.End R R) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * 1)) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ 1 (one_mul 1) h1ρ ρ₂) =
      ρ₂.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro f
  have hx : x.1 = 0 := Subsingleton.elim x.1 0
  simp [hx, LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, equivOfIsometry_apply]

/-- Pointwise left-unit law: for `[Unique M₁]` and the positive grading `1` of `R`, the left unitor
`TensorProduct.lid R F` intertwines `cliffordProdTensor` with `ρ₂`. -/
theorem lid_cliffordProdTensor
    (h1ρ : ∀ v, (1 : Module.End R R) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * 1))
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F (cliffordProdTensor ρ₁ 1 (one_mul 1) h1ρ ρ₂ a z) =
      ρ₂ (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a)
        (TensorProduct.lid R F z) := by
  have h := congrArg (fun g ↦ g a (TensorProduct.lid R F z))
    (conjAlgEquiv_lid_cliffordProdTensor ρ₁ ρ₂ h1ρ)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- **Signed left-unit contrast**: when `R` is given the negative grading `-1` instead of `1`,
conjugating `cliffordProdTensor` by `TensorProduct.lid R F` twists `ρ₂` by the grade involution
`CliffordAlgebra.involute`, negating every vector of `M₂`. -/
theorem conjAlgEquiv_lid_cliffordProdTensor_neg_one
    (hneg : (-1 : Module.End R R) * (-1) = 1)
    (hnegρ : ∀ v, (-1 : Module.End R R) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-1))) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ (-1) hneg hnegρ ρ₂) =
      (ρ₂.comp (CliffordAlgebra.involute (Q := Q₂))).comp
        (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro f
  have hx : x.1 = 0 := Subsingleton.elim x.1 0
  simp [hx, LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, equivOfIsometry_apply]

/-- Pointwise signed left-unit contrast: with the grading `-1` on `R`, the left unitor carries
`cliffordProdTensor` to `ρ₂ ∘ involute`. -/
theorem lid_cliffordProdTensor_neg_one
    (hneg : (-1 : Module.End R R) * (-1) = 1)
    (hnegρ : ∀ v, (-1 : Module.End R R) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-1)))
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F (cliffordProdTensor ρ₁ (-1) hneg hnegρ ρ₂ a z) =
      ρ₂ (CliffordAlgebra.involute
        (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a))
        (TensorProduct.lid R F z) := by
  have h := congrArg (fun g ↦ g a (TensorProduct.lid R F z))
    (conjAlgEquiv_lid_cliffordProdTensor_neg_one ρ₁ ρ₂ hneg hnegρ)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end LeftUnit

section RightUnit

variable {R M₁ M₂ E : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [Unique M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R)

/-- When `M₂` is trivial, conjugating `cliffordProdTensor` by the right unitor
`E ⊗[R] R ≃ₗ[R] E` recovers `ρ₁` transported along `QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂`,
for any grading `γ` of `E`. -/
theorem conjAlgEquiv_rid_cliffordProdTensor :
    ((TensorProduct.rid R E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₁.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro e
  have hx : x.2 = 0 := Subsingleton.elim x.2 0
  simp [hx, LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, equivOfIsometry_apply]

/-- Pointwise right-unit law: for `[Unique M₂]` and any grading `γ` of `E`, the right unitor
`TensorProduct.rid R E` intertwines `cliffordProdTensor` with `ρ₁`. -/
theorem rid_cliffordProdTensor (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] R) :
    TensorProduct.rid R E (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₁ (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂) a)
        (TensorProduct.rid R E z) := by
  have h := congrArg (fun g ↦ g a (TensorProduct.rid R E z))
    (conjAlgEquiv_rid_cliffordProdTensor ρ₁ γ hγ hγρ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end RightUnit

end AlgHom
