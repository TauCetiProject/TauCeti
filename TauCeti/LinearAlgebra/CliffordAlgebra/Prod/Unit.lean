/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Left and right unit laws of graded Clifford tensor products

When the first quadratic space `M₁` is trivial (`Unique M₁`) and `E = R` carries the positive
grading `γ = 1`, the left unitor `TensorProduct.lid R F : R ⊗ F ≃ F` intertwines the graded
tensor product action of `CliffordAlgebra (Q₁.prod Q₂)` with the action of `CliffordAlgebra Q₂`
on `F`, transported along `QuadraticMap.IsometryEquiv.uniqueProd`. When `E = R` instead carries
the negative grading `γ = -1`, every vector of `M₂` acts with a minus sign, so `TensorProduct.lid`
intertwines the graded product with the grade-involuted action `ρ₂ ∘ involute`.

When the second quadratic space `M₂` is trivial (`Unique M₂`) and `F = R`, the right unitor
`TensorProduct.rid R E : E ⊗ R ≃ E` intertwines the graded tensor product action with the action
of `CliffordAlgebra Q₁` on `E` along `QuadraticMap.IsometryEquiv.prodUnique`, for every grading
`γ` of `E`.

No finiteness or invertibility of two is needed.

## Main results

* `AlgHom.conjAlgEquiv_cliffordProdTensor_lid`, `AlgHom.lid_cliffordProdTensor`: left unit for
  `γ = 1`.
* `AlgHom.conjAlgEquiv_cliffordProdTensor_lid_of_eq_neg_one`,
  `AlgHom.lid_cliffordProdTensor_of_eq_neg_one`: left unitor under `γ = -1` intertwines with
  `ρ₂ ∘ involute`.
* `AlgHom.conjAlgEquiv_cliffordProdTensor_rid`, `AlgHom.rid_cliffordProdTensor`: right unit for
  every grading `γ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open TensorProduct CliffordAlgebra

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

section LeftUnit

variable [Unique M₁]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R) (γ : Module.End R R)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- Conjugating the graded Clifford action on `R ⊗ F` by the left unitor `TensorProduct.lid`
yields the action of `CliffordAlgebra Q₂` on `F` when `M₁` is trivial and `γ = 1`. -/
theorem conjAlgEquiv_cliffordProdTensor_lid (hγ1 : γ = 1) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₂.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  ext f
  simp [LinearEquiv.conjAlgEquiv_apply, Subsingleton.elim x.1 0, hγ1]

/-- The left unitor `TensorProduct.lid` intertwines the graded Clifford action on `R ⊗ F` with the
action on `F` when `M₁` is trivial and `γ = 1`. -/
theorem lid_cliffordProdTensor (hγ1 : γ = 1) (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₂ (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a)
        (TensorProduct.lid R F z) := by
  have h := congrArg (fun f ↦ f a (TensorProduct.lid R F z))
    (conjAlgEquiv_cliffordProdTensor_lid ρ₁ γ hγ hγρ ρ₂ hγ1)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- When `M₁` is trivial and `E = R` carries the negative grading `γ = -1`, conjugating the graded
Clifford action on `R ⊗ F` by `TensorProduct.lid` yields the grade-involuted action
`ρ₂ ∘ involute` on `F`. -/
theorem conjAlgEquiv_cliffordProdTensor_lid_of_eq_neg_one (hγ1 : γ = -1) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      (ρ₂.comp involute).comp
        (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  ext f
  simp [LinearEquiv.conjAlgEquiv_apply, Subsingleton.elim x.1 0, hγ1]

/-- When `M₁` is trivial and `γ = -1`, the left unitor `TensorProduct.lid` intertwines the graded
Clifford action on `R ⊗ F` with the grade-involuted action `ρ₂ ∘ involute` on `F`. -/
theorem lid_cliffordProdTensor_of_eq_neg_one (hγ1 : γ = -1) (a : CliffordAlgebra (Q₁.prod Q₂))
    (z : R ⊗[R] F) :
    TensorProduct.lid R F (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₂ (involute (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a))
        (TensorProduct.lid R F z) := by
  have h := congrArg (fun f ↦ f a (TensorProduct.lid R F z))
    (conjAlgEquiv_cliffordProdTensor_lid_of_eq_neg_one ρ₁ γ hγ hγρ ρ₂ hγ1)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end LeftUnit

section RightUnit

variable [Unique M₂]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R)

/-- Conjugating the graded Clifford action on `E ⊗ R` by the right unitor `TensorProduct.rid`
yields the action of `CliffordAlgebra Q₁` on `E` when `M₂` is trivial. -/
theorem conjAlgEquiv_cliffordProdTensor_rid :
    ((TensorProduct.rid R E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₁.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  ext e
  simp [LinearEquiv.conjAlgEquiv_apply, Subsingleton.elim x.2 0]

/-- The right unitor `TensorProduct.rid` intertwines the graded Clifford action on `E ⊗ R` with
the action on `E` when `M₂` is trivial. -/
theorem rid_cliffordProdTensor (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] R) :
    TensorProduct.rid R E (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₁ (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂) a)
        (TensorProduct.rid R E z) := by
  have h := congrArg (fun f ↦ f a (TensorProduct.rid R E z))
    (conjAlgEquiv_cliffordProdTensor_rid ρ₁ γ hγ hγρ ρ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end RightUnit

end AlgHom
