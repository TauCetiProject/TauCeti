/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Unit laws for the graded tensor product of Clifford modules

When one quadratic summand in `Q₁.prod Q₂` is trivial, its generators vanish in the Clifford
algebra, and `TensorProduct.lid` and `TensorProduct.rid` compare `AlgHom.cliffordProdTensor` with
the action on the remaining factor:

* **Left unit** (`Unique M₁`): grading `R` by `1` makes `lid R F` intertwine `cliffordProdTensor`
  with `ρ₂` along `QuadraticMap.IsometryEquiv.uniqueProd`
  (`AlgHom.conjAlgEquiv_cliffordProdTensor_uniqueProd`, `AlgHom.lid_cliffordProdTensor`), whereas
  grading `R` by `-1` negates every vector of `M₂` (`AlgHom.lid_cliffordProdTensor_neg_one_ι_inr`).
* **Right unit** (`Unique M₂`): `rid R E` intertwines `cliffordProdTensor` with `ρ₁` along
  `QuadraticMap.IsometryEquiv.prodUnique` for any grading `γ` on `E`
  (`AlgHom.conjAlgEquiv_cliffordProdTensor_prodUnique`, `AlgHom.rid_cliffordProdTensor`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open TensorProduct CliffordAlgebra

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- **Left unit of the graded tensor product**: when `M₁` is trivial and `R` is graded by `1`,
conjugating by the left unitor `TensorProduct.lid R F` identifies `AlgHom.cliffordProdTensor` with
`ρ₂` transported along `QuadraticMap.IsometryEquiv.uniqueProd`. -/
theorem conjAlgEquiv_cliffordProdTensor_uniqueProd [Unique M₁]
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F) :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ 1 (mul_one 1)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂) =
      ρ₂.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun ⟨x₁, x₂⟩ ↦ LinearMap.ext fun f ↦ ?_
  rw [Subsingleton.elim x₁ 0]
  simp [LinearEquiv.conjAlgEquiv_apply, equivOfIsometry_apply]

/-- The left unitor `TensorProduct.lid R F` intertwines the positively graded left-unit tensor
product action with `ρ₂`. -/
theorem lid_cliffordProdTensor [Unique M₁]
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F
        (cliffordProdTensor ρ₁ 1 (mul_one 1)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂ a z) =
      ρ₂ (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a)
        (TensorProduct.lid R F z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    congrArg (fun g ↦ g a (TensorProduct.lid R F z))
      (conjAlgEquiv_cliffordProdTensor_uniqueProd ρ₁ ρ₂)

/-- Grading the trivial left factor `R` by `-1` instead of `1` negates the action of every vector
of `M₂` under `TensorProduct.lid R F`, so the unitor does not intertwine the two actions when a
vector acts nontrivially. -/
theorem lid_cliffordProdTensor_neg_one_ι_inr [Subsingleton M₁]
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F) (w : M₂) (z : R ⊗[R] F) :
    TensorProduct.lid R F
        (cliffordProdTensor ρ₁ (-1) (by ext; simp)
          (fun v ↦ by simp [Subsingleton.elim v 0]) ρ₂
          (ι (Q₁.prod Q₂) (0, w)) z) =
      -ρ₂ (ι Q₂ w) (TensorProduct.lid R F z) := by
  rw [cliffordProdTensor_ι_inr]
  induction z using TensorProduct.inductionOn with
  | tmul r f => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

/-- **Right unit of the graded tensor product**: when `M₂` is trivial, conjugating by the right
unitor `TensorProduct.rid R E` identifies `AlgHom.cliffordProdTensor` with `ρ₁` transported along
`QuadraticMap.IsometryEquiv.prodUnique`, for any grading `γ` on `E`. -/
theorem conjAlgEquiv_cliffordProdTensor_prodUnique [Unique M₂]
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
    (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R) :
    ((TensorProduct.rid R E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₁.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun ⟨x₁, x₂⟩ ↦ LinearMap.ext fun e ↦ ?_
  rw [Subsingleton.elim x₂ 0]
  simp [LinearEquiv.conjAlgEquiv_apply, equivOfIsometry_apply]

/-- The right unitor `TensorProduct.rid R E` intertwines the right-unit graded tensor product
action with `ρ₁`. -/
theorem rid_cliffordProdTensor [Unique M₂]
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
    (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R)
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] R) :
    TensorProduct.rid R E (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₁ (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂) a)
        (TensorProduct.rid R E z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    congrArg (fun g ↦ g a (TensorProduct.rid R E z))
      (conjAlgEquiv_cliffordProdTensor_prodUnique ρ₁ γ hγ hγρ ρ₂)

end AlgHom
