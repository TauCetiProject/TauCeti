/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Associativity of graded tensor products of Clifford modules

The native `TensorProduct.assoc` intertwines the two iterated graded Clifford actions after
reassociating the quadratic spaces with `QuadraticMap.IsometryEquiv.prodAssoc`. Thus a vector
`((v, w), z)` acts, in either parenthesization, by the sum of the three operators
`c₁(v) ⊗ 1 ⊗ 1`, `γ₁ ⊗ c₂(w) ⊗ 1`, and `γ₁ ⊗ γ₂ ⊗ c₃(z)`.
The intertwining holds for every Clifford element, not just for vectors.

Only the first two modules need grading operators to form these actions. If the third is graded
as well, the tensor gradings are intertwined by the same associator: this is the existing
`TensorProduct.map_map_assoc` applied to the three grading operators. No finiteness or
invertibility of two is needed.

The construction reuses Mathlib's `TensorProduct.assoc` and its pure-tensor equations, and the
universal property `CliffordAlgebra.hom_ext`; no new tensor equivalence is introduced.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open TensorProduct CliffordAlgebra

namespace AlgHom

variable {R M₁ M₂ M₃ E F G : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ₁ : Module.End R E)
  (hγ₁ : γ₁ * γ₁ = 1) (hγ₁ρ : ∀ v, γ₁ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ₁))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F) (γ₂ : Module.End R F)
  (hγ₂ : γ₂ * γ₂ = 1) (hγ₂ρ : ∀ w, γ₂ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * γ₂))
  (ρ₃ : CliffordAlgebra Q₃ →ₐ[R] Module.End R G)

/-- Conjugating the left-associated graded Clifford action by the native tensor associator
gives the right-associated action, with the Clifford algebra transported along the orthogonal
sum associator. -/
theorem conjAlgEquiv_cliffordProdTensor_assoc :
    let ρ₁₂ := cliffordProdTensor ρ₁ γ₁ hγ₁ hγ₁ρ ρ₂
    let ρ₂₃ := cliffordProdTensor ρ₂ γ₂ hγ₂ hγ₂ρ ρ₃
    ((TensorProduct.assoc R E F G).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁₂ (TensorProduct.map γ₁ γ₂)
          (by rw [← TensorProduct.map_mul, hγ₁, hγ₂, TensorProduct.map_one])
          (map_mul_cliffordProdTensor_ι ρ₁ γ₁ hγ₁ hγ₁ρ ρ₂ γ₂ hγ₂ρ) ρ₃) =
      (cliffordProdTensor ρ₁ γ₁ hγ₁ hγ₁ρ ρ₂₃).comp
        (equivOfIsometry (QuadraticMap.IsometryEquiv.prodAssoc Q₁ Q₂ Q₃)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  apply TensorProduct.ext_threefold'
  intro e f g
  simp [LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul,
    tmul_add, add_tmul, add_assoc]

/-- The native tensor associator intertwines the iterated graded actions on arbitrary Clifford
elements and arbitrary tensors. -/
-- This is a named rewrite: the source action contains the second grading laws only in proof
-- arguments.
theorem assoc_cliffordProdTensor (a : CliffordAlgebra ((Q₁.prod Q₂).prod Q₃))
    (t : (E ⊗[R] F) ⊗[R] G) :
    (TensorProduct.assoc R E F G)
        (cliffordProdTensor (cliffordProdTensor ρ₁ γ₁ hγ₁ hγ₁ρ ρ₂) (TensorProduct.map γ₁ γ₂)
          (by rw [← TensorProduct.map_mul, hγ₁, hγ₂, TensorProduct.map_one])
          (map_mul_cliffordProdTensor_ι ρ₁ γ₁ hγ₁ hγ₁ρ ρ₂ γ₂ hγ₂ρ) ρ₃ a t) =
      cliffordProdTensor ρ₁ γ₁ hγ₁ hγ₁ρ
        (cliffordProdTensor ρ₂ γ₂ hγ₂ hγ₂ρ ρ₃)
        (equivOfIsometry (QuadraticMap.IsometryEquiv.prodAssoc Q₁ Q₂ Q₃) a)
        ((TensorProduct.assoc R E F G) t) := by
  have h := congrArg (fun f ↦ f a ((TensorProduct.assoc R E F G) t))
    (conjAlgEquiv_cliffordProdTensor_assoc ρ₁ γ₁ hγ₁ hγ₁ρ ρ₂ γ₂ hγ₂ hγ₂ρ ρ₃)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end AlgHom
