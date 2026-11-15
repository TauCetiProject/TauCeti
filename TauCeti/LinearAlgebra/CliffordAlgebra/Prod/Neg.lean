/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic

/-!
# Reversing the grading of the first factor in a graded Clifford tensor product

If `γ` is a grading operator of a `CliffordAlgebra Q₁`-module `E` — an involution anticommuting
with every vector — then `-γ` is again a grading operator of `E`. Replacing `γ` by `-γ` in
`AlgHom.cliffordProdTensor` leaves the action `c₁(v) ⊗ 1` of the first summand unchanged and
negates the action `γ ⊗ c₂(w)` of every vector `(0, w)` of the second summand.

When the second factor `F` carries an endomorphism `δ` anticommuting with every vector `c₂(w)`,
the operator `1 ⊗ δ` (`LinearMap.lTensor E δ`) intertwines the graded tensor product for `-γ` with
that for `γ` on the whole Clifford algebra `CliffordAlgebra (Q₁.prod Q₂)`: it fixes `c₁(v) ⊗ 1`
because the two factors commute, and it negates `γ ⊗ c₂(w)` because `δ` anticommutes with `c₂(w)`.
When `δ` is moreover an involution, conjugation by `1 ⊗ δ` identifies the two algebra maps.

For oriented Euclidean spaces, reversing the orientation of an even-dimensional space `V` negates
its chirality `Γ_V`, so `1 ⊗ Γ_W` intertwines the two product actions when `W` is even-dimensional;
similarly, when `dim V ≡ 2 (mod 4)` the reverse-dual chirality `Γ_(E*) = -Γ_Eᵀ` differs by a sign
from the transpose grading, and `1 ⊗ Γ_(F*)` restores the sign in the tensor-dual pairing.

## Main results

* `AlgHom.cliffordProdTensor_neg_ι` and `AlgHom.cliffordProdTensor_neg_ι_inr`: negating `γ`
  negates the action of the second summand's vectors.
* `AlgHom.lTensor_comp_cliffordProdTensor_neg` and `AlgHom.lTensor_cliffordProdTensor_neg`: if `δ`
  anticommutes with every `c₂(w)`, then `1 ⊗ δ` intertwines the `-γ` and `γ` product actions.
* `AlgHom.conjAlgEquiv_cliffordProdTensor_neg`: when `δ` is also an involution, conjugation by
  `1 ⊗ δ` carries the `-γ` product action to the `γ` product action.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra TensorProduct

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

variable (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- With the negated grading `-γ`, a vector `(v, w)` acts by `c₁(v) ⊗ 1 - γ ⊗ c₂(w)`. -/
theorem cliffordProdTensor_neg_ι (hneg : (-γ) * (-γ) = 1)
    (hnegρ : ∀ v, (-γ) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-γ))) (x : M₁ × M₂) :
    cliffordProdTensor ρ₁ (-γ) hneg hnegρ ρ₂ (ι (Q₁.prod Q₂) x) =
      (ρ₁ (ι Q₁ x.1)).rTensor F - map γ (ρ₂ (ι Q₂ x.2)) := by
  apply TensorProduct.ext'
  intro e f
  simp [cliffordProdTensor_ι_tmul, neg_tmul, sub_eq_add_neg]

/-- With the negated grading `-γ`, a vector `(0, w)` of the second summand acts by
`-γ ⊗ c₂(w)`. -/
theorem cliffordProdTensor_neg_ι_inr (hneg : (-γ) * (-γ) = 1)
    (hnegρ : ∀ v, (-γ) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-γ))) (w : M₂) :
    cliffordProdTensor ρ₁ (-γ) hneg hnegρ ρ₂ (ι (Q₁.prod Q₂) (0, w)) =
      -map γ (ρ₂ (ι Q₂ w)) := by
  apply TensorProduct.ext'
  intro e f
  simp [cliffordProdTensor_ι_inr, neg_tmul]

/-- **Intertwining the negated grading by `1 ⊗ δ`**: if `δ` anticommutes with every generating
vector `c₂(w)` on `F`, then `1 ⊗ δ` (`δ.lTensor E`) intertwines the graded tensor product for `-γ`
with that for `γ` on every element of `CliffordAlgebra (Q₁.prod Q₂)`. No involutivity of `δ` is
required. -/
theorem lTensor_comp_cliffordProdTensor_neg (hneg : (-γ) * (-γ) = 1)
    (hnegρ : ∀ v, (-γ) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-γ))) (δ : Module.End R F)
    (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ)) (a : CliffordAlgebra (Q₁.prod Q₂)) :
    δ.lTensor E ∘ₗ cliffordProdTensor ρ₁ (-γ) hneg hnegρ ρ₂ a =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a ∘ₗ δ.lTensor E := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    ext z
    simp [Algebra.algebraMap_eq_smul_one]
  | ι x =>
    apply TensorProduct.ext'
    intro e f
    have hδ := LinearMap.congr_fun (hδρ x.2) f
    simp only [mul_apply_eq_comp, LinearMap.neg_apply] at hδ
    simp [cliffordProdTensor_ι_tmul, hδ, tmul_neg, neg_tmul]
  | add a b ha hb =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- Pointwise form of `AlgHom.lTensor_comp_cliffordProdTensor_neg`: if `δ` anticommutes with every
vector `c₂(w)`, then `(1 ⊗ δ) (a ·₋ z) = a ·₊ ((1 ⊗ δ) z)`. -/
theorem lTensor_cliffordProdTensor_neg (hneg : (-γ) * (-γ) = 1)
    (hnegρ : ∀ v, (-γ) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-γ))) (δ : Module.End R F)
    (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ))
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] F) :
    δ.lTensor E (cliffordProdTensor ρ₁ (-γ) hneg hnegρ ρ₂ a z) =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a (δ.lTensor E z) :=
  LinearMap.congr_fun (lTensor_comp_cliffordProdTensor_neg ρ₁ γ hγ hγρ ρ₂ hneg hnegρ δ hδρ a) z

/-- **Conjugating away a grading sign**: when `δ` is an involution anticommuting with every vector
`c₂(w)`, conjugating by `1 ⊗ δ` carries the `-γ` graded tensor product to the `γ` graded tensor
product as algebra homomorphisms. -/
theorem conjAlgEquiv_cliffordProdTensor_neg (hneg : (-γ) * (-γ) = 1)
    (hnegρ : ∀ v, (-γ) * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * (-γ))) (δ : Module.End R F)
    (hδ : Function.Involutive δ) (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ)) :
    (((LinearEquiv.ofInvolutive δ hδ).lTensor E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ (-γ) hneg hnegρ ρ₂) =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  apply TensorProduct.ext'
  intro e f
  have hsymm : (LinearEquiv.ofInvolutive δ hδ).symm f = δ f := rfl
  have hδ' := LinearMap.congr_fun (hδρ x.2) (δ f)
  simp only [mul_apply_eq_comp, LinearMap.neg_apply, hδ f] at hδ'
  simp [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.lTensor, LinearEquiv.coe_ofInvolutive, hsymm,
    cliffordProdTensor_ι_tmul, hδ f, hδ', tmul_neg, neg_tmul]

end AlgHom
