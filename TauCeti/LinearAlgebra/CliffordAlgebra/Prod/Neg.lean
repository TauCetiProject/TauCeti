/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic

/-!
# Negating the grading in a graded tensor product of Clifford modules

Replacing the grading operator `γ` of `E` by `-γ` in `AlgHom.cliffordProdTensor` changes the
generator action `c₁(v) ⊗ 1 + γ ⊗ c₂(w)` into `c₁(v) ⊗ 1 - γ ⊗ c₂(w)`. Whenever `F` carries an
endomorphism `δ` anticommuting with every `c₂(w)`, `1 ⊗ δ` (`LinearMap.lTensor E δ`) intertwines
the `-γ`-graded tensor product action with the `γ`-graded one on the entire Clifford algebra
(`AlgHom.lTensor_comp_cliffordProdTensor_neg`), conjugating one into the other when `δ` is an
involution (`AlgHom.conjAlgEquiv_cliffordProdTensor_neg`).

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
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- With negated grading `-γ`, a vector `(v, w)` acts by `c₁(v) ⊗ 1 - γ ⊗ c₂(w)`. -/
theorem cliffordProdTensor_neg_ι (x : M₁ × M₂) :
    cliffordProdTensor ρ₁ (-γ) (by rw [neg_mul_neg, hγ])
        (fun v ↦ by rw [neg_mul, mul_neg, neg_neg, hγρ, neg_neg]) ρ₂ (ι (Q₁.prod Q₂) x) =
      (ρ₁ (ι Q₁ x.1)).rTensor F - TensorProduct.map γ (ρ₂ (ι Q₂ x.2)) :=
  TensorProduct.ext' fun _ _ ↦ by simp [cliffordProdTensor_ι_tmul, neg_tmul, sub_eq_add_neg]

/-- **Intertwining the negated-grading product action**: if `δ` anticommutes with every generator
of `Q₂` on `F`, then `1 ⊗ δ` intertwines the `-γ`-graded tensor product action with the `γ`-graded
one on every element of `CliffordAlgebra (Q₁.prod Q₂)`. No square-one assumption on `δ` is
needed. -/
theorem lTensor_comp_cliffordProdTensor_neg {δ : Module.End R F}
    (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ))
    (a : CliffordAlgebra (Q₁.prod Q₂)) :
    δ.lTensor E ∘ₗ cliffordProdTensor ρ₁ (-γ) (by rw [neg_mul_neg, hγ])
        (fun v ↦ by rw [neg_mul, mul_neg, neg_neg, hγρ, neg_neg]) ρ₂ a =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a ∘ₗ δ.lTensor E := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => ext z; simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    refine TensorProduct.ext' fun e f ↦ ?_
    have hf := LinearMap.congr_fun (hδρ v.2) f
    simp only [mul_apply_eq_comp, LinearMap.neg_apply] at hf
    simp [cliffordProdTensor_ι_tmul, hf, tmul_neg, neg_tmul]
  | add a b ha hb => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- When `δ` is an involution of `F` anticommuting with every generator of `Q₂`, conjugating by
`1 ⊗ δ` carries the `-γ`-graded tensor product action to the `γ`-graded one. -/
theorem conjAlgEquiv_cliffordProdTensor_neg {δ : Module.End R F}
    (hδ : Function.Involutive δ) (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ)) :
    (((LinearEquiv.ofInvolutive δ hδ).lTensor E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ (-γ) (by rw [neg_mul_neg, hγ])
          (fun v ↦ by rw [neg_mul, mul_neg, neg_neg, hγρ, neg_neg]) ρ₂) =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ := by
  refine AlgHom.ext fun a ↦ ?_
  have he : ((LinearEquiv.ofInvolutive δ hδ).lTensor E).toLinearMap = δ.lTensor E :=
    TensorProduct.ext' fun _ _ ↦ rfl
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    ← LinearMap.comp_assoc, eq_comm, LinearEquiv.eq_comp_toLinearMap_symm, eq_comm, he]
  exact lTensor_comp_cliffordProdTensor_neg ρ₁ γ hγ hγρ ρ₂ hδρ a

end AlgHom
