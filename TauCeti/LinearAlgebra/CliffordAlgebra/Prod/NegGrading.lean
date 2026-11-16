/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic

/-!
# Negating the grading of a graded Clifford tensor product

Let `E` and `F` be Clifford modules over `Q₁` and `Q₂`, with grading `γ` on `E`. Replacing `γ` by
`-γ` leaves the action of `M₁` unchanged and negates the action of `M₂`:
`c(v, w) = c₁(v) ⊗ 1 - γ ⊗ c₂(w)`.

Whenever `F` carries an endomorphism `δ` anticommuting with every `c₂(w)`, the map
`1 ⊗ δ = δ.lTensor E` intertwines the action graded by `-γ` with the action graded by `γ`, because
`δ` commutes with `1` on the first summand and reverses the sign of `c₂(w)` on the second. No
involutivity of `δ`, finiteness, or invertibility of two is required for the intertwining itself.
When `δ` is an involution, `(LinearEquiv.ofInvolutive δ hδ).lTensor E` conjugates the two actions.

This single mechanism underlies both orientation reversal of the first factor and the sign change
in reverse duality of `complexProdTensor` in dimensions `2ℓ` with `ℓ` odd.

## Main results

* `AlgHom.lTensor_cliffordProdTensor_of_eq_neg`: `1 ⊗ δ` intertwines the graded product actions
  for `γ' = -γ` and `γ`.
* `AlgHom.lTensor_cliffordProdTensor_of_eq_neg_apply`: pointwise form on `E ⊗ F`.
* `AlgHom.conjAlgEquiv_cliffordProdTensor_lTensor_of_eq_neg`: conjugation form when `δ` is
  involutive.

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

/-- If `δ` anticommutes with every generator of `CliffordAlgebra Q₂` on `F`, then `1 ⊗ δ`
intertwines the graded product action using `γ' = -γ` with that using `γ`. No involutivity of `δ`
is required. -/
theorem lTensor_cliffordProdTensor_of_eq_neg
    {γ' : Module.End R E} (hγ' : γ' * γ' = 1)
    (hγ'ρ : ∀ v, γ' * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ')) (hneg : γ' = -γ)
    (δ : Module.End R F) (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ))
    (a : CliffordAlgebra (Q₁.prod Q₂)) :
    δ.lTensor E ∘ₗ cliffordProdTensor ρ₁ γ' hγ' hγ'ρ ρ₂ a =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a ∘ₗ δ.lTensor E := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => ext e f; simp
  | ι x =>
    apply TensorProduct.ext'
    intro e f
    have hδw := LinearMap.congr_fun (hδρ x.2) f
    simp only [mul_apply_eq_comp, LinearMap.neg_apply] at hδw
    simp [hneg, hδw, neg_tmul, tmul_neg]
  | add a b ha hb =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- Pointwise form of `AlgHom.lTensor_cliffordProdTensor_of_eq_neg`: `1 ⊗ δ` intertwines the
graded product actions for `γ' = -γ` and `γ`. -/
theorem lTensor_cliffordProdTensor_of_eq_neg_apply
    {γ' : Module.End R E} (hγ' : γ' * γ' = 1)
    (hγ'ρ : ∀ v, γ' * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ')) (hneg : γ' = -γ)
    (δ : Module.End R F) (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ))
    (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] F) :
    δ.lTensor E (cliffordProdTensor ρ₁ γ' hγ' hγ'ρ ρ₂ a z) =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a (δ.lTensor E z) :=
  LinearMap.congr_fun
    (lTensor_cliffordProdTensor_of_eq_neg ρ₁ γ hγ hγρ ρ₂ hγ' hγ'ρ hneg δ hδρ a) z

/-- When `δ` is an involution anticommuting with every generator of `CliffordAlgebra Q₂` on `F`,
conjugation by `1 ⊗ δ` carries the graded product action using `γ' = -γ` to that using `γ`. -/
theorem conjAlgEquiv_cliffordProdTensor_lTensor_of_eq_neg
    {γ' : Module.End R E} (hγ' : γ' * γ' = 1)
    (hγ'ρ : ∀ v, γ' * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ')) (hneg : γ' = -γ)
    (δ : Module.End R F) (hδ : Function.Involutive δ)
    (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ)) :
    (((LinearEquiv.ofInvolutive δ hδ).lTensor E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ' hγ' hγ'ρ ρ₂) =
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ := by
  apply AlgHom.ext
  intro a
  apply LinearMap.ext
  intro z
  set e := (LinearEquiv.ofInvolutive δ hδ).lTensor E
  have hcoe : (e : E ⊗[R] F →ₗ[R] E ⊗[R] F) = δ.lTensor E := by
    apply TensorProduct.ext'
    intro x y
    rfl
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply]
  have h := lTensor_cliffordProdTensor_of_eq_neg_apply ρ₁ γ hγ hγρ ρ₂ hγ' hγ'ρ hneg δ hδρ a
    (e.symm z)
  rw [← hcoe] at h
  simpa [e.apply_symm_apply] using h

end AlgHom
