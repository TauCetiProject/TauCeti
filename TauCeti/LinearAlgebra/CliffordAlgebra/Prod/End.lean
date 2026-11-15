/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
-- Private: tensor-product endomorphism equivalence, right exactness, and complementary-subspace
-- projections are used only inside the proofs of surjectivity and bijectivity.
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Surjectivity and bijectivity of the graded Clifford tensor product

When `E` and `F` are finite projective `R`-modules, `TensorProduct.homTensorHomEquiv` identifies
`End_R(E) ⊗_R End_R(F)` with `End_R(E ⊗_R F)`. Together with Mathlib's `CliffordAlgebra.prodEquiv`
and the parity decomposition `CliffordAlgebra Q₂ = evenOdd Q₂ 0 ⊕ evenOdd Q₂ 1`, the graded tensor
product `AlgHom.cliffordProdTensor` factors as a composite of `CliffordAlgebra.prodEquiv`, the
tensor product of `ρ₁` and `ρ₂` twisted on the odd summand of `CliffordAlgebra Q₂` by right
multiplication by the involution `γ`, and `TensorProduct.homTensorHomEquiv`.

Consequently, if `ρ₁` and `ρ₂` are surjective (respectively bijective), then
`AlgHom.cliffordProdTensor` is surjective (respectively bijective). In particular, the graded
tensor product of two spinor modules of even-dimensional Euclidean spaces is a spinor module of
their orthogonal sum.

## Main results

* `AlgHom.surjective_cliffordProdTensor`: `cliffordProdTensor` is surjective when `E` and `F` are
  finite projective and `ρ₁`, `ρ₂` are surjective.
* `AlgHom.bijective_cliffordProdTensor`: `cliffordProdTensor` is bijective when `E` and `F` are
  finite projective and `ρ₁`, `ρ₂` are bijective.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open CliffordAlgebra TensorProduct

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

variable {ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E} {γ : Module.End R E}
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  {ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F}

/-- Twisting `End_R(E) ⊗ CliffordAlgebra Q₂` by right multiplication by `γ` on the odd summand of
`CliffordAlgebra Q₂`. -/
private noncomputable def oddTwist (γ : Module.End R E) (Q₂ : QuadraticForm R M₂) :
    Module.End R E ⊗[R] CliffordAlgebra Q₂ →ₗ[R] Module.End R E ⊗[R] CliffordAlgebra Q₂ :=
  ((evenOdd Q₂ 0).projection (evenOdd Q₂ 1) (evenOdd_isCompl Q₂)).lTensor (Module.End R E) +
    map (LinearMap.mulRight R γ)
      ((evenOdd Q₂ 1).projection (evenOdd Q₂ 0) (evenOdd_isCompl Q₂).symm)

private theorem oddTwist_tmul_even (u : Module.End R E) {b : CliffordAlgebra Q₂}
    (hb : b ∈ evenOdd Q₂ 0) :
    oddTwist γ Q₂ (u ⊗ₜ b) = u ⊗ₜ b := by
  simp [oddTwist, Submodule.projection_apply_of_mem_left _ hb,
    Submodule.projection_apply_of_mem_right _ hb]

private theorem oddTwist_tmul_odd (u : Module.End R E) {b : CliffordAlgebra Q₂}
    (hb : b ∈ evenOdd Q₂ 1) :
    oddTwist γ Q₂ (u ⊗ₜ b) = (u * γ) ⊗ₜ b := by
  simp [oddTwist, Submodule.projection_apply_of_mem_right _ hb,
    Submodule.projection_apply_of_mem_left _ hb]

include hγ in
private theorem oddTwist_involutive : Function.Involutive (oddTwist γ Q₂) := fun z ↦ by
  induction z using TensorProduct.inductionOn with
  | tmul u b =>
    have hb₀ : (evenOdd Q₂ 0).projection (evenOdd Q₂ 1) (evenOdd_isCompl Q₂) b ∈ evenOdd Q₂ 0 :=
      Submodule.coe_mem _
    have hb₁ : (evenOdd Q₂ 1).projection (evenOdd Q₂ 0) (evenOdd_isCompl Q₂).symm b ∈
        evenOdd Q₂ 1 :=
      Submodule.coe_mem _
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self (evenOdd_isCompl Q₂) b]
    conv_rhs => rw [← Submodule.projection_add_projection_eq_self (evenOdd_isCompl Q₂) b]
    rw [tmul_add, map_add, map_add, oddTwist_tmul_even u hb₀, oddTwist_tmul_even u hb₀,
      oddTwist_tmul_odd u hb₁, oddTwist_tmul_odd (u * γ) hb₁, mul_assoc, hγ, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `oddTwist` as a linear equivalence. -/
private noncomputable def oddTwistEquiv :
    Module.End R E ⊗[R] CliffordAlgebra Q₂ ≃ₗ[R] Module.End R E ⊗[R] CliffordAlgebra Q₂ :=
  LinearEquiv.ofInvolutive (oddTwist γ Q₂) (oddTwist_involutive hγ)

/-- As a linear map on `(CliffordAlgebra Q₁) ⊗ (CliffordAlgebra Q₂)`, the composite of `toProd` and
`cliffordProdTensor` factors through `ρ₁ ⊗ 1`, `oddTwistEquiv`, `1 ⊗ ρ₂`, and
`homTensorHomEquiv`. -/
private theorem cliffordProdTensor_comp_toProd_comp_of
    [Module.Finite R E] [Module.Projective R E] [Module.Finite R F] [Module.Projective R F] :
    (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap ∘ₗ
        (toProd Q₁ Q₂).toLinearMap ∘ₗ
        (GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)).toLinearMap =
      (homTensorHomEquiv R E F E F).toLinearMap ∘ₗ
        ρ₂.toLinearMap.lTensor (Module.End R E) ∘ₗ
        (oddTwistEquiv hγ).toLinearMap ∘ₗ
        ρ₁.toLinearMap.rTensor (CliffordAlgebra Q₂) := by
  apply TensorProduct.ext'
  intro a b
  set b₀ := (evenOdd Q₂ 0).projection (evenOdd Q₂ 1) (evenOdd_isCompl Q₂) b
  set b₁ := (evenOdd Q₂ 1).projection (evenOdd Q₂ 0) (evenOdd_isCompl Q₂).symm b
  have hb₀ : b₀ ∈ evenOdd Q₂ 0 := Submodule.coe_mem _
  have hb₁ : b₁ ∈ evenOdd Q₂ 1 := Submodule.coe_mem _
  rw [← Submodule.projection_add_projection_eq_self (evenOdd_isCompl Q₂) b, tmul_add, map_add,
    map_add]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.coe_toLinearMap]
  have h0 := cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a hb₀
  have h1 := cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a hb₁
  simp only [ZMod.val_zero, pow_zero, mul_one] at h0
  simp only [ZMod.val_one, pow_one] at h1
  -- Expose `GradedTensorProduct.of R _ _ (a ⊗ₜ bᵢ)` as the graded pure tensor `a ᵍ⊗ₜ bᵢ`.
  change cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (toProd Q₁ Q₂ (a ᵍ⊗ₜ b₀)) +
      cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ (toProd Q₁ Q₂ (a ᵍ⊗ₜ b₁)) = _
  rw [h0, h1, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, oddTwistEquiv,
    LinearEquiv.coe_ofInvolutive, oddTwist_tmul_even _ hb₀, oddTwist_tmul_odd _ hb₁,
    LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
  rfl

/-- **Surjectivity of the graded Clifford tensor product**: if `E` and `F` are finite projective
`R`-modules and `ρ₁` and `ρ₂` are surjective onto `End_R(E)` and `End_R(F)`, then
`cliffordProdTensor` is surjective onto `End_R(E ⊗_R F)`. -/
theorem surjective_cliffordProdTensor
    [Module.Finite R E] [Module.Projective R E] [Module.Finite R F] [Module.Projective R F]
    (h₁ : Function.Surjective ρ₁) (h₂ : Function.Surjective ρ₂) :
    Function.Surjective (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) := by
  have hcomp : Function.Surjective
      ((cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap ∘ₗ
        (toProd Q₁ Q₂).toLinearMap ∘ₗ
        (GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)).toLinearMap) := by
    rw [cliffordProdTensor_comp_toProd_comp_of hγ hγρ]
    exact (homTensorHomEquiv R E F E F).surjective.comp <|
      (LinearMap.lTensor_surjective (Module.End R E) h₂).comp <|
        (oddTwistEquiv (Q₂ := Q₂) hγ).surjective.comp
          (LinearMap.rTensor_surjective (CliffordAlgebra Q₂) h₁)
  exact Function.Surjective.of_comp (g := _) hcomp

/-- **Bijectivity of the graded Clifford tensor product**: if `E` and `F` are finite projective
`R`-modules and `ρ₁` and `ρ₂` are bijective onto `End_R(E)` and `End_R(F)`, then
`cliffordProdTensor` is bijective onto `End_R(E ⊗_R F)`. -/
theorem bijective_cliffordProdTensor
    [Module.Finite R E] [Module.Projective R E] [Module.Finite R F] [Module.Projective R F]
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂) :
    Function.Bijective (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) := by
  let e₁ : CliffordAlgebra Q₁ ≃ₗ[R] Module.End R E := LinearEquiv.ofBijective ρ₁.toLinearMap h₁
  let e₂ : CliffordAlgebra Q₂ ≃ₗ[R] Module.End R F := LinearEquiv.ofBijective ρ₂.toLinearMap h₂
  have heq : (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap ∘ₗ
        (toProd Q₁ Q₂).toLinearMap ∘ₗ
        (GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)).toLinearMap =
      ((e₁.rTensor (CliffordAlgebra Q₂)).trans <|
        (oddTwistEquiv (Q₂ := Q₂) hγ).trans <|
          (e₂.lTensor (Module.End R E)).trans (homTensorHomEquiv R E F E F)).toLinearMap :=
    cliffordProdTensor_comp_toProd_comp_of hγ hγρ
  have hbij : Function.Bijective
      (((cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ : _ → _) ∘ (CliffordAlgebra.prodEquiv Q₁ Q₂).symm) ∘
        GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)) := by
    -- Identify the function composite with the linear-equivalence composite `heq`.
    change Function.Bijective ⇑((cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap ∘ₗ
      (toProd Q₁ Q₂).toLinearMap ∘ₗ
      (GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)).toLinearMap)
    rw [heq]
    exact LinearEquiv.bijective _
  have hbij' : Function.Bijective
      ((cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ : _ → _) ∘ (CliffordAlgebra.prodEquiv Q₁ Q₂).symm) :=
    (Function.Bijective.of_comp_iff _
      (GradedTensorProduct.of R (evenOdd Q₁) (evenOdd Q₂)).bijective).mp hbij
  exact (Function.Bijective.of_comp_iff _ (CliffordAlgebra.prodEquiv Q₁ Q₂).symm.bijective).mp hbij'

end AlgHom
