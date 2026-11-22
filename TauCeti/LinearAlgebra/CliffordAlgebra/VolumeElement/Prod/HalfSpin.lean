/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution

/-!
# Half-spin decomposition of graded Clifford tensor products

Decomposes the `±1`-eigenspaces of the product chirality `Γ_(V ⊕ W)` on `E ⊗ F` as
`(E ⊗ F)^μ ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))`, and proves the corresponding complex dimension
formulas `dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^(-μ)` and `2 ^ ((n + m) / 2 - 1)` for
spinor modules.

## Main definitions and results

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: half-spin decomposition of the
  `μ`-eigenspace of `Γ_(V ⊕ W)`.
* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv_apply` and
  `CliffordAlgebra.coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply`: forward and
  inverse maps of the half-spin equivalence.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume`: dimension formula in terms
  of the factors' eigenspaces.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume_of_bijective`: half-spin
  dimension `2 ^ ((n + m) / 2 - 1)` for tensor products of spinor modules.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-! ### Half-spin eigenspace decomposition -/

section HalfSpin

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

section Eigenspace

variable (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
  (ho : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
    (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
  {μ : ℂ} (hμ : μ * μ = 1)

/-- **Half-spin decomposition of the graded tensor product.** For even-dimensional `(V, o₁)` and
`(W, o₂)` with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, the `μ`-eigenspace (`μ * μ = 1`) of `Γ_(V ⊕ W)`
on `E ⊗ F` is linearly isomorphic to `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))`. -/
def complexProdTensorComplexVolumeEigenspaceEquiv :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ ≃ₗ[ℂ]
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) :=
  (LinearEquiv.ofEq _ _
      (congrArg (fun f ↦ Module.End.eigenspace f μ)
        (complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho))).trans
    (Module.End.eigenspaceTensorMapEquiv
      (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂) hμ)

/-- Forward map of `complexProdTensorComplexVolumeEigenspaceEquiv`. -/
@[simp]
theorem complexProdTensorComplexVolumeEigenspaceEquiv_apply
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) :
    complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho hμ z =
      (TensorProduct.map
          (Module.End.eigenProjOfInvolutive (ρ₁.involutive_complexVolume o₁ hQ₁)
            (one_mul 1))
          (Module.End.eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂) hμ) z.val,
        TensorProduct.map
          (Module.End.eigenProjOfInvolutive (ρ₁.involutive_complexVolume o₁ hQ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (Module.End.eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂)
            ((neg_mul_neg μ μ).trans hμ)) z.val) := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_apply,
    Module.End.eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- Inverse of `complexProdTensorComplexVolumeEigenspaceEquiv`. -/
@[simp]
theorem coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
            (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
          ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
            (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ))) :
    ((complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho hμ).symm p :
        E ⊗[ℂ] F) =
      TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ).subtype p.fst +
        TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)).subtype p.snd := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    Module.End.coe_eigenspaceTensorMapEquiv_symm_apply]

include hm hQ₂ ho hμ in
/-- Dimension of the `μ`-eigenspace (`μ * μ = 1`) of `Γ_(V ⊕ W)` on `E ⊗ F`:
`dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^(-μ)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
  rw [(complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm hQ₂ ho
      hμ).finrank_eq,
    Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct]

end Eigenspace

omit [Fact (finrank ℝ W = m)] in
/-- **Half-spin dimension of `S_V ⊗ S_W`.** When `E` and `F` are spinor modules (`ρ₁`, `ρ₂`
bijective) and `n + m ≠ 0`, both the `±1`-eigenspaces of `Γ_(V ⊕ W)` on `E ⊗ F` have complex
dimension `2 ^ ((n + m) / 2 - 1)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hnm : n + m ≠ 0)
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂)
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  -- Equip `E ⊗ F` with the `CliffordAlgebra (Q.baseChange ℂ)`-module structure induced by
  -- `complexProdTensor` so `finrank_eigenspace_complexVolume_of_bijective_lsmul` applies.
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    Module.compHom (E ⊗[ℂ] F) (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).toRingHom
  have hsmul (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
      a • z = complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z := rfl
  have : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    ⟨fun c a z ↦ by rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have hlsmul : (Algebra.lsmul ℂ ℂ (E ⊗[ℂ] F) :
      CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F)) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ :=
    AlgHom.ext fun a ↦ LinearMap.ext fun z ↦ hsmul a z
  rw [← hlsmul]
  exact finrank_eigenspace_complexVolume_of_bijective_lsmul o
    (QuadraticForm.withLpProd_eq_neg_norm_sq hQ hQ₁ hQ₂)
    (hlsmul.symm ▸ complexProdTensor_bijective hQ o₁ hQ₁ hn ρ₁ ρ₂ hρ₁ hρ₂) hnm hμ

end HalfSpin

end CliffordAlgebra
