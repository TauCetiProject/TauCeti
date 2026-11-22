/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Half-spin decomposition of the graded tensor product of Clifford modules

For even-dimensional oriented real inner product spaces `V` and `W` with `Q₁ v = -‖v‖²`,
`Q₂ w = -‖w‖²`, and the transported product orientation `o` on `V ⊕ W`, `Γ_(V ⊕ W)` acts on
`E ⊗ F` as `Γ_V ⊗ Γ_W`. Since `Γ_V` and `Γ_W` are involutions, `Module.End.eigenspaceTensorMapEquiv`
decomposes the `μ`-eigenspace (`μ * μ = 1`) without finiteness or irreducibility assumptions:

* `CliffordAlgebra.complexProdTensorEigenspaceEquiv`:
  `Eig(Γ_(V ⊕ W), μ) ≃ (E⁺ ⊗ Eig(Γ_W, μ)) × (E⁻ ⊗ Eig(Γ_W, -μ))` (`(E ⊗ F)⁺ ≃ (E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)`
  at `μ = 1`).
* `CliffordAlgebra.complexProdTensorEigenspaceNegOneEquiv`:
  `(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`.
* `CliffordAlgebra.bijective_complexProdTensor`: the graded tensor product of two spinor modules
  is again a spinor module.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume` and
  `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume_of_bijective`: finite-rank
  formula and half-spin dimension `2 ^ ((n + m) / 2 - 1)` for spinor modules when `n + m ≠ 0`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

section Decomposition

variable (o₂ : Orientation ℝ W (Fin m)) (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

/-- **Half-spin decomposition of `E ⊗ F`**: for even-dimensional `V` and `W` with `Q₁ v = -‖v‖²`,
`Q₂ w = -‖w‖²`, the ordered product orientation `o` on `V ⊕ W`, and `μ * μ = 1`, the `μ`-eigenspace
of `Γ_(V ⊕ W)` on `E ⊗ F` splits as `(E⁺ ⊗ Eig(Γ_W, μ)) × (E⁻ ⊗ Eig(Γ_W, -μ))`. -/
def complexProdTensorEigenspaceEquiv (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ ≃ₗ[ℂ]
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ] (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) :=
  (LinearEquiv.ofEq _ _ (congrArg (Module.End.eigenspace · μ)
      (complexProdTensor_complexVolume_of_map_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm ho))).trans
    (eigenspaceTensorMapEquiv (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂) hμ)

/-- The forward map of `CliffordAlgebra.complexProdTensorEigenspaceEquiv` projects onto
the two complementary tensor summands via `Module.End.eigenProjOfInvolutive`. -/
@[simp]
theorem complexProdTensorEigenspaceEquiv_apply (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (hm : Even m) (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1)
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) :
    complexProdTensorEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho hμ z =
      (TensorProduct.map
          (eigenProjOfInvolutive (ρ₁.involutive_complexVolume o₁ hQ₁) (one_mul 1))
          (eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂) hμ) z,
        TensorProduct.map
          (eigenProjOfInvolutive (ρ₁.involutive_complexVolume o₁ hQ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂)
            ((neg_mul_neg μ μ).trans hμ)) z) := by
  rw [complexProdTensorEigenspaceEquiv, LinearEquiv.trans_apply,
    eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- The inverse of `CliffordAlgebra.complexProdTensorEigenspaceEquiv` adds the two
tensor products of the half-spin submodule inclusions. -/
@[simp]
theorem coe_complexProdTensorEigenspaceEquiv_symm_apply (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (hm : Even m) (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1)
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ] (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
        (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ))) :
    ((complexProdTensorEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho hμ).symm p :
        E ⊗[ℂ] F) =
      TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ).subtype p.1 +
        TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)).subtype p.2 := by
  rw [complexProdTensorEigenspaceEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    coe_eigenspaceTensorMapEquiv_symm_apply]

/-- **Negative half-spin decomposition of `E ⊗ F`**: `(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`. -/
def complexProdTensorEigenspaceNegOneEquiv (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace (-1) ≃ₗ[ℂ]
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ] (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-1)) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace 1) :=
  (complexProdTensorEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho
      ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1))).trans
    ((LinearEquiv.refl ℂ _).prodCongr
      (TensorProduct.congr (LinearEquiv.refl ℂ _)
        (LinearEquiv.ofEq _ _
          (congrArg (ρ₂ (complexVolume Q₂ o₂)).eigenspace (neg_neg (1 : ℂ))))))

/-- The forward map of `CliffordAlgebra.complexProdTensorEigenspaceNegOneEquiv` projects onto
`E⁺ ⊗ F⁻` and `E⁻ ⊗ F⁺`. -/
@[simp]
theorem complexProdTensorEigenspaceNegOneEquiv_apply (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace (-1)) :
    complexProdTensorEigenspaceNegOneEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho z =
      (TensorProduct.map
          (eigenProjOfInvolutive (ρ₁.involutive_complexVolume o₁ hQ₁) (one_mul 1))
          (eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1))) z,
        TensorProduct.map
          (eigenProjOfInvolutive (ρ₁.involutive_complexVolume o₁ hQ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂) (one_mul 1)) z) := by
  rw [complexProdTensorEigenspaceNegOneEquiv, LinearEquiv.trans_apply,
    complexProdTensorEigenspaceEquiv_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  refine Prod.ext rfl ?_
  dsimp only
  rw [← LinearEquiv.coe_toLinearMap, TensorProduct.toLinearMap_congr,
    LinearEquiv.refl_toLinearMap, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.id_comp, ofEq_comp_eigenProjOfInvolutive (ρ₂.involutive_complexVolume o₂ hQ₂)
      _ (one_mul 1) (neg_neg (1 : ℂ))]

/-- The inverse of `CliffordAlgebra.complexProdTensorEigenspaceNegOneEquiv` adds the two
tensor products of the half-spin submodule inclusions. -/
@[simp]
theorem coe_complexProdTensorEigenspaceNegOneEquiv_symm_apply
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
        (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-1)) ×
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
        (ρ₂ (complexVolume Q₂ o₂)).eigenspace 1)) :
    ((complexProdTensorEigenspaceNegOneEquiv
        hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho).symm p : E ⊗[ℂ] F) =
      TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-1)).subtype p.1 +
        TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace 1).subtype p.2 := by
  rw [complexProdTensorEigenspaceNegOneEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_symm, LinearEquiv.refl_symm,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    coe_complexProdTensorEigenspaceEquiv_symm_apply]
  congr 1
  dsimp only
  rw [TensorProduct.congr_symm, LinearEquiv.refl_symm, LinearEquiv.ofEq_symm,
    ← LinearEquiv.ofEq_rfl (p := (ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)),
    ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
    TensorProduct.map_subtype_comp_congr_ofEq]

/-- **Half-spin dimension formula for finite-dimensional modules**: for `μ * μ = 1`,
`dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^(-μ)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
  rw [(complexProdTensorEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho hμ).finrank_eq,
    Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct]

end Decomposition

/-- **The graded tensor product of spinor modules is a spinor module**: when `ρ₁` and `ρ₂` are
bijective onto `End_ℂ E` and `End_ℂ F`, `complexProdTensor` is bijective onto `End_ℂ (E ⊗ F)`. -/
theorem bijective_complexProdTensor (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    Function.Bijective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  rw [complexProdTensor_eq_comp]
  exact (AlgHom.bijective_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂
      hρ₁ hρ₂).comp
    (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).bijective

/-- **Half-spin dimension of a graded tensor product of spinor modules**: when `ρ₁` and `ρ₂` are
bijective onto `End_ℂ E` and `End_ℂ F` and `n + m ≠ 0`, both half-spin spaces `(E ⊗ F)^±` have
dimension `2 ^ ((n + m) / 2 - 1)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂)
    (hnm : n + m ≠ 0) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) :=
  AlgHom.finrank_eigenspace_complexVolume_of_bijective
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) o
    (QuadraticMap.apply_eq_neg_norm_sq_of_withLp_prod Q hQ hQ₁ hQ₂)
    (bijective_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ hρ₁ hρ₂) hnm hμ

end CliffordAlgebra
