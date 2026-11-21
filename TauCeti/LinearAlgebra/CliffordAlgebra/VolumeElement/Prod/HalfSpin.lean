/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Eigenspace.Separation

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
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (o₂ : Orientation ℝ W (Fin m)) (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

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

private theorem tensorProduct_congr_ofEq_comp_map {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {T₁ : Module.End ℂ E} {T₂ : Module.End ℂ F}
    (hT₁ : Function.Involutive T₁) (hT₂ : Function.Involutive T₂) {μ₁ μ₂ ν : ℂ}
    (h₁ : μ₁ * μ₁ = 1) (h₂ : μ₂ * μ₂ = 1) (hν : ν * ν = 1) (h : μ₂ = ν) :
    (TensorProduct.congr (LinearEquiv.refl ℂ _)
        (LinearEquiv.ofEq _ _ (congrArg T₂.eigenspace h))).toLinearMap.comp
      (TensorProduct.map (eigenProjOfInvolutive hT₁ h₁) (eigenProjOfInvolutive hT₂ h₂)) =
      TensorProduct.map (eigenProjOfInvolutive hT₁ h₁) (eigenProjOfInvolutive hT₂ hν) := by
  subst h
  refine TensorProduct.ext' fun x y ↦ ?_
  simp

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
  exact Prod.ext rfl (LinearMap.congr_fun
    (tensorProduct_congr_ofEq_comp_map (ρ₁.involutive_complexVolume o₁ hQ₁)
      (ρ₂.involutive_complexVolume o₂ hQ₂) _ _ (one_mul 1) (neg_neg (1 : ℂ))) z)

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
  obtain ⟨p₁, p₂⟩ := p
  rw [complexProdTensorEigenspaceNegOneEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_symm, LinearEquiv.refl_symm,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    coe_complexProdTensorEigenspaceEquiv_symm_apply]
  congr 1
  induction p₂ using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
      LinearEquiv.ofEq_symm, TensorProduct.map_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, Submodule.subtype_apply, Submodule.subtype_apply,
      LinearEquiv.coe_ofEq_apply]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

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

/-- **Half-spin dimension of a graded tensor product of spinor modules**: when `ρ₁` and `ρ₂` are
bijective onto `End_ℂ E` and `End_ℂ F` and `n + m ≠ 0`, both half-spin spaces `(E ⊗ F)^±` have
dimension `2 ^ ((n + m) / 2 - 1)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂)
    (hnm : n + m ≠ 0)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  have hm : Even m := by
    simpa [Module.finrank_baseChange, Fact.out (p := finrank ℝ W = m)] using
      CliffordAlgebra.even_finrank_of_bijective (Q₂.baseChange ℂ) hρ₂
  have hfinE : FiniteDimensional ℂ E := Module.Finite.of_surjective_end ρ₁ hρ₁.2
  have hfinF : FiniteDimensional ℂ F := Module.Finite.of_surjective_end ρ₂ hρ₂.2
  have hdimE : finrank ℂ E = 2 ^ (n / 2) := by
    simpa [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)] using
      CliffordAlgebra.finrank_eq_two_pow_of_bijective (Q₁.baseChange ℂ) hρ₁
  have hdimF : finrank ℂ F = 2 ^ (m / 2) := by
    simpa [Module.finrank_baseChange, Fact.out (p := finrank ℝ W = m)] using
      CliffordAlgebra.finrank_eq_two_pow_of_bijective (Q₂.baseChange ℂ) hρ₂
  have hμ2 : μ * μ = 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hnegμ : -μ = 1 ∨ -μ = -1 := by
    rcases hμ with rfl | rfl; · exact Or.inr rfl
    · exact Or.inl (neg_neg 1)
  rw [finrank_eigenspace_complexProdTensor_complexVolume hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hQ₂ hm ho hμ2]
  by_cases hn0 : n = 0
  · have hm0 : m ≠ 0 := by omega
    have hsumE : finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) = 2 ^ (n / 2) := by
      rw [Submodule.finrank_add_eq_of_isCompl (ρ₁.isCompl_eigenspace_complexVolume o₁ hQ₁), hdimE]
    rw [ρ₂.finrank_eigenspace_complexVolume_of_bijective o₂ hQ₂ hρ₂ hm0 hμ,
      ρ₂.finrank_eigenspace_complexVolume_of_bijective o₂ hQ₂ hρ₂ hm0 hnegμ,
      ← Nat.add_mul, hsumE, hn0]
    simp
  · have hcomplF : IsCompl ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ)
        ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
      have h := ρ₂.isCompl_eigenspace_complexVolume o₂ hQ₂
      rcases hμ with rfl | rfl; · exact h
      · rw [neg_neg]; exact h.symm
    have hsumF : finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) = 2 ^ (m / 2) := by
      rw [Submodule.finrank_add_eq_of_isCompl hcomplF, hdimF]
    rw [ρ₁.finrank_eigenspace_complexVolume_of_bijective o₁ hQ₁ hρ₁ hn0 (Or.inl rfl),
      ρ₁.finrank_eigenspace_complexVolume_of_bijective o₁ hQ₁ hρ₁ hn0 (Or.inr rfl),
      ← Nat.mul_add, hsumF, ← pow_add]
    obtain ⟨k, rfl⟩ := hn; obtain ⟨l, rfl⟩ := hm; congr 1; omega

end CliffordAlgebra
