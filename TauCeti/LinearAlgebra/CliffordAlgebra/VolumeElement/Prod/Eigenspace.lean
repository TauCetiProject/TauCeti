/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Half-spin decomposition of the graded tensor product of Clifford modules

Let `V` and `W` be even-dimensional oriented real inner product spaces of dimensions `n` and `m`
with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and equip `V ⊕ W` with `Orientation.prod o₁ o₂`. Since
`Γ_(V ⊕ W)` acts on `E ⊗ F` as `Γ_V ⊗ Γ_W`, `Module.End.eigenspaceTensorMapEquiv` decomposes its
`μ`-eigenspace (`μ * μ = 1`) as `(E ⊗ F)^μ ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})` without finiteness
assumptions on `E` or `F`. For finite-dimensional modules this gives the rank formula, and for
spinor modules with `n + m ≠ 0` it gives `dim (S_V ⊗ S_W)^± = 2 ^ ((n + m) / 2 - 1)` (in
particular `1 + 1 = 2` inside `dim = 4` for two oriented planes `n = m = 2`).

## Main definitions

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`:
  `(E ⊗ F)^μ ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})` for `μ * μ = 1`.

## Main results

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv_apply` and
  `CliffordAlgebra.coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply`: projection and
  inclusion formulas.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume` and
  `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume_of_bijective_lsmul`: general
  and spinor half-rank formulas.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules.
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
  (o₂ : Orientation ℝ W (Fin m)) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))

section Modules

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out)

/-- **Half-spin decomposition of the graded tensor product**: for `μ * μ = 1`, the `μ`-eigenspace
of the product chirality `Γ_(V ⊕ W)` on `E ⊗ F` is `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})`. -/
def complexProdTensorComplexVolumeEigenspaceEquiv {μ : ℂ} (hμ : μ * μ = 1) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ ≃ₗ[ℂ]
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) :=
  (LinearEquiv.ofEq _ _
    (congrArg (eigenspace · μ)
      (complexProdTensor_complexVolume_of_map_eq_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o hm ho))).trans
    (eigenspaceTensorMapEquiv _ _
      (map_complexVolume_involutive o₁ hQ₁ ρ₁)
      (map_complexVolume_involutive o₂ hQ₂ ρ₂) hμ)

/-- The forward map of `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv` applies the
tensor products of the chirality projections on `E` and `F`. -/
@[simp]
theorem complexProdTensorComplexVolumeEigenspaceEquiv_apply {μ : ℂ} (hμ : μ * μ = 1)
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) :
    complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn o₂ hQ₂ hm o ρ₁ ρ₂ ho hμ z =
      (TensorProduct.map
          (eigenProjOfInvolutive (map_complexVolume_involutive o₁ hQ₁ ρ₁) (one_mul 1))
          (eigenProjOfInvolutive (map_complexVolume_involutive o₂ hQ₂ ρ₂) hμ) z,
        TensorProduct.map
          (eigenProjOfInvolutive (map_complexVolume_involutive o₁ hQ₁ ρ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (map_complexVolume_involutive o₂ hQ₂ ρ₂)
            ((neg_mul_neg μ μ).trans hμ)) z) := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_apply,
    eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- The inverse of `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv` sums the two
tensor products of the eigenspace inclusions. -/
@[simp]
theorem coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply {μ : ℂ} (hμ : μ * μ = 1)
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ))) :
    ((complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn o₂ hQ₂ hm o ρ₁ ρ₂ ho hμ).symm p :
        E ⊗[ℂ] F) =
      TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) p.1 +
        TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) p.2 := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    coe_eigenspaceTensorMapEquiv_symm_apply]

include hQ₂ hm ho in
/-- For finite-dimensional `E` and `F` and `μ * μ = 1`, the dimension of `(E ⊗ F)^μ` is
`dim E⁺ · dim F^μ + dim E⁻ · dim F^{-μ}`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume [Module.Finite ℂ E] [Module.Finite ℂ F]
    {μ : ℂ} (hμ : μ * μ = 1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
  rw [(complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn o₂ hQ₂ hm o ρ₁ ρ₂ ho
      hμ).finrank_eq,
    Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct]

end Modules

section Spinors

variable {S₁ S₂ : Type*} [AddCommGroup S₁] [Module ℂ S₁]
  [Module (CliffordAlgebra (Q₁.baseChange ℂ)) S₁]
  [IsScalarTower ℂ (CliffordAlgebra (Q₁.baseChange ℂ)) S₁]
  [AddCommGroup S₂] [Module ℂ S₂]
  [Module (CliffordAlgebra (Q₂.baseChange ℂ)) S₂]
  [IsScalarTower ℂ (CliffordAlgebra (Q₂.baseChange ℂ)) S₂]

include hQ₂ in
/-- **Half-spin rank of a product of spinor modules**: for spinor modules `S₁` and `S₂` with
`n + m ≠ 0` (even `m` is forced by the existence of `S₂`), both half-spin spaces `(S₁ ⊗ S₂)^±` have
dimension `2 ^ ((n + m) / 2 - 1)`. For two planes (`n = m = 2`) this is `2 ^ 1 = 2`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective_lsmul
    (h₁ : Function.Bijective
      (Algebra.lsmul ℂ ℂ S₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₁))
    (h₂ : Function.Bijective
      (Algebra.lsmul ℂ ℂ S₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S₂))
    (hnm : n + m ≠ 0)
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out)
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn (Algebra.lsmul ℂ ℂ S₁) (Algebra.lsmul ℂ ℂ S₂)
        (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  have := Module.Finite.of_surjective_end _ h₁.2
  have := Module.Finite.of_surjective_end _ h₂.2
  have hV : finrank ℂ (ℂ ⊗[ℝ] V) = n := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)]
  have hW : finrank ℂ (ℂ ⊗[ℝ] W) = m := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ W = m)]
  have hm : Even m := hW ▸ even_finrank_of_algEquiv_end _ (AlgEquiv.ofBijective _ h₂)
  have hμ2 : μ * μ = 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hnegμ : -μ = 1 ∨ -μ = -1 := by rcases hμ with rfl | rfl <;> simp
  rw [finrank_eigenspace_complexProdTensor_complexVolume hQ o₁ hQ₁ hn o₂ hQ₂ hm o _ _ ho hμ2]
  rcases eq_or_ne m 0 with rfl | hm0
  · have hn0 : n ≠ 0 := by omega
    have hc := Submodule.finrank_add_eq_of_isCompl
      (isCompl_eigenspace_complexVolume (E := S₂) o₂ hQ₂)
    rw [finrank_eq_two_pow_of_bijective_lsmul _ h₂, hW] at hc
    have hsum₂ : finrank ℂ ((Algebra.lsmul ℂ ℂ S₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((Algebra.lsmul ℂ ℂ S₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) = 1 := by
      rcases hμ with rfl | rfl
      · simpa using hc
      · rw [neg_neg, add_comm]; simpa using hc
    rw [finrank_eigenspace_complexVolume_of_bijective_lsmul o₁ hQ₁ h₁ hn0 (.inl rfl),
      finrank_eigenspace_complexVolume_of_bijective_lsmul o₁ hQ₁ h₁ hn0 (.inr rfl),
      ← mul_add, hsum₂, mul_one, add_zero]
  · have hsum₁ := Submodule.finrank_add_eq_of_isCompl
      (isCompl_eigenspace_complexVolume (E := S₁) o₁ hQ₁)
    rw [finrank_eq_two_pow_of_bijective_lsmul _ h₁, hV] at hsum₁
    rw [finrank_eigenspace_complexVolume_of_bijective_lsmul o₂ hQ₂ h₂ hm0 hμ,
      finrank_eigenspace_complexVolume_of_bijective_lsmul o₂ hQ₂ h₂ hm0 hnegμ,
      ← add_mul, hsum₁, ← pow_add]
    obtain ⟨k, rfl⟩ := hn; obtain ⟨l, rfl⟩ := hm; congr 1; omega

end Spinors

end CliffordAlgebra
