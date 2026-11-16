/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Half-spin decomposition of the graded tensor product of Clifford modules

Let `V` and `W` be oriented even-dimensional real inner product spaces of dimensions `n` and `m`,
with negative-metric quadratic forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `Q` on
`V ⊕ W = WithLp 2 (V × W)` satisfy `Q (v, w) = Q₁ v + Q₂ w`. Given Clifford modules `E` and `F`
for `Q₁` and `Q₂`, the normalized complex volume element `Γ_(V ⊕ W)` for the product orientation
acts on `E ⊗ F` as the tensor product `Γ_V ⊗ Γ_W` of the two chirality involutions
(`CliffordAlgebra.complexProdTensor_complexVolume_prod`).

Applying `Module.End.eigenspaceTensorMapEquiv` to `Γ_V` and `Γ_W` splits the half-spin spaces of
`E ⊗ F` into the standard graded tensor product pieces:

  `(E ⊗ F)⁺ ≃ (E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)`,  `(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`,

uniformly stated for any `μ : ℂ` with `μ * μ = 1` as
`Eig(Γ_(V ⊕ W), μ) ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))` without any finiteness hypothesis on `E` or `F`.
When `E` and `F` are finite-dimensional, this gives the dimension formula
`dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^(-μ)`. When `E` and `F` are spinor modules
(bijective representations of the complexified Clifford algebras) and `n + m > 0`, both half-spin
spaces of `E ⊗ F` have dimension `2 ^ ((n + m) / 2 - 1)`, including when one factor has rank zero.

## Main definitions

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: the canonical identification
  `Eig(Γ_(V ⊕ W), μ) ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))` for `μ * μ = 1`.

## Main results

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv_apply` and
  `CliffordAlgebra.coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply`: forward and
  inverse formulas in terms of the eigenspace projections and inclusions.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume`: dimension count for
  finite-dimensional `E` and `F`.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume_of_bijective`: for spinor
  modules `E` and `F` with `n + m ≠ 0`, each half-spin space has dimension `2 ^ ((n + m) / 2 - 1)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Half-spin decomposition of the graded tensor product**: for even-dimensional oriented
Euclidean spaces `V` and `W` with negative-metric forms and `μ * μ = 1`, the `μ`-eigenspace of
the product chirality `Γ_(V ⊕ W)` on `E ⊗ F` splits as `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))`. For `μ = 1`
this is `(E ⊗ F)⁺ ≃ (E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)`, and for `μ = -1` it is
`(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`. No finiteness on `E` or `F` is needed. -/
def complexProdTensorComplexVolumeEigenspaceEquiv {μ : ℂ} (hμ : μ * μ = 1) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
      (complexVolume Q (Orientation.map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out)))).eigenspace μ
      ≃ₗ[ℂ]
    ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ] (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
        (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) :=
  (LinearEquiv.ofEq _ _
    (congrArg (fun f ↦ f.eigenspace μ)
      (complexProdTensor_complexVolume_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm))).trans
    (eigenspaceTensorMapEquiv (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂) hμ)

/-- The forward map of `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv` applies the
tensor products of the chirality projections on `E` and `F`. -/
@[simp]
theorem complexProdTensorComplexVolumeEigenspaceEquiv_apply {μ : ℂ} (hμ : μ * μ = 1)
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
      (complexVolume Q (Orientation.map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out)))).eigenspace μ) :
    complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ hμ z =
      (TensorProduct.map
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (one_mul 1))
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₂ hQ₂ ρ₂) hμ) z,
        TensorProduct.map
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
            ((neg_mul_neg μ μ).trans hμ)) z) := by
  simp only [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_apply]
  rw [eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- The inverse of `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv` adds the two
tensor products of the eigenspace inclusions. -/
@[simp]
theorem coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply {μ : ℂ} (hμ : μ * μ = 1)
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ] (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
        (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ))) :
    ((complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ hμ).symm p :
        E ⊗[ℂ] F) =
      TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ).subtype p.1 +
        TensorProduct.map ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)).subtype
          ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)).subtype p.2 := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    coe_eigenspaceTensorMapEquiv_symm_apply]

include hQ₂ hm in
/-- **Dimension of the product half-spin spaces**: for finite-dimensional Clifford modules `E` and
`F` and `μ * μ = 1`,
`dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^(-μ)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume [Module.Finite ℂ E] [Module.Finite ℂ F]
    {μ : ℂ} (hμ : μ * μ = 1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
      (complexVolume Q (Orientation.map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out)))).eigenspace μ) =
      finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
  rw [(complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ hμ).finrank_eq,
    Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct]

/-- Auxiliary dimension facts for a bijective representation `ρ` of a complexified Clifford
algebra. -/
private theorem finrank_and_halfSpin_of_bijective {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] {k : ℕ} [Fact (finrank ℝ X = k)]
    {QX : QuadraticForm ℝ X} (ox : Orientation ℝ X (Fin k)) (hQX : ∀ x, QX x = -‖x‖ ^ 2)
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ρ : CliffordAlgebra (QX.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) (hρ : Function.Bijective ρ) :
    Module.Finite ℂ S ∧
      finrank ℂ S = 2 ^ (k / 2) ∧
      (∀ {μ : ℂ}, μ * μ = 1 →
        finrank ℂ ((ρ (complexVolume QX ox)).eigenspace μ) +
          finrank ℂ ((ρ (complexVolume QX ox)).eigenspace (-μ)) = 2 ^ (k / 2)) ∧
      (k ≠ 0 → ∀ {μ : ℂ}, μ * μ = 1 →
        finrank ℂ ((ρ (complexVolume QX ox)).eigenspace μ) = 2 ^ (k / 2 - 1)) := by
  let _ : Module (CliffordAlgebra (QX.baseChange ℂ)) S := Module.compHom S ρ.toRingHom
  have _ : IsScalarTower ℂ (CliffordAlgebra (QX.baseChange ℂ)) S :=
    ⟨fun c a s ↦ by
      -- Scalar multiplication by the Clifford algebra is defined via `ρ`.
      change ρ (c • a) s = c • ρ a s
      rw [map_smul, LinearMap.smul_apply]⟩
  have hlsmul : (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (QX.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) =
      ρ := by
    ext a s
    rfl
  have hbij : Function.Bijective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (QX.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) :=
    hlsmul ▸ hρ
  have hfin : Module.Finite ℂ S := Module.Finite.of_surjective_end _ hbij.2
  have hX : finrank ℂ (ℂ ⊗[ℝ] X) = k := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ X = k)]
  have hdim : finrank ℂ S = 2 ^ (k / 2) := by
    rw [finrank_eq_two_pow_of_bijective_lsmul _ hbij, hX]
  refine ⟨hfin, hdim, fun {μ} hμ ↦ ?_, fun hk0 {μ} hμ ↦ ?_⟩
  · have hμ' : μ = 1 ∨ μ = -1 := mul_self_eq_one_iff.mp hμ
    have hcomp := isCompl_eigenspace_complexVolume (E := S) ox hQX
    rw [hlsmul] at hcomp
    rcases hμ' with rfl | rfl
    · rw [Submodule.finrank_add_eq_of_isCompl hcomp, hdim]
    · rw [neg_neg, Submodule.finrank_add_eq_of_isCompl hcomp.symm, hdim]
  · have hμ' : μ = 1 ∨ μ = -1 := mul_self_eq_one_iff.mp hμ
    have hhalf := finrank_eigenspace_complexVolume_of_bijective_lsmul (S := S) ox hQX hbij hk0 hμ'
    rwa [hlsmul] at hhalf

include hQ₂ hm in
/-- **Half-spin dimensions for a graded tensor product of spinor modules**: when `ρ₁` and `ρ₂`
are bijective representations (spinor modules) for even-dimensional Euclidean spaces `V` and `W`
with `n + m ≠ 0`, each `±1`-eigenspace of `Γ_(V ⊕ W)` on `E ⊗ F` has dimension
`2 ^ ((n + m) / 2 - 1)`, including when one factor has rank zero. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) (hnm : n + m ≠ 0)
    {μ : ℂ} (hμ : μ * μ = 1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
      (complexVolume Q (Orientation.map (Fin (n + m))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm (o₁.prod o₂ Fact.out Fact.out)))).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  obtain ⟨hfinE, _, hsumE, hhalfE⟩ := finrank_and_halfSpin_of_bijective o₁ hQ₁ ρ₁ hρ₁
  obtain ⟨hfinF, _, hsumF, hhalfF⟩ := finrank_and_halfSpin_of_bijective o₂ hQ₂ ρ₂ hρ₂
  rw [finrank_eigenspace_complexProdTensor_complexVolume hQ o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ hμ]
  have hnegμ : (-μ) * (-μ) = 1 := by simpa using hμ
  obtain ⟨j, rfl⟩ := hn
  obtain ⟨k, rfl⟩ := hm
  by_cases hj : j + j ≠ 0
  · rw [hhalfE hj (one_mul 1), hhalfE hj (by simp), ← mul_add, hsumF hμ, ← pow_add]
    congr 1
    omega
  · have hk : k + k ≠ 0 := by omega
    rw [hhalfF hk hμ, hhalfF hk hnegμ, ← add_mul, hsumE (one_mul 1), ← pow_add]
    congr 1
    omega

end CliffordAlgebra
