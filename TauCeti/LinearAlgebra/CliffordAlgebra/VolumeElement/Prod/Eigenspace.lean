/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
-- Private: dimension of tensor products, finiteness of spinor modules, bijectivity of
-- `cliffordProdTensor`, and single-factor spinor half-spin dimensions are proof-only.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.End
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Half-spin decomposition and spinor bijectivity of `complexProdTensor`

Let `V` and `W` be even-dimensional oriented real inner product spaces of dimensions `n` and `m`
with the negative-metric quadratic forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `E` and `F` be
complex Clifford modules given by `ρ₁` and `ρ₂`. Write `E^±` and `F^±` for the `±1`-eigenspaces of
the chiralities `Γ_V` and `Γ_W`.

For the canonical product orientation `o` of `V ⊕ W` (`WithLp 2 (V × W)`), the product chirality
acts on `E ⊗ F` via `CliffordAlgebra.complexProdTensor` as `Γ_V ⊗ Γ_W`
(`CliffordAlgebra.complexProdTensor_complexVolume_of_prod`). Combining this with
`Module.End.eigenspaceTensorMapEquiv` decomposes its eigenspaces (`μ * μ = 1`) as

`Eig(Γ_(V ⊕ W), μ) ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})`
(`CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`);

in particular the `+1` half-spin space of `E ⊗ F` is `(E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)` and the `-1`
half-spin space is `(E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`.

When `ρ₁` and `ρ₂` are bijective (so `E` and `F` are spinor modules of `V` and `W`, automatically
finite-dimensional over `ℂ`), `CliffordAlgebra.complexProdTensor` is again bijective
(`CliffordAlgebra.complexProdTensor_bijective`), making `E ⊗ F` a spinor module of `V ⊕ W`. Each
`±1`-eigenspace of the product chirality on `E ⊗ F` therefore has complex dimension
`2 ^ ((n + m) / 2 - 1)` whenever `n + m ≠ 0`
(`CliffordAlgebra.finrank_eigenspace_complexProdTensor_of_bijective`); see
`TauCeti/Examples/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod/Eigenspace.lean` for the
two-plane (`n = m = 2`) half-spin check.

## Main definitions

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: the half-spin eigenspace
  decomposition `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})` of `E ⊗ F`.

## Main results

* `CliffordAlgebra.complexProdTensor_surjective` and `CliffordAlgebra.complexProdTensor_bijective`:
  `complexProdTensor` preserves surjectivity and bijectivity onto `End_ℂ`.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume`: dimension formula for the
  `μ`-eigenspace of the product chirality.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_of_bijective`: half-spin rank
  `2 ^ ((n + m) / 2 - 1)` for a graded tensor product of spinor modules.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 2.2.42.
-/

public section

noncomputable section

open Module Module.End
open scoped TensorProduct

namespace CliffordAlgebra

section Endomorphism

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-! ### Surjectivity and bijectivity onto `End_ℂ(E ⊗ F)` -/

/-- **Surjectivity of `complexProdTensor`**: if `F` is finite-dimensional over `ℂ` and `ρ₁`, `ρ₂`
are surjective onto `End_ℂ(E)` and `End_ℂ(F)`, then `complexProdTensor` is surjective onto
`End_ℂ(E ⊗ F)` (`E` is automatically finite-dimensional from `h₁` and `[FiniteDimensional ℝ V]`). -/
theorem complexProdTensor_surjective [FiniteDimensional ℂ F]
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Surjective ρ₁) (h₂ : Function.Surjective ρ₂) :
    Function.Surjective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  have : Module.Finite ℂ E := Module.Finite.of_surjective_end ρ₁.toLinearMap h₁
  rw [complexProdTensor_def, AlgHom.coe_comp]
  exact (AlgHom.cliffordProdTensor_surjective (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
    (map_complexVolume_mul_map_ι o₁ hn ρ₁) h₁ h₂).comp
    (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ ℂ)).surjective

/-- **Bijectivity of `complexProdTensor`**: if `F` is finite-dimensional over `ℂ` and `ρ₁`, `ρ₂`
are bijective onto `End_ℂ(E)` and `End_ℂ(F)` (so `E` and `F` are spinor modules), then
`complexProdTensor` is bijective onto `End_ℂ(E ⊗ F)` (so `E ⊗ F` is a spinor module of `V ⊕ W`). -/
theorem complexProdTensor_bijective [FiniteDimensional ℂ F]
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂) :
    Function.Bijective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  have : Module.Finite ℂ E := Module.Finite.of_surjective_end ρ₁.toLinearMap h₁.surjective
  rw [complexProdTensor_def, AlgHom.coe_comp]
  exact (AlgHom.cliffordProdTensor_bijective (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
    (map_complexVolume_mul_map_ι o₁ hn ρ₁) h₁ h₂).comp
    (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ ℂ)).bijective

end Endomorphism

/-! ### Half-spin eigenspace decomposition -/

section HalfSpin

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]

/-- **The half-spin decomposition of `E ⊗ F`.** For even-dimensional oriented spaces `V` and `W`
with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and `o` the canonical product orientation of `V ⊕ W`, the
`μ`-eigenspace (`μ * μ = 1`) of the product chirality `Γ_(V ⊕ W)` on `E ⊗ F` is linearly equivalent
to `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})`:

* for `μ = 1`, `(E ⊗ F)⁺ ≃ (E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)`;
* for `μ = -1`, `(E ⊗ F)⁻ ≃ (E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)`. -/
def complexProdTensorComplexVolumeEigenspaceEquiv (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1) :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ ≃ₗ[ℂ]
      ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) :=
  (LinearEquiv.ofEq _ _
    (congrArg (eigenspace · μ)
      (complexProdTensor_complexVolume_of_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho))).trans
    (eigenspaceTensorMapEquiv (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (map_complexVolume_involutive o₁ hQ₁ ρ₁)
      (map_complexVolume_involutive o₂ hQ₂ ρ₂) hμ)

/-- Forward evaluation of `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: it
applies the tensor products of the eigenspace projections of `Γ_V` and `Γ_W`. -/
@[simp]
theorem complexProdTensorComplexVolumeEigenspaceEquiv_apply (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1)
    (z : (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) :
    complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho hμ z =
      (TensorProduct.map
          (eigenProjOfInvolutive (map_complexVolume_involutive o₁ hQ₁ ρ₁) (one_mul 1))
          (eigenProjOfInvolutive (map_complexVolume_involutive o₂ hQ₂ ρ₂) hμ) (z : E ⊗[ℂ] F),
        TensorProduct.map
          (eigenProjOfInvolutive (map_complexVolume_involutive o₁ hQ₁ ρ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (map_complexVolume_involutive o₂ hQ₂ ρ₂)
            ((neg_mul_neg μ μ).trans hμ)) (z : E ⊗[ℂ] F)) := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.trans_apply,
    eigenspaceTensorMapEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- Inverse evaluation of `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: it adds
the two tensor products of the eigenspace inclusions. -/
@[simp]
theorem coe_complexProdTensorComplexVolumeEigenspaceEquiv_symm_apply (hm : Even m)
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1)
    (p : ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1 ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) ×
        ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1) ⊗[ℂ]
          (ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ))) :
    ((complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho hμ).symm p :
        E ⊗[ℂ] F) =
      TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) p.1 +
        TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) p.2 := by
  rw [complexProdTensorComplexVolumeEigenspaceEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply, coe_eigenspaceTensorMapEquiv_symm_apply]

/-- **Dimension of the product chirality eigenspaces**: for finite-dimensional `E` and `F`,
`dim (E ⊗ F)^μ = dim E⁺ · dim F^μ + dim E⁻ · dim F^{-μ}`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (hm : Even m) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) {μ : ℂ} (hμ : μ * μ = 1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace 1) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace μ) +
        finrank ℂ ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)) *
          finrank ℂ ((ρ₂ (complexVolume Q₂ o₂)).eigenspace (-μ)) := by
  rw [(complexProdTensorComplexVolumeEigenspaceEquiv hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho hμ).finrank_eq,
    Module.finrank_prod, Module.finrank_tensorProduct, Module.finrank_tensorProduct]

end HalfSpin

section SpinorHalfSpin

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]

/-- **Half-spin dimension of a graded tensor product of spinor modules**: when `E` and `F` are
spinor modules of `V` and `W` (`ρ₁` and `ρ₂` bijective) and `n + m ≠ 0`, each `±1`-eigenspace of
the product chirality on `E ⊗ F` has dimension `2 ^ ((n + m) / 2 - 1)` (while `dim (E ⊗ F) =
2 ^ ((n + m) / 2)`). Finiteness of `E` and `F` over `ℂ` is deduced automatically from `h₁` and
`h₂`. -/
theorem finrank_eigenspace_complexProdTensor_of_bijective (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂) (hnm : n + m ≠ 0)
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  have : Module.Finite ℂ F := Module.Finite.of_surjective_end ρ₂.toLinearMap h₂.surjective
  let ρ := complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
  let _ : Module (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    Module.compHom (E ⊗[ℂ] F) ρ.toRingHom
  have hact (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) : a • z = ρ a z := rfl
  let _ : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    ⟨fun c a z ↦ by simp only [hact, map_smul, LinearMap.smul_apply]⟩
  have hlsmul : Algebra.lsmul ℂ ℂ (E ⊗[ℂ] F) = ρ :=
    AlgHom.ext fun a ↦ LinearMap.ext (hact a)
  have hbij : Function.Bijective
      (Algebra.lsmul ℂ ℂ (E ⊗[ℂ] F) :
        CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F)) := by
    rw [hlsmul]
    exact complexProdTensor_bijective hQ o₁ hQ₁ hn h₁ h₂
  rw [show complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ = ρ from rfl, ← hlsmul]
  exact finrank_eigenspace_complexVolume_of_bijective_lsmul o
    (TauCeti.apply_eq_neg_norm_sq_of_withLp_prod hQ hQ₁ hQ₂) hbij hnm hμ

end SpinorHalfSpin

end CliffordAlgebra
