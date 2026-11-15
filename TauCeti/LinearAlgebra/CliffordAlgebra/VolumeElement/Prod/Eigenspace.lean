/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
-- Private: dimension of tensor products, bijectivity of `cliffordProdTensor`, and single-factor
-- spinor half-spin dimensions are used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.End
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace

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

When `E` and `F` are finite-dimensional and `ρ₁`, `ρ₂` are bijective (so `E` and `F` are spinor
modules of `V` and `W`), `CliffordAlgebra.complexProdTensor` is again bijective
(`CliffordAlgebra.bijective_complexProdTensor`), making `E ⊗ F` a spinor module of `V ⊕ W`. Its
half-spin spaces therefore have dimension `2 ^ ((n + m) / 2 - 1)` whenever `n + m ≠ 0`; for two
negative planes (`n = m = 2`), each half-spin space `S⁺ ⊗ S⁺ ⊕ S⁻ ⊗ S⁻` has rank `2` inside the
`4`-dimensional tensor product (`CliffordAlgebra.finrank_eigenspace_complexProdTensor_two_two`).

Finally, transporting Mathlib's `CliffordAlgebra.toProd` along the `L²` base-change isometry gives
the homogeneous action formula `(a ᵍ⊗ b)(e ⊗ f) = (-1) ^ (i * j.val) • (ρ₁ a e ⊗ ρ₂ b f)` for `b`
of parity `j` and `e` of chirality `(-1) ^ i`
(`CliffordAlgebra.complexProdTensor_toProd_tmul_tmul_of_apply_eq_neg_one_pow_smul`).

## Main definitions

* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`: the half-spin eigenspace
  decomposition `(E⁺ ⊗ F^μ) × (E⁻ ⊗ F^{-μ})` of `E ⊗ F`.

## Main results

* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume`: dimension formula for the
  `μ`-eigenspace of the product chirality.
* `CliffordAlgebra.surjective_complexProdTensor` and `CliffordAlgebra.bijective_complexProdTensor`:
  `complexProdTensor` preserves surjectivity and bijectivity onto `End_ℂ`.
* `CliffordAlgebra.finrank_eigenspace_complexProdTensor_of_bijective` and
  `CliffordAlgebra.finrank_eigenspace_complexProdTensor_two_two`: half-spin rank
  `2 ^ ((n + m) / 2 - 1)` (and `2` of `4` for two planes).
* `CliffordAlgebra.complexProdTensor_toProd_tmul_tmul_of_apply_eq_neg_one_pow_smul`: Koszul-signed
  action of `CliffordAlgebra.toProd` on chirality-homogeneous pure tensors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 2.2.42.
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
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-! ### Comparison with `AlgHom.cliffordProdTensor` and Mathlib's `CliffordAlgebra.toProd` -/

/-- Under `CliffordAlgebra.complexWithLpProd` and Mathlib's `CliffordAlgebra.toProd`, the
pure tensor `a ᵍ⊗ b` with `b` of parity `j` acts via `complexProdTensor` by
`ρ₁ a * Γ_V ^ j.val ⊗ ρ₂ b`. -/
theorem complexProdTensor_toProd_tmul (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry (complexWithLpProd hQ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) := by
  rw [complexProdTensor_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  exact AlgHom.cliffordProdTensor_toProd_tmul _ _ _ _ ρ₂ a hb

/-- **Koszul-signed action of `CliffordAlgebra.toProd` on homogeneous spinors**: for `b` of parity
`j` and `e ∈ E` satisfying `Γ_V e = (-1) ^ i • e`, the pure tensor `a ᵍ⊗ b` acts on `e ⊗ f` via
`complexProdTensor` as `(-1) ^ (i * j.val) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem complexProdTensor_toProd_tmul_tmul_of_apply_eq_neg_one_pow_smul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2} {b : CliffordAlgebra (Q₂.baseChange ℂ)}
    (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) {i : ℕ} {e : E}
    (he : ρ₁ (complexVolume Q₁ o₁) e = (-1 : ℂ) ^ i • e) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂
        ((equivOfIsometry (complexWithLpProd hQ)).symm
          (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b))) (e ⊗ₜ f) =
      (-1 : ℂ) ^ (i * j.val) • (ρ₁ a e ⊗ₜ ρ₂ b f) := by
  rw [complexProdTensor_def, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  exact AlgHom.cliffordProdTensor_toProd_tmul_tmul_of_apply_eq_neg_one_pow_smul _ _ _ _ ρ₂ a hb he f

/-! ### Surjectivity and bijectivity onto `End_ℂ(E ⊗ F)` -/

/-- **Surjectivity of `complexProdTensor`**: if `E` and `F` are finite-dimensional over `ℂ` and
`ρ₁`, `ρ₂` are surjective onto `End_ℂ(E)` and `End_ℂ(F)`, then `complexProdTensor` is surjective
onto `End_ℂ(E ⊗ F)`. -/
theorem surjective_complexProdTensor [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Surjective ρ₁) (h₂ : Function.Surjective ρ₂) :
    Function.Surjective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  rw [complexProdTensor_def, AlgHom.coe_comp]
  exact (AlgHom.surjective_cliffordProdTensor (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
    (map_complexVolume_mul_map_ι o₁ hn ρ₁) h₁ h₂).comp
    (equivOfIsometry (complexWithLpProd hQ)).surjective

/-- **Bijectivity of `complexProdTensor`**: if `E` and `F` are finite-dimensional over `ℂ` and
`ρ₁`, `ρ₂` are bijective onto `End_ℂ(E)` and `End_ℂ(F)` (so `E` and `F` are spinor modules), then
`complexProdTensor` is bijective onto `End_ℂ(E ⊗ F)` (so `E ⊗ F` is a spinor module of `V ⊕ W`). -/
theorem bijective_complexProdTensor [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂) :
    Function.Bijective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  rw [complexProdTensor_def, AlgHom.coe_comp]
  exact (AlgHom.bijective_cliffordProdTensor (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
    (map_complexVolume_mul_map_ι o₁ hn ρ₁) h₁ h₂).comp
    (equivOfIsometry (complexWithLpProd hQ)).bijective

/-! ### Half-spin eigenspace decomposition -/

section HalfSpin

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
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
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
      (involutive_apply_complexVolume o₂ hQ₂ ρ₂) hμ)

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
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (one_mul 1))
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₂ hQ₂ ρ₂) hμ) (z : E ⊗[ℂ] F),
        TensorProduct.map
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
            ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1)))
          (eigenProjOfInvolutive (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
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

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]

/-- **Half-spin dimension of a graded tensor product of spinor modules**: when `E` and `F` are
spinor modules of `V` and `W` (`ρ₁` and `ρ₂` bijective) and `n + m ≠ 0`, each `±1`-eigenspace of
the product chirality on `E ⊗ F` has dimension `2 ^ ((n + m) / 2 - 1)` (while `dim (E ⊗ F) =
2 ^ ((n + m) / 2)`). -/
theorem finrank_eigenspace_complexProdTensor_of_bijective [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂) (hnm : n + m ≠ 0)
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  -- Endow `E ⊗ F` locally with the `CliffordAlgebra (Q.baseChange ℂ)`-module structure of
  -- `complexProdTensor` so `finrank_eigenspace_complexVolume_of_bijective_lsmul` applies.
  let _ : Module (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    Module.compHom (E ⊗[ℂ] F) (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).toRingHom
  have _ : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    IsScalarTower.of_algebraMap_smul fun c z ↦ by
      -- Unfold `Module.compHom` scalar multiplication to the `complexProdTensor` action.
      change (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) (algebraMap ℂ _ c) z = c • z
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        one_apply_eq_self]
  have hbij : Function.Bijective
      (Algebra.lsmul ℂ ℂ (E ⊗[ℂ] F) :
        CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F)) :=
    bijective_complexProdTensor hQ o₁ hQ₁ hn h₁ h₂
  exact finrank_eigenspace_complexVolume_of_bijective_lsmul o
    (norm_sq_of_withLp_prod hQ hQ₁ hQ₂) hbij hnm hμ

/-- **Two-plane half-spin check**: for two oriented negative planes `V` and `W` (`n = 2`, `m = 2`)
with spinor modules `E` and `F` (`dim E = dim F = 2`), each half-spin space
`(E⁺ ⊗ F⁺) × (E⁻ ⊗ F⁻)` and `(E⁺ ⊗ F⁻) × (E⁻ ⊗ F⁺)` of `E ⊗ F` has complex dimension `2` inside
the `4`-dimensional space `E ⊗ F`. -/
theorem finrank_eigenspace_complexProdTensor_two_two [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (hn2 : n = 2) (hm2 : m = 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    {ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F}
    (h₁ : Function.Bijective ρ₁) (h₂ : Function.Bijective ρ₂)
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) = 2 := by
  subst hn2 hm2
  simpa using finrank_eigenspace_complexProdTensor_of_bijective hQ o₁ hQ₁ hn hQ₂ h₁ h₂
    (by decide) o hμ

end SpinorHalfSpin

end CliffordAlgebra
