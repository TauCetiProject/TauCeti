/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Graded-algebra comparison and half-spin decomposition of Clifford tensor products

Identifies `CliffordAlgebra (Q.baseChange ℂ)` on `WithLp 2 (V × W)` with
`evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ)` via `CliffordAlgebra.prodEquiv`
(`complexWithLpProdEquiv`), proves the Koszul-signed evaluation and spinor bijectivity of
`complexProdTensor`, and decomposes the `±1`-eigenspaces of `Γ_(V ⊕ W)` as
`(E ⊗ F)^μ ≃ (E⁺ ⊗ F^μ) × (E⁻ ⊗ F^(-μ))` with half-spin `finrank` formulas.

## Main definitions and results

* `CliffordAlgebra.complexWithLpProdEquiv`: graded-algebra equivalence with
  `evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ)`.
* `CliffordAlgebra.complexProdTensor_complexWithLpProdEquiv_symm_tmul` and
  `CliffordAlgebra.complexProdTensor_complexWithLpProdEquiv_symm_tmul_apply_tmul`: Koszul-signed
  action of homogeneous graded tensors on `E ⊗ F`.
* `CliffordAlgebra.complexProdTensor_bijective`: tensor product of spinor modules is a spinor
  module.
* `CliffordAlgebra.complexProdTensorComplexVolumeEigenspaceEquiv`,
  `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume`, and
  `CliffordAlgebra.finrank_eigenspace_complexProdTensor_complexVolume_of_bijective`: half-spin
  decomposition and dimension formulas.

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

/-! ### Comparison with `CliffordAlgebra.prodEquiv` -/

include hQ in
/-- The complexified Clifford algebra of `WithLp 2 (V × W)` is isomorphic to the graded tensor
product `evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ)`. -/
def complexWithLpProdEquiv :
    CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ]
      evenOdd (Q₁.baseChange ℂ) ᵍ⊗[ℂ] evenOdd (Q₂.baseChange ℂ) :=
  (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).trans
    (prodEquiv (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))

/-- On a real vector `(v, w)`, `complexWithLpProdEquiv` sends `ι (1 ⊗ (v, w))` to
`ι (1 ⊗ v) ᵍ⊗ 1 + 1 ᵍ⊗ ι (1 ⊗ w)`. -/
@[simp]
theorem complexWithLpProdEquiv_ι_one_tmul_toLp (v : V) (w : W) :
    complexWithLpProdEquiv hQ (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ v) ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w) := by
  simp [complexWithLpProdEquiv, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChangeProd_tmul]

/-- The inverse of `complexWithLpProdEquiv` sends `ι u ᵍ⊗ 1` to the left-summand vector. -/
@[simp]
theorem complexWithLpProdEquiv_symm_ι_tmul_one (v : V) :
    (complexWithLpProdEquiv hQ).symm (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v) ᵍ⊗ₜ 1) =
      ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, 0)) :=
  (complexWithLpProdEquiv hQ).injective (by simp [complexWithLpProdEquiv_ι_one_tmul_toLp])

/-- The inverse of `complexWithLpProdEquiv` sends `1 ᵍ⊗ ι w` to the right-summand vector. -/
@[simp]
theorem complexWithLpProdEquiv_symm_one_tmul_ι (w : W) :
    (complexWithLpProdEquiv hQ).symm (1 ᵍ⊗ₜ ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) =
      ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w)) :=
  (complexWithLpProdEquiv hQ).injective (by simp [complexWithLpProdEquiv_ι_one_tmul_toLp])

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

private theorem complexProdTensor_comp_complexWithLpProdEquiv_symm :
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp (complexWithLpProdEquiv hQ).symm.toAlgHom =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)) := by
  have h : complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ =
      ((AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂).comp
        (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ))).comp
        (complexWithLpProdEquiv hQ).toAlgHom := by
    refine AlgHom.toRingHom_injective <| baseChange_ringHom_ext Q (fun _ ↦ by simp) fun x' ↦ ?_
    rcases x' with ⟨⟨v, w⟩⟩
    simp
  exact AlgHom.ext fun x ↦ by rw [h]; simp

/-- **Comparison with Mathlib's `CliffordAlgebra.prodEquiv`.** Under `complexWithLpProdEquiv`, a
pure tensor `a ᵍ⊗ b` with `b` of parity `j` acts on `E ⊗ F` by `ρ₁ a Γ_V ^ j ⊗ ρ₂ b`. -/
theorem complexProdTensor_complexWithLpProdEquiv_symm_tmul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ ((complexWithLpProdEquiv hQ).symm (a ᵍ⊗ₜ b)) =
      TensorProduct.map (ρ₁ a * ρ₁ (complexVolume Q₁ o₁) ^ j.val) (ρ₂ b) :=
  (AlgHom.congr_fun
    (complexProdTensor_comp_complexWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂) (a ᵍ⊗ₜ b)).trans
    (AlgHom.cliffordProdTensor_toProd_tmul ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂ a hb)

/-- **Koszul-signed evaluation on homogeneous spinors.** If `b` has parity `j` and `e` lies in the
`(-1) ^ i`-eigenspace of `Γ_V`, then `(complexWithLpProdEquiv hQ).symm (a ᵍ⊗ b)` sends `e ⊗ f` to
`(-1) ^ (i * j.val) • (ρ₁ a e ⊗ ρ₂ b f)`. -/
theorem complexProdTensor_complexWithLpProdEquiv_symm_tmul_apply_tmul
    (a : CliffordAlgebra (Q₁.baseChange ℂ)) {j : ZMod 2}
    {b : CliffordAlgebra (Q₂.baseChange ℂ)} (hb : b ∈ evenOdd (Q₂.baseChange ℂ) j)
    {i : ℕ} {e : E} (he : e ∈ (ρ₁ (complexVolume Q₁ o₁)).eigenspace ((-1 : ℂ) ^ i)) (f : F) :
    complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ ((complexWithLpProdEquiv hQ).symm (a ᵍ⊗ₜ b)) (e ⊗ₜ f) =
      (-1 : ℂ) ^ (i * j.val) • (ρ₁ a e ⊗ₜ ρ₂ b f) :=
  (LinearMap.congr_fun (AlgHom.congr_fun
    (complexProdTensor_comp_complexWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂) (a ᵍ⊗ₜ b))
      (e ⊗ₜ f)).trans
    (AlgHom.cliffordProdTensor_toProd_tmul_apply_tmul ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂ a hb he f)

/-- **The graded tensor product of spinor modules is a spinor module.** When `W` is
finite-dimensional and `ρ₁`, `ρ₂` are bijective onto `End_ℂ E` and `End_ℂ F`, `complexProdTensor`
is bijective onto `End_ℂ (E ⊗ F)`. -/
theorem complexProdTensor_bijective [FiniteDimensional ℝ W]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    Function.Bijective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
  have : Module.Finite ℂ E := Module.Finite.of_surjective_end ρ₁ hρ₁.surjective
  have : Module.Finite ℂ F := Module.Finite.of_surjective_end ρ₂ hρ₂.surjective
  have hbij : Function.Bijective
      ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).comp (complexWithLpProdEquiv hQ).symm.toAlgHom) := by
    rw [complexProdTensor_comp_complexWithLpProdEquiv_symm hQ o₁ hQ₁ hn ρ₁ ρ₂]
    exact (AlgHom.cliffordProdTensor_bijective ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁) ρ₂
      hρ₁ hρ₂).comp (prodEquiv (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).symm.bijective
  convert hbij.comp (complexWithLpProdEquiv hQ).bijective
  ext a z; simp

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
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    Module.compHom (E ⊗[ℂ] F) (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).toRingHom
  have : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) (E ⊗[ℂ] F) :=
    ⟨fun c a z ↦ by
      change complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (c • a) z =
        c • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z
      rw [map_smul, LinearMap.smul_apply]⟩
  have hQ_norm (x : WithLp 2 (V × W)) : Q x = -‖x‖ ^ 2 := by
    rw [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2]; dsimp only [WithLp.fst, WithLp.snd]; ring
  have hlsmul : (Algebra.lsmul ℂ ℂ (E ⊗[ℂ] F) :
      CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F)) =
      complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ := by ext a z; rfl
  rw [← hlsmul]
  exact finrank_eigenspace_complexVolume_of_bijective_lsmul o hQ_norm
    (hlsmul.symm ▸ complexProdTensor_bijective hQ o₁ hQ₁ hn ρ₁ ρ₂ hρ₁ hρ₂) hnm hμ

end HalfSpin

end CliffordAlgebra
