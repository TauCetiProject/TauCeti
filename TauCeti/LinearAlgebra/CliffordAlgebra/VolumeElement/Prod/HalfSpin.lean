/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Involution
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
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

attribute [local instance] instFactFinrankWithLpProd

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

private theorem tensorProduct_map_subtype_congr_ofEq {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (S₁ : Submodule ℂ E) {T₂ : Module.End ℂ F} {μ ν : ℂ} (h : μ = ν) :
    (TensorProduct.map S₁.subtype (T₂.eigenspace μ).subtype).comp
        (TensorProduct.congr (LinearEquiv.refl ℂ S₁)
          (LinearEquiv.ofEq (T₂.eigenspace μ) (T₂.eigenspace ν)
            (congrArg T₂.eigenspace h)).symm).toLinearMap =
      TensorProduct.map S₁.subtype (T₂.eigenspace ν).subtype := by
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
  refine Prod.ext rfl ?_
  have hmap :
      (TensorProduct.congr (LinearEquiv.refl ℂ _)
          (LinearEquiv.ofEq _ _
            (congrArg (ρ₂ (complexVolume Q₂ o₂)).eigenspace (neg_neg (1 : ℂ))))).toLinearMap =
        TensorProduct.map
          (LinearMap.id (R := ℂ) (M := (ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1)))
          (LinearEquiv.ofEq _ _
            (congrArg (ρ₂ (complexVolume Q₂ o₂)).eigenspace (neg_neg (1 : ℂ)))).toLinearMap :=
    TensorProduct.ext' fun _ _ ↦ rfl
  dsimp only
  rw [← LinearEquiv.coe_toLinearMap, hmap, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
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
  exact LinearMap.congr_fun
    (tensorProduct_map_subtype_congr_ofEq ((ρ₁ (complexVolume Q₁ o₁)).eigenspace (-1))
      (T₂ := ρ₂ (complexVolume Q₂ o₂)) (neg_neg (1 : ℂ))) p.2

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
  have hfinE : FiniteDimensional ℂ E := Module.Finite.of_surjective_end ρ₁ hρ₁.2
  have hfinF : FiniteDimensional ℂ F := Module.Finite.of_surjective_end ρ₂ hρ₂.2
  have hm : Even (finrank ℝ W) := by
    simpa [Module.finrank_baseChange] using
      CliffordAlgebra.even_finrank_of_algEquiv_end (Q₂.baseChange ℂ) (AlgEquiv.ofBijective ρ₂ hρ₂)
  have hdimE : finrank ℂ E = 2 ^ (n / 2) := by
    simpa [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)] using
      CliffordAlgebra.finrank_eq_two_pow_of_bijective (Q₁.baseChange ℂ) hρ₁
  have hdimF : finrank ℂ F = 2 ^ (finrank ℝ W / 2) := by
    simpa [Module.finrank_baseChange] using
      CliffordAlgebra.finrank_eq_two_pow_of_bijective (Q₂.baseChange ℂ) hρ₂
  have hsurj : Function.Surjective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) := by
    suffices hmem : ∀ T : Module.End ℂ (E ⊗[ℂ] F),
        T ∈ LinearMap.range (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).toLinearMap from
      fun T ↦ LinearMap.mem_range.mp (hmem T)
    intro T
    obtain ⟨U, rfl⟩ := (homTensorHomEquiv ℂ E F E F).surjective T
    induction U using TensorProduct.inductionOn with
    | tmul u v =>
      obtain ⟨a, rfl⟩ := hρ₁.2 u
      obtain ⟨b, rfl⟩ := hρ₂.2 v
      obtain ⟨b₀, hb₀, b₁, hb₁, hadd⟩ := Submodule.mem_sup.mp
        ((evenOdd_isCompl (Q₂.baseChange ℂ)).sup_eq_top ▸ Submodule.mem_top (x := b))
      rw [← hadd, map_add, TensorProduct.tmul_add, map_add]
      refine Submodule.add_mem _ ?_ ?_
      · refine ⟨(equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).symm
            (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (a ᵍ⊗ₜ b₀)), ?_⟩
        rw [AlgHom.toLinearMap_apply,
          complexProdTensor_equivOfIsometry_symm_toProd_tmul hQ o₁ hQ₁ hn ρ₁ ρ₂ a hb₀]
        simp [homTensorHomEquiv_apply, homTensorHomMap_apply]
      · refine ⟨(equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).symm
            (toProd (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)
              ((a * complexVolume Q₁ o₁) ᵍ⊗ₜ b₁)), ?_⟩
        rw [AlgHom.toLinearMap_apply,
          complexProdTensor_equivOfIsometry_symm_toProd_tmul hQ o₁ hQ₁ hn ρ₁ ρ₂
            (a * complexVolume Q₁ o₁) hb₁,
          map_mul, ZMod.val_one, pow_one, mul_assoc, map_complexVolume_mul_self o₁ hQ₁ ρ₁,
          mul_one]
        simp [homTensorHomEquiv_apply, homTensorHomMap_apply]
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  have hfinrank :
      finrank ℂ (CliffordAlgebra (Q.baseChange ℂ)) = finrank ℂ (Module.End ℂ (E ⊗[ℂ] F)) := by
    rw [finrank_eq_two_pow, Module.finrank_baseChange,
      (WithLp.linearEquiv 2 ℝ (V × W)).finrank_eq, Module.finrank_prod,
      Fact.out (p := finrank ℝ V = n), Module.finrank_linearMap,
      Module.finrank_tensorProduct, hdimE, hdimF]
    obtain ⟨k, rfl⟩ := hn
    obtain ⟨l, hl⟩ := hm
    rw [hl]
    simp [← two_mul, ← pow_add]
    ring
  have hinj : Function.Injective (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mpr hsurj
  exact ⟨hinj, hsurj⟩

/-- **Half-spin dimension of a graded tensor product of spinor modules**: when `ρ₁` and `ρ₂` are
bijective onto `End_ℂ E` and `End_ℂ F` and `n + m ≠ 0`, both half-spin spaces `(E ⊗ F)^±` have
dimension `2 ^ ((n + m) / 2 - 1)`. -/
theorem finrank_eigenspace_complexProdTensor_complexVolume_of_bijective
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂)
    (hnm : n + m ≠ 0) {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)).eigenspace μ) =
      2 ^ ((n + m) / 2 - 1) := by
  have hQ_neg : ∀ x : WithLp 2 (V × W), Q x = -‖x‖ ^ 2 := fun x ↦ by
    rw [hQ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
    ring
  exact AlgHom.finrank_eigenspace_complexVolume_of_bijective
    (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) o hQ_neg
    (bijective_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ hρ₁ hρ₂) hnm hμ

end CliffordAlgebra
