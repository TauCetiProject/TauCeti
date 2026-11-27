/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Bijectivity of the graded tensor product of Clifford endomorphism modules

When `E` and `F` are finite projective `R`-modules and `ρ₁ : CliffordAlgebra Q₁ →ₐ[R] End_R E`,
`ρ₂ : CliffordAlgebra Q₂ →ₐ[R] End_R F` are surjective (respectively bijective), the graded tensor
product action
`AlgHom.cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ : CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] End_R (E ⊗ F)` is
surjective (respectively bijective) onto `End_R (E ⊗ F)`. No finiteness assumption on `M₁` or `M₂`
and no invertibility of `2` is needed.

## Main results

* `AlgHom.cliffordProdTensor_surjective`: for finite projective `E` and `F`, surjectivity of `ρ₁`
  and `ρ₂` implies surjectivity of `cliffordProdTensor`.
* `AlgHom.cliffordProdTensor_bijective`: for finite projective `E` and `F`, bijectivity of `ρ₁` and
  `ρ₂` implies bijectivity of `cliffordProdTensor`.
-/

public section

open TensorProduct

namespace AlgHom

open CliffordAlgebra

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

variable (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

private noncomputable def cliffordProdTensorLinearEquiv
    [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    CliffordAlgebra (Q₁.prod Q₂) ≃ₗ[R] Module.End R (E ⊗[R] F) :=
  let rγ : Module.End R E ≃ₗ[R] Module.End R E := Units.mulRightLinearEquiv R ⟨γ, γ, hγ, hγ⟩
  have hρ₁' : Function.Bijective ρ₁.toLinearMap := by simpa only [AlgHom.coe_toLinearMap] using hρ₁
  have hρ₂' : Function.Bijective ρ₂.toLinearMap := by simpa only [AlgHom.coe_toLinearMap] using hρ₂
  prodTensorLinearEquiv Q₁ Q₂ ≪≫ₗ
    TensorProduct.congr (LinearEquiv.ofBijective ρ₁.toLinearMap hρ₁')
      (evenOddProdEquiv Q₂).symm ≪≫ₗ
    TensorProduct.prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1) ≪≫ₗ
    LinearEquiv.prodCongr (.refl R _) (rγ.rTensor (evenOdd Q₂ 1)) ≪≫ₗ
    (TensorProduct.prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1)).symm ≪≫ₗ
    TensorProduct.congr (.refl R _)
      ((evenOddProdEquiv Q₂).trans (LinearEquiv.ofBijective ρ₂.toLinearMap hρ₂')) ≪≫ₗ
    homTensorHomEquiv R E F E F

private theorem cliffordProdTensor_eq_linearEquiv_tmul
    [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂)
    (a : CliffordAlgebra Q₁) {j : ZMod 2} {y : CliffordAlgebra Q₂} (hy : y ∈ evenOdd Q₂ j) :
    cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ ((prodTensorLinearEquiv Q₁ Q₂).symm (a ⊗ₜ y)) =
      cliffordProdTensorLinearEquiv ρ₁ γ hγ ρ₂ hρ₁ hρ₂
        ((prodTensorLinearEquiv Q₁ Q₂).symm (a ⊗ₜ y)) := by
  have hmid :
      (TensorProduct.prodRight R R (Module.End R E) (evenOdd Q₂ 0) (evenOdd Q₂ 1)).symm
          (ρ₁ a ⊗ₜ[R] ((evenOddProdEquiv Q₂).symm y).1,
            (ρ₁ a * γ) ⊗ₜ[R] ((evenOddProdEquiv Q₂).symm y).2) =
        (ρ₁ a * γ ^ j.val) ⊗ₜ (evenOddProdEquiv Q₂).symm y := by
    rw [LinearEquiv.symm_apply_eq]
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) j with rfl | rfl
    · simp [evenOddProdEquiv_symm_apply_of_mem_even hy, ZMod.val_zero]
    · simp [evenOddProdEquiv_symm_apply_of_mem_odd hy, ZMod.val_one]
  have hΨ : cliffordProdTensorLinearEquiv ρ₁ γ hγ ρ₂ hρ₁ hρ₂
      ((prodTensorLinearEquiv Q₁ Q₂).symm (a ⊗ₜ y)) =
      TensorProduct.map (ρ₁ a * γ ^ j.val) (ρ₂ y) := by
    simp [cliffordProdTensorLinearEquiv, hmid, TensorProduct.homTensorHomMap_apply]
  rw [hΨ, prodTensorLinearEquiv_symm_tmul, cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a hy]

/-- **Surjectivity of the graded tensor product of endomorphism representations.** When `E` and
`F` are finite projective `R`-modules and `ρ₁`, `ρ₂` are surjective onto `End_R E` and `End_R F`,
the graded tensor product action `cliffordProdTensor` is surjective onto `End_R (E ⊗ F)`. No
finiteness assumption on `M₁` or `M₂` and no invertibility of `2` is needed. -/
theorem cliffordProdTensor_surjective [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (hρ₁ : Function.Surjective ρ₁) (hρ₂ : Function.Surjective ρ₂) :
    Function.Surjective (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) := by
  obtain ⟨g, hg⟩ := hρ₁ γ
  intro T
  obtain ⟨U, rfl⟩ := (homTensorHomEquiv R E F E F).surjective T
  suffices hmem : homTensorHomEquiv R E F E F U ∈
      LinearMap.range (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap from
    LinearMap.mem_range.mp hmem
  induction U using TensorProduct.inductionOn with
  | tmul u v =>
    obtain ⟨a, rfl⟩ := hρ₁ u
    obtain ⟨b, rfl⟩ := hρ₂ v
    obtain ⟨b₀, hb₀, b₁, hb₁, hadd⟩ := Submodule.mem_sup.mp
      ((evenOdd_isCompl Q₂).sup_eq_top ▸ Submodule.mem_top (x := b))
    rw [← hadd, map_add, TensorProduct.tmul_add, map_add]
    refine Submodule.add_mem _ ?_ ?_
    · refine ⟨toProd Q₁ Q₂ (a ᵍ⊗ₜ b₀), ?_⟩
      rw [AlgHom.toLinearMap_apply, cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ a hb₀]
      simp [homTensorHomEquiv_apply, homTensorHomMap_apply]
    · refine ⟨toProd Q₁ Q₂ ((a * g) ᵍ⊗ₜ b₁), ?_⟩
      rw [AlgHom.toLinearMap_apply, cliffordProdTensor_toProd_tmul ρ₁ γ hγ hγρ ρ₂ (a * g) hb₁,
        map_mul, hg, ZMod.val_one, pow_one, mul_assoc, hγ, mul_one]
      simp [homTensorHomEquiv_apply, homTensorHomMap_apply]
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- **Bijectivity of the graded tensor product of endomorphism representations.** When `E` and `F`
are finite projective `R`-modules and `ρ₁`, `ρ₂` are bijective onto `End_R E` and `End_R F`, the
graded tensor product action `cliffordProdTensor` is bijective onto `End_R (E ⊗ F)`. No finiteness
assumption on `M₁` or `M₂` and no invertibility of `2` is needed. -/
theorem cliffordProdTensor_bijective [Module.Finite R E] [Module.Projective R E]
    [Module.Finite R F] [Module.Projective R F]
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) :
    Function.Bijective (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) := by
  let Ψ := cliffordProdTensorLinearEquiv ρ₁ γ hγ ρ₂ hρ₁ hρ₂
  have hlin : (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).toLinearMap = Ψ.toLinearMap := by
    refine (prodTensorLinearEquiv Q₁ Q₂).symm.surjective.injective_linearMapComp_right
      (TensorProduct.ext' fun a b ↦ ?_)
    obtain ⟨⟨b₀, b₁⟩, rfl⟩ := (evenOddProdEquiv Q₂).surjective b
    rw [evenOddProdEquiv_apply, tmul_add, map_add, map_add]
    dsimp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, AlgHom.toLinearMap_apply]
    rw [cliffordProdTensor_eq_linearEquiv_tmul ρ₁ γ hγ hγρ ρ₂ hρ₁ hρ₂ a b₀.property,
      cliffordProdTensor_eq_linearEquiv_tmul ρ₁ γ hγ hγρ ρ₂ hρ₁ hρ₂ a b₁.property]
  exact congrArg DFunLike.coe hlin ▸ Ψ.bijective

end AlgHom
