/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Gluing

/-!
# Iterated gluing of determinant lines

Three operators `D₁`, `D₂` and `D₃`, stabilized by `ιᵢ : Sᵢ → Fᵢ` with stabilized kernels `Kᵢ`, can
be glued to an operator `D` in two orders. First gluing `D₁` to `D₂` gives an operator `D₁₂`,
stabilized by some `j₁₂` on `S₁ × S₂`, with a kernel isomorphism `g₁₂ : K₁ × K₂ ≃ K₁₂`; gluing
`D₁₂` to `D₃` gives `D`, stabilized by `j` on `(S₁ × S₂) × S₃`, with `g : K₁₂ × K₃ ≃ K` onto
`K = ker (D.coprod j)`. First gluing `D₂` to `D₃` gives `D₂₃` with `g₂₃ : K₂ × K₃ ≃ K₂₃`, and gluing
`D₁` to `D₂₃` gives `D` again, stabilized by `j'` on `S₁ × (S₂ × S₃)`, with `g' : K₁ × K₂₃ ≃ K'`
onto `K' = ker (D.coprod j')`. The two stabilizations of
`D` are compatible when `j'` reassociated is `j`; the two kernel isomorphisms are compatible when

`g' (k₁, g₂₃ (k₂, k₃)) = (x, (a, (b, c)))` whenever `g (g₁₂ (k₁, k₂), k₃) = (x, ((a, b), c))`,

that is, `g'` and `g` identify `K₁ × K₂ × K₃` with the stabilized kernel of `D` in the same way up
to the reassociation `ContinuousLinearMap.kerCoprodMap` of the stabilizing parameters.

Under these compatibilities the ordered gluing isomorphisms of
`ContinuousLinearMap.detLineGluingEquiv` are **associative**: the two isomorphisms
`det D₁ ⊗ det D₂ ⊗ det D₃ ≃ det D` obtained by gluing in the two orders agree, with no sign
(`ContinuousLinearMap.detLineGluingEquiv_assoc`). The Koszul signs
`(-1) ^ (dim S₁ * (dim K₂ + dim S₂))` of the four gluing isomorphisms combine to the same total
in both orders, and the gathering isomorphism `TauCeti.detLineTensorDualProdEquiv` is associative
(`TauCeti.congr_detLineCongr_prodAssoc_detLineTensorDualProdEquiv`). This is the compatibility of
the determinant-line isomorphism of linear gluing with iterated gluing: the orientation of a
multiply glued operator induced from orientations of its pieces does not depend on the order in
which the necks are glued.

## Main results

* `ContinuousLinearMap.detLineGluingEquiv_assoc`: the gluing isomorphisms obtained by gluing three
  operators in the two orders agree.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles and stabilization).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

variable {𝕜 E₁ S₁ F₁ E₂ S₂ F₂ E₃ S₃ F₃ E₁₂ F₁₂ E₂₃ F₂₃ E F : Type*} [Field 𝕜]
  [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
  [AddCommGroup S₁] [Module 𝕜 S₁] [TopologicalSpace S₁]
  [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁] [ContinuousAdd F₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup S₂] [Module 𝕜 S₂] [TopologicalSpace S₂]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂] [ContinuousAdd F₂]
  [AddCommGroup E₃] [Module 𝕜 E₃] [TopologicalSpace E₃]
  [AddCommGroup S₃] [Module 𝕜 S₃] [TopologicalSpace S₃]
  [AddCommGroup F₃] [Module 𝕜 F₃] [TopologicalSpace F₃] [ContinuousAdd F₃]
  [AddCommGroup E₁₂] [Module 𝕜 E₁₂] [TopologicalSpace E₁₂]
  [AddCommGroup F₁₂] [Module 𝕜 F₁₂] [TopologicalSpace F₁₂] [ContinuousAdd F₁₂]
  [AddCommGroup E₂₃] [Module 𝕜 E₂₃] [TopologicalSpace E₂₃]
  [AddCommGroup F₂₃] [Module 𝕜 F₂₃] [TopologicalSpace F₂₃] [ContinuousAdd F₂₃]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  {D₁ : E₁ →L[𝕜] F₁} {ι₁ : S₁ →L[𝕜] F₁} {D₂ : E₂ →L[𝕜] F₂} {ι₂ : S₂ →L[𝕜] F₂}
  {D₃ : E₃ →L[𝕜] F₃} {ι₃ : S₃ →L[𝕜] F₃}
  {D₁₂ : E₁₂ →L[𝕜] F₁₂} {j₁₂ : S₁ × S₂ →L[𝕜] F₁₂}
  {D₂₃ : E₂₃ →L[𝕜] F₂₃} {j₂₃ : S₂ × S₃ →L[𝕜] F₂₃}
  {D : E →L[𝕜] F} {j : (S₁ × S₂) × S₃ →L[𝕜] F} {j' : S₁ × (S₂ × S₃) →L[𝕜] F}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 S₁]
  [FiniteDimensional 𝕜 D₂.ker] [FiniteDimensional 𝕜 S₂]
  [FiniteDimensional 𝕜 D₃.ker] [FiniteDimensional 𝕜 S₃]
  [FiniteDimensional 𝕜 D₁₂.ker] [FiniteDimensional 𝕜 D₂₃.ker]

/-- **Associativity of the gluing isomorphism.** Glue `D₁` to `D₂` along `g₁₂` and the result
`D₁₂` to `D₃` along `g`, or `D₂` to `D₃` along `g₂₃` and `D₁` to the result `D₂₃` along `g'`.
If the stabilizers `j` and `j'` of `D` agree up to reassociation and the kernel isomorphisms are
compatible, `g' (k₁, g₂₃ (k₂, k₃))` being the reassociation
(`ContinuousLinearMap.kerCoprodMap`) of `g (g₁₂ (k₁, k₂), k₃)`, then the two isomorphisms
`det D₁ ⊗ det D₂ ⊗ det D₃ ≃ det D` agree, with no sign. -/
theorem detLineGluingEquiv_assoc (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h₃ : Function.Surjective (D₃.coprod ι₃))
    (h₁₂ : Function.Surjective (D₁₂.coprod j₁₂)) (h₂₃ : Function.Surjective (D₂₃.coprod j₂₃))
    (h : Function.Surjective (D.coprod j))
    (hj : ∀ l, j' ((LinearEquiv.prodAssoc 𝕜 S₁ S₂ S₃).toLinearMap l) = j l)
    (g₁₂ : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D₁₂.coprod j₁₂).ker)
    (g₂₃ : ((D₂.coprod ι₂).ker × (D₃.coprod ι₃).ker) ≃ₗ[𝕜] (D₂₃.coprod j₂₃).ker)
    (g : ((D₁₂.coprod j₁₂).ker × (D₃.coprod ι₃).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (g' : ((D₁.coprod ι₁).ker × (D₂₃.coprod j₂₃).ker) ≃ₗ[𝕜] (D.coprod j').ker)
    (hg : ∀ k₁ k₂ k₃, g' (k₁, g₂₃ (k₂, k₃)) = kerCoprodMap D hj (g (g₁₂ (k₁, k₂), k₃)))
    (t₁ : (D₁ : E₁ →ₗ[𝕜] F₁).detLine) (t₂ : (D₂ : E₂ →ₗ[𝕜] F₂).detLine)
    (t₃ : (D₃ : E₃ →ₗ[𝕜] F₃).detLine) :
    detLineGluingEquiv h₁₂ h₃ h g (detLineGluingEquiv h₁ h₂ h₁₂ g₁₂ (t₁ ⊗ₜ t₂) ⊗ₜ t₃) =
      detLineGluingEquiv h₁ h₂₃ (surjective_coprod_of_comp hj h) g'
        (t₁ ⊗ₜ detLineGluingEquiv h₂ h₃ h₂₃ g₂₃ (t₂ ⊗ₜ t₃)) := by
  have : FiniteDimensional 𝕜 (D.coprod j).ker := g.finiteDimensional
  have := finiteDimensional_ker_of_finiteDimensional_ker_coprod D j
  have h' := surjective_coprod_of_comp hj h
  -- The reassociation `ContinuousLinearMap.kerCoprodMap` of the stabilized kernels of `D`, as an
  -- isomorphism: through `g` and `g'` it is the associator of `K₁ × K₂ × K₃`.
  let eS : (D.coprod j).ker ≃ₗ[𝕜] (D.coprod j').ker :=
    g.symm ≪≫ₗ g₁₂.symm.prodCongr (LinearEquiv.refl 𝕜 _) ≪≫ₗ LinearEquiv.prodAssoc 𝕜 _ _ _ ≪≫ₗ
      (LinearEquiv.refl 𝕜 _).prodCongr g₂₃ ≪≫ₗ g'
  have heS (v : (D.coprod j).ker) : eS v = kerCoprodMap D hj v := by
    obtain ⟨⟨k₁₂, k₃⟩, rfl⟩ := g.surjective v
    obtain ⟨⟨k₁, k₂⟩, rfl⟩ := g₁₂.surjective k₁₂
    simp [eS, hg]
  obtain ⟨x₁, rfl⟩ := (detLineStabilizationEquiv D₁ ι₁ h₁).surjective t₁
  obtain ⟨x₂, rfl⟩ := (detLineStabilizationEquiv D₂ ι₂ h₂).surjective t₂
  obtain ⟨x₃, rfl⟩ := (detLineStabilizationEquiv D₃ ι₃ h₃).surjective t₃
  rw [detLineGluingEquiv_detLineStabilizationEquiv_tmul h₁ h₂ h₁₂ g₁₂, ← smul_tmul',
    LinearEquiv.map_smul, detLineGluingEquiv_detLineStabilizationEquiv_tmul h₁₂ h₃ h g,
    detLineGluingEquiv_detLineStabilizationEquiv_tmul h₂ h₃ h₂₃ g₂₃, tmul_smul,
    LinearEquiv.map_smul, detLineGluingEquiv_detLineStabilizationEquiv_tmul h₁ h₂₃ h' g',
    TauCeti.rTensor_detLineCongr_detLineTensorDualProdEquiv_assoc g₁₂ g₂₃ g g' eS
      (fun k₁ k₂ k₃ ↦ (hg k₁ k₂ k₃).trans (heS _).symm),
    detLineStabilizationEquiv_congrKerCoker (LinearEquiv.refl 𝕜 _) eS (LinearEquiv.refl 𝕜 _)
      (fun u ↦ Subtype.ext (by simp [heS])) (fun y ↦ by simp [heS])
      (fun l ↦ by simp [parameterToCoker_apply, ← hj]) h h',
    LinearMap.detLineCongrKerCoker_refl, LinearEquiv.refl_apply, smul_smul, smul_smul]
  congr 1
  -- The Koszul signs of the two orders agree.
  have hK : finrank 𝕜 (D₂₃.coprod j₂₃).ker =
      finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 (D₃.coprod ι₃).ker := by
    rw [← g₂₃.finrank_eq, finrank_prod]
  rw [← pow_add, ← pow_add, hK, finrank_prod, finrank_prod]
  ring

end ContinuousLinearMap
