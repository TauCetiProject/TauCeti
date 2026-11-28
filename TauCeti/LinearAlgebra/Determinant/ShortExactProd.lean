/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.DirectSum

/-!
# Determinant lines of products of short exact sequences

The product of two short exact sequences `0 → Uᵢ → Vᵢ → Wᵢ → 0` of finite-dimensional vector
spaces is exact, and its isomorphism `det (U₁ × U₂) ⊗ det (W₁ × W₂) ≃ det (V₁ × V₂)`
(`TauCeti.detLineShortExactEquiv`) is the product of the isomorphisms of the two sequences, read
through `TauCeti.detLineProdEquiv`, up to the Koszul sign `(-1) ^ (dim U₂ * dim W₁)` of moving the
lifts of `W₁` past the directions of `U₂`
(`TauCeti.detLineProdEquiv_detLineShortExactEquiv_tmul`).

Consequently, for pairs of short exact sequences `0 → Uᵢ → Vᵢ → Wᵢ → 0` and
`0 → Uᵢ' → Vᵢ' → Wᵢ → 0` with common quotients, cancelling the common quotient `W₁ × W₂` of the
product sequences (`TauCeti.detLineShortExactCancelEquiv`) is the product of the cancellations of
`W₁` and `W₂`, read through `TauCeti.detLineTensorDualProdEquiv`, up to the sign
`(-1) ^ ((dim U₂ + dim U₂') * dim W₁)` (`TauCeti.detLineShortExactCancelEquiv_prodMap`). Enlarging
the finite-dimensional stabilizers of a Fredholm operator acts on its stabilized determinant line
by such a cancellation (`ContinuousLinearMap.detLineCoprodMapEquiv`), so this is how enlarging the
stabilizers of two operators at once acts on their gathered stabilized determinant lines, as in
linear gluing (`TauCeti.Analysis.Fredholm.DeterminantLine.Gluing`). It is the short exact
counterpart of the product law for four-term sequences, `TauCeti.detLineFourTermEquiv_prodMap`.

## Main results

* `TauCeti.detLineProdEquiv_detLineShortExactEquiv_tmul`: the isomorphism of a product of short
  exact sequences is the product of the isomorphisms, up to a Koszul sign.
* `TauCeti.detLineShortExactCancelEquiv_prodMap`: cancelling the common quotient of products of
  short exact sequences is the product of the cancellations, up to a Koszul sign.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, [arXiv:1304.6368](https://arxiv.org/abs/1304.6368) (the canonical
  isomorphisms of determinant lines and their sign conventions).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable {K : Type*} [Field K] {U₁ V₁ W₁ U₂ V₂ W₂ : Type*} [AddCommGroup U₁] [Module K U₁]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup W₁] [Module K W₁] [AddCommGroup U₂] [Module K U₂]
  [AddCommGroup V₂] [Module K V₂] [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K U₁]
  [FiniteDimensional K V₁] [FiniteDimensional K W₁] [FiniteDimensional K U₂]
  [FiniteDimensional K V₂] [FiniteDimensional K W₂] {f₁ : U₁ →ₗ[K] V₁} {g₁ : V₁ →ₗ[K] W₁}
  {f₂ : U₂ →ₗ[K] V₂} {g₂ : V₂ →ₗ[K] W₂} (hf₁ : Function.Injective f₁)
  (hfg₁ : Function.Exact f₁ g₁) (hg₁ : Function.Surjective g₁) (hf₂ : Function.Injective f₂)
  (hfg₂ : Function.Exact f₂ g₂) (hg₂ : Function.Surjective g₂)

include hf₁ hfg₁ hg₁ hf₂ hfg₂ hg₂ in
/-- `TauCeti.detLineProdEquiv_detLineShortExactEquiv_tmul` on exterior products of bases `uᵢ` of
`Uᵢ` and of lifts `vᵢ` of bases of `Wᵢ`: both sides are the exterior product of `(fᵢ uᵢ)` followed
by the lifts `(vᵢ)`, in the order `u₁, u₂, v₁, v₂`, and the left side exchanges `v₁` and `u₂`. -/
private theorem detLineProdEquiv_detLineShortExactEquiv_ιMulti (u₁ : Fin (finrank K U₁) → U₁)
    (v₁ : Fin (finrank K W₁) → V₁) (u₂ : Fin (finrank K U₂) → U₂) (v₂ : Fin (finrank K W₂) → V₂) :
    detLineProdEquiv K V₁ V₂ (detLineShortExactEquiv hf₁ hfg₁ hg₁
        (exteriorPower.ιMulti K _ u₁ ⊗ₜ exteriorPower.ιMulti K _ (g₁ ∘ v₁)) ⊗ₜ
        detLineShortExactEquiv hf₂ hfg₂ hg₂
          (exteriorPower.ιMulti K _ u₂ ⊗ₜ exteriorPower.ιMulti K _ (g₂ ∘ v₂))) =
      (-1 : K) ^ (finrank K U₂ * finrank K W₁) •
        detLineShortExactEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂) (hf₁.prodMap hf₂)
          (hfg₁.prodMap hfg₂) (hg₁.prodMap hg₂)
          (detLineProdEquiv K U₁ U₂
              (exteriorPower.ιMulti K _ u₁ ⊗ₜ exteriorPower.ιMulti K _ u₂) ⊗ₜ
            detLineProdEquiv K W₁ W₂
              (exteriorPower.ιMulti K _ (g₁ ∘ v₁) ⊗ₜ exteriorPower.ιMulti K _ (g₂ ∘ v₂))) := by
  have hU : finrank K (U₁ × U₂) = finrank K U₁ + finrank K U₂ := Module.finrank_prod
  have hW : finrank K (W₁ × W₂) = finrank K W₁ + finrank K W₂ := Module.finrank_prod
  have hu : exteriorPower.ιMulti K _
      (Fin.append (LinearMap.inl K U₁ U₂ ∘ u₁) (LinearMap.inr K U₁ U₂ ∘ u₂) ∘ Fin.cast hU) =
      detLineProdEquiv K U₁ U₂ (exteriorPower.ιMulti K _ u₁ ⊗ₜ exteriorPower.ιMulti K _ u₂) :=
    Subtype.ext (by rw [coe_detLineProdEquiv_tmul, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_comp_cast])
  have hw : exteriorPower.ιMulti K _ (⇑(g₁.prodMap g₂) ∘
      (Fin.append (LinearMap.inl K V₁ V₂ ∘ v₁) (LinearMap.inr K V₁ V₂ ∘ v₂) ∘ Fin.cast hW)) =
      detLineProdEquiv K W₁ W₂
        (exteriorPower.ιMulti K _ (g₁ ∘ v₁) ⊗ₜ exteriorPower.ιMulti K _ (g₂ ∘ v₂)) :=
    Subtype.ext (by rw [coe_detLineProdEquiv_tmul, exteriorPower.ιMulti_apply_coe,
      ← Function.comp_assoc, LinearMap.prodMap_comp_append, ExteriorAlgebra.ιMulti_comp_cast])
  have h := coe_smul_detLineProdEquiv_tmul
    (coe_detLineShortExactEquiv_tmul hf₁ hfg₁ hg₁ u₁ v₁)
    (coe_detLineShortExactEquiv_tmul hf₂ hfg₂ hg₂ u₂ v₂) hU hW
  have h' := coe_detLineShortExactEquiv_tmul (f := f₁.prodMap f₂) (g := g₁.prodMap g₂)
    (hf₁.prodMap hf₂) (hfg₁.prodMap hfg₂) (hg₁.prodMap hg₂)
    (Fin.append (LinearMap.inl K U₁ U₂ ∘ u₁) (LinearMap.inr K U₁ U₂ ∘ u₂) ∘ Fin.cast hU)
    (Fin.append (LinearMap.inl K V₁ V₂ ∘ v₁) (LinearMap.inr K V₁ V₂ ∘ v₂) ∘ Fin.cast hW)
  refine Subtype.ext ?_
  rw [← hu, ← hw, Submodule.coe_smul, h', ← Function.comp_assoc,
    LinearMap.prodMap_comp_append, ← h, Submodule.coe_smul, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]

include hf₁ hfg₁ hg₁ hf₂ hfg₂ hg₂ in
/-- **The short exact isomorphism of a product of sequences.** The product of two short exact
sequences `0 → Uᵢ → Vᵢ → Wᵢ → 0` is exact, and its isomorphism
`det (U₁ × U₂) ⊗ det (W₁ × W₂) ≃ det (V₁ × V₂)` (`TauCeti.detLineShortExactEquiv`) is the product
of the isomorphisms of the two sequences, read through `TauCeti.detLineProdEquiv`, up to the sign
`(-1) ^ (dim U₂ * dim W₁)`: the isomorphism of a sequence puts the directions of the subspace
first, and the product exchanges the lifts of `W₁` with the directions of `U₂`. -/
theorem detLineProdEquiv_detLineShortExactEquiv_tmul (a₁ : detLine K U₁) (w₁ : detLine K W₁)
    (a₂ : detLine K U₂) (w₂ : detLine K W₂) :
    detLineProdEquiv K V₁ V₂ (detLineShortExactEquiv hf₁ hfg₁ hg₁ (a₁ ⊗ₜ w₁) ⊗ₜ
        detLineShortExactEquiv hf₂ hfg₂ hg₂ (a₂ ⊗ₜ w₂)) =
      (-1 : K) ^ (finrank K U₂ * finrank K W₁) •
        detLineShortExactEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂) (hf₁.prodMap hf₂)
          (hfg₁.prodMap hfg₂) (hg₁.prodMap hg₂)
          (detLineProdEquiv K U₁ U₂ (a₁ ⊗ₜ a₂) ⊗ₜ detLineProdEquiv K W₁ W₂ (w₁ ⊗ₜ w₂)) := by
  -- Every element of `det Uᵢ` and of `det Wᵢ` is a multiple of the exterior product of a basis,
  -- and that of `Wᵢ` is the image of `dim Wᵢ` vectors `vᵢ` of `Vᵢ`.
  choose v₁ hv₁ using fun i ↦ hg₁ (Module.finBasis K W₁ i)
  choose v₂ hv₂ using fun i ↦ hg₂ (Module.finBasis K W₂ i)
  obtain ⟨r₁, rfl⟩ := (Module.finBasis K U₁).exists_smul_ιMulti_eq a₁
  obtain ⟨s₁, rfl⟩ := (Module.finBasis K W₁).exists_smul_ιMulti_eq w₁
  obtain ⟨r₂, rfl⟩ := (Module.finBasis K U₂).exists_smul_ιMulti_eq a₂
  obtain ⟨s₂, rfl⟩ := (Module.finBasis K W₂).exists_smul_ιMulti_eq w₂
  rw [show ⇑(Module.finBasis K W₁) = g₁ ∘ v₁ from (funext hv₁).symm,
    show ⇑(Module.finBasis K W₂) = g₂ ∘ v₂ from (funext hv₂).symm]
  simp only [← smul_tmul', tmul_smul, map_smul, smul_smul]
  rw [detLineProdEquiv_detLineShortExactEquiv_ιMulti, smul_smul]
  congr 1
  ring

include hf₁ hfg₁ hg₁ hf₂ hfg₂ hg₂ in
/-- The functional on `det (U₁ × U₂)` obtained from the product `φ` of `φ₁` and `φ₂` and the
product `w` of `w₁ ∈ det W₁` and `w₂ ∈ det W₂` through the product sequence, `a ↦ φ (a ∧ w)`, is
`(-1) ^ (dim U₂ * dim W₁)` times the product of the functionals `aᵢ ↦ φᵢ (aᵢ ∧ wᵢ)`. -/
private theorem detLineDualProdEquiv_comp_detLineShortExactEquiv (φ₁ : Dual K (detLine K V₁))
    (φ₂ : Dual K (detLine K V₂)) (w₁ : detLine K W₁) (w₂ : detLine K W₂) :
    detLineDualProdEquiv K V₁ V₂ (φ₁ ⊗ₜ φ₂) ∘ₗ
      (detLineShortExactEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂) (hf₁.prodMap hf₂)
        (hfg₁.prodMap hfg₂) (hg₁.prodMap hg₂)).toLinearMap ∘ₗ
      (TensorProduct.mk K _ _).flip (detLineProdEquiv K W₁ W₂ (w₁ ⊗ₜ w₂)) =
      (-1 : K) ^ (finrank K U₂ * finrank K W₁) • detLineDualProdEquiv K U₁ U₂
        ((φ₁ ∘ₗ (detLineShortExactEquiv hf₁ hfg₁ hg₁).toLinearMap ∘ₗ
          (TensorProduct.mk K _ _).flip w₁) ⊗ₜ
        (φ₂ ∘ₗ (detLineShortExactEquiv hf₂ hfg₂ hg₂).toLinearMap ∘ₗ
          (TensorProduct.mk K _ _).flip w₂)) := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨t, rfl⟩ := (detLineProdEquiv K U₁ U₂).surjective c
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul c₁ c₂ =>
  have h := detLineProdEquiv_detLineShortExactEquiv_tmul hf₁ hfg₁ hg₁ hf₂ hfg₂ hg₂ c₁ w₁ c₂ w₂
  have h' : detLineShortExactEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂)
      (hf₁.prodMap hf₂) (hfg₁.prodMap hfg₂) (hg₁.prodMap hg₂)
      (detLineProdEquiv K U₁ U₂ (c₁ ⊗ₜ c₂) ⊗ₜ detLineProdEquiv K W₁ W₂ (w₁ ⊗ₜ w₂)) =
      (-1 : K) ^ (finrank K U₂ * finrank K W₁) • detLineProdEquiv K V₁ V₂
        (detLineShortExactEquiv hf₁ hfg₁ hg₁ (c₁ ⊗ₜ w₁) ⊗ₜ
          detLineShortExactEquiv hf₂ hfg₂ hg₂ (c₂ ⊗ₜ w₂)) := by
    rw [h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearEquiv.coe_coe, LinearMap.smul_apply, h', map_smul, detLineDualProdEquiv_tmul_apply]

variable {U₁' V₁' U₂' V₂' : Type*} [AddCommGroup U₁'] [Module K U₁'] [AddCommGroup V₁']
  [Module K V₁'] [AddCommGroup U₂'] [Module K U₂'] [AddCommGroup V₂'] [Module K V₂']
  [FiniteDimensional K U₁'] [FiniteDimensional K V₁'] [FiniteDimensional K U₂']
  [FiniteDimensional K V₂'] {f₁' : U₁' →ₗ[K] V₁'} {g₁' : V₁' →ₗ[K] W₁} {f₂' : U₂' →ₗ[K] V₂'}
  {g₂' : V₂' →ₗ[K] W₂} (hf₁' : Function.Injective f₁') (hfg₁' : Function.Exact f₁' g₁')
  (hg₁' : Function.Surjective g₁') (hf₂' : Function.Injective f₂')
  (hfg₂' : Function.Exact f₂' g₂') (hg₂' : Function.Surjective g₂')

include hf₁ hfg₁ hg₁ hf₂ hfg₂ hg₂ hf₁' hfg₁' hg₁' hf₂' hfg₂' hg₂' in
/-- **Cancelling the common quotient of a product.** For pairs of short exact sequences
`0 → Uᵢ → Vᵢ → Wᵢ → 0` and `0 → Uᵢ' → Vᵢ' → Wᵢ → 0` with common quotients `Wᵢ`, cancelling the
quotient `W₁ × W₂` of the product sequences (`TauCeti.detLineShortExactCancelEquiv`) is the
product of the cancellations of `W₁` and `W₂`, read through
`TauCeti.detLineTensorDualProdEquiv`, up to the sign `(-1) ^ ((dim U₂ + dim U₂') * dim W₁)`. -/
theorem detLineShortExactCancelEquiv_prodMap
    (x₁ : detLine K V₁ ⊗[K] Dual K (detLine K V₁'))
    (x₂ : detLine K V₂ ⊗[K] Dual K (detLine K V₂')) :
    detLineShortExactCancelEquiv (f := f₁.prodMap f₂) (g := g₁.prodMap g₂)
        (f' := f₁'.prodMap f₂') (g' := g₁'.prodMap g₂') (hf₁.prodMap hf₂) (hfg₁.prodMap hfg₂)
        (hg₁.prodMap hg₂) (hf₁'.prodMap hf₂') (hfg₁'.prodMap hfg₂') (hg₁'.prodMap hg₂')
        (detLineTensorDualProdEquiv K V₁ V₁' V₂ V₂' (x₁ ⊗ₜ x₂)) =
      (-1 : K) ^ ((finrank K U₂ + finrank K U₂') * finrank K W₁) •
        detLineTensorDualProdEquiv K U₁ U₁' U₂ U₂'
          (detLineShortExactCancelEquiv hf₁ hfg₁ hg₁ hf₁' hfg₁' hg₁' x₁ ⊗ₜ
            detLineShortExactCancelEquiv hf₂ hfg₂ hg₂ hf₂' hfg₂' hg₂' x₂) := by
  -- Both sides are linear in `x₁` and `x₂`, and `det Vᵢ` is the image of `det Uᵢ ⊗ det Wᵢ`.
  induction x₁ using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx', smul_add]
  | tmul y₁ φ₁ =>
  induction x₂ using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.tmul_add, map_add, hx, hx', smul_add]
  | tmul y₂ φ₂ =>
  obtain ⟨z₁, rfl⟩ := (detLineShortExactEquiv hf₁ hfg₁ hg₁).surjective y₁
  obtain ⟨z₂, rfl⟩ := (detLineShortExactEquiv hf₂ hfg₂ hg₂).surjective y₂
  induction z₁ using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx', smul_add]
  | tmul a₁ w₁ =>
  induction z₂ using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [add_tmul, tmul_add, map_add, hx, hx', smul_add]
  | tmul a₂ w₂ =>
  have hc := detLineShortExactCancelEquiv_tmul (f := f₁.prodMap f₂) (g := g₁.prodMap g₂)
    (f' := f₁'.prodMap f₂') (g' := g₁'.prodMap g₂') (hf₁.prodMap hf₂) (hfg₁.prodMap hfg₂)
    (hg₁.prodMap hg₂) (hf₁'.prodMap hf₂') (hfg₁'.prodMap hfg₂') (hg₁'.prodMap hg₂')
    (detLineProdEquiv K U₁ U₂ (a₁ ⊗ₜ a₂)) (detLineProdEquiv K W₁ W₂ (w₁ ⊗ₜ w₂))
    (detLineDualProdEquiv K V₁' V₂' (φ₁ ⊗ₜ φ₂))
  -- The functional produced by the cancellation of `W₁ × W₂` is the product of those produced by
  -- the cancellations of `W₁` and `W₂`, up to `(-1) ^ (dim U₂' * dim W₁)`.
  have hφ := detLineDualProdEquiv_comp_detLineShortExactEquiv hf₁' hfg₁' hg₁' hf₂' hfg₂' hg₂'
    φ₁ φ₂ w₁ w₂
  rw [detLineTensorDualProdEquiv_tmul, detLineProdEquiv_detLineShortExactEquiv_tmul,
    ← smul_tmul', map_smul, hc, detLineShortExactCancelEquiv_tmul,
    detLineShortExactCancelEquiv_tmul, detLineTensorDualProdEquiv_tmul, hφ, tmul_smul, smul_smul,
    ← pow_add, add_mul]

end TauCeti
