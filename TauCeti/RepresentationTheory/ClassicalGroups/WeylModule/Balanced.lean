/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Decomposition
public import TauCeti.RepresentationTheory.Symmetric.Specht.Complex
-- Non-public: the Specht module is exhibited as a retract of the regular representation only
-- inside the proof of `TauCeti.balancedSchurPresentation`; no statement mentions the retract or
-- the coinvariant contraction.
import TauCeti.RepresentationTheory.Symmetric.Specht.Retract
import TauCeti.RepresentationTheory.Tensor.Coinvariants

/-!
# The balanced tensor presentation of the Schur functor

The tensor power `(ℂᵈ)^{⊗n}` is a right module over `ℂ[Sₙ]` through `v · σ = σ⁻¹ v`, and the
complex Specht module `S^μ` of a partition `μ` of `n` is a left module, so they have a balanced
tensor product `(ℂᵈ)^{⊗n} ⊗_{ℂ[Sₙ]} S^μ`: the quotient of `(ℂᵈ)^{⊗n} ⊗ S^μ` by the balancing
relations `(v · σ) ⊗ s - v ⊗ (σ · s)`, `TauCeti.balancedSchurRelations d n μ`. The general linear
group `GL d ℂ`, acting diagonally on the tensor power, commutes with `Sₙ` and so acts on it.
This file proves that it is the Schur functor `𝕊^μ(ℂᵈ)` (`TauCeti.balancedSchurPresentation`):
there is a surjective, `GL d ℂ`-equivariant linear map `(ℂᵈ)^{⊗n} ⊗ S^μ → 𝕊^μ(ℂᵈ)` whose kernel
is exactly the span of the balancing relations. This is the classical definition
`𝕊^μ V = V^{⊗n} ⊗_{ℂ[Sₙ]} S^μ` of the Schur functor, compared with its construction as the image
`c_μ V^{⊗n}` of a Young symmetrizer. Both vanish when `μ` has more than `d` rows.

The balanced tensor product is the coinvariants `((ℂᵈ)^{⊗n} ⊗ S^μ)_{Sₙ}`
(`TauCeti.coinvariantsKer_tprod_eq_balancedSchurRelations`), and for a retract `W` of the regular
representation, with idempotent `e`, the coinvariants `(V ⊗ W)_G` are the image of the antipode
of `e` acting on `V` (`Representation.IntertwiningMap.ker_tprodContraction` and
`Representation.IntertwiningMap.range_tprodContraction`). The proof exhibits `S^μ` as such a
retract, with an idempotent whose antipode is a nonzero multiple of the Young symmetrizer `c_μ`
itself (`TauCeti.exists_retract_spechtModuleℂ`). The image of `c_μ` is the Weyl module of `μ`
(`TauCeti.weylRepOfShapeEquivRange`), which is the Schur functor.

## Main definitions

* `TauCeti.balancedSchurRelations`: the balancing relations in `(ℂᵈ)^{⊗n} ⊗ S^μ`.

## Main results

* `TauCeti.coinvariantsKer_tprod_eq_balancedSchurRelations`: they are the coinvariant kernel.
* `TauCeti.balancedSchurRelations_le_comap_rTensor`: they are invariant under `GL d ℂ`.
* `TauCeti.balancedSchurRelations_le_ker_lift_iff`: a bilinear map factors through the quotient
  exactly when it is balanced.
* `TauCeti.balancedSchurPresentation`: **the balanced tensor presentation**: the quotient by them
  is `𝕊^μ(ℂᵈ)`, as a representation of `GL d ℂ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §6.1, where
  `𝕊_λ V = V^{⊗d} ⊗_{ℂ[S_d]} V_λ` is identified with the image `V^{⊗d} c_λ`.
-/

public section

open Representation
open scoped TensorProduct

namespace TauCeti


variable (d n : ℕ) (μ : n.Partition)

/-- **The balancing relations** of `(ℂᵈ)^{⊗n} ⊗ S^μ`: the complex span of
`(v · σ) ⊗ s - v ⊗ (σ · s)` for `σ ∈ Sₙ`, where `v · σ = σ⁻¹ v` makes the tensor power a right
module over `ℂ[Sₙ]`. The quotient by them is the balanced tensor product
`(ℂᵈ)^{⊗n} ⊗_{ℂ[Sₙ]} S^μ`; by linearity the relations for every `a ∈ ℂ[Sₙ]` lie in the span. -/
noncomputable def balancedSchurRelations :
    Submodule ℂ ((⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) ⊗[ℂ] spechtModuleℂ μ) :=
  Submodule.span ℂ {x | ∃ (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) (s : spechtModuleℂ μ)
    (g : Equiv.Perm (Fin n)),
    x = permTensorAction ℂ d n g⁻¹ v ⊗ₜ[ℂ] s - v ⊗ₜ[ℂ] (spechtModuleℂ μ).ρ g s}

/-- The balancing relations are the span of the relations `(v · σ) ⊗ s - v ⊗ (σ · s)`. -/
theorem balancedSchurRelations_def :
    balancedSchurRelations d n μ = Submodule.span ℂ {x | ∃ (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ))
      (s : spechtModuleℂ μ) (g : Equiv.Perm (Fin n)),
      x = permTensorAction ℂ d n g⁻¹ v ⊗ₜ[ℂ] s - v ⊗ₜ[ℂ] (spechtModuleℂ μ).ρ g s} :=
  (rfl)

/-- **The balancing relations are the coinvariant kernel** of the tensor product of the
permutation action with the Specht action: the balanced tensor product is the coinvariants
`((ℂᵈ)^{⊗n} ⊗ S^μ)_{Sₙ}`. -/
theorem coinvariantsKer_tprod_eq_balancedSchurRelations :
    Coinvariants.ker (V := (⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) ⊗[ℂ] spechtModuleℂ μ)
      ((permTensorAction ℂ d n).tprod (spechtModuleℂ μ).ρ) = balancedSchurRelations d n μ :=
  coinvariantsKer_tprod_eq_span (permTensorAction ℂ d n) (spechtModuleℂ μ).ρ

/-- Each balancing relation `(v · σ) ⊗ s - v ⊗ (σ · s)` lies in the span of the balancing
relations. -/
theorem sub_mem_balancedSchurRelations (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ))
    (s : spechtModuleℂ μ) (g : Equiv.Perm (Fin n)) :
    permTensorAction ℂ d n g⁻¹ v ⊗ₜ[ℂ] s - v ⊗ₜ[ℂ] (spechtModuleℂ μ).ρ g s ∈
      balancedSchurRelations d n μ := by
  rw [balancedSchurRelations_def]
  exact Submodule.subset_span ⟨v, s, g, rfl⟩

/-- **The universal property of the balanced tensor product**: a bilinear map out of
`(ℂᵈ)^{⊗n} × S^μ` vanishes on the balancing relations, and so factors through the quotient by
them (`Submodule.liftQ`, uniquely since the quotient map is onto), exactly when it is balanced,
sending `(v · σ, s)` and `(v, σ · s)` to the same value. -/
theorem balancedSchurRelations_le_ker_lift_iff {M : Type*} [AddCommGroup M] [Module ℂ M]
    (B : (⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) →ₗ[ℂ] spechtModuleℂ μ →ₗ[ℂ] M) :
    balancedSchurRelations d n μ ≤ LinearMap.ker (TensorProduct.lift B) ↔
      ∀ v s g, B (permTensorAction ℂ d n g⁻¹ v) s = B v ((spechtModuleℂ μ).ρ g s) := by
  rw [balancedSchurRelations_def, Submodule.span_le]
  refine ⟨fun h v s g => ?_, ?_⟩
  · have := h ⟨v, s, g, rfl⟩
    rwa [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
      TensorProduct.lift.tmul, sub_eq_zero] at this
  · rintro h _ ⟨v, s, g, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
      TensorProduct.lift.tmul, h, sub_self]

/-- **The balancing relations are invariant under `GL d ℂ`** acting on the tensor-power factor,
because that action commutes with the permutation of the tensor factors. So `GL d ℂ` acts on the
balanced tensor product. -/
theorem balancedSchurRelations_le_comap_rTensor (g : GL (Fin d) ℂ) :
    balancedSchurRelations d n μ ≤ (balancedSchurRelations d n μ).comap
      ((tensorPowerRep ℂ d n g).rTensor (spechtModuleℂ μ)) := by
  rw [balancedSchurRelations_def, Submodule.span_le]
  rintro _ ⟨v, s, σ, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, LinearMap.rTensor_tmul,
    tensorPowerRep_permTensorAction_apply]
  exact sub_mem_balancedSchurRelations d n μ _ s σ

/-- **The balanced tensor presentation of the Schur functor.** There is a surjective linear map
`(ℂᵈ)^{⊗n} ⊗ S^μ → 𝕊^μ(ℂᵈ)` whose kernel is exactly the span of the balancing relations
`(v · σ) ⊗ s - v ⊗ (σ · s)`, and which intertwines the diagonal action of `GL d ℂ` on the
tensor-power factor with the action on the Schur functor. So it induces a `GL d ℂ`-equivariant
equivalence `(ℂᵈ)^{⊗n} ⊗_{ℂ[Sₙ]} S^μ ≅ 𝕊^μ(ℂᵈ)`, also when `μ` has more than `d` rows, where
both sides vanish. -/
theorem balancedSchurPresentation :
    ∃ f : ((⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) ⊗[ℂ] spechtModuleℂ μ) →ₗ[ℂ]
        schurFunctor d (YoungDiagram.ofPartition μ),
      Function.Surjective f ∧ LinearMap.ker f = balancedSchurRelations d n μ ∧
      ∀ (g : GL (Fin d) ℂ) (v : ⨂[ℂ] (_ : Fin n), (Fin d → ℂ)) (s : spechtModuleℂ μ),
        f ((tensorPowerRep ℂ d n g v) ⊗ₜ[ℂ] s) =
          (schurFunctor d (YoungDiagram.ofPartition μ)).ρ g (f (v ⊗ₜ[ℂ] s)) := by
  obtain ⟨i, p, hpi, c, hc, he⟩ := exists_retract_spechtModuleℂ μ
  -- the contraction `v ⊗ s ↦ S(i s) · v` has image `c_μ (ℂᵈ)^{⊗n}`, identified with `𝕊^μ(ℂᵈ)`
  let F := i.tprodContraction (permTensorAction ℂ d n)
  have hrange : LinearMap.range F =
      LinearMap.range ((permTensorAction ℂ d n).asAlgebraHom (μ.youngSymmetrizer ℂ)) := by
    rw [IntertwiningMap.range_tprodContraction hpi, he, map_smul, LinearMap.range_smul _ _ hc]
  let W := weylRepOfShapeEquivRange ℂ d n μ
  let e := (LinearEquiv.ofEq _ _ hrange).trans W.symm.toLinearEquiv
  refine ⟨e.toLinearMap ∘ₗ F.rangeRestrict, e.surjective.comp F.surjective_rangeRestrict, ?_, ?_⟩
  · rw [LinearEquiv.ker_comp, LinearMap.ker_rangeRestrict, IntertwiningMap.ker_tprodContraction hpi,
      coinvariantsKer_tprod_eq_balancedSchurRelations]
  · intro g v s
    have hF : F (tensorPowerRep ℂ d n g v ⊗ₜ s) = tensorPowerRep ℂ d n g (F (v ⊗ₜ s)) := by
      simp only [F, IntertwiningMap.tprodContraction_tmul,
        tensorPowerRep_asAlgebraHom_permTensorAction_apply]
    -- `LinearEquiv.ofEq`, `rangeRestrict` and the action on the subrepresentation all act on the
    -- underlying vectors, so after coercion this is `hF`
    have hr : LinearEquiv.ofEq _ _ hrange (F.rangeRestrict (tensorPowerRep ℂ d n g v ⊗ₜ s)) =
        (tensorPowerRep ℂ d n).subrepresentation _
          (range_asAlgebraHom_permTensorAction_le_comap ℂ d n _) g
          (LinearEquiv.ofEq _ _ hrange (F.rangeRestrict (v ⊗ₜ s))) :=
      Subtype.ext (by simpa using hF)
    have hW := LinearMap.congr_fun (W.symm.toIntertwiningMap.isIntertwining' g)
      (LinearEquiv.ofEq _ _ hrange (F.rangeRestrict (v ⊗ₜ s)))
    simp only [LinearMap.coe_comp, Function.comp_apply] at hW
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
      LinearEquiv.trans_apply, hr, Representation.Equiv.toLinearEquiv_apply, FDRep.of_ρ']
    exact hW

end TauCeti
