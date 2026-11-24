/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import TauCeti.Analysis.Normed.Operator.LinearPMap.ProdLp

/-!
# Transport of the operator represented by a form

Let `j : V →L[𝕜] H` be injective with dense range and `q : V →L⋆[𝕜] V →L[𝕜] 𝕜` a bounded
sesquilinear form, and let `A = closedFormOperator j hj hdense q` be the operator it represents:
`j u ∈ dom A` with `A (j u) = h` exactly when `q u v = ⟪h, j v⟫_𝕜` for every `v`. This file
transports `A` along the three operations on the data `(V, H, j, q)` that leave the form unchanged.

* **Unitary transport.** For a linear isometric equivalence `U : H ≃ₗᵢ[𝕜] H'`, the form `q` along
  `U ∘ j` represents the unitary conjugate `U A U⁻¹`.
* **Change of form-domain carrier.** For a continuous linear equivalence `e : V' ≃L[𝕜] V`, the
  pulled-back form `(u', v') ↦ q (e u') (e v')` along `j ∘ e` represents the same operator `A`.
  In particular the operator depends on the form domain only up to isometric isomorphism.
* **Finite orthogonal sums.** For two forms `q₁` along `j₁` and `q₂` along `j₂`, the sum form
  `q₁ ⊕ q₂` on `V₁ × V₂` along `j₁ × j₂ : V₁ × V₂ → WithLp 2 (H₁ × H₂)` represents the direct sum
  `A₁ ⊕ A₂` (`LinearPMap.withLpProdMap`) on the Hilbert direct sum.

None of these needs completeness, coercivity or the Hermitian property: they are statements about
the graph relation of the form, compared through
`ContinuousLinearMap.eq_closedFormOperator_of_mem_graph_iff`.

## Main results

* `ContinuousLinearMap.closedFormOperator_comp_linearIsometryEquiv`: unitary transport.
* `ContinuousLinearMap.closedFormOperator_comp_continuousLinearEquiv`: change of carrier.
* `ContinuousLinearMap.closedFormOperator_prod`: finite orthogonal sums.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.2, Theorem 2.13,
  for the operator represented by a closed form.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Unitary transport of the form operator.** For a linear isometric equivalence
`U : H ≃ₗᵢ[𝕜] H'`, the operator represented by `q` along `U ∘ j` is the unitary conjugate
`U A U⁻¹` of the operator `A` represented by `q` along `j`. -/
theorem closedFormOperator_comp_linearIsometryEquiv {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace 𝕜 H'] (j : V →L[𝕜] H) (hj : Function.Injective j) (hdense : DenseRange j)
    (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (U : H ≃ₗᵢ[𝕜] H') :
    closedFormOperator ((U : H →L[𝕜] H').comp j) (U.injective.comp hj)
        (U.surjective.denseRange.comp hdense U.continuous) q =
      (closedFormOperator j hj hdense q).conj ((U : H ≃L[𝕜] H') : H ≃ₗ[𝕜] H') := by
  refine (eq_closedFormOperator_of_mem_graph_iff _ _ _ q fun x h ↦ ?_).symm
  rw [LinearPMap.mem_graph_conj_iff, mem_graph_closedFormOperator_iff]
  refine exists_congr fun u ↦ and_congr ?_ (forall_congr' fun v ↦ ?_)
  · change j u = U.symm x ↔ U (j u) = x
    exact ⟨fun h ↦ by rw [h, U.apply_symm_apply], fun h ↦ by rw [← h, U.symm_apply_apply]⟩
  · change q u v = ⟪U.symm h, j v⟫_𝕜 ↔ q u v = ⟪h, U (j v)⟫_𝕜
    rw [← U.inner_map_map, U.apply_symm_apply]

/-- **Change of form-domain carrier.** For a continuous linear equivalence `e : V' ≃L[𝕜] V`, the
pulled-back form `(u', v') ↦ q (e u') (e v')` along `j ∘ e` represents the same operator as `q`
along `j`. -/
theorem closedFormOperator_comp_continuousLinearEquiv {V' : Type*} [SeminormedAddCommGroup V']
    [NormedSpace 𝕜 V'] (j : V →L[𝕜] H) (hj : Function.Injective j) (hdense : DenseRange j)
    (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (e : V' ≃L[𝕜] V) :
    closedFormOperator (j.comp (e : V' →L[𝕜] V)) (hj.comp e.injective)
        (by
          rw [DenseRange, coe_comp, ContinuousLinearEquiv.coe_coe, e.surjective.range_comp]
          exact hdense)
        (q.bilinearComp (e : V' →L[𝕜] V) (e : V' →L[𝕜] V)) =
      closedFormOperator j hj hdense q := by
  refine (eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h ↦ ?_).symm
  rw [mem_graph_closedFormOperator_iff]
  simp only [coe_comp, Function.comp_apply, bilinearComp_apply, ContinuousLinearEquiv.coe_coe]
  refine ⟨fun ⟨u, hu, hq⟩ ↦ ⟨e.symm u, by simpa using hu, fun v ↦ by simpa using hq (e v)⟩,
    fun ⟨u, hu, hq⟩ ↦ ⟨e u, hu, fun v ↦ ?_⟩⟩
  simpa using hq (e.symm v)

/-- **The form operator of an orthogonal sum.** For forms `q₁` along `j₁ : V₁ →L[𝕜] H₁` and `q₂`
along `j₂ : V₂ →L[𝕜] H₂`, the sum form `((u₁, u₂), (v₁, v₂)) ↦ q₁ u₁ v₁ + q₂ u₂ v₂` on
`V₁ × V₂` along `j₁ × j₂ : V₁ × V₂ → WithLp 2 (H₁ × H₂)` represents the direct sum `A₁ ⊕ A₂` of
the operators represented by `q₁` and `q₂`. -/
theorem closedFormOperator_prod {V₂ H₂ : Type*} [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) (q : V →L⋆[𝕜] V →L[𝕜] 𝕜) (j₂ : V₂ →L[𝕜] H₂)
    (hj₂ : Function.Injective j₂) (hdense₂ : DenseRange j₂) (q₂ : V₂ →L⋆[𝕜] V₂ →L[𝕜] 𝕜) :
    closedFormOperator
        (((WithLp.prodContinuousLinearEquiv 2 𝕜 H H₂).symm : H × H₂ →L[𝕜] WithLp 2 (H × H₂)).comp
          (j.prodMap j₂))
        ((WithLp.prodContinuousLinearEquiv 2 𝕜 H H₂).symm.injective.comp (hj.prodMap hj₂))
        ((WithLp.prodContinuousLinearEquiv 2 𝕜 H H₂).symm.surjective.denseRange.comp
          (hdense.prodMap hdense₂) (WithLp.prodContinuousLinearEquiv 2 𝕜 H H₂).symm.continuous)
        (q.bilinearComp (fst 𝕜 V V₂) (fst 𝕜 V V₂) + q₂.bilinearComp (snd 𝕜 V V₂) (snd 𝕜 V V₂)) =
      (closedFormOperator j hj hdense q).withLpProdMap 2
        (closedFormOperator j₂ hj₂ hdense₂ q₂) := by
  refine (eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h ↦ ?_).symm
  rw [LinearPMap.mem_graph_withLpProdMap_iff, mem_graph_closedFormOperator_iff,
    mem_graph_closedFormOperator_iff]
  simp only [coe_comp, Function.comp_apply, add_apply, bilinearComp_apply, coe_fst', coe_snd',
    WithLp.prod_inner_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, coe_prodMap', Prod.forall]
  constructor
  · rintro ⟨⟨u, hu, hq⟩, ⟨u₂, hu₂, hq₂⟩⟩
    refine ⟨(u, u₂), WithLp.ofLp_injective 2 (Prod.ext hu hu₂), fun v v₂ ↦ ?_⟩
    simp [hq, hq₂]
  · rintro ⟨⟨u, u₂⟩, hu, hq⟩
    subst hu
    refine ⟨⟨u, rfl, fun v ↦ by simpa using hq v 0⟩, ⟨u₂, rfl, fun v₂ ↦ by simpa using hq 0 v₂⟩⟩

end ContinuousLinearMap
