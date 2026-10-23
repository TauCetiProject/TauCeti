/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Noetherian
public import TauCeti.RingTheory.Huber.ModuleTopology.Complete
public import TauCeti.Topology.Algebra.Module.Completion

import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Topology.Algebra.Nonarchimedean.Completion.Surjective
import TauCeti.Topology.Algebra.Nonarchimedean.Pi
import TauCeti.Topology.UniformSpace.AbstractCompletion

/-!
# Completion of a finite module over a Huber ring is base change to the completed ring

Let `A` be a Huber ring with a pair of definition `(A₀, I)` such that `A₀` is noetherian, `Â` its
completion and `M` a finitely generated `A`-module with its natural topology. The canonical map
`Â ⊗[A] M → M̂` (`UniformSpace.Completion.ofTensorProduct`) is bijective, and it is a homeomorphism
when `Â ⊗[A] M` carries its natural `Â`-module topology
(Huber, *A generalization of formal schemes and rigid analytic varieties*, Lemma 2.3(iii)).
Neither `A` nor `M` is assumed complete or Hausdorff: for `A = ℤ` with the `p`-adic topology and
`M = ℤ ⧸ ℓ` with `ℓ ≠ p` prime, `M` is indiscrete and both sides vanish.

This is the identification of the completed Čech complexes of finite modules with the Čech
complexes of their base changes, used in Huber's sheafiness theorem for rings with a noetherian
ring of definition.

## Implementation notes

Choose a surjection `q : Aⁿ → M` with kernel `K`. Identifying the completion of `Aⁿ` with `Âⁿ`
(`AbstractCompletion.pi`), completion of the open surjection `q` is an open surjection
`ψ : Âⁿ → M̂` whose kernel is the closure of the image of `K`
(`AddMonoidHom.surjective_completion`, `AddMonoidHom.ker_completion`). On the other side,
`Âⁿ → Â ⊗[A] M` is surjective and kills the `Â`-submodule spanned by `K`. The ring of definition
of `Â` is noetherian (`TauCeti.Huber.PairOfDefinition.isNoetherianRing_completion`) and `Â` is
complete, so every `Â`-submodule of `Âⁿ` is closed
(`TauCeti.Huber.PairOfDefinition.isClosed_of_isNoetherianRing`); in particular the closure of
the image of `K` lies in its `Â`-span, which gives injectivity.

## Main results

* `TauCeti.Huber.PairOfDefinition.ofTensorProduct_bijective`: `Â ⊗[A] M → M̂` is bijective.
* `TauCeti.Huber.PairOfDefinition.isHomeomorph_ofTensorProduct`: it is a homeomorphism for the
  natural `Â`-module topology on `Â ⊗[A] M`.
* `TauCeti.Huber.PairOfDefinition.ofTensorProductEquiv`: the resulting `A`-linear equivalence.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(iii) and its proof.
-/

public section

open Topology TensorProduct UniformSpace

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M]

section Presentation

/-! ### A presentation `q : Aⁿ → M` and the two maps out of `Âⁿ` -/

variable {n : ℕ} (q : (Fin n → A) →ₗ[A] M)

/-- The map `Âⁿ → Â ⊗[A] M`, `x ↦ ∑ xᵢ ⊗ q(eᵢ)`, induced by a presentation `q : Aⁿ → M`: the base
change of `q` along `A → Â`, read through `Â ⊗[A] Aⁿ ≃ Âⁿ`. -/
private noncomputable def tensorOfPresentation :
    (Fin n → Completion A) →ₗ[Completion A] Completion A ⊗[A] M :=
  q.baseChange (Completion A) ∘ₗ
    (piScalarRight A (Completion A) (Completion A) (Fin n)).symm.toLinearMap

private theorem tensorOfPresentation_apply (x : Fin n → Completion A) :
    tensorOfPresentation q x = ∑ i, x i ⊗ₜ q (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  simp [tensorOfPresentation]

/-- `tensorOfPresentation q` sends the image of `v ∈ Aⁿ` to `1 ⊗ q v`. -/
private theorem tensorOfPresentation_coe (v : Fin n → A) :
    tensorOfPresentation q (fun i ↦ (v i : Completion A)) = 1 ⊗ₜ q v := by
  have : (piScalarRight A (Completion A) (Completion A) (Fin n)).symm
      (fun i ↦ (v i : Completion A)) = 1 ⊗ₜ v := by
    rw [LinearEquiv.symm_apply_eq, piScalarRight_apply, piScalarRightHom_tmul]
    ext i
    rw [← Completion.coe_one, ← Completion.coe_smul, smul_eq_mul, mul_one]
  simp [tensorOfPresentation, this]

private theorem tensorOfPresentation_surjective (hq : Function.Surjective q) :
    Function.Surjective (tensorOfPresentation q) :=
  (LinearMap.baseChange_surjective _ hq).comp (LinearEquiv.surjective _)

variable [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology A M]
  [UniformContinuousConstSMul A M]

private theorem continuous_ofTensorProduct_comp_tensorOfPresentation :
    Continuous (Completion.ofTensorProduct A M ∘ tensorOfPresentation q) := by
  have : Completion.ofTensorProduct A M ∘ tensorOfPresentation q = fun x ↦
      ∑ i, Completion.ofTensorProduct A M (x i ⊗ₜ q (Pi.single i 1)) := by
    ext x
    simp [tensorOfPresentation_apply]
  rw [this]
  exact continuous_finsetSum _ fun i _ ↦
    (Completion.continuous_ofTensorProduct_tmul _).comp (continuous_apply i)

/-- Up to `Completion (Fin n → A) ≃ Fin n → Â`, the composite `Âⁿ → Â ⊗[A] M → M̂` is the
completion of `q`. -/
private theorem ofTensorProduct_comp_tensorOfPresentation_comp_piEquiv :
    Completion.ofTensorProduct A M ∘ tensorOfPresentation q ∘ Completion.piEquiv (fun _ ↦ A) =
      q.toAddMonoidHom.completion (IsModuleTopology.continuous_of_linearMap q) := by
  refine Completion.ext ((continuous_ofTensorProduct_comp_tensorOfPresentation q).comp
    (Completion.piEquiv _).continuous) (AddMonoidHom.continuous_completion _ _) fun v ↦
    (?_ : _ = ((q v : M) : Completion M)).trans (AddMonoidHom.completion_coe q.toAddMonoidHom
      (IsModuleTopology.continuous_of_linearMap q) v).symm
  rw [Function.comp_apply, Function.comp_apply, Completion.piEquiv_coe, tensorOfPresentation_coe,
    ← Completion.coe_one, Completion.ofTensorProduct_coe_tmul, one_smul]

/-- The composite `Âⁿ → Â ⊗[A] M → M̂` is the completion of `q`, read through
`Completion (Fin n → A) ≃ Fin n → Â`. -/
private theorem ofTensorProduct_comp_tensorOfPresentation :
    Completion.ofTensorProduct A M ∘ tensorOfPresentation q =
      q.toAddMonoidHom.completion (IsModuleTopology.continuous_of_linearMap q) ∘
        (Completion.piEquiv fun _ ↦ A).symm := by
  rw [← ofTensorProduct_comp_tensorOfPresentation_comp_piEquiv]
  ext x
  simp

variable [IsHuberRing A] {q}

/-- For a surjective presentation `q`, the composite `Âⁿ → Â ⊗[A] M → M̂` is an open quotient
map: completion keeps the open surjection `q` an open surjection. -/
private theorem isOpenQuotientMap_ofTensorProduct_comp_tensorOfPresentation
    (hq : Function.Surjective q) :
    IsOpenQuotientMap (Completion.ofTensorProduct A M ∘ tensorOfPresentation q) := by
  have hqc : Continuous q := IsModuleTopology.continuous_of_linearMap q
  have hqo := (IsModuleTopology.isOpenQuotientMap_of_surjective hq).isOpenMap
  rw [ofTensorProduct_comp_tensorOfPresentation]
  exact ⟨(q.toAddMonoidHom.surjective_completion hqc hq hqo).comp
      (Completion.piEquiv _).symm.surjective,
    (AddMonoidHom.continuous_completion _ _).comp (Completion.piEquiv _).symm.continuous,
    (q.toAddMonoidHom.isOpenMap_completion hqc hqo).comp
      (Completion.piEquiv _).symm.toHomeomorph.isOpenMap⟩

/-- The kernel of `Âⁿ → M̂` lies in the closure of the image of `ker q`. -/
private theorem mem_closure_of_ofTensorProduct_tensorOfPresentation_eq_zero
    (hq : Function.Surjective q) {x : Fin n → Completion A}
    (hx : Completion.ofTensorProduct A M (tensorOfPresentation q x) = 0) :
    x ∈ closure ((fun (v : Fin n → A) i ↦ (v i : Completion A)) '' (LinearMap.ker q : Set _)) := by
  have hqc : Continuous q := IsModuleTopology.continuous_of_linearMap q
  have hqo := (IsModuleTopology.isOpenQuotientMap_of_surjective hq).isOpenMap
  set e := Completion.piEquiv fun _ : Fin n ↦ A
  have hz : e.symm x ∈ (q.toAddMonoidHom.completion hqc).ker := by
    rw [AddMonoidHom.mem_ker, ← Function.comp_apply (f := q.toAddMonoidHom.completion hqc),
      ← ofTensorProduct_comp_tensorOfPresentation]
    exact hx
  rw [q.toAddMonoidHom.ker_completion hqc hqo] at hz
  convert image_closure_subset_closure_image e.continuous ⟨_, hz, e.apply_symm_apply x⟩ using 2
  ext y
  simp [e]

/-- `Φ = tensorOfPresentation q` vanishes on the kernel of `Âⁿ → M̂`: that kernel lies in the
closure of the image `S` of `ker q`, hence in the `Â`-span of `S`, which is closed because the
ring of definition of `Â` is noetherian, and `Φ` kills `S`. -/
private theorem tensorOfPresentation_eq_zero (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] (hq : Function.Surjective q) {x : Fin n → Completion A}
    (hx : Completion.ofTensorProduct A M (tensorOfPresentation q x) = 0) :
    tensorOfPresentation q x = 0 := by
  have hN := closure_minimal Submodule.subset_span
    (P.completion.isClosed_of_isNoetherianRing _)
    (mem_closure_of_ofTensorProduct_tensorOfPresentation_eq_zero hq hx)
  refine LinearMap.mem_ker.mp (Submodule.span_le.mpr ?_ hN)
  rintro _ ⟨v, hv, rfl⟩
  simp_all [tensorOfPresentation_coe]

end Presentation

variable [Module.Finite A M] [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology A M]
  [UniformContinuousConstSMul A M]

/-- **Completion of a finite module is base change to the completed ring** (Huber, Lemma
2.3(iii)). If `A` is a Huber ring with a noetherian ring of definition and `M` is a finitely
generated `A`-module with its natural topology, the canonical map `Â ⊗[A] M → M̂` is bijective. -/
theorem ofTensorProduct_bijective (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] :
    Function.Bijective (Completion.ofTensorProduct A M) := by
  have : IsHuberRing A := ⟨⟨P⟩⟩
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A M
  refine ⟨(injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_,
    (isOpenQuotientMap_ofTensorProduct_comp_tensorOfPresentation hq).surjective.of_comp⟩
  obtain ⟨x, rfl⟩ := tensorOfPresentation_surjective q hq t
  exact tensorOfPresentation_eq_zero P hq ht

/-- **The comparison `Â ⊗[A] M → M̂` is a homeomorphism** for the natural `Â`-module topology on
`Â ⊗[A] M`, if `A` is a Huber ring with a noetherian ring of definition and `M` is a finitely
generated `A`-module with its natural topology (Huber, Lemma 2.3(iii)). -/
theorem isHomeomorph_ofTensorProduct (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] [TopologicalSpace (Completion A ⊗[A] M)]
    [IsModuleTopology (Completion A) (Completion A ⊗[A] M)] :
    IsHomeomorph (Completion.ofTensorProduct A M) := by
  have : IsHuberRing A := ⟨⟨P⟩⟩
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A M
  have hψ := isOpenQuotientMap_ofTensorProduct_comp_tensorOfPresentation hq
  -- `Φ : Âⁿ → Â ⊗[A] M` is an open quotient map for the natural topology, and so is `ψ = T ∘ Φ`.
  have hΦ := IsModuleTopology.isOpenQuotientMap_of_surjective (tensorOfPresentation_surjective q hq)
  refine ⟨hΦ.isQuotientMap.continuous_iff.mpr hψ.continuous, fun U hU ↦ ?_,
    P.ofTensorProduct_bijective⟩
  rw [← Set.image_preimage_eq U hΦ.surjective, Set.image_image]
  exact hψ.isOpenMap _ (hU.preimage hΦ.continuous)

/-- The `A`-linear equivalence `Â ⊗[A] M ≃ M̂` given by the canonical map, for a finitely
generated module `M` over a Huber ring with a noetherian ring of definition. -/
noncomputable def ofTensorProductEquiv (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] :
    Completion A ⊗[A] M ≃ₗ[A] Completion M :=
  LinearEquiv.ofBijective _ P.ofTensorProduct_bijective

/-- The equivalence `ofTensorProductEquiv` is the canonical map. -/
@[simp]
theorem ofTensorProductEquiv_apply (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] (t : Completion A ⊗[A] M) :
    P.ofTensorProductEquiv t = Completion.ofTensorProduct A M t :=
  (rfl)

/-- The inverse of `ofTensorProductEquiv` sends the image of `m : M` in `M̂` to `1 ⊗ m`. -/
@[simp]
theorem ofTensorProductEquiv_symm_coe (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] (m : M) :
    P.ofTensorProductEquiv.symm (m : Completion M) = 1 ⊗ₜ m := by
  rw [LinearEquiv.symm_apply_eq, ofTensorProductEquiv_apply, ← Completion.coe_one,
    Completion.ofTensorProduct_coe_tmul, one_smul]

end TauCeti.Huber.PairOfDefinition
