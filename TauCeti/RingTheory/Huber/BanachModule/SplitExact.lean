/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor

/-!
# Split exactness of completed module tensor products

Completed tensor products preserve finite products and topologically split short exact
sequences. No completeness, separation or lattice assumptions on the factors are needed:
the assertions follow from the completed tensor product's continuous bilinear universal
property. The splitting maps must be continuous; algebraic splittings alone do not suffice.

`TauCeti.Huber.BanachModule.CompletedTensor.prodLeft` identifies
`(U × Q) ⊗̂ W` with `(U ⊗̂ W) × (Q ⊗̂ W)`.
`TauCeti.Huber.BanachModule.CompletedTensor.exact_of_split` proves middle exactness from a
continuous splitting identity. Retractions and sections remain retractions and sections by
`map_comp` and `map_id`, so a topologically split short exact sequence remains such after
completed tensoring.

For Banach modules this is the split case of the tensor exactness discussed in Kedlaya–Liu,
*Relative p-adic Hodge theory: Foundations*, §2.2, Lemma 2.2.9. Here the tensor product is
formed with the tensor topology, without choosing norms.
-/

public section

open Function

namespace TauCeti.Huber.BanachModule.CompletedTensor

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {U : Type*} [AddCommGroup U] [Module A U] [TopologicalSpace U]
  {V : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
  {Q : Type*} [AddCommGroup Q] [Module A Q] [TopologicalSpace Q]
  {W : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]

section Product

/-- Completed tensoring in the first variable preserves binary products. -/
noncomputable def prodLeft :
    CompletedTensor A (U × Q) W ≃L[A]
      CompletedTensor A U W × CompletedTensor A Q W :=
  ContinuousLinearEquiv.equivOfInverse'
    ((map (ContinuousLinearMap.fst A U Q) (.id A W)).prod
      (map (ContinuousLinearMap.snd A U Q) (.id A W)))
    ((map (ContinuousLinearMap.inl A U Q) (.id A W)).coprod
      (map (ContinuousLinearMap.inr A U Q) (.id A W)))
    (by ext v w <;> simp)
    (by
      apply ext
      intro v w
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coprod_apply, map_tmul, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      rw [← LinearMap.add_apply, ← map_add]
      simp)

/-- The product comparison sends an elementary tensor to its two component tensors. -/
@[simp]
theorem prodLeft_tmul (v : U × Q) (w : W) :
    prodLeft (tmul A (U × Q) W v w) = (tmul A U W v.1 w, tmul A Q W v.2 w) := by
  simp [prodLeft]

/-- The inverse product comparison is the sum of the two completed tensor inclusions. -/
@[simp]
theorem prodLeft_symm_apply (x : CompletedTensor A U W) (y : CompletedTensor A Q W) :
    prodLeft.symm (x, y) =
      map (ContinuousLinearMap.inl A U Q) (.id A W) x +
        map (ContinuousLinearMap.inr A U Q) (.id A W) y := by
  rfl

end Product

/-- Completed tensoring preserves the exactness of a continuously split pair.

The equation `i ∘ r + s ∘ p = id` supplies a preimage of every element of the kernel,
including elements only present after completion. If `r ∘ i = id` and `p ∘ s = id` as well,
`map_comp` and `map_id` preserve these equations, giving a topologically split short exact
sequence, not just middle exactness. -/
theorem exact_of_split
    {i : U →L[A] V} {p : V →L[A] Q} (r : V →L[A] U) (s : Q →L[A] V)
    (hpi : p.comp i = 0) (hsplit : ∀ v, i (r v) + s (p v) = v) :
    Exact (map i (.id A W)) (map p (.id A W)) := by
  have hzero : (map p (.id A W)).comp (map i (.id A W)) = 0 := by
    apply ext
    intro u w
    have h := DFunLike.congr_fun hpi u
    simpa using congrArg (fun q ↦ tmul A Q W q w) h
  have hdecomp :
      (map i (.id A W)).comp (map r (.id A W)) +
        (map s (.id A W)).comp (map p (.id A W)) =
          ContinuousLinearMap.id A (CompletedTensor A V W) := by
    apply ext
    intro v w
    simpa [← map_add, ← LinearMap.add_apply] using
      congrArg (fun v ↦ tmul A V W v w) (hsplit v)
  refine Exact.of_comp_of_mem_range (congrArg DFunLike.coe hzero) ?_
  intro x hx
  refine ⟨map r (.id A W) x, ?_⟩
  simpa [hx] using DFunLike.congr_fun hdecomp x

end TauCeti.Huber.BanachModule.CompletedTensor
