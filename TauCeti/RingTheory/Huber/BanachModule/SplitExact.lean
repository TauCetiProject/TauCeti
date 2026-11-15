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

Completed tensor products preserve topologically split short exact sequences.
No completeness, separation or lattice assumptions on the factors are needed:
the assertions follow from the completed tensor product's continuous bilinear universal
property. The splitting maps must be continuous; algebraic splittings alone do not suffice.

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
