/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Internal

/-!
# Refining an internal direct sum by decompositions of its summands

If a module `M` is identified with an external direct sum `⨁ i, N i`, and each summand `N i` is
in turn the internal direct sum of a family of submodules `B i j`, then `M` is the internal direct
sum of the images of all the `B i j`, indexed by the pairs `⟨i, j⟩` of the sigma type. This is the
step that iterates a decomposition, as in building a basis adapted to a chain of subgroups one
link at a time.

## Main results

* `LinearEquiv.isInternal_sigma_map`: the images of the `B i j` form an internal direct sum.
-/

public section

open scoped DirectSum

/-- **Refining a decomposition by decompositions of its summands.** If `E` identifies the
external direct sum `⨁ i, N i` with `M`, and each `N i` is the internal direct sum of a family
`B i`, then `M` is the internal direct sum of the images of all the `B i j` in `M`, indexed by the
pairs `⟨i, j⟩`. -/
theorem LinearEquiv.isInternal_sigma_map {R ι M : Type*} [Semiring R] [DecidableEq ι]
    [AddCommMonoid M] [Module R M] {N : ι → Type*} [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (N i)] {κ : ι → Type*} [∀ i, DecidableEq (κ i)]
    (E : (⨁ i, N i) ≃ₗ[R] M) {B : ∀ i, κ i → Submodule R (N i)}
    (hB : ∀ i, DirectSum.IsInternal (B i)) :
    DirectSum.IsInternal fun x : Σ i, κ i ↦
      (B x.1 x.2).map (E.toLinearMap ∘ₗ DirectSum.lof R ι N x.1) := by
  refine TauCeti.DirectSum.isInternal_of_lof (N := fun x : Σ i, κ i ↦ B x.1 x.2)
    (fun x ↦ Submodule.equivMapOfInjective (E.toLinearMap ∘ₗ DirectSum.lof R ι N x.1)
      (E.injective.comp (DirectSum.of_injective x.1)) _)
    ((DirectSum.sigmaLcurryEquiv R).trans ((DirectSum.congrLinearEquiv fun i ↦
      LinearEquiv.ofBijective (DirectSum.coeLinearMap (B i)) (hB i)).trans E)) fun x y ↦ ?_
  rw [Submodule.coe_equivMapOfInjective_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  have h : DirectSum.sigmaLcurryEquiv R (δ := fun i j ↦ B i j)
        (DirectSum.lof R (Σ i, κ i) (fun x ↦ B x.1 x.2) x y) =
      DirectSum.lof R ι _ x.1 (DirectSum.lof R (κ x.1) (fun j ↦ B x.1 j) x.2 y) :=
    DirectSum.sigmaCurry_of (δ := fun i j ↦ B i j) x y
  rw [h, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  exact congrArg (fun z ↦ E (DirectSum.lof R ι N x.1 z))
    (DirectSum.coeLinearMap_lof (B x.1) x.2 y)
