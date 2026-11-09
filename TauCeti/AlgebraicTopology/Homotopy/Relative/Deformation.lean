/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Relative homotopy sets of weakly equivalent pairs

If the inclusion `A ↪ X` of the subspace of a based pair `(X, A, a₀)` is a weak homotopy
equivalence, then every relative homotopy set `π_{n+1}(X, A, a₀)` is trivial
(`TauCeti.RelHomotopyGroup.subsingleton_of_isWeakHomotopyEquivalence`): the inclusion is bijective
on all homotopy groups, and the exact homotopy sequence of the pair
(`TauCeti.RelHomotopyGroup.subsingleton_of_injective_of_surjective`) concludes.

The inclusion is a homotopy equivalence in particular when `X` deforms into `A` in the weak sense:
by a homotopy that starts at the identity, ends inside `A`, and keeps `A` inside `A` at all times,
but need not fix `A` (`ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction`). This gives
`TauCeti.RelHomotopyGroup.subsingleton_ofSubset_of_deformation`. Straight-line deformations of a
convex set into a star-convex subset, which slide the points of the subset within it, are of this
kind.

## Main results

* `TauCeti.RelHomotopyGroup.subsingleton_of_isWeakHomotopyEquivalence`: `π_{n+1}(X, A, a₀)` is
  trivial when the inclusion `A ↪ X` is a weak homotopy equivalence.
* `TauCeti.RelHomotopyGroup.subsingleton_ofSubset_of_deformation`: `π_{n+1}(X, A, a)` is trivial
  when `X` deforms into `A` in the weak sense.
-/

public section

open scoped unitInterval Topology.Homotopy

universe u v

namespace TauCeti

namespace RelHomotopyGroup

variable {N : Type v} [Finite N]

/-- **Relative homotopy sets of a weakly equivalent pair are trivial.** If the inclusion of the
subspace of a based pair `(X, A, a₀)` is a weak homotopy equivalence, then `π_{n+1}(X, A, a₀)` is
trivial, where `n` is the cardinality of `N`. -/
theorem subsingleton_of_isWeakHomotopyEquivalence {X : BasedTopPair.{u}}
    (h : X.pair.map.hom.IsWeakHomotopyEquivalence) : Subsingleton (RelHomotopyGroup N X) :=
  subsingleton_of_injective_of_surjective (h.map_bijective N X.basepoint).injective
    (h.map_bijective (Option N) X.basepoint).surjective

/-- **A weak deformation into the subspace trivializes the relative homotopy sets.** Let `A` be a
subset of a space `X`, and let `H : I × X → X` be a homotopy that starts at the identity, ends
inside `A`, and keeps `A` inside `A` at all times. Then `π_{n+1}(X, A, a)` is trivial for every
`a ∈ A`, where `n` is the cardinality of `N`. -/
theorem subsingleton_ofSubset_of_deformation {X : TopCat.{u}} {A : Set X} (H : C(I × X, X))
    (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A) (hA : ∀ t, ∀ x ∈ A, H (t, x) ∈ A)
    (a : A) : Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset A, a⟩) := by
  let e := (ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction (Set.subset_univ A)
      (fun p ↦ H (p.1, p.2)) (by fun_prop) (fun _ ↦ Set.mem_univ _) (fun x ↦ h₀ x)
      (fun x ↦ h₁ x) fun t x hx ↦ hA t x hx).trans (Homeomorph.Set.univ X).toHomotopyEquiv
  have he : e.toFun = (TopPair.ofSubset A).map.hom := ContinuousMap.ext fun x ↦
    ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply _ _ _ _ _ _ _ x
  exact subsingleton_of_isWeakHomotopyEquivalence (he ▸ e.isWeakHomotopyEquivalence)

end RelHomotopyGroup

end TauCeti
