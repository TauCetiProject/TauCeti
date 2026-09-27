/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# The universal property of the topological abelianization

The topological abelianization `G ⧸ closure [G, G]` of a topological group `G` is the universal
continuous homomorphism from `G` to a commutative `T1` topological group: such a homomorphism
kills every commutator, so its closed kernel contains the closure of the commutator subgroup, and
it factors uniquely through the quotient. This is the topological counterpart of
`Abelianization.lift`; it is what identifies the abelianization of a concrete profinite group with
an abelian profinite group given by its universal property.

## Main definitions

* `TopologicalAbelianization.lift`: the continuous homomorphism
  `TopologicalAbelianization G →ₜ* A` induced by a continuous homomorphism `G →ₜ* A` into a
  commutative `T1` group.

## Main results

* `TopologicalAbelianization.topologicalClosure_commutator_le_ker`: the closure of the
  commutator subgroup lies in the kernel of every continuous homomorphism to a commutative `T1`
  group.
* `TopologicalAbelianization.lift_mk`, `TopologicalAbelianization.lift_unique`:
  the factorisation and its uniqueness.
* `TopologicalAbelianization.hom_ext`: a continuous homomorphism out of the topological
  abelianization is determined by its values on the classes of elements of `G`.
-/

public section

open TauCeti

namespace TopologicalAbelianization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Lift

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A]

/-- The closure of the commutator subgroup lies in the kernel of every continuous homomorphism to
a commutative `T1` group: the kernel is closed and contains all commutators. -/
theorem topologicalClosure_commutator_le_ker (f : G →ₜ* A) :
    (commutator G).topologicalClosure ≤ (f : G →* A).ker :=
  (commutator G).topologicalClosure_minimal (Abelianization.commutator_subset_ker _)
    (isClosed_singleton.preimage f.continuous)

/-- **The universal property of the topological abelianization.** A continuous homomorphism from
`G` to a commutative `T1` group factors through `TopologicalAbelianization G`. -/
noncomputable def lift (f : G →ₜ* A) : TopologicalAbelianization G →ₜ* A :=
  ContinuousMonoidHom.quotientLift _ f (topologicalClosure_commutator_le_ker f)

/-- The lift of `f` evaluates as `f` on the class of an element. -/
@[simp]
theorem lift_mk (f : G →ₜ* A) (x : G) : lift f (x : TopologicalAbelianization G) = f x :=
  ContinuousMonoidHom.quotientLift_mk _ f _ x

/-- The lift of `f` composed with the projection is `f`. -/
@[simp]
theorem lift_comp_quotientMk (f : G →ₜ* A) :
    (lift f).comp (ContinuousMonoidHom.quotientMk (commutator G).topologicalClosure) = f :=
  ContinuousMonoidHom.quotientLift_comp_quotientMk _ f _

/-- A continuous homomorphism out of the topological abelianization that agrees with `f` on
classes is the lift of `f`. -/
theorem lift_unique (f : G →ₜ* A) (g : TopologicalAbelianization G →ₜ* A)
    (hg : ∀ x : G, g (x : TopologicalAbelianization G) = f x) : g = lift f :=
  ContinuousMonoidHom.quotientLift_unique _ f _ g hg

end Lift

/-- Two continuous homomorphisms out of the topological abelianization that agree on the classes
of elements of `G` are equal. -/
@[ext]
theorem hom_ext {B : Type*} [Monoid B] [TopologicalSpace B]
    {g g' : TopologicalAbelianization G →ₜ* B}
    (h : ∀ x : G, g (x : TopologicalAbelianization G) = g' x) : g = g' :=
  ContinuousMonoidHom.ext fun q ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact h x

end TopologicalAbelianization
