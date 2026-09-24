/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# Finite embedding problems

A **finite embedding problem** for a topological group `G` is a continuous surjection
`π : G ↠ Q` onto a finite group together with a surjection `α : E ↠ Q` of finite groups. A
**solution** is a continuous homomorphism `β : G → E` with `α ∘ β = π`. For homomorphisms into
finite discrete groups, continuity is recorded as openness of the kernel. This equivalence uses
the topological group structure on `G`.

A solution need not be surjective. For example, if `G` is cyclic of order `p`, `Q = 1`, and
`E = G × G`, no homomorphism `G → E` is surjective.

## Main definitions

* `TauCeti.FiniteEmbeddingProblem`: a finite embedding problem for `G`.
* `TauCeti.FiniteEmbeddingProblem.IsSolution`: a solution of a finite embedding problem.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.4 and §4.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter III, §5.
-/

public section

namespace TauCeti

universe u v w

/-- A **finite embedding problem** for a topological group `G`: a continuous surjection
`π : G ↠ Q` onto a finite group, together with a surjection `α : E ↠ Q` of finite groups.
Continuity of `π` is recorded as openness of its kernel, which is what continuity into a finite
discrete group amounts to. -/
structure FiniteEmbeddingProblem (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  /-- The finite quotient of `G` the problem sits over. -/
  Q : Type v
  [groupQ : Group Q]
  [finiteQ : Finite Q]
  /-- The finite group into which a solution maps. -/
  E : Type w
  [groupE : Group E]
  [finiteE : Finite E]
  /-- The continuous surjection `G ↠ Q`. -/
  π : G →* Q
  /-- Continuity of `π`, as openness of its kernel. -/
  isOpen_ker_π : IsOpen (π.ker : Set G)
  /-- Surjectivity of `π`. -/
  π_surjective : Function.Surjective π
  /-- The surjection of finite groups `E ↠ Q`. -/
  α : E →* Q
  /-- Surjectivity of `α`. -/
  α_surjective : Function.Surjective α

attribute [instance] FiniteEmbeddingProblem.groupQ FiniteEmbeddingProblem.finiteQ
  FiniteEmbeddingProblem.groupE FiniteEmbeddingProblem.finiteE

namespace FiniteEmbeddingProblem

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : FiniteEmbeddingProblem G)

/-- A **solution** of a finite embedding problem `P`: a homomorphism `β : G → E` with open kernel
(that is, continuous for the discrete topology on `E`) such that `α ∘ β = π`. A solution need not
be surjective. -/
def IsSolution (β : G →* P.E) : Prop :=
  IsOpen (β.ker : Set G) ∧ ∀ g : G, P.α (β g) = P.π g

variable {P}

/-- A homomorphism solves `P` exactly when its kernel is open and `α ∘ β = π`. -/
@[simp] theorem isSolution_iff {β : G →* P.E} :
    P.IsSolution β ↔ IsOpen (β.ker : Set G) ∧ P.α.comp β = P.π :=
  and_congr_right' <| by simp [MonoidHom.ext_iff]

/-- A solution of a finite embedding problem has open kernel. -/
theorem IsSolution.isOpen_ker {β : G →* P.E} (hβ : P.IsSolution β) : IsOpen (β.ker : Set G) :=
  hβ.1

/-- A solution of a finite embedding problem lifts `π` through `α`. -/
@[simp] theorem IsSolution.comp_eq {β : G →* P.E} (hβ : P.IsSolution β) : P.α.comp β = P.π :=
  (isSolution_iff.mp hβ).2

end FiniteEmbeddingProblem

end TauCeti
