/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.GroupTheory.Coset.Card
import TauCeti.GroupTheory.PGroup

/-!
# Finite embedding problems

A **finite embedding problem** for a topological group `G` is a continuous surjection
`π : G ↠ Q` onto a finite group together with a surjection `α : E ↠ Q` of finite groups; a
**solution** is a continuous homomorphism `β : G → E` with `α ∘ β = π`. Continuity of a
homomorphism into a finite discrete group is openness of its kernel, and that is how it is
written here, so no field of the problem carries a topology. A solution is not required to be
surjective, and in general none is: for `G` cyclic of order `p`, `Q = 1` and `E = G × G`, no
homomorphism `G → E` is surjective.

Solvability of the embedding problems whose kernel `ker α` is a `p`-group is the finite-level form
of the lifting property that defines projective pro-`p` groups. The cohomological input, vanishing
of `H²`, only controls the problems whose kernel is elementary abelian. This file proves that
this special case already gives all of them:
`TauCeti.hasPGroupSolutions_of_hasElementaryAbelianSolutions`.

The proof is an induction on `Nat.card E`. A nontrivial `p`-group kernel `N` contains a nontrivial
subgroup `A`, normal in `E`, which centralizes `N` and has exponent dividing `p`
(`IsPGroup.exists_normal_ne_bot_le_inf_centralizer`). The problem is first solved for the
smaller group `E ⧸ A`, and the resulting solution is then lifted along `E ↠ E ⧸ A`, whose kernel
`A` is elementary abelian. The solution for `E ⧸ A` need not be surjective, so the second step is
an embedding problem over its image; this is why the lifting statements below,
`HasElementaryAbelianSolutions.exists_lift` and
`HasElementaryAbelianSolutions.exists_lift_of_isPGroup`, are stated for an arbitrary continuous
homomorphism `γ : G → F`, not only for surjective ones.

## Main definitions

* `TauCeti.FiniteEmbeddingProblem`: a finite embedding problem for `G`.
* `TauCeti.FiniteEmbeddingProblem.IsSolution`: a solution of a finite embedding problem.
* `TauCeti.HasElementaryAbelianSolutions p G`: every finite embedding problem for `G` whose kernel
  is an elementary abelian `p`-group has a solution.
* `TauCeti.HasPGroupSolutions p G`: every finite embedding problem for `G` whose kernel is a
  `p`-group has a solution.

## Main results

* `TauCeti.HasElementaryAbelianSolutions.exists_lift_of_isPGroup`: under
  `HasElementaryAbelianSolutions p G`, every continuous homomorphism `G → F` lifts along every
  surjection `E ↠ F` from a finite group whose kernel is a `p`-group.
* `TauCeti.hasPGroupSolutions_iff_hasElementaryAbelianSolutions`: the two solvability conditions
  agree.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.4 and §4.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter III, §5.
-/

public section

namespace TauCeti

universe u

/-- A **finite embedding problem** for a topological group `G`: a continuous surjection
`π : G ↠ Q` onto a finite group, together with a surjection `α : E ↠ Q` of finite groups.
Continuity of `π` is recorded as openness of its kernel, which is what continuity into a finite
discrete group amounts to. -/
structure FiniteEmbeddingProblem (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  /-- The finite quotient of `G` the problem sits over. -/
  Q : Type u
  [groupQ : Group Q]
  [finiteQ : Finite Q]
  /-- The finite group into which a solution maps. -/
  E : Type u
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
theorem isSolution_iff {β : G →* P.E} :
    P.IsSolution β ↔ IsOpen (β.ker : Set G) ∧ P.α.comp β = P.π :=
  and_congr_right' <| by simp [MonoidHom.ext_iff]

/-- A solution of a finite embedding problem has open kernel. -/
theorem IsSolution.isOpen_ker {β : G →* P.E} (hβ : P.IsSolution β) : IsOpen (β.ker : Set G) :=
  hβ.1

/-- A solution of a finite embedding problem lifts `π` through `α`. -/
theorem IsSolution.comp_eq {β : G →* P.E} (hβ : P.IsSolution β) : P.α.comp β = P.π :=
  (isSolution_iff.mp hβ).2

end FiniteEmbeddingProblem

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `HasElementaryAbelianSolutions p G`: every finite embedding problem for `G` whose kernel
`ker α` is an elementary abelian `p`-group (commutative, with every element killed by `p`) has a
solution. This is the solvability condition that the vanishing of `H²(G, M)` on elementary
abelian `p`-primary coefficients provides. -/
def HasElementaryAbelianSolutions : Prop :=
  ∀ P : FiniteEmbeddingProblem G, (∀ x ∈ P.α.ker, x ^ p = 1) →
    (∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, Commute x y) → ∃ β : G →* P.E, P.IsSolution β

/-- `HasPGroupSolutions p G`: every finite embedding problem for `G` whose kernel `ker α` is a
`p`-group has a solution. -/
def HasPGroupSolutions : Prop :=
  ∀ P : FiniteEmbeddingProblem G, IsPGroup p P.α.ker → ∃ β : G →* P.E, P.IsSolution β

variable {p G}

/-- Unfolding of `HasElementaryAbelianSolutions`. -/
theorem hasElementaryAbelianSolutions_iff : HasElementaryAbelianSolutions p G ↔
    ∀ P : FiniteEmbeddingProblem G, (∀ x ∈ P.α.ker, x ^ p = 1) →
      (∀ x ∈ P.α.ker, ∀ y ∈ P.α.ker, Commute x y) → ∃ β : G →* P.E, P.IsSolution β :=
  Iff.rfl

/-- Unfolding of `HasPGroupSolutions`. -/
theorem hasPGroupSolutions_iff : HasPGroupSolutions p G ↔
    ∀ P : FiniteEmbeddingProblem G, IsPGroup p P.α.ker → ∃ β : G →* P.E, P.IsSolution β :=
  Iff.rfl

/-- A kernel of exponent dividing `p` is a `p`-group, so solvability of all embedding problems
with `p`-group kernel includes the elementary abelian ones. -/
theorem HasPGroupSolutions.hasElementaryAbelianSolutions (h : HasPGroupSolutions p G) :
    HasElementaryAbelianSolutions p G :=
  fun P hpow _ ↦ h P fun x ↦ ⟨1, Subtype.ext <| by simpa using hpow x x.2⟩

namespace HasElementaryAbelianSolutions

/-- **Lifting along an elementary abelian kernel.** Under `HasElementaryAbelianSolutions p G`, a
homomorphism `γ : G → F` with open kernel lifts along every surjection `φ : E ↠ F` from a finite
group whose kernel is commutative of exponent dividing `p`. The homomorphism `γ` need not be
surjective. -/
theorem exists_lift (h : HasElementaryAbelianSolutions p G) {E F : Type u} [Group E] [Finite E]
    [Group F] {φ : E →* F} (hφ : Function.Surjective φ) (hpow : ∀ x ∈ φ.ker, x ^ p = 1)
    (hcomm : ∀ x ∈ φ.ker, ∀ y ∈ φ.ker, Commute x y) {γ : G →* F}
    (hγ : IsOpen (γ.ker : Set G)) :
    ∃ β : G →* E, IsOpen (β.ker : Set G) ∧ φ.comp β = γ := by
  have : Finite F := Finite.of_surjective φ hφ
  -- The embedding problem over the image of `γ`, with `E` replaced by the preimage of that image.
  let P : FiniteEmbeddingProblem G :=
    { Q := γ.range
      E := γ.range.comap φ
      π := γ.rangeRestrict
      isOpen_ker_π := by rwa [MonoidHom.ker_rangeRestrict]
      π_surjective := γ.rangeRestrict_surjective
      α := φ.subgroupComap γ.range
      α_surjective := φ.subgroupComap_surjective_of_surjective γ.range hφ }
  -- An element of `ker (P.α)` is an element of `ker φ`.
  have hker (x : P.E) (hx : x ∈ P.α.ker) : (x : E) ∈ φ.ker :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  obtain ⟨β, hβ⟩ := h P
    (fun x hx ↦ Subtype.ext <| (SubmonoidClass.coe_pow x p).trans (hpow _ (hker x hx)))
    (fun x hx y hy ↦ Subtype.ext <| hcomm x (hker x hx) y (hker y hy))
  refine ⟨(γ.range.comap φ).subtype.comp β, ?_, MonoidHom.ext fun g ↦ ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ Subtype.val_injective]
    exact hβ.isOpen_ker
  · exact congrArg Subtype.val (hβ.2 g)

/-- **Lifting along a `p`-group kernel.** Under `HasElementaryAbelianSolutions p G`, a
homomorphism `γ : G → F` with open kernel lifts along every surjection `φ : E ↠ F` from a finite
group whose kernel is a `p`-group. The homomorphism `γ` need not be surjective. -/
theorem exists_lift_of_isPGroup [Fact p.Prime] (h : HasElementaryAbelianSolutions p G)
    {E F : Type u} [Group E] [Finite E] [Group F] {φ : E →* F} (hφ : Function.Surjective φ)
    (hker : IsPGroup p φ.ker) {γ : G →* F} (hγ : IsOpen (γ.ker : Set G)) :
    ∃ β : G →* E, IsOpen (β.ker : Set G) ∧ φ.comp β = γ := by
  -- Induction on `Nat.card E`: the kernel contains a nontrivial subgroup `A`, normal in `E`, which
  -- centralizes the kernel and has exponent dividing `p`. Lift first along the induced surjection
  -- `E ⧸ A ↠ F`, then along `E ↠ E ⧸ A` by `exists_lift`.
  induction hn : Nat.card E using Nat.strong_induction_on generalizing E with
  | _ n ih =>
  by_cases hbot : φ.ker = ⊥
  · exact h.exists_lift hφ (by simp [hbot]) (by simp [hbot]) hγ
  obtain ⟨A, hAn, hA, hAle, hApow⟩ := hker.exists_normal_ne_bot_le_inf_centralizer hbot
  have hAker : A ≤ φ.ker := hAle.trans inf_le_left
  -- Solve over `E ⧸ A`, which is smaller than `E` because `A` is nontrivial.
  have hcard : Nat.card (E ⧸ A) < n := by
    have : 1 < Nat.card A := Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot A).mpr hA)
    rw [← hn, A.card_eq_card_quotient_mul_card_subgroup]
    exact lt_mul_of_one_lt_right Nat.card_pos this
  have hkerA : IsPGroup p (QuotientGroup.lift A φ hAker).ker := by
    rw [QuotientGroup.ker_lift]
    exact hker.map _
  obtain ⟨β₀, hβ₀, hβ₀φ⟩ := ih _ hcard (QuotientGroup.lift_surjective_of_surjective _ _ hφ hAker)
    hkerA rfl
  -- Lift along `E ↠ E ⧸ A`, whose kernel `A` is elementary abelian.
  obtain ⟨β, hβ, hββ₀⟩ := h.exists_lift (QuotientGroup.mk'_surjective A)
    (fun x hx ↦ hApow x <| (QuotientGroup.ker_mk' A).le hx)
    (fun x hx y hy ↦ by
      rw [QuotientGroup.ker_mk'] at hx hy
      exact (Subgroup.mem_centralizer_iff.mp (hAle hx).2 y (hAle hy).1).symm) hβ₀
  refine ⟨β, hβ, ?_⟩
  rw [← hβ₀φ, ← hββ₀, ← MonoidHom.comp_assoc, QuotientGroup.lift_comp_mk']

end HasElementaryAbelianSolutions

/-- **Solvability with `p`-group kernel from solvability with elementary abelian kernel.** If
every finite embedding problem for `G` with elementary abelian `p`-group kernel has a solution,
then so does every finite embedding problem for `G` with `p`-group kernel. -/
theorem hasPGroupSolutions_of_hasElementaryAbelianSolutions [Fact p.Prime]
    (h : HasElementaryAbelianSolutions p G) : HasPGroupSolutions p G := fun P hP ↦ by
  obtain ⟨β, hβ, hβα⟩ := h.exists_lift_of_isPGroup P.α_surjective hP P.isOpen_ker_π
  exact ⟨β, FiniteEmbeddingProblem.isSolution_iff.mpr ⟨hβ, hβα⟩⟩

/-- Solvability of the finite embedding problems with `p`-group kernel is equivalent to
solvability of those with elementary abelian `p`-group kernel. -/
theorem hasPGroupSolutions_iff_hasElementaryAbelianSolutions [Fact p.Prime] :
    HasPGroupSolutions p G ↔ HasElementaryAbelianSolutions p G :=
  ⟨HasPGroupSolutions.hasElementaryAbelianSolutions,
    hasPGroupSolutions_of_hasElementaryAbelianSolutions⟩

end TauCeti
