/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PLowerCentralSeries
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.ElementaryAbelian

/-!
# Finite embedding problems with `p`-group kernel

Two solvability predicates for the finite embedding problems of a topological group `G`, and the
reduction of one to the other.

* `TauCeti.HasElementaryAbelianSolutions p G`: every finite embedding problem for `G` whose kernel
  `ker α` is commutative and killed by `p` (elementary abelian, when `p` is prime) has a solution.
* `TauCeti.HasPGroupSolutions p G`: every finite embedding problem for `G` whose kernel is a
  `p`-group has a solution.

The second predicate implies the first, since a group killed by `p` is a `p`-group. The main
theorem, `TauCeti.HasElementaryAbelianSolutions.hasPGroupSolutions`, is the converse for a prime
`p`. A `p`-group kernel `N = ker α` is filtered by its lower `p`-central series `λ_k(N)`, whose
terms are normal in `E` and whose successive factors `λ_k(N) ⧸ λ_{k+1}(N)` are elementary abelian.
A solution is built one layer at a time: a solution modulo `λ_k(N)`, that is a homomorphism
`β_k : G → E ⧸ λ_k(N)` with open kernel lying over `π`, is lifted through the surjection
`E ⧸ λ_{k+1}(N) ↠ E ⧸ λ_k(N)`, whose kernel is elementary abelian, by solving the finite embedding
problem `TauCeti.FiniteEmbeddingProblem.ofSurjective` cut out by that surjection and `β_k`
(`TauCeti.HasElementaryAbelianSolutions.exists_comp_eq`). Since the series reaches `⊥`, the last
stage is a solution of the original problem.

The two predicates quantify over the finite embedding problems whose groups live in the universe
of `G`. Every finite group is isomorphic to one in any universe, so this is no restriction on the
finite groups that occur, and it keeps the predicates free of universe parameters that nothing
else would determine. Only the elementary abelian case consumes cohomology: the extension
`1 → ker α → E → Q → 1` has a class in `H²(Q, ker α)`, and its pullback along `π` to `H²(G, ker α)`
is the obstruction to solving the problem, so the vanishing of `H²(G, M)` for the finite discrete
`G`-modules `M` killed by `p` gives `HasElementaryAbelianSolutions p G`, and the theorem here
extends it to `p`-group kernels.

## Main definitions

* `TauCeti.HasElementaryAbelianSolutions`: every finite embedding problem with commutative kernel
  killed by `p` has a solution.
* `TauCeti.HasPGroupSolutions`: every finite embedding problem with `p`-group kernel has a
  solution.

## Main results

* `TauCeti.HasPGroupSolutions.hasElementaryAbelianSolutions`: solvability with `p`-group kernel
  gives solvability with commutative kernel killed by `p`.
* `TauCeti.HasElementaryAbelianSolutions.exists_comp_eq`: under
  `HasElementaryAbelianSolutions p G`, a homomorphism `β : G → F` with open kernel lifts through a
  surjection `φ : E ↠ F` of finite groups whose kernel is commutative and killed by `p`.
* `TauCeti.HasElementaryAbelianSolutions.hasPGroupSolutions`: for a prime `p`, solvability with
  elementary abelian kernel gives solvability with `p`-group kernel.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.4, Proposition 16 and its proof.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter III, §5.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 7.6.
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Solvability with `p`-group kernel.** Every finite embedding problem for `G`, with groups in
the universe of `G`, whose kernel `ker α` is a `p`-group has a solution. -/
def HasPGroupSolutions : Prop :=
  ∀ P : FiniteEmbeddingProblem.{u, u, u} G, IsPGroup p P.α.ker → ∃ β : G →* P.E, P.IsSolution β

variable {p G}

/-- The defining property of `HasPGroupSolutions`, as a lemma usable outside this module. -/
theorem hasPGroupSolutions_iff :
    HasPGroupSolutions p G ↔
      ∀ P : FiniteEmbeddingProblem.{u, u, u} G, IsPGroup p P.α.ker →
        ∃ β : G →* P.E, P.IsSolution β :=
  Iff.rfl

/-- Solvability with `p`-group kernel gives solvability with commutative kernel killed by `p`:
such a kernel is a `p`-group. -/
theorem HasPGroupSolutions.hasElementaryAbelianSolutions (h : HasPGroupSolutions p G) :
    HasElementaryAbelianSolutions p G := hasElementaryAbelianSolutions_iff.mpr fun P hpow _ ↦
  h P fun x ↦ ⟨1, Subtype.ext <| by simpa using hpow x x.2⟩

/-- **Lifting through a commutative kernel killed by `p`.** If every finite embedding problem for
`G` with commutative kernel killed by `p` has a solution, then a homomorphism `β : G → F` with open
kernel lifts, with open kernel, through every surjection `φ : E ↠ F` of finite groups whose kernel
is commutative and killed by `p`. -/
theorem HasElementaryAbelianSolutions.exists_comp_eq (h : HasElementaryAbelianSolutions p G)
    {E F : Type u} [Group E] [Finite E] [Group F] (φ : E →* F) (hφ : Function.Surjective φ)
    (hpow : ∀ x ∈ φ.ker, x ^ p = 1) (hcomm : ∀ x ∈ φ.ker, ∀ y ∈ φ.ker, x * y = y * x)
    (β : G →* F) (hβ : IsOpen (β.ker : Set G)) :
    ∃ β' : G →* E, IsOpen (β'.ker : Set G) ∧ φ.comp β' = β := by
  have hpow' : ∀ x ∈ (FiniteEmbeddingProblem.ofSurjective φ hφ β hβ).α.ker, x ^ p = 1 := by
    intro x hx
    rw [FiniteEmbeddingProblem.ker_ofSurjective_α, mem_subgroupOf] at hx
    exact Subtype.ext <| by simpa using hpow x hx
  have hcomm' : ∀ x ∈ (FiniteEmbeddingProblem.ofSurjective φ hφ β hβ).α.ker,
      ∀ y ∈ (FiniteEmbeddingProblem.ofSurjective φ hφ β hβ).α.ker, x * y = y * x := by
    intro x hx y hy
    rw [FiniteEmbeddingProblem.ker_ofSurjective_α, mem_subgroupOf] at hx hy
    exact Subtype.ext <| by simpa using hcomm x hx y hy
  obtain ⟨β', hβ'⟩ := hasElementaryAbelianSolutions_iff.mp h _ hpow' hcomm'
  exact ⟨_, hβ'.isOpen_ker_subtype_comp, hβ'.comp_subtype_comp⟩

/-- Under `HasElementaryAbelianSolutions p G`, every finite embedding problem `P` has, for every
`k`, a solution modulo the `k`-th term `λ_k` of the lower `p`-central series of its kernel: there is
a homomorphism `β : G → E ⧸ λ_k` with open kernel whose composite with the map `E ⧸ λ_k → Q` induced
by `α` is `π`. This is the engine of `TauCeti.HasElementaryAbelianSolutions.hasPGroupSolutions`. -/
private theorem HasElementaryAbelianSolutions.exists_comp_lift_pLowerCentralSeries_eq
    (h : HasElementaryAbelianSolutions p G) (P : FiniteEmbeddingProblem.{u, u, u} G) (k : ℕ) :
    ∃ β : G →* P.E ⧸ P.α.ker.pLowerCentralSeries p k, IsOpen (β.ker : Set G) ∧
      (_root_.QuotientGroup.lift _ P.α (P.α.ker.pLowerCentralSeries_le p k)).comp β = P.π := by
  induction k with
  | zero =>
    -- At stage `0` the quotient is `E ⧸ ker α ≅ Q`, and the solution is `π` itself.
    have hbij : Function.Bijective
        (_root_.QuotientGroup.lift _ P.α (P.α.ker.pLowerCentralSeries_le p 0)) := by
      refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_,
        _root_.QuotientGroup.lift_surjective_of_surjective _ _ P.α_surjective _⟩
      rw [_root_.QuotientGroup.ker_lift, Subgroup.map_eq_bot_iff, _root_.QuotientGroup.ker_mk',
        pLowerCentralSeries_zero]
    let e := MulEquiv.ofBijective _ hbij
    refine ⟨(e.symm : _ →* _).comp P.π, ?_, ?_⟩
    · rw [MonoidHom.ker_mulEquiv_comp]
      exact P.isOpen_ker_π
    · ext g
      exact MulEquiv.ofBijective_apply_symm_apply _ hbij
  | succ k ih =>
    -- Lift the solution modulo `λ_k` through `E ⧸ λ_{k+1} ↠ E ⧸ λ_k`, whose kernel `λ_k ⧸ λ_{k+1}`
    -- is elementary abelian.
    obtain ⟨β, hβ, hβπ⟩ := ih
    have hker : ∀ x ∈ (QuotientGroup.mapOfLE (P.α.ker.pLowerCentralSeries_succ_le p k)).ker,
        ∃ y ∈ P.α.ker.pLowerCentralSeries p k, (y : P.E ⧸ _) = x := fun x hx ↦ by
      rwa [QuotientGroup.ker_mapOfLE] at hx
    obtain ⟨β', hβ', hβ'β⟩ := h.exists_comp_eq
      (QuotientGroup.mapOfLE (P.α.ker.pLowerCentralSeries_succ_le p k))
      (QuotientGroup.mapOfLE_surjective _)
      (fun x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := hker x hx
        exact P.α.ker.mk_pow_eq_one_of_mem_pLowerCentralSeries p hy)
      (fun x hx x' hx' ↦ by
        obtain ⟨y, hy, rfl⟩ := hker x hx
        obtain ⟨y', hy', rfl⟩ := hker x' hx'
        exact (P.α.ker.commute_mk_of_mem_pLowerCentralSeries p hy hy').eq) β hβ
    refine ⟨β', hβ', ?_⟩
    rw [← hβπ, ← hβ'β, ← MonoidHom.comp_assoc]
    congr 1
    exact _root_.QuotientGroup.monoidHom_ext _ (by ext; simp)

/-- **Solvability with `p`-group kernel from solvability with elementary abelian kernel.** For a
prime `p`, if every finite embedding problem for `G` with elementary abelian kernel has a solution,
then every finite embedding problem for `G` whose kernel is a `p`-group has a solution. -/
theorem HasElementaryAbelianSolutions.hasPGroupSolutions [Fact p.Prime]
    (h : HasElementaryAbelianSolutions p G) : HasPGroupSolutions p G := by
  intro P hP
  -- The lower `p`-central series of the kernel reaches `⊥`, where `E ⧸ ⊥ ≅ E`.
  obtain ⟨m, hm⟩ := hP.exists_pLowerCentralSeries_eq_bot
  obtain ⟨β, hβ, hβπ⟩ := h.exists_comp_lift_pLowerCentralSeries_eq P m
  have hbij : Function.Bijective (_root_.QuotientGroup.mk' (P.α.ker.pLowerCentralSeries p m)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp ((_root_.QuotientGroup.ker_mk' _).trans hm),
      _root_.QuotientGroup.mk'_surjective _⟩
  let e := MulEquiv.ofBijective _ hbij
  refine ⟨(e.symm : _ →* _).comp β, FiniteEmbeddingProblem.isSolution_iff.mpr ⟨?_, ?_⟩⟩
  · rw [MonoidHom.ker_mulEquiv_comp]
    exact hβ
  · ext g
    have hg : _root_.QuotientGroup.mk' _ (e.symm (β g)) = β g :=
      MulEquiv.ofBijective_apply_symm_apply _ hbij
    rw [_root_.QuotientGroup.mk'_apply] at hg
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      ← _root_.QuotientGroup.lift_mk' _ (P.α.ker.pLowerCentralSeries_le p m),
      MonoidHom.coe_ofClass, hg, ← MonoidHom.comp_apply, hβπ]

end TauCeti
