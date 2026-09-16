/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Data.Sym.Disjoint
import Mathlib.Basic.Finite.Sigma

/-!
# Unordered tuples with one point in each member of a family

Given a family `A : Fin n → Set α` of subsets of a type, `TauCeti.Sym.pi A` is the set of
unordered `n`-tuples obtained by choosing one point in each `A i`. When the members of the family
are pairwise disjoint that choice is recorded faithfully: the unordered tuple remembers which of
its points came from which member, so `TauCeti.Sym.pi A` is parametrized by the product
`∀ i, ↥(A i)` (`TauCeti.Sym.piEquiv`).

The case to keep in mind is the pair of tori `T_α = α₁ × ⋯ × α_g` and `T_β = β₁ × ⋯ × β_g` inside
the symmetric power `Sym^g(Σ)` of a Heegaard surface, attached to the two systems of attaching
curves of a Heegaard diagram (Ozsváth--Szabó, *Holomorphic disks and topological invariants for
closed three-manifolds*, §2.1). The main result here describes their intersection: a point of
`T_α ∩ T_β` is exactly a **matching**, a bijection `σ` of the index set together with a point of
`α_i ∩ β_{σ i}` for each `i`. Consequently `T_α ∩ T_β` is finite as soon as the curves meet
finitely often, and its cardinality is the permanent of the matrix of intersection numbers
`#(α_i ∩ β_j)`; these are the points that generate the Heegaard Floer chain complex. For a
genus-one diagram the permanent degenerates to the number of intersection points of the two curves.

The parametrization by ordered tuples, its injectivity for a pairwise disjoint family, and the
description of its range are `TauCeti.Sym.ofFn_map_injective` and
`TauCeti.Sym.mem_range_ofFn_map`, which this file specializes to subtype coercions. Only the
combinatorics of unordered tuples is used, so nothing here is topological; the corresponding
statements about `TauCeti.Sym.pi A` as a subspace of the topological symmetric power are in
`TauCeti/Topology/Sym/Pi.lean`.

## Main declarations

* `TauCeti.Sym.pi`: the unordered tuples with one point in each member of the family, with
  `TauCeti.Sym.pi_nonempty_iff` recording when it is inhabited.
* `TauCeti.Sym.mem_pi_iff` and `TauCeti.Sym.mem_pi_iff_card_filter`: membership, either through an
  ordered presentation or as "exactly one point in each member".
* `TauCeti.Sym.ofFn_coe_injective` and `TauCeti.Sym.piEquiv`: for a pairwise disjoint family, the
  unordered tuples in `TauCeti.Sym.pi A` are parametrized by `∀ i, ↥(A i)`.
* `TauCeti.Sym.matchingTuple` and `TauCeti.Sym.piInterEquiv`: the unordered tuple of a matching,
  and the resulting bijection between matchings and points of `pi A ∩ pi B`.
* `TauCeti.Sym.finite_pi_inter_pi` and `TauCeti.Sym.natCard_pi_inter_pi`: the intersection is
  finite when the pairwise intersections are, with cardinality the permanent of the matrix of
  their cardinalities.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004), [arXiv:math/0101206](
  https://arxiv.org/abs/math/0101206), §2.1.
-/

public section

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ} {A B : Fin n → Set α}

/-! ### One point in each member of a family -/

/-- The unordered `n`-tuples having one point in each member of a family `A : Fin n → Set α` of
subsets, presented as the range of the parametrization by ordered tuples.

For the `g` attaching curves `α₁, …, α_g` of a Heegaard diagram on a surface `Σ` this is the torus
`T_α ⊆ Sym^g(Σ)`; the name follows `Set.pi`, of which it is the unordered analogue. -/
def pi (A : Fin n → Set α) : Set (Sym α n) :=
  Set.range fun x : ∀ i, ↥(A i) => ofFn fun i => (x i : α)

/-- `TauCeti.Sym.pi A` is by definition the range of the parametrization by ordered tuples. -/
theorem pi_eq_range (A : Fin n → Set α) :
    pi A = Set.range fun x : ∀ i, ↥(A i) => ofFn fun i => (x i : α) := (rfl)

/-- An unordered tuple has one point in each member of the family exactly when it is presented by
an ordered tuple whose `i`-th entry lies in `A i`. -/
theorem mem_pi_iff {s : Sym α n} :
    s ∈ pi A ↔ ∃ x : Fin n → α, (∀ i, x i ∈ A i) ∧ ofFn x = s := by
  rw [pi_eq_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => (x i : α), fun i => (x i).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩

/-- An ordered tuple whose `i`-th entry lies in `A i` presents an unordered tuple with one point in
each member of the family. -/
theorem ofFn_mem_pi {x : Fin n → α} (hx : ∀ i, x i ∈ A i) : ofFn x ∈ pi A :=
  mem_pi_iff.2 ⟨x, hx, rfl⟩

/-- There is an unordered tuple with one point in each member of the family exactly when every
member is nonempty. -/
@[simp]
theorem pi_nonempty_iff : (pi A).Nonempty ↔ ∀ i, (A i).Nonempty := by
  constructor
  · rintro ⟨s, hs⟩ i
    obtain ⟨x, hx, -⟩ := mem_pi_iff.1 hs
    exact ⟨x i, hx i⟩
  · intro hA
    choose x hx using hA
    exact ⟨ofFn x, ofFn_mem_pi hx⟩

/-- `TauCeti.Sym.pi A` is the image of the product `Set.pi` of the family under the quotient map
from ordered tuples. -/
theorem pi_eq_image_univ_pi (A : Fin n → Set α) : pi A = ofFn '' Set.univ.pi A := by
  ext s
  simp [mem_pi_iff, Set.mem_image]

/-! ### Pairwise disjoint families -/

/-- The members of the family are the ranges of their subtype coercions, so a pairwise disjoint
family is a family with pairwise disjoint ranges. -/
private theorem pairwise_disjoint_range_val (h : Pairwise (Function.onFun Disjoint A)) :
    Pairwise (Function.onFun Disjoint fun i => Set.range (Subtype.val : ↥(A i) → α)) := by
  simpa only [Subtype.range_coe] using h

/-- For a pairwise disjoint family, the ordered tuple with `i`-th entry in `A i` presenting a given
unordered tuple is unique: no point can be attributed to two different members. -/
theorem ofFn_coe_injective (h : Pairwise (Function.onFun Disjoint A)) :
    Function.Injective fun x : ∀ i, ↥(A i) => ofFn fun i => (x i : α) :=
  ofFn_map_injective _ (fun _ => Subtype.val_injective) (pairwise_disjoint_range_val h)

/-- The `Set.InjOn` form of `TauCeti.Sym.ofFn_coe_injective`: for a pairwise disjoint family, two
ordered tuples with `i`-th entry in `A i` presenting the same unordered tuple are equal. -/
theorem injOn_ofFn_univ_pi (h : Pairwise (Function.onFun Disjoint A)) :
    Set.InjOn (ofFn : (Fin n → α) → Sym α n) (Set.univ.pi A) := by
  intro x hx y hy hxy
  rw [Set.mem_univ_pi] at hx hy
  have hsub := ofFn_coe_injective h (a₁ := fun i => ⟨x i, hx i⟩) (a₂ := fun i => ⟨y i, hy i⟩) hxy
  exact funext fun i => congrArg Subtype.val (congrFun hsub i)

section Counting

attribute [local instance] Classical.propDecidable

/-- For a pairwise disjoint family, membership in `TauCeti.Sym.pi A` is the condition that
**exactly one** point of the unordered tuple lies in each member of the family. -/
theorem mem_pi_iff_card_filter (h : Pairwise (Function.onFun Disjoint A)) {s : Sym α n} :
    s ∈ pi A ↔ ∀ i, Multiset.card (Multiset.filter (· ∈ A i) (s : Multiset α)) = 1 := by
  rw [pi_eq_range]
  simpa only [Subtype.range_coe] using
    mem_range_ofFn_map (fun i => (Subtype.val : ↥(A i) → α))
      (pairwise_disjoint_range_val h) (w := s)

end Counting

/-- **The unordered tuples with one point in each member of a pairwise disjoint family are the
product of its members.** For the attaching curves of a Heegaard diagram this identifies `T_α`
with `α₁ × ⋯ × α_g`. -/
noncomputable def piEquiv (h : Pairwise (Function.onFun Disjoint A)) :
    (∀ i, ↥(A i)) ≃ ↥(pi A) :=
  Equiv.ofBijective (fun x => ⟨ofFn fun i => (x i : α), ofFn_mem_pi fun i => (x i).2⟩)
    ⟨fun _ _ hxy => ofFn_coe_injective h (congrArg Subtype.val hxy), by
      rintro ⟨s, hs⟩
      obtain ⟨x, hx, rfl⟩ := mem_pi_iff.1 hs
      exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩⟩

/-- The parametrization underlying `TauCeti.Sym.piEquiv` is the one by ordered tuples. -/
@[simp]
theorem coe_piEquiv (h : Pairwise (Function.onFun Disjoint A)) (x : ∀ i, ↥(A i)) :
    (piEquiv h x : Sym α n) = ofFn fun i => (x i : α) := by
  simp [piEquiv, Equiv.ofBijective]

/-! ### Matchings between two families -/

/-- An unordered tuple lies in both `TauCeti.Sym.pi A` and `TauCeti.Sym.pi B` as soon as it is
presented by an ordered tuple with `i`-th entry in `A i` and in `B (σ i)`, for a permutation `σ` of
the index set. -/
theorem ofFn_mem_pi_inter_pi {σ : Equiv.Perm (Fin n)} {x : Fin n → α} (hA : ∀ i, x i ∈ A i)
    (hB : ∀ i, x i ∈ B (σ i)) : ofFn x ∈ pi A ∩ pi B :=
  ⟨ofFn_mem_pi hA, mem_pi_iff.2 ⟨x ∘ σ.symm, fun j => by simpa using hB (σ.symm j),
    ofFn_comp_perm σ.symm x⟩⟩

/-- Conversely, an unordered tuple lying in both `TauCeti.Sym.pi A` and `TauCeti.Sym.pi B` is
presented by such an ordered tuple: the two presentations of it differ by a permutation. -/
theorem exists_perm_of_mem_pi_inter_pi {s : Sym α n} (hs : s ∈ pi A ∩ pi B) :
    ∃ (σ : Equiv.Perm (Fin n)) (x : Fin n → α),
      (∀ i, x i ∈ A i) ∧ (∀ i, x i ∈ B (σ i)) ∧ ofFn x = s := by
  obtain ⟨x, hx, rfl⟩ := mem_pi_iff.1 hs.1
  obtain ⟨y, hy, hyx⟩ := mem_pi_iff.1 hs.2
  obtain ⟨τ, rfl⟩ := ofFn_eq_ofFn_iff.1 hyx.symm
  refine ⟨τ.symm, x, hx, fun i => ?_, rfl⟩
  simpa using hy (τ.symm i)

/-- **The unordered tuple of a matching.** A permutation `σ` of the index set together with a point
of `A i ∩ B (σ i)` for each `i` determines an unordered tuple lying in both `TauCeti.Sym.pi A` and
`TauCeti.Sym.pi B`. -/
def matchingTuple (p : (σ : Equiv.Perm (Fin n)) × ∀ i, ↥(A i ∩ B (σ i))) : ↥(pi A ∩ pi B) :=
  ⟨ofFn fun i => ((p.2 i : α)),
    ofFn_mem_pi_inter_pi (fun i => (p.2 i).2.1) fun i => (p.2 i).2.2⟩

/-- The unordered tuple of a matching is the tuple of its chosen points. -/
@[simp]
theorem coe_matchingTuple (p : (σ : Equiv.Perm (Fin n)) × ∀ i, ↥(A i ∩ B (σ i))) :
    (matchingTuple p : Sym α n) = ofFn fun i => ((p.2 i : α)) := (rfl)

/-- Every unordered tuple lying in both `TauCeti.Sym.pi A` and `TauCeti.Sym.pi B` comes from a
matching. -/
theorem matchingTuple_surjective :
    Function.Surjective (matchingTuple (A := A) (B := B)) := by
  rintro ⟨s, hs⟩
  obtain ⟨σ, x, hA, hB, rfl⟩ := exists_perm_of_mem_pi_inter_pi hs
  exact ⟨⟨σ, fun i => ⟨x i, hA i, hB i⟩⟩, rfl⟩

/-- For a pair of pairwise disjoint families, a matching is determined by the unordered tuple of
its chosen points: the points determine the permutation, and the permutation determines them. -/
theorem matchingTuple_injective (hA : Pairwise (Function.onFun Disjoint A))
    (hB : Pairwise (Function.onFun Disjoint B)) :
    Function.Injective (matchingTuple (A := A) (B := B)) := by
  rintro ⟨σ, p⟩ ⟨τ, q⟩ hpq
  have hpts : (fun i => ((p i : α))) = fun i => ((q i : α)) :=
    injOn_ofFn_univ_pi hA (Set.mem_univ_pi.2 fun i => (p i).2.1)
      (Set.mem_univ_pi.2 fun i => (q i).2.1) (congrArg Subtype.val hpq)
  obtain rfl : σ = τ := by
    refine Equiv.ext fun i => by_contra fun hne => ?_
    refine Set.disjoint_left.1 (hB hne) (p i).2.2 ?_
    exact congrFun hpts i ▸ (q i).2.2
  exact congrArg _ (funext fun i => Subtype.ext (congrFun hpts i))

/-- **The points common to two tori are the matchings.** For a pair of pairwise disjoint families,
the unordered tuples with one point in each `A i` and one point in each `B j` correspond to the
data of a permutation `σ` of the index set and a point of `A i ∩ B (σ i)` for each `i`.

For the attaching curves of a Heegaard diagram this is the description of `T_α ∩ T_β`, whose points
generate the Heegaard Floer chain complex. -/
noncomputable def piInterEquiv (hA : Pairwise (Function.onFun Disjoint A))
    (hB : Pairwise (Function.onFun Disjoint B)) :
    ((σ : Equiv.Perm (Fin n)) × ∀ i, ↥(A i ∩ B (σ i))) ≃ ↥(pi A ∩ pi B) :=
  Equiv.ofBijective matchingTuple ⟨matchingTuple_injective hA hB, matchingTuple_surjective⟩

/-- `TauCeti.Sym.piInterEquiv` sends a matching to its unordered tuple. -/
@[simp]
theorem piInterEquiv_apply (hA : Pairwise (Function.onFun Disjoint A))
    (hB : Pairwise (Function.onFun Disjoint B))
    (p : (σ : Equiv.Perm (Fin n)) × ∀ i, ↥(A i ∩ B (σ i))) :
    piInterEquiv hA hB p = matchingTuple p := (rfl)

/-! ### Counting the common points -/

/-- Two tori meet in a finite set as soon as the members of the two families meet pairwise in
finite sets: every common point is a matching, and there are finitely many of those. -/
theorem finite_pi_inter_pi (hfin : ∀ i j, (A i ∩ B j).Finite) : (pi A ∩ pi B).Finite := by
  have hfib (i j : Fin n) : Finite ↥(A i ∩ B j) := (hfin i j).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_surjective _ matchingTuple_surjective)

/-- **The number of common points of two tori is the permanent of the matrix of intersection
numbers.** Summing over the matchings groups the common points by the permutation matching the
members of the first family to those of the second.

For the attaching curves of a Heegaard diagram this counts the generators of the Heegaard Floer
chain complex. -/
theorem natCard_pi_inter_pi (hA : Pairwise (Function.onFun Disjoint A))
    (hB : Pairwise (Function.onFun Disjoint B)) (hfin : ∀ i j, (A i ∩ B j).Finite) :
    Nat.card ↥(pi A ∩ pi B) =
      (Matrix.of fun i j => Nat.card ↥(A i ∩ B j)).permanent := by
  have hfib (i j : Fin n) : Finite ↥(A i ∩ B j) := (hfin i j).to_subtype
  rw [← Nat.card_congr (piInterEquiv hA hB), Nat.card_sigma,
    ← Matrix.permanent_transpose, Matrix.permanent]
  exact Finset.sum_congr rfl fun σ _ => Nat.card_pi

/-- For a single pair of sets the permanent count degenerates to the number of common points: the
generator count of a genus-one Heegaard diagram, carrying one attaching curve on each side. No
finiteness is needed, the two sides being `0` together when the two curves meet infinitely often. -/
theorem natCard_pi_inter_pi_fin_one {A B : Fin 1 → Set α} :
    Nat.card ↥(pi A ∩ pi B) = Nat.card ↥(A 0 ∩ B 0) :=
  Nat.card_congr <| (piInterEquiv (A := A) (B := B) Subsingleton.pairwise
    Subsingleton.pairwise).symm.trans <| (Equiv.uniqueSigma _).trans (Equiv.piUnique _)

end Sym

end TauCeti
