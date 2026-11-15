/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Eichler's theorem: the decomposition into indecomposable summands

A positive definite integral lattice is an orthogonal sum of indecomposable sublattices in exactly
one way. This file proves this for a reflexive bilinear form `B` on an arbitrary `ℤ`-module `M`
whose values `B x x` on nonzero vectors are positive.

A vector is *orthogonally irreducible* when it is nonzero and is not the sum of two nonzero
vectors orthogonal to each other. Since `B (y + z) (y + z) = B y y + B z z` when `y` and `z` are
orthogonal, induction on the norm writes every vector as a sum of irreducible vectors. Join two
irreducible vectors when they are not orthogonal; the spans of the connected components of this
graph are the *orthogonal components* `LinearMap.BilinForm.orthComponents B`.

An irreducible vector of `P ⊔ Q` with `P` and `Q` orthogonal lies in `P` or in `Q`, and two
non-orthogonal irreducible vectors lie in the same summand. Hence each component of the graph
lies in one summand of any orthogonal decomposition, which gives both the indecomposability of
the orthogonal components and the uniqueness of the decomposition.

## Main definitions

* `LinearMap.BilinForm.IsOrthIrreducible`: a nonzero vector that is not the sum of two nonzero
  orthogonal vectors.
* `LinearMap.BilinForm.IsOrthIndecomposable`: a nonzero submodule that is not the sum of two
  nonzero orthogonal submodules.
* `LinearMap.BilinForm.orthComponents`: the spans of the connected components of the
  non-orthogonality graph on irreducible vectors.

## Main results

* `LinearMap.BilinForm.span_setOf_isOrthIrreducible`: for a positive definite integral form the
  irreducible vectors span.
* `LinearMap.BilinForm.isOrthIndecomposable_of_mem_orthComponents`,
  `LinearMap.BilinForm.pairwise_orthComponents` and `LinearMap.BilinForm.sSup_orthComponents`:
  the orthogonal components are indecomposable, pairwise orthogonal, and span.
* `LinearMap.BilinForm.eq_orthComponents_iff`: **Eichler's theorem**. A set of submodules is a
  decomposition of `M` into pairwise orthogonal indecomposable submodules exactly when it is the
  set of orthogonal components.
* `LinearMap.BilinForm.sSupIndep_orthComponents` and
  `LinearMap.BilinForm.finite_orthComponents`: the sum is direct, and finite for a finitely
  generated module.

## References

* M. Eichler, *Note zur Theorie der Kristallgitter*, Math. Ann. 125 (1952), 51–55.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 105:1.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, Theorem 6.4.
-/

public section

open Submodule

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (B : LinearMap.BilinForm R M)

/-- A vector is *orthogonally irreducible* for `B` when it is nonzero and is not the sum of two
nonzero vectors `y`, `z` with `B y z = 0`. -/
def IsOrthIrreducible (x : M) : Prop :=
  x ≠ 0 ∧ ∀ y z, y + z = x → B y z = 0 → y = 0 ∨ z = 0

/-- A submodule is *orthogonally indecomposable* for `B` when it is nonzero and is not the sum of
two nonzero submodules orthogonal to each other. -/
def IsOrthIndecomposable (N : Submodule R M) : Prop :=
  N ≠ ⊥ ∧ ∀ P Q : Submodule R M, P ≤ B.orthogonal Q → P ⊔ Q = N → P = ⊥ ∨ Q = ⊥

/-- The graph on orthogonally irreducible vectors joining two distinct vectors that are not
orthogonal. -/
private def orthIrreducibleGraph : SimpleGraph {x : M // B.IsOrthIrreducible x} :=
  SimpleGraph.fromRel fun x y ↦ B x y ≠ 0

/-- The *orthogonal components* of `B`: the spans of the connected components of the graph on
orthogonally irreducible vectors in which two vectors are joined when they are not orthogonal.
For a positive definite integral form these are the summands of the unique decomposition into
orthogonally indecomposable submodules (`LinearMap.BilinForm.eq_orthComponents_iff`). -/
def orthComponents : Set (Submodule R M) :=
  Set.range fun c : (orthIrreducibleGraph B).ConnectedComponent ↦
    span R (Subtype.val '' c.supp)

variable {B}

/-- The defining property of an orthogonally irreducible vector. -/
theorem isOrthIrreducible_iff {x : M} :
    B.IsOrthIrreducible x ↔ x ≠ 0 ∧ ∀ y z, y + z = x → B y z = 0 → y = 0 ∨ z = 0 :=
  Iff.rfl

/-- The defining property of an orthogonally indecomposable submodule. -/
theorem isOrthIndecomposable_iff {N : Submodule R M} :
    B.IsOrthIndecomposable N ↔
      N ≠ ⊥ ∧ ∀ P Q : Submodule R M, P ≤ B.orthogonal Q → P ⊔ Q = N → P = ⊥ ∨ Q = ⊥ :=
  Iff.rfl

/-- An orthogonally irreducible vector is nonzero. -/
theorem IsOrthIrreducible.ne_zero {x : M} (hx : B.IsOrthIrreducible x) : x ≠ 0 :=
  hx.1

/-- An orthogonally irreducible vector of `P ⊔ Q`, where `P` is orthogonal to `Q`, lies in `P`
or in `Q`. -/
theorem IsOrthIrreducible.mem_or_mem_of_mem_sup {x : M} (hx : B.IsOrthIrreducible x)
    {P Q : Submodule R M} (hPQ : P ≤ B.orthogonal Q) (h : x ∈ P ⊔ Q) : x ∈ P ∨ x ∈ Q := by
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp h
  rcases hx.2 z y (add_comm z y) (hPQ hy z hz) with rfl | rfl
  · simpa using Or.inl hy
  · simpa using Or.inr hz

/-- An orthogonally irreducible vector lies in a member of every family of pairwise orthogonal
submodules spanning `M`. -/
theorem IsOrthIrreducible.exists_mem_of_sSup_eq_top {x : M} (hx : B.IsOrthIrreducible x)
    {S : Set (Submodule R M)} (hS : S.Pairwise fun N N' ↦ N ≤ B.orthogonal N')
    (htop : sSup S = ⊤) : ∃ N ∈ S, x ∈ N := by
  classical
  obtain ⟨s, hsS, hxs⟩ := mem_sSup_iff_exists_finset.mp (htop ▸ mem_top : x ∈ sSup S)
  induction s using Finset.induction_on with
  | empty => exact absurd (by simpa using hxs) hx.ne_zero
  | insert a s ha ih =>
    have haS : a ∈ S := hsS (Finset.mem_insert_self a s)
    have hle : ⨆ i ∈ s, i ≤ B.orthogonal a := iSup₂_le fun i hi ↦
      hS (hsS (Finset.mem_insert_of_mem hi)) haS fun h ↦ ha (h ▸ hi)
    rw [Finset.iSup_insert, sup_comm] at hxs
    rcases hx.mem_or_mem_of_mem_sup hle hxs with h | h
    · exact ih (fun i hi ↦ hsS (Finset.mem_insert_of_mem hi)) h
    · exact ⟨a, haS, h⟩

private theorem apply_eq_zero_of_not_reachable {u v : {x : M // B.IsOrthIrreducible x}}
    (h : ¬(orthIrreducibleGraph B).Reachable u v) : B u v = 0 := by
  by_contra huv
  refine h (SimpleGraph.Adj.reachable ?_)
  rw [orthIrreducibleGraph, SimpleGraph.fromRel_adj]
  exact ⟨fun huv' ↦ h (huv' ▸ SimpleGraph.Reachable.refl u), Or.inl huv⟩

/-- Irreducible vectors outside a connected component of the non-orthogonality graph span a
submodule orthogonal to the span of that component. -/
private theorem span_le_orthogonal_span_supp {s : Set M} (hs : ∀ x ∈ s, B.IsOrthIrreducible x)
    (c : (orthIrreducibleGraph B).ConnectedComponent) (hsc : Disjoint s (Subtype.val '' c.supp)) :
    span R s ≤ B.orthogonal (span R (Subtype.val '' c.supp)) := by
  refine span_le.mpr fun x hx ↦ ?_
  rw [SetLike.mem_coe, orthogonal, mem_orthogonalBilin_span]
  rintro _ ⟨v, hv, rfl⟩
  refine apply_eq_zero_of_not_reachable (v := ⟨x, hs x hx⟩) fun h ↦ ?_
  exact Set.disjoint_left.mp hsc hx ⟨_, (SimpleGraph.ConnectedComponent.sound h).symm.trans hv, rfl⟩

/-- Distinct orthogonal components are orthogonal. -/
theorem pairwise_orthComponents :
    B.orthComponents.Pairwise fun N N' ↦ N ≤ B.orthogonal N' := by
  rintro _ ⟨c', rfl⟩ _ ⟨c, rfl⟩ hne
  refine span_le_orthogonal_span_supp (by rintro _ ⟨v, -, rfl⟩; exact v.2) c ?_
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
  have hcc : c' = c := by rw [← hv, ← hw, Subtype.ext hvw]
  exact hne (hcc ▸ rfl)

/-- For an anisotropic form, the orthogonal components are independent. -/
theorem sSupIndep_orthComponents (hani : B.toQuadraticMap.Anisotropic) :
    sSupIndep B.orthComponents :=
  sSupIndep_of_pairwise_le_orthogonal hani pairwise_orthComponents

/-- For an anisotropic form on a Noetherian module, there are finitely many orthogonal
components. -/
theorem finite_orthComponents [IsNoetherian R M] (hani : B.toQuadraticMap.Anisotropic) :
    B.orthComponents.Finite :=
  WellFoundedGT.finite_of_sSupIndep (sSupIndep_orthComponents hani)

/-- Within a connected component whose vertices all lie in `P` or in `Q`, with no edge from `P`
to `Q`, every vertex lies in the summand containing a given one. -/
private theorem forall_mem_of_mem {c : (orthIrreducibleGraph B).ConnectedComponent}
    {P Q : Submodule R M} (hmem : ∀ u ∈ c.supp, (u : M) ∈ P ∨ (u : M) ∈ Q)
    (hadj : ∀ u v : {x : M // B.IsOrthIrreducible x}, (u : M) ∈ P → (v : M) ∈ Q →
      ¬(orthIrreducibleGraph B).Adj u v)
    {u₀ : {x : M // B.IsOrthIrreducible x}} (hu₀ : u₀ ∈ c.supp) (h₀ : (u₀ : M) ∈ P) :
    ∀ u ∈ c.supp, (u : M) ∈ P := by
  intro u hu
  have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (c.reachable_of_mem_supp hu₀ hu)
  clear hu
  suffices u ∈ c.supp ∧ (u : M) ∈ P from this.2
  induction h with
  | refl => exact ⟨hu₀, h₀⟩
  | @tail v w _ hvw ih =>
    have hw := c.mem_supp_of_adj_mem_supp ih.1 hvw
    exact ⟨hw, (hmem w hw).resolve_right fun hwQ ↦ hadj v w ih.2 hwQ hvw⟩

/-- For a reflexive anisotropic form, each orthogonal component is orthogonally indecomposable. -/
theorem isOrthIndecomposable_of_mem_orthComponents (hB : B.IsRefl)
    (hani : B.toQuadraticMap.Anisotropic) {N : Submodule R M} (hN : N ∈ B.orthComponents) :
    B.IsOrthIndecomposable N := by
  obtain ⟨c, rfl⟩ := hN
  dsimp only
  obtain ⟨u₀, hu₀⟩ := c.nonempty_supp
  refine ⟨(Submodule.ne_bot_iff _).mpr ⟨u₀, subset_span ⟨u₀, hu₀, rfl⟩, u₀.2.ne_zero⟩,
    fun P Q hPQ hsup ↦ ?_⟩
  have hmem : ∀ u ∈ c.supp, (u : M) ∈ P ∨ (u : M) ∈ Q := fun u hu ↦
    u.2.mem_or_mem_of_mem_sup hPQ (hsup ▸ subset_span ⟨u, hu, rfl⟩)
  -- No edge joins a vector of `P` to a vector of `Q`, so the component lies in one summand.
  have hadj : ∀ u v : {x : M // B.IsOrthIrreducible x}, (u : M) ∈ P → (v : M) ∈ Q →
      ¬(orthIrreducibleGraph B).Adj u v := fun u v hu hv huv ↦ by
    have h₁ : B v u = 0 := hPQ hu v hv
    rw [orthIrreducibleGraph, SimpleGraph.fromRel_adj] at huv
    exact huv.2.elim (· (hB _ _ h₁)) (· h₁)
  rcases hmem u₀ hu₀ with h₀ | h₀
  · have hle : span R (Subtype.val '' c.supp) ≤ P := span_le.mpr <| by
      rintro _ ⟨u, hu, rfl⟩
      exact forall_mem_of_mem hmem hadj hu₀ h₀ u hu
    exact Or.inr <| eq_bot_of_le_orthogonal hani <|
      (le_sup_right.trans hsup.le).trans (hle.trans hPQ)
  · have hle : span R (Subtype.val '' c.supp) ≤ Q := span_le.mpr <| by
      rintro _ ⟨u, hu, rfl⟩
      exact forall_mem_of_mem (fun u hu ↦ (hmem u hu).symm)
        (fun u v hu hv huv ↦ hadj v u hv hu huv.symm) hu₀ h₀ u hu
    have hPQ' : P ≤ Q := (le_sup_left.trans hsup.le).trans hle
    exact Or.inl <| eq_bot_of_le_orthogonal hani <| hPQ.trans (orthogonal_le hPQ')

section Int

variable {M : Type*} [AddCommGroup M] {B : LinearMap.BilinForm ℤ M}

/-- For a reflexive positive definite integral form, every vector is a sum of orthogonally
irreducible vectors. -/
theorem span_setOf_isOrthIrreducible (hB : B.IsRefl) (hpos : B.toQuadraticMap.PosDef) :
    span ℤ {x | B.IsOrthIrreducible x} = ⊤ := by
  refine eq_top_iff'.mpr fun x ↦ ?_
  induction hn : (B x x).toNat using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases hx : B.IsOrthIrreducible x
  · exact subset_span hx
  by_cases h0 : x = 0
  · exact h0 ▸ zero_mem _
  obtain ⟨y, z, rfl, hyz, hy, hz⟩ : ∃ y z, y + z = x ∧ B y z = 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
    simpa [IsOrthIrreducible, h0, not_or] using hx
  have hpy : 0 < B y y := by simpa using hpos y hy
  have hpz : 0 < B z z := by simpa using hpos z hz
  have hsum : B (y + z) (y + z) = B y y + B z z := by simp [hyz, hB y z hyz]
  exact add_mem (ih _ (by omega) y rfl) (ih _ (by omega) z rfl)

/-- For a reflexive positive definite integral form, the orthogonal components span. -/
theorem sSup_orthComponents (hB : B.IsRefl) (hpos : B.toQuadraticMap.PosDef) :
    sSup B.orthComponents = ⊤ := by
  rw [orthComponents, sSup_range, ← span_iUnion, ← Set.image_iUnion,
    SimpleGraph.iUnion_connectedComponentSupp, Set.image_univ, Subtype.range_coe_subtype]
  exact span_setOf_isOrthIrreducible hB hpos

/-- A member of a decomposition into pairwise orthogonal submodules is spanned by the irreducible
vectors it contains. -/
private theorem span_setOf_isOrthIrreducible_and_mem (hB : B.IsRefl)
    (hpos : B.toQuadraticMap.PosDef) {S : Set (Submodule ℤ M)}
    (hS : S.Pairwise fun N N' ↦ N ≤ B.orthogonal N') (htop : sSup S = ⊤) {N : Submodule ℤ M}
    (hN : N ∈ S) : span ℤ {x | B.IsOrthIrreducible x ∧ x ∈ N} = N := by
  have hIN : span ℤ {x | B.IsOrthIrreducible x ∧ x ∈ N} ≤ N := span_le.mpr fun x hx ↦ hx.2
  refine le_antisymm hIN fun n hn ↦ ?_
  -- The irreducible vectors outside `N` lie in other members, hence are orthogonal to `N`.
  have hJ : span ℤ {x | B.IsOrthIrreducible x ∧ x ∉ N} ≤ B.orthogonal N :=
    span_le.mpr fun x (hx : B.IsOrthIrreducible x ∧ x ∉ N) ↦ by
      obtain ⟨N', hN', hxN'⟩ := hx.1.exists_mem_of_sSup_eq_top hS htop
      exact hS hN' hN (fun h ↦ hx.2 (h ▸ hxN')) hxN'
  have hn' : n ∈ span ℤ {x | B.IsOrthIrreducible x ∧ x ∈ N} ⊔
      span ℤ {x | B.IsOrthIrreducible x ∧ x ∉ N} := by
    have hunion : {x | B.IsOrthIrreducible x ∧ x ∈ N} ∪ {x | B.IsOrthIrreducible x ∧ x ∉ N} =
        {x | B.IsOrthIrreducible x} := by
      ext x
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      tauto
    rw [← span_union, hunion, span_setOf_isOrthIrreducible hB hpos]
    exact mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hn'
  have haN : a ∈ N := hIN ha
  have hbN : b ∈ N := by simpa using sub_mem hn haN
  have hb0 : b = 0 := hpos.anisotropic b (by simpa using hJ hb b hbN)
  simpa [hb0] using ha

/-- In a decomposition into pairwise orthogonal indecomposable submodules, the member containing
an irreducible vector `u` is the span of the connected component of `u`. -/
private theorem eq_span_supp (hB : B.IsRefl) (hpos : B.toQuadraticMap.PosDef)
    {S : Set (Submodule ℤ M)} (hind : ∀ N ∈ S, B.IsOrthIndecomposable N)
    (hS : S.Pairwise fun N N' ↦ N ≤ B.orthogonal N') (htop : sSup S = ⊤) {N : Submodule ℤ M}
    (hN : N ∈ S) {u : {x : M // B.IsOrthIrreducible x}} (hu : (u : M) ∈ N) :
    N = span ℤ (Subtype.val '' ((orthIrreducibleGraph B).connectedComponentMk u).supp) := by
  set c := (orthIrreducibleGraph B).connectedComponentMk u
  set I := {x | B.IsOrthIrreducible x ∧ x ∈ N}
  -- The component of `u` lies in `N`, since an edge never leaves a member of `S`.
  have hC : Subtype.val '' c.supp ⊆ I := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v.2, ?_⟩
    have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (SimpleGraph.ConnectedComponent.exact hv.symm)
    clear hv
    induction h with
    | refl => exact hu
    | @tail w w' _ hww' hw =>
      obtain ⟨N', hN', hw'⟩ := w'.2.exists_mem_of_sSup_eq_top hS htop
      by_contra hne
      have h₁ : B w' w = 0 := hS hN hN' (fun h ↦ hne (h ▸ hw')) hw w' hw'
      rw [orthIrreducibleGraph, SimpleGraph.fromRel_adj] at hww'
      exact hww'.2.elim (· (hB _ _ h₁)) (· h₁)
  -- The other irreducible vectors of `N` span an orthogonal summand, which must vanish.
  have hsplit : span ℤ (Subtype.val '' c.supp) ⊔ span ℤ (I \ Subtype.val '' c.supp) = N := by
    rw [← span_union, Set.union_sdiff_cancel hC,
      span_setOf_isOrthIrreducible_and_mem hB hpos hS htop hN]
  have horth : span ℤ (I \ Subtype.val '' c.supp) ≤
      B.orthogonal (span ℤ (Subtype.val '' c.supp)) :=
    span_le_orthogonal_span_supp (fun x (hx : x ∈ I \ Subtype.val '' c.supp) ↦ hx.1.1) c
      Set.disjoint_sdiff_left
  rcases (hind N hN).2 _ _ horth (by rw [sup_comm, hsplit]) with h | h
  · rw [h, sup_bot_eq] at hsplit
    exact hsplit.symm
  · exact absurd ((mem_bot ℤ).mp (h ▸ subset_span
      ⟨u, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩)) u.2.ne_zero

/-- **Eichler's theorem.** For a reflexive positive definite integral form, a set of submodules
consists of pairwise orthogonal orthogonally indecomposable submodules spanning `M` exactly when
it is the set of orthogonal components. In particular such a decomposition exists and is unique. -/
theorem eq_orthComponents_iff (hB : B.IsRefl) (hpos : B.toQuadraticMap.PosDef)
    {S : Set (Submodule ℤ M)} :
    S = B.orthComponents ↔ (∀ N ∈ S, B.IsOrthIndecomposable N) ∧
      S.Pairwise (fun N N' ↦ N ≤ B.orthogonal N') ∧ sSup S = ⊤ := by
  refine ⟨?_, fun ⟨hind, hS, htop⟩ ↦ Set.ext fun N ↦ ⟨fun hN ↦ ?_, ?_⟩⟩
  · rintro rfl
    exact ⟨fun N hN ↦ isOrthIndecomposable_of_mem_orthComponents hB hpos.anisotropic hN,
      pairwise_orthComponents, sSup_orthComponents hB hpos⟩
  · obtain ⟨u, hu⟩ : ∃ u : {x : M // B.IsOrthIrreducible x}, (u : M) ∈ N := by
      by_contra! h
      refine (hind N hN).1 ?_
      rw [← span_setOf_isOrthIrreducible_and_mem hB hpos hS htop hN, span_eq_bot]
      exact fun x hx ↦ (h ⟨x, hx.1⟩ hx.2).elim
    exact ⟨_, (eq_span_supp hB hpos hind hS htop hN hu).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨u, rfl⟩ := c.exists_rep
    obtain ⟨N, hN, hu⟩ := u.2.exists_mem_of_sSup_eq_top hS htop
    rw [eq_span_supp hB hpos hind hS htop hN hu] at hN
    exact hN

/-- For a reflexive positive definite integral form, `M` is orthogonally indecomposable exactly
when it is its only orthogonal component. -/
theorem isOrthIndecomposable_top_iff (hB : B.IsRefl) (hpos : B.toQuadraticMap.PosDef) :
    B.IsOrthIndecomposable ⊤ ↔ B.orthComponents = {⊤} := by
  refine ⟨fun h ↦ ((eq_orthComponents_iff hB hpos).mpr ?_).symm, fun h ↦
    isOrthIndecomposable_of_mem_orthComponents hB hpos.anisotropic (h ▸ Set.mem_singleton ⊤)⟩
  exact ⟨fun N hN ↦ (Set.mem_singleton_iff.mp hN) ▸ h, Set.pairwise_singleton _ _, sSup_singleton⟩

end Int

end LinearMap.BilinForm
