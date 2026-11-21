/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.PotentialIso
public import TauCeti.ModelTheory.Order

/-!
# Potential isomorphism of well-ordered structures

Well-ordered structures are rigid: in any back-and-forth system `S` of finitely generated partial
equivalences out of a well-ordered structure `M`, no two distinct elements of `M` can be sent to
the same element of `N` by members of `S`, as otherwise a minimal counterexample on `M` yields a
strictly smaller counterexample by one forth step and one back step. Consequently, all members of
`S` agree on overlaps and form a directed system whose `DirectLimit.partialEquivLimit` is a single
global isomorphism `e : M ≃[L] N` lying above every member of `S`
(`TauCeti.exists_forall_le_equiv_of_isWellOrder_rel`).

Therefore potential isomorphism with a well-ordered structure is equivalent to isomorphism, with no
cardinality assumption on either structure and no restriction on the language: function symbols,
nullary relations, empty structures and arbitrary universes are all allowed. This applies both to a
binary relation symbol `lt : L.Relations 2` that well-orders `M`
(`TauCeti.potentialIso_iff_iso_of_isWellOrder`) and to an ordered structure whose underlying order
is a well-order (`TauCeti.potentialIso_iff_iso_of_wellFoundedLT`).

## Main results

* `TauCeti.exists_forall_le_equiv_of_isWellOrder_rel`: every back-and-forth system out of a
  well-ordered structure is simultaneously bounded by a single isomorphism.
* `TauCeti.potentialIso_iff_iso_of_isWellOrder`: for a structure well-ordered by a binary relation
  symbol, potential isomorphism is equivalent to isomorphism.
* `TauCeti.potentialIso_iff_iso_of_wellFoundedLT`: for an ordered structure whose order is a
  well-order, potential isomorphism is equivalent to isomorphism.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language Structure

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- The pair relation of a family of partial equivalences: some member sends `m` to `n`. -/
private def Pair (S : Set (L.FGEquiv M N)) (m : M) (n : N) : Prop :=
  ∃ f ∈ S, ∃ hm : m ∈ f.val.dom, (f.val.toEquiv ⟨m, hm⟩ : N) = n

private theorem not_pair_of_rel {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.val.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.val.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.val.dom), r x y ↔ s (f.val.toEquiv x) (f.val.toEquiv y)) :
    ∀ m₁ m₂ n, r m₂ m₁ → Pair S m₁ n → ¬ Pair S m₂ n := by
  intro m₁
  refine WellFounded.induction (inferInstance : IsWellOrder M r).wf
    (C := fun m₁ => ∀ m₂ n, r m₂ m₁ → Pair S m₁ n → ¬ Pair S m₂ n) m₁
    fun m₁ ih m₂ n hm₂₁ h₁ h₂ => ?_
  obtain ⟨f, hf, hm₁, hfn⟩ := h₁
  obtain ⟨g, hg, hm₂, hgn⟩ := h₂
  -- Extend `f` forward to `m₂`, obtaining an image `y` strictly `s`-below `n`.
  obtain ⟨f', hf', hm₂', hff'⟩ := hforth f hf m₂
  have hm₁' : m₁ ∈ f'.val.dom := PartialEquiv.dom_le_dom hff' hm₁
  have hf'n : (f'.val.toEquiv ⟨m₁, hm₁'⟩ : N) = n :=
    (PartialEquiv.toEquiv_apply_of_le hff' hm₁).trans hfn
  set y : N := (f'.val.toEquiv ⟨m₂, hm₂'⟩ : N)
  have hsy : s y n := hf'n ▸ (hrel f' hf' ⟨m₂, hm₂'⟩ ⟨m₁, hm₁'⟩).mp hm₂₁
  -- Extend `g` backward to `y`, pulling `y` back to `m₃` strictly `r`-below `m₂`.
  obtain ⟨g', hg', hy', hgg'⟩ := hback g hg y
  have hm₂g : m₂ ∈ g'.val.dom := PartialEquiv.dom_le_dom hgg' hm₂
  have hg'n : (g'.val.toEquiv ⟨m₂, hm₂g⟩ : N) = n :=
    (PartialEquiv.toEquiv_apply_of_le hgg' hm₂).trans hgn
  set m₃ : g'.val.dom := g'.val.toEquiv.symm ⟨y, hy'⟩
  have hg'm₃ : (g'.val.toEquiv m₃ : N) = y := by simp [m₃]
  have hm₃₂ : r m₃ m₂ := (hrel g' hg' m₃ ⟨m₂, hm₂g⟩).mpr (by rw [hg'm₃, hg'n]; exact hsy)
  exact ih m₂ hm₂₁ m₃ y hm₃₂ ⟨f', hf', hm₂', rfl⟩ ⟨g', hg', m₃.property, hg'm₃⟩

private theorem pair_left_unique {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.val.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.val.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.val.dom), r x y ↔ s (f.val.toEquiv x) (f.val.toEquiv y))
    {m₁ m₂ : M} {n : N} (h₁ : Pair S m₁ n) (h₂ : Pair S m₂ n) : m₁ = m₂ := by
  rcases trichotomous_of r m₁ m₂ with hlt | rfl | hgt
  · exact (not_pair_of_rel hforth hback hrel m₂ m₁ n hlt h₂ h₁).elim
  · rfl
  · exact (not_pair_of_rel hforth hback hrel m₁ m₂ n hgt h₁ h₂).elim

private theorem pair_right_unique {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.val.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.val.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.val.dom), r x y ↔ s (f.val.toEquiv x) (f.val.toEquiv y))
    {m : M} {n₁ n₂ : N} (h₁ : Pair S m n₁) (h₂ : Pair S m n₂) : n₁ = n₂ := by
  obtain ⟨f, hf, hm, hfn₁⟩ := h₁
  obtain ⟨f', hf', hn₂, hff'⟩ := hback f hf n₂
  set m' : f'.val.dom := f'.val.toEquiv.symm ⟨n₂, hn₂⟩
  have hm'n₂ : (f'.val.toEquiv m' : N) = n₂ := by simp [m']
  have heq : (m' : M) = m :=
    pair_left_unique hforth hback hrel ⟨f', hf', m'.property, hm'n₂⟩ h₂
  have hm' : m ∈ f'.val.dom := PartialEquiv.dom_le_dom hff' hm
  have hfn₁' : (f'.val.toEquiv ⟨m, hm'⟩ : N) = n₁ :=
    (PartialEquiv.toEquiv_apply_of_le hff' hm).trans hfn₁
  calc n₁ = (f'.val.toEquiv ⟨m, hm'⟩ : N) := hfn₁'.symm
    _ = (f'.val.toEquiv m' : N) := congrArg (fun x : f'.val.dom => (f'.val.toEquiv x : N))
        (Subtype.ext heq.symm)
    _ = n₂ := hm'n₂

/-- Every back-and-forth system of finitely generated partial equivalences out of a well-ordered
structure is simultaneously bounded by a single isomorphism. No cardinality assumption is made on
`M` or `N`, and the language is arbitrary. -/
theorem exists_forall_le_equiv_of_isWellOrder_rel {S : Set (L.FGEquiv M N)} (hS : S.Nonempty)
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.val.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.val.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.val.dom), r x y ↔ s (f.val.toEquiv x) (f.val.toEquiv y)) :
    ∃ e : M ≃[L] N, ∀ f ∈ S, f.val ≤ e.toEmbedding.toPartialEquiv := by
  obtain ⟨f₀, hf₀⟩ := hS
  let : Nonempty S := ⟨⟨f₀, hf₀⟩⟩
  -- Any two members of `S` agree on overlaps, so `S` is directed under extension.
  have : IsDirectedOrder S := ⟨fun f g => by
    obtain ⟨h, hh, hdom, hgh⟩ :=
      FGEquiv.exists_le_and_le_dom_of_fg hforth g.property f.val.property
    refine ⟨⟨h, hh⟩, ?_, hgh⟩
    refine (PartialEquiv.le_def _ _).mpr ⟨hdom, ?_⟩
    ext ⟨x, hx⟩
    exact (pair_right_unique hforth hback hrel ⟨f.val, f.property, hx, rfl⟩
      ⟨h, hh, hdom hx, rfl⟩).symm⟩
  let C : S →o M ≃ₚ[L] N := ⟨fun f => f.val.val, fun _ _ h => h⟩
  let F := DirectLimit.partialEquivLimit C
  have hdom : F.dom = ⊤ := top_unique fun m _ => by
    obtain ⟨g, hg, hm, -⟩ := hforth f₀ hf₀ m
    exact PartialEquiv.dom_le_dom (DirectLimit.le_partialEquivLimit C ⟨g, hg⟩) hm
  have hcod : F.cod = ⊤ := top_unique fun n _ => by
    obtain ⟨g, hg, hn, -⟩ := hback f₀ hf₀ n
    exact PartialEquiv.cod_le_cod (DirectLimit.le_partialEquivLimit C ⟨g, hg⟩) hn
  refine ⟨PartialEquiv.toEquivOfEqTop hdom hcod, fun f hf => ?_⟩
  rw [PartialEquiv.toEquivOfEqTop_toEmbedding, Embedding.toPartialEquiv_toEmbedding hdom]
  exact DirectLimit.le_partialEquivLimit C ⟨f, hf⟩

/-- Potential isomorphism out of a structure carrying a well-ordering preserved by all finitely
generated partial equivalences yields an isomorphism, with no cardinality assumption on either
structure. -/
theorem PotentialIso.nonempty_equiv_of_isWellOrder_rel {r : M → M → Prop} {s : N → N → Prop}
    [IsWellOrder M r]
    (hrel : ∀ (f : L.FGEquiv M N) (x y : f.val.dom), r x y ↔ s (f.val.toEquiv x) (f.val.toEquiv y))
    (h : PotentialIso (L := L) M N) : Nonempty (M ≃[L] N) := by
  obtain ⟨S, hS, hforth, hback⟩ := potentialIso_def.mp h
  exact ⟨(exists_forall_le_equiv_of_isWellOrder_rel hS hforth hback fun f _ => hrel f).choose⟩

/-- Potential isomorphism out of a structure well-ordered by a binary relation symbol yields an
isomorphism, with no cardinality assumption on either structure. -/
theorem PotentialIso.nonempty_equiv_of_isWellOrder (lt : L.Relations 2)
    [IsWellOrder M (fun x y => RelMap lt ![x, y])] (h : PotentialIso (L := L) M N) :
    Nonempty (M ≃[L] N) :=
  h.nonempty_equiv_of_isWellOrder_rel
    (r := fun x y => RelMap lt ![x, y]) (s := fun x y => RelMap lt ![x, y])
    fun f x y => (f.val.map_rel_two lt x y).symm

/-- For a structure well-ordered by a binary relation symbol, potential isomorphism is equivalent
to isomorphism. No cardinality assumption is made on `M` or `N`, and the language is arbitrary. -/
theorem potentialIso_iff_iso_of_isWellOrder (lt : L.Relations 2)
    [IsWellOrder M (fun x y => RelMap lt ![x, y])] :
    PotentialIso (L := L) M N ↔ Nonempty (M ≃[L] N) :=
  ⟨PotentialIso.nonempty_equiv_of_isWellOrder lt, fun ⟨e⟩ => e.potentialIso⟩

/-- Potential isomorphism out of an ordered structure whose order is a well-order yields an
isomorphism, with no order or cardinality assumption on `N`. -/
theorem PotentialIso.nonempty_equiv_of_wellFoundedLT [IsOrdered L] [LinearOrder M]
    [WellFoundedLT M] [L.OrderedStructure M] (h : PotentialIso (L := L) M N) :
    Nonempty (M ≃[L] N) :=
  h.nonempty_equiv_of_isWellOrder_rel
    (r := (· < ·))
    (s := fun x y => RelMap (leSymb (L := L)) ![x, y] ∧ ¬ RelMap (leSymb (L := L)) ![y, x])
    fun f x y => by
      simpa only [lt_iff_le_not_ge, relMap_leSymb, Matrix.cons_val_zero, Matrix.cons_val_one] using
        and_congr (f.val.map_rel_two (leSymb (L := L)) x y).symm
          (not_congr (f.val.map_rel_two (leSymb (L := L)) y x).symm)

/-- For an ordered structure whose order is a well-order, potential isomorphism is equivalent to
isomorphism, with no order or cardinality assumption on `N`. -/
theorem potentialIso_iff_iso_of_wellFoundedLT [IsOrdered L] [LinearOrder M] [WellFoundedLT M]
    [L.OrderedStructure M] : PotentialIso (L := L) M N ↔ Nonempty (M ≃[L] N) :=
  ⟨PotentialIso.nonempty_equiv_of_wellFoundedLT, fun ⟨e⟩ => e.potentialIso⟩

end TauCeti
