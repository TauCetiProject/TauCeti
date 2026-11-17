/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Order
public import TauCeti.ModelTheory.BackAndForth.PotentialIso
import Mathlib.Order.InitialSeg

/-!
# Potential isomorphism of well-ordered structures

Well-ordered structures are rigid: any two isomorphisms out of a structure carrying a well-ordering
preserved by isomorphisms are equal (`FirstOrder.Language.Equiv.subsingleton_of_isWellOrder_rel`).
The same rigidity extends to back-and-forth systems. In any back-and-forth system `S` of finitely
generated partial equivalences out of a well-ordered structure `M`, no two distinct elements of `M`
can be sent to the same element of `N` by members of `S`: otherwise a minimal counterexample on `M`
yields a strictly smaller counterexample by one forth step and one back step. Consequently, all
members of `S` agree on overlaps and assemble into a single global isomorphism `e : M ≃[L] N`
lying above every member of `S` (`TauCeti.exists_forall_le_equiv_of_isWellOrder_rel`).

Therefore potential isomorphism with a well-ordered structure is equivalent to isomorphism, with no
cardinality assumption on either structure and no restriction on the language: function symbols,
nullary relations, empty structures and arbitrary universes are all allowed. This applies both to a
binary relation symbol `lt : L.Relations 2` that well-orders `M`
(`TauCeti.potentialIso_iff_iso_of_isWellOrder`) and to an ordered structure whose underlying order
is a well-order (`TauCeti.potentialIso_iff_iso_of_wellFoundedLT`).

## Main results

* `FirstOrder.Language.Equiv.subsingleton_of_isWellOrder_rel`,
  `FirstOrder.Language.Equiv.subsingleton_of_isWellOrder`,
  `FirstOrder.Language.Equiv.subsingleton_of_wellFoundedLT`: rigidity of well-ordered structures.
* `TauCeti.exists_forall_le_equiv_of_isWellOrder_rel`: every back-and-forth system out of a
  well-ordered structure is simultaneously bounded by a single isomorphism.
* `TauCeti.potentialIso_iff_iso_of_isWellOrder`: for a structure well-ordered by a binary relation
  symbol, potential isomorphism is equivalent to isomorphism.
* `TauCeti.potentialIso_iff_iso_of_wellFoundedLT`: for an ordered structure whose order is a
  well-order, potential isomorphism is equivalent to isomorphism.
-/

public section

universe u v w w'

namespace FirstOrder.Language.Equiv

open Structure

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- If `M` carries a well-ordering preserved by all `L`-isomorphisms into `N`, then there is at
most one isomorphism `M ≃[L] N`. -/
theorem subsingleton_of_isWellOrder_rel {r : M → M → Prop} {s : N → N → Prop}
    [IsWellOrder M r] (hrel : ∀ (e : M ≃[L] N) (x y : M), r x y ↔ s (e x) (e y)) :
    Subsingleton (M ≃[L] N) := by
  refine ⟨fun e₁ e₂ => ?_⟩
  let iso₁ : r ≃r s := ⟨e₁.toEquiv, fun {a b} => (hrel e₁ a b).symm⟩
  let iso₂ : r ≃r s := ⟨e₂.toEquiv, fun {a b} => (hrel e₂ a b).symm⟩
  have : IsWellOrder N s := iso₁.symm.toRelEmbedding.isWellOrder
  ext x
  exact InitialSeg.eq iso₁.toInitialSeg iso₂.toInitialSeg x

/-- If a binary relation symbol well-orders `M`, there is at most one `L`-isomorphism `M ≃[L] N`. -/
theorem subsingleton_of_isWellOrder (lt : L.Relations 2)
    [IsWellOrder M (fun x y => RelMap lt ![x, y])] : Subsingleton (M ≃[L] N) :=
  subsingleton_of_isWellOrder_rel
    (r := fun x y => RelMap lt ![x, y]) (s := fun x y => RelMap lt ![x, y])
    fun e x y => by
      have h : (e ∘ ![x, y]) = ![e x, e y] := funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
      simpa only [h] using (e.map_rel lt ![x, y]).symm

/-- If `M` is an ordered structure whose order is a well-order, there is at most one
`L`-isomorphism `M ≃[L] N`, with no order assumption on `N`. -/
theorem subsingleton_of_wellFoundedLT [IsOrdered L] [LinearOrder M] [WellFoundedLT M]
    [L.OrderedStructure M] : Subsingleton (M ≃[L] N) :=
  subsingleton_of_isWellOrder_rel
    (r := (· < ·))
    (s := fun x y => RelMap (leSymb (L := L)) ![x, y] ∧ ¬ RelMap (leSymb (L := L)) ![y, x])
    fun e x y => by
      have hmap (a b : M) : RelMap (leSymb (L := L)) ![a, b] ↔
          RelMap (leSymb (L := L)) ![e a, e b] := by
        have h : (e ∘ ![a, b]) = ![e a, e b] := funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
        simpa only [h] using (e.map_rel (leSymb (L := L)) ![a, b]).symm
      simpa only [lt_iff_le_not_ge, relMap_leSymb, Matrix.cons_val_zero, Matrix.cons_val_one] using
        and_congr (hmap x y) (not_congr (hmap y x))

end FirstOrder.Language.Equiv

namespace TauCeti

open FirstOrder FirstOrder.Language Structure

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- The pair relation of a family of partial equivalences: some member sends `m` to `n`. -/
private def Pair (S : Set (L.FGEquiv M N)) (m : M) (n : N) : Prop :=
  ∃ f ∈ S, ∃ hm : m ∈ f.1.dom, (f.1.toEquiv ⟨m, hm⟩ : N) = n

private theorem not_pair_of_rel {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.1.dom), r x y ↔ s (f.1.toEquiv x) (f.1.toEquiv y)) :
    ∀ m₁ m₂ n, r m₂ m₁ → Pair S m₁ n → ¬ Pair S m₂ n := by
  intro m₁
  refine WellFounded.induction (inferInstance : IsWellOrder M r).wf
    (C := fun m₁ => ∀ m₂ n, r m₂ m₁ → Pair S m₁ n → ¬ Pair S m₂ n) m₁
    fun m₁ ih m₂ n hm₂₁ h₁ h₂ => ?_
  obtain ⟨f, hf, hm₁, hfn⟩ := h₁
  obtain ⟨g, hg, hm₂, hgn⟩ := h₂
  -- Extend `f` forward to `m₂`, obtaining an image `y` strictly `s`-below `n`.
  obtain ⟨f', hf', hm₂', hff'⟩ := hforth f hf m₂
  have hm₁' : m₁ ∈ f'.1.dom := PartialEquiv.dom_le_dom hff' hm₁
  have hf'n : (f'.1.toEquiv ⟨m₁, hm₁'⟩ : N) = n :=
    (PartialEquiv.toEquiv_apply_of_le hff' hm₁).trans hfn
  set y : N := (f'.1.toEquiv ⟨m₂, hm₂'⟩ : N)
  have hsy : s y n := hf'n ▸ (hrel f' hf' ⟨m₂, hm₂'⟩ ⟨m₁, hm₁'⟩).mp hm₂₁
  -- Extend `g` backward to `y`, pulling `y` back to `m₃` strictly `r`-below `m₂`.
  obtain ⟨g', hg', hy', hgg'⟩ := hback g hg y
  have hm₂g : m₂ ∈ g'.1.dom := PartialEquiv.dom_le_dom hgg' hm₂
  have hg'n : (g'.1.toEquiv ⟨m₂, hm₂g⟩ : N) = n :=
    (PartialEquiv.toEquiv_apply_of_le hgg' hm₂).trans hgn
  set m₃ : g'.1.dom := g'.1.toEquiv.symm ⟨y, hy'⟩
  have hg'm₃ : (g'.1.toEquiv m₃ : N) = y := by simp [m₃]
  have hm₃₂ : r m₃ m₂ := (hrel g' hg' m₃ ⟨m₂, hm₂g⟩).mpr (by rw [hg'm₃, hg'n]; exact hsy)
  exact ih m₂ hm₂₁ m₃ y hm₃₂ ⟨f', hf', hm₂', rfl⟩ ⟨g', hg', m₃.2, hg'm₃⟩

private theorem pair_left_unique {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.1.dom), r x y ↔ s (f.1.toEquiv x) (f.1.toEquiv y))
    {m₁ m₂ : M} {n : N} (h₁ : Pair S m₁ n) (h₂ : Pair S m₂ n) : m₁ = m₂ := by
  rcases trichotomous_of r m₁ m₂ with hlt | rfl | hgt
  · exact (not_pair_of_rel hforth hback hrel m₂ m₁ n hlt h₂ h₁).elim
  · rfl
  · exact (not_pair_of_rel hforth hback hrel m₁ m₂ n hgt h₁ h₂).elim

private theorem pair_right_unique {S : Set (L.FGEquiv M N)}
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.1.dom), r x y ↔ s (f.1.toEquiv x) (f.1.toEquiv y))
    {m : M} {n₁ n₂ : N} (h₁ : Pair S m n₁) (h₂ : Pair S m n₂) : n₁ = n₂ := by
  obtain ⟨f, hf, hm, hfn₁⟩ := h₁
  obtain ⟨f', hf', hn₂, hff'⟩ := hback f hf n₂
  set m' : f'.1.dom := f'.1.toEquiv.symm ⟨n₂, hn₂⟩
  have hm'n₂ : (f'.1.toEquiv m' : N) = n₂ := by simp [m']
  have heq : (m' : M) = m :=
    pair_left_unique hforth hback hrel ⟨f', hf', m'.2, hm'n₂⟩ h₂
  have hm' : m ∈ f'.1.dom := PartialEquiv.dom_le_dom hff' hm
  have hfn₁' : (f'.1.toEquiv ⟨m, hm'⟩ : N) = n₁ :=
    (PartialEquiv.toEquiv_apply_of_le hff' hm).trans hfn₁
  calc n₁ = (f'.1.toEquiv ⟨m, hm'⟩ : N) := hfn₁'.symm
    _ = (f'.1.toEquiv m' : N) := congrArg (fun x : f'.1.dom => (f'.1.toEquiv x : N))
        (Subtype.ext heq.symm)
    _ = n₂ := hm'n₂

/-- Every back-and-forth system of finitely generated partial equivalences out of a well-ordered
structure is simultaneously bounded by a single isomorphism. No cardinality assumption is made on
`M` or `N`, and the language is arbitrary. -/
theorem exists_forall_le_equiv_of_isWellOrder_rel {S : Set (L.FGEquiv M N)} (hS : S.Nonempty)
    (hforth : ∀ f ∈ S, ∀ m : M, ∃ g ∈ S, m ∈ g.1.dom ∧ f ≤ g)
    (hback : ∀ f ∈ S, ∀ n : N, ∃ g ∈ S, n ∈ g.1.cod ∧ f ≤ g)
    {r : M → M → Prop} {s : N → N → Prop} [IsWellOrder M r]
    (hrel : ∀ f ∈ S, ∀ (x y : f.1.dom), r x y ↔ s (f.1.toEquiv x) (f.1.toEquiv y)) :
    ∃ e : M ≃[L] N, ∀ f ∈ S, f.1 ≤ e.toEmbedding.toPartialEquiv := by
  classical
  obtain ⟨f₀, hf₀⟩ := hS
  have htotal : ∀ m : M, ∃ n : N, Pair S m n := fun m => by
    obtain ⟨f, hf, hm, -⟩ := hforth f₀ hf₀ m
    exact ⟨f.1.toEquiv ⟨m, hm⟩, f, hf, hm, rfl⟩
  choose toFun htoFun using htotal
  have hagree : ∀ f ∈ S, ∀ x : f.1.dom, (f.1.toEquiv x : N) = toFun x := fun f hf x =>
    pair_right_unique hforth hback hrel ⟨f, hf, x.2, rfl⟩ (htoFun x)
  have hbij : Function.Bijective toFun := by
    refine ⟨fun m₁ m₂ h => pair_left_unique hforth hback hrel (htoFun m₁) (h ▸ htoFun m₂),
      fun n => ?_⟩
    obtain ⟨f, hf, hn, -⟩ := hback f₀ hf₀ n
    let m : f.1.dom := f.1.toEquiv.symm ⟨n, hn⟩
    exact ⟨m, (hagree f hf m).symm.trans (by simp [m])⟩
  -- For any finite tuple in `M`, some member of `S` covers the substructure it generates.
  have hcover : ∀ {k : ℕ} (a : Fin k → M),
      ∃ f ∈ S, Substructure.closure L (Set.range a) ≤ f.1.dom := fun a => by
    have hfg : (Substructure.closure L (Set.range a)).FG :=
      ⟨Finset.univ.image a, by simp⟩
    obtain ⟨f, hf, hle, -⟩ := FGEquiv.exists_le_and_le_dom_of_fg hforth hf₀ hfg
    exact ⟨f, hf, hle⟩
  let e : M ≃[L] N :=
    { toEquiv := _root_.Equiv.ofBijective toFun hbij
      map_fun' := fun {k} fn a => by
        obtain ⟨f, hf, hle⟩ := hcover a
        have ha : ∀ i, a i ∈ f.1.dom := fun i =>
          hle (Substructure.subset_closure (Set.mem_range_self i))
        have hfa : funMap fn a ∈ f.1.dom := f.1.dom.fun_mem fn _ ha
        have harg : (fun i => (f.1.toEquiv ⟨a i, ha i⟩ : N)) = toFun ∘ a :=
          funext fun i => hagree f hf ⟨a i, ha i⟩
        calc toFun (funMap fn a)
            = (f.1.toEquiv ⟨funMap fn a, hfa⟩ : N) := (hagree f hf ⟨_, hfa⟩).symm
          _ = (f.1.toEquiv (funMap fn fun i => ⟨a i, ha i⟩) : N) := rfl
          _ = funMap fn fun i => (f.1.toEquiv ⟨a i, ha i⟩ : N) := by
              rw [f.1.toEquiv.map_fun]; rfl
          _ = funMap fn (toFun ∘ a) := by rw [harg]
      map_rel' := fun {k} R a => by
        obtain ⟨f, hf, hle⟩ := hcover a
        have ha : ∀ i, a i ∈ f.1.dom := fun i =>
          hle (Substructure.subset_closure (Set.mem_range_self i))
        have harg : (fun i => (f.1.toEquiv ⟨a i, ha i⟩ : N)) = toFun ∘ a :=
          funext fun i => hagree f hf ⟨a i, ha i⟩
        have hmap : RelMap R (fun i => (f.1.toEquiv ⟨a i, ha i⟩ : N)) ↔ RelMap R a :=
          f.1.toEquiv.map_rel R fun i => ⟨a i, ha i⟩
        exact harg ▸ hmap }
  refine ⟨e, fun f hf => (PartialEquiv.le_def _ _).2 ⟨le_top, ?_⟩⟩
  ext ⟨x, hx⟩
  exact (hagree f hf ⟨x, hx⟩).symm

/-- Potential isomorphism out of a structure carrying a well-ordering preserved by all finitely
generated partial equivalences yields an isomorphism, with no cardinality assumption on either
structure. -/
theorem PotentialIso.nonempty_equiv_of_isWellOrder_rel {r : M → M → Prop} {s : N → N → Prop}
    [IsWellOrder M r]
    (hrel : ∀ (f : L.FGEquiv M N) (x y : f.1.dom), r x y ↔ s (f.1.toEquiv x) (f.1.toEquiv y))
    (h : PotentialIso (L := L) M N) : Nonempty (M ≃[L] N) := by
  obtain ⟨S, hS, hforth, hback⟩ := potentialIso_def.mp h
  exact ⟨(exists_forall_le_equiv_of_isWellOrder_rel hS hforth hback fun f _ => hrel f).choose⟩

private theorem fgEquiv_map_rel_finTwo (f : L.FGEquiv M N) (R : L.Relations 2) (x y : f.1.dom) :
    RelMap R ![x.1, y.1] ↔ RelMap R ![(f.1.toEquiv x : N), f.1.toEquiv y] := by
  have hmap : RelMap R (fun i => (f.1.toEquiv (![x, y] i) : N)) ↔
      RelMap R (fun i => ((![x, y] i : f.1.dom) : M)) :=
    f.1.toEquiv.map_rel R ![x, y]
  have h1 : (fun i => (f.1.toEquiv (![x, y] i) : N)) = ![(f.1.toEquiv x : N), f.1.toEquiv y] :=
    funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  have h2 : (fun i => ((![x, y] i : f.1.dom) : M)) = ![x.1, y.1] :=
    funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  rw [h1, h2] at hmap
  exact hmap.symm

/-- Potential isomorphism out of a structure well-ordered by a binary relation symbol yields an
isomorphism, with no cardinality assumption on either structure. -/
theorem PotentialIso.nonempty_equiv_of_isWellOrder (lt : L.Relations 2)
    [IsWellOrder M (fun x y => RelMap lt ![x, y])] (h : PotentialIso (L := L) M N) :
    Nonempty (M ≃[L] N) :=
  h.nonempty_equiv_of_isWellOrder_rel
    (r := fun x y => RelMap lt ![x, y]) (s := fun x y => RelMap lt ![x, y])
    fun f x y => fgEquiv_map_rel_finTwo f lt x y

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
        and_congr (fgEquiv_map_rel_finTwo f (leSymb (L := L)) x y)
          (not_congr (fgEquiv_map_rel_finTwo f (leSymb (L := L)) y x))

/-- For an ordered structure whose order is a well-order, potential isomorphism is equivalent to
isomorphism, with no order or cardinality assumption on `N`. -/
theorem potentialIso_iff_iso_of_wellFoundedLT [IsOrdered L] [LinearOrder M] [WellFoundedLT M]
    [L.OrderedStructure M] : PotentialIso (L := L) M N ↔ Nonempty (M ≃[L] N) :=
  ⟨PotentialIso.nonempty_equiv_of_wellFoundedLT, fun ⟨e⟩ => e.potentialIso⟩

end TauCeti
