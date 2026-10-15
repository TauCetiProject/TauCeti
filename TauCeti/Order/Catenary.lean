/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension

/-!
# Catenary orders

A preorder is *catenary* when, between any two of its elements, strict chains have bounded length
and all saturated chains (chains whose consecutive members are covering pairs) have the same
length. Applied to the prime spectrum of a commutative ring this is the notion of a catenary ring
(Stacks, Definition 10.105.1 (00NI)); applied to the specialization order of a sober topological
space it is the notion of a catenary space (Stacks, Definition 5.11.4 (02I1)). Every property used
to transport catenarity between rings is order-theoretic, so it is developed here for preorders.

Saturated chains are Mathlib's `RelSeries {(a, b) : α × α | a ⋖ b}`, the target of
`LTSeries.exists_relSeries_covBy`, and strict chains are `LTSeries α`.

## Main definitions and results

* `TauCeti.Order.IsCatenary α`: strict chains between two fixed elements have bounded length, and
  saturated chains with the same endpoints have the same length.
* `OrderEmbedding.isCatenary`: catenarity passes along an order embedding whose
  range is order-connected; in particular to order-connected subsets and along order
  isomorphisms.
* `TauCeti.Order.IsCatenary.of_forall_exists_ordConnected`: a preorder is catenary as soon as any
  two comparable elements lie in a common catenary order-connected subset.
* An order of Krull dimension at most one is catenary.
-/

public section

namespace TauCeti.Order

variable {α β : Type*} [Preorder α] [Preorder β]

/-- A preorder is *catenary* if, for any two elements `a` and `b`, the lengths of the strict chains
`a = a₀ < a₁ < ⋯ < aₙ = b` are bounded, and any two saturated chains from `a` to `b`, that is
chains `a = a₀ ⋖ a₁ ⋖ ⋯ ⋖ aₙ = b` of covering pairs, have the same length. Both conditions are
vacuous unless `a ≤ b`. For the prime spectrum of a ring this is Stacks, Definition 10.105.1
(00NI). -/
class IsCatenary (α : Type*) [Preorder α] : Prop where
  /-- The strict chains between two fixed elements have bounded length. -/
  exists_length_le (a b : α) :
    ∃ n : ℕ, ∀ s : LTSeries α, s.head = a → s.last = b → s.length ≤ n
  /-- Two saturated chains with the same endpoints have the same length. -/
  length_eq_of_covBy {s t : RelSeries {(x, y) : α × α | x ⋖ y}} :
    s.head = t.head → s.last = t.last → s.length = t.length

end TauCeti.Order

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

/-- Catenarity passes along an order embedding with order-connected range: strict and saturated
chains of `α` map to strict and saturated chains of `β` with the same length. -/
theorem isCatenary [TauCeti.Order.IsCatenary β] (f : α ↪o β)
    (hf : (Set.range f).OrdConnected) : TauCeti.Order.IsCatenary α where
  exists_length_le a b := by
    obtain ⟨n, hn⟩ := TauCeti.Order.IsCatenary.exists_length_le (f a) (f b)
    exact ⟨n, fun s hsa hsb => hn (s.map f f.strictMono) (by simp [hsa]) (by simp [hsb])⟩
  length_eq_of_covBy {s t} hst hst' := by
    let g : SetRel.Hom {(x, y) : α × α | x ⋖ y} {(x, y) : β × β | x ⋖ y} :=
      ⟨f, fun h => CovBy.image f h hf⟩
    exact TauCeti.Order.IsCatenary.length_eq_of_covBy
      (s := s.map g) (t := t.map g) (by simp [g, hst]) (by simp [g, hst'])

end OrderEmbedding

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

/-- Catenarity is invariant under order isomorphism. -/
theorem isCatenary [TauCeti.Order.IsCatenary β] (e : α ≃o β) : TauCeti.Order.IsCatenary α :=
  e.toOrderEmbedding.isCatenary (by simpa using Set.ordConnected_univ)

end OrderIso

namespace Set

variable {α : Type*} [Preorder α]

/-- An order-connected subset of a catenary preorder is catenary. -/
instance isCatenary [TauCeti.Order.IsCatenary α] (S : Set α) [S.OrdConnected] :
    TauCeti.Order.IsCatenary S :=
  (OrderEmbedding.subtype _).isCatenary (by simpa)

end Set


namespace TauCeti.Order.IsCatenary

variable {α : Type*} [Preorder α]

/-- Catenarity is local: a preorder is catenary as soon as any two elements `a ≤ b` lie in a common
catenary order-connected subset. Every chain from `a` to `b` lies in such a subset, and covering
pairs there are covering pairs of `α`. -/
theorem of_forall_exists_ordConnected
    (h : ∀ a b : α, a ≤ b → ∃ S : Set α, S.OrdConnected ∧ a ∈ S ∧ b ∈ S ∧ IsCatenary S) :
    IsCatenary α := by
  -- The entries of a strict or saturated chain from `a` to `b` lie in every order-connected set
  -- containing `a` and `b`.
  have hmem {S : Set α} (hS : S.OrdConnected) {u : LTSeries α} (ha : u.head ∈ S)
      (hb : u.last ∈ S) (i) : u i ∈ S :=
    hS.out ha hb ⟨u.monotone (Fin.zero_le i), u.monotone (Fin.le_last i)⟩
  let toLT (u : RelSeries {(x, y) : α × α | x ⋖ y}) : LTSeries α := u.map ⟨id, fun h => CovBy.lt h⟩
  refine ⟨fun a b => ?_, fun {s t} hst hst' => ?_⟩
  · by_cases hab : a ≤ b
    · obtain ⟨S, hS, ha, hb, hcat⟩ := h a b hab
      obtain ⟨n, hn⟩ := hcat.exists_length_le ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨n, fun u hua hub => hn ⟨u.length, fun i => ⟨u i, ?_⟩, u.step⟩
        (Subtype.ext hua) (Subtype.ext hub)⟩
      exact hmem hS (hua ▸ ha) (hub ▸ hb) i
    · exact ⟨0, fun u hua hub => (hab (hua ▸ hub ▸ u.head_le_last)).elim⟩
  · obtain ⟨S, hS, ha, hb, hcat⟩ := h s.head s.last (toLT s).head_le_last
    -- Restrict a saturated chain from `s.head` to `s.last` to `S`.
    let res (u : RelSeries {(x, y) : α × α | x ⋖ y}) (hua : u.head = s.head)
        (hub : u.last = s.last) : RelSeries {(x, y) : S × S | x ⋖ y} :=
      ⟨u.length, fun i => ⟨u i, hmem (u := toLT u) hS (hua ▸ ha) (hub ▸ hb) i⟩, fun i =>
        (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype (· ∈ S))
          (by rwa [OrderEmbedding.coe_subtype, Subtype.range_coe])).1 (u.step i)⟩
    exact hcat.length_eq_of_covBy (s := res s rfl rfl) (t := res t hst.symm hst'.symm)
      (Subtype.ext hst) (Subtype.ext hst')

/-- A preorder of Krull dimension at most one is catenary: strict chains have length at most one,
and a chain of length zero and one of length one cannot share both endpoints. -/
instance of_krullDimLE_one [Order.KrullDimLE 1 α] : IsCatenary α :=
  have hlen (s : LTSeries α) : s.length ≤ 1 := by
    have := (Order.LTSeries.length_le_krullDim s).trans (Order.KrullDimLE.krullDim_le (n := 1))
    exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp this)
  { exists_length_le _ _ := ⟨1, fun s _ _ => hlen s⟩
    length_eq_of_covBy {s t} hst hst' := by
      let toLT (u : RelSeries {(x, y) : α × α | x ⋖ y}) : LTSeries α :=
        u.map ⟨id, fun h => CovBy.lt h⟩
      -- A saturated chain has length zero exactly when its endpoints agree.
      have hzero (u : RelSeries {(x, y) : α × α | x ⋖ y}) : u.length = 0 ↔ u.head = u.last := by
        refine ⟨fun h => congrArg u (Fin.ext (by simp [h])), fun h => ?_⟩
        simpa [Fin.ext_iff, eq_comm] using congrArg Fin.val ((toLT u).strictMono.injective h)
      have h0 : s.length = 0 ↔ t.length = 0 := by rw [hzero, hzero, hst, hst']
      have h1 := hlen (toLT s)
      have h2 := hlen (toLT t)
      simp only [toLT, RelSeries.map_length] at h1 h2
      omega }

end TauCeti.Order.IsCatenary
