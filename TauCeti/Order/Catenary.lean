/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension

import Mathlib.Data.Nat.Cast.Order.Basic

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
* `TauCeti.Order.IsCatenary.krullDim_Icc_eq_length`: in a catenary partial order every saturated
  chain from `a` to `b` has length the Krull dimension of the interval `[a, b]`.
* `TauCeti.Order.krullDim_Icc_eq_length_of_add`: the same conclusion in any partial order where
  Krull dimension is additive on intervals.
* `TauCeti.Order.isCatenary_iff_krullDim_Icc_add`: a partial order is catenary if and only if its
  intervals have finite Krull dimension and Krull dimension is additive on intervals,
  `dim [a, c] = dim [a, b] + dim [b, c]` for `a ≤ b ≤ c`. This is the form in which catenarity is
  usually verified, for instance through a dimension formula.
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

namespace CovBy

variable {α : Type*} [PartialOrder α] {a b : α}

/-- The interval between the two members of a covering pair has Krull dimension one. -/
theorem krullDim_Icc (hab : a ⋖ b) : Order.krullDim (Set.Icc a b) = 1 := by
  refine le_antisymm (Order.krullDim_le_one_iff.2 fun x => ?_) (Order.one_le_krullDim_iff.2
    ⟨⟨a, Set.left_mem_Icc.2 hab.le⟩, ⟨b, Set.right_mem_Icc.2 hab.le⟩, hab.lt⟩)
  rcases hab.eq_or_eq x.2.1 x.2.2 with hx | hx
  · exact Or.inl fun y _ => by rw [← Subtype.coe_le_coe, hx]; exact y.2.1
  · exact Or.inr fun y _ => by rw [← Subtype.coe_le_coe, hx]; exact y.2.2

end CovBy

namespace TauCeti.Order.IsCatenary

open _root_.Order

variable {α : Type*} [PartialOrder α] [IsCatenary α]

/-- In a catenary partial order, a strict chain of greatest length between two comparable
elements is saturated. -/
private theorem exists_covBy_series_forall_length_le {a b : α} (hab : a ≤ b) :
    ∃ s : RelSeries {(x, y) : α × α | x ⋖ y}, s.head = a ∧ s.last = b ∧
      ∀ t : LTSeries α, t.head = a → t.last = b → t.length ≤ s.length := by
  classical
  obtain ⟨N, hN⟩ := exists_length_le a b
  let P (n : ℕ) : Prop := ∃ t : LTSeries α, t.head = a ∧ t.last = b ∧ t.length = n
  obtain ⟨t₀, ht₀a, ht₀b⟩ : ∃ t : LTSeries α, t.head = a ∧ t.last = b := by
    rcases hab.eq_or_lt with rfl | h
    · exact ⟨RelSeries.singleton _ a, rfl, rfl⟩
    · exact ⟨(RelSeries.singleton _ a).snoc b (by simpa using h), by simp, by simp⟩
  -- A strict chain from `a` to `b` of the greatest possible length.
  obtain ⟨t, hta, htb, htm⟩ : P (Nat.findGreatest P N) :=
    Nat.findGreatest_spec (hN t₀ ht₀a ht₀b) ⟨t₀, ht₀a, ht₀b, rfl⟩
  have hmax (u : LTSeries α) (hua : u.head = a) (hub : u.last = b) : u.length ≤ t.length :=
    htm ▸ Nat.le_findGreatest (hN u hua hub) ⟨u, hua, hub, rfl⟩
  refine ⟨⟨t.length, t, fun i => ?_⟩, hta, htb, hmax⟩
  -- If a step of `t` were not a covering, inserting an intermediate element would lengthen `t`.
  by_contra hi
  obtain ⟨c, h₁, h₂⟩ := (not_covBy_iff (t.step i)).1 hi
  let u : LTSeries α := ((t.take i.castSucc).snoc c (by simpa using h₁)).append (t.drop i.succ)
    (by simpa using h₂)
  have := hmax u (by simp [u, hta]) (by simp [u, htb])
  simp [u] at this

/-- In a catenary partial order, any two comparable elements are joined by a saturated chain. -/
theorem exists_covBy_series {a b : α} (hab : a ≤ b) :
    ∃ s : RelSeries {(x, y) : α × α | x ⋖ y}, s.head = a ∧ s.last = b :=
  let ⟨s, hsa, hsb, _⟩ := exists_covBy_series_forall_length_le hab
  ⟨s, hsa, hsb⟩

/-- In a catenary partial order, a saturated chain is at least as long as every strict chain
lying between its endpoints. -/
theorem length_le_of_covBy (s : RelSeries {(x, y) : α × α | x ⋖ y}) (t : LTSeries α)
    (hhead : s.head ≤ t.head) (hlast : t.last ≤ s.last) : t.length ≤ s.length := by
  -- Extend `t` to a strict chain `u` from `s.head` to `s.last`.
  obtain ⟨u, hua, hub, htu⟩ : ∃ u : LTSeries α, u.head = s.head ∧ u.last = s.last ∧
      t.length ≤ u.length := by
    obtain ⟨u, hu₁, hu₂, hu₃⟩ : ∃ u : LTSeries α, u.head = s.head ∧ u.last = t.last ∧
        t.length ≤ u.length := by
      rcases hhead.eq_or_lt with h | h
      · exact ⟨t, h.symm, rfl, le_rfl⟩
      · exact ⟨t.cons s.head h, by simp, by simp, by simp⟩
    rcases hlast.eq_or_lt with h | h
    · exact ⟨u, hu₁, hu₂.trans h, hu₃⟩
    · exact ⟨u.snoc s.last (hu₂ ▸ h), by simp [hu₁], by simp, by simp; omega⟩
  obtain ⟨s', hs'a, hs'b, hs'⟩ :=
    exists_covBy_series_forall_length_le (hhead.trans (t.head_le_last.trans hlast))
  exact htu.trans ((hs' u hua hub).trans (length_eq_of_covBy hs'a hs'b).le)

/-- In a catenary partial order, the interval between the endpoints of a saturated chain has
Krull dimension the length of the chain. -/
theorem krullDim_Icc_eq_length (s : RelSeries {(x, y) : α × α | x ⋖ y}) :
    krullDim (Set.Icc s.head s.last) = s.length := by
  refine le_antisymm (iSup_le fun u => ?_) ?_
  · have := length_le_of_covBy s (u.map Subtype.val (Subtype.strictMono_coe _)) u.head.2.1
      u.last.2.2
    rw [LTSeries.map_length] at this
    exact_mod_cast this
  · let t : LTSeries α := s.map ⟨id, fun h => CovBy.lt h⟩
    exact LTSeries.length_le_krullDim
      ⟨t.length, fun i => ⟨t i, t.head_le i, t.monotone (Fin.le_last i)⟩, fun i => t.step i⟩

end TauCeti.Order.IsCatenary

namespace TauCeti.Order

open _root_.Order IsCatenary

variable {α : Type*} [PartialOrder α]

/-- If Krull dimension is additive on intervals, then the interval between the endpoints of a
saturated chain has Krull dimension the length of the chain: additivity computes it one covering
pair at a time. -/
theorem krullDim_Icc_eq_length_of_add
    (hadd : ∀ a b c : α, a ≤ b → b ≤ c →
      krullDim (Set.Icc a c) = krullDim (Set.Icc a b) + krullDim (Set.Icc b c))
    (s : RelSeries {(x, y) : α × α | x ⋖ y}) : krullDim (Set.Icc s.head s.last) = s.length := by
  induction hs : s.length generalizing s with
  | zero =>
    rw [show s.last = s.head from congrArg s (Fin.ext (by simp [hs]))]
    have := (Set.subsingleton_Icc_of_ge (le_refl s.head)).coe_sort
    have : Nonempty (Set.Icc s.head s.head) := ⟨⟨s.head, le_rfl, le_rfl⟩⟩
    exact_mod_cast krullDim_eq_zero
  | succ n ih =>
    have hpos : s.length ≠ 0 := by omega
    -- Split off the first covering pair `s.head ⋖ s 1` of `s`.
    have h01 : s.head ⋖ (s.tail hpos).head := by
      have h := s.step ⟨0, Nat.pos_of_ne_zero hpos⟩
      have e : (Fin.succ ⟨0, Nat.pos_of_ne_zero hpos⟩ : Fin (s.length + 1)) = 1 :=
        Fin.ext (by simp [Nat.mod_eq_of_lt (show 1 < s.length + 1 by omega)])
      rw [e] at h
      rw [RelSeries.head_tail]
      exact h
    have hle : (s.tail hpos).head ≤ (s.tail hpos).last :=
      LTSeries.head_le_last ((s.tail hpos).map ⟨id, fun h => CovBy.lt h⟩)
    rw [← RelSeries.last_tail s hpos, hadd _ _ _ h01.le hle, h01.krullDim_Icc,
      ih _ (by simp [hs])]
    push_cast
    exact add_comm _ _

/-- A partial order is catenary if and only if every interval `[a, b]` has finite Krull dimension
and Krull dimension is additive on intervals: `dim [a, c] = dim [a, b] + dim [b, c]` whenever
`a ≤ b ≤ c`. For the specialization order of a topological space this is the characterisation of
catenary spaces by additivity of codimension (Stacks, Lemma 5.11.6 (02I6)). -/
theorem isCatenary_iff_krullDim_Icc_add :
    IsCatenary α ↔ (∀ a b : α, a ≤ b → krullDim (Set.Icc a b) ≠ ⊤) ∧
      ∀ a b c : α, a ≤ b → b ≤ c →
        krullDim (Set.Icc a c) = krullDim (Set.Icc a b) + krullDim (Set.Icc b c) := by
  refine ⟨fun _ => ⟨fun a b hab => ?_, fun a b c hab hbc => ?_⟩, fun ⟨hfin, hadd⟩ => ?_⟩
  · obtain ⟨s, rfl, rfl⟩ := exists_covBy_series hab
    rw [krullDim_Icc_eq_length, ← WithBot.coe_top, ← WithBot.coe_natCast, Ne, WithBot.coe_inj]
    exact ENat.natCast_ne_top _
  · -- Concatenate saturated chains from `a` to `b` and from `b` to `c`.
    obtain ⟨s, rfl, rfl⟩ := exists_covBy_series hab
    obtain ⟨t, hts, rfl⟩ := exists_covBy_series hbc
    have hst := krullDim_Icc_eq_length (s.smash t hts.symm)
    have ht := krullDim_Icc_eq_length t
    rw [RelSeries.head_smash, RelSeries.last_smash] at hst
    rw [hts] at ht
    rw [hst, krullDim_Icc_eq_length, ht]
    exact_mod_cast rfl
  refine ⟨fun a b => ?_, fun {s t} hst hst' => ?_⟩
  · by_cases hab : a ≤ b
    · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1
        (krullDim_ne_bot_iff.2 ⟨⟨a, le_rfl, hab⟩⟩ : krullDim (Set.Icc a b) ≠ ⊥)
      obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1
        (fun h => hfin a b hab (by rw [← hd, h]; rfl) : d ≠ ⊤)
      refine ⟨n, fun t hta htb => ?_⟩
      subst hta htb
      have := LTSeries.length_le_krullDim
        ⟨t.length, fun i => (⟨t i, t.head_le i, t.monotone (Fin.le_last i)⟩ :
          Set.Icc t.head t.last), fun i => t.step i⟩
      rw [← hd] at this
      exact_mod_cast this
    · exact ⟨0, fun t hta htb => (hab (hta ▸ htb ▸ t.head_le_last)).elim⟩
  · have := krullDim_Icc_eq_length_of_add hadd s
    rw [hst, hst', krullDim_Icc_eq_length_of_add hadd t] at this
    exact_mod_cast this.symm

end TauCeti.Order
