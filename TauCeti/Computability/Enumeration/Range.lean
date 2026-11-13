/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Domain
import Mathlib.Data.Set.Finite.Basic

/-!
# Total and injective enumerations of c.e. sets

A nonempty c.e. set is the range of a total computable function. The enumeration
runs bounded computations in dovetailed order and uses a fixed member of the set
when a computation has not yet halted. No total range presentation is possible
for the empty set.

For an infinite range, repetitions can be removed effectively: keep the finite
list of previous outputs and search for the least input with a fresh value.
This gives an injective total computable enumeration of every infinite c.e. set.
The infinite-range premise supplies termination of each search, not a decision
procedure for membership in the limiting set.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987,
  Chapter II.1.
-/

public section

namespace REPred

/-- A nonempty c.e. set has a total computable range presentation. -/
theorem exists_computable_range {α : Type*} [Primcodable α] {S : Set α}
    (hS : REPred (· ∈ S)) (hne : S.Nonempty) :
    ∃ f : ℕ → α, Computable f ∧ Set.range f = S := by
  obtain ⟨a, ha⟩ := hne
  let d : ℕ → α := fun n => (Encodable.decode n).getD a
  have hd : Computable d := Computable.decode.option_getD (Computable.const a)
  have hpre : REPred fun n => d n ∈ S := Partrec.comp hS hd
  obtain ⟨c, hc⟩ := TauCeti.Enumeration.rePred_iff_exists_code.mp hpre
  let f : ℕ → α := fun n =>
    if (Nat.Partrec.Code.evaln n.unpair.2 c n.unpair.1).isSome then d n.unpair.1 else a
  have heval : Computable fun n : ℕ => Nat.Partrec.Code.evaln n.unpair.2 c n.unpair.1 :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (((Computable.snd.comp Computable.unpair).pair (Computable.const c)).pair
        (Computable.fst.comp Computable.unpair))
  have hf : Computable f := by
    simpa only [f, Bool.cond_eq_ite] using (Primrec.option_isSome.to_comp.comp heval).cond
      (hd.comp (Computable.fst.comp Computable.unpair)) (Computable.const a)
  refine ⟨f, hf, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨n, rfl⟩
    dsimp [f]
    split_ifs with h
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
      exact (hc _).mpr (Nat.Partrec.Code.evaln_sound hy).fst
    · exact ha
  · intro x hx
    obtain ⟨n, rfl⟩ := Encodable.surjective_decode_getD α a x
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp ((hc n).mp hx)
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hy
    refine ⟨Nat.pair n s, ?_⟩
    simp [f, Nat.unpair_pair, Option.isSome_iff_exists.mpr ⟨y, hs⟩, d]

end REPred

namespace TauCeti.Enumeration

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
private theorem exists_fresh_input {f : ℕ → α} (h : (Set.range f).Infinite)
    (l : List α) : ∃ n, f n ∉ l := by
  classical
  obtain ⟨x, ⟨n, rfl⟩, hn⟩ := h.exists_notMem_finset l.toFinset
  exact ⟨n, by simpa using hn⟩

private def freshIndex (f : ℕ → α) (h : (Set.range f).Infinite) (l : List α) : ℕ :=
  Nat.find (exists_fresh_input h l)

private theorem freshIndex_spec {f : ℕ → α} (h : (Set.range f).Infinite) (l : List α) :
    f (freshIndex f h l) ∉ l := Nat.find_spec (exists_fresh_input h l)

private theorem freshIndex_le {f : ℕ → α} (h : (Set.range f).Infinite) (l : List α)
    {t : ℕ} (ht : f t ∉ l) : freshIndex f h l ≤ t := Nat.find_min' _ ht

private theorem computable_freshIndex [Primcodable α] {f : ℕ → α} (hf : Computable f)
    (h : (Set.range f).Infinite) : Computable (freshIndex f h) := by
  have hmem : PrimrecRel fun (l : List α) x => x ∈ l :=
    Primrec.eq.exists_mem_list.of_eq fun l x => by simp
  exact Computable.find
    ((hmem.decide.to_comp.comp Computable.fst (hf.comp Computable.snd)).computablePred.not)
    (exists_fresh_input h)

private def freshHistory (f : ℕ → α) (h : (Set.range f).Infinite) : ℕ → List α
  | 0 => []
  | n + 1 => f (freshIndex f h (freshHistory f h n)) :: freshHistory f h n

private theorem computable_freshHistory [Primcodable α] {f : ℕ → α} (hf : Computable f)
    (h : (Set.range f).Infinite) : Computable (freshHistory f h) := by
  have hstep : Computable fun l => f (freshIndex f h l) :: l :=
    Computable.list_cons.comp (hf.comp (computable_freshIndex hf h)) Computable.id
  exact (Computable.nat_rec Computable.id (Computable.const [])
    (hstep.comp (Computable.snd.comp Computable.snd)).to₂).of_eq fun n => by
      induction n with
      | zero => rfl
      | succ n ih => simpa [freshHistory] using congrArg (fun l => f (freshIndex f h l) :: l) ih

private theorem mem_freshHistory {f : ℕ → α} (h : (Set.range f).Infinite) (n : ℕ) (x : α) :
    x ∈ freshHistory f h n ↔ ∃ k < n, f (freshIndex f h (freshHistory f h k)) = x := by
  induction n with
  | zero => simp [freshHistory]
  | succ n ih =>
    simp only [freshHistory, List.mem_cons, ih, Nat.lt_succ_iff_lt_or_eq,
      or_and_right, exists_or, exists_eq_left]
    grind

private theorem exists_injective_range_nat {α : Type*} [Primcodable α] {f : ℕ → α}
    (hf : Computable f) (h : (Set.range f).Infinite) :
    ∃ g : ℕ → α, Computable g ∧ Function.Injective g ∧ Set.range g = Set.range f := by
  classical
  let g := fun n => f (freshIndex f h (freshHistory f h n))
  have hg : Computable g := hf.comp
    ((computable_freshIndex hf h).comp (computable_freshHistory hf h))
  have hfresh (n) : g n ∉ freshHistory f h n := freshIndex_spec h _
  have hmem (n x) : x ∈ freshHistory f h n ↔ ∃ k < n, g k = x := mem_freshHistory h n x
  have hinj : Function.Injective g := by
    intro m n heq
    rcases lt_trichotomy m n with hlt | rfl | hlt
    · exact False.elim (hfresh n ((hmem n (g n)).mpr ⟨m, hlt, heq⟩))
    · rfl
    · exact False.elim (hfresh m ((hmem m (g m)).mpr ⟨n, hlt, heq.symm⟩))
  refine ⟨g, hg, hinj, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨n, rfl⟩
    exact ⟨_, rfl⟩
  · rintro x ⟨t, rfl⟩
    by_contra hx
    -- A permanently omitted value bounds every least fresh input, forcing the
    -- injective enumeration into the finite image of an initial segment.
    have hbound (n) : freshIndex f h (freshHistory f h n) ≤ t := by
      apply freshIndex_le
      intro ht
      obtain ⟨k, -, hk⟩ := (hmem n (f t)).mp ht
      exact hx ⟨k, hk⟩
    have hfinite : (Set.range g).Finite := ((Finset.range (t + 1)).finite_toSet.image f).subset (by
      rintro y ⟨n, rfl⟩
      exact ⟨_, Finset.mem_range.mpr (by have := hbound n; omega), rfl⟩)
    exact Set.infinite_range_of_injective hinj hfinite

end TauCeti.Enumeration

namespace Computable

/-- An infinite computable range admits a total computable enumeration without repetitions. -/
theorem exists_injective_range {α β : Type*} [Primcodable α] [Primcodable β] {f : α → β}
    (hf : Computable f) (h : (Set.range f).Infinite) :
    ∃ g : ℕ → β, Computable g ∧ Function.Injective g ∧ Set.range g = Set.range f := by
  obtain ⟨_, a, _⟩ := h.nonempty
  let d : ℕ → α := fun n => (Encodable.decode n).getD a
  have hd : Computable d := Computable.decode.option_getD (Computable.const a)
  have hrange : Set.range (f ∘ d) = Set.range f :=
    (Encodable.surjective_decode_getD α a).range_comp f
  obtain ⟨g, hg, hinj, hgrange⟩ :=
    TauCeti.Enumeration.exists_injective_range_nat (hf.comp hd) (hrange ▸ h)
  exact ⟨g, hg, hinj, hgrange.trans hrange⟩

end Computable

namespace REPred

/-- Every infinite c.e. set has an injective total computable enumeration. -/
theorem exists_injective_computable_range {α : Type*} [Primcodable α] {S : Set α}
    (hS : REPred (· ∈ S)) (h : S.Infinite) :
    ∃ f : ℕ → α, Computable f ∧ Function.Injective f ∧ Set.range f = S := by
  obtain ⟨f, hf, hfrange⟩ := hS.exists_computable_range h.nonempty
  obtain ⟨g, hg, hinj, hgrange⟩ := hf.exists_injective_range (hfrange ▸ h)
  exact ⟨g, hg, hinj, hgrange.trans hfrange⟩

end REPred
