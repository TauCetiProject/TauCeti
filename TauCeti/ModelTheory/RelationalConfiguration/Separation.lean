/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.SetTheory.Descriptive.Antichain
import TauCeti.SetTheory.Descriptive.Tree

/-!
# Uniform back-and-forth separation of relational configurations

On a countable carrier `V`, two relational configurations are isomorphic precisely when they are
back-and-forth equivalent at every ordinal depth (`isoSetoid_iff_forall_bfEquivSetoid`). Pointwise,
any non-isomorphic pair is therefore separated at some countable depth `β < ω₁`. This file proves
the uniform descriptive counterpart (**uniform back-and-forth separation**): if `S` is an analytic
set of pairs of configurations on `V` containing no isomorphic pair, then a single countable level
`β < ω₁` separates every pair in `S` simultaneously (`exists_uniform_bfSeparation`).

No countability hypothesis is imposed on the relational language `L`, even though
`RelationalConfiguration L V` need not be Polish or metrizable when `L` has uncountably many
relation symbols. Given a surjection `enum : ℕ → V`, we attach to each pair `(c, d)` its **forced
back-and-forth tree** `bfTree enum c d` on the countable alphabet `V × V`: a finite sequence of
pairs belongs to the tree when even steps query `enum (i / 2)` on the left, odd steps query
`enum (i / 2)` on the right, and the two projected tuples have the same atomic type in
`c.toStructure` and `d.toStructure`. Infinite branches of `bfTree enum c d` assemble into
`L`-isomorphisms, so `bfTree enum c d` is well-founded whenever `c` and `d` are non-isomorphic;
conversely, transfinite induction along subtree rank shows that `c` and `d` cannot be
back-and-forth equivalent at the ordinal rank of `bfTree enum c d`. For each fixed finite node
`w`, membership `w ∈ bfTree enum c d` is an arbitrary intersection of clopen atom-agreement
conditions and constant equality conditions, hence closed in the product topology for every
relational language `L`. Applying the Lusin–Sierpiński / Kunen–Martin analytic boundedness theorem
(`MeasureTheory.AnalyticSet.exists_treeRank_lt_omega_one_of_isClosed`) bounds the tree ranks
strictly below `ω₁` across `S`.

Two consequences follow directly from uniform separation:

* **Asymptotic back-and-forth saturation of analytic and Borel splits.** If `B` and `C \ B` are
  analytic and `B` is closed under isomorphism into `C`, applying uniform separation to
  `B ×ˢ (C \ B)` produces a countable threshold `α < ω₁` above which `bfEquivSetoid L V β` cannot
  cross from `B` into `C \ B` (`exists_bfLevel_saturated_of_analyticSet`, together with the
  two-sided equivalence `exists_bfLevel_mem_iff_of_analyticSet` and its Borel specialization
  `exists_bfLevel_mem_iff_of_measurableSet`).
* **Absence of Cantor antichains and thinness from countable back-and-forth quotients.** If `A`
  meets only countably many classes of `bfEquivSetoid L V α` at every countable level `α < ω₁`,
  then `A` carries no Cantor antichain for isomorphism
  (`not_hasCantorAntichainOn_of_countable_bfEquivSetoid`), unconditionally on `L` and `A`: the
  off-diagonal of the continuous image of Cantor space is analytic and disjoint from isomorphism,
  so one countable level would separate the entire Cantor copy and inject `ℕ → Bool` into a
  countable quotient. When `L` has countably many relation symbols of each arity,
  `RelationalConfiguration L V` is Polish and `A` is therefore thin
  (`isThinOn_of_countable_bfEquivSetoid`).

## Main results

* `TauCeti.RelationalConfiguration.exists_uniform_bfSeparation`: an analytic set of non-isomorphic
  pairs on a countable carrier is uniformly separated at a single countable back-and-forth level.
* `TauCeti.RelationalConfiguration.exists_bfLevel_saturated_of_analyticSet`,
  `TauCeti.RelationalConfiguration.exists_bfLevel_mem_iff_of_analyticSet`, and
  `TauCeti.RelationalConfiguration.exists_bfLevel_mem_iff_of_measurableSet`: asymptotic saturation
  of isomorphism-invariant analytic and relatively Borel splits.
* `TauCeti.RelationalConfiguration.not_hasCantorAntichainOn_of_countable_bfEquivSetoid` and
  `TauCeti.RelationalConfiguration.isThinOn_of_countable_bfEquivSetoid`: countable level quotients
  forbid Cantor antichains unconditionally and force thinness in countable vocabularies.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University
  Press, 2021, Part 2, Chapter XII.
* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 31.1.
* The forced back-and-forth tree argument, analytic split saturation, and the off-diagonal
  Cantor-antichain obstruction follow `InfinitaryLogic/Descriptive/BFSeparation.lean`,
  `InfinitaryLogic/Descriptive/BFConcentration.lean`, and
  `InfinitaryLogic/Descriptive/BFScattered.lean` in Cameron Freer's `cameronfreer/infinitary-logic`
  (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, Apache-2.0), generalized here to
  arbitrary relational languages without countability hypotheses on the vocabulary and to arbitrary
  countable carriers and ordinal universes.
-/

public section

universe u v w o

open Cardinal Descriptive Descriptive.Tree FirstOrder FirstOrder.Language MeasureTheory Ordinal Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-! ### The forced back-and-forth tree -/

section ForcedTree

/-- First projection of a finite list of pairs as a tuple of length `w.length`. -/
private def tupleFst (w : List (V × V)) (i : Fin w.length) : V :=
  (w[i]).1

/-- Second projection of a finite list of pairs as a tuple of length `w.length`. -/
private def tupleSnd (w : List (V × V)) (i : Fin w.length) : V :=
  (w[i]).2

private theorem tupleFst_append_singleton (w : List (V × V)) (p : V × V) :
    tupleFst (w ++ [p]) =
      Fin.snoc (tupleFst w) p.1 ∘ Fin.cast (by simp : (w ++ [p]).length = w.length + 1) := by
  funext i
  rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using i.2 : i.1 < w.length + 1) with hlt | heq
  · have hi : Fin.cast (by simp : (w ++ [p]).length = w.length + 1) i = Fin.castSucc ⟨i.1, hlt⟩ :=
      by ext; rfl
    rw [Function.comp_apply, hi, Fin.snoc_castSucc]
    simp [tupleFst, List.getElem_append_left hlt]
  · have hlast : Fin.cast (by simp : (w ++ [p]).length = w.length + 1) i = Fin.last w.length := by
      ext; exact heq
    rw [Function.comp_apply, hlast, Fin.snoc_last]
    simp [tupleFst, heq]

private theorem tupleSnd_append_singleton (w : List (V × V)) (p : V × V) :
    tupleSnd (w ++ [p]) =
      Fin.snoc (tupleSnd w) p.2 ∘ Fin.cast (by simp : (w ++ [p]).length = w.length + 1) := by
  funext i
  rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using i.2 : i.1 < w.length + 1) with hlt | heq
  · have hi : Fin.cast (by simp : (w ++ [p]).length = w.length + 1) i = Fin.castSucc ⟨i.1, hlt⟩ :=
      by ext; rfl
    rw [Function.comp_apply, hi, Fin.snoc_castSucc]
    simp [tupleSnd, List.getElem_append_left hlt]
  · have hlast : Fin.cast (by simp : (w ++ [p]).length = w.length + 1) i = Fin.last w.length := by
      ext; exact heq
    rw [Function.comp_apply, hlast, Fin.snoc_last]
    simp [tupleSnd, heq]

/-- Schedule constraint along an enumeration `enum : ℕ → V`: even positions prescribe the left
entry `enum (i / 2)` and odd positions prescribe the right entry `enum (i / 2)`. -/
private def bfSchedule (enum : ℕ → V) (w : List (V × V)) : Prop :=
  ∀ i : Fin w.length, if Even i.1 then (w[i]).1 = enum (i.1 / 2) else (w[i]).2 = enum (i.1 / 2)

/-- Membership condition for the forced back-and-forth tree of `(c, d)` along `enum`: the schedule
is respected and the projected tuples have the same atomic type in `c` and `d`. -/
private def bfNode (enum : ℕ → V) (c d : RelationalConfiguration L V) (w : List (V × V)) : Prop :=
  bfSchedule enum w ∧
    @SameAtomicType L w.length V V c.toStructure d.toStructure _ (tupleFst w) (tupleSnd w)

private theorem bfNode_of_append_singleton {enum : ℕ → V} {c d : RelationalConfiguration L V}
    {w : List (V × V)} {p : V × V} (h : bfNode enum c d (w ++ [p])) : bfNode enum c d w := by
  refine ⟨fun i => ?_, ?_⟩
  · have hi := h.1 ⟨i.1, by simp⟩
    simpa [List.getElem_append_left i.2] using hi
  · let g : Fin w.length → Fin (w ++ [p]).length := fun i => ⟨i.1, by simp⟩
    have hfst : tupleFst w = tupleFst (w ++ [p]) ∘ g := by
      funext i
      simp [tupleFst, g, List.getElem_append_left i.2]
    have hsnd : tupleSnd w = tupleSnd (w ++ [p]) ∘ g := by
      funext i
      simp [tupleSnd, g, List.getElem_append_left i.2]
    rw [hfst, hsnd]
    exact @SameAtomicType.comp L (w ++ [p]).length V V c.toStructure d.toStructure _
      (tupleFst (w ++ [p])) (tupleSnd (w ++ [p])) h.2 w.length g

/-- The forced back-and-forth descriptive tree of `(c, d)` along `enum : ℕ → V`. -/
private def bfTree (enum : ℕ → V) (c d : RelationalConfiguration L V) : Descriptive.tree (V × V) :=
  ⟨{w | bfNode enum c d w}, fun _ _ => bfNode_of_append_singleton⟩

@[simp]
private theorem mem_bfTree {enum : ℕ → V} {c d : RelationalConfiguration L V}
    {w : List (V × V)} : w ∈ bfTree enum c d ↔ bfNode enum c d w :=
  Iff.rfl

/-- For any fixed finite sequence `w`, the set of pairs `(c, d)` whose forced back-and-forth tree
contains `w` is closed in the product topology, with no countability assumption on `L` or `V`. -/
private theorem isClosed_setOf_mem_bfTree (enum : ℕ → V) (w : List (V × V)) :
    IsClosed {q : RelationalConfiguration L V × RelationalConfiguration L V |
      w ∈ bfTree enum q.1 q.2} := by
  have heq : {q : RelationalConfiguration L V × RelationalConfiguration L V |
      w ∈ bfTree enum q.1 q.2} =
      {q | bfSchedule enum w} ∩
        ⋂ idx : AtomicIdx L w.length,
          {q | @AtomicIdx.Holds L w.length V q.1.toStructure idx (tupleFst w) ↔
            @AtomicIdx.Holds L w.length V q.2.toStructure idx (tupleSnd w)} := by
    ext q
    simp [bfNode, @sameAtomicType_def L w.length V V q.1.toStructure q.2.toStructure]
  rw [heq]
  refine isClosed_const.inter (isClosed_iInter fun idx => ?_)
  cases idx with
  | eq i j =>
    simp only [AtomicIdx.holds_eq]
    exact isClosed_const
  | rel R f =>
    simp only [AtomicIdx.holds_rel, toStructure_relMap, ← Bool.eq_iff_iff]
    exact isClosed_eq ((continuous_eval _).comp continuous_fst)
      ((continuous_eval _).comp continuous_snd)

/-- An infinite branch through `bfTree enum c d` along a surjective enumeration `enum : ℕ → V`
induces an isomorphism between `c` and `d`. -/
private theorem isoSetoid_of_not_isWellFounded_bfTree {enum : ℕ → V}
    (henum : Function.Surjective enum) {c d : RelationalConfiguration L V}
    (h : ¬ IsWellFounded (bfTree enum c d)) : isoSetoid L V c d := by
  obtain ⟨f, hf⟩ := not_isWellFounded_iff.mp h
  have hsched (i : ℕ) :
      if Even i then (f i).1 = enum (i / 2) else (f i).2 = enum (i / 2) := by
    let idx : Fin (List.ofFn fun j : Fin (i + 1) => f j).length :=
      ⟨i, by rw [List.length_ofFn]; exact Nat.lt_succ_self i⟩
    have hi := (mem_bfTree.mp (hf (i + 1))).1 idx
    simpa only [Fin.getElem_fin, List.getElem_ofFn, idx] using hi
  have hN (N : ℕ) : ∀ idx : AtomicIdx L N,
      @AtomicIdx.Holds L N V c.toStructure idx (fun i : Fin N => (f i).1) ↔
        @AtomicIdx.Holds L N V d.toStructure idx (fun i : Fin N => (f i).2) := by
    let w := List.ofFn (fun i : Fin N => f i)
    have hw := (mem_bfTree.mp (hf N)).2
    have hcomp := @SameAtomicType.comp L w.length V V c.toStructure d.toStructure _
      (tupleFst w) (tupleSnd w) hw N (Fin.cast List.length_ofFn.symm)
    have hfst : tupleFst w ∘ Fin.cast List.length_ofFn.symm = fun i : Fin N => (f i).1 := by
      funext i; simp [tupleFst, w]
    have hsnd : tupleSnd w ∘ Fin.cast List.length_ofFn.symm = fun i : Fin N => (f i).2 := by
      funext i; simp [tupleSnd, w]
    rw [hfst, hsnd] at hcomp
    exact (@sameAtomicType_def L N V V c.toStructure d.toStructure _ _ _).mp hcomp
  have heq (i j : ℕ) : (f i).1 = (f j).1 ↔ (f i).2 = (f j).2 := by
    simpa only [AtomicIdx.holds_eq] using hN (max i j + 1) (.eq ⟨i, by omega⟩ ⟨j, by omega⟩)
  have hrel {k : ℕ} (R : L.Relations k) (idx : Fin k → ℕ) :
      @Structure.RelMap L V c.toStructure k R (fun m => (f (idx m)).1) ↔
        @Structure.RelMap L V d.toStructure k R (fun m => (f (idx m)).2) := by
    let N := Finset.univ.sup idx + 1
    let g : Fin k → Fin N := fun m => ⟨idx m, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ m))⟩
    simpa only [AtomicIdx.holds_rel, Function.comp_def] using hN N (.rel R g)
  have hsurj₁ (x : V) : ∃ i : ℕ, (f i).1 = x := by
    obtain ⟨m, rfl⟩ := henum x
    refine ⟨2 * m, ?_⟩
    have hm := hsched (2 * m)
    have heven : Even (2 * m) := even_two_mul m
    simpa [heven] using hm
  have hsurj₂ (y : V) : ∃ j : ℕ, (f j).2 = y := by
    obtain ⟨m, rfl⟩ := henum y
    refine ⟨2 * m + 1, ?_⟩
    have hm := hsched (2 * m + 1)
    have hodd : ¬ Even (2 * m + 1) := by simp
    have hdiv : (2 * m + 1) / 2 = m := by omega
    simpa [hodd, hdiv] using hm
  choose idx₁ hidx₁ using hsurj₁
  choose idx₂ hidx₂ using hsurj₂
  let toFun : V → V := fun x => (f (idx₁ x)).2
  let invFun : V → V := fun y => (f (idx₂ y)).1
  refine isoSetoid_apply.mpr ⟨@Language.Equiv.mk L V V c.toStructure d.toStructure
    { toFun := toFun
      invFun := invFun
      left_inv := fun x => ((heq _ _).mpr (hidx₂ (toFun x))).trans (hidx₁ x)
      right_inv := fun y => ((heq _ _).mp (hidx₁ (invFun y))).trans (hidx₂ y) }
    (fun {n} fn => IsEmpty.elim (inferInstance : IsEmpty (L.Functions n)) fn)
    (fun R x => by
      dsimp [toFun, Function.comp_def]
      conv_rhs => rw [funext fun m => (hidx₁ (x m)).symm]
      exact (hrel R (fun m => idx₁ (x m))).symm)⟩

/-- Contrapositively, when `c` and `d` are non-isomorphic, `bfTree enum c d` is well-founded. -/
private theorem isWellFounded_bfTree_of_not_isoSetoid {enum : ℕ → V}
    (henum : Function.Surjective enum) {c d : RelationalConfiguration L V}
    (h : ¬ isoSetoid L V c d) : IsWellFounded (bfTree enum c d) := by
  by_contra hnot
  exact h (isoSetoid_of_not_isWellFounded_bfTree henum hnot)

/-- If `bfTree enum c d` is well-founded and its residual subtree at `w ∈ bfTree enum c d` has rank
at most `γ`, then the projected tuples of `w` are not `γ`-equivalent. -/
private theorem not_bfEquiv_of_rank_subAt_bfTree_le {enum : ℕ → V}
    {c d : RelationalConfiguration L V} (hwf : IsWellFounded (bfTree enum c d))
    {γ : Ordinal.{w}} :
    ∀ {w : List (V × V)}, w ∈ bfTree enum c d →
      Tree.rank (Tree.subAt (bfTree enum c d) w) ≤ γ →
      ¬ @BFEquiv L _ V V c.toStructure d.toStructure γ w.length (tupleFst w) (tupleSnd w) := by
  induction γ using WellFoundedLT.induction with
  | ind γ ih =>
    intro w hw hrank hbf
    rw [hwf.rank_subAt_eq_succ_iSup hw, Order.succ_eq_add_one] at hrank
    set δ : Ordinal.{w} := ⨆ p : V × V, Tree.rank (Tree.subAt (bfTree enum c d) (w ++ [p]))
    have hδlt : δ < γ := (Order.lt_add_one_iff.mpr le_rfl).trans_le hrank
    have hbf' : @BFEquiv L _ V V c.toStructure d.toStructure (δ + 1) w.length
        (tupleFst w) (tupleSnd w) :=
      @BFEquiv.mono L _ V V c.toStructure d.toStructure w.length (tupleFst w) (tupleSnd w)
        (δ + 1) γ hbf hrank
    obtain ⟨_, hforth, hback⟩ :=
      (@BFEquiv.add_one L _ V V c.toStructure d.toStructure w.length δ
        (tupleFst w) (tupleSnd w)).mp hbf'
    have hex : ∃ p : V × V,
        (if Even w.length then p.1 = enum (w.length / 2) else p.2 = enum (w.length / 2)) ∧
        @BFEquiv L _ V V c.toStructure d.toStructure δ (w.length + 1)
          (Fin.snoc (tupleFst w) p.1) (Fin.snoc (tupleSnd w) p.2) := by
      by_cases heven : Even w.length
      · obtain ⟨y, hy⟩ := hforth (enum (w.length / 2))
        exact ⟨(enum (w.length / 2), y), by simp [heven], hy⟩
      · obtain ⟨x, hx⟩ := hback (enum (w.length / 2))
        exact ⟨(x, enum (w.length / 2)), by simp [heven], hx⟩
    obtain ⟨p, hpsched, hpbf⟩ := hex
    have hpbf' : @BFEquiv L _ V V c.toStructure d.toStructure δ (w ++ [p]).length
        (tupleFst (w ++ [p])) (tupleSnd (w ++ [p])) := by
      rw [tupleFst_append_singleton, tupleSnd_append_singleton]
      exact @BFEquiv.comp L _ V V c.toStructure d.toStructure (w.length + 1)
        (Fin.snoc (tupleFst w) p.1) (Fin.snoc (tupleSnd w) p.2) δ hpbf (w ++ [p]).length
        (Fin.cast (by simp))
    have hmem : w ++ [p] ∈ bfTree enum c d := by
      refine ⟨fun i => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using i.2 : i.1 < w.length + 1) with hlt | heq
        · simpa [List.getElem_append_left hlt] using hw.1 ⟨i.1, hlt⟩
        · simpa [heq] using hpsched
      · exact @BFEquiv.sameAtomicType L _ V V c.toStructure d.toStructure (w ++ [p]).length
          (tupleFst (w ++ [p])) (tupleSnd (w ++ [p])) δ hpbf'
    have hple : Tree.rank (Tree.subAt (bfTree enum c d) (w ++ [p])) ≤ δ :=
      Ordinal.le_iSup (fun q : V × V => Tree.rank (Tree.subAt (bfTree enum c d) (w ++ [q]))) p
    exact ih δ hδlt hmem hple hpbf'

/-- When `bfTree enum c d` is well-founded and has rank at most `γ`, `c` and `d` are not
`γ`-equivalent. -/
private theorem not_bfEquivSetoid_of_rank_bfTree_le {enum : ℕ → V}
    {c d : RelationalConfiguration L V} (hwf : IsWellFounded (bfTree enum c d))
    {γ : Ordinal.{w}} (hrank : Tree.rank (bfTree enum c d) ≤ γ) :
    ¬ bfEquivSetoid L V γ c d := by
  have hfst : tupleFst ([] : List (V × V)) = Fin.elim0 := funext fun i => Fin.elim0 i
  have hsnd : tupleSnd ([] : List (V × V)) = Fin.elim0 := funext fun i => Fin.elim0 i
  by_cases hnil : ([] : List (V × V)) ∈ bfTree enum c d
  · intro hbf
    have h0 : @BFEquiv L _ V V c.toStructure d.toStructure γ ([] : List (V × V)).length
        (tupleFst []) (tupleSnd []) := by
      rw [hfst, hsnd]
      exact bfEquivSetoid_apply.mp hbf
    exact not_bfEquiv_of_rank_subAt_bfTree_le hwf hnil (by simpa using hrank) h0
  · intro hbf
    apply hnil
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    rw [hfst, hsnd]
    exact @BFEquiv.sameAtomicType L _ V V c.toStructure d.toStructure 0 Fin.elim0 Fin.elim0 γ
      (bfEquivSetoid_apply.mp hbf)

end ForcedTree

/-! ### Uniform back-and-forth separation -/

/-- **Uniform back-and-forth separation.** Let `S` be an analytic set of pairs of relational
configurations on a countable carrier `V` containing no isomorphic pair. Then there is a single
countable ordinal `β < ω₁` such that no pair in `S` is back-and-forth equivalent at depth `β`. No
countability hypothesis on `L` is required, and `β` may be chosen in any ordinal universe `o`. -/
theorem exists_uniform_bfSeparation [Countable V]
    {S : Set (RelationalConfiguration L V × RelationalConfiguration L V)}
    (hS : AnalyticSet S) (hdisj : ∀ p ∈ S, ¬ isoSetoid L V p.1 p.2) :
    ∃ β : Ordinal.{o}, β < ω₁ ∧ ∀ p ∈ S, ¬ bfEquivSetoid L V β p.1 p.2 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨0, Ordinal.omega_pos 1,
      fun p hp h0 => hdisj p hp (isoSetoid_iff_bfEquivSetoid_of_isEmpty.mpr h0)⟩
  · obtain ⟨enum, henum⟩ := exists_surjective_nat V
    obtain ⟨βw, hβw, hbound⟩ :=
      hS.exists_treeRank_lt_omega_one_of_isClosed (fun p => bfTree enum p.1 p.2)
        (fun p hp => isWellFounded_bfTree_of_not_isoSetoid henum (hdisj p hp))
        (isClosed_setOf_mem_bfTree enum)
    have hβw' : βw < Ordinal.lift.{w, 0} (ω₁ : Ordinal.{0}) := by
      rwa [Ordinal.lift_eq_omega_one.mpr rfl]
    obtain ⟨β₀, hβ₀, hβ₀_eq⟩ := Ordinal.lt_lift_iff.mp hβw'
    refine ⟨Ordinal.lift.{o, 0} β₀, Ordinal.lift_lt_omega_one.mpr hβ₀, fun p hp hbf => ?_⟩
    rw [bfEquivSetoid_lift, ← bfEquivSetoid_lift.{u, v, w, 0, w}, hβ₀_eq] at hbf
    exact not_bfEquivSetoid_of_rank_bfTree_le
      (isWellFounded_bfTree_of_not_isoSetoid henum (hdisj p hp)) (hbound p hp).le hbf

/-! ### Asymptotic saturation of analytic and Borel splits -/

/-- **Back-and-forth saturation of an analytic split** (one-sided form). Let `V` be countable and
suppose `B` and `C \ B` are analytic sets of configurations on `V` such that isomorphism cannot
carry a point of `B` to a point of `C \ B`. Then from some countable level `α < ω₁` onward, no
`bfEquivSetoid L V β`-step carries a point of `B` into `C \ B`. -/
theorem exists_bfLevel_saturated_of_analyticSet [Countable V]
    {B C : Set (RelationalConfiguration L V)}
    (hB : AnalyticSet B) (hCB : AnalyticSet (C \ B))
    (hinv : ∀ b ∈ B, ∀ c ∈ C, isoSetoid L V b c → c ∈ B) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ b ∈ B, ∀ c ∈ C, bfEquivSetoid L V β b c → c ∈ B := by
  obtain ⟨α, hα, hsep⟩ := exists_uniform_bfSeparation.{u, v, w, o} (hB.prod hCB)
    fun p ⟨hb, hc, hnotB⟩ hiso => hnotB (hinv p.1 hb p.2 hc hiso)
  refine ⟨α, hα, fun β hαβ b hb c hc hbc => by_contra fun hnotB => ?_⟩
  exact hsep (b, c) ⟨hb, hc, hnotB⟩ (bfEquivSetoid_anti hαβ hbc)

/-- **Back-and-forth saturation of an analytic split** (two-sided form). If `C ∩ B` and `C \ B` are
analytic and `B` is closed under isomorphism within `C`, then from some countable level `α < ω₁`
onward, `bfEquivSetoid L V β`-equivalent members of `C` lie on the same side of `B`. -/
theorem exists_bfLevel_mem_iff_of_analyticSet [Countable V]
    {B C : Set (RelationalConfiguration L V)}
    (hCB : AnalyticSet (C ∩ B)) (hCdiff : AnalyticSet (C \ B))
    (hinv : ∀ c ∈ C, ∀ d ∈ C, isoSetoid L V c d → c ∈ B → d ∈ B) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ c ∈ C, ∀ d ∈ C, bfEquivSetoid L V β c d → (c ∈ B ↔ d ∈ B) := by
  have hdiff : C \ (C ∩ B) = C \ B := by ext; simp
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated_of_analyticSet.{u, v, w, o} hCB (hdiff ▸ hCdiff)
    fun b ⟨hbC, hbB⟩ c hc hiso => ⟨hc, hinv b hbC c hc hiso hbB⟩
  refine ⟨α, hα, fun β hαβ c hc d hd hcd => ⟨fun hcB => ?_, fun hdB => ?_⟩⟩
  · exact (hsat β hαβ c ⟨hc, hcB⟩ d hd hcd).2
  · exact (hsat β hαβ d ⟨hd, hdB⟩ c hc ((bfEquivSetoid L V β).symm hcd)).2

/-- **Back-and-forth saturation of a Borel cut of an analytic class.** On a countable carrier in a
vocabulary with countably many relation symbols of each arity, if `C` is analytic, `B` is Borel,
and `B` is closed under isomorphism within `C`, then from some countable level `α < ω₁` onward,
`bfEquivSetoid L V β`-equivalent members of `C` lie on the same side of `B`. -/
theorem exists_bfLevel_mem_iff_of_measurableSet [Countable V] [∀ n, Countable (L.Relations n)]
    {B C : Set (RelationalConfiguration L V)}
    (hC : AnalyticSet C) (hB : MeasurableSet B)
    (hinv : ∀ c ∈ C, ∀ d ∈ C, isoSetoid L V c d → c ∈ B → d ∈ B) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧
      ∀ β ≥ α, ∀ c ∈ C, ∀ d ∈ C, bfEquivSetoid L V β c d → (c ∈ B ↔ d ∈ B) :=
  exists_bfLevel_mem_iff_of_analyticSet (hC.inter_measurableSet hB)
    (@Set.sdiff_eq _ C B ▸ hC.inter_measurableSet hB.compl) hinv

/-! ### Cantor antichains and thinness from countable level quotients -/

/-- **Countable level quotients forbid Cantor antichains.** On a countable carrier `V`, if a set
`A` of configurations meets only countably many classes of `bfEquivSetoid L V α` at every countable
level `α < ω₁`, then `A` carries no Cantor antichain for isomorphism. No definability or invariance
of `A`, and no countability hypothesis on `L`, is assumed. -/
theorem not_hasCantorAntichainOn_of_countable_bfEquivSetoid [Countable V]
    {A : Set (RelationalConfiguration L V)}
    (hA : ∀ α : Ordinal.{o}, α < ω₁ →
      Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : A → _)))) :
    ¬ (isoSetoid L V).HasCantorAntichainOn A := by
  intro hcantor
  obtain ⟨f, hf, hrange, hinj, hnoniso⟩ := hcantor.exists_injective
  have : TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → Bool) :=
    TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable
  have hoff : AnalyticSet (range f).offDiag := (analyticSet_range_of_polishSpace hf).offDiag
  have hdisj : ∀ p ∈ (range f).offDiag, ¬ isoSetoid L V p.1 p.2 := by
    rintro ⟨_, _⟩ ⟨⟨a, rfl⟩, ⟨b, rfl⟩, hne⟩
    exact hnoniso a b (fun hab => hne (congrArg f hab))
  obtain ⟨β, hβ, hsep⟩ := exists_uniform_bfSeparation.{u, v, w, o} hoff hdisj
  have hcantorβ : (bfEquivSetoid L V β).HasCantorAntichainOn A :=
    Setoid.hasCantorAntichainOn_iff.mpr
      ⟨f, hf, fun a => hrange (mem_range_self a),
        fun a b hab => hsep (f a, f b) ⟨mem_range_self a, mem_range_self b, hinj.ne hab⟩⟩
  have hcont : 𝔠 ≤ #(Quotient ((bfEquivSetoid L V β).comap (Subtype.val : A → _))) :=
    hcantorβ.continuum_le_mk_quotient_comap
  have := hA β hβ
  have hle : #(Quotient ((bfEquivSetoid L V β).comap (Subtype.val : A → _))) ≤ ℵ₀ :=
    mk_le_aleph0
  exact Cardinal.aleph0_lt_continuum.not_ge (hcont.trans hle)

/-- **Countable level quotients imply thinness.** On a countable carrier `V` in a vocabulary with
countably many relation symbols of each arity, any set `A` of configurations meeting countably many
classes at every countable back-and-forth level is thin for isomorphism. -/
theorem isThinOn_of_countable_bfEquivSetoid [Countable V] [∀ n, Countable (L.Relations n)]
    {A : Set (RelationalConfiguration L V)}
    (hA : ∀ α : Ordinal.{o}, α < ω₁ →
      Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : A → _)))) :
    (isoSetoid L V).IsThinOn A :=
  Setoid.isThinOn_iff_not_hasCantorAntichainOn.mpr
    (not_hasCantorAntichainOn_of_countable_bfEquivSetoid hA)

end TauCeti.RelationalConfiguration
