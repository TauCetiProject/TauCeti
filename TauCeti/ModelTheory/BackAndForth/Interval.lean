/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.LinearOrder
public import TauCeti.Order.CmpCell
public import Mathlib.Order.Hom.Set

/-!
# Back-and-forth equivalence of linear orders, interval by interval

For linear orders, read as structures in the language of orders through Mathlib's
`FirstOrder.Language.orderStructure`, back-and-forth equivalence of tuples is local: two tuples of
the same atomic type are back-and-forth equivalent at level `γ` exactly when the intervals they cut
out of their orders are pairwise back-and-forth equivalent at level `γ`. The intervals are indexed
by comparison patterns. For a tuple `a : Fin n → M` and `σ : Fin n → Ordering`, the cell
`TauCeti.cmpCell a σ` is the set of points `z` with `cmp (a i) z = σ i` for every `i`. Listing
the distinct entries of `a` in increasing order, the cells are the open intervals between
consecutive entries (including the two unbounded ones), the singletons of the entries, and empty
sets; two tuples of the same atomic type have empty and singleton cells at the same patterns, so
quantifying over all patterns is the same as quantifying over the open intervals.

As a consequence, back-and-forth equivalence at level `γ` is compatible with ordered sums: if
`A` is equivalent to `A'` and `B` to `B'`, then `A ⊕ₗ B` is equivalent to `A' ⊕ₗ B'`. These are
the tools for computing back-and-forth levels of well-orders, such as the equivalence of the
ordinals `ω ^ γ * δ` and `ω ^ γ * ε` at level `γ` for nonzero `δ` and `ε`.

## Main results

* `TauCeti.bfEquiv_iff_forall_cmpCell`: the interval lemma.
* `TauCeti.bfEquiv_snoc_elim0_iff`: the interval lemma for one point, whose cells are the initial
  and final segments it cuts out.
* `TauCeti.BFEquiv.sumLex`: back-and-forth equivalence at level `γ` passes to ordered sums.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Lemma II.37,
  stated there for the one-sided back-and-forth relations.
-/

public section

universe w w' u₁ u₂ u₃ u₄ o

namespace TauCeti

open FirstOrder FirstOrder.Language Fin

attribute [local instance] orderStructure

/-! ### The interval lemma -/

section IntervalLemma

variable {M : Type w} {N : Type w'} [LinearOrder M] [LinearOrder N] {n : ℕ}

/-- The interval lemma at the level `γ`, for linear orders in the universes `u₁` and `u₂`. -/
private def IntervalLemma (γ : Ordinal.{o}) : Prop :=
  ∀ (M : Type u₁) (N : Type u₂) [LinearOrder M] [LinearOrder N] (n : ℕ) (a : Fin n → M)
    (b : Fin n → N), BFEquiv (L := Language.order) γ n a b ↔
      SameAtomicType (L := Language.order) a b ∧ ∀ σ, BFEquiv (L := Language.order) γ 0
        (Fin.elim0 : Fin 0 → cmpCell a σ) (Fin.elim0 : Fin 0 → cmpCell b σ)

/-- The interval lemma for one order of the two universes gives it for the other. -/
private theorem IntervalLemma.swap {γ : Ordinal.{o}} (h : IntervalLemma.{u₁, u₂} γ) :
    IntervalLemma.{u₂, u₁} γ := by
  intro M N _ _ n a b
  rw [BFEquiv.symm_iff, h N M n b a]
  exact and_congr ⟨.symm, .symm⟩ (forall_congr' fun _ => BFEquiv.symm_iff _ _ _)

/-- The forth step for the cells of two tuples that satisfy the forth step at the next level. -/
private theorem IntervalLemma.forth_cmpCell {γ : Ordinal.{o}} (ih : IntervalLemma.{w, w'} γ)
    {a : Fin n → M} {b : Fin n → N}
    (hf : ∀ x : M, ∃ y : N, BFEquiv (L := Language.order) γ (n + 1) (snoc a x) (snoc b y))
    (σ : Fin n → Ordering) (p : cmpCell a σ) :
    ∃ q : cmpCell b σ, BFEquiv (L := Language.order) γ 1
      (snoc (Fin.elim0 : Fin 0 → cmpCell a σ) p) (snoc (Fin.elim0 : Fin 0 → cmpCell b σ) q) := by
  obtain ⟨y, hy⟩ := hf p
  obtain ⟨hs, hc⟩ := (ih M N _ _ _).1 hy
  have hq : y ∈ cmpCell b σ := mem_cmpCell.2 fun i =>
    ((sameAtomicType_snoc_iff_cmp.1 hs).2 i).symm.trans (mem_cmpCell.1 p.property i)
  refine ⟨⟨y, hq⟩, (ih _ _ _ _ _).2 ⟨sameAtomicType_snoc_elim0 _ _, fun τ => ?_⟩⟩
  exact (hc _).orderIso_congr (cmpCellSnocOrderIso a σ p τ).symm
    (cmpCellSnocOrderIso b σ ⟨y, hq⟩ τ).symm

/-- The forth step for two tuples whose cells are equivalent at the next level. -/
private theorem IntervalLemma.forth_snoc {γ : Ordinal.{o}} (ih : IntervalLemma.{w, w'} γ)
    {a : Fin n → M} {b : Fin n → N} (hs : SameAtomicType (L := Language.order) a b)
    (hc : ∀ σ, BFEquiv (L := Language.order) (γ + 1) 0
      (Fin.elim0 : Fin 0 → cmpCell a σ) (Fin.elim0 : Fin 0 → cmpCell b σ)) (x : M) :
    ∃ y : N, BFEquiv (L := Language.order) γ (n + 1) (snoc a x) (snoc b y) := by
  -- Answer `x` by a point `q` of the matching cell, chosen by the forth step inside the cell.
  obtain ⟨σ₀, hx⟩ : ∃ σ₀, x ∈ cmpCell a σ₀ := ⟨_, mem_cmpCell_cmp a x⟩
  obtain ⟨q, hq⟩ := ((BFEquiv.add_one γ _ _).1 (hc σ₀)).2.1 ⟨x, hx⟩
  obtain ⟨-, hsub⟩ := (ih _ _ _ _ _).1 hq
  refine ⟨q, (ih M N _ _ _).2
    ⟨sameAtomicType_snoc_iff_cmp.2
      ⟨hs, fun i => (mem_cmpCell.1 hx i).trans (mem_cmpCell.1 q.property i).symm⟩,
      fun σ' => ?_⟩⟩
  obtain ⟨σ, o, rfl⟩ : ∃ σ o, σ' = snoc σ o := ⟨init σ', σ' (last n), (snoc_init_self σ').symm⟩
  by_cases hσ : σ = σ₀
  · -- Inside the cell of `x`, the cells of `snoc a x` are the cells of `x` within it.
    subst hσ
    exact (hsub fun _ => o).orderIso_congr (cmpCellSnocOrderIso a _ ⟨x, hx⟩ fun _ => o)
      (cmpCellSnocOrderIso b _ q fun _ => o)
  · -- Elsewhere they are whole cells of `a` and `b`, or empty, in the same way.
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hσ
    rw [cmpCell_snoc_snoc_of_ne hx hi, cmpCell_snoc_snoc_of_ne q.property hi]
    by_cases hP : cmpOfNe (σ₀ i) (σ i) = o
    · rw [ite_eq_left hP, ite_eq_left hP]
      exact (hc σ).mono le_self_add
    · rw [ite_eq_right hP, ite_eq_right hP]
      exact BFEquiv.of_isEmpty γ

/-- The interval lemma, by induction on the level. -/
private theorem intervalLemma (γ : Ordinal.{o}) : IntervalLemma.{w, w'} γ := by
  induction γ using Ordinal.limitRecOn with
  | zero =>
    intro M N _ _ n a b
    simp [sameAtomicType_elim0]
  | add_one γ ih =>
    intro M N _ _ n a b
    rw [BFEquiv.add_one]
    constructor
    · rintro ⟨h, hf, hb⟩
      refine ⟨h.sameAtomicType, fun σ => (BFEquiv.add_one γ _ _).2
        ⟨((ih M N n a b).1 h).2 σ, ih.forth_cmpCell hf σ, fun q => ?_⟩⟩
      obtain ⟨p, hp⟩ := ih.swap.forth_cmpCell (fun y => (hb y).imp fun _ h => h.symm) σ q
      exact ⟨p, hp.symm⟩
    · rintro ⟨hs, hc⟩
      refine ⟨(ih M N n a b).2 ⟨hs, fun σ => (hc σ).mono le_self_add⟩, ih.forth_snoc hs hc,
        fun y => ?_⟩
      obtain ⟨x, hx⟩ := ih.swap.forth_snoc hs.symm (fun σ => (hc σ).symm) y
      exact ⟨x, hx.symm⟩
  | limit γ hγ ih =>
    intro M N _ _ n a b
    simp only [BFEquiv.limit hγ]
    refine ⟨fun h => ⟨(h 0 hγ.pos).sameAtomicType,
      fun σ β hβ => ((ih β hβ M N n a b).1 (h β hβ)).2 σ⟩, fun ⟨hs, hc⟩ β hβ => ?_⟩
    exact (ih β hβ M N n a b).2 ⟨hs, fun σ => hc σ β hβ⟩

/-- **The interval lemma.** Two tuples of linear orders are back-and-forth equivalent at level
`γ` exactly when they have the same atomic type and each cell of the first tuple is
back-and-forth equivalent at level `γ` to the cell of the second tuple with the same comparison
pattern. -/
theorem bfEquiv_iff_forall_cmpCell (γ : Ordinal.{o}) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := Language.order) γ n a b ↔
      SameAtomicType (L := Language.order) a b ∧ ∀ σ, BFEquiv (L := Language.order) γ 0
        (Fin.elim0 : Fin 0 → cmpCell a σ) (Fin.elim0 : Fin 0 → cmpCell b σ) :=
  intervalLemma γ M N n a b

/-- **The interval lemma for one point.** Two points of linear orders are back-and-forth
equivalent at level `γ` exactly when the initial segments below them are, and so are the final
segments above them. -/
theorem bfEquiv_snoc_elim0_iff (γ : Ordinal.{o}) (x : M) (y : N) :
    BFEquiv (L := Language.order) γ 1 (snoc (Fin.elim0 : Fin 0 → M) x)
        (snoc (Fin.elim0 : Fin 0 → N) y) ↔
      BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → Set.Iio x)
          (Fin.elim0 : Fin 0 → Set.Iio y) ∧
        BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → Set.Ioi x)
          (Fin.elim0 : Fin 0 → Set.Ioi y) := by
  rw [bfEquiv_iff_forall_cmpCell, and_iff_right (sameAtomicType_snoc_elim0 x y)]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hIio, hIoi⟩ τ => ?_⟩
  · have := h fun _ => .gt
    rwa [cmpCell_snoc_elim0_of_gt rfl, cmpCell_snoc_elim0_of_gt rfl] at this
  · have := h fun _ => .lt
    rwa [cmpCell_snoc_elim0_of_lt rfl, cmpCell_snoc_elim0_of_lt rfl] at this
  · rcases hτ : τ (last 0)
    · rwa [cmpCell_snoc_elim0_of_lt hτ, cmpCell_snoc_elim0_of_lt hτ]
    · rw [cmpCell_snoc_elim0_of_eq hτ, cmpCell_snoc_elim0_of_eq hτ]
      exact (BFEquiv.refl γ _).orderIso_congr (OrderIso.refl _) (OrderIso.ofUnique _ _)
    · rwa [cmpCell_snoc_elim0_of_gt hτ, cmpCell_snoc_elim0_of_gt hτ]

end IntervalLemma

/-! ### Ordered sums -/

section SumLex

variable {A : Type u₁} {B : Type u₃} [LinearOrder A] [LinearOrder B]

/-- The proposition `p`, as a subset of a linear order, is back-and-forth equivalent to the same
subset of an equivalent order. -/
private theorem bfEquiv_setOf_const {A' : Type u₂} [LinearOrder A'] {γ : Ordinal.{o}}
    (h : BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A'))
    (p : Prop) : BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → {_x : A | p})
      (Fin.elim0 : Fin 0 → {_x : A' | p}) := by
  by_cases hp : p
  · rw [Set.eq_univ_of_forall (s := {_x : A | p}) fun _ => hp,
      Set.eq_univ_of_forall (s := {_x : A' | p}) fun _ => hp]
    exact h.orderIso_congr (OrderIso.Set.univ).symm (OrderIso.Set.univ).symm
  · have : IsEmpty {_x : A | p} := ⟨fun x => hp x.property⟩
    have : IsEmpty {_x : A' | p} := ⟨fun x => hp x.property⟩
    exact BFEquiv.of_isEmpty γ

/-- Back-and-forth equivalence of ordered sums at the level `γ`, for linear orders in the given
universes. -/
private def SumLexStatement (γ : Ordinal.{o}) : Prop :=
  ∀ (A : Type u₁) (A' : Type u₂) (B : Type u₃) (B' : Type u₄) [LinearOrder A] [LinearOrder A']
    [LinearOrder B] [LinearOrder B'],
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A') →
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → B) (Fin.elim0 : Fin 0 → B') →
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → A ⊕ₗ B) (Fin.elim0 : Fin 0 → A' ⊕ₗ B')

/-- The sum statement for one order of the universes gives it for the swapped order. -/
private theorem SumLexStatement.swap {γ : Ordinal.{o}} (h : SumLexStatement.{u₁, u₂, u₃, u₄} γ) :
    SumLexStatement.{u₂, u₁, u₄, u₃} γ :=
  fun A A' B B' _ _ _ _ hA hB => (h A' A B' B hA.symm hB.symm).symm

/-- The forth step for ordered sums of orders that are equivalent at the next level: a point of
one summand is answered in the same summand. -/
private theorem SumLexStatement.forth {A' : Type u₂} {B' : Type u₄} [LinearOrder A']
    [LinearOrder B'] {γ : Ordinal.{o}} (ih : SumLexStatement.{u₁, u₂, u₃, u₄} γ)
    (hA : BFEquiv (L := Language.order) (γ + 1) 0 (Fin.elim0 : Fin 0 → A)
      (Fin.elim0 : Fin 0 → A'))
    (hB : BFEquiv (L := Language.order) (γ + 1) 0 (Fin.elim0 : Fin 0 → B)
      (Fin.elim0 : Fin 0 → B')) (z : A ⊕ₗ B) :
    ∃ z' : A' ⊕ₗ B', BFEquiv (L := Language.order) γ 1 (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) z)
      (snoc (Fin.elim0 : Fin 0 → A' ⊕ₗ B') z') := by
  obtain ⟨a | b, rfl⟩ := toLex.surjective z
  · obtain ⟨a', ha⟩ := ((BFEquiv.add_one γ _ _).1 hA).2.1 a
    refine ⟨toLex (Sum.inl a'),
      (bfEquiv_iff_forall_cmpCell γ _ _).2 ⟨sameAtomicType_snoc_elim0 _ _, fun τ => ?_⟩⟩
    exact (ih _ _ _ _ (((bfEquiv_iff_forall_cmpCell γ _ _).1 ha).2 τ)
      (bfEquiv_setOf_const (hB.mono le_self_add) _)).orderIso_congr
        (cmpCellInlOrderIso a τ).symm (cmpCellInlOrderIso a' τ).symm
  · obtain ⟨b', hb⟩ := ((BFEquiv.add_one γ _ _).1 hB).2.1 b
    refine ⟨toLex (Sum.inr b'),
      (bfEquiv_iff_forall_cmpCell γ _ _).2 ⟨sameAtomicType_snoc_elim0 _ _, fun τ => ?_⟩⟩
    exact (ih _ _ _ _ (bfEquiv_setOf_const (hA.mono le_self_add) _)
      (((bfEquiv_iff_forall_cmpCell γ _ _).1 hb).2 τ)).orderIso_congr
        (cmpCellInrOrderIso b τ).symm (cmpCellInrOrderIso b' τ).symm

/-- Back-and-forth equivalence of ordered sums, by induction on the level. -/
private theorem sumLexStatement (γ : Ordinal.{o}) : SumLexStatement.{u₁, u₂, u₃, u₄} γ := by
  induction γ using Ordinal.limitRecOn with
  | zero =>
    intro A A' B B' _ _ _ _ _ _
    exact BFEquiv.zero.2 sameAtomicType_elim0
  | add_one γ ih =>
    intro A A' B B' _ _ _ _ hA hB
    refine (BFEquiv.add_one γ _ _).2 ⟨ih _ _ _ _ (hA.mono le_self_add) (hB.mono le_self_add),
      ih.forth hA hB, fun z' => ?_⟩
    obtain ⟨z, hz⟩ := ih.swap.forth hA.symm hB.symm z'
    exact ⟨z, hz.symm⟩
  | limit γ hγ ih =>
    intro A A' B B' _ _ _ _ hA hB
    exact (BFEquiv.limit hγ _ _).2 fun β hβ => ih β hβ _ _ _ _
      ((BFEquiv.limit hγ _ _).1 hA β hβ) ((BFEquiv.limit hγ _ _).1 hB β hβ)

/-- **Ordered sums.** If `A` and `A'`, and `B` and `B'`, are back-and-forth equivalent at level
`γ` as linear orders, then so are the ordered sums `A ⊕ₗ B` and `A' ⊕ₗ B'`. -/
theorem BFEquiv.sumLex {A' : Type u₂} {B' : Type u₄} [LinearOrder A'] [LinearOrder B']
    {γ : Ordinal.{o}}
    (hA : BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A'))
    (hB : BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → B) (Fin.elim0 : Fin 0 → B')) :
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → A ⊕ₗ B)
      (Fin.elim0 : Fin 0 → A' ⊕ₗ B') :=
  sumLexStatement γ A A' B B' hA hB

end SumLex

end TauCeti
