/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.LinearOrder
public import TauCeti.Order.Sum.Order
public import Mathlib.Order.Hom.Set

/-!
# Back-and-forth equivalence of linear orders, interval by interval

For linear orders, read as structures in the language of orders through Mathlib's
`FirstOrder.Language.orderStructure`, back-and-forth equivalence of tuples is local: two tuples of
the same atomic type are back-and-forth equivalent at level `γ` exactly when the intervals they cut
out of their orders are pairwise back-and-forth equivalent at level `γ`. The intervals are indexed
by comparison patterns. For a tuple `a : Fin n → M` and `σ : Fin n → Ordering`, the cell
`cmpCell a σ` is the set of points `z` with `cmp (a i) z = σ i` for every `i`. Listing the
distinct entries of `a` in increasing order, the cells are the open intervals between consecutive
entries (including the two unbounded ones), the singletons of the entries, and empty sets; two
tuples of the same atomic type have empty and singleton cells at the same patterns, so quantifying
over all patterns is the same as quantifying over the open intervals.

As a consequence, back-and-forth equivalence at level `γ` is compatible with ordered sums: if
`A` is equivalent to `A'` and `B` to `B'`, then `A ⊕ₗ B` is equivalent to `A' ⊕ₗ B'`. These are
the tools for computing back-and-forth levels of well-orders, such as the equivalence of the
ordinals `ω ^ γ * δ` and `ω ^ γ * ε` at level `γ` for nonzero `δ` and `ε`.

## Main definitions

* `TauCeti.cmpCell a σ`: the points of a linear order whose comparisons with the entries of the
  tuple `a` are prescribed by `σ`.

## Main results

* `TauCeti.bfEquiv_iff_forall_cmpCell`: the interval lemma.
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

section Cell

variable {M : Type w} {N : Type w'} [LinearOrder M] [LinearOrder N] {n : ℕ}

/-- The cell of the comparison pattern `σ` for the tuple `a`: the points `z` with
`cmp (a i) z = σ i` for every `i`. -/
def cmpCell (a : Fin n → M) (σ : Fin n → Ordering) : Set M :=
  {z | ∀ i, cmp (a i) z = σ i}

@[simp]
theorem mem_cmpCell {a : Fin n → M} {σ : Fin n → Ordering} {z : M} :
    z ∈ cmpCell a σ ↔ ∀ i, cmp (a i) z = σ i :=
  Iff.rfl

/-- The empty tuple has a single cell, the whole order. -/
@[simp]
theorem cmpCell_fin_zero (a : Fin 0 → M) (σ : Fin 0 → Ordering) : cmpCell a σ = Set.univ := by
  ext z
  simp

/-- The cells of an extended tuple are the cells of the original tuple cut by the new point. -/
theorem mem_cmpCell_snoc {a : Fin n → M} {x z : M} {σ : Fin (n + 1) → Ordering} :
    z ∈ cmpCell (snoc a x) σ ↔ z ∈ cmpCell a (init σ) ∧ cmp x z = σ (last n) := by
  simp [forall_fin_succ', init]

/-- The cells of a single point `x` are cut out by the comparison with `x`. -/
theorem mem_cmpCell_snoc_elim0 {x z : M} {τ : Fin 1 → Ordering} :
    z ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ ↔ cmp x z = τ (last 0) := by
  rw [mem_cmpCell_snoc, cmpCell_fin_zero]
  exact and_iff_right (Set.mem_univ z)

/-- Cells pull back along strictly monotone maps: `f z` lies in the cell of `f ∘ a` for `σ`
exactly when `z` lies in the cell of `a` for `σ`. -/
theorem _root_.StrictMono.mem_cmpCell_comp {f : M → N} (hf : StrictMono f) {a : Fin n → M}
    {σ : Fin n → Ordering} {z : M} : f z ∈ cmpCell (f ∘ a) σ ↔ z ∈ cmpCell a σ := by
  simp only [mem_cmpCell, Function.comp_apply, hf.cmp_map_eq]

/-- The cells of a single point pull back along strictly monotone maps. -/
theorem _root_.StrictMono.mem_cmpCell_snoc_elim0 {f : M → N} (hf : StrictMono f) {x z : M}
    {τ : Fin 1 → Ordering} :
    f z ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → N) (f x)) τ ↔
      z ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ := by
  rw [← hf.mem_cmpCell_comp, comp_snoc, Subsingleton.elim (f ∘ Fin.elim0) Fin.elim0]

/-- The cell of a single point `x` below it is `Set.Iio x`. -/
theorem cmpCell_snoc_elim0_of_gt {x : M} {τ : Fin 1 → Ordering} (h : τ (last 0) = .gt) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ = Set.Iio x := by
  ext z
  rw [mem_cmpCell_snoc_elim0, h, cmp_eq_gt_iff, Set.mem_Iio]

/-- The cell of a single point `x` at it is `{x}`. -/
theorem cmpCell_snoc_elim0_of_eq {x : M} {τ : Fin 1 → Ordering} (h : τ (last 0) = .eq) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ = {x} := by
  ext z
  rw [mem_cmpCell_snoc_elim0, h, cmp_eq_eq_iff, Set.mem_singleton_iff, eq_comm]

/-- The cell of a single point `x` above it is `Set.Ioi x`. -/
theorem cmpCell_snoc_elim0_of_lt {x : M} {τ : Fin 1 → Ordering} (h : τ (last 0) = .lt) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → M) x) τ = Set.Ioi x := by
  ext z
  rw [mem_cmpCell_snoc_elim0, h, cmp_eq_lt_iff, Set.mem_Ioi]

/-- Every point lies in the cell of its own comparison pattern. -/
theorem mem_cmpCell_cmp (a : Fin n → M) (x : M) : x ∈ cmpCell a (fun i => cmp (a i) x) :=
  fun _ => rfl

end Cell

/-! ### The interval lemma -/

section IntervalLemma

variable {M : Type w} {N : Type w'} [LinearOrder M] [LinearOrder N] {n : ℕ}

/-- The comparison of `x` with `z` when `x` and `z` compare with a third point `w` as `s₀` and
`s`, with `s ≠ s₀`. -/
private def cmpOfNe : Ordering → Ordering → Ordering
  | .lt, .eq | .lt, .gt | .eq, .gt => .gt
  | .eq, .lt | .gt, .lt | .gt, .eq => .lt
  | _, _ => .eq

/-- If `x` and `z` compare differently with `w`, their own comparison is determined by these two
comparisons. -/
private theorem cmp_eq_cmpOfNe {w x z : M} (h : cmp w z ≠ cmp w x) :
    cmp x z = cmpOfNe (cmp w x) (cmp w z) := by
  cases hwx : cmp w x <;> cases hwz : cmp w z <;>
    simp_all only [ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true, cmp_eq_lt_iff,
      cmp_eq_eq_iff, cmp_eq_gt_iff, cmpOfNe] <;>
    first | exact hwz.trans hwx | exact hwx.trans hwz

/-- Off the cell of `x`, a cell of `snoc a x` is a whole cell of `a` or empty, according to a rule
that only depends on the comparison patterns. -/
private theorem cmpCell_snoc_snoc_of_ne {a : Fin n → M} {x : M} {σ₀ σ : Fin n → Ordering}
    {o : Ordering} {i : Fin n} (hx : x ∈ cmpCell a σ₀) (hi : σ i ≠ σ₀ i) :
    cmpCell (snoc a x) (snoc σ o) = if cmpOfNe (σ₀ i) (σ i) = o then cmpCell a σ else ∅ := by
  have hcmp {z : M} (hz : z ∈ cmpCell a σ) : cmp x z = cmpOfNe (σ₀ i) (σ i) := by
    rw [cmp_eq_cmpOfNe (by rwa [hz i, hx i]), hz i, hx i]
  ext z
  rw [mem_cmpCell_snoc, init_snoc, snoc_last]
  split_ifs with h
  · exact ⟨And.left, fun hz => ⟨hz, (hcmp hz).trans h⟩⟩
  · exact iff_of_false (fun hz => h ((hcmp hz.1).symm.trans hz.2)) id

/-- Inside the cell `cmpCell a σ`, the cells of a point `p` are the cells of `snoc a p`. -/
private def cmpCellSnocOrderIso (a : Fin n → M) (σ : Fin n → Ordering) (p : cmpCell a σ)
    (τ : Fin 1 → Ordering) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → cmpCell a σ) p) τ ≃o
      cmpCell (snoc a (p : M)) (snoc σ (τ (last 0))) where
  toFun z := ⟨z.val.val, mem_cmpCell_snoc.2 ⟨by rw [init_snoc]; exact z.val.property, by
    rw [snoc_last]
    exact mem_cmpCell_snoc_elim0.1
      ((Subtype.strictMono_coe _).mem_cmpCell_snoc_elim0.2 z.property)⟩⟩
  invFun z := ⟨⟨z.val, by simpa using (mem_cmpCell_snoc.1 z.property).1⟩,
    (Subtype.strictMono_coe _).mem_cmpCell_snoc_elim0.1 <|
      mem_cmpCell_snoc_elim0.2 (by simpa using (mem_cmpCell_snoc.1 z.property).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

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
  have hq : y ∈ cmpCell b σ := fun i =>
    ((sameAtomicType_snoc_iff_cmp.1 hs).2 i).symm.trans (p.property i)
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
    ⟨sameAtomicType_snoc_iff_cmp.2 ⟨hs, fun i => (hx i).trans (q.property i).symm⟩,
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

/-- The cells of a point of the left summand. -/
private def cmpCellInlOrderIso (a : A) (τ : Fin 1 → Ordering) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inl a))) τ ≃o
      cmpCell (snoc (Fin.elim0 : Fin 0 → A) a) τ ⊕ₗ {_b : B | Ordering.lt = τ (last 0)} :=
  let s := cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inl a))) τ
  OrderIso.subtypeSumLex.trans <| OrderIso.sumLexCongr
    (Set.orderIsoOfEq {x | toLex (Sum.inl x) ∈ s} _ <| Set.ext fun _ =>
      Sum.Lex.inl_strictMono.mem_cmpCell_snoc_elim0 (x := a))
    (Set.orderIsoOfEq {y | toLex (Sum.inr y) ∈ s} _ <| Set.ext fun y => by
      simp only [s, Set.mem_ofPred_eq, mem_cmpCell_snoc_elim0, (Sum.Lex.inl_lt_inr a y).cmp_eq_lt])

/-- The cells of a point of the right summand. -/
private def cmpCellInrOrderIso (b : B) (τ : Fin 1 → Ordering) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inr b))) τ ≃o
      {_a : A | Ordering.gt = τ (last 0)} ⊕ₗ cmpCell (snoc (Fin.elim0 : Fin 0 → B) b) τ :=
  let s := cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inr b))) τ
  OrderIso.subtypeSumLex.trans <| OrderIso.sumLexCongr
    (Set.orderIsoOfEq {x | toLex (Sum.inl x) ∈ s} _ <| Set.ext fun x => by
      simp only [s, Set.mem_ofPred_eq, mem_cmpCell_snoc_elim0, (Sum.Lex.inl_lt_inr x b).cmp_eq_gt])
    (Set.orderIsoOfEq {y | toLex (Sum.inr y) ∈ s} _ <| Set.ext fun _ =>
      Sum.Lex.inr_strictMono.mem_cmpCell_snoc_elim0 (x := b))

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
