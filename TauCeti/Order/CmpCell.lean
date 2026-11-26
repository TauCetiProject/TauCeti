/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Hom.Set
public import TauCeti.Order.Compare
public import TauCeti.Order.Sum.Order

/-!
# Cells of comparison patterns

For a tuple `a : Fin n → M` of points of a linear order and a comparison pattern
`σ : Fin n → Ordering`, the cell `TauCeti.cmpCell a σ` is the set of points `z` with
`cmp (a i) z = σ i` for every `i`. Listing the distinct entries of `a` in increasing order, the
cells are the open intervals between consecutive entries (including the two unbounded ones), the
singletons of the entries, and empty sets.

## Main definitions

* `TauCeti.cmpCell a σ`: the points of a linear order whose comparisons with the entries of the
  tuple `a` are prescribed by `σ`.

## Main results

* `TauCeti.mem_cmpCell_snoc`: the cells of an extended tuple are the cells of the original tuple
  cut by the new point.
* `TauCeti.cmpCell_snoc_elim0_of_gt`, `TauCeti.cmpCell_snoc_elim0_of_eq`,
  `TauCeti.cmpCell_snoc_elim0_of_lt`: the cells of a single point `x` are `Set.Iio x`, `{x}` and
  `Set.Ioi x`.
* `StrictMono.mem_cmpCell_comp`: cells pull back along strictly monotone maps.
* `TauCeti.cmpCell_snoc_snoc_of_ne`: off the cell of the new point, a cell of an extended tuple is
  a whole cell of the original tuple or empty.
* `TauCeti.cmpCellSnocOrderIso`: inside a cell of `a`, the cells of a point `p` are the cells of
  `snoc a p`.
* `TauCeti.cmpCellInlOrderIso`, `TauCeti.cmpCellInrOrderIso`: the cells of a point of `A ⊕ₗ B`
  are ordered sums of a cell of that point in its summand and the other summand or `∅`.
-/

public section

universe w w'

namespace TauCeti

open Fin

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

/-- Off the cell of `x`, a cell of `snoc a x` is a whole cell of `a` or empty, according to a rule
that only depends on the comparison patterns. -/
theorem cmpCell_snoc_snoc_of_ne {a : Fin n → M} {x : M} {σ₀ σ : Fin n → Ordering}
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
def cmpCellSnocOrderIso (a : Fin n → M) (σ : Fin n → Ordering) (p : cmpCell a σ)
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

/-- `cmpCellSnocOrderIso` does not change the underlying point. -/
@[simp]
theorem coe_cmpCellSnocOrderIso_apply (a : Fin n → M) (σ : Fin n → Ordering) (p : cmpCell a σ)
    (τ : Fin 1 → Ordering) (z : cmpCell (snoc (Fin.elim0 : Fin 0 → cmpCell a σ) p) τ) :
    (cmpCellSnocOrderIso a σ p τ z : M) = z.val.val :=
  (rfl)

/-- The inverse of `cmpCellSnocOrderIso` does not change the underlying point. -/
@[simp]
theorem coe_coe_cmpCellSnocOrderIso_symm_apply (a : Fin n → M) (σ : Fin n → Ordering)
    (p : cmpCell a σ) (τ : Fin 1 → Ordering) (z : cmpCell (snoc a (p : M)) (snoc σ (τ (last 0)))) :
    ((cmpCellSnocOrderIso a σ p τ).symm z : M) = z.val :=
  (rfl)

section SumLex

variable {A : Type*} {B : Type*} [LinearOrder A] [LinearOrder B]

/-- The cells of a point of the left summand of `A ⊕ₗ B`: a cell of the point in `A`, followed by
all of `B` or by nothing. -/
def cmpCellInlOrderIso (a : A) (τ : Fin 1 → Ordering) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inl a))) τ ≃o
      cmpCell (snoc (Fin.elim0 : Fin 0 → A) a) τ ⊕ₗ {_b : B | Ordering.lt = τ (last 0)} :=
  let s := cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inl a))) τ
  OrderIso.subtypeSumLex.trans <| OrderIso.sumLexCongr
    (Set.orderIsoOfEq {x | toLex (Sum.inl x) ∈ s} _ <| Set.ext fun _ =>
      Sum.Lex.inl_strictMono.mem_cmpCell_snoc_elim0 (x := a))
    (Set.orderIsoOfEq {y | toLex (Sum.inr y) ∈ s} _ <| Set.ext fun y => by
      simp only [s, Set.mem_ofPred_eq, mem_cmpCell_snoc_elim0, (Sum.Lex.inl_lt_inr a y).cmp_eq_lt])

/-- The cells of a point of the right summand of `A ⊕ₗ B`: all of `A` or nothing, followed by a
cell of the point in `B`. -/
def cmpCellInrOrderIso (b : B) (τ : Fin 1 → Ordering) :
    cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inr b))) τ ≃o
      {_a : A | Ordering.gt = τ (last 0)} ⊕ₗ cmpCell (snoc (Fin.elim0 : Fin 0 → B) b) τ :=
  let s := cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inr b))) τ
  OrderIso.subtypeSumLex.trans <| OrderIso.sumLexCongr
    (Set.orderIsoOfEq {x | toLex (Sum.inl x) ∈ s} _ <| Set.ext fun x => by
      simp only [s, Set.mem_ofPred_eq, mem_cmpCell_snoc_elim0, (Sum.Lex.inl_lt_inr x b).cmp_eq_gt])
    (Set.orderIsoOfEq {y | toLex (Sum.inr y) ∈ s} _ <| Set.ext fun _ =>
      Sum.Lex.inr_strictMono.mem_cmpCell_snoc_elim0 (x := b))

/-- `cmpCellInlOrderIso` sends a point of the left summand to the same point of `A`. -/
@[simp]
theorem cmpCellInlOrderIso_apply_inl (a x : A) (τ : Fin 1 → Ordering)
    (h : toLex (Sum.inl x) ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inl a))) τ) :
    cmpCellInlOrderIso a τ ⟨toLex (Sum.inl x), h⟩ =
      toLex (Sum.inl ⟨x, Sum.Lex.inl_strictMono.mem_cmpCell_snoc_elim0.1 h⟩) :=
  by rw [cmpCellInlOrderIso, OrderIso.trans_apply, OrderIso.subtypeSumLex_apply_inl]; rfl

/-- `cmpCellInlOrderIso` sends a point of the right summand to the same point of `B`. -/
@[simp]
theorem cmpCellInlOrderIso_apply_inr (a : A) (y : B) (τ : Fin 1 → Ordering)
    (h : toLex (Sum.inr y) ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inl a))) τ) :
    cmpCellInlOrderIso a τ ⟨toLex (Sum.inr y), h⟩ =
      toLex (Sum.inr ⟨y, by
        rwa [mem_cmpCell_snoc_elim0, (Sum.Lex.inl_lt_inr a y).cmp_eq_lt] at h⟩) :=
  by rw [cmpCellInlOrderIso, OrderIso.trans_apply, OrderIso.subtypeSumLex_apply_inr]; rfl

/-- `cmpCellInrOrderIso` sends a point of the left summand to the same point of `A`. -/
@[simp]
theorem cmpCellInrOrderIso_apply_inl (b : B) (x : A) (τ : Fin 1 → Ordering)
    (h : toLex (Sum.inl x) ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inr b))) τ) :
    cmpCellInrOrderIso b τ ⟨toLex (Sum.inl x), h⟩ =
      toLex (Sum.inl ⟨x, by
        rwa [mem_cmpCell_snoc_elim0, (Sum.Lex.inl_lt_inr x b).cmp_eq_gt] at h⟩) :=
  by rw [cmpCellInrOrderIso, OrderIso.trans_apply, OrderIso.subtypeSumLex_apply_inl]; rfl

/-- `cmpCellInrOrderIso` sends a point of the right summand to the same point of `B`. -/
@[simp]
theorem cmpCellInrOrderIso_apply_inr (b y : B) (τ : Fin 1 → Ordering)
    (h : toLex (Sum.inr y) ∈ cmpCell (snoc (Fin.elim0 : Fin 0 → A ⊕ₗ B) (toLex (Sum.inr b))) τ) :
    cmpCellInrOrderIso b τ ⟨toLex (Sum.inr y), h⟩ =
      toLex (Sum.inr ⟨y, Sum.Lex.inr_strictMono.mem_cmpCell_snoc_elim0.1 h⟩) :=
  by rw [cmpCellInrOrderIso, OrderIso.trans_apply, OrderIso.subtypeSumLex_apply_inr]; rfl

end SumLex

end TauCeti
