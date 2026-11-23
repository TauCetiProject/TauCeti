/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import TauCeti.Computability.SingleOracle.Code
-- Proving `toSingleOracleCode_prefixDom` requires the private equations of `toSingleOracleCode`.
import all TauCeti.Computability.SingleOracle.Code
import Mathlib.Order.Interval.Finset.Nat
import TauCeti.Data.PFun.Basic

/-!
# Prefix-convergence compilation for programs

Given a program `c`, `TauCeti.Oracle.Single.Code.prefixDom c` runs `c` sequentially on
`0, 1, …, x` by primitive recursion and returns `0` when all of those calls converge, diverging
as soon as any call `k ≤ x` diverges. The compiler is primitive recursive and injective on
program syntax, independently of the oracle, and its exact partial evaluation equation holds even
for partial oracles.

Consequently, the domain of `prefixDom c` is always downward closed in `ℕ`:
* if `c` diverges at some input, the domain of `prefixDom c` is the finite initial segment
  `Set.Iio m` up to the least divergence point `m`;
* if `c` is total relative to the oracle, the domain of `prefixDom c` is `Set.univ`.

In particular, `{x | (eval O (prefixDom c) x).Dom}` is finite if and only if `c` diverges
somewhere, and infinite if and only if `c` is total. `Nat.Partrec.Code.prefixDom` implements the
matching syntax transformation on ordinary query-free Mathlib codes.

## Main definitions

* `TauCeti.Oracle.Single.Code.prefixDom`: prefix-convergence compiler on single-oracle programs.
* `Nat.Partrec.Code.prefixDom`: matching prefix-convergence compiler on ordinary Mathlib codes.

## Main results

* `TauCeti.Oracle.Single.Code.eval_prefixDom`, `TauCeti.Oracle.Single.Code.dom_eval_prefixDom`:
  exact partial semantics and domain characterization for arbitrary partial oracles.
* `TauCeti.Oracle.Single.Code.primrec_prefixDom`, `TauCeti.Oracle.Single.Code.prefixDom_inj`:
  primitive recursiveness and syntactic injectivity.
* `TauCeti.Oracle.Single.Code.exists_dom_eval_prefixDom_eq_Iio`,
  `TauCeti.Oracle.Single.Code.dom_eval_prefixDom_eq_univ_iff`: initial-segment domain dichotomy.
* `TauCeti.Oracle.Single.Code.finite_dom_eval_prefixDom_iff`,
  `TauCeti.Oracle.Single.Code.infinite_dom_eval_prefixDom_iff`: finiteness and infiniteness of the
  compiled domain in terms of divergence or totality of `c`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.3
  (Theorem IV.3.2).
-/

public section

namespace TauCeti.Oracle.Single.Code

/-- Compile a program `c` into a program that on input `x` runs `c` sequentially on `0, 1, …, x`
and outputs `0` when all of those computations halt, diverging otherwise. -/
def prefixDom (c : Code) : Code :=
  comp (prec (comp zero c) (comp zero (comp c (comp succ (comp left right)))))
    (pair zero (pair left right))

/-- The prefix-convergence compiler is primitive recursive on programs. -/
theorem primrec_prefixDom : Primrec prefixDom :=
  primrec₂_comp.comp
    (primrec₂_prec.comp
      (primrec₂_comp.comp (Primrec.const zero) Primrec.id)
      (primrec₂_comp.comp (Primrec.const zero)
        (primrec₂_comp.comp Primrec.id (Primrec.const (comp succ (comp left right))))))
    (Primrec.const (pair zero (pair left right)))

/-- Prefix-convergence compilation retains the source program in its syntax. -/
@[simp]
theorem prefixDom_inj {c d : Code} : prefixDom c = prefixDom d ↔ c = d := by
  constructor
  · intro h
    simp only [prefixDom, Code.comp.injEq, Code.prec.injEq, true_and, and_true] at h
    exact h.1
  · rintro rfl
    rfl

/-- `TauCeti.Oracle.Single.Code.prefixDom` is injective on program syntax. -/
theorem prefixDom_injective : Function.Injective prefixDom :=
  fun _ _ => prefixDom_inj.1

/-- `prefixDom c` outputs `0` on `x` precisely when `c` halts on every `k ≤ x`. -/
theorem mem_eval_prefixDom {O : ℕ →. ℕ} {c : Code} {x y : ℕ} :
    y ∈ eval O (prefixDom c) x ↔ (∀ k ≤ x, (eval O c k).Dom) ∧ y = 0 := by
  have hz : eval O zero = fun _ => Part.some 0 := funext eval_zero
  have hl : eval O left = fun n => Part.some n.unpair.1 := funext eval_left
  have hs : eval O succ = fun n => Part.some (n + 1) := funext eval_succ
  have hbase : eval O (comp zero c) 0 = (eval O c 0).map fun _ => 0 := by
    simp [hz, Part.bind_some_eq_map]
  have hstep (k i : ℕ) :
      eval O (comp zero (comp c (comp succ (comp left right)))) (Nat.pair 0 (Nat.pair k i)) =
        (eval O c (k + 1)).map fun _ => 0 := by
    simp [hz, hl, hs, PFun.some_bind, Part.bind_some_eq_map]
  rw [prefixDom, eval_comp, eval_pair_zero_left_right, PFun.some_bind]
  induction x generalizing y with
  | zero =>
    rw [eval_prec_zero, hbase, Part.mem_map_iff]
    simp [Part.dom_iff_mem, eq_comm]
  | succ x ih =>
    rw [eval_prec_succ]
    refine (Part.mem_bind_iff).trans ?_
    constructor
    · rintro ⟨i, hi, hy⟩
      obtain ⟨hprev, rfl⟩ := ih.1 hi
      rw [hstep, Part.mem_map_iff] at hy
      obtain ⟨z, hz', hy⟩ := hy
      refine ⟨fun k hk => ?_, hy.symm⟩
      rcases Nat.of_le_succ hk with hle | rfl
      · exact hprev k hle
      · exact Part.dom_iff_mem.2 ⟨z, hz'⟩
    · rintro ⟨hall, rfl⟩
      obtain ⟨z, hz'⟩ := Part.dom_iff_mem.1 (hall (x + 1) le_rfl)
      refine ⟨0, ih.2 ⟨fun k hk => hall k (Nat.le_succ_of_le hk), rfl⟩, ?_⟩
      rw [hstep, Part.mem_map_iff]
      exact ⟨z, hz', rfl⟩

/-- Exact partial evaluation of `prefixDom c`, uniformly for every partial oracle. -/
theorem eval_prefixDom (O : ℕ →. ℕ) (c : Code) (x : ℕ) :
    eval O (prefixDom c) x = Part.assert (∀ k ≤ x, (eval O c k).Dom) fun _ => Part.some 0 := by
  ext y
  simp [mem_eval_prefixDom, Part.mem_assert_iff]

/-- `prefixDom c` halts on `x` if and only if `c` halts on every `k ≤ x`. -/
@[simp]
theorem dom_eval_prefixDom (O : ℕ →. ℕ) (c : Code) (x : ℕ) :
    (eval O (prefixDom c) x).Dom ↔ ∀ k ≤ x, (eval O c k).Dom := by
  simp [eval_prefixDom, Part.assert]

/-- The domain of `prefixDom c` is downward closed. -/
theorem dom_eval_prefixDom_of_le {O : ℕ →. ℕ} {c : Code} {x y : ℕ} (hxy : x ≤ y)
    (hy : (eval O (prefixDom c) y).Dom) : (eval O (prefixDom c) x).Dom :=
  (dom_eval_prefixDom O c x).2 fun k hk =>
    (dom_eval_prefixDom O c y).1 hy k (hk.trans hxy)

/-- If `c` diverges at some input relative to `O`, then the domain of `prefixDom c` is the finite
initial segment `Set.Iio m` below the first divergence point `m`. -/
theorem exists_dom_eval_prefixDom_eq_Iio {O : ℕ →. ℕ} {c : Code}
    (h : ∃ k, ¬(eval O c k).Dom) :
    ∃ m, ¬(eval O c m).Dom ∧ (∀ k < m, (eval O c k).Dom) ∧
      {x | (eval O (prefixDom c) x).Dom} = Set.Iio m := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun k hk => not_not.1 (Nat.find_min h hk), ?_⟩
  ext x
  simp only [Set.mem_ofPred, dom_eval_prefixDom, Set.mem_Iio]
  constructor
  · intro hx
    by_contra hge
    exact Nat.find_spec h (hx (Nat.find h) (not_lt.1 hge))
  · exact fun hx k hk => not_not.1 (Nat.find_min h (lt_of_le_of_lt hk hx))

/-- The domain of `prefixDom c` is all of `ℕ` if and only if `c` is total relative to `O`. -/
theorem dom_eval_prefixDom_eq_univ_iff {O : ℕ →. ℕ} {c : Code} :
    {x | (eval O (prefixDom c) x).Dom} = Set.univ ↔ ∀ k, (eval O c k).Dom := by
  simp only [Set.eq_univ_iff_forall, Set.mem_ofPred, dom_eval_prefixDom]
  exact ⟨fun h k => h k k le_rfl, fun h x k _ => h k⟩

/-- The domain of `prefixDom c` is finite if and only if `c` diverges at some input. -/
theorem finite_dom_eval_prefixDom_iff {O : ℕ →. ℕ} {c : Code} :
    {x | (eval O (prefixDom c) x).Dom}.Finite ↔ ∃ k, ¬(eval O c k).Dom := by
  classical
  constructor
  · intro hfin
    by_contra! hall
    exact Set.infinite_univ ((dom_eval_prefixDom_eq_univ_iff.2 hall) ▸ hfin)
  · intro h
    obtain ⟨m, -, -, heq⟩ := exists_dom_eval_prefixDom_eq_Iio h
    exact heq ▸ Set.finite_Iio m

/-- The domain of `prefixDom c` is infinite if and only if `c` halts on every input. -/
theorem infinite_dom_eval_prefixDom_iff {O : ℕ →. ℕ} {c : Code} :
    {x | (eval O (prefixDom c) x).Dom}.Infinite ↔ ∀ k, (eval O c k).Dom := by
  classical
  rw [Set.Infinite, finite_dom_eval_prefixDom_iff, not_exists_not]

end TauCeti.Oracle.Single.Code

/-! ### Query-free prefix-convergence compilation -/

namespace Nat.Partrec.Code

/-- Compile an ordinary code `c` into a code that on input `x` runs `c` sequentially on
`0, 1, …, x` and outputs `0` when all of those computations halt, diverging otherwise. -/
def prefixDom (c : Nat.Partrec.Code) : Nat.Partrec.Code :=
  comp (prec (comp zero c) (comp zero (comp c (comp succ (comp left right)))))
    (pair zero (pair left right))

/-- Prefix-convergence compilation on ordinary codes is primitive recursive. -/
theorem primrec_prefixDom : Primrec prefixDom :=
  primrec₂_comp.comp
    (primrec₂_prec.comp
      (primrec₂_comp.comp (_root_.Primrec.const zero) _root_.Primrec.id)
      (primrec₂_comp.comp (_root_.Primrec.const zero)
        (primrec₂_comp.comp _root_.Primrec.id
          (_root_.Primrec.const (comp succ (comp left right))))))
    (_root_.Primrec.const (pair zero (pair left right)))

/-- Prefix-convergence compilation on ordinary codes retains the source code in its syntax. -/
@[simp]
theorem prefixDom_inj {c d : Nat.Partrec.Code} : c.prefixDom = d.prefixDom ↔ c = d := by
  constructor
  · intro h
    simp only [prefixDom, comp.injEq, prec.injEq, true_and, and_true] at h
    exact h.1
  · rintro rfl
    rfl

/-- `Nat.Partrec.Code.prefixDom` is injective on code syntax. -/
theorem prefixDom_injective : Function.Injective prefixDom :=
  fun _ _ => prefixDom_inj.1

/-- Translating `c.prefixDom` into a query-free single-oracle program yields the single-oracle
prefix-convergence compilation of `c.toSingleOracleCode`. -/
@[simp]
theorem toSingleOracleCode_prefixDom (c : Nat.Partrec.Code) :
    c.prefixDom.toSingleOracleCode = c.toSingleOracleCode.prefixDom := by
  simp only [prefixDom, TauCeti.Oracle.Single.Code.prefixDom, toSingleOracleCode]

/-- Relative to every oracle, `c.prefixDom` and `c.toSingleOracleCode.prefixDom` compute the same
partial function. -/
@[simp]
theorem eval_toSingleOracleCode_prefixDom (O : ℕ →. ℕ) (c : Nat.Partrec.Code) :
    TauCeti.Oracle.Single.Code.eval O c.toSingleOracleCode.prefixDom = c.prefixDom.eval := by
  rw [← toSingleOracleCode_prefixDom, TauCeti.Oracle.Single.Code.eval_toSingleOracleCode]

/-- `c.prefixDom` outputs `0` on `x` precisely when `c` halts on every `k ≤ x`. -/
theorem mem_eval_prefixDom {c : Nat.Partrec.Code} {x y : ℕ} :
    y ∈ c.prefixDom.eval x ↔ (∀ k ≤ x, (c.eval k).Dom) ∧ y = 0 := by
  rw [← eval_toSingleOracleCode_prefixDom default,
    ← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default]
  exact TauCeti.Oracle.Single.Code.mem_eval_prefixDom

/-- Exact partial evaluation of `c.prefixDom` for an ordinary code `c`. -/
theorem eval_prefixDom (c : Nat.Partrec.Code) (x : ℕ) :
    c.prefixDom.eval x = Part.assert (∀ k ≤ x, (c.eval k).Dom) fun _ => Part.some 0 := by
  rw [← eval_toSingleOracleCode_prefixDom default,
    ← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default]
  exact TauCeti.Oracle.Single.Code.eval_prefixDom default c.toSingleOracleCode x

/-- `c.prefixDom` halts on `x` if and only if `c` halts on every `k ≤ x`. -/
@[simp]
theorem dom_eval_prefixDom (c : Nat.Partrec.Code) (x : ℕ) :
    (c.prefixDom.eval x).Dom ↔ ∀ k ≤ x, (c.eval k).Dom := by
  rw [← eval_toSingleOracleCode_prefixDom default,
    ← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default]
  exact TauCeti.Oracle.Single.Code.dom_eval_prefixDom default c.toSingleOracleCode x

/-- The domain of `c.prefixDom` is downward closed. -/
theorem dom_eval_prefixDom_of_le {c : Nat.Partrec.Code} {x y : ℕ} (hxy : x ≤ y)
    (hy : (c.prefixDom.eval y).Dom) : (c.prefixDom.eval x).Dom := by
  rw [← eval_toSingleOracleCode_prefixDom default] at hy ⊢
  exact TauCeti.Oracle.Single.Code.dom_eval_prefixDom_of_le hxy hy

/-- If `c` diverges at some input, then the domain of `c.prefixDom` is the finite initial segment
`Set.Iio m` below the first divergence point `m`. -/
theorem exists_dom_eval_prefixDom_eq_Iio {c : Nat.Partrec.Code} (h : ∃ k, ¬(c.eval k).Dom) :
    ∃ m, ¬(c.eval m).Dom ∧ (∀ k < m, (c.eval k).Dom) ∧
      {x | (c.prefixDom.eval x).Dom} = Set.Iio m := by
  rw [← eval_toSingleOracleCode_prefixDom default]
  rw [← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default] at h ⊢
  exact TauCeti.Oracle.Single.Code.exists_dom_eval_prefixDom_eq_Iio h

/-- The domain of `c.prefixDom` is all of `ℕ` if and only if `c` is total. -/
theorem dom_eval_prefixDom_eq_univ_iff {c : Nat.Partrec.Code} :
    {x | (c.prefixDom.eval x).Dom} = Set.univ ↔ ∀ k, (c.eval k).Dom := by
  rw [← eval_toSingleOracleCode_prefixDom default,
    ← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default]
  exact TauCeti.Oracle.Single.Code.dom_eval_prefixDom_eq_univ_iff

/-- The domain of `c.prefixDom` is finite if and only if `c` diverges at some input. -/
theorem finite_dom_eval_prefixDom_iff {c : Nat.Partrec.Code} :
    {x | (c.prefixDom.eval x).Dom}.Finite ↔ ∃ k, ¬(c.eval k).Dom := by
  rw [← eval_toSingleOracleCode_prefixDom default,
    ← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default]
  exact TauCeti.Oracle.Single.Code.finite_dom_eval_prefixDom_iff

/-- The domain of `c.prefixDom` is infinite if and only if `c` halts on every input. -/
theorem infinite_dom_eval_prefixDom_iff {c : Nat.Partrec.Code} :
    {x | (c.prefixDom.eval x).Dom}.Infinite ↔ ∀ k, (c.eval k).Dom := by
  rw [← eval_toSingleOracleCode_prefixDom default,
    ← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode default]
  exact TauCeti.Oracle.Single.Code.infinite_dom_eval_prefixDom_iff

end Nat.Partrec.Code
