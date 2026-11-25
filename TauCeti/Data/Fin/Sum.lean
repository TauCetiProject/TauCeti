/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate
import TauCeti.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-!
# Finite sums and finite types

`Unit ⊕ Unit` and `Fin 2`, or `Unit ⊕ Unit ⊕ Unit` and `Fin 3`, are the two ways a small index
type arises: one variable per named slot, or one variable per numeral. Translating between them
is pure bookkeeping, needed wherever an object indexed by named slots must be presented against
an API indexed by `Fin n`.

More generally, an embedding of a type `α` into a finite type `β` identifies `β` with the sum of
`α` and a finite complementary type `Fin l`. This packages the standard splitting of a finite
type along the range of an embedding. Likewise, a dependent sum of blocks `Fin (m i)` over a
finite index type is equivalent to `Fin n` as soon as the block sizes add up to `n`.

Two copies of a type `ι` are the pairs `(i, 0)` and `(i, 1)` of `ι × Fin 2`. For `ι = Fin n`,
listing these pairs consecutively through `finProdFinEquiv` interleaves the two copies of `Fin n`
into `Fin (n + n)`: the first copy goes to the even positions and the second to the odd ones.

The two `Unit`-sum equivalences are Mathlib's own compositions — `finOneEquiv` on each summand,
then `finSumFinEquiv` — given a name and their evaluation lemmas, so that call sites reindexing a
two- or three-variable object can rewrite rather than unfold them.

## Main declarations

* `TauCeti.unitSumUnitEquivFinTwo`: the equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left
  summand to `0` and the right to `1`.
* `TauCeti.unitSumUnitSumUnitEquivFinThree`: the equivalence `Unit ⊕ Unit ⊕ Unit ≃ Fin 3`,
  sending the outer left summand to `0` and the two inner ones to `1` and `2`.
* `TauCeti.sumEquivProdFinTwo`: the equivalence `ι ⊕ ι ≃ ι × Fin 2`, sending `Sum.inl i` to
  `(i, 0)` and `Sum.inr i` to `(i, 1)`.
* `TauCeti.finSumFinEquivInterleave`: the equivalence `Fin n ⊕ Fin n ≃ Fin (n + n)` sending
  `Sum.inl i` to `2 i` and `Sum.inr i` to `2 i + 1`.
* `Function.Embedding.exists_equiv_sum_fin`: an embedding into a finite type extends to an
  equivalence from the sum with a finite complement.
* `TauCeti.nonempty_sigmaFinEquiv`: blocks `Fin (m i)` whose sizes add up to `n` together form a
  type equivalent to `Fin n`.
* `TauCeti.interleaveIndex`: the embedding `Fin a ⊕ Fin b ↪ Fin (2 * max a b)` placing the left
  summand in the even positions and the right summand in the odd positions.
* `TauCeti.finSumFinInterleaveEquiv`: for `a = b = k` this embedding is the interleaving
  `Fin k ⊕ Fin k ≃ Fin (2 * k)`, `inl t ↦ 2 * t`, `inr t ↦ 2 * t + 1`, with its rotation formulas
  `TauCeti.finRotate_finSumFinInterleaveEquiv_inl` and
  `TauCeti.finRotate_finSumFinInterleaveEquiv_inr`: one step of `finRotate (2 * k)` moves from
  `2 * t` to `2 * t + 1`, and from `2 * t + 1` to the even position of `finRotate k t`.

## Implementation notes

The constructions are implementation details: `Mathlib.Data.Fintype.BigOperators` and
`Mathlib.Data.Fintype.EquivFin` are imported privately rather than re-exported, as is
`TauCeti.Data.Fin.Basic`, which supplies the value formula for `finRotate`. Only the finite sum,
finiteness, equivalence, rotation and embedding interfaces needed by the declaration types are
public; `Mathlib.Logic.Equiv.Fin.Basic`, which provides `finSumFinEquiv`, is re-exported through
`Mathlib.Logic.Equiv.Fin.Rotate`.
-/

public section

namespace Function.Embedding

/-- An embedding `s : α ↪ β` into a finite type extends to an equivalence from `α` together with
a finite complement to `β`. -/
theorem exists_equiv_sum_fin {α β : Type*} [Finite β] (s : α ↪ β) :
    ∃ (l : ℕ) (e : α ⊕ Fin l ≃ β), ∀ a, e (Sum.inl a) = s a := by
  classical
  obtain ⟨l, ⟨f⟩⟩ := Finite.exists_equiv_fin {b : β // b ∉ Set.range s}
  exact ⟨l, (Equiv.sumCongr (Equiv.ofInjective s s.injective) f.symm).trans
    (Equiv.sumCompl (· ∈ Set.range s)), fun a ↦ by simp⟩

end Function.Embedding

namespace TauCeti

/-- The equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left summand to `0` and the right to `1`.

An `Equiv` rather than a bare `Function.Embedding`: injectivity is what turns a coefficient under
a reindexing into an equality rather than a sum over a fibre, but surjectivity is what lets a
statement about *every* `Fin 2` index be pulled back, and both directions are wanted downstream. -/
def unitSumUnitEquivFinTwo : (Unit ⊕ Unit) ≃ Fin 2 :=
  (Equiv.sumCongr finOneEquiv.symm finOneEquiv.symm).trans finSumFinEquiv

@[simp]
theorem unitSumUnitEquivFinTwo_inl : unitSumUnitEquivFinTwo (Sum.inl ()) = 0 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_inr : unitSumUnitEquivFinTwo (Sum.inr ()) = 1 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_symm_zero :
    unitSumUnitEquivFinTwo.symm 0 = Sum.inl () := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_symm_one :
    unitSumUnitEquivFinTwo.symm 1 = Sum.inr () := by decide

/-- The equivalence `Unit ⊕ Unit ≃ Fin 2` iterated on the right, `Unit ⊕ Unit ⊕ Unit ≃ Fin 3`,
sending the outer left summand to `0` and the two inner summands to `1` and `2`.

The nesting is the one a three-variable identity meets: an outer variable together with a pair of
inner ones, matching the shape in which an associativity law names its three slots. -/
def unitSumUnitSumUnitEquivFinThree : (Unit ⊕ Unit ⊕ Unit) ≃ Fin 3 :=
  (Equiv.sumCongr finOneEquiv.symm unitSumUnitEquivFinTwo).trans finSumFinEquiv

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_inl :
    unitSumUnitSumUnitEquivFinThree (Sum.inl ()) = 0 := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_inr_inl :
    unitSumUnitSumUnitEquivFinThree (Sum.inr (Sum.inl ())) = 1 := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_inr_inr :
    unitSumUnitSumUnitEquivFinThree (Sum.inr (Sum.inr ())) = 2 := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_symm_zero :
    unitSumUnitSumUnitEquivFinThree.symm 0 = Sum.inl () := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_symm_one :
    unitSumUnitSumUnitEquivFinThree.symm 1 = Sum.inr (Sum.inl ()) := by decide

@[simp]
theorem unitSumUnitSumUnitEquivFinThree_symm_two :
    unitSumUnitSumUnitEquivFinThree.symm 2 = Sum.inr (Sum.inr ()) := by decide

/-- The equivalence `ι ⊕ ι ≃ ι × Fin 2` identifying the left and right copies of `i` with the
pairs `(i, 0)` and `(i, 1)`. -/
def sumEquivProdFinTwo (ι : Type*) : ι ⊕ ι ≃ ι × Fin 2 where
  toFun := Sum.elim (·, 0) (·, 1)
  invFun p := if p.2 = 0 then .inl p.1 else .inr p.1
  left_inv := by rintro (i | i) <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    fin_cases j <;> simp

variable {ι : Type*}

@[simp]
theorem sumEquivProdFinTwo_inl (i : ι) : sumEquivProdFinTwo ι (.inl i) = (i, 0) := by
  simp [sumEquivProdFinTwo]

@[simp]
theorem sumEquivProdFinTwo_inr (i : ι) : sumEquivProdFinTwo ι (.inr i) = (i, 1) := by
  simp [sumEquivProdFinTwo]

@[simp]
theorem sumEquivProdFinTwo_symm_zero (i : ι) : (sumEquivProdFinTwo ι).symm (i, 0) = .inl i := by
  simp [sumEquivProdFinTwo]

@[simp]
theorem sumEquivProdFinTwo_symm_one (i : ι) : (sumEquivProdFinTwo ι).symm (i, 1) = .inr i := by
  simp [sumEquivProdFinTwo]

/-- The interleaving of two copies of `Fin n` into `Fin (n + n)`: the first copy goes to the even
positions and the second copy to the odd positions, `Sum.inl i ↦ 2 i` and `Sum.inr i ↦ 2 i + 1`
(`TauCeti.val_finSumFinEquivInterleave_inl`, `TauCeti.val_finSumFinEquivInterleave_inr`). It is
`TauCeti.sumEquivProdFinTwo` followed by `finProdFinEquiv`, which lists the pairs `(i, 0)` and
`(i, 1)` consecutively. -/
def finSumFinEquivInterleave (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (n + n) :=
  (sumEquivProdFinTwo (Fin n)).trans (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))

@[simp]
theorem val_finSumFinEquivInterleave_inl {n : ℕ} (i : Fin n) :
    (finSumFinEquivInterleave n (.inl i) : ℕ) = 2 * i := by
  simp [finSumFinEquivInterleave]

@[simp]
theorem val_finSumFinEquivInterleave_inr {n : ℕ} (i : Fin n) :
    (finSumFinEquivInterleave n (.inr i) : ℕ) = 2 * i + 1 := by
  simp [finSumFinEquivInterleave, Nat.add_comm]

/-- A sigma type of finite sets whose cardinalities add up to `n` is equivalent to `Fin n`. -/
theorem nonempty_sigmaFinEquiv {ι : Type*} [Fintype ι] {m : ι → ℕ} {n : ℕ}
    (hn : ∑ i, m i = n) : Nonempty ((Σ i, Fin (m i)) ≃ Fin n) :=
  ⟨Fintype.equivFinOfCardEq (by simpa using hn)⟩

/-- The disjoint even/odd positions for two finite coordinate blocks. -/
def interleaveIndex (a b : ℕ) : Fin a ⊕ Fin b ↪ Fin (2 * max a b) where
  toFun := Sum.elim
    (fun i ↦ ⟨2 * i.val, by have := i.isLt; have := Nat.le_max_left a b; omega⟩)
    (fun i ↦ ⟨2 * i.val + 1, by have := i.isLt; have := Nat.le_max_right a b; omega⟩)
  inj' := by
    rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))

@[simp] theorem interleaveIndex_inl_val (a b : ℕ) (i : Fin a) :
    (interleaveIndex a b (.inl i)).val = 2 * i.val := (rfl)

@[simp] theorem interleaveIndex_inr_val (a b : ℕ) (i : Fin b) :
    (interleaveIndex a b (.inr i)).val = 2 * i.val + 1 := (rfl)

/-- The interleaving of two copies of `Fin k` into `Fin (2 * k)`: `inl t ↦ 2 * t` and
`inr t ↦ 2 * t + 1`. It is the embedding `TauCeti.interleaveIndex k k`, which is onto. -/
def finSumFinInterleaveEquiv (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2 * k) where
  toFun t := Fin.cast (by rw [max_self]) (interleaveIndex k k t)
  invFun s := if s.val % 2 = 0 then .inl ⟨s / 2, by omega⟩ else .inr ⟨s / 2, by omega⟩
  left_inv := by
    rintro (t | t)
    · simp
    · simp [Fin.ext_iff]
      omega
  right_inv s := by
    by_cases h : s.val % 2 = 0 <;> simp [h, Fin.ext_iff] <;> omega

@[simp]
theorem val_finSumFinInterleaveEquiv_inl {k : ℕ} (t : Fin k) :
    (finSumFinInterleaveEquiv k (.inl t) : ℕ) = 2 * t :=
  (rfl)

@[simp]
theorem val_finSumFinInterleaveEquiv_inr {k : ℕ} (t : Fin k) :
    (finSumFinInterleaveEquiv k (.inr t) : ℕ) = 2 * t + 1 :=
  (rfl)

/-- The step after the even position `2 * t` is the odd position `2 * t + 1`. -/
theorem finRotate_finSumFinInterleaveEquiv_inl {k : ℕ} (t : Fin k) :
    finRotate (2 * k) (finSumFinInterleaveEquiv k (.inl t)) =
      finSumFinInterleaveEquiv k (.inr t) := by
  rw [Fin.ext_iff, Fin.coe_finRotate_eq_ite]
  simp only [val_finSumFinInterleaveEquiv_inl, val_finSumFinInterleaveEquiv_inr]
  split_ifs <;> omega

/-- The step after the odd position `2 * t + 1` is the even position of the cyclically next index
`t + 1`. -/
theorem finRotate_finSumFinInterleaveEquiv_inr {k : ℕ} (t : Fin k) :
    finRotate (2 * k) (finSumFinInterleaveEquiv k (.inr t)) =
      finSumFinInterleaveEquiv k (.inl (finRotate k t)) := by
  rw [Fin.ext_iff, Fin.coe_finRotate_eq_ite, val_finSumFinInterleaveEquiv_inl,
    Fin.coe_finRotate_eq_ite]
  simp only [val_finSumFinInterleaveEquiv_inr]
  split_ifs <;> omega

/-- An upper-block and a lower-block index have distinct images under `finSumFinEquiv`. -/
theorem _root_.Fin.finSumFinEquiv_inl_ne_inr {m n : ℕ} (i : Fin m) (j : Fin n) :
    finSumFinEquiv (Sum.inl i) ≠ finSumFinEquiv (Sum.inr j) :=
  finSumFinEquiv.injective.ne Sum.inl_ne_inr

/-- A lower-block and an upper-block index have distinct images under `finSumFinEquiv`. -/
theorem _root_.Fin.finSumFinEquiv_inr_ne_inl {m n : ℕ} (i : Fin n) (j : Fin m) :
    finSumFinEquiv (Sum.inr i) ≠ finSumFinEquiv (Sum.inl j) :=
  finSumFinEquiv.injective.ne Sum.inr_ne_inl

end TauCeti
