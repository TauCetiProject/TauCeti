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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

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

The two `Unit`-sum equivalences are Mathlib's own compositions — `finOneEquiv` on each summand,
then `finSumFinEquiv` — given a name and their evaluation lemmas, so that call sites reindexing a
two- or three-variable object can rewrite rather than unfold them.

## Main declarations

* `TauCeti.unitSumUnitEquivFinTwo`: the equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left
  summand to `0` and the right to `1`.
* `TauCeti.unitSumUnitSumUnitEquivFinThree`: the equivalence `Unit ⊕ Unit ⊕ Unit ≃ Fin 3`,
  sending the outer left summand to `0` and the two inner ones to `1` and `2`.
* `Function.Embedding.exists_equiv_sum_fin`: an embedding into a finite type extends to an
  equivalence from the sum with a finite complement.
* `TauCeti.nonempty_sigmaFinEquiv`: blocks `Fin (m i)` whose sizes add up to `n` together form a
  type equivalent to `Fin n`.

## Implementation notes

The constructions are implementation details: `Mathlib.Data.Fintype.BigOperators`,
`Mathlib.Data.Fintype.EquivFin` and `Mathlib.Logic.Equiv.Fin.Basic` are imported privately rather
than re-exported. Only the finite sum, finiteness, equivalence and embedding interfaces needed by
the declaration types are public.
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

/-- The left block occupies the even positions. -/
@[simp] theorem interleaveIndex_inl_val (a b : ℕ) (i : Fin a) :
    (interleaveIndex a b (.inl i)).val = 2 * i.val := (rfl)

/-- The right block occupies the odd positions. -/
@[simp] theorem interleaveIndex_inr_val (a b : ℕ) (i : Fin b) :
    (interleaveIndex a b (.inr i)).val = 2 * i.val + 1 := (rfl)

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

/-- Equal-sized blocks exhaust the even and odd positions in `Fin (2 * k)`. -/
def interleaveIndexEquiv (k : ℕ) : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
  let e := (Equiv.prodUnique (Fin k) Unit).symm
  (Equiv.sumCongr e e).trans
    ((Equiv.prodSumDistrib (Fin k) Unit Unit).symm.trans
      ((Equiv.prodCongr (Equiv.refl _) unitSumUnitEquivFinTwo).trans
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2)))))

/-- The even position of a left index. -/
@[simp] theorem interleaveIndexEquiv_inl_val {k : ℕ} (i : Fin k) :
    (interleaveIndexEquiv k (.inl i)).val = 2 * i.val :=
  Nat.zero_add _

/-- The odd position of a right index. -/
@[simp] theorem interleaveIndexEquiv_inr_val {k : ℕ} (i : Fin k) :
    (interleaveIndexEquiv k (.inr i)).val = 2 * i.val + 1 := by
  exact Nat.add_comm 1 _

/-- The inverse interleaving reads an even position on the left and an odd position on the right. -/
theorem interleaveIndexEquiv_symm_apply {k : ℕ} (i : Fin (2 * k)) :
    (interleaveIndexEquiv k).symm i =
      if (i : ℕ) % 2 = 0 then .inl ⟨i / 2, by have := i.isLt; omega⟩
      else .inr ⟨i / 2, by have := i.isLt; omega⟩ := by
  apply (interleaveIndexEquiv k).injective
  have := i.isLt
  by_cases h : (i : ℕ) % 2 = 0
  · simp only [Equiv.apply_symm_apply, h, ite_true, Fin.ext_iff, interleaveIndexEquiv_inl_val]
    omega
  · simp only [Equiv.apply_symm_apply, h, ite_false, Fin.ext_iff, interleaveIndexEquiv_inr_val]
    omega

/-- Rotating an even position advances to the odd position of the same index. -/
@[simp high] theorem finRotate_interleaveIndexEquiv_inl {k : ℕ} (i : Fin k) :
    finRotate (2 * k) (interleaveIndexEquiv k (.inl i)) = interleaveIndexEquiv k (.inr i) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    have hi : interleaveIndexEquiv (k + 1) (.inl i) ≠ Fin.last (2 * k + 1) := by
      simp [Fin.ext_iff]
      omega
    apply Fin.ext
    let j := interleaveIndexEquiv (k + 1) (.inl i)
    have hrot : (finRotate (2 * (k + 1)) j).val =
        if j = Fin.last (2 * k + 1) then 0 else j.val + 1 :=
      coe_finRotate j
    rw [hrot, ite_eq_right hi]
    simp only [j, interleaveIndexEquiv_inl_val, interleaveIndexEquiv_inr_val]

/-- Rotating an odd position advances to the even position of the next cyclic index. -/
@[simp high] theorem finRotate_interleaveIndexEquiv_inr {k : ℕ} (i : Fin k) :
    finRotate (2 * k) (interleaveIndexEquiv k (.inr i)) =
      interleaveIndexEquiv k (.inl (finRotate k i)) := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    have hi : interleaveIndexEquiv (k + 1) (.inr i) = Fin.last (2 * k + 1) ↔
        i = Fin.last k := by
      simp only [Fin.ext_iff, interleaveIndexEquiv_inr_val, Fin.val_last]
      omega
    apply Fin.ext
    let j := interleaveIndexEquiv (k + 1) (.inr i)
    have hrot : (finRotate (2 * (k + 1)) j).val =
        if j = Fin.last (2 * k + 1) then 0 else j.val + 1 :=
      coe_finRotate j
    rw [hrot, interleaveIndexEquiv_inl_val, @coe_finRotate k]
    simp only [j, hi, interleaveIndexEquiv_inr_val]
    split <;> omega

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

/-- A sigma type of finite sets whose cardinalities add up to `n` is equivalent to `Fin n`. -/
theorem nonempty_sigmaFinEquiv {ι : Type*} [Fintype ι] {m : ι → ℕ} {n : ℕ}
    (hn : ∑ i, m i = n) : Nonempty ((Σ i, Fin (m i)) ≃ Fin n) :=
  ⟨Fintype.equivFinOfCardEq (by simpa using hn)⟩

end TauCeti
