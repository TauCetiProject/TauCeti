/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Precomposing a multilinear map with the product of two adjacent arguments

For a multilinear map `f` in `n` arguments from an algebra `A` and `l < n`, the map
`(a₀, …, aₙ) ↦ f (a₀, …, aₗ aₗ₊₁, …, aₙ)`, which multiplies the adjacent arguments `aₗ` and
`aₗ₊₁` (`Fin.contractNth`), is multilinear in `n + 1` arguments
(`MultilinearMap.compContractNth`): each argument enters exactly one entry of the contracted tuple,
and enters it linearly, either alone or as one factor of the product. Such terms are the product
terms of the Hochschild coboundary and of the `A∞` relations.

## Main definitions

* `MultilinearMap.compContractNth`: the multilinear map
  `a ↦ f (Fin.contractNth l.castSucc (· * ·) a)`.
-/

public section

open Function

namespace MultilinearMap

variable {R A N : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [AddCommMonoid N]
  [Module R N] {n : ℕ}

/-- The entry of the tuple `Fin.contractNth l.castSucc (· * ·) a` in which the argument `aᵢ`
appears: the entry `i` up to the contracted pair, and the entry `i - 1` after it. -/
private def contractNthPos (l : Fin n) (i : Fin (n + 1)) : Fin n :=
  ⟨if (i : ℕ) ≤ l then (i : ℕ) else (i : ℕ) - 1, by
    have := l.isLt; have := i.isLt; split_ifs <;> omega⟩

private theorem val_contractNthPos (l : Fin n) (i : Fin (n + 1)) :
    (contractNthPos l i : ℕ) = if (i : ℕ) ≤ l then (i : ℕ) else (i : ℕ) - 1 :=
  (rfl)

/-- Updating one argument changes only the entry of the contracted tuple in which it appears. -/
private theorem contractNth_update (l : Fin n) (a : Fin (n + 1) → A) (i : Fin (n + 1)) (x : A) :
    Fin.contractNth l.castSucc (· * ·) (update a i x) =
      update (Fin.contractNth l.castSucc (· * ·) a) (contractNthPos l i)
        (Fin.contractNth l.castSucc (· * ·) (update a i x) (contractNthPos l i)) := by
  funext k
  by_cases hk : k = contractNthPos l i
  · rw [hk, update_self]
  · rw [update_of_ne hk]
    have hk' : (k : ℕ) ≠ if (i : ℕ) ≤ l then (i : ℕ) else (i : ℕ) - 1 := fun h =>
      hk (Fin.ext (h.trans (val_contractNthPos l i).symm))
    simp only [Fin.contractNth, Fin.val_castSucc, update_apply, Fin.ext_iff, Fin.val_succ]
    split_ifs at hk' ⊢ <;> first | rfl | omega

/-- The entry of the contracted tuple in which an argument appears is additive in it. -/
private theorem contractNth_update_add (l : Fin n) (a : Fin (n + 1) → A) (i : Fin (n + 1))
    (x y : A) :
    Fin.contractNth l.castSucc (· * ·) (update a i (x + y)) (contractNthPos l i) =
      Fin.contractNth l.castSucc (· * ·) (update a i x) (contractNthPos l i) +
        Fin.contractNth l.castSucc (· * ·) (update a i y) (contractNthPos l i) := by
  simp only [Fin.contractNth, val_contractNthPos, Fin.val_castSucc, update_apply, Fin.ext_iff,
    Fin.val_succ]
  split_ifs <;> first | omega | simp [add_mul, mul_add]

/-- The entry of the contracted tuple in which an argument appears is homogeneous in it. -/
private theorem contractNth_update_smul [IsScalarTower R A A] [SMulCommClass R A A] (l : Fin n)
    (a : Fin (n + 1) → A) (i : Fin (n + 1)) (c : R) (x : A) :
    Fin.contractNth l.castSucc (· * ·) (update a i (c • x)) (contractNthPos l i) =
      c • Fin.contractNth l.castSucc (· * ·) (update a i x) (contractNthPos l i) := by
  simp only [Fin.contractNth, val_contractNthPos, Fin.val_castSucc, update_apply, Fin.ext_iff,
    Fin.val_succ]
  split_ifs <;> first | omega | simp [smul_mul_assoc, mul_smul_comm]

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The multilinear map `(a₀, …, aₙ) ↦ f (a₀, …, aₗ aₗ₊₁, …, aₙ)` in `n + 1` arguments, which
multiplies the adjacent arguments `aₗ` and `aₗ₊₁` before applying `f`. -/
def compContractNth (f : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) N) (l : Fin n) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) N where
  toFun a := f (Fin.contractNth l.castSucc (· * ·) a)
  map_update_add' := by
    intro _ a i x y
    obtain rfl : ‹DecidableEq (Fin (n + 1))› = instDecidableEqFin _ := Subsingleton.elim _ _
    rw [contractNth_update, contractNth_update_add, f.map_update_add, ← contractNth_update,
      ← contractNth_update]
  map_update_smul' := by
    intro _ a i c x
    obtain rfl : ‹DecidableEq (Fin (n + 1))› = instDecidableEqFin _ := Subsingleton.elim _ _
    rw [contractNth_update, contractNth_update_smul, f.map_update_smul, ← contractNth_update]

@[simp]
theorem compContractNth_apply (f : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) N)
    (l : Fin n) (a : Fin (n + 1) → A) :
    f.compContractNth l a = f (Fin.contractNth l.castSucc (· * ·) a) :=
  (rfl)

end MultilinearMap
