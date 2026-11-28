/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Counting linearly independent families in finite vector spaces

`TauCeti.natCard_linearIndependent` extends Mathlib's `card_linearIndependent` to arbitrary finite
index types and all family lengths. This counts independent rows even when a matrix has too many
rows to have full row rank.
-/

public section

namespace TauCeti

open Module

/-- The number of independent families indexed by a finite type of size `k` in a finite
`n`-dimensional vector space over a division ring of order `q` is `∏_{i<k} (q^n - q^i)`,
including zero for `n < k`. -/
theorem natCard_linearIndependent (K V : Type*) [DivisionRing K] [Finite K]
    [AddCommGroup V] [Module K V] [Finite V] (ι : Type*) [Finite ι] :
    Nat.card {s : ι → V // LinearIndependent K s} =
      ∏ i : Fin (Nat.card ι), (Nat.card K ^ finrank K V - Nat.card K ^ i.val) := by
  classical
  let e := Finite.equivFin ι
  let reindex := Equiv.piCongrLeft' (fun _ ↦ V) e
  let families := reindex.subtypeEquiv
    (p := fun s ↦ LinearIndependent K s) (q := fun s ↦ LinearIndependent K s)
    (fun s ↦ by
      have h : s ∘ e.symm = reindex s := by
        funext i
        simp only [reindex, Equiv.piCongrLeft'_apply, Function.comp_apply]
      exact (linearIndependent_equiv' (R := K) e.symm h).symm)
  rw [Nat.card_congr families]
  generalize Nat.card ι = k
  let := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)]
  rcases le_or_gt k (finrank K V) with hk | hk
  · exact card_linearIndependent hk
  · have hempty : IsEmpty {s : Fin k → V // LinearIndependent K s} :=
      ⟨fun s ↦ hk.not_ge ((Fintype.card_fin k).symm.trans_le s.property.fintype_card_le_finrank)⟩
    rw [Nat.card_eq_zero.mpr (.inl hempty)]
    exact (Finset.prod_eq_zero (Finset.mem_univ (⟨_, hk⟩ : Fin k)) (Nat.sub_self _)).symm

end TauCeti
