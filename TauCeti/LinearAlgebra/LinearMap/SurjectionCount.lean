/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Counting surjective linear maps over finite fields

`TauCeti.natCard_linearMap_surjective` counts surjective `LinearMap`s between finite-dimensional
vector spaces. Taking the target to be a prescribed column space gives the
number of matrices with that image. The coordinate equivalence is Mathlib's `Matrix.toLin`, and
`card_linearIndependent` gives the independent-row count.
-/

public section

namespace TauCeti

open Module

/-- Over a field of order `q`, the number of surjections from a space of dimension `n` to a
space of dimension `r` is `∏_{i<r} (q^n - q^i)`, with subtraction in `ℕ`. -/
theorem natCard_linearMap_surjective (K V W : Type*) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Nat.card {f : V →ₗ[K] W // Function.Surjective f} =
      ∏ i : Fin (finrank K W), (Nat.card K ^ finrank K V - Nat.card K ^ i.val) := by
  classical
  let := Fintype.ofFinite K
  let v := finBasis K V
  let w := finBasis K W
  let e := (Matrix.toLin v w).toEquiv.subtypeEquiv
    (p := fun A ↦ LinearIndependent K A.row) (q := fun f : V →ₗ[K] W ↦ Function.Surjective f)
    (fun A ↦ by
      have hcoords : w.equivFun ∘ Matrix.toLin v w A = A.mulVec ∘ v.equivFun := by
        funext x
        simpa only [Function.comp_apply, Basis.equivFun_apply] using Matrix.repr_toLin v w A x
      rw [← Matrix.mulVec_surjective_iff_linearIndependent_row, LinearEquiv.coe_toEquiv,
        ← Function.Surjective.of_comp_iff _ v.equivFun.surjective, ← hcoords,
        Function.Surjective.of_comp_iff' w.equivFun.bijective])
  let rows := (Matrix.rowEquiv (Fin (finrank K W)) (Fin (finrank K V)) K).subtypeEquiv
    (q := fun s ↦ LinearIndependent K s) (fun A ↦ by rw [Matrix.coe_rowEquiv])
  rw [Nat.card_congr (e.symm.trans rows), Nat.card_eq_fintype_card (α := K)]
  have hd : finrank K (Fin (finrank K V) → K) = finrank K V := by simp
  by_cases h : finrank K W ≤ finrank K V
  · simpa only [hd] using (card_linearIndependent (K := K) (V := Fin (finrank K V) → K)
      (k := finrank K W) (hd.symm ▸ h))
  · have hlt : finrank K V < finrank K W := Nat.lt_of_not_ge h
    have hempty : IsEmpty {s : Fin (finrank K W) → Fin (finrank K V) → K //
        LinearIndependent K s} :=
      ⟨fun s ↦ h ((Fintype.card_fin _).symm.trans_le
        (s.property.fintype_card_le_finrank.trans hd.le))⟩
    rw [Nat.card_eq_zero.mpr (.inl hempty)]
    exact (Finset.prod_eq_zero (Finset.mem_univ (⟨_, hlt⟩ : Fin (finrank K W)))
      (Nat.sub_self (Fintype.card K ^ finrank K V))).symm

end TauCeti
