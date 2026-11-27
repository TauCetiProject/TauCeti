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

`LinearMap.natCard_surjective` counts surjections between finite-dimensional vector spaces.
In coordinates, their matrices have independent rows, so Mathlib's `card_linearIndependent`
gives the count.
-/

public section

namespace LinearMap

open Module

/-- Over a field of order `q`, the number of surjections from a space of dimension `n` to a
space of dimension `r` is `∏_{i<r} (q^n - q^i)`, with subtraction in `ℕ`. -/
theorem natCard_surjective (K V W : Type*) [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Nat.card {f : V →ₗ[K] W // Function.Surjective f} =
      ∏ i : Fin (finrank K W), (Fintype.card K ^ finrank K V - Fintype.card K ^ i.val) := by
  classical
  let v := (finBasis K V).equivFun
  let w := (finBasis K W).equivFun
  let e : (V →ₗ[K] W) ≃ₗ[K] ((Fin (finrank K V) → K) →ₗ[K] (Fin (finrank K W) → K)) :=
    LinearEquiv.arrowCongr v w
  have hcoords (f : V →ₗ[K] W) : Function.Surjective f ↔ Function.Surjective (e f) := by
    have he : (e f : _ → _) = w ∘ f ∘ v.symm := funext (LinearEquiv.arrowCongr_apply v w f)
    rw [he, Function.Surjective.of_comp_iff' w.bijective,
      Function.Surjective.of_comp_iff _ v.symm.surjective]
  let b := (Matrix.toLin' (R := K) (m := Fin (finrank K W)) (n := Fin (finrank K V))).toEquiv
  have hmatrix (A : Matrix (Fin (finrank K W)) (Fin (finrank K V)) K) :
      LinearIndependent K A.row ↔ Function.Surjective (b A) := by
    simpa only [b, LinearEquiv.coe_toEquiv, Matrix.toLin'_apply', Matrix.coe_mulVecLin] using
      (Matrix.mulVec_surjective_iff_linearIndependent_row (A := A)).symm
  let surjectiveCoordinates (f : (Fin (finrank K V) → K) →ₗ[K] (Fin (finrank K W) → K)) :=
    Function.Surjective f
  -- A matrix presented as a function is already its family of rows.
  have hrow (s : Fin (finrank K W) → Fin (finrank K V) → K) :
      LinearIndependent K s ↔ LinearIndependent K (Matrix.of s).row := Iff.rfl
  let rowEquiv := Matrix.of.subtypeEquiv
    (q := fun A : Matrix (Fin (finrank K W)) (Fin (finrank K V)) K ↦ LinearIndependent K A.row) hrow
  rw [Nat.card_congr (e.toEquiv.subtypeEquiv (q := surjectiveCoordinates) hcoords),
    Nat.card_congr (b.subtypeEquiv (q := surjectiveCoordinates) hmatrix).symm,
    Nat.card_congr rowEquiv.symm]
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

end LinearMap
