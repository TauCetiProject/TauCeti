/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.LinearAlgebra.LinearIndependent.Card
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Counting surjective linear maps over finite fields

`TauCeti.natCard_linearMap_surjective` counts surjective `LinearMap`s between finite-dimensional
vector spaces. Taking the target to be a prescribed column space gives the
number of matrices with that image. The coordinate equivalence is Mathlib's `Matrix.toLin`, and
`TauCeti.natCard_linearIndependent` gives the independent-row count.
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
  rw [Nat.card_congr (e.symm.trans rows), natCard_linearIndependent, finrank_fin_fun]

end TauCeti
