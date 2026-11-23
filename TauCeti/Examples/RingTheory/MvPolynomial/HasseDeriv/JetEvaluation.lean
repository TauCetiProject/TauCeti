/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FinCases
import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation

/-!
# Worked jet maps in monomial coordinates

These examples compute a rectangular jet matrix in its actual monomial basis and its rank,
exhibit a nonzero kernel element, and reduce a jet row modulo `3`. Repeated nodes and an order
above the polynomial degree test that rows record the prescribed jets rather than just the
points.
-/

open MvPolynomial Finsupp

namespace TauCeti.JetEvaluationExamples

/-- Rows are the value at `0` and the first jet at `1`; columns are `1`, `X`, `X²`, in that order.
The jet matrix `[[1, 0, 0], [0, 1, 2]]` has rank `2`: its minor on the columns of `1` and `X` is
`1`. -/
example :
    let s : Finset (Fin 1 →₀ ℕ) := {0, single 0 1, single 0 2}
    let col (j : Fin 3) : (s : Set (Fin 1 →₀ ℕ)) :=
      ⟨single 0 j, by fin_cases j <;> simp [s]⟩
    let M := (LinearMap.toMatrix (basisRestrictSupport ℤ (s : Set (Fin 1 →₀ ℕ)))
      (Pi.basisFun ℤ (Fin 2))
      (jetEval (s : Set (Fin 1 →₀ ℕ)) ![fun _ ↦ 0, fun _ ↦ 1]
        ![0, single 0 1])).submatrix id col
    M = !![1, 0, 0; 0, 1, 2] ∧ M.rank = 2 := by
  intro s col M
  have hM : M = !![1, 0, 0; 0, 1, 2] := by
    simp only [M]
    rw [toMatrix_jetEval]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [col, eval_monomial, constantCoeff_monomial]
  refine ⟨hM, le_antisymm (Matrix.rank_le_height _) ?_⟩
  rw [hM]
  calc 2 = (Matrix.submatrix !![(1 : ℤ), 0, 0; 0, 1, 2] id ![0, 1]).rank := by
        rw [Matrix.rank_of_det_ne_zero (by simp [Matrix.det_fin_two]), Fintype.card_fin]
    _ ≤ _ := Matrix.rank_submatrix_le _ _ _

/-- The nonzero polynomial `X² - 2X` satisfies both prescribed vanishing conditions. -/
example :
    let s : Finset (Fin 1 →₀ ℕ) := {0, single 0 1, single 0 2}
    let col (j : Fin 3) : (s : Set (Fin 1 →₀ ℕ)) :=
      ⟨single 0 j, by fin_cases j <;> simp [s]⟩
    let f := basisRestrictSupport ℤ _ (col 2) - (2 : ℤ) • basisRestrictSupport ℤ _ (col 1)
    f ≠ 0 ∧ f ∈ LinearMap.ker
      (jetEval (s : Set (Fin 1 →₀ ℕ)) ![fun _ ↦ 0, fun _ ↦ 1] ![0, single 0 1]) := by
  intro s col f
  constructor
  · intro h
    have h := congrArg (fun p : restrictSupport ℤ (s : Set (Fin 1 →₀ ℕ)) ↦
      (basisRestrictSupport ℤ _).repr p (col 2)) h
    simp only [f, map_sub, map_smul, Module.Basis.repr_self, map_zero] at h
    norm_num [col, Finsupp.single_apply, Subtype.ext_iff] at h
  · simp only [LinearMap.mem_ker, f, map_sub, map_smul]
    ext i
    fin_cases i <;> simp only [Pi.sub_apply, Pi.smul_apply, jetEval_apply,
      basisRestrictSupport_apply_coe]
    all_goals simp [col, eval_monomial, constantCoeff_monomial]

/-- Repeated nodes impose their own jet orders: the nonzero `X²` has zero value, first jet,
and third jet at the origin. The third order exceeds every degree in this support. -/
example :
    let s : Finset (Fin 1 →₀ ℕ) := {0, single 0 1, single 0 2}
    let col (j : Fin 3) : (s : Set (Fin 1 →₀ ℕ)) :=
      ⟨single 0 j, by fin_cases j <;> simp [s]⟩
    basisRestrictSupport ℤ _ (col 2) ≠ 0 ∧
      jetEval (s : Set (Fin 1 →₀ ℕ)) (fun _ : Fin 3 ↦ fun _ ↦ (0 : ℤ))
        ![0, single 0 1, single 0 3] (basisRestrictSupport ℤ _ (col 2)) = 0 := by
  intro s col
  constructor
  · exact (basisRestrictSupport ℤ _).ne_zero (col 2)
  · ext i
    simp only [jetEval_apply, basisRestrictSupport_apply_coe]
    fin_cases i <;> simp [col, constantCoeff_monomial, ← single_tsub]

/-- The mixed Hasse jet of `Z W` at `(2, 3)` is one. -/
example : jetMatrix {single (0 : Fin 2) 1 + single 1 1}
    (fun _ : Unit ↦ ![(2 : ℤ), 3]) (fun _ ↦ single 0 1 + single 1 1) () ⟨_, rfl⟩ = 1 := by
  norm_num [jetMatrix_apply, Finsupp.prod_fintype, Fin.prod_univ_two]

/-- Evaluation at the integer `3` has the monomial row `[1, 3]`. -/
example :
    let s : Finset (Fin 1 →₀ ℕ) := {0, single 0 1}
    let col (j : Fin 2) : (s : Set (Fin 1 →₀ ℕ)) :=
      ⟨single 0 j, by fin_cases j <;> simp [s]⟩
    (jetMatrix (s : Set (Fin 1 →₀ ℕ)) (fun _ : Fin 1 ↦ fun _ ↦ (3 : ℤ))
      (fun _ ↦ 0)).submatrix id col = !![1, 3] := by
  intro s col
  ext i j
  fin_cases i; fin_cases j <;> simp [col, eval_monomial]

/-- Reducing coefficients and the point modulo `3` commutes with forming the jet matrix.
The integer row `[1, 3]` becomes `[1, 0]`. -/
example :
    let s : Finset (Fin 1 →₀ ℕ) := {0, single 0 1}
    let col (j : Fin 2) : (s : Set (Fin 1 →₀ ℕ)) :=
      ⟨single 0 j, by fin_cases j <;> simp [s]⟩
    (jetMatrix (s : Set (Fin 1 →₀ ℕ))
      (fun _ : Fin 1 ↦ (Int.castRingHom (ZMod 3)) ∘ fun _ ↦ (3 : ℤ))
      (fun _ ↦ 0)).submatrix id col = !![1, 0] := by
  intro s col
  rw [jetMatrix_map]
  ext i j
  fin_cases i
  fin_cases j
  · simp [col]
  · calc
      _ = (3 : ZMod 3) := by norm_num [col, eval_monomial]
      _ = 0 := rfl

/-- Reducing the coefficient-supported polynomial `X` and its evaluation at `3` commute;
its value in `ℤ / (3)` is zero. -/
example :
    let s : Finset (Fin 1 →₀ ℕ) := {0, single 0 1}
    let col : (s : Set (Fin 1 →₀ ℕ)) := ⟨single 0 1, by simp [s]⟩
    jetEval (s : Set (Fin 1 →₀ ℕ))
      (fun _ : Fin 1 ↦ (Ideal.Quotient.mk (Ideal.span ({3} : Set ℤ))) ∘ fun _ ↦ (3 : ℤ))
      (fun _ ↦ 0)
      (mapRestrictSupport _ (Ideal.Quotient.mk (Ideal.span ({3} : Set ℤ)))
        (basisRestrictSupport ℤ _ col)) = 0 := by
  intro s col
  rw [jetEval_mapRestrictSupport]
  ext i
  simp only [Function.comp_apply, jetEval_apply, basisRestrictSupport_apply_coe]
  simpa [col, eval_monomial] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton (3 : ℤ))))

/-- With no points, every supported polynomial maps to the unique empty vector. -/
example (R σ : Type*) [CommSemiring R] (s : Set (σ →₀ ℕ))
    (a : Fin 0 → σ → R) (d : Fin 0 → σ →₀ ℕ) : jetEval s a d = 0 := by
  exact Subsingleton.elim _ _

end TauCeti.JetEvaluationExamples
