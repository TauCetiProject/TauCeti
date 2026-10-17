/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block. It also identifies the iterated derivatives at zero of a convergent scalar series over a
complete nontrivially normed field.
-/

public section

open scoped BigOperators

namespace FormalMultilinearSeries

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E] [IsTopologicalRing E]

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions. This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) =
      ofScalars E fun n ↦ ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i) := by
  have prod_ofFn_smul {m : ℕ} (a : Fin m → 𝕜) (b : Fin m → E) :
      (List.ofFn fun i ↦ a i • b i).prod = (∏ i, a i) • (List.ofFn b).prod := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, Fin.prod_univ_succ]
      simp only [List.prod_cons, ih]
      exact smul_mul_smul_comm _ _ _ _
  ext n v
  simp only [FormalMultilinearSeries.comp, ofScalars]
  rw [sum_apply, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hprod :
      (List.ofFn fun i : Fin p.length ↦ (ofScalars E d).applyComposition p v i).prod =
        (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
    simp only [applyComposition, ofScalars, _root_.smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    rw [prod_ofFn_smul]
    congr 1
    have hblocks :
        List.ofFn (fun i : Fin p.length ↦ (List.ofFn (v ∘ p.embedding i)).prod) =
          ((List.ofFn v).splitWrtComposition p).map List.prod := by
      refine List.ext_getElem (by simp) fun i hi₁ hi₂ ↦ ?_
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_splitWrtComposition]
      refine congrArg List.prod (List.ext_getElem ?_ fun j hj₁ hj₂ ↦ by simp; rfl)
      rw [List.length_ofFn, List.length_drop, List.length_take, List.length_ofFn,
        Nat.min_eq_left (p.sizeUpTo_le _), p.sizeUpTo_succ' ⟨i, by simpa using hi₁⟩,
        Nat.add_sub_cancel_left]
    rw [hblocks, ← List.prod_flatten, List.splitWrtComposition,
      List.flatten_splitWrtCompositionAux (by simp)]
  simp only [compAlongComposition_apply, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [hprod, smul_smul]

/-- The iterated derivatives at zero of the sum of a scalar formal multilinear series over a
complete nontrivially normed field recover its coefficients, up to the factorial normalization. -/
theorem iteratedDeriv_ofScalarsSum_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (c : ℕ → 𝕜) (hc : 0 < (ofScalars 𝕜 c).radius) (n : ℕ) :
    iteratedDeriv n (ofScalarsSum (E := 𝕜) c) 0 = n.factorial * c n := by
  have hseries := (ofScalars 𝕜 c).hasFPowerSeriesOnBall hc
  have hfac := hseries.factorial_smul (1 : 𝕜)
  simp only [apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    one_pow, one_mul, smul_eq_mul, coeff_ofScalars] at hfac
  have h := hfac n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simpa [ofScalarsSum, nsmul_eq_mul, mul_comm] using h.symm

end FormalMultilinearSeries
