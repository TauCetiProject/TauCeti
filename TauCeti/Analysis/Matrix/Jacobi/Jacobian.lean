/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Jacobi.Moments
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.ConfluentVandermonde

/-!
# The Dumitriu–Edelman spectral Jacobian and Lebesgue change of variables

This file computes the Jacobian of `TauCeti.spectralMomentMap` via the confluent Vandermonde
determinant (`Matrix.det_confluentVandermonde`) and combines it with
`TauCeti.det_fderiv_jacobiMomentMap` and
`TauCeti.prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_vandermonde` to obtain the exact Lebesgue
change-of-variables law for `TauCeti.jacobiSpectralChart`: pushing forward Lebesgue measure on
`TauCeti.jacobiDomain n` weighted by `2 ^ n * (∏ k, q k) / (∏ j, b j)` produces Lebesgue measure
restricted to `TauCeti.spectralDomain n`.

## Main results

* `TauCeti.differentiable_spectralMomentMap`: global differentiability of the spectral moment map.
* `TauCeti.abs_det_fderiv_spectralMomentMap`:
  `|(fderiv ℝ (spectralMomentMap n) y).det| = |∏ k, q k| * ∏ i < j, (lam i - lam j) ^ 4`.
* `TauCeti.lintegral_jacobi_eq_lintegral_spectral`: Lebesgue integral change-of-variables identity
  between Jacobi and spectral chart coordinates.
* `TauCeti.map_jacobiSpectralChart_withDensity`: pushforward presentation of restricted Lebesgue
  measure on `TauCeti.spectralDomain n`.

## References

* I. Dumitriu and A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.5.1.
-/

public section

noncomputable section

open Matrix MeasureTheory Set TauCeti.Probability
open scoped ENNReal

namespace TauCeti

/-! ### Differentiability and Jacobian of the spectral moment map -/

/-- The spectral moment map is globally differentiable. -/
theorem differentiable_spectralMomentMap (n : ℕ) : Differentiable ℝ (spectralMomentMap n) := by
  rw [differentiable_pi]
  intro r
  simp_rw [spectralMomentMap_apply]
  refine Differentiable.fun_sum fun k _ => ?_
  have hlam : Differentiable ℝ fun y : Fin (2 * n + 1) → ℝ =>
      ((spectralCoordEquiv n).symm y).1 k := by
    simpa using differentiable_apply (⟨k.val, by omega⟩ : Fin (2 * n + 1))
  have hq : Differentiable ℝ fun y : Fin (2 * n + 1) → ℝ =>
      dirichletChart (Fin.last n) ((spectralCoordEquiv n).symm y).2 k := by
    by_cases hk : k = Fin.last n
    · subst hk
      simp_rw [dirichletChart_apply_self]
      refine (differentiable_const (1 : ℝ)).sub (Differentiable.fun_sum fun j _ => ?_)
      simpa using differentiable_apply
        (⟨n + 1 + j.1.val, by have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩ :
          Fin (2 * n + 1))
    · simp_rw [dirichletChart_apply_of_ne (Fin.last n) _ hk]
      simpa using differentiable_apply
        (⟨n + 1 + k.val, by have : k.val < n := Fin.lt_last_iff_ne_last.mpr hk; omega⟩ :
          Fin (2 * n + 1))
  exact hq.mul (hlam.pow (r.val + 1))

/-- Partial derivative of `spectralMomentMap n` with respect to an eigenvalue coordinate. -/
private theorem deriv_spectralMomentMap_lam (n : ℕ) (lam : Fin (n + 1) → ℝ)
    (q' : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) (r c : Fin (2 * n + 1)) (hc : c.val < n + 1) :
    deriv (fun t => spectralMomentMap n (Function.update (spectralCoordEquiv n (lam, q')) c t) r)
        (spectralCoordEquiv n (lam, q') c) =
      dirichletChart (Fin.last n) q' ⟨c.val, hc⟩ * ((r.val + 1 : ℕ) : ℝ) *
        lam ⟨c.val, hc⟩ ^ r.val := by
  let y := spectralCoordEquiv n (lam, q')
  let k₀ : Fin (n + 1) := ⟨c.val, hc⟩
  have hc_eq : c = ⟨k₀.val, by omega⟩ := Fin.ext rfl
  have hfn : (fun t => spectralMomentMap n (Function.update y c t) r) =
      fun t => ∑ k : Fin (n + 1),
        dirichletChart (Fin.last n) q' k * (if k = k₀ then t else lam k) ^ (r.val + 1) := by
    funext t
    rw [spectralMomentMap_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq_eq : ((spectralCoordEquiv n).symm (Function.update y c t)).2 = q' := by
      funext j
      rw [spectralCoordEquiv_symm_snd]
      have hne : (⟨n + 1 + j.1.val, by
          have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩ :
          Fin (2 * n + 1)) ≠ c := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      rw [Function.update_of_ne hne]
      exact spectralCoordEquiv_apply_right n lam q' j
    have hlam_eq : ((spectralCoordEquiv n).symm (Function.update y c t)).1 k =
        if k = k₀ then t else lam k := by
      rw [spectralCoordEquiv_symm_fst]
      by_cases hkk : k = k₀
      · subst hkk
        rw [ite_eq_left rfl, ← hc_eq, Function.update_self]
      · have hne : (⟨k.val, by omega⟩ : Fin (2 * n + 1)) ≠ c := fun heq =>
          hkk (Fin.ext (by have hv := congrArg Fin.val heq; simpa [k₀] using hv))
        rw [ite_eq_right hkk, Function.update_of_ne hne]
        exact spectralCoordEquiv_apply_left n lam q' k
    rw [hq_eq, hlam_eq]
  rw [hfn]
  have hsum : HasDerivAt (fun t => ∑ k : Fin (n + 1),
      dirichletChart (Fin.last n) q' k * (if k = k₀ then t else lam k) ^ (r.val + 1))
      (∑ k : Fin (n + 1), if k = k₀ then
        dirichletChart (Fin.last n) q' k₀ * ((r.val + 1 : ℕ) : ℝ) * lam k₀ ^ r.val else 0)
      (y c) := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    by_cases hkk : k = k₀
    · subst hkk
      have hyc : y c = lam k₀ := by
        rw [hc_eq]; exact spectralCoordEquiv_apply_left n lam q' k₀
      have hd := (hasDerivAt_pow (r.val + 1) (y c)).const_mul (dirichletChart (Fin.last n) q' k₀)
      simp only [↓reduceIte]
      convert hd using 1
      rw [hyc]
      simp [mul_assoc]
    · simp only [ite_eq_right hkk]
      exact hasDerivAt_const (y c) _
  simpa using hsum.deriv

/-- Partial derivative of `spectralMomentMap n` with respect to a weight coordinate. -/
private theorem deriv_spectralMomentMap_weight (n : ℕ) (lam : Fin (n + 1) → ℝ)
    (q' : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) (r c : Fin (2 * n + 1))
    (hc : ¬c.val < n + 1) :
    deriv (fun t => spectralMomentMap n (Function.update (spectralCoordEquiv n (lam, q')) c t) r)
        (spectralCoordEquiv n (lam, q') c) =
      lam ⟨c.val - (n + 1), by omega⟩ ^ (r.val + 1) - lam (Fin.last n) ^ (r.val + 1) := by
  let y := spectralCoordEquiv n (lam, q')
  let j₀ : {i : Fin (n + 1) // i ≠ Fin.last n} :=
    ⟨⟨c.val - (n + 1), by omega⟩, fun heq => by have := congrArg Fin.val heq; simp at this; omega⟩
  have hfn : (fun t => spectralMomentMap n (Function.update y c t) r) =
      fun t => ∑ k : Fin (n + 1),
        dirichletChart (Fin.last n) (Function.update q' j₀ t) k * lam k ^ (r.val + 1) := by
    funext t
    rw [spectralMomentMap_apply]
    have hlam_eq : ((spectralCoordEquiv n).symm (Function.update y c t)).1 = lam := by
      funext k
      rw [spectralCoordEquiv_symm_fst]
      have hne : (⟨k.val, by omega⟩ : Fin (2 * n + 1)) ≠ c := by
        intro heq; have := congrArg Fin.val heq; simp at this; omega
      rw [Function.update_of_ne hne]
      exact spectralCoordEquiv_apply_left n lam q' k
    have hq_eq : ((spectralCoordEquiv n).symm (Function.update y c t)).2 =
        Function.update q' j₀ t := by
      funext j
      rw [spectralCoordEquiv_symm_snd]
      by_cases hjj : j = j₀
      · subst hjj
        have hceq : (⟨n + 1 + j₀.1.val, by
            have : j₀.1.val < n := Fin.lt_last_iff_ne_last.mpr j₀.2; omega⟩ :
            Fin (2 * n + 1)) = c := by
          ext; simp [j₀]; omega
        rw [hceq, Function.update_self, Function.update_self]
      · have hne : (⟨n + 1 + j.1.val, by
            have : j.1.val < n := Fin.lt_last_iff_ne_last.mpr j.2; omega⟩ :
            Fin (2 * n + 1)) ≠ c := by
          intro heq
          apply hjj
          refine Subtype.ext (Fin.ext ?_)
          have hv := congrArg Fin.val heq
          simp only [j₀] at hv ⊢
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hjj]
        exact spectralCoordEquiv_apply_right n lam q' j
    rw [hlam_eq, hq_eq]
  rw [hfn]
  have hlin : (fun t => ∑ k : Fin (n + 1),
      dirichletChart (Fin.last n) (Function.update q' j₀ t) k * lam k ^ (r.val + 1)) =
      fun t => ((1 - ∑ j ∈ Finset.univ.erase j₀, q' j) * lam (Fin.last n) ^ (r.val + 1) +
        ∑ j ∈ Finset.univ.erase j₀, q' j * lam j.1 ^ (r.val + 1)) +
        (lam j₀.1 ^ (r.val + 1) - lam (Fin.last n) ^ (r.val + 1)) * t := by
    funext t
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (Fin.last n), dirichletChart_apply_self]
    simp_rw [dirichletChart_apply_coe]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Function.update_self]
    have h1 : ∑ j ∈ Finset.univ.erase j₀, Function.update q' j₀ t j =
        ∑ j ∈ Finset.univ.erase j₀, q' j :=
      Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) t q'
    have h2 : ∑ j ∈ Finset.univ.erase j₀, Function.update q' j₀ t j * lam j.1 ^ (r.val + 1) =
        ∑ j ∈ Finset.univ.erase j₀, q' j * lam j.1 ^ (r.val + 1) :=
      Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj) t q']
    rw [h1, h2]
    ring
  rw [hlin]
  have hd := ((hasDerivAt_id' (y c)).const_mul
    (lam j₀.1 ^ (r.val + 1) - lam (Fin.last n) ^ (r.val + 1))).const_add
    ((1 - ∑ j ∈ Finset.univ.erase j₀, q' j) * lam (Fin.last n) ^ (r.val + 1) +
      ∑ j ∈ Finset.univ.erase j₀, q' j * lam j.1 ^ (r.val + 1))
  rw [hd.deriv, mul_one]

/-- Adding column `Fin.last (2 * n + 1)` to each column `n + 1 + j` (`j < m`) preserves the
determinant of a `(2 * n + 2) × (2 * n + 2)` matrix. -/
private theorem det_add_lastCol_prefix {n : ℕ}
    (A : Matrix (Fin (2 * n + 2)) (Fin (2 * n + 2)) ℝ) (m : ℕ) (hm : m ≤ n) :
    (Matrix.of fun r c : Fin (2 * n + 2) =>
      if n + 1 ≤ c.val ∧ c.val < n + 1 + m then A r c + A r (Fin.last (2 * n + 1))
      else A r c).det = A.det := by
  induction m with
  | zero =>
      have heq : (Matrix.of fun r c : Fin (2 * n + 2) =>
          if n + 1 ≤ c.val ∧ c.val < n + 1 + 0 then A r c + A r (Fin.last (2 * n + 1))
          else A r c) = A := by
        ext r c
        have h : ¬(n + 1 ≤ c.val ∧ c.val < n + 1 + 0) := by omega
        change (if n + 1 ≤ c.val ∧ c.val < n + 1 + 0 then _ else _) = A r c
        rw [ite_eq_right h]
      rw [heq]
  | succ m ih =>
      let B : Matrix (Fin (2 * n + 2)) (Fin (2 * n + 2)) ℝ :=
        Matrix.of fun r c =>
          if n + 1 ≤ c.val ∧ c.val < n + 1 + m then A r c + A r (Fin.last (2 * n + 1))
          else A r c
      let c₀ : Fin (2 * n + 2) := ⟨n + 1 + m, by omega⟩
      have hne : c₀ ≠ Fin.last (2 * n + 1) := by
        intro heq; have := congrArg Fin.val heq; simp [c₀] at this; omega
      have hstep : (Matrix.of fun r c : Fin (2 * n + 2) =>
          if n + 1 ≤ c.val ∧ c.val < n + 1 + (m + 1) then A r c + A r (Fin.last (2 * n + 1))
          else A r c) =
          B.updateCol c₀ (fun r => B r c₀ + (1 : ℝ) • B r (Fin.last (2 * n + 1))) := by
        ext r c
        by_cases hc : c = c₀
        · subst hc
          have h1 : n + 1 ≤ c₀.val ∧ c₀.val < n + 1 + (m + 1) := by simp [c₀]
          have h2 : ¬(n + 1 ≤ c₀.val ∧ c₀.val < n + 1 + m) := by simp [c₀]
          have h3 : ¬(n + 1 ≤ (Fin.last (2 * n + 1)).val ∧
              (Fin.last (2 * n + 1)).val < n + 1 + m) := by simp; omega
          simp only [Matrix.of_apply, Matrix.updateCol_self, one_smul, B]
          rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3]
        · have hiff : (n + 1 ≤ c.val ∧ c.val < n + 1 + (m + 1)) ↔
              (n + 1 ≤ c.val ∧ c.val < n + 1 + m) := by
            have hvc : c.val ≠ n + 1 + m := fun h => hc (Fin.ext h)
            omega
          simp only [Matrix.of_apply, Matrix.updateCol_ne hc, B]
          rw [if_congr hiff rfl rfl]
      rw [hstep, Matrix.det_updateCol_add_smul_self B hne 1, ih (by omega)]

/-- Splitting `Fin (2 * n + 2)` into jet pairs `(k, 1)` for `c < n + 1` and `(k, 0)` for
`c ≥ n + 1`. -/
private def splitHalfEquiv (n : ℕ) : Fin (2 * n + 2) ≃ (_ : Fin (n + 1)) × Fin 2 where
  toFun c :=
    if h : c.val < n + 1 then ⟨⟨c.val, h⟩, (1 : Fin 2)⟩
    else ⟨⟨c.val - (n + 1), by omega⟩, (0 : Fin 2)⟩
  invFun x := if x.2.val = 1 then ⟨x.1.val, by omega⟩ else ⟨n + 1 + x.1.val, by omega⟩
  left_inv c := by
    by_cases h : c.val < n + 1
    · dsimp only
      rw [dite_eq_left h]
      simp
    · dsimp only
      rw [dite_eq_right h]
      ext; simp; omega
  right_inv x := by
    rcases x with ⟨k, d⟩
    fin_cases d
    · dsimp only
      have h01 : (0 : ℕ) ≠ 1 := by decide
      rw [ite_eq_right h01]
      have h : ¬(n + 1 + k.val < n + 1) := by omega
      rw [dite_eq_right h]
      refine Sigma.ext (Fin.ext (by simp)) (by simp)
    · dsimp only
      rw [ite_eq_left (rfl : (1 : ℕ) = 1)]
      have h : k.val < n + 1 := k.isLt
      rw [dite_eq_left h]
      rfl

/-- Column permutation sending derivative columns `0, …, n` to jets `⟨k, 1⟩` and value columns
`n + 1, …, 2 * n + 1` to jets `⟨k, 0⟩` of `Matrix.confluentVandermonde lam (fun _ => 2)`. -/
private def confluentColEquiv (n : ℕ) :
    Fin (2 * n + 2) ≃ Fin (∑ _ : Fin (n + 1), (2 : ℕ)) :=
  (splitHalfEquiv n).trans finSigmaFinEquiv

/-- **Absolute Jacobian determinant of the spectral moment map**: at `(lam, q')`,
`|(fderiv ℝ (spectralMomentMap n) y).det| = |∏ k, q k| * ∏ i < j, (lam i - lam j) ^ 4`. -/
theorem abs_det_fderiv_spectralMomentMap (n : ℕ) (lam : Fin (n + 1) → ℝ)
    (q' : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) :
    |(fderiv ℝ (spectralMomentMap n) (spectralCoordEquiv n (lam, q'))).det| =
      |∏ k : Fin (n + 1), dirichletChart (Fin.last n) q' k| *
        ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (lam i - lam j) ^ 4 := by
  let q : Fin (n + 1) → ℝ := fun k => dirichletChart (Fin.last n) q' k
  let M := LinearMap.toMatrix' (fderiv ℝ (spectralMomentMap n) (spectralCoordEquiv n (lam, q')) :
    (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] (Fin (2 * n + 1) → ℝ))
  let A : Matrix (Fin (2 * n + 2)) (Fin (2 * n + 2)) ℝ := Matrix.of fun m c =>
    if h1 : c.val < n + 1 then
      q ⟨c.val, h1⟩ * ((m.val.choose 1 : ℕ) : ℝ) * lam ⟨c.val, h1⟩ ^ (m.val - 1)
    else if h2 : c.val < 2 * n + 1 then
      lam ⟨c.val - (n + 1), by omega⟩ ^ m.val - lam (Fin.last n) ^ m.val
    else
      lam (Fin.last n) ^ m.val
  have hMsub : A.submatrix Fin.succ (Fin.last (2 * n + 1)).succAbove = M := by
    ext r c
    rw [Matrix.submatrix_apply, Fin.succAbove_last]
    dsimp only [M]
    have hMrc : LinearMap.toMatrix'
        (fderiv ℝ (spectralMomentMap n) (spectralCoordEquiv n (lam, q')) :
          (Fin (2 * n + 1) → ℝ) →ₗ[ℝ] (Fin (2 * n + 1) → ℝ)) r c =
        deriv (fun t => spectralMomentMap n
          (Function.update (spectralCoordEquiv n (lam, q')) c t) r)
          (spectralCoordEquiv n (lam, q') c) := by
      have hfx : HasFDerivAt (spectralMomentMap n)
          (fderiv ℝ (spectralMomentMap n) (spectralCoordEquiv n (lam, q')))
          (Function.update (spectralCoordEquiv n (lam, q')) c
            (spectralCoordEquiv n (lam, q') c)) := by
        simpa [Function.update_eq_self] using
          (differentiable_spectralMomentMap n (spectralCoordEquiv n (lam, q'))).hasFDerivAt
      have hcomp := hfx.comp_hasDerivAt _ (hasDerivAt_update _ c _)
      have hcoord := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * n + 1) => ℝ) r)
        |>.hasFDerivAt.comp_hasDerivAt _ hcomp
      simpa [LinearMap.toMatrix'_apply, Function.comp_def] using hcoord.deriv.symm
    rw [hMrc]
    simp only [A, of_apply, Fin.val_castSucc, Fin.val_succ, Nat.choose_one_right,
      add_tsub_cancel_right, q]
    by_cases hc : c.val < n + 1
    · rw [dite_eq_left hc, deriv_spectralMomentMap_lam n lam q' r c hc]
    · rw [dite_eq_right hc, dite_eq_left c.isLt, deriv_spectralMomentMap_weight n lam q' r c hc]
  have hAdet : |A.det| = |M.det| := by
    rw [Matrix.det_succ_row_zero]
    have hrow0 : ∀ c : Fin (2 * n + 2),
        (-1 : ℝ) ^ c.val * A 0 c * (A.submatrix Fin.succ c.succAbove).det =
        if c = Fin.last (2 * n + 1) then (-1 : ℝ) ^ (2 * n + 1) * 1 * M.det else 0 := by
      intro c
      by_cases hc : c = Fin.last (2 * n + 1)
      · subst hc
        have h1 : ¬((Fin.last (2 * n + 1)).val < n + 1) := by simp; omega
        have h2 : ¬((Fin.last (2 * n + 1)).val < 2 * n + 1) := by simp
        rw [ite_eq_left rfl, hMsub]
        have hA0 : A 0 (Fin.last (2 * n + 1)) = 1 := by
          dsimp only [A, Matrix.of_apply]
          rw [dite_eq_right h1, dite_eq_right h2]; simp
        rw [hA0, Fin.val_last]
      · rw [ite_eq_right hc]
        have hA0 : A 0 c = 0 := by
          dsimp only [A, Matrix.of_apply]
          by_cases h1 : c.val < n + 1
          · rw [dite_eq_left h1]; simp
          · have h2 : c.val < 2 * n + 1 :=
              Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp c.isLt) fun h => hc (Fin.ext h)
            rw [dite_eq_right h1, dite_eq_left h2]; simp
        rw [hA0, mul_zero, zero_mul]
    simp only [hrow0, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
  let B : Matrix (Fin (2 * n + 2)) (Fin (2 * n + 2)) ℝ := Matrix.of fun m c =>
    if n + 1 ≤ c.val ∧ c.val < n + 1 + n then A m c + A m (Fin.last (2 * n + 1)) else A m c
  have hBdet : B.det = A.det := det_add_lastCol_prefix A n le_rfl
  let e : Fin (∑ _ : Fin (n + 1), (2 : ℕ)) ≃ Fin (2 * n + 2) := finCongr (by simp; omega)
  let σ : Equiv.Perm (Fin (2 * n + 2)) := (confluentColEquiv n).trans e
  let w : Fin (2 * n + 2) → ℝ := fun c => if h : c.val < n + 1 then q ⟨c.val, h⟩ else 1
  have hBfac : B =
      (((Matrix.confluentVandermonde lam (fun _ => 2))ᵀ.submatrix e.symm e.symm).submatrix id σ) *
        Matrix.diagonal w := by
    ext m c
    rw [Matrix.mul_diagonal, Matrix.submatrix_apply, Matrix.submatrix_apply, transpose_apply, id_eq]
    have hσc : e.symm (σ c) = confluentColEquiv n c := by simp [σ]
    rw [hσc]
    have hem : (e.symm m).val = m.val := rfl
    by_cases h1 : c.val < n + 1
    · have hnot : ¬(n + 1 ≤ c.val ∧ c.val < n + 1 + n) := by omega
      dsimp only [B, A, Matrix.of_apply, confluentColEquiv, Equiv.trans_apply, splitHalfEquiv,
        Equiv.coe_fn_mk, w]
      rw [ite_eq_right hnot, dite_eq_left h1, dite_eq_left h1, dite_eq_left h1,
        Matrix.confluentVandermonde_finSigmaFinEquiv, Fin.val_one, hem]
      ring
    · by_cases h2 : c.val < 2 * n + 1
      · have hmem : n + 1 ≤ c.val ∧ c.val < n + 1 + n := by omega
        have hlast1 : ¬((Fin.last (2 * n + 1)).val < n + 1) := by simp; omega
        have hlast2 : ¬((Fin.last (2 * n + 1)).val < 2 * n + 1) := by simp
        dsimp only [B, A, Matrix.of_apply, confluentColEquiv, Equiv.trans_apply, splitHalfEquiv,
          Equiv.coe_fn_mk, w]
        rw [ite_eq_left hmem, dite_eq_right h1, dite_eq_left h2, dite_eq_right hlast1,
          dite_eq_right hlast2, dite_eq_right h1, dite_eq_right h1,
          Matrix.confluentVandermonde_finSigmaFinEquiv, Fin.val_zero, Nat.choose_zero_right,
          Nat.cast_one, Nat.sub_zero, one_mul, mul_one, hem, sub_add_cancel]
      · have hnot : ¬(n + 1 ≤ c.val ∧ c.val < n + 1 + n) := by omega
        have hclast : (⟨c.val - (n + 1), by omega⟩ : Fin (n + 1)) = Fin.last n := by
          ext; simp; omega
        dsimp only [B, A, Matrix.of_apply, confluentColEquiv, Equiv.trans_apply, splitHalfEquiv,
          Equiv.coe_fn_mk, w]
        rw [ite_eq_right hnot, dite_eq_right h1, dite_eq_right h2, dite_eq_right h1,
          dite_eq_right h1, Matrix.confluentVandermonde_finSigmaFinEquiv, Fin.val_zero,
          Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul, mul_one, hem, hclast]
  have hprodw : ∏ c : Fin (2 * n + 2), w c = ∏ k : Fin (n + 1), q k := by
    let s : Finset (Fin (2 * n + 2)) := Finset.univ.filter (fun c => c.val < n + 1)
    rw [← Finset.prod_subset (Finset.subset_univ s) (fun c _ hc => by
      have h : ¬(c.val < n + 1) := by simpa [s] using hc
      dsimp only [w]; rw [dite_eq_right h])]
    refine Finset.prod_bij (fun c hc => (⟨c.val, (Finset.mem_filter.mp hc).2⟩ : Fin (n + 1)))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val (n := n + 1)) h))
      (fun k _ => ⟨⟨k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩,
        Fin.ext rfl⟩)
      (fun c hc => by dsimp only [w]; rw [dite_eq_left (Finset.mem_filter.mp hc).2])
  have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hcv : |(Matrix.confluentVandermonde lam (fun _ => 2)).det| =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (lam i - lam j) ^ 4 := by
    rw [Matrix.det_confluentVandermonde]
    have h4 : ∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
        (if i < j then (lam j - lam i) ^ (2 * 2) else (1 : ℝ)) =
        ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (lam i - lam j) ^ 4 := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr (by ext j; simp) fun j _ => ?_
      ring
    rw [h4, abs_of_nonneg]
    exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by positivity
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  change |M.det| = _
  rw [← hAdet, ← hBdet, hBfac, Matrix.det_mul, Matrix.det_permute',
    Matrix.det_submatrix_equiv_self, Matrix.det_transpose, Matrix.det_diagonal, hprodw, abs_mul,
    abs_mul, hsign, one_mul, hcv, mul_comm]

/-! ### Change-of-variables measure theorem -/

/-- Exact ratio of the Jacobi and spectral moment Jacobians on `jacobiDomain n`. -/
private theorem jacobi_div_spectral_jacobian {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hb : ∀ j, 0 < b j) :
    (2 ^ n * ∏ j : Fin n, b j ^ (4 * (n - j.val) - 1)) /
      ((∏ k : Fin (n + 1), jacobiSpectralWeight a b k) *
        ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
          (jacobiEigenvalues a b i - jacobiEigenvalues a b j) ^ 4) =
      2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight a b k) / ∏ j : Fin n, b j := by
  have hbne : ∀ j, b j ≠ 0 := fun j => (hb j).ne'
  have hvw := congrArg (· ^ 4)
    (prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_vandermonde (a := a) hb)
  simp only [mul_pow, ← Finset.prod_pow, ← pow_mul] at hvw
  have hq4 : ∏ k : Fin (n + 1), Real.sqrt (jacobiSpectralWeight a b k) ^ 4 =
      (∏ k : Fin (n + 1), jacobiSpectralWeight a b k) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hqpos := (jacobiSpectralWeight_pos (a := a) hbne k).le
    calc Real.sqrt (jacobiSpectralWeight a b k) ^ 4
        = (Real.sqrt (jacobiSpectralWeight a b k) ^ 2) ^ 2 := by ring
      _ = jacobiSpectralWeight a b k ^ 2 := by rw [Real.sq_sqrt hqpos]
  rw [hq4] at hvw
  have hb4 : (∏ j : Fin n, b j ^ (4 * (n - j.val) - 1)) * (∏ j : Fin n, b j) =
      ∏ j : Fin n, b j ^ ((n - j.val) * 4) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_succ]
    congr 1; omega
  have hprod_b : (∏ j : Fin n, b j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hbne j
  have hprod_q : (∏ k : Fin (n + 1), jacobiSpectralWeight a b k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => (jacobiSpectralWeight_pos hbne k).ne'
  have hprod_v : (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      (jacobiEigenvalues a b i - jacobiEigenvalues a b j) ^ 4) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero 4 (sub_ne_zero.mpr (strictAnti_jacobiEigenvalues hbne (Finset.mem_Ioi.mp hj)).ne')
  rw [div_eq_div_iff (mul_ne_zero hprod_q hprod_v) hprod_b]
  calc (2 ^ n * ∏ j : Fin n, b j ^ (4 * (n - j.val) - 1)) * (∏ j : Fin n, b j)
      = 2 ^ n * ((∏ j : Fin n, b j ^ (4 * (n - j.val) - 1)) * ∏ j : Fin n, b j) := by ring
    _ = 2 ^ n * ((∏ k : Fin (n + 1), jacobiSpectralWeight a b k) ^ 2 *
          ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
            (jacobiEigenvalues a b i - jacobiEigenvalues a b j) ^ 4) := by rw [hb4, hvw]
    _ = 2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight a b k) *
          ((∏ k : Fin (n + 1), jacobiSpectralWeight a b k) *
            ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
              (jacobiEigenvalues a b i - jacobiEigenvalues a b j) ^ 4) := by ring

/-- **Lebesgue integral change of variables between Jacobi and spectral chart coordinates**:
for any `ℝ≥0∞`-valued function `h` on spectral chart coordinates, its integral over
`spectralDomain n` equals the weighted integral of `h ∘ jacobiSpectralChart n` over
`jacobiDomain n` with Jacobian weight `2 ^ n * (∏ k, q k) / (∏ j, b j)`. -/
theorem lintegral_jacobi_eq_lintegral_spectral (n : ℕ)
    (h : (Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) → ℝ≥0∞) :
    ∫⁻ p in jacobiDomain n,
        ENNReal.ofReal (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
          ∏ j : Fin n, p.2 j) * h (jacobiSpectralChart n p) ∂(volume.prod volume) =
      ∫⁻ s in spectralDomain n, h s ∂(volume.prod volume) := by
  classical
  let eJ := jacobiCoordEquiv n
  let eS := spectralCoordEquiv n
  let UJ := eJ '' jacobiDomain n
  let US := eS '' spectralDomain n
  have hUJ : MeasurableSet UJ := eJ.measurableEmbedding.measurableSet_image.mpr
    (measurableSet_jacobiDomain n)
  have hUS : MeasurableSet US := eS.measurableEmbedding.measurableSet_image.mpr
    (measurableSet_spectralDomain n)
  let g : (Fin (2 * n + 1) → ℝ) → ℝ≥0∞ := fun z =>
    if hz : z ∈ spectralMomentMap n '' US then
      let y := hz.choose
      h (eS.symm y) / ENNReal.ofReal |(fderiv ℝ (spectralMomentMap n) y).det|
    else 0
  have hgG : ∀ y ∈ US, g (spectralMomentMap n y) =
      h (eS.symm y) / ENNReal.ofReal |(fderiv ℝ (spectralMomentMap n) y).det| := by
    intro y hy
    have hz : spectralMomentMap n y ∈ spectralMomentMap n '' US := ⟨y, hy, rfl⟩
    have hy' : hz.choose = y := injOn_spectralMomentMap n hz.choose_spec.1 hy hz.choose_spec.2
    simp only [g, dite_eq_left hz, hy']
  have hGpos : ∀ y ∈ US, 0 < |(fderiv ℝ (spectralMomentMap n) y).det| := by
    rintro y ⟨⟨lam, q'⟩, hs, rfl⟩
    obtain ⟨hlam, hq'⟩ := mem_spectralDomain_iff.mp hs
    rw [abs_det_fderiv_spectralMomentMap]
    refine mul_pos (abs_pos.mpr (Finset.prod_ne_zero_iff.mpr fun k _ =>
      (dirichletChart_pos hq' k).ne')) (Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      pow_pos (sub_pos.mpr (hlam (Finset.mem_Ioi.mp hj))) 4)
  have hRHS : ∫⁻ z in spectralMomentMap n '' US, g z =
      ∫⁻ s in spectralDomain n, h s ∂(volume.prod volume) := by
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hUS
      (fun y _ => (differentiable_spectralMomentMap n y).hasFDerivAt.hasFDerivWithinAt)
      (injOn_spectralMomentMap n) g]
    have hcongr : ∫⁻ y in US,
        ENNReal.ofReal |(fderiv ℝ (spectralMomentMap n) y).det| * g (spectralMomentMap n y) =
        ∫⁻ y in US, h (eS.symm y) := by
      refine setLIntegral_congr_fun hUS fun y hy => ?_
      rw [hgG y hy, ENNReal.mul_div_cancel (ENNReal.ofReal_pos.mpr (hGpos y hy)).ne'
        ENNReal.ofReal_ne_top]
    rw [hcongr, ← (measurePreserving_spectralCoordEquiv n).setLIntegral_comp_emb
      eS.measurableEmbedding (fun y => h (eS.symm y)) (spectralDomain n)]
    simp [eS]
  have hLHS : ∫⁻ z in jacobiMomentMap n '' UJ, g z =
      ∫⁻ p in jacobiDomain n,
        ENNReal.ofReal (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
          ∏ j : Fin n, p.2 j) * h (jacobiSpectralChart n p) ∂(volume.prod volume) := by
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hUJ
      (fun x _ => (differentiable_jacobiMomentMap n x).hasFDerivAt.hasFDerivWithinAt)
      (injOn_jacobiMomentMap n) g,
      ← (measurePreserving_jacobiCoordEquiv n).setLIntegral_comp_emb eJ.measurableEmbedding
        (fun x => ENNReal.ofReal |(fderiv ℝ (jacobiMomentMap n) x).det| *
          g (jacobiMomentMap n x)) (jacobiDomain n)]
    refine setLIntegral_congr_fun (measurableSet_jacobiDomain n) fun p hp => ?_
    have hpb : ∀ j, 0 < p.2 j := mem_jacobiDomain_iff.mp hp
    let s := jacobiSpectralChart n p
    have hs : s ∈ spectralDomain n := by
      rw [← jacobiSpectralChart_image_domain n]; exact ⟨p, hp, rfl⟩
    have hys : eS s ∈ US := ⟨s, hs, rfl⟩
    have hΦG : jacobiMomentMap n (eJ p) = spectralMomentMap n (eS s) :=
      (spectralMomentMap_jacobiSpectralChart hp).symm
    rw [hΦG, hgG (eS s) hys, MeasurableEquiv.symm_apply_apply]
    have hdetΦ : |(fderiv ℝ (jacobiMomentMap n) (eJ p)).det| =
        2 ^ n * ∏ j : Fin n, p.2 j ^ (4 * (n - j.val) - 1) := by
      rw [det_fderiv_jacobiMomentMap]
      exact abs_of_pos (mul_pos (pow_pos two_pos n) (Finset.prod_pos fun j _ => pow_pos (hpb j) _))
    have hdetG : |(fderiv ℝ (spectralMomentMap n) (eS s)).det| =
        (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) *
          ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
            (jacobiEigenvalues p.1 p.2 i - jacobiEigenvalues p.1 p.2 j) ^ 4 := by
      rw [abs_det_fderiv_spectralMomentMap]
      simp_rw [dirichletChart_jacobiSpectralChart_snd hp, jacobiSpectralChart_fst]
      rw [abs_of_pos (Finset.prod_pos fun k _ => jacobiSpectralWeight_pos (fun j => (hpb j).ne') k)]
    rw [div_eq_mul_inv, mul_left_comm, mul_comm (h s), ← div_eq_mul_inv,
      ← ENNReal.ofReal_div_of_pos (hGpos (eS s) hys), hdetΦ, hdetG,
      jacobi_div_spectral_jacobian hpb]
  rw [← hLHS, ← hRHS, jacobiMomentMap_image_eq_spectralMomentMap_image n]

/-- **Change of variables for the Jacobi spectral chart**: pushing forward Lebesgue measure on
`jacobiDomain n` weighted by `2 ^ n * (∏ k, q k) / (∏ j, b j)` along `jacobiSpectralChart n`
yields Lebesgue measure restricted to `spectralDomain n`. -/
theorem map_jacobiSpectralChart_withDensity (n : ℕ) :
    (((volume.prod volume).restrict (jacobiDomain n)).withDensity
        fun p => ENNReal.ofReal (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
          ∏ j : Fin n, p.2 j)).map (jacobiSpectralChart n) =
      (volume.prod volume).restrict (spectralDomain n) := by
  ext s hs
  rw [Measure.map_apply (measurable_jacobiSpectralChart n) hs,
    withDensity_apply _ (measurable_jacobiSpectralChart n hs),
    ← lintegral_indicator (measurable_jacobiSpectralChart n hs),
    Measure.restrict_apply hs]
  let one : (Fin (n + 1) → ℝ) × ({i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) → ℝ≥0∞ := 1
  have hind : ∫⁻ p in jacobiDomain n,
      (jacobiSpectralChart n ⁻¹' s).indicator
        (fun p => ENNReal.ofReal (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
          ∏ j : Fin n, p.2 j)) p ∂(volume.prod volume) =
      ∫⁻ p in jacobiDomain n,
        ENNReal.ofReal (2 ^ n * (∏ k : Fin (n + 1), jacobiSpectralWeight p.1 p.2 k) /
          ∏ j : Fin n, p.2 j) * s.indicator one
          (jacobiSpectralChart n p) ∂(volume.prod volume) := by
    refine setLIntegral_congr_fun (measurableSet_jacobiDomain n) fun p _ => ?_
    by_cases hps : jacobiSpectralChart n p ∈ s <;> simp [one, hps]
  rw [hind, lintegral_jacobi_eq_lintegral_spectral n (s.indicator one),
    lintegral_indicator_one hs, Measure.restrict_apply hs]

end TauCeti
