/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff

/-!
# Normalization examples for multi-index coefficients and Taylor coefficients

These examples verify from a downstream module the normalization conventions of
`FormalMultilinearSeries.mvCoeff` and `TauCeti.mvTaylorCoeff`:

* for the non-symmetric bilinear series `p 2 (u, v) = u 0 * v 1` on `Fin 2 → 𝕜`,
  `p.mvCoeff ![1, 1] = 1` (both orderings `(e 0, e 1)` and `(e 1, e 0)` are summed over);
* for `q 2 (u, v) = u 0 * v 0` on `Fin 2 → 𝕜`, `q.mvCoeff ![2, 0] = 1`, not `2` (the sum runs
  over distinct tuples of basis vectors rather than permutations of positions);
* `mvCoeff` at `0` recovers the constant term (`0` for `p` and `q`, and `c` for
  `constFormalMultilinearSeries`);
* for `z ↦ z 0 ^ 2` at `0` on `Fin 1 → 𝕜`, the Taylor coefficient at `![2]` is `1` while the
  second derivative at `0` is `2`;
* for `z ↦ z 0 ^ 2` at `fun _ ↦ 3` on `Fin 1 → 𝕜`, the Taylor coefficient at `![1]` is `6`, the
  linear coefficient of `(3 + w) ^ 2`;
* for `z ↦ 1 + conj (z 0)` on `Fin 1 → ℂ`, which is nowhere complex-analytic, every Taylor
  coefficient vanishes—in particular `mvTaylorCoeff _ 0 0 = 0` even though the value at `0` is `1`.
-/

open TauCeti

section FormalSeries

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- For `p 2 (u, v) = u 0 * v 1` (and `p k = 0` for `k ≠ 2`), `p.mvCoeff ![1, 1] = 1` and
-- `p.mvCoeff 0 = 0`: `(e 0, e 1)` contributes `1` and `(e 1, e 0)` contributes `0`.
example :
    let B : (Fin 2 → 𝕜) [×2]→L[𝕜] 𝕜 :=
      (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin 2) 𝕜).compContinuousLinearMap
        ![ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 2 ↦ 𝕜) 0,
          ContinuousLinearMap.proj 1]
    let p : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 :=
      Pi.single (M := fun k ↦ (Fin 2 → 𝕜) [×k]→L[𝕜] 𝕜) 2 B
    p.mvCoeff ![1, 1] = 1 ∧ p.mvCoeff 0 = 0 := by
  intro B p
  have hp2 : (p 2 : (Fin 2 → 𝕜) [×2]→L[𝕜] 𝕜) = B :=
    Pi.single_eq_same (M := fun k ↦ (Fin 2 → 𝕜) [×k]→L[𝕜] 𝕜) 2 B
  have hp0 : (p 0 : (Fin 2 → 𝕜) [×0]→L[𝕜] 𝕜) = 0 :=
    Pi.single_eq_of_ne (M := fun k ↦ (Fin 2 → 𝕜) [×k]→L[𝕜] 𝕜) (by decide : (0 : ℕ) ≠ 2) B
  constructor
  · have hk : ∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i = 2 := by decide
    have hfilter :
        (Finset.univ.filter fun a : Fin 2 → Fin 2 ↦
          ∀ i, Fintype.card {j // a j = i} = (![1, 1] : Fin 2 → ℕ) i) = {![0, 1], ![1, 0]} := by
      decide
    refine (p.mvCoeff_eq_sum hk).trans ((Finset.sum_congr hfilter fun a _ ↦
      congrFun (congrArg DFunLike.coe hp2) fun j ↦ Pi.single (a j) 1).trans ?_)
    rw [Finset.sum_pair (by decide : (![0, 1] : Fin 2 → Fin 2) ≠ ![1, 0])]
    simp [B]
  · exact (p.mvCoeff_zero_eq_apply 0).trans (congrFun (congrArg DFunLike.coe hp0) 0)

-- For `q 2 (u, v) = u 0 * v 0` (and `q k = 0` for `k ≠ 2`), `q.mvCoeff ![2, 0] = 1` (not `2`,
-- because `(e 0, e 0)` is counted once) and `q.mvCoeff 0 = 0`.
example :
    let B : (Fin 2 → 𝕜) [×2]→L[𝕜] 𝕜 :=
      (ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin 2) 𝕜).compContinuousLinearMap
        ![ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 2 ↦ 𝕜) 0,
          ContinuousLinearMap.proj 0]
    let q : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 :=
      Pi.single (M := fun k ↦ (Fin 2 → 𝕜) [×k]→L[𝕜] 𝕜) 2 B
    q.mvCoeff ![2, 0] = 1 ∧ q.mvCoeff 0 = 0 := by
  intro B q
  have hq2 : (q 2 : (Fin 2 → 𝕜) [×2]→L[𝕜] 𝕜) = B :=
    Pi.single_eq_same (M := fun k ↦ (Fin 2 → 𝕜) [×k]→L[𝕜] 𝕜) 2 B
  have hq0 : (q 0 : (Fin 2 → 𝕜) [×0]→L[𝕜] 𝕜) = 0 :=
    Pi.single_eq_of_ne (M := fun k ↦ (Fin 2 → 𝕜) [×k]→L[𝕜] 𝕜) (by decide : (0 : ℕ) ≠ 2) B
  constructor
  · have hk : ∑ i : Fin 2, (![2, 0] : Fin 2 → ℕ) i = 2 := by decide
    have hfilter :
        (Finset.univ.filter fun a : Fin 2 → Fin 2 ↦
          ∀ i, Fintype.card {j // a j = i} = (![2, 0] : Fin 2 → ℕ) i) = {![0, 0]} := by
      decide
    refine (q.mvCoeff_eq_sum hk).trans ((Finset.sum_congr hfilter fun a _ ↦
      congrFun (congrArg DFunLike.coe hq2) fun j ↦ Pi.single (a j) 1).trans ?_)
    rw [Finset.sum_singleton]
    simp [B]
  · exact (q.mvCoeff_zero_eq_apply 0).trans (congrFun (congrArg DFunLike.coe hq0) 0)

-- Constant series at the zero multi-index recovers the constant.
example (c : 𝕜) : (constFormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) c).mvCoeff 0 = c := by
  rw [FormalMultilinearSeries.mvCoeff_zero_eq_apply _ 0]
  simp

end FormalSeries

section TaylorCoeff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- For `z ↦ z 0 ^ 2` at `0`, the Taylor coefficient at `![2]` is `1`, whereas the second
-- derivative of `w ↦ w ^ 2` at `0` is `2`.
example : mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) 0 ![2] = 1 ∧
    iteratedDeriv 2 (fun w : 𝕜 ↦ w ^ 2) 0 = 2 := by
  constructor
  · have hfn : (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) = fun z ↦ ∏ i : Fin 1, z i ^ (![2] : Fin 1 → ℕ) i := by
      ext z; simp
    rw [hfn, mvTaylorCoeff_prod_pow_zero, ite_eq_left rfl]
  · simp

-- For `z ↦ z 0 ^ 2` at `fun _ ↦ 3`, the Taylor coefficient at `![1]` is `6` (from `(w + 3)^2`).
example : mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) (fun _ ↦ 3) ![1] = 6 := by
  let L : (Fin 1 → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj 0
  have hL (x : Fin 1 → 𝕜) : AnalyticAt 𝕜 (fun z : Fin 1 → 𝕜 ↦ z 0) x := L.analyticAt x
  have hsq : (fun z : Fin 1 → 𝕜 ↦ z 0 ^ 2) = fun z ↦ z 0 * z 0 := by ext z; exact sq (z 0)
  have h0 : mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0) (fun _ ↦ 3) 0 = 3 :=
    (hL _).mvTaylorCoeff_zero
  have h1 : mvTaylorCoeff (fun z : Fin 1 → 𝕜 ↦ z 0) (fun _ ↦ 3) ![1] = 1 := by
    rw [← zero_add (fun _ : Fin 1 ↦ (3 : 𝕜)),
      ← mvTaylorCoeff_comp_add_right (fun z : Fin 1 → 𝕜 ↦ z 0) 0 (fun _ ↦ 3) ![1]]
    have hshift : (fun z : Fin 1 → 𝕜 ↦ (z + fun _ : Fin 1 ↦ (3 : 𝕜)) 0) =
        (fun z : Fin 1 → 𝕜 ↦ z 0) + fun _ ↦ 3 := rfl
    have hmon : (fun z : Fin 1 → 𝕜 ↦ z 0) = fun z ↦ ∏ i : Fin 1, z i ^ (![1] : Fin 1 → ℕ) i := by
      ext z; simp
    rw [hshift, (hL 0).mvTaylorCoeff_add analyticAt_const, hmon, mvTaylorCoeff_prod_pow_zero,
      mvTaylorCoeff_const]
    have hne : (![1] : Fin 1 → ℕ) ≠ 0 := by decide
    simp [hne]
  have hIic : Finset.Iic (![1] : Fin 1 → ℕ) = {0, ![1]} := by
    ext β
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton, Pi.le_def,
      Fin.forall_fin_one, funext_iff, Pi.zero_apply, Matrix.cons_val_zero]
    omega
  have hsub0 : (fun i : Fin 1 ↦ (![1] : Fin 1 → ℕ) i - (0 : Fin 1 → ℕ) i) = ![1] := by
    ext i; fin_cases i; rfl
  have hsub1 : (fun i : Fin 1 ↦ (![1] : Fin 1 → ℕ) i - (![1] : Fin 1 → ℕ) i) = 0 := by
    ext i; fin_cases i; rfl
  rw [hsq, (hL _).mvTaylorCoeff_fun_mul (hL _) ![1], hIic,
    Finset.sum_pair (by decide : (0 : Fin 1 → ℕ) ≠ ![1]), hsub0, hsub1, h0, h1]
  norm_num

-- Complex conjugation is nowhere `ℂ`-differentiable, hence `z ↦ 1 + conj (z 0)` is nowhere
-- `ℂ`-analytic and all its Taylor coefficients vanish (including order `0` at `0`).
example : (∀ (z : Fin 1 → ℂ) (α : Fin 1 → ℕ),
    mvTaylorCoeff (fun w : Fin 1 → ℂ ↦ 1 + starRingEnd ℂ (w 0)) z α = 0) ∧
    (fun w : Fin 1 → ℂ ↦ 1 + starRingEnd ℂ (w 0)) 0 = 1 := by
  refine ⟨fun z α ↦ mvTaylorCoeff_of_not_analyticAt (fun han ↦ ?_) α, by simp⟩
  let incl : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℂ ℂ
  have h_eq : z = incl (z 0) := by ext i; simp [incl, Subsingleton.elim i 0]
  rw [h_eq] at han
  have hconj_an : AnalyticAt ℂ (starRingEnd ℂ) (z 0) := by
    have hcomp := (han.comp (incl.analyticAt (z 0))).sub (analyticAt_const (v := (1 : ℂ)))
    refine hcomp.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp [incl]
  have hd : DifferentiableAt ℂ (starRingEnd ℂ) (z 0) := hconj_an.differentiableAt
  have huniq := (Complex.conjCLE.hasFDerivAt (x := z 0)).unique (hd.hasFDerivAt.restrictScalars ℝ)
  have h1 : fderiv ℂ (starRingEnd ℂ) (z 0) 1 = 1 := by
    have := ContinuousLinearMap.ext_iff.1 huniq 1
    simpa using this.symm
  have hI : fderiv ℂ (starRingEnd ℂ) (z 0) Complex.I = -Complex.I := by
    have := ContinuousLinearMap.ext_iff.1 huniq Complex.I
    simpa using this.symm
  have hlin : fderiv ℂ (starRingEnd ℂ) (z 0) Complex.I = Complex.I := by
    calc fderiv ℂ (starRingEnd ℂ) (z 0) Complex.I
        = Complex.I • fderiv ℂ (starRingEnd ℂ) (z 0) 1 := by
          rw [← map_smul, smul_eq_mul, mul_one]
      _ = Complex.I := by rw [h1, smul_eq_mul, mul_one]
  exact Complex.I_ne_zero (by linear_combination (norm := ring) (hlin.symm.trans hI) / 2)

end TaylorCoeff
