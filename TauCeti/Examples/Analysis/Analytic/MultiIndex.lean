/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.Analytic.MultiIndex.CoordinateDivision

/-!
# Normalization checks for multi-index coefficients and Taylor coefficients

This file checks the normalization conventions for `FormalMultilinearSeries.mvCoeff`,
`TauCeti.mvTaylorCoeff`, and `TauCeti.analyticAt_dslope_update`:

* On `Fin 2 → 𝕜`, the asymmetric bilinear map `(u, v) ↦ u 0 * v 1` has `mvCoeff` equal to `1` at
  `![1, 1]` (summing over both orderings `(e 0, e 1)` and `(e 1, e 0)`), and `0` at `0`.
* On `Fin 2 → 𝕜`, the symmetric bilinear map `(u, v) ↦ u 0 * v 0` has `mvCoeff` equal to `1` (not
  `2`) at `![2, 0]`, and `0` at `0`.
* The constant formal series `p 0 = c` has `mvCoeff p 0 = c`.
* In one variable (`Fin 1 → ℂ`), `z ↦ z 0 ^ 2` at `0` has `mvTaylorCoeff` equal to `1` at `![2]`,
  while its second derivative is `2`.
* In one variable (`Fin 1 → ℂ`), `z ↦ z 0 ^ 2` at `fun _ ↦ 3` has `mvTaylorCoeff` equal to `6` at
  `![1]`.
* The non-analytic function `z ↦ 1 + starRingEnd ℂ (z 0)` on `Fin 1 → ℂ` has every `mvTaylorCoeff`
  equal to `0`, including at order `0` (where the function value is `1`).
* The Cauchy-product formula `AnalyticAt.mvTaylorCoeff_smul` specializes directly to scalar
  multiplication on `ℂ`.
* The divided difference `z ↦ dslope (fun w ↦ Function.update z 0 w 0 ^ 2) 0 (z 0)` is analytic at
  `0`.
-/

open Finset

namespace TauCeti.MultiIndexExample

/-! ### Normalization checks for `FormalMultilinearSeries.mvCoeff` -/

section MvCoeffChecks

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- For the asymmetric series `p 2 (u, v) = u 0 * v 1`, `mvCoeff p ![1, 1] = 1`. -/
example :
    let p : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 := fun n ↦
      match n with
      | 2 => (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin 2) (1 : 𝕜)).compContinuousLinearMap
          ![ContinuousLinearMap.proj (R := 𝕜) (0 : Fin 2),
            ContinuousLinearMap.proj (R := 𝕜) (1 : Fin 2)]
      | _ => 0
    p.mvCoeff ![1, 1] = 1 := by
  intro p
  rw [FormalMultilinearSeries.mvCoeff_eq_sum p (k := 2) (by decide)]
  have hfilt : ∀ a : Fin 2 → Fin 2,
      (∀ i, Fintype.card {j // a j = i} = (![1, 1] : Fin 2 → ℕ) i) ↔
        a ∈ ({![0, 1], ![1, 0]} : Finset (Fin 2 → Fin 2)) := by
    decide
  rw [Finset.sum_congr (s₂ := {![0, 1], ![1, 0]}) (by ext a; simp [hfilt]) (fun _ _ ↦ rfl),
    sum_pair (by decide)]
  simp [p, Fin.prod_univ_two]

/-- For the symmetric series `p 2 (u, v) = u 0 * v 0`, `mvCoeff p ![2, 0] = 1` (not `2`). -/
example :
    let p : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 := fun n ↦
      match n with
      | 2 => (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin 2) (1 : 𝕜)).compContinuousLinearMap
          ![ContinuousLinearMap.proj (R := 𝕜) (0 : Fin 2),
            ContinuousLinearMap.proj (R := 𝕜) (0 : Fin 2)]
      | _ => 0
    p.mvCoeff ![2, 0] = 1 := by
  intro p
  rw [FormalMultilinearSeries.mvCoeff_eq_sum p (k := 2) (by decide)]
  have hfilt : ∀ a : Fin 2 → Fin 2,
      (∀ i, Fintype.card {j // a j = i} = (![2, 0] : Fin 2 → ℕ) i) ↔
        a ∈ ({![0, 0]} : Finset (Fin 2 → Fin 2)) := by
    decide
  rw [Finset.sum_congr (s₂ := {![0, 0]}) (by ext a; simp [hfilt]) (fun _ _ ↦ rfl), sum_singleton]
  simp [p, Fin.prod_univ_two]

/-- A degree-`2` formal series has constant coefficient `mvCoeff p 0 = 0`. -/
example (i j : Fin 2) :
    let p : FormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) 𝕜 := fun n ↦
      match n with
      | 2 => (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin 2) (1 : 𝕜)).compContinuousLinearMap
          ![ContinuousLinearMap.proj (R := 𝕜) i, ContinuousLinearMap.proj (R := 𝕜) j]
      | _ => 0
    p.mvCoeff 0 = 0 := by
  intro p
  rw [FormalMultilinearSeries.mvCoeff_zero_eq_apply p (fun _ ↦ 0)]
  simp [p]

/-- The constant formal series `p 0 = c` has `mvCoeff p 0 = c`. -/
example (c : 𝕜) :
    (constFormalMultilinearSeries 𝕜 (Fin 2 → 𝕜) c).mvCoeff 0 = c := by
  rw [FormalMultilinearSeries.mvCoeff_zero_eq_apply _ (fun _ ↦ 0)]
  simp [constFormalMultilinearSeries]

end MvCoeffChecks

/-! ### Normalization checks for `TauCeti.mvTaylorCoeff` -/

/-- For `z ↦ z 0 ^ 2` at `0`, the order-`2` Taylor coefficient is `1`, while the second derivative
is `2`. -/
example :
    TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) 0 ![2] = 1 ∧
      iteratedDeriv 2 (fun w : ℂ ↦ w ^ 2) 0 = 2 := by
  have hcoeff : TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) 0 ![2] = 1 := by
    simpa [Fin.prod_univ_one] using
      TauCeti.mvTaylorCoeff_prod_pow (𝕜 := ℂ) (ι := Fin 1) ![2] ![2]
  have hf : AnalyticAt ℂ (fun w : ℂ ↦ w ^ 2) 0 := analyticAt_id.pow 2
  have hderiv : iteratedDeriv 2 (fun w : ℂ ↦ w ^ 2) 0 = 2 := by
    have h := hf.factorial_smul_mvTaylorCoeff_of_unique (ι := Fin 1) ![2]
    simp only [Fin.default_eq_zero, Matrix.cons_val_zero] at h
    rw [← h, ← Pi.zero_def, hcoeff]
    norm_num
  exact ⟨hcoeff, hderiv⟩

/-- For `z ↦ z 0 ^ 2` at `3`, the order-`1` Taylor coefficient is `6`. -/
example : TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) (fun _ ↦ 3) ![1] = 6 := by
  have hshift : TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) (fun _ ↦ 3) ![1] =
      TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ (z 0 + 3) ^ 2) 0 ![1] := by
    simpa using (TauCeti.mvTaylorCoeff_comp_add_right (𝕜 := ℂ) (fun z : Fin 1 → ℂ ↦ z 0 ^ 2)
      0 (fun _ ↦ 3) ![1]).symm
  rw [hshift]
  have hexpand : (fun z : Fin 1 → ℂ ↦ (z 0 + 3) ^ 2) =
      (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) + ((fun z : Fin 1 → ℂ ↦ (6 : ℂ) • z 0) +
        (fun _ : Fin 1 → ℂ ↦ (9 : ℂ))) := by
    ext z
    simp [Pi.add_apply]
    ring
  rw [hexpand]
  let p0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)
  have h1 : AnalyticAt ℂ (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) 0 := (p0.analyticAt 0).pow 2
  have h2 : AnalyticAt ℂ (fun z : Fin 1 → ℂ ↦ (6 : ℂ) • z 0) 0 :=
    (analyticAt_const (v := (6 : ℂ))).smul (p0.analyticAt 0)
  have h3 : AnalyticAt ℂ (fun _ : Fin 1 → ℂ ↦ (9 : ℂ)) 0 := analyticAt_const
  rw [h1.mvTaylorCoeff_add (h2.add h3), h2.mvTaylorCoeff_add h3, TauCeti.mvTaylorCoeff_const_smul,
    TauCeti.mvTaylorCoeff_const]
  have hm2 : TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0 ^ 2) 0 ![1] = 0 := by
    simpa [Fin.prod_univ_one] using
      TauCeti.mvTaylorCoeff_prod_pow (𝕜 := ℂ) (ι := Fin 1) ![2] ![1]
  have hm1 : TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0) 0 ![1] = 1 := by
    simpa [Fin.prod_univ_one] using
      TauCeti.mvTaylorCoeff_prod_pow (𝕜 := ℂ) (ι := Fin 1) ![1] ![1]
  have hne : (![1] : Fin 1 → ℕ) ≠ 0 := by decide
  simp [hm2, hm1, hne]

/-- `z ↦ 1 + starRingEnd ℂ (z 0)` is analytic nowhere, so every `mvTaylorCoeff` vanishes — in
particular at order `0` at the origin (even though the function value there is `1`). -/
example (x : Fin 1 → ℂ) (α : Fin 1 → ℕ) :
    TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ 1 + starRingEnd ℂ (z 0)) x α = 0 := by
  refine TauCeti.mvTaylorCoeff_of_not_analyticAt (fun h ↦ ?_) α
  let incl : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℂ ℂ
  have h1 : AnalyticAt ℂ (fun w : ℂ ↦ 1 + starRingEnd ℂ w) (x 0) := by
    have hx : incl (x 0) = x := by ext i; fin_cases i; rfl
    have h' : AnalyticAt ℂ (fun z : Fin 1 → ℂ ↦ 1 + starRingEnd ℂ (z 0)) (incl (x 0)) :=
      hx.symm ▸ h
    exact h'.comp (incl.analyticAt (x 0))
  have hconj : AnalyticAt ℂ (starRingEnd ℂ) (x 0) := by
    have hsub := h1.sub (analyticAt_const (v := (1 : ℂ)))
    convert hsub using 1
    ext w
    simp
  obtain ⟨L, hL⟩ := hconj.differentiableAt
  have hreal : L.restrictScalars ℝ = Complex.conjCLE.toContinuousLinearMap :=
    (hL.restrictScalars ℝ).unique Complex.conjCLE.hasFDerivAt
  have hL1 : L 1 = 1 := by simpa using DFunLike.congr_fun hreal 1
  have hLI : L Complex.I = -Complex.I := by
    simpa using DFunLike.congr_fun hreal Complex.I
  have hbad : Complex.I = -Complex.I := by
    calc Complex.I = Complex.I • L 1 := by simp [hL1]
      _ = L (Complex.I • 1) := (L.map_smul Complex.I 1).symm
      _ = L Complex.I := by simp
      _ = -Complex.I := hLI
  exact Complex.I_ne_zero (by linear_combination hbad / 2)

/-! ### Check for `AnalyticAt.mvTaylorCoeff_smul` and `TauCeti.analyticAt_dslope_update` -/

/-- The Cauchy-product rule `AnalyticAt.mvTaylorCoeff_smul` recovers the order-`![2]` coefficient of
`z ↦ z 0 • z 0` at `0`. -/
example :
    TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0 • z 0) 0 ![2] =
      ∑ β ∈ Finset.Iic (![2] : Fin 1 → ℕ),
        TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0) 0 β •
          TauCeti.mvTaylorCoeff (fun z : Fin 1 → ℂ ↦ z 0) 0 (![2] - β) := by
  let p0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)
  exact (p0.analyticAt 0).mvTaylorCoeff_smul (p0.analyticAt 0) ![2]

/-- The divided difference of `z ↦ z 0 ^ 2` along coordinate `0` at `0` is analytic across the
hyperplane `z 0 = 0`. -/
example : AnalyticAt ℂ
    (fun z : Fin 2 → ℂ ↦ dslope (fun w ↦ Function.update z 0 w 0 ^ 2) 0 (z 0)) 0 := by
  let p0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)
  have hf : AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z 0 ^ 2) 0 := (p0.analyticAt 0).pow 2
  simpa using TauCeti.analyticAt_dslope_update (𝕜 := ℂ) (f := fun z : Fin 2 → ℂ ↦ z 0 ^ 2)
    (0 : Fin 2) 0 hf (by simpa using hf)

end TauCeti.MultiIndexExample
