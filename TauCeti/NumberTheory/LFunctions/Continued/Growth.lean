/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.PoleCleared
public import TauCeti.NumberTheory.LFunctions.Continued.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth

/-!
# Order of the pole-cleared continued functions of the Dirichlet and zeta records

* `dirichletData_orderLE_continuedL`: for a primitive character the continued function has
  order at most one. For the character modulo `1` it is zeta, with its pole at `1`.
* `riemannZetaData_orderLE_poleClearedContinuedL`: clearing the pole of zeta at `1` by `X - 1`
  gives a function of order at most one, which is entire by
  `differentiable_poleClearedContinuedL` and `riemannZetaData_continuedL_cleared_by_X_sub_one`.
* `riemannZetaData_poleClearedContinuedL_X_sub_one_apply_one`: its value at `1` is the residue
  `1`, whereas the raw product `(1 - 1) · riemannZeta 1` is `0`.
-/

public section

open Complex Filter Topology Polynomial

namespace TauCeti.LFunctions

/-- **Order of a Dirichlet continued function.** For a primitive character `χ`, the continued
function of `dirichletData χ hχ` has order at most one. -/
theorem dirichletData_orderLE_continuedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : OrderLE (dirichletData χ hχ).continuedL 1 :=
  AnalyticLFunctionData.orderLE_continuedL (dirichletData_entireCompletion_orderLE_one χ hχ) le_rfl

/-- The polynomial `X - 1` clears the only pole of the zeta continued function. -/
theorem riemannZetaData_continuedL_cleared_by_X_sub_one (s : ℂ) :
    0 ≤ meromorphicOrderAt riemannZetaData.continuedL s +
      ((X - C 1 : ℂ[X]).rootMultiplicity s : ℕ) := by
  have h := riemannZetaData_hasMeromorphicContinuation
  rcases eq_or_ne s 1 with rfl | hs
  · rw [AnalyticLFunctionData.meromorphicOrderAt_continuedL h.meromorphic,
      h.meromorphicOrderAt_eq 1 (by simp),
      (riemannZetaData.meromorphicOrderAt_gammaFactor_eq_zero_iff 1).mpr
        (by rw [riemannZetaData_gammaFactor, Gammaℝ_one]; exact one_ne_zero),
      rootMultiplicity_X_sub_C_self]
    simp
  · rw [riemannZetaData_continuedL]
    exact le_add_of_le_of_nonneg (analyticOn_riemannZeta s hs).meromorphicOrderAt_nonneg
      (by exact_mod_cast Nat.zero_le _)

/-- **Order of the pole-cleared zeta function.** Clearing the pole of zeta at `1` by `X - 1`
gives a function of order at most one. It is entire by `differentiable_poleClearedContinuedL`
and `riemannZetaData_continuedL_cleared_by_X_sub_one`. -/
theorem riemannZetaData_orderLE_poleClearedContinuedL :
    OrderLE (riemannZetaData.poleClearedContinuedL (X - C 1)) 1 :=
  AnalyticLFunctionData.orderLE_poleClearedContinuedL
    (by rw [riemannZetaData_entireCompletion]; exact orderLE_zetaEntireCompletion) le_rfl

/-- **The repaired value at the pole of zeta is its residue.** Clearing by `X - 1` gives the
value `1` at `1`, whereas the raw product `(1 - 1) · riemannZeta 1` is `0`. -/
theorem riemannZetaData_poleClearedContinuedL_X_sub_one_apply_one :
    riemannZetaData.poleClearedContinuedL (X - C 1) 1 = 1 := by
  have ha := AnalyticLFunctionData.analyticAt_poleClearedContinuedL (P := X - C 1)
    ((AnalyticLFunctionData.meromorphicOrderAt_poleClearedContinuedL (X_sub_C_ne_zero 1) 1).symm
      ▸ riemannZetaData_continuedL_cleared_by_X_sub_one 1)
  refine tendsto_nhds_unique (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (riemannZeta_residue_one.congr' ?_)
  filter_upwards [AnalyticLFunctionData.poleClearedContinuedL_eventuallyEq (d := riemannZetaData)
    (P := X - C 1) 1] with z hz
  rw [hz, eval_sub, eval_X, eval_C, riemannZetaData_continuedL]

/-! ### Checks -/

/-- Away from `1` the pole-cleared zeta function is `(s - 1) ζ(s)`; at `0` it is `1/2`. -/
example : riemannZetaData.poleClearedContinuedL (X - C 1) 0 = 1 / 2 := by
  rw [AnalyticLFunctionData.poleClearedContinuedL_eq_of_eval_ne_zero (by simp),
    riemannZetaData_continuedL, riemannZeta_zero]
  norm_num

/-- The raw product vanishes at the pole, so it is not the pole-cleared function. -/
example : (X - C 1 : ℂ[X]).eval 1 * riemannZetaData.continuedL 1 ≠
    riemannZetaData.poleClearedContinuedL (X - C 1) 1 := by
  rw [riemannZetaData_poleClearedContinuedL_X_sub_one_apply_one]
  simp

end TauCeti.LFunctions
