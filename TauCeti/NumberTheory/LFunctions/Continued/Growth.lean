/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Dirichlet
public import TauCeti.NumberTheory.LFunctions.Continued.PoleCleared
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth

/-!
# Order of the pole-cleared continued functions of the Dirichlet and zeta records

* `dirichletData_orderLE_continuedL`: for a primitive character the continued function has
  order at most one. For the character modulo `1` it is zeta, with its pole at `1`.
* `DirichletCharacter.orderLE_LFunction` and `orderLE_riemannZeta`: Mathlib's `χ.LFunction`, for
  every Dirichlet character, and `riemannZeta` have order at most one. The order only bounds
  growth outside bounded sets, so the pole of zeta at `1` does not affect it. The entire
  extension `LFunctionTrivChar₁ 1` of `(s - 1) ζ(s)` has order at most one by
  `TauCeti.orderLE_LFunctionTrivChar₁_one`.
* `riemannZetaData_orderLE_poleClearedContinuedL`: clearing the pole of zeta at `1` by `X - 1`
  gives a function of order at most one, which is entire by
  `differentiable_poleClearedContinuedL` and `riemannZetaData_continuedL_cleared_by_X_sub_one`.
* `riemannZetaData_poleClearedContinuedL_X_sub_one_apply_one`: its value at `1` is the residue
  `1`, whereas the raw product `(1 - 1) · riemannZeta 1` is `0`.
-/

public section

open Complex Filter Topology Polynomial DirichletCharacter

namespace TauCeti.LFunctions

/-- **Order of a Dirichlet continued function.** For a primitive character `χ`, the continued
function of `dirichletData χ hχ` has order at most one. -/
theorem dirichletData_orderLE_continuedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : OrderLE (dirichletData χ hχ).continuedL 1 :=
  AnalyticLFunctionData.orderLE_continuedL (dirichletData_entireCompletion_orderLE_one χ hχ) le_rfl

/-- **Order of a Dirichlet L-function.** For every Dirichlet character `χ`, Mathlib's
`χ.LFunction` has order at most one. For a primitive character this is
`dirichletData_orderLE_continuedL`; otherwise `χ.LFunction` is the L-function of the primitive
character times finitely many Euler factors `1 - χ'(p) p^(-s)`, each of order at most one. For
the trivial character the pole at `1` does not matter: the order only bounds growth outside
bounded sets. -/
theorem _root_.DirichletCharacter.orderLE_LFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : OrderLE χ.LFunction 1 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ' := χ.primitiveCharacter
  have hprim := dirichletData_orderLE_continuedL χ' χ.primitiveCharacter_isPrimitive
  rw [dirichletData_continuedL] at hprim
  have hE : OrderLE (fun s ↦ χ'.LFunction s *
      ∏ p ∈ N.primeFactors, (1 - χ' p * (p : ℂ) ^ (-s))) 1 :=
    hprim.mul <| OrderLE.prod fun p _ ↦ (orderLE_const 1 1).sub <| by
      simpa using (orderLE_cpow_mul (p : ℂ) (-1)).const_mul (χ' p)
  refine EventuallyEq.isBigO ?_ |>.orderLE hE
  filter_upwards [Bornology.eventually_ne_cobounded (1 : ℂ)] with s hs
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  exact LFunction_changeLevel _ _ (.inr hs)

/-- **Order of the Riemann zeta function.** `riemannZeta` has order at most one, although it
has a pole at `1`: the order only bounds growth outside bounded sets. -/
theorem orderLE_riemannZeta : OrderLE riemannZeta 1 := by
  simpa using (1 : DirichletCharacter ℂ 1).orderLE_LFunction

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

/-- For a nontrivial character the order bound holds for an entire function. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) :
    Differentiable ℂ χ.LFunction ∧ OrderLE χ.LFunction 1 :=
  ⟨DirichletCharacter.differentiable_LFunction hne, χ.orderLE_LFunction⟩

/-- Clearing the pole by the raw product `(s - 1) ζ(s)` keeps order at most one. -/
example : OrderLE (fun s ↦ (s - 1) * riemannZeta s) 1 := by
  simpa using (orderLE_polynomial_mul_iff (X_sub_C_ne_zero 1) zero_le_one).mpr orderLE_riemannZeta

/-- The raw product vanishes at the pole, so it is not the pole-cleared function. -/
example : (X - C 1 : ℂ[X]).eval 1 * riemannZetaData.continuedL 1 ≠
    riemannZetaData.poleClearedContinuedL (X - C 1) 1 := by
  rw [riemannZetaData_poleClearedContinuedL_X_sub_one_apply_one]
  simp

end TauCeti.LFunctions
