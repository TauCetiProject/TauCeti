/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.CriticalLine
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection
import TauCeti.NumberTheory.LFunctions.Continued.Dirichlet

/-!
# The generalized Riemann hypothesis for analytic L-function records

The hypothesis of a record says that every point of positive meromorphic order of its
completed function lies on the critical line. It does not constrain poles or read the values
assigned there. Unlike a statement about the divisor, it rejects an identically zero completed
function, which has infinite order everywhere.

The functional equation reflects orders across the critical line. Thus one can check just the
right half-plane, using the uncompleted function there when its gamma factor is regular and
nonzero. The resulting criterion applies to primitive Dirichlet characters, and for the zeta
record it is equivalent to Mathlib's `RiemannHypothesis`, via `AllOnCriticalLine` for
`completedRiemannZeta`; for the record of a primitive Dirichlet character `χ` it is
`TauCeti.DirichletGRH χ`. The dual has the same zero-free right half-planes by
`AnalyticLFunctionData.dual_completed` and `zeroFreeRightOf_conj_conj_iff`.
-/

public section

open Set Complex ComplexConjugate

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData}

/-- All zeros of the completed function, read as points of positive meromorphic order, lie on
`re s = 1 / 2`. This is intended for records with meromorphic continuation. -/
def GeneralizedRiemannHypothesis (d : AnalyticLFunctionData) : Prop :=
  ∀ s : ℂ, 0 < meromorphicOrderAt d.completed s → s.re = 1 / 2

/-- The order characterization of the generalized Riemann hypothesis. -/
theorem generalizedRiemannHypothesis_iff :
    d.GeneralizedRiemannHypothesis ↔ ∀ s : ℂ, 0 < meromorphicOrderAt d.completed s → s.re = 1 / 2 :=
  Iff.rfl

/-- Dualizing a record preserves the generalized Riemann hypothesis. -/
@[simp] theorem generalizedRiemannHypothesis_dual_iff (d : AnalyticLFunctionData) :
    d.dual.GeneralizedRiemannHypothesis ↔ d.GeneralizedRiemannHypothesis := by
  simp only [generalizedRiemannHypothesis_iff, dual_completed, meromorphicOrderAt_conj_conj]
  exact (conjCLE.toEquiv.forall_congr fun s ↦ by simp).symm

/-- The hypothesis rules out completed zeros to the right of the critical line, without any
functional equation assumption. -/
theorem GeneralizedRiemannHypothesis.zeroFreeRightOf_completed
    (h : d.GeneralizedRiemannHypothesis) : ZeroFreeRightOf (1 / 2) d.completed := by
  rw [zeroFreeRightOf_iff]
  exact fun s hs ↦ le_of_not_gt fun hpos ↦
    hs.ne ((generalizedRiemannHypothesis_iff.mp h s hpos).symm)

/-- Under the functional equation, absence of zeros right of the critical line is enough to
place all zeros of the completed function on that line. -/
theorem HasFunctionalEquation.generalizedRiemannHypothesis_iff_zeroFreeRightOf_completed
    (hfe : d.HasFunctionalEquation) :
    d.GeneralizedRiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) d.completed := by
  refine ⟨GeneralizedRiemannHypothesis.zeroFreeRightOf_completed, fun h ↦ ?_⟩
  rw [generalizedRiemannHypothesis_iff]
  rw [zeroFreeRightOf_iff] at h
  intro s hpos
  apply le_antisymm
  · exact le_of_not_gt fun hs ↦ (not_lt_of_ge (h s hs)) hpos
  · by_contra! hs
    have hre : 1 / 2 < (1 - conj s).re := by
      simp only [sub_re, one_re, conj_re]
      linarith
    have horder := h (1 - conj s) hre
    rw [hfe.meromorphicOrderAt_completed_one_sub, dual_completed, meromorphicOrderAt_conj_conj,
      conj_conj] at horder
    exact (not_lt_of_ge horder) hpos

/-- For a meromorphic completed function of finite order at some point (not identically zero),
the order and divisor formulations of the generalized Riemann hypothesis agree. -/
theorem generalizedRiemannHypothesis_iff_allOnCriticalLine (d : AnalyticLFunctionData)
    (hm : Meromorphic d.completed) {s₀ : ℂ} (h₀ : meromorphicOrderAt d.completed s₀ ≠ ⊤) :
    d.GeneralizedRiemannHypothesis ↔ AllOnCriticalLine d.completed univ univ := by
  rw [generalizedRiemannHypothesis_iff, allOnCriticalLine_iff]
  simp only [mem_univ, forall_const]
  refine forall_congr' fun s ↦ ?_
  have hfin := hm.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ s₀) (mem_univ s) h₀
  rw [← hm.meromorphicOn.coe_divisor_eq_meromorphicOrderAt (mem_univ s) hfin,
    ← WithTop.coe_zero, WithTop.coe_lt_coe]

/-- The uncompleted function tests the generalized Riemann hypothesis if the gamma factor is
nonzero throughout the half-plane to the right of the critical line. -/
theorem HasFunctionalEquation.generalizedRiemannHypothesis_iff_zeroFreeRightOf_continuedL
    (hfe : d.HasFunctionalEquation) (hm : Meromorphic d.completed)
    (hγ : ∀ s : ℂ, 1 / 2 < s.re → d.gammaFactor s ≠ 0) :
    d.GeneralizedRiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) d.continuedL := by
  rw [hfe.generalizedRiemannHypothesis_iff_zeroFreeRightOf_completed,
    zeroFreeRightOf_iff, zeroFreeRightOf_iff]
  refine forall₂_congr fun s hs ↦ ?_
  rw [d.meromorphicOrderAt_continuedL hm,
    (d.meromorphicOrderAt_gammaFactor_eq_zero_iff s).mpr (hγ s hs), sub_zero]

/-- If every gamma shift has real part at least `-1/2`, the uncompleted function is zero-free
right of the critical line exactly when the completed function satisfies the hypothesis. -/
theorem HasFunctionalEquation.generalizedRiemannHypothesis_iff_zeroFreeRightOf_continuedL_of_shifts
    (hfe : d.HasFunctionalEquation) (hm : Meromorphic d.completed)
    (hR : ∀ μ ∈ d.gammaR, -(1 / 2) ≤ μ.re) (hC : ∀ ν ∈ d.gammaC, -(1 / 2) ≤ ν.re) :
    d.GeneralizedRiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) d.continuedL :=
  hfe.generalizedRiemannHypothesis_iff_zeroFreeRightOf_continuedL hm fun s hs ↦
    d.gammaFactor_ne_zero_of_forall_re_add_pos (fun μ hμ ↦ by linarith [hR μ hμ])
      (fun ν hν ↦ by linarith [hC ν hν])

end TauCeti.LFunctions.AnalyticLFunctionData

namespace TauCeti.LFunctions

/-- The Riemann hypothesis for the zeta record is Mathlib's `RiemannHypothesis`. -/
@[simp] theorem riemannZetaData_generalizedRiemannHypothesis_iff :
    riemannZetaData.GeneralizedRiemannHypothesis ↔ RiemannHypothesis := by
  rw [riemannZetaData.generalizedRiemannHypothesis_iff_allOnCriticalLine
    riemannZetaData_hasMeromorphicContinuation.meromorphic (s₀ := 1),
    riemannZetaData_completed, allOnCriticalLine_completedRiemannZeta_iff]
  simp [riemannZetaData_completed, meromorphicOrderAt_completedRiemannZeta_one]

/-- For a primitive Dirichlet character, the completed record satisfies the hypothesis exactly
when Mathlib's Dirichlet L-function is zero-free right of the critical line. -/
theorem dirichletData_generalizedRiemannHypothesis_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (dirichletData χ hχ).GeneralizedRiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) χ.LFunction := by
  rw [← dirichletData_continuedL χ hχ]
  have hfe := dirichletData_hasFunctionalEquation χ hχ
  refine hfe.generalizedRiemannHypothesis_iff_zeroFreeRightOf_continuedL_of_shifts
    (dirichletData_hasMeromorphicContinuation χ hχ).meromorphic ?_ ?_
  · rw [dirichletData_gammaR]
    simp only [Multiset.mem_singleton]
    rintro _ rfl
    split <;> norm_num
  · simp [dirichletData_gammaC]

/-- For a primitive Dirichlet character, the hypothesis of the completed record is
`TauCeti.DirichletGRH χ`. -/
theorem dirichletData_generalizedRiemannHypothesis_iff_dirichletGRH {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (dirichletData χ hχ).GeneralizedRiemannHypothesis ↔ DirichletGRH χ := by
  rw [dirichletData_generalizedRiemannHypothesis_iff,
    χ.zeroFreeRightOf_one_half_LFunction_iff_forall_re_pos, χ.dirichletGRH_def]

end TauCeti.LFunctions
