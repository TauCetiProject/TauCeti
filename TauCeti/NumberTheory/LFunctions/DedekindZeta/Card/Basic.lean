/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.LFunctions.Data.SimplePoles
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completion
import TauCeti.NumberTheory.LFunctions.GammaFactor.Basic

/-!
# The completed L-function card of the Dedekind zeta function

For a number field `K` of degree `n = r₁ + 2 r₂` and discriminant `d_K`, the Dedekind zeta
function defines an analytic L-function card `TauCeti.LFunctions.dedekindZetaData K`:

* Dirichlet coefficients `normCoeff K (1 : IdealArithmeticFunction K)`, counting nonzero integral
  ideals of each positive norm (and vanishing at `0`),
* conductor `|d_K|`,
* `r₁` real gamma shifts `0` and `r₂` complex gamma shifts `0`, giving degree `[K : ℚ]` and
  gamma factor `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`,
* root number `1`,
* completed function `TauCeti.LFunctions.completedDedekindZeta K`,
* polar divisor consisting of simple poles at `0` and `1`.

This lightweight module defines `dedekindZetaData K` and proves self-duality,
`HasDirichletAgreement`, `HasMeromorphicContinuation`, and `HasFunctionalEquation`, keeping
coefficient-growth and `AnalyticLFunctionData.ofSeries` recovery in
`TauCeti.NumberTheory.LFunctions.DedekindZeta.Card.Series`.

The card definition and the self-duality, meromorphic-continuation, and functional-equation proofs
are closely adapted from `TauCeti.LFunctions.riemannZetaData`
(`TauCeti.NumberTheory.LFunctions.Data.RiemannZeta`) as their formal template.

## Main definitions

* `TauCeti.LFunctions.dedekindZetaData`: the analytic L-function card of `ζ_K`.

## Main results

* `TauCeti.LFunctions.dedekindZetaData_degree`, `TauCeti.LFunctions.dedekindZetaData_gammaFactor`,
  `TauCeti.LFunctions.dedekindZetaData_gammaFactor_ne_zero`,
  `TauCeti.LFunctions.dedekindZetaData_conductor_cast`, `TauCeti.LFunctions.dedekindZetaData_dual`:
  degree, gamma factor, right-half-plane nonvanishing, conductor cast, and self-duality.
* `TauCeti.LFunctions.dedekindZetaData_hasDirichletAgreement`,
  `TauCeti.LFunctions.dedekindZetaData_hasMeromorphicContinuation`,
  `TauCeti.LFunctions.dedekindZetaData_hasFunctionalEquation`: the analytic L-function axioms.
-/

public section

noncomputable section

open Complex ComplexConjugate NumberField NumberField.InfinitePlace

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The Dedekind zeta card** of a number field `K`. Coefficients
`normCoeff K (1 : IdealArithmeticFunction K)`, conductor `|d_K|`, `r₁` real gamma shifts `0` and
`r₂` complex gamma shifts `0`, root number `1`, completed function `completedDedekindZeta K`, and
simple poles at `0` and `1`. -/
def dedekindZetaData : AnalyticLFunctionData where
  coeff n := normCoeff K (1 : IdealArithmeticFunction K) n
  conductor := ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩
  gammaR := Multiset.replicate (nrRealPlaces K) 0
  gammaC := Multiset.replicate (nrComplexPlaces K) 0
  rootNumber := 1
  completed := completedDedekindZeta K
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp]
theorem dedekindZetaData_coeff (n : ℕ) :
    (dedekindZetaData K).coeff n = normCoeff K (1 : IdealArithmeticFunction K) n := (rfl)

@[simp]
theorem dedekindZetaData_conductor :
    (dedekindZetaData K).conductor =
      ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩ := (rfl)

/-- The complex-valued conductor of `dedekindZetaData K` is `((|discr K| : ℤ) : ℂ)`. -/
theorem dedekindZetaData_conductor_cast :
    (((dedekindZetaData K).conductor : ℕ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
  simp only [dedekindZetaData_conductor, PNat.mk_coe]
  rw [← Int.cast_natCast, Int.natCast_natAbs]

@[simp]
theorem dedekindZetaData_gammaR :
    (dedekindZetaData K).gammaR = Multiset.replicate (nrRealPlaces K) 0 := (rfl)

@[simp]
theorem dedekindZetaData_gammaC :
    (dedekindZetaData K).gammaC = Multiset.replicate (nrComplexPlaces K) 0 := (rfl)

@[simp]
theorem dedekindZetaData_rootNumber : (dedekindZetaData K).rootNumber = 1 := (rfl)

@[simp]
theorem dedekindZetaData_completed :
    (dedekindZetaData K).completed = completedDedekindZeta K := (rfl)

@[simp]
theorem dedekindZetaData_polarOrder :
    (dedekindZetaData K).polarOrder = Finsupp.single 0 1 + Finsupp.single 1 1 := (rfl)

/-- The degree of the Dedekind zeta card is the field degree `[K : ℚ] = r₁ + 2 r₂`. -/
@[simp]
theorem dedekindZetaData_degree : (dedekindZetaData K).degree = Module.finrank ℚ K := by
  simp only [AnalyticLFunctionData.degree_def, dedekindZetaData_gammaR, dedekindZetaData_gammaC,
    Multiset.card_replicate]
  exact InfinitePlace.card_add_two_mul_card_eq_rank K

/-- The gamma factor of the Dedekind zeta card is `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`. -/
@[simp]
theorem dedekindZetaData_gammaFactor (s : ℂ) :
    (dedekindZetaData K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  simp [AnalyticLFunctionData.gammaFactor_def]

/-- The gamma factor of `dedekindZetaData K` does not vanish on `0 < s.re`. -/
theorem dedekindZetaData_gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) :
    (dedekindZetaData K).gammaFactor s ≠ 0 :=
  (dedekindZetaData K).gammaFactor_ne_zero_of_forall_re_add_pos
    (fun μ hμ ↦ by simpa [Multiset.eq_of_mem_replicate hμ] using hs)
    (fun ν hν ↦ by simpa [Multiset.eq_of_mem_replicate hν] using hs)

/-- The Dedekind zeta card is self-dual. -/
@[simp]
theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext s
  · simp only [AnalyticLFunctionData.dual_coeff, dedekindZetaData_coeff, normCoeff_one_apply]
    split_ifs <;> simp
  · exact AnalyticLFunctionData.dual_conductor _
  · simp
  · simp
  · simp
  · simp [completedDedekindZeta_conj]
  · simp [AnalyticLFunctionData.single_zero_one_add_single_one_one_conj]

/-- On `Re s > 1`, `completedDedekindZeta K` agrees with the completed Dirichlet series of
`dedekindZetaData K`. -/
theorem dedekindZetaData_hasDirichletAgreement :
    (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by
    simp [normCoeff_apply_one]
  degree_pos := by
    rw [dedekindZetaData_degree]
    exact Module.finrank_pos
  completed_eq s hs := by
    have hcoeff : (dedekindZetaData K).coeff = ⇑(normCoeff K (1 : IdealArithmeticFunction K)) :=
      funext (dedekindZetaData_coeff K)
    rw [dedekindZetaData_completed, completedDedekindZeta_eq hs, dedekindZetaData_conductor_cast,
      dedekindZetaData_gammaFactor, hcoeff, dedekindZeta_eq_LSeries_normCoeff_one K s]
    ring

open AnalyticLFunctionData in
/-- The completed Dedekind zeta function is meromorphic on `ℂ` with simple poles at `0` and `1`
and no other singularities. -/
theorem dedekindZetaData_hasMeromorphicContinuation :
    (dedekindZetaData K).HasMeromorphicContinuation :=
  hasMeromorphicContinuation_of_polarOrder_eq_single_zero_one_add_single_one_one
    (dedekindZetaData_polarOrder K)
    (meromorphicOrderAt_completedDedekindZeta_zero K)
    (meromorphicOrderAt_completedDedekindZeta_one K)
    fun _ h0 h1 ↦ analyticAt_completedDedekindZeta h0 h1

/-- The completed Dedekind zeta function satisfies the functional equation `Λ_K(s) = Λ_K(1 - s)`
with root number `1`. -/
theorem dedekindZetaData_hasFunctionalEquation :
    (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    simpa only [dedekindZetaData_polarOrder] using
      AnalyticLFunctionData.single_zero_one_add_single_one_one_one_sub_conj s
  completed_eq s _ _ := by
    rw [dedekindZetaData_dual, dedekindZetaData_rootNumber, one_mul, dedekindZetaData_completed,
      completedDedekindZeta_one_sub]

end TauCeti.LFunctions
