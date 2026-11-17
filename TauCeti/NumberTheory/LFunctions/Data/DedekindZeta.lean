/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed.Zeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial

/-!
# The completed L-function card of the Dedekind zeta function

For a number field `K`, the Dedekind zeta function has Dirichlet coefficients
`n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}` (matching Mathlib's
`NumberField.dedekindZeta`), conductor `|discr K|` (`(discr K).natAbs`), `r₁ = nrRealPlaces K`
real gamma shifts at `0` and `r₂ = nrComplexPlaces K` complex gamma shifts at `0`, degree
`r₁ + 2 r₂ = [K : ℚ]`, root number `1`, completed function
`TauCeti.LFunctions.completedDedekindZeta K`, and simple poles at `0` and `1`.

This file defines the card `TauCeti.LFunctions.dedekindZetaData K`, proves that it is self-dual,
and establishes all four analytic predicates:

* `HasAverageCoefficientGrowth` (from `TauCeti.abscissaOfAbsConv_dedekindZetaCoeff`),
* `HasDirichletAgreement`,
* `HasMeromorphicContinuation`,
* `HasFunctionalEquation`.

Because `completedDedekindZeta K` is already in meromorphic normal form on the whole complex plane,
`AnalyticLFunctionData.ofSeries` recovers `dedekindZetaData K` identically
(`ofSeries_dedekindZetaData`).

Over `K = ℚ`, we verify that `completedDedekindZeta ℚ` agrees with the meromorphic normal form of
Mathlib's `completedRiemannZeta` (and agrees pointwise off `{0, 1}`), that `dedekindZetaC ℚ`
agrees with `riemannZeta` off `1` (giving `dedekindZetaC ℚ 0 = -1 / 2`), and that
`dedekindZetaData ℚ` compares via `EqOffZero` with the normalized `riemannZetaData` while remaining
distinct as a record because `coeff 0` is `1` (the zero ideal) rather than `0`.

## Main definitions

* `TauCeti.LFunctions.dedekindZetaData`: the analytic L-function card of `ζ_K`.

## Main results

* `TauCeti.LFunctions.dedekindZetaData_dual`: `dedekindZetaData K` is self-dual.
* `TauCeti.LFunctions.dedekindZetaData_hasAverageCoefficientGrowth`,
  `TauCeti.LFunctions.dedekindZetaData_hasDirichletAgreement`,
  `TauCeti.LFunctions.dedekindZetaData_hasMeromorphicContinuation`,
  `TauCeti.LFunctions.dedekindZetaData_hasFunctionalEquation`.
* `TauCeti.LFunctions.ofSeries_dedekindZetaData`: exact recovery by
  `AnalyticLFunctionData.ofSeries`.
* `TauCeti.LFunctions.completedDedekindZeta_rat_eq_toMeromorphicNFOn`,
  `TauCeti.LFunctions.dedekindZetaC_rat_eq`, `TauCeti.LFunctions.dedekindZetaC_rat_zero`,
  `TauCeti.LFunctions.dedekindZetaData_rat_eqOffZero`:
  identification over `ℚ` with Mathlib's Riemann zeta function and `riemannZetaData`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

noncomputable section

open Complex ComplexConjugate NumberField NumberField.InfinitePlace Set

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The Dedekind zeta card** of a number field `K`: ideal-counting coefficients
`Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}`, conductor `|discr K|`, `nrRealPlaces K` real
and `nrComplexPlaces K` complex gamma shifts at `0`, root number `1`, completed function
`completedDedekindZeta K`, and simple poles at `0` and `1`. -/
def dedekindZetaData : AnalyticLFunctionData where
  coeff n := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  conductor := ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩
  gammaR := Multiset.replicate (nrRealPlaces K) 0
  gammaC := Multiset.replicate (nrComplexPlaces K) 0
  rootNumber := 1
  completed := completedDedekindZeta K
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp]
theorem dedekindZetaData_coeff (n : ℕ) :
    (dedekindZetaData K).coeff n = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) :=
  (rfl)

@[simp]
theorem dedekindZetaData_conductor :
    (dedekindZetaData K).conductor = ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩ :=
  (rfl)

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

/-- The degree of `dedekindZetaData K` is the field extension degree `[K : ℚ]`. -/
@[simp]
theorem dedekindZetaData_degree : (dedekindZetaData K).degree = Module.finrank ℚ K := by
  simp only [AnalyticLFunctionData.degree_def, dedekindZetaData_gammaR, dedekindZetaData_gammaC,
    Multiset.card_replicate]
  exact card_add_two_mul_card_eq_rank K

/-- The gamma factor of `dedekindZetaData K` is `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`. -/
@[simp]
theorem dedekindZetaData_gammaFactor (s : ℂ) :
    (dedekindZetaData K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  simp [AnalyticLFunctionData.gammaFactor_def]

private theorem card_absNorm_eq_dedekindZetaCoeff (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} = TauCeti.dedekindZetaCoeff K n := by
  by_cases hn : n = 0
  · subst hn
    simp only [Ideal.absNorm_eq_zero_iff, TauCeti.dedekindZetaCoeff_zero]
    exact Nat.card_unique
  · rw [← TauCeti.card_normFiber_eq_dedekindZetaCoeff K hn, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr <| Equiv.symm <|
      (Equiv.subtypeEquivRight fun I ↦ TauCeti.mem_normFiber (K := K)).trans
        { toFun := fun I ↦ ⟨I.1.1, I.2⟩
          invFun := fun I ↦ ⟨⟨I.1, by
            rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
            exact fun hzero ↦ hn (I.2.symm.trans hzero)⟩, I.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }

/-- The Dedekind zeta coefficients satisfy the average absolute growth bound. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le]
  have hcoeff : (dedekindZetaData K).coeff = fun n ↦ (TauCeti.dedekindZetaCoeff K n : ℂ) := by
    funext n
    rw [dedekindZetaData_coeff, card_absNorm_eq_dedekindZetaCoeff]
  rw [hcoeff, TauCeti.abscissaOfAbsConv_dedekindZetaCoeff K]

/-- The Dedekind zeta card is its own dual. -/
@[simp]
theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext
  · simp
  · simp; rfl
  · simp
  · simp
  · simp
  · simp [completedDedekindZeta_conj]
  · simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
      map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- On `Re s > 1`, the completed Dedekind zeta function is `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`,
with `a(1) = 1` (the unit ideal `⊤`) and positive degree `[K : ℚ] > 0`. -/
theorem dedekindZetaData_hasDirichletAgreement :
    (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by
    simp only [dedekindZetaData_coeff, Ideal.absNorm_eq_one_iff]
    norm_cast
    exact Nat.card_unique
  degree_pos := by
    rw [dedekindZetaData_degree]
    exact Module.finrank_pos
  completed_eq s hs := by
    have hcond : (((dedekindZetaData K).conductor : ℕ) : ℂ) = ((|discr K| : ℤ) : ℂ) := by
      rw [dedekindZetaData_conductor, PNat.mk_coe, ← Int.cast_natCast, Int.natCast_natAbs]
    have hL : LSeries (dedekindZetaData K).coeff s = dedekindZeta K s := rfl
    rw [dedekindZetaData_completed, completedDedekindZeta_eq K hs, dedekindZetaData_gammaFactor,
      hcond, hL]
    ring

/-- The completed Dedekind zeta function is meromorphic on `ℂ`, with simple poles at `0` and `1`
and analytic everywhere else. -/
theorem dedekindZetaData_hasMeromorphicContinuation :
    (dedekindZetaData K).HasMeromorphicContinuation where
  meromorphic := meromorphic_completedDedekindZeta K
  meromorphicOrderAt_eq p hp := by
    by_cases h0 : p = 0
    · subst h0
      simp [meromorphicOrderAt_completedDedekindZeta_zero]
    by_cases h1 : p = 1
    · subst h1
      simp [meromorphicOrderAt_completedDedekindZeta_one]
    simp [Ne.symm h0, Ne.symm h1] at hp
  analyticAt p hp := by
    refine analyticAt_completedDedekindZeta K ?_ ?_ <;> rintro rfl <;> simp at hp

/-- The functional equation `Λ_K(s) = Λ_K(1 - s)` of the completed Dedekind zeta function, with
root number `1`. -/
theorem dedekindZetaData_hasFunctionalEquation :
    (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    have hconj (z : ℂ) : (dedekindZetaData K).polarOrder (conj z) =
        (dedekindZetaData K).polarOrder z := by
      rw [← AnalyticLFunctionData.dual_polarOrder_apply, dedekindZetaData_dual]
    have e0 : (0 : ℂ) = 1 - s ↔ 1 = s := by rw [eq_comm, sub_eq_zero]
    have e1 : (1 : ℂ) = 1 - s ↔ 0 = s := by rw [eq_comm, sub_eq_self, eq_comm]
    rw [← map_one (starRingEnd ℂ), ← map_sub, hconj]
    simp only [dedekindZetaData_polarOrder, Finsupp.add_apply, Finsupp.single_apply, e0, e1]
    rw [add_comm]
  completed_eq s hs _ := by
    have h0 : s ≠ 0 := by rintro rfl; simp at hs
    have h1 : s ≠ 1 := by rintro rfl; simp at hs
    rw [dedekindZetaData_dual, dedekindZetaData_rootNumber, one_mul, dedekindZetaData_completed,
      completedDedekindZeta_one_sub K h0 h1]

/-- Constructing the Dedekind-zeta card from its Dirichlet series via
`AnalyticLFunctionData.ofSeries` recovers `dedekindZetaData K` exactly, because
`completedDedekindZeta K` is already in meromorphic normal form on `ℂ`. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
      dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq
    (dedekindZetaData_hasDirichletAgreement K)
    (dedekindZetaData_hasFunctionalEquation K)
    (meromorphicNFOn_completedDedekindZeta K) ?_ ?_
  · simp
  · rw [dedekindZetaData_completed, completedDedekindZeta_eq K (by norm_num)]
    have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
    have hcp : ((|discr K| : ℤ) : ℂ) ^ ((2 : ℂ) / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]
      exact fun h ↦ hd h.1
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero hcp
        (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos (by norm_num))))
        (pow_ne_zero _ (Complex.Gammaℂ_ne_zero_of_re_pos (by norm_num))))
      (TauCeti.dedekindZeta_ne_zero_of_one_lt_re (K := K) (by norm_num))

/-! ### Specialization to `ℚ` and comparison with `riemannZetaData` -/

private theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s := by
  rw [TauCeti.dedekindZeta_eq_LSeries_dedekindZetaCoeff,
    ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  simp [TauCeti.dedekindZetaCoeff_rat, hn]

/-- Over `ℚ`, `completedDedekindZeta ℚ` is the meromorphic normal form of Mathlib's
`completedRiemannZeta`. -/
theorem completedDedekindZeta_rat_eq_toMeromorphicNFOn :
    completedDedekindZeta ℚ = toMeromorphicNFOn completedRiemannZeta univ := by
  rw [completedDedekindZeta_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn meromorphic_completedRiemannZeta
    (fun s hs ↦ analyticAt_completedRiemannZeta
      (by rintro rfl; norm_num at hs) (by rintro rfl; norm_num at hs))
    fun s hs ↦ ?_
  have hs' : 1 < s.re := hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs'
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [discr_rat, nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    dedekindZeta_rat_eq_riemannZeta hs', riemannZeta_def_of_ne_zero hs0]
  simp [field]

/-- Over `ℚ`, `completedDedekindZeta ℚ` agrees pointwise with `completedRiemannZeta` away from
`{0, 1}`. -/
theorem completedDedekindZeta_rat_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta ℚ s = completedRiemannZeta s := by
  rw [completedDedekindZeta_rat_eq_toMeromorphicNFOn]
  exact toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
    (analyticAt_completedRiemannZeta h0 h1)

/-- Over `ℚ`, `dedekindZetaC ℚ` agrees pointwise with `riemannZeta` away from `s = 1`. -/
theorem dedekindZetaC_rat_eq {s : ℂ} (h1 : s ≠ 1) :
    dedekindZetaC ℚ s = riemannZeta s := by
  refine eq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_dedekindZetaC ℚ) meromorphic_riemannZeta
    (fun z hz ↦ by rw [dedekindZetaC_eq ℚ hz, dedekindZeta_rat_eq_riemannZeta hz])
    (analyticAt_dedekindZetaC ℚ h1) (analyticOn_riemannZeta s h1)

/-- Over `ℚ`, `dedekindZetaC ℚ 0 = -1 / 2`. -/
theorem dedekindZetaC_rat_zero : dedekindZetaC ℚ 0 = -1 / 2 := by
  rw [dedekindZetaC_rat_eq zero_ne_one, riemannZeta_zero]

/-- Over `ℚ`, the analytic L-function card `dedekindZetaData ℚ` compares via `EqOffZero` with
`riemannZetaData` (with its completed function put in meromorphic normal form). The two cards are
not equal because `dedekindZetaData ℚ` has zeroth coefficient `1` (the zero ideal), whereas
`riemannZetaData` has `0`. -/
theorem dedekindZetaData_rat_eqOffZero :
    (dedekindZetaData ℚ).EqOffZero
      { riemannZetaData with completed := toMeromorphicNFOn completedRiemannZeta univ } where
  coeff_eq n hn := by
    rw [dedekindZetaData_coeff, card_absNorm_eq_dedekindZetaCoeff]
    simp [TauCeti.dedekindZetaCoeff_rat, hn]
  conductor_eq := by
    apply Subtype.ext
    simp
  gammaR_eq := by
    simp [nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)]
  gammaC_eq := by simp
  rootNumber_eq := by simp
  completed_eq := completedDedekindZeta_rat_eq_toMeromorphicNFOn
  polarOrder_eq := by
    simp [dedekindZetaData_polarOrder, riemannZetaData_polarOrder]

/-- `dedekindZetaData ℚ` differs from the normalized `riemannZetaData` at index `0`. -/
theorem dedekindZetaData_rat_ne_riemannZetaData_normalized :
    dedekindZetaData ℚ ≠
      { riemannZetaData with completed := toMeromorphicNFOn completedRiemannZeta univ } := by
  intro h
  have h0 := congrArg (fun d : AnalyticLFunctionData ↦ d.coeff 0) h
  rw [dedekindZetaData_coeff, card_absNorm_eq_dedekindZetaCoeff] at h0
  simp at h0

end TauCeti.LFunctions
