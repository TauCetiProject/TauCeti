/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Growth
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.HeckeIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.LFunctions.GammaFactor.Order

/-!
# The completed Dedekind zeta function and its functional equation

Summing the completed partial zeta functions `completedPartialZeta I` from
`TauCeti.NumberTheory.LFunctions.DedekindZeta.HeckeIntegral` over a system of representatives of
the ideal class group of a number field `K` gives the completed Dedekind zeta function

`Λ_K(s) = |d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`,

continued canonically from `Re s > 1` as `TauCeti.LFunctions.completedDedekindZeta K`. Because
each partial zeta function has simple poles at `s = 0` and `s = 1` with residues `-2 a₀` and
`2 a₀` (where `a₀ = 2^(r₁ + r₂ - 1) R / w` is `mellinConstant K`), is analytic everywhere else,
and satisfies `Z(I, 1 - s) = Z(I^∨, s)` against the trace dual `I^∨ = FractionalIdeal.dual ℤ ℚ I`,
summing over the `h = classNumber K` ideal classes — which the trace dual permutes — yields the
meromorphic continuation, poles, residues, and functional equation of `Λ_K`:

* `completedDedekindZeta_eq_sum_completedPartialZeta`: `Λ_K(s)` is the sum of
  `completedPartialZeta (rep c) s` over any system `rep` of ideal-class representatives.
* `analyticAt_completedDedekindZeta`, `meromorphicOrderAt_completedDedekindZeta_zero`,
  `meromorphicOrderAt_completedDedekindZeta_one`: `Λ_K` is meromorphic on `ℂ`, analytic away from
  `0` and `1`, with simple poles at both points.
* `tendsto_sub_one_mul_completedDedekindZeta` and `tendsto_mul_completedDedekindZeta_zero`: the
  residues at `1` and `0` are `± 2^(r₁ + r₂) h R / w`, equal to
  `|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ Res_{s=1} ζ_K` (`completedDedekindZeta_residue_eq`).
* `completedDedekindZeta_one_sub` and `completedDedekindZeta_one_sub_eventuallyEq`: the functional
  equation `Λ_K(1 - s) = Λ_K(s)` off `{0, 1}` and as punctured germs everywhere.
* `completedDedekindZeta_conj`: reflection symmetry `Λ_K(conj s) = conj Λ_K(s)` on all of `ℂ`.

Dividing by the archimedean and discriminant factor (whose reciprocal is entire, with a zero of
order `r₁ + r₂ = Units.rank K + 1` at `s = 0`) recovers the analytic properties of the continued
Dedekind zeta function `dedekindZetaC K`:

* `dedekindZetaC_eq`, `dedekindZetaC_eventuallyEq`, `dedekindZetaC_conj`: agreement with Mathlib's
  `NumberField.dedekindZeta K` on `Re s > 1` (pointwise and locally) and reflection symmetry.
* `analyticAt_dedekindZetaC`, `meromorphicOrderAt_dedekindZetaC_one`,
  `tendsto_sub_one_mul_dedekindZetaC`: `dedekindZetaC K` is analytic away from `s = 1`, where it
  has a simple pole with residue `NumberField.dedekindZeta_residue K`.
* `meromorphicOrderAt_dedekindZetaC_zero` and `tendsto_dedekindZetaC_div_pow_rank_zero`: at
  `s = 0`, `dedekindZetaC K` has a zero of order `Units.rank K = r₁ + r₂ - 1` with leading
  coefficient `-h R / w` (Neukirch VII (5.11)).

Finally, `TauCeti.LFunctions.dedekindZetaData K` packages `ζ_K` as a self-dual
`AnalyticLFunctionData` card of degree `[K : ℚ]`, conductor `|d_K|`, and root number `1`,
satisfying `HasAverageCoefficientGrowth`, `HasDirichletAgreement`, `HasMeromorphicContinuation`,
`HasFunctionalEquation`, and exact recovery via `AnalyticLFunctionData.ofSeries`.

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the completed Dedekind zeta function `Λ_K`.
* `TauCeti.LFunctions.dedekindZetaData`: the analytic L-function card of `ζ_K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.9) and (5.11).
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
-/

public section

noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace NumberField.Units Set
  TauCeti.GlobalNumberFields
open scoped ComplexConjugate nonZeroDivisors Real Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-! ### The completed Dedekind zeta function -/

/-- **The completed Dedekind zeta function** `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)` of a number
field `K`, canonically continued in meromorphic normal form from the half-plane `Re s > 1`. -/
def completedDedekindZeta : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

/-- Defining equation of `completedDedekindZeta`. -/
theorem completedDedekindZeta_def :
    completedDedekindZeta K = meromorphicContinuation 1 fun s ↦
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := (rfl)

/-- The completed Dedekind zeta function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_completedDedekindZeta :
    MeromorphicNFOn (completedDedekindZeta K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The completed Dedekind zeta function is meromorphic on the plane. -/
theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedDedekindZeta K).meromorphicOn

/-! ### Sum over ideal classes -/

/-- A chosen representative in `(FractionalIdeal (𝓞 K)⁰ K)ˣ` for each ideal class. -/
private def classRep (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (ClassGroup.mk0_surjective (R := 𝓞 K) c).choose

private theorem classGroup_mk_classRep (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (classRep K c) = c := by
  rw [classRep, ClassGroup.mk_mk0]
  exact (ClassGroup.mk0_surjective (R := 𝓞 K) c).choose_spec

/-- The trace dual `I^∨ = FractionalIdeal.dual ℤ ℚ I` as a unit of fractional ideals. -/
private def traceDualUnit {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

private theorem traceDualUnit_eq_mul_inv {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceDualUnit I = traceDualUnit (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) * I⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val]
  exact FractionalIdeal.dual_eq_mul_inv ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)

variable {K}

/-- On `Re s > 1`, summing the completed partial zeta functions over any system of class-group
representatives gives the completed Dedekind zeta series. -/
private theorem sum_completedPartialZeta_eq_of_one_lt_re
    {rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) {s : ℂ} (hs : 1 < s.re) :
    ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s =
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  let : Fintype (RayClassGroup (Modulus.one K)) :=
    Fintype.ofEquiv (ClassGroup (𝓞 K)) oneEquivClassGroup.symm.toEquiv
  let e : RayClassGroup (Modulus.one K) ≃ ClassGroup (𝓞 K) :=
    oneEquivClassGroup.toEquiv.trans (Equiv.inv (ClassGroup (𝓞 K)))
  rw [← Equiv.sum_comp e]
  have hterm (c : RayClassGroup (Modulus.one K)) :
      completedPartialZeta (rep (e c)) s =
        ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K *
          LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s := by
    refine completedPartialZeta_eq_LSeries_rayClassCoeff (rep (e c)) c ?_ hs
    simp [e, hrep]
  simp_rw [hterm, ← Finset.mul_sum, sum_LSeries_rayClassCoeff_one hs]

private theorem meromorphic_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s := fun s ↦
  MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta (rep c) s

private theorem analyticAt_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z) s :=
  Finset.analyticAt_fun_sum _ fun c _ ↦ analyticAt_completedPartialZeta (rep c) h0 h1

private theorem analyticOnNhd_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z)
      {s | 1 < s.re} := fun _ hs ↦
  analyticAt_sum_completedPartialZeta rep (by rintro rfl; norm_num at hs)
    (by rintro rfl; norm_num at hs)

/-- **Germ decomposition over the ideal class group.** At every point of the plane, including the
poles `0` and `1`, `completedDedekindZeta K` has the punctured germ of the sum of
`completedPartialZeta (rep c)` over any system `rep` of ideal-class representatives. -/
theorem completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    {rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (z : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] z]
      fun s ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s :=
  meromorphicContinuation_eventuallyEq
    (meromorphic_sum_completedPartialZeta rep)
    (analyticOnNhd_sum_completedPartialZeta rep)
    (fun _ hs ↦ sum_completedPartialZeta_eq_of_one_lt_re hrep hs) z

/-- **Decomposition over the ideal class group.** Away from the poles `0` and `1`,
`completedDedekindZeta K s` is the sum of the completed partial zeta functions over any system
`rep` of ideal-class representatives. -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta
    {rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta K s = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s :=
  meromorphicContinuation_apply
    (meromorphic_sum_completedPartialZeta rep)
    (analyticOnNhd_sum_completedPartialZeta rep)
    (fun _ hs ↦ sum_completedPartialZeta_eq_of_one_lt_re hrep hs)
    (analyticAt_sum_completedPartialZeta rep h0 h1)

/-! ### Half-plane agreement, regularity, poles, residues, and symmetries -/

variable (K)

/-- On `Re s > 1`, `completedDedekindZeta K s` equals
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [completedDedekindZeta_eq_sum_completedPartialZeta (classGroup_mk_classRep K) h0 h1,
    sum_completedPartialZeta_eq_of_one_lt_re (classGroup_mk_classRep K) hs]

/-- The completed Dedekind zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  rw [← (meromorphicNFOn_completedDedekindZeta K
        (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_congr
      (completedDedekindZeta_eventuallyEq_sum_completedPartialZeta (classGroup_mk_classRep K) s)]
  exact (analyticAt_sum_completedPartialZeta (classRep K) h0 h1).meromorphicOrderAt_nonneg

/-- The residue `2^(r₁ + r₂) h R / w` of `completedDedekindZeta K` at `s = 1` equals the completed
factor at `1` times `NumberField.dedekindZeta_residue K`. -/
theorem completedDedekindZeta_residue_eq :
    ((discr K).natAbs : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
        Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ) =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
        (regulator K : ℂ) / (torsionOrder K : ℂ) := by
  have hD_pos : (0 : ℝ) < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hD_natAbs : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hsqrt : ((discr K).natAbs : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt |(discr K : ℝ)| : ℂ) := by
    rw [Real.sqrt_eq_rpow, ← hD_natAbs, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hsq : (Real.sqrt |(discr K : ℝ)| : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD_pos).ne'
  rw [hsqrt, Gammaℝ_one, one_pow, mul_one, Gammaℂ_one, dedekindZeta_residue_def]
  push_cast
  rw [pow_add, one_div, inv_pow, mul_pow]
  field_simp [hpi, hw, hsq]

private theorem classNumber_mul_two_mul_mellinConstant :
    (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) =
      2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
        (regulator K : ℂ) / (torsionOrder K : ℂ) := by
  have hpos : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have h2 : (2 : ℂ) * (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) =
      (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [mellinConstant_def]
  push_cast
  field_simp [hw]
  linear_combination (classNumber K : ℂ) * (regulator K : ℂ) * h2

private theorem completedDedekindZeta_residue_ne_zero :
    (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
      (regulator K : ℂ) / (torsionOrder K : ℂ) ≠ 0 := by
  rw [← classNumber_mul_two_mul_mellinConstant]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (classNumber_ne_zero K))
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))

/-- **Residue of `completedDedekindZeta K` at `s = 1`**:
`(s - 1) * Λ_K(s) → 2^(r₁ + r₂) h R / w` as `s → 1`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
        (regulator K : ℂ) / (torsionOrder K : ℂ))) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ClassGroup (𝓞 K)))
    fun c _ ↦ tendsto_sub_one_mul_completedPartialZeta (classRep K c)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← classNumber,
    classNumber_mul_two_mul_mellinConstant] at hsum
  refine hsum.congr' ?_
  filter_upwards
    [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta (classGroup_mk_classRep K) 1]
    with s hs
  rw [hs, Finset.mul_sum]

/-- **Residue of `completedDedekindZeta K` at `s = 0`**:
`s * Λ_K(s) → -(2^(r₁ + r₂) h R / w)` as `s → 0`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
        (regulator K : ℂ) / (torsionOrder K : ℂ)))) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ClassGroup (𝓞 K)))
    fun c _ ↦ tendsto_mul_completedPartialZeta_zero (classRep K c)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg, ← classNumber,
    classNumber_mul_two_mul_mellinConstant] at hsum
  refine hsum.congr' ?_
  filter_upwards
    [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta (classGroup_mk_classRep K) 0]
    with s hs
  rw [hs, Finset.mul_sum]

/-- The completed Dedekind zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) := by
  refine (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (neg_ne_zero.mpr (completedDedekindZeta_residue_ne_zero K)) ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K

/-- The completed Dedekind zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) := by
  refine (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (completedDedekindZeta_residue_ne_zero K) ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedDedekindZeta K

/-- **Functional equation of the completed Dedekind zeta function**, Neukirch VII (5.9):
`Λ_K(1 - s) = Λ_K(s)` away from the poles `0` and `1`. -/
theorem completedDedekindZeta_one_sub {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  have hs0' : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  have hs1' : 1 - s ≠ 1 := fun h ↦ h0 (by linear_combination -h)
  rw [completedDedekindZeta_eq_sum_completedPartialZeta (classGroup_mk_classRep K) hs0' hs1',
    completedDedekindZeta_eq_sum_completedPartialZeta (classGroup_mk_classRep K) h0 h1]
  let σ : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    (Equiv.inv (ClassGroup (𝓞 K))).trans
      (Equiv.mulLeft (ClassGroup.mk K (traceDualUnit (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))))
  have hterm (c : ClassGroup (𝓞 K)) :
      completedPartialZeta (classRep K c) (1 - s) = completedPartialZeta (classRep K (σ c)) s := by
    rw [completedPartialZeta_one_sub (J := traceDualUnit (classRep K c)) rfl h0 h1]
    refine congrFun (completedPartialZeta_eq_of_class_eq ?_) s
    rw [traceDualUnit_eq_mul_inv, map_mul, map_inv, classGroup_mk_classRep,
      classGroup_mk_classRep]
    rfl
  simp_rw [hterm]
  exact Equiv.sum_comp σ fun c ↦ completedPartialZeta (classRep K c) s

/-- **Functional equation of the completed Dedekind zeta function, as punctured germs** at every
point of the plane, including the poles `0` and `1`. -/
theorem completedDedekindZeta_one_sub_eventuallyEq (s : ℂ) :
    (fun z ↦ completedDedekindZeta K (1 - z)) =ᶠ[𝓝[≠] s] completedDedekindZeta K := by
  have hfin : ({0, 1} : Set ℂ).Finite := (Set.finite_singleton 1).insert 0
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite univ_mem hfin.to_subtype] with z hz
  simp only [Set.mem_sdiff, mem_univ, mem_insert_iff, mem_singleton_iff, true_and, not_or] at hz
  exact completedDedekindZeta_one_sub K hz.1 hz.2

private theorem meromorphicNFOn_conj_conj {f : ℂ → ℂ} (hf : MeromorphicNFOn f univ) :
    MeromorphicNFOn (conj ∘ f ∘ conj) univ := fun z _ ↦ by
  rw [meromorphicNFAt_iff_analyticAt_or]
  rcases meromorphicNFAt_iff_analyticAt_or.mp (hf (mem_univ (conj z))) with ha | ⟨hm, hord, hz⟩
  · exact Or.inl (analyticAt_conj_conj_iff.mpr ha)
  · exact Or.inr ⟨meromorphicAt_conj_conj_iff.mpr hm,
      by rwa [meromorphicOrderAt_conj_conj], by simp [hz]⟩

private theorem conj_dedekindZeta_conj (z : ℂ) :
    conj (dedekindZeta K (conj z)) = dedekindZeta K z := by
  have hstar : star (fun n ↦ (dedekindZetaCoeff K n : ℂ)) =
      fun n ↦ (dedekindZetaCoeff K n : ℂ) := by
    funext n
    simp
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff, dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  simpa [hstar, Complex.star_def] using
    (TauCeti.LSeries.LSeries_star (fun n ↦ (dedekindZetaCoeff K n : ℂ)) (conj z)).symm

/-- **Reflection symmetry of the completed Dedekind zeta function**:
`Λ_K(conj s) = conj (Λ_K s)` for every `s : ℂ`. -/
theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  have heq : conj ∘ completedDedekindZeta K ∘ conj = completedDedekindZeta K := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1)
      (meromorphicNFOn_conj_conj (meromorphicNFOn_completedDedekindZeta K))
      (meromorphicNFOn_completedDedekindZeta K) fun z hz ↦ ?_
    have hz' : 1 < (conj z).re := by simpa using hz
    have hD := TauCeti.ofReal_cpow_conj (Nat.cast_nonneg (discr K).natAbs) (conj z / 2)
    rw [Complex.ofReal_natCast, map_div₀, map_ofNat, Complex.conj_conj] at hD
    simp only [Function.comp_apply, completedDedekindZeta_eq K hz', completedDedekindZeta_eq K hz,
      map_mul, map_pow, hD, Complex.Gammaℝ_conj, Complex.Gammaℂ_conj, Complex.conj_conj,
      conj_dedekindZeta_conj]
  have h := congrFun heq s
  simpa only [Function.comp_apply, Complex.conj_conj] using congrArg (starRingEnd ℂ) h

/-! ### The continued Dedekind zeta function `dedekindZetaC` -/

/-- The archimedean and discriminant completion factor `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`. -/
private def completionFactor (s : ℂ) : ℂ :=
  ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

/-- The entire reciprocal `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂` of `completionFactor K`. -/
private def invCompletionFactor (s : ℂ) : ℂ :=
  ((discr K).natAbs : ℂ) ^ (-(s / 2)) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ nrComplexPlaces K

private theorem invCompletionFactor_eq_inv (s : ℂ) :
    invCompletionFactor K s = (completionFactor K s)⁻¹ := by
  simp only [invCompletionFactor, completionFactor, mul_inv, inv_pow, Complex.cpow_neg]

private theorem differentiable_invCompletionFactor : Differentiable ℂ (invCompletionFactor K) := by
  have hD : ((discr K).natAbs : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr (discr_ne_zero K))
  have h1 : Differentiable ℂ fun s : ℂ ↦ ((discr K).natAbs : ℂ) ^ (-(s / 2)) :=
    (differentiable_id.div_const 2).neg.const_cpow (.inl hD)
  exact (h1.mul (differentiable_Gammaℝ_inv.pow _)).mul (differentiable_Gammaℂ_inv.pow _)

private theorem completionFactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completionFactor K s ≠ 0 := by
  have hD : ((discr K).natAbs : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr (discr_ne_zero K))
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)))
    (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl hD)

private theorem meromorphic_completionFactor : Meromorphic (completionFactor K) := fun s ↦ by
  have h := ((differentiable_invCompletionFactor K).analyticAt s).meromorphicAt.inv
  have heq : (invCompletionFactor K)⁻¹ = completionFactor K :=
    funext fun z ↦ by simp [invCompletionFactor_eq_inv]
  rwa [heq] at h

private theorem analyticAt_completionFactor_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (completionFactor K) s := by
  have hne : invCompletionFactor K s ≠ 0 := by
    rw [invCompletionFactor_eq_inv]
    exact inv_ne_zero (completionFactor_ne_zero_of_re_pos K hs)
  have h := ((differentiable_invCompletionFactor K).analyticAt s).inv hne
  have heq : (invCompletionFactor K)⁻¹ = completionFactor K :=
    funext fun z ↦ by simp [invCompletionFactor_eq_inv]
  rwa [heq] at h

private theorem invCompletionFactor_mul_completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    invCompletionFactor K s * completedDedekindZeta K s = dedekindZeta K s := by
  rw [invCompletionFactor_eq_inv, completedDedekindZeta_eq K hs]
  exact inv_mul_cancel_left₀ (completionFactor_ne_zero_of_re_pos K (zero_lt_one.trans hs)) _

private theorem meromorphicOrderAt_invCompletionFactor_zero :
    meromorphicOrderAt (invCompletionFactor K) 0 =
      ((nrRealPlaces K + nrComplexPlaces K : ℕ) : ℤ) := by
  have hD : ((discr K).natAbs : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr (discr_ne_zero K))
  let f1 : ℂ → ℂ := fun s ↦ ((discr K).natAbs : ℂ) ^ (-(s / 2))
  have h1a : AnalyticAt ℂ f1 0 :=
    ((differentiable_id.div_const 2).neg.const_cpow (.inl hD)).analyticAt 0
  have h1o : meromorphicOrderAt f1 0 = 0 := by
    rw [h1a.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
    simp [f1]
  have hRa : AnalyticAt ℂ (Gammaℝ⁻¹) 0 := differentiable_Gammaℝ_inv.analyticAt 0
  have hCa : AnalyticAt ℂ (Gammaℂ⁻¹) 0 := differentiable_Gammaℂ_inv.analyticAt 0
  have hRo : meromorphicOrderAt (Gammaℝ⁻¹) 0 = (1 : ℤ) := by
    rw [meromorphicOrderAt_inv, (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff 0).mpr ⟨0, by simp⟩]
    rfl
  have hCo : meromorphicOrderAt (Gammaℂ⁻¹) 0 = (1 : ℤ) := by
    rw [meromorphicOrderAt_inv, (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff 0).mpr ⟨0, by simp⟩]
    rfl
  have hRpow : meromorphicOrderAt (Gammaℝ⁻¹ ^ nrRealPlaces K) 0 = (nrRealPlaces K : ℤ) := by
    rw [meromorphicOrderAt_pow hRa.meromorphicAt, hRo]
    simp
  have hCpow : meromorphicOrderAt (Gammaℂ⁻¹ ^ nrComplexPlaces K) 0 = (nrComplexPlaces K : ℤ) := by
    rw [meromorphicOrderAt_pow hCa.meromorphicAt, hCo]
    simp
  have heq : invCompletionFactor K =
      f1 * Gammaℝ⁻¹ ^ nrRealPlaces K * Gammaℂ⁻¹ ^ nrComplexPlaces K := rfl
  rw [heq, meromorphicOrderAt_mul (h1a.mul (hRa.pow _)).meromorphicAt (hCa.pow _).meromorphicAt,
    meromorphicOrderAt_mul h1a.meromorphicAt (hRa.pow _).meromorphicAt,
    h1o, hRpow, hCpow, zero_add, ← WithTop.coe_add, Nat.cast_add]

/-- **Germ relation between `dedekindZetaC` and `completedDedekindZeta` (uncompleted side).** At
every point of the plane, `dedekindZetaC K` has the punctured germ of the entire reciprocal
completion factor times `completedDedekindZeta K`. -/
theorem dedekindZetaC_eventuallyEq_inv_mul_completedDedekindZeta (z : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] z] fun s ↦
      ((discr K).natAbs : ℂ) ^ (-(s / 2)) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq
    (g := fun s ↦ invCompletionFactor K s * completedDedekindZeta K s)
    (fun s ↦ ((differentiable_invCompletionFactor K).analyticAt s).meromorphicAt.mul
      (meromorphic_completedDedekindZeta K s))
    (fun s hs ↦ ((differentiable_invCompletionFactor K).analyticAt s).mul
      (analyticAt_completedDedekindZeta K (by rintro rfl; norm_num at hs)
        (by rintro rfl; norm_num at hs)))
    (fun _ hs ↦ invCompletionFactor_mul_completedDedekindZeta_eq K hs) z

/-- **Germ relation between `completedDedekindZeta` and `dedekindZetaC` (completed side).** At
every point of the plane, `completedDedekindZeta K` has the punctured germ of
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ dedekindZetaC K s`. -/
theorem completedDedekindZeta_eventuallyEq_mul_dedekindZetaC (z : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] z] fun s ↦
      ((discr K).natAbs : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZetaC K s := by
  rw [completedDedekindZeta_def, dedekindZetaC_def]
  exact meromorphicContinuation_smul_eventuallyEq (meromorphic_completionFactor K)
    (fun _ hs ↦ analyticAt_completionFactor_of_re_pos K (zero_lt_one.trans hs))
    (fun _ hs ↦ completionFactor_ne_zero_of_re_pos K (zero_lt_one.trans hs))
    (analyticOnNhd_dedekindZeta K) z

/-- The continued Dedekind zeta function is meromorphic on the plane. -/
theorem meromorphic_dedekindZetaC : Meromorphic (dedekindZetaC K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_dedekindZetaC K).meromorphicOn

/-- **Order of vanishing at `s = 0`**, Neukirch VII (5.11): `dedekindZetaC K` vanishes at `s = 0`
to exact order `Units.rank K = r₁ + r₂ - 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = (Units.rank K : ℤ) := by
  have hrank : ((nrRealPlaces K + nrComplexPlaces K : ℕ) : ℤ) + (-1 : ℤ) =
      (Units.rank K : ℤ) := by
    have hcard := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have hpos : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos
    rw [Units.rank]
    omega
  rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_inv_mul_completedDedekindZeta K 0)]
  have heq : (fun s ↦ ((discr K).natAbs : ℂ) ^ (-(s / 2)) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s) =
      invCompletionFactor K * completedDedekindZeta K := rfl
  rw [heq,
    meromorphicOrderAt_mul ((differentiable_invCompletionFactor K).analyticAt 0).meromorphicAt
      (meromorphic_completedDedekindZeta K 0),
    meromorphicOrderAt_invCompletionFactor_zero, meromorphicOrderAt_completedDedekindZeta_zero,
    ← WithTop.coe_add, hrank]

/-- **Holomorphy of `dedekindZetaC K` away from `s = 1`**, including at `s = 0` where the simple
pole of `completedDedekindZeta K` is cancelled by the `r₁ + r₂ ≥ 1` gamma poles. -/
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (dedekindZetaC K) s := by
  rw [← (meromorphicNFOn_dedekindZetaC K (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt]
  by_cases h0 : s = 0
  · subst h0
    rw [meromorphicOrderAt_dedekindZetaC_zero]
    exact WithTop.coe_le_coe.mpr (Nat.cast_nonneg _)
  · rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_inv_mul_completedDedekindZeta K s)]
    exact (((differentiable_invCompletionFactor K).analyticAt s).mul
      (analyticAt_completedDedekindZeta K h0 hs)).meromorphicOrderAt_nonneg

/-- On `Re s > 1`, `dedekindZetaC K` agrees with Mathlib's `NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have ht1 : Tendsto (dedekindZetaC K) (𝓝[≠] s) (𝓝 (dedekindZetaC K s)) :=
    (analyticAt_dedekindZetaC K h1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun z ↦ invCompletionFactor K z * completedDedekindZeta K z) (𝓝[≠] s)
      (𝓝 (invCompletionFactor K s * completedDedekindZeta K s)) :=
    (((differentiable_invCompletionFactor K).analyticAt s).mul
      (analyticAt_completedDedekindZeta K h0 h1)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [tendsto_nhds_unique ht1
      (ht2.congr' (dedekindZetaC_eventuallyEq_inv_mul_completedDedekindZeta K s).symm),
    invCompletionFactor_mul_completedDedekindZeta_eq K hs]

/-- On `Re s > 1`, `dedekindZetaC K` agrees with `NumberField.dedekindZeta K` on a neighbourhood
of `s`. -/
theorem dedekindZetaC_eventuallyEq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K =ᶠ[𝓝 s] dedekindZeta K :=
  Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨{z | 1 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
      fun _ hz ↦ dedekindZetaC_eq K hz⟩

/-- **Reflection symmetry of the continued Dedekind zeta function**:
`dedekindZetaC K (conj s) = conj (dedekindZetaC K s)` for every `s : ℂ`. -/
theorem dedekindZetaC_conj (s : ℂ) :
    dedekindZetaC K (conj s) = conj (dedekindZetaC K s) := by
  have heq : conj ∘ dedekindZetaC K ∘ conj = dedekindZetaC K := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1)
      (meromorphicNFOn_conj_conj (meromorphicNFOn_dedekindZetaC K))
      (meromorphicNFOn_dedekindZetaC K) fun z hz ↦ ?_
    have hz' : 1 < (conj z).re := by simpa using hz
    simp only [Function.comp_apply, dedekindZetaC_eq K hz', dedekindZetaC_eq K hz,
      conj_dedekindZeta_conj]
  have h := congrFun heq s
  simpa only [Function.comp_apply, Complex.conj_conj] using congrArg (starRingEnd ℂ) h

/-- **Analytic class number formula for the continued Dedekind zeta function**:
`(s - 1) * dedekindZetaC K s → dedekindZeta_residue K` as `s → 1` in `ℂ \ {1}`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have hinv_t : Tendsto (invCompletionFactor K) (𝓝[≠] 1) (𝓝 (invCompletionFactor K 1)) :=
    ((differentiable_invCompletionFactor K).continuous.tendsto 1).mono_left nhdsWithin_le_nhds
  have hmul := hinv_t.mul (tendsto_sub_one_mul_completedDedekindZeta K)
  have hlim : invCompletionFactor K 1 *
      (2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
        (regulator K : ℂ) / (torsionOrder K : ℂ)) = (dedekindZeta_residue K : ℂ) := by
    rw [← completedDedekindZeta_residue_eq, invCompletionFactor_eq_inv]
    exact inv_mul_cancel_left₀ (completionFactor_ne_zero_of_re_pos K (by norm_num)) _
  rw [hlim] at hmul
  refine hmul.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_inv_mul_completedDedekindZeta K 1] with s hs
  rw [hs]
  simp only [invCompletionFactor]
  ring

/-- The continued Dedekind zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : ℤ) := by
  refine (meromorphic_dedekindZetaC K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)) ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_dedekindZetaC K

/-- **Leading behaviour at `s = 0`**, Neukirch VII (5.11):
`dedekindZetaC K s / s ^ Units.rank K → -(classNumber K * regulator K / torsionOrder K)` as
`s → 0` in `ℂ \ {0}`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ Units.rank K) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ)))) := by
  have hD : ((discr K).natAbs : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr (discr_ne_zero K))
  have hrank : Units.rank K + 1 = nrRealPlaces K + nrComplexPlaces K := by
    rw [Units.rank, ← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      Nat.sub_add_cancel Fintype.card_pos]
  have h1 : Tendsto (fun s : ℂ ↦ ((discr K).natAbs : ℂ) ^ (-(s / 2))) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous fun s : ℂ ↦ ((discr K).natAbs : ℂ) ^ (-(s / 2)) :=
      (continuous_id.div_const 2).neg.const_cpow (.inl hD)
    simpa only [zero_div, neg_zero, Complex.cpow_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℂ ↦ (s * Gammaℝ s)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2⁻¹ : ℂ) ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have h3 : Tendsto (fun s : ℂ ↦ (s * Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2⁻¹ : ℂ) ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod := ((h1.mul h2).mul h3).mul (tendsto_mul_completedDedekindZeta_zero K)
  have hlim : (1 : ℂ) * (2⁻¹ : ℂ) ^ nrRealPlaces K * (2⁻¹ : ℂ) ^ nrComplexPlaces K *
      -(2 ^ (nrRealPlaces K + nrComplexPlaces K) * (classNumber K : ℂ) *
        (regulator K : ℂ) / (torsionOrder K : ℂ)) =
      -((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ)) := by
    rw [one_mul, ← pow_add, inv_pow]
    have h2pow : (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp [h2pow]
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    dedekindZetaC_eventuallyEq_inv_mul_completedDedekindZeta K 0] with s hs hζ
  have hs0 : s ≠ 0 := mem_compl_singleton_iff.mp hs
  rw [hζ]
  simp_rw [mul_inv, mul_pow, inv_pow]
  have hspow : s ^ nrRealPlaces K * s ^ nrComplexPlaces K = s ^ Units.rank K * s := by
    rw [← pow_add, ← hrank, pow_succ]
  have hsR : s ^ nrRealPlaces K ≠ 0 := pow_ne_zero _ hs0
  have hsC : s ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ hs0
  have hsr : s ^ Units.rank K ≠ 0 := pow_ne_zero _ hs0
  field_simp [hs0, hsR, hsC, hsr]
  linear_combination ((discr K).natAbs : ℂ) ^ (-(s / 2)) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s * hspow.symm

/-! ### The analytic L-function card `dedekindZetaData` -/

/-- **The analytic L-function card of the Dedekind zeta function** of a number field `K`:
coefficients `dedekindZetaCoeff K`, conductor `|d_K|`, `r₁` real and `r₂` complex gamma factors
with shift `0`, root number `1`, completed function `completedDedekindZeta K`, and simple poles at
`0` and `1`. -/
def dedekindZetaData : AnalyticLFunctionData where
  coeff n := (dedekindZetaCoeff K n : ℂ)
  conductor := ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩
  gammaR := Multiset.replicate (nrRealPlaces K) 0
  gammaC := Multiset.replicate (nrComplexPlaces K) 0
  rootNumber := 1
  completed := completedDedekindZeta K
  polarOrder := Finsupp.single 0 1 + Finsupp.single 1 1

@[simp]
theorem dedekindZetaData_coeff (n : ℕ) :
    (dedekindZetaData K).coeff n = (dedekindZetaCoeff K n : ℂ) := (rfl)

@[simp]
theorem dedekindZetaData_conductor :
    (dedekindZetaData K).conductor = ⟨(discr K).natAbs, Int.natAbs_pos.mpr (discr_ne_zero K)⟩ :=
  (rfl)

/-- The numeric conductor of the Dedekind zeta card is `|d_K|`. -/
theorem dedekindZetaData_conductor_val :
    ((dedekindZetaData K).conductor : ℕ) = (discr K).natAbs := (rfl)

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

/-- The degree of the Dedekind zeta card is `[K : ℚ]`. -/
@[simp]
theorem dedekindZetaData_degree : (dedekindZetaData K).degree = Module.finrank ℚ K := by
  simp [AnalyticLFunctionData.degree_def, InfinitePlace.card_add_two_mul_card_eq_rank]

/-- The gamma factor of the Dedekind zeta card is `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`. -/
@[simp]
theorem dedekindZetaData_gammaFactor (s : ℂ) :
    (dedekindZetaData K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  simp [AnalyticLFunctionData.gammaFactor_def]

/-- The Dedekind zeta card satisfies average absolute coefficient growth. -/
theorem dedekindZetaData_hasAverageCoefficientGrowth :
    (dedekindZetaData K).HasAverageCoefficientGrowth := by
  rw [AnalyticLFunctionData.hasAverageCoefficientGrowth_iff_abscissaOfAbsConv_le]
  exact (abscissaOfAbsConv_dedekindZetaCoeff K).le

/-- The Dedekind zeta card is its own dual. -/
@[simp]
theorem dedekindZetaData_dual : (dedekindZetaData K).dual = dedekindZetaData K := by
  ext
  · simp
  · exact AnalyticLFunctionData.dual_conductor _
  · simp
  · simp
  · simp
  · simp [completedDedekindZeta_conj]
  · simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
      map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- On `Re s > 1`, the completed function of `dedekindZetaData K` agrees with the completed
Dedekind Dirichlet series. -/
theorem dedekindZetaData_hasDirichletAgreement :
    (dedekindZetaData K).HasDirichletAgreement where
  coeff_one := by
    rw [dedekindZetaData_coeff, ← card_normFiber_eq_dedekindZetaCoeff K one_ne_zero, normFiber_one]
    simp
  degree_pos := by
    rw [dedekindZetaData_degree]
    exact Module.finrank_pos
  completed_eq s hs := by
    have hL : LSeries (dedekindZetaData K).coeff s =
        LSeries (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s := rfl
    rw [dedekindZetaData_completed, dedekindZetaData_conductor_val,
      dedekindZetaData_gammaFactor, completedDedekindZeta_eq K hs,
      dedekindZeta_eq_LSeries_dedekindZetaCoeff, hL]
    ring

/-- The completed Dedekind zeta function is meromorphic, with simple poles at `0` and `1` and no
other poles. -/
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

/-- The completed Dedekind zeta card satisfies the self-dual functional equation with root
number `1`. -/
theorem dedekindZetaData_hasFunctionalEquation :
    (dedekindZetaData K).HasFunctionalEquation where
  norm_rootNumber := by simp
  polarOrder_one_sub_conj s := by
    have hconj (z : ℂ) :
        (dedekindZetaData K).polarOrder (conj z) = (dedekindZetaData K).polarOrder z := by
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

/-- Constructing the Dedekind zeta card canonically from its Dirichlet series recovers
`dedekindZetaData K` exactly, including its root number `1` and its normal-form completion. -/
theorem ofSeries_dedekindZetaData :
    AnalyticLFunctionData.ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC
      (dedekindZetaData K).polarOrder = dedekindZetaData K := by
  refine AnalyticLFunctionData.ofSeries_eq (dedekindZetaData_hasDirichletAgreement K)
    (dedekindZetaData_hasFunctionalEquation K) (meromorphicNFOn_completedDedekindZeta K)
    (by simp) ?_
  rw [dedekindZetaData_completed, completedDedekindZeta_eq K (by norm_num : (1 : ℝ) < (2 : ℂ).re)]
  exact mul_ne_zero (completionFactor_ne_zero_of_re_pos K (by norm_num))
    (dedekindZeta_ne_zero_of_one_lt_re (by norm_num))

end TauCeti.LFunctions
