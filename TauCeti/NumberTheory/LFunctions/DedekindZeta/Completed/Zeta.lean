/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed.Partial
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial

/-!
# The completed Dedekind zeta function and its functional equation

This file defines the completed Dedekind zeta function of a number field `K`,

`Λ_K(s) = |d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`,

as the canonical meromorphic continuation `TauCeti.LFunctions.completedDedekindZeta K` from
`Re s > 1`, identifies it with the sum of the completed partial zeta functions
`TauCeti.LFunctions.completedPartialZeta` over any system of ideal-class representatives of
`ClassGroup (𝓞 K)`, and deduces the analytic continuation, poles, residues, functional equation,
and Schwarz reflection symmetry of both `completedDedekindZeta K` and `dedekindZetaC K`.

For the uncompleted continued Dedekind zeta function `dedekindZetaC K` we divide by the
archimedean factor `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂` via its entire reciprocal
`invArchFactor K`. Because `Γ_ℝ` and `Γ_ℂ` each have a simple pole at `0` with residue `2`,
`dedekindZetaC K` is analytic away from `s = 1`, has a simple pole at `s = 1` with residue
`NumberField.dedekindZeta_residue K` (the analytic class number formula), and vanishes at `s = 0`
to exact order `r = NumberField.Units.rank K = r₁ + r₂ - 1` with leading coefficient
`-h R / w` (`dedekindZetaC_leading_zero`, Neukirch VII, §5, (5.11)).

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the canonical completed Dedekind zeta function
  `Λ_K` in meromorphic normal form on `ℂ`.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_eventuallyEq_sum_completedPartialZeta`:
  `Λ_K` is the sum of `completedPartialZeta (rep c)` over the ideal classes `c : ClassGroup (𝓞 K)`.
* `TauCeti.LFunctions.completedDedekindZeta_eq`: agreement with
  `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)` on `Re s > 1`.
* `TauCeti.LFunctions.analyticAt_completedDedekindZeta`: `Λ_K` is analytic away from `{0, 1}`.
* `TauCeti.LFunctions.completedDedekindZeta_residue_eq`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.tendsto_mul_completedDedekindZeta_zero`:
  exact residues of `Λ_K` at `1` and `0`.
* `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_one`:
  `Λ_K` has simple poles at `0` and `1`.
* `TauCeti.LFunctions.completedDedekindZeta_one_sub`,
  `TauCeti.LFunctions.completedDedekindZeta_one_sub_eventuallyEq`:
  **Hecke's functional equation** `Λ_K(1 - s) = Λ_K(s)` off `{0, 1}` and as punctured germs.
* `TauCeti.LFunctions.completedDedekindZeta_conj`:
  Schwarz reflection symmetry `Λ_K(conj s) = conj (Λ_K s)` on the whole plane.
* `TauCeti.LFunctions.meromorphic_dedekindZetaC`, `TauCeti.LFunctions.dedekindZetaC_eq`,
  `TauCeti.LFunctions.analyticAt_dedekindZetaC`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_one`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_dedekindZetaC`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.dedekindZetaC_leading_zero`,
  `TauCeti.LFunctions.dedekindZetaC_conj`:
  full-plane continuation, poles, analytic class number residue, and leading behavior at `s = 0`
  for `dedekindZetaC K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.9)–(5.11).
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace
  NumberField.Units Set
open scoped nonZeroDivisors Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-! ### Definition and normal form of `completedDedekindZeta` -/

/-- **The completed Dedekind zeta function** of a number field `K`: the canonical meromorphic
continuation from `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)` (Neukirch VII, §5). -/
def completedDedekindZeta : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

/-- The defining equation of `completedDedekindZeta`. -/
theorem completedDedekindZeta_def :
    completedDedekindZeta K = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := (rfl)

/-- `completedDedekindZeta K` is in meromorphic normal form on the whole complex plane. -/
theorem meromorphicNFOn_completedDedekindZeta :
    MeromorphicNFOn (completedDedekindZeta K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedDedekindZeta K` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedDedekindZeta K).meromorphicOn

/-! ### Decomposition as a sum of completed partial zeta functions -/

private def classRep (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (ClassGroup.mk0_surjective c).choose

private theorem classGroup_mk_classRep (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (classRep K c) = c := by
  rw [classRep, ClassGroup.mk_mk0]
  exact (ClassGroup.mk0_surjective c).choose_spec

private theorem sum_completedPartialZeta_eq_on_halfPlane
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) {s : ℂ} (hs : 1 < s.re) :
    ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  classical
  simp_rw [completedPartialZeta_eq_tsum _ hs, ← Finset.mul_sum]
  congr 1
  -- Partition the nonzero integral ideals `(Ideal (𝓞 K))⁰` by the inverse of their ideal class.
  have hζ : dedekindZeta K s =
      ∑' 𝔟 : (Ideal (𝓞 K))⁰, (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    rw [TauCeti.dedekindZeta_eq_LSeries_normCoeff_one,
      TauCeti.LSeries_normCoeff K (TauCeti.summable_idealTerm_one_iff.mpr hs)]
    refine tsum_congr fun 𝔟 ↦ ?_
    simp [TauCeti.idealTerm_def, Complex.cpow_neg]
  have hg : Summable (fun 𝔟 : (Ideal (𝓞 K))⁰ ↦
      (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
    refine (TauCeti.summable_idealTerm_one_iff.mpr hs).congr fun 𝔟 ↦ ?_
    simp [TauCeti.idealTerm_def, Complex.cpow_neg]
  let S (c : ClassGroup (𝓞 K)) : Set (Ideal (𝓞 K))⁰ := {𝔟 | ClassGroup.mk0 𝔟 = c⁻¹}
  have hterm (c : ClassGroup (𝓞 K)) :
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ∃ x : Kˣ,
          ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * (rep c : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      ∑' 𝔟 : (Ideal (𝓞 K))⁰, (S c).indicator
        (fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) 𝔟 := by
    rw [← tsum_subtype (S c) (fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s))]
    refine (Equiv.subtypeEquivRight fun 𝔟 ↦ ?_).tsum_eq
      (f := fun 𝔟 : S c ↦ (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s))
    rw [exists_spanSingleton_iff_classGroup_mk0, hrep c]
    rfl
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum (fun c _ ↦ hg.indicator (S c)), hζ]
  refine tsum_congr fun 𝔟 ↦ ?_
  rw [Finset.sum_eq_single (ClassGroup.mk0 𝔟)⁻¹]
  · simp [S]
  · intro c _ hc
    refine indicator_of_notMem (fun h ↦ hc ?_) _
    have h' : ClassGroup.mk0 𝔟 = c⁻¹ := h
    rw [h', inv_inv]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- For any system of ideal-class representatives `rep`, `completedDedekindZeta K` is the
meromorphic normal form of the sum `∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c)`. -/
theorem completedDedekindZeta_eq_toMeromorphicNFOn_sum
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) :
    completedDedekindZeta K =
      toMeromorphicNFOn (fun s ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s) univ := by
  refine meromorphicContinuation_eq_toMeromorphicNFOn ?_ ?_ fun s hs ↦
    sum_completedPartialZeta_eq_on_halfPlane K rep hrep hs
  · intro z
    exact MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta (rep c) z
  · intro s hs
    have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    exact Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
      analyticAt_completedPartialZeta (rep c) h0 h1

/-- At every point `s : ℂ` (poles included), `completedDedekindZeta K` has the same punctured germ
as the sum of `completedPartialZeta (rep c)` over the ideal classes. -/
theorem completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s]
      fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z := by
  rw [completedDedekindZeta_eq_toMeromorphicNFOn_sum K rep hrep]
  have hm : Meromorphic (fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z) :=
    fun z ↦ MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta (rep c) z
  exact hm.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- On the right half-plane `Re s > 1`, `completedDedekindZeta K` agrees with
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hrep := classGroup_mk_classRep K
  rw [completedDedekindZeta_eq_toMeromorphicNFOn_sum K (classRep K) hrep,
    toMeromorphicNFOn_apply_of_analyticAt
      (fun z ↦ MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta _ z)
      (Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
        analyticAt_completedPartialZeta _ h0 h1)]
  exact sum_completedPartialZeta_eq_on_halfPlane K (classRep K) hrep hs

/-- `completedDedekindZeta K` is analytic away from `0` and `1`. -/
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  have hrep := classGroup_mk_classRep K
  have ha : AnalyticAt ℂ (fun z ↦ ∑ c : ClassGroup (𝓞 K),
      completedPartialZeta (classRep K c) z) s :=
    Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
      analyticAt_completedPartialZeta (classRep K c) h0 h1
  have hm : Meromorphic (fun z ↦ ∑ c : ClassGroup (𝓞 K),
      completedPartialZeta (classRep K c) z) :=
    fun z ↦ MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta _ z
  have hopen : ∀ᶠ z in 𝓝 s, z ≠ 0 ∧ z ≠ 1 :=
    Filter.eventually_and.mpr ⟨eventually_ne_nhds h0, eventually_ne_nhds h1⟩
  refine ha.congr ?_
  filter_upwards [hopen] with z ⟨hz0, hz1⟩
  rw [completedDedekindZeta_eq_toMeromorphicNFOn_sum K (classRep K) hrep,
    toMeromorphicNFOn_apply_of_analyticAt hm
      (Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
        analyticAt_completedPartialZeta _ hz0 hz1)]

/-! ### Residues, simple poles, and exact sum identity -/

/-- The completed residue identity connecting Mathlib's `dedekindZeta_residue K` with
`h_K * (2 * mellinConstant K) = 2^(r₁ + r₂) h_K R_K / w_K`. -/
theorem completedDedekindZeta_residue_eq :
    ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
        Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ) =
      (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) := by
  have hd_abs : (0 : ℝ) < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hsqrt_ne : Real.sqrt |(discr K : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr hd_abs).ne'
  have hw_ne : (torsionOrder K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hcpow : ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt |(discr K : ℝ)| : ℂ) := by
    have hcast : ((|discr K| : ℤ) : ℂ) = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_intCast, Int.cast_abs]
    have hhalf : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, hhalf, ← Complex.ofReal_cpow hd_abs.le, ← Real.sqrt_eq_rpow]
  rw [hcpow, Gammaℝ_one, one_pow, mul_one, Gammaℂ_one]
  norm_cast
  have hreal : Real.sqrt |(discr K : ℝ)| * (1 / Real.pi) ^ nrComplexPlaces K *
      dedekindZeta_residue K = (classNumber K : ℝ) * (2 * mellinConstant K) := by
    rw [dedekindZeta_residue_def, two_mul_mellinConstant K, pow_add]
    have hpow : (1 / Real.pi) ^ nrComplexPlaces K * (2 * Real.pi) ^ nrComplexPlaces K =
        2 ^ nrComplexPlaces K := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc
      Real.sqrt |(discr K : ℝ)| * (1 / Real.pi) ^ nrComplexPlaces K *
          (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
            regulator K * classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|))
        = (2 ^ nrRealPlaces K * ((1 / Real.pi) ^ nrComplexPlaces K *
              (2 * Real.pi) ^ nrComplexPlaces K) * regulator K * classNumber K) /
            torsionOrder K := by
          field_simp [hsqrt_ne, hw_ne]
      _ = (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K * regulator K * classNumber K) /
            torsionOrder K := by rw [hpow]
      _ = (classNumber K : ℝ) *
            (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K * regulator K / torsionOrder K) := by
          ring
  exact_mod_cast hreal

/-- The residue of `completedDedekindZeta K` at `s = 1` is
`|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ · dedekindZeta_residue K = 2^(r₁ + r₂) h R / w`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) *
        Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K *
        (dedekindZeta_residue K : ℂ))) := by
  rw [completedDedekindZeta_residue_eq K]
  have hsum : Tendsto (fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K),
        (s - 1) * completedPartialZeta (classRep K c) s)
      (𝓝[≠] 1) (𝓝 (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ)))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦
      tendsto_sub_one_mul_completedPartialZeta (classRep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), (2 * (mellinConstant K : ℂ))) =
      (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta K
    (classRep K) (classGroup_mk_classRep K) 1] with z hz
  rw [hz, Finset.mul_sum]

/-- The residue of `completedDedekindZeta K` at `s = 0` is
`-(|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ · dedekindZeta_residue K) = -2^(r₁ + r₂) h R / w`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) *
        Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K *
        (dedekindZeta_residue K : ℂ)))) := by
  rw [completedDedekindZeta_residue_eq K]
  have hsum : Tendsto (fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K),
        s * completedPartialZeta (classRep K c) s)
      (𝓝[≠] 0) (𝓝 (∑ _c : ClassGroup (𝓞 K), (-(2 * (mellinConstant K : ℂ))))) :=
    tendsto_finsetSum Finset.univ fun c _ ↦
      tendsto_mul_completedPartialZeta_zero (classRep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), (-(2 * (mellinConstant K : ℂ)))) =
      -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber, mul_neg]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta K
    (classRep K) (classGroup_mk_classRep K) 0] with z hz
  rw [hz, Finset.mul_sum]

private theorem completedDedekindZeta_residue_ne_zero :
    ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
      Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ) ≠ 0 := by
  rw [completedDedekindZeta_residue_eq K]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (classNumber_ne_zero K))
    (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))

/-- `completedDedekindZeta K` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : WithTop ℤ) := by
  have hlim : Tendsto (fun z : ℂ ↦ (z - 0) • completedDedekindZeta K z) (𝓝[≠] 0)
      (𝓝 (-(((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
        Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ)))) := by
    simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K
  exact (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (neg_ne_zero.mpr (completedDedekindZeta_residue_ne_zero K)) hlim

/-- `completedDedekindZeta K` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : WithTop ℤ) := by
  have hlim : Tendsto (fun z : ℂ ↦ (z - 1) • completedDedekindZeta K z) (𝓝[≠] 1)
      (𝓝 (((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
        Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ))) := by
    simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedDedekindZeta K
  exact (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (completedDedekindZeta_residue_ne_zero K) hlim

/-- For any system of ideal-class representatives `rep`, `completedDedekindZeta K s` equals the sum
of `completedPartialZeta (rep c) s` over `c : ClassGroup (𝓞 K)` at every `s : ℂ` (both sides are
in meromorphic normal form and hence agree even at the poles `0` and `1`, where both vanish). -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (s : ℂ) :
    completedDedekindZeta K s =
      ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s := by
  have vanish {f : ℂ → ℂ} {z : ℂ} (hnf : MeromorphicNFOn f univ)
      (hord : meromorphicOrderAt f z = (-1 : WithTop ℤ)) : f z = 0 := by
    have hne : meromorphicOrderAt f z ≠ 0 := by
      rw [hord]
      decide
    exact not_not.mp ((hnf (mem_univ z)).meromorphicOrderAt_eq_zero_iff.not.mp hne)
  by_cases h0 : s = 0
  · subst h0
    have hL : completedDedekindZeta K 0 = 0 :=
      vanish (meromorphicNFOn_completedDedekindZeta K)
        (meromorphicOrderAt_completedDedekindZeta_zero K)
    have hR : ∀ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) 0 = 0 := fun c ↦
      vanish (meromorphicNFOn_completedPartialZeta (rep c))
        (meromorphicOrderAt_completedPartialZeta_zero (rep c))
    simp [hL, hR]
  by_cases h1 : s = 1
  · subst h1
    have hL : completedDedekindZeta K 1 = 0 :=
      vanish (meromorphicNFOn_completedDedekindZeta K)
        (meromorphicOrderAt_completedDedekindZeta_one K)
    have hR : ∀ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) 1 = 0 := fun c ↦
      vanish (meromorphicNFOn_completedPartialZeta (rep c))
        (meromorphicOrderAt_completedPartialZeta_one (rep c))
    simp [hL, hR]
  · rw [completedDedekindZeta_eq_toMeromorphicNFOn_sum K rep hrep]
    exact toMeromorphicNFOn_apply_of_analyticAt
      (fun z ↦ MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta (rep c) z)
      (Finset.analyticAt_fun_sum Finset.univ fun c _ ↦
        analyticAt_completedPartialZeta (rep c) h0 h1)

/-! ### Functional equation and Schwarz reflection symmetry -/

/-- **Hecke's functional equation for the completed Dedekind zeta function** (Neukirch VII, §5,
(5.9)): `completedDedekindZeta K (1 - s) = completedDedekindZeta K s` away from `{0, 1}`. -/
theorem completedDedekindZeta_one_sub {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  have hrep := classGroup_mk_classRep K
  rw [completedDedekindZeta_eq_sum_completedPartialZeta K (classRep K) hrep (1 - s),
    completedDedekindZeta_eq_sum_completedPartialZeta K (classRep K) hrep s]
  let d : ClassGroup (𝓞 K) := ClassGroup.mk K (dualUnit (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    { toFun := fun c ↦ d * c⁻¹
      invFun := fun c ↦ d * c⁻¹
      left_inv := fun c ↦ by simp [mul_comm, mul_inv_rev]
      right_inv := fun c ↦ by simp [mul_comm, mul_inv_rev] }
  calc
    ∑ c : ClassGroup (𝓞 K), completedPartialZeta (classRep K c) (1 - s)
      = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (dualUnit (classRep K c)) s := by
        refine Finset.sum_congr rfl fun c _ ↦ completedPartialZeta_one_sub (classRep K c) h0 h1
    _ = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (classRep K (e c)) s := by
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        have hcls : ClassGroup.mk K (dualUnit (classRep K c)) =
            ClassGroup.mk K (classRep K (e c)) := by
          rw [classGroup_mk_dualUnit, hrep c, hrep (e c)]
          rfl
        exact congrFun (completedPartialZeta_eq_of_classGroup_eq hcls) s
    _ = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (classRep K c) s :=
        Equiv.sum_comp e fun c ↦ completedPartialZeta (classRep K c) s

/-- Hecke's functional equation for `completedDedekindZeta K` as an equality of punctured germs at
every point of the complex plane, the poles included. -/
theorem completedDedekindZeta_one_sub_eventuallyEq (s : ℂ) :
    (fun z ↦ completedDedekindZeta K (1 - z)) =ᶠ[𝓝[≠] s] completedDedekindZeta K := by
  have hne (a : ℂ) : ∀ᶠ z in 𝓝[≠] s, z ≠ a := by
    rcases eq_or_ne s a with rfl | h
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h)
  filter_upwards [hne 0, hne 1] with z hz0 hz1
  exact completedDedekindZeta_one_sub K hz0 hz1

/-- **Schwarz reflection symmetry**:
`completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s)` for every `s : ℂ`
(including at poles, where both sides vanish in meromorphic normal form). -/
theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  have hrep := classGroup_mk_classRep K
  rw [completedDedekindZeta_eq_sum_completedPartialZeta K (classRep K) hrep (conj s),
    completedDedekindZeta_eq_sum_completedPartialZeta K (classRep K) hrep s, map_sum]
  exact Finset.sum_congr rfl fun c _ ↦ completedPartialZeta_conj (classRep K c) s

/-! ### Continuation, poles, residue, and zero-value behavior of `dedekindZetaC` -/

/-- The entire reciprocal of the archimedean factor `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂`. -/
private abbrev invArchFactor (s : ℂ) : ℂ :=
  ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ nrComplexPlaces K

private theorem differentiable_invArchFactor : Differentiable ℂ (invArchFactor K) := by
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  have h1 : Differentiable ℂ (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) :=
    ((differentiable_id.neg).div_const 2).const_cpow (Or.inl hd)
  exact (h1.mul (differentiable_Gammaℝ_inv.pow (nrRealPlaces K))).mul
    (differentiable_Gammaℂ_inv.pow (nrComplexPlaces K))

private theorem invArchFactor_mul_arch_mul {s : ℂ} (hs : 0 < s.re) (c : ℂ) :
    invArchFactor K s *
      (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * c) = c := by
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hΓℂ : Gammaℂ s ≠ 0 := Complex.Gammaℂ_ne_zero_of_re_pos hs
  have hd_mul : ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2) = 1 := by
    rw [← cpow_add _ _ hd]
    have : -s / 2 + s / 2 = 0 := by ring
    rw [this, cpow_zero]
  calc
    invArchFactor K s *
        (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K * c)
      = (((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((Gammaℝ s)⁻¹ * Gammaℝ s) ^ nrRealPlaces K *
          ((Gammaℂ s)⁻¹ * Gammaℂ s) ^ nrComplexPlaces K * c := by
        simp only [mul_pow]
        ring
    _ = c := by
        rw [hd_mul, inv_mul_cancel₀ hΓℝ, inv_mul_cancel₀ hΓℂ, one_pow, one_pow,
          one_mul, one_mul, one_mul]

private theorem invArchFactor_mul_completed_eq_on_halfPlane {s : ℂ} (hs : 1 < s.re) :
    invArchFactor K s * completedDedekindZeta K s = dedekindZeta K s := by
  rw [completedDedekindZeta_eq K hs]
  exact invArchFactor_mul_arch_mul K (by linarith) (dedekindZeta K s)

/-- `dedekindZetaC K` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_dedekindZetaC : Meromorphic (dedekindZetaC K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_dedekindZetaC K).meromorphicOn

/-- `dedekindZetaC K` is the meromorphic normal form of
`invArchFactor K * completedDedekindZeta K`. -/
theorem dedekindZetaC_eq_toMeromorphicNFOn :
    dedekindZetaC K = toMeromorphicNFOn
      (fun s ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s) univ := by
  rw [dedekindZetaC_def]
  refine meromorphicContinuation_eq_toMeromorphicNFOn ?_ ?_ fun s hs ↦
    invArchFactor_mul_completed_eq_on_halfPlane K hs
  · intro z
    exact ((differentiable_invArchFactor K).analyticAt z).meromorphicAt.mul
      (meromorphic_completedDedekindZeta K z)
  · intro s hs
    have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    exact ((differentiable_invArchFactor K).analyticAt s).mul
      (analyticAt_completedDedekindZeta K h0 h1)

/-- Punctured germ relation between `dedekindZetaC K` and `completedDedekindZeta K` at every point
of the complex plane. -/
theorem dedekindZetaC_eventuallyEq_invArch_mul_completed (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s]
      fun z ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z := by
  rw [dedekindZetaC_eq_toMeromorphicNFOn K]
  have hm : Meromorphic (fun z ↦ invArchFactor K z * completedDedekindZeta K z) := fun z ↦
    ((differentiable_invArchFactor K).analyticAt z).meromorphicAt.mul
      (meromorphic_completedDedekindZeta K z)
  exact hm.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- On `Re s > 1`, `dedekindZetaC K` agrees with Mathlib's `NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hm : Meromorphic (fun z ↦ invArchFactor K z * completedDedekindZeta K z) := fun z ↦
    ((differentiable_invArchFactor K).analyticAt z).meromorphicAt.mul
      (meromorphic_completedDedekindZeta K z)
  have ha : AnalyticAt ℂ (fun z ↦ invArchFactor K z * completedDedekindZeta K z) s :=
    ((differentiable_invArchFactor K).analyticAt s).mul
      (analyticAt_completedDedekindZeta K h0 h1)
  rw [dedekindZetaC_eq_toMeromorphicNFOn K]
  exact (toMeromorphicNFOn_apply_of_analyticAt hm ha).trans
    (invArchFactor_mul_completed_eq_on_halfPlane K hs)

/-- Punctured germ relation expressing `completedDedekindZeta K` as the archimedean factor times
`dedekindZetaC K` at every point `s : ℂ`. -/
theorem completedDedekindZeta_eventuallyEq_mul_dedekindZetaC (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s]
      fun z ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
        Gammaℂ z ^ nrComplexPlaces K * dedekindZetaC K z := by
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  have hm : Meromorphic (fun z ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
      Gammaℂ z ^ nrComplexPlaces K * dedekindZetaC K z) := by
    intro z
    have h1 : MeromorphicAt (fun w : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (w / 2)) z :=
      ((((differentiable_id.div_const 2).const_cpow (Or.inl hd)).analyticAt z)).meromorphicAt
    exact ((h1.mul ((TauCeti.meromorphic_Gammaℝ z).pow _)).mul
      ((TauCeti.meromorphic_Gammaℂ z).pow _)).mul (meromorphic_dedekindZetaC K z)
  exact eventuallyEq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_completedDedekindZeta K) hm
    (fun z hz ↦ by dsimp only; rw [completedDedekindZeta_eq K hz, dedekindZetaC_eq K hz]) s

/-- At `s = 0`, `dedekindZetaC K` has a zero of exact order `NumberField.Units.rank K`
(`= r₁ + r₂ - 1`). -/
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = ((Units.rank K : ℤ) : WithTop ℤ) := by
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_invArch_mul_completed K 0)]
  have h1a : AnalyticAt ℂ (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) 0 :=
    (((differentiable_id.neg).div_const 2).const_cpow (Or.inl hd)).analyticAt 0
  have h1ne : ((|discr K| : ℤ) : ℂ) ^ (-(0 : ℂ) / 2) ≠ 0 := by simp
  have h1o : meromorphicOrderAt (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) 0 = 0 := by
    rw [h1a.meromorphicOrderAt_eq, h1a.analyticOrderAt_eq_zero.mpr h1ne]
    simp
  have h2m : MeromorphicAt (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 :=
    ((differentiable_Gammaℝ_inv.pow (nrRealPlaces K)).analyticAt 0).meromorphicAt
  have h3m : MeromorphicAt (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 :=
    ((differentiable_Gammaℂ_inv.pow (nrComplexPlaces K)).analyticAt 0).meromorphicAt
  have h2o : meromorphicOrderAt (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 =
      (nrRealPlaces K : WithTop ℤ) := by
    have hΓ : meromorphicOrderAt (Gammaℝ⁻¹) 0 = (1 : WithTop ℤ) := by
      have h0 : meromorphicOrderAt Gammaℝ 0 = (-1 : WithTop ℤ) := by
        simpa using (meromorphicOrderAt_Gammaℝ (0 : ℂ)).trans
          (by simpa using meromorphicOrderAt_Gamma_neg_nat 0)
      rw [meromorphicOrderAt_inv, h0]
      rfl
    have hpow := meromorphicOrderAt_pow (TauCeti.meromorphic_Gammaℝ 0).inv (n := nrRealPlaces K)
    rw [hΓ, mul_one] at hpow
    exact hpow
  have h3o : meromorphicOrderAt (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 =
      (nrComplexPlaces K : WithTop ℤ) := by
    have hΓ : meromorphicOrderAt (Gammaℂ⁻¹) 0 = (1 : WithTop ℤ) := by
      have h0 : meromorphicOrderAt Gammaℂ 0 = (-1 : WithTop ℤ) := by
        simpa using (meromorphicOrderAt_Gammaℂ (0 : ℂ)).trans
          (by simpa using meromorphicOrderAt_Gamma_neg_nat 0)
      rw [meromorphicOrderAt_inv, h0]
      rfl
    have hpow := meromorphicOrderAt_pow (TauCeti.meromorphic_Gammaℂ 0).inv
      (n := nrComplexPlaces K)
    rw [hΓ, mul_one] at hpow
    exact hpow
  have hmul1 := meromorphicOrderAt_mul
    (f := fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
      (Gammaℂ z)⁻¹ ^ nrComplexPlaces K)
    (g := completedDedekindZeta K)
    ((h1a.meromorphicAt.mul h2m).mul h3m) (meromorphic_completedDedekindZeta K 0)
  have hmul2 := meromorphicOrderAt_mul
    (f := fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K)
    (g := fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K)
    (h1a.meromorphicAt.mul h2m) h3m
  have hmul3 := meromorphicOrderAt_mul
    (f := fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2))
    (g := fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K)
    h1a.meromorphicAt h2m
  have hord : meromorphicOrderAt (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z) 0 =
      (nrRealPlaces K : WithTop ℤ) + (nrComplexPlaces K : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) := by
    calc
      meromorphicOrderAt (fun z : ℂ ↦
          ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
            (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z) 0
        = meromorphicOrderAt (fun z : ℂ ↦
            ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
              (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 +
            meromorphicOrderAt (completedDedekindZeta K) 0 := hmul1
      _ = meromorphicOrderAt (fun z : ℂ ↦
            ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 +
            meromorphicOrderAt (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 +
            meromorphicOrderAt (completedDedekindZeta K) 0 :=
          congrArg (· + meromorphicOrderAt (completedDedekindZeta K) 0) hmul2
      _ = meromorphicOrderAt (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) 0 +
            meromorphicOrderAt (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 +
            meromorphicOrderAt (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 +
            meromorphicOrderAt (completedDedekindZeta K) 0 :=
          congrArg (fun x ↦ x + meromorphicOrderAt (fun z : ℂ ↦
            (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 +
            meromorphicOrderAt (completedDedekindZeta K) 0) hmul3
      _ = (nrRealPlaces K : WithTop ℤ) + (nrComplexPlaces K : WithTop ℤ) +
            ((-1 : ℤ) : WithTop ℤ) := by
        rw [h1o, h2o, h3o, meromorphicOrderAt_completedDedekindZeta_zero K, zero_add]
        rfl
  rw [hord]
  have hpos : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hrank : Units.rank K = nrRealPlaces K + nrComplexPlaces K - 1 := by
    rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces]
  have hint : ((nrRealPlaces K : ℤ) + (nrComplexPlaces K : ℤ) + (-1 : ℤ)) =
      ((Units.rank K : ℤ)) := by
    omega
  rw [← WithTop.coe_natCast (nrRealPlaces K), ← WithTop.coe_natCast (nrComplexPlaces K),
    ← WithTop.coe_add, ← WithTop.coe_add, hint]

/-- `dedekindZetaC K` is analytic away from `s = 1` (including at `s = 0`). -/
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (dedekindZetaC K) s := by
  by_cases h0 : s = 0
  · subst h0
    refine ((meromorphicNFOn_dedekindZetaC K (mem_univ 0))
      |>.meromorphicOrderAt_nonneg_iff_analyticAt).mp ?_
    rw [meromorphicOrderAt_dedekindZetaC_zero K]
    exact WithTop.coe_le_coe.mpr (Nat.cast_nonneg _)
  · have hm : Meromorphic (fun z ↦ invArchFactor K z * completedDedekindZeta K z) := fun z ↦
      ((differentiable_invArchFactor K).analyticAt z).meromorphicAt.mul
        (meromorphic_completedDedekindZeta K z)
    have ha : AnalyticAt ℂ (fun z ↦ invArchFactor K z * completedDedekindZeta K z) s :=
      ((differentiable_invArchFactor K).analyticAt s).mul
        (analyticAt_completedDedekindZeta K h0 hs)
    have hopen : ∀ᶠ z in 𝓝 s, z ≠ 0 ∧ z ≠ 1 :=
      Filter.eventually_and.mpr ⟨eventually_ne_nhds h0, eventually_ne_nhds hs⟩
    refine ha.congr ?_
    filter_upwards [hopen] with z ⟨hz0, hz1⟩
    rw [dedekindZetaC_eq_toMeromorphicNFOn K]
    exact (toMeromorphicNFOn_apply_of_analyticAt hm
      (((differentiable_invArchFactor K).analyticAt z).mul
        (analyticAt_completedDedekindZeta K hz0 hz1))).symm

/-- **Analytic class number formula for the continued Dedekind zeta function**:
`(s - 1) * dedekindZetaC K s → dedekindZeta_residue K` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have hinv : Tendsto (invArchFactor K) (𝓝[≠] 1) (𝓝 (invArchFactor K 1)) :=
    ((differentiable_invArchFactor K).continuous.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  have hmul := hinv.mul (tendsto_sub_one_mul_completedDedekindZeta K)
  rw [invArchFactor_mul_arch_mul K (by norm_num : (0 : ℝ) < (1 : ℂ).re)
    (dedekindZeta_residue K : ℂ)] at hmul
  refine hmul.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_invArch_mul_completed K 1] with z hz
  rw [hz]
  ring

/-- `dedekindZetaC K` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : WithTop ℤ) := by
  have hlim : Tendsto (fun z : ℂ ↦ (z - 1) • dedekindZetaC K z) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
    simpa only [smul_eq_mul] using tendsto_sub_one_mul_dedekindZetaC K
  exact (meromorphic_dedekindZetaC K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)) hlim

/-- **Leading behavior of `dedekindZetaC K` at `s = 0`** (Neukirch VII, §5, (5.11)):
`ζ_K` vanishes at `s = 0` to exact order `r = NumberField.Units.rank K = r₁ + r₂ - 1`, and
`ζ_K(s) / s^r → -h R / w` as `s → 0`, `s ≠ 0`. -/
theorem dedekindZetaC_leading_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = ((Units.rank K : ℤ) : WithTop ℤ) ∧
      Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ Units.rank K) (𝓝[≠] 0)
        (𝓝 (-((classNumber K : ℝ) * regulator K / (torsionOrder K : ℝ)) : ℂ)) := by
  refine ⟨meromorphicOrderAt_dedekindZetaC_zero K, ?_⟩
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  have hpos : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hrank : Units.rank K + 1 = nrRealPlaces K + nrComplexPlaces K := by
    rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hdisc : Tendsto (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) 0 :=
      (((differentiable_id.neg).div_const 2).const_cpow (Or.inl hd)).continuous.continuousAt
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun z : ℂ ↦
        ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (z * completedDedekindZeta K z))
      (𝓝[≠] 0) (𝓝 (-((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))))) := by
    have hΛ := tendsto_mul_completedDedekindZeta_zero K
    rw [completedDedekindZeta_residue_eq K] at hΛ
    simpa using hdisc.mul hΛ
  have hden : Tendsto (fun z : ℂ ↦
        (z * Gammaℝ z) ^ nrRealPlaces K * (z * Gammaℂ z) ^ nrComplexPlaces K)
      (𝓝[≠] 0) (𝓝 ((2 : ℂ) ^ nrRealPlaces K * (2 : ℂ) ^ nrComplexPlaces K)) :=
    (Gammaℝ_residue_zero.pow (nrRealPlaces K)).mul (Gammaℂ_residue_zero.pow (nrComplexPlaces K))
  have hden_ne : (2 : ℂ) ^ nrRealPlaces K * (2 : ℂ) ^ nrComplexPlaces K ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)
  have hdiv := hnum.div hden hden_ne
  have hlim : -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) /
      ((2 : ℂ) ^ nrRealPlaces K * (2 : ℂ) ^ nrComplexPlaces K) =
      (-((classNumber K : ℝ) * regulator K / (torsionOrder K : ℝ)) : ℂ) := by
    have h2m : (2 : ℂ) * (mellinConstant K : ℂ) =
        (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) * (regulator K : ℂ) /
          (torsionOrder K : ℂ) := by
      exact_mod_cast two_mul_mellinConstant K
    rw [h2m, ← pow_add]
    have h2p : (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) ≠ 0 :=
      pow_ne_zero _ two_ne_zero
    have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
    push_cast
    field_simp [h2p, hw]
  rw [hlim] at hdiv
  have hΓℝ_ne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * Gammaℝ z ≠ 0 :=
    Gammaℝ_residue_zero.eventually_ne (by norm_num)
  have hΓℂ_ne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * Gammaℂ z ≠ 0 :=
    Gammaℂ_residue_zero.eventually_ne (by norm_num)
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hΓℝ_ne, hΓℂ_ne,
    dedekindZetaC_eventuallyEq_invArch_mul_completed K 0] with z hz0 hR hC heq
  have hz : z ≠ 0 := hz0
  have hR' : Gammaℝ z ≠ 0 := right_ne_zero_of_mul hR
  have hC' : Gammaℂ z ≠ 0 := right_ne_zero_of_mul hC
  rw [heq]
  have hpow : z ^ nrRealPlaces K * z ^ nrComplexPlaces K = z ^ Units.rank K * z := by
    rw [← pow_add, ← hrank, pow_succ]
  calc
    ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (z * completedDedekindZeta K z) /
        ((z * Gammaℝ z) ^ nrRealPlaces K * (z * Gammaℂ z) ^ nrComplexPlaces K)
      = ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (z * completedDedekindZeta K z) /
          ((z ^ nrRealPlaces K * z ^ nrComplexPlaces K) *
            Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K) := by
        simp only [mul_pow]
        ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (z * completedDedekindZeta K z) /
          ((z ^ Units.rank K * z) *
            Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K) := by
        rw [hpow]
    _ = ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z /
          z ^ Units.rank K := by
        rw [inv_pow, inv_pow]
        field_simp [hz, hR', hC']

/-- **Schwarz reflection symmetry**: `dedekindZetaC K (conj s) = conj (dedekindZetaC K s)` for
every `s : ℂ` (including at the pole `s = 1`, where both sides vanish in normal form). -/
theorem dedekindZetaC_conj (s : ℂ) :
    dedekindZetaC K (conj s) = conj (dedekindZetaC K s) := by
  have hnf : MeromorphicNFOn (conj ∘ dedekindZetaC K ∘ conj) univ := by
    simpa only [preimage_univ] using (meromorphicNFOn_dedekindZetaC K).conj_conj
  have heq : conj ∘ dedekindZetaC K ∘ conj = dedekindZetaC K := by
    refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (σ := 1) hnf
      (meromorphicNFOn_dedekindZetaC K) fun z hz ↦ ?_
    have hz' : 1 < z.re := hz
    have hzc : 1 < (conj z).re := by simpa using hz'
    have hpos : 0 < z.re := by linarith
    have hd_nn : (0 : ℝ) ≤ (|discr K| : ℤ) := by positivity
    have hΓℝ : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
    have hΓℂ : Gammaℂ z ≠ 0 := Complex.Gammaℂ_ne_zero_of_re_pos hpos
    have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
    have hdiscr : conj (((|discr K| : ℤ) : ℂ) ^ (conj z / 2)) =
        ((|discr K| : ℤ) : ℂ) ^ (z / 2) := by
      have h1 : conj z / 2 = conj (z / 2) := by rw [map_div₀, map_ofNat]
      rw [h1, ← Complex.ofReal_intCast, TauCeti.ofReal_cpow_conj hd_nn, conj_conj]
    have hfac_ne : ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
        Gammaℂ z ^ nrComplexPlaces K ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hΓℝ)) (pow_ne_zero _ hΓℂ)
      rw [Ne, cpow_eq_zero_iff]
      exact fun h ↦ hd h.1
    have hΛ := congrArg conj (completedDedekindZeta_conj K z)
    rw [conj_conj] at hΛ
    rw [completedDedekindZeta_eq K hzc, completedDedekindZeta_eq K hz'] at hΛ
    simp only [map_mul, map_pow, hdiscr, Gammaℝ_conj, Gammaℂ_conj, conj_conj] at hΛ
    have hζ : conj (dedekindZeta K (conj z)) = dedekindZeta K z :=
      mul_left_cancel₀ hfac_ne hΛ
    simp only [Function.comp_apply, dedekindZetaC_eq K hzc, dedekindZetaC_eq K hz', hζ]
  have hval := congrFun heq (conj s)
  simpa only [Function.comp_apply, conj_conj] using hval.symm

end TauCeti.LFunctions
