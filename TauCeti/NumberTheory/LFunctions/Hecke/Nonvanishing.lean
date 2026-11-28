/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.LFunctions.UnitaryCancelling
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Complex.HalfPlaneIdentity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.NumberTheory.LFunctions.Hecke.EulerCorrection
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Boundary nonvanishing for ray class character L-functions

Over an arbitrary number field `K` and modulus `𝔪 : Modulus K`, the unitary ideal weights
`χ ↦ χ.toUnitaryIdealWeight` of ray class characters satisfy
`TauCeti.LFunctions.IsUnitaryCharacterFamily`: the trivial character's weight is the indicator of
ideals prime to `𝔪` (hence trivial on its good ideals), multiplication of characters corresponds to
pointwise multiplication of weights, and every imaginary norm twist of every nontrivial character
has partial-sum cancellation (`RayClassCharacter.hasCancellation_normTwist_toUnitaryIdealWeight`).

Consequently every nontrivial ray class character satisfies `TauCeti.LFunctions.UnitaryCancelling`,
its continued L-function `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` is nonzero on
`Re s ≥ 1` away from `s = 1` in the quadratic case `χ ^ 2 = 1`, and for `[K : ℚ] = 1`,
`RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re` closes the
remaining point `χ ^ 2 = 1 ∧ s = 1` via Landau's theorem
(`TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one`).

For an arbitrary number field `K` and any continuation `L : ℂ → ℂ` agreeing with the `L`-series
of `χ` on `Re z > 1`, `RayClassCharacter.ne_zero_of_one_le_re` and
`RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re` give pointwise nonvanishing and
meromorphic-order-zero criteria on `Re s ≥ 1`: on `Re s > 1` only series agreement is needed; on
`Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`, `3-4-1` / punctured germ comparison with
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` (or `dedekindZetaC K` times the trivial-modulus
Euler correction when `χ = 1`) requires only local differentiability (`MeromorphicAt` for order
zero); and only at `χ ^ 2 = 1 ∧ s = 1` do they ask for a holomorphic continuation `Z` of `ζ_K` on
`{z | 1 / 2 < z.re} \ {1}`, holomorphy of `L` on `{z | 1 / 2 < z.re}`, and the sharp boundary
condition that `(Z σ * L σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.

## Main results

* `RayClassCharacter.isUnitaryCharacterFamily_toUnitaryIdealWeight`:
  `toUnitaryIdealWeight` on `RayClassCharacter 𝔪` forms a unitary character family.
* `RayClassCharacter.unitaryCancelling_toUnitaryIdealWeight_iff`:
  `UnitaryCancelling χ.toUnitaryIdealWeight ↔ χ ≠ 1`.
* `RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero`:
  for `χ ≠ 1` and `1 ≤ s.re`, `continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0` whenever
  `χ ^ 2 ≠ 1` or `s ≠ 1`.
* `RayClassCharacter.exists_analyticAt_ne_zero_eventuallyEq_nhdsNE_of_eqOn_LSeries`:
  shared punctured-germ comparison on `Re s = 1 \ {(1, χ ^ 2 = 1)}` against an analytic
  nonvanishing local model.
* `RayClassCharacter.ne_zero_of_one_le_re` and
  `RayClassCharacter.meromorphicOrderAt_eq_zero_of_one_le_re`: nonvanishing and
  meromorphic-order-zero criteria on `Re s ≥ 1` for an arbitrary continuation `L`.
* `RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re`:
  nonvanishing on `Re s ≥ 1` for `χ ≠ 1`, requiring `[K : ℚ] = 1` only when `χ ^ 2 = 1 ∧ s = 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

open Filter NumberField Set TauCeti TauCeti.LFunctions
open scoped NumberField Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Any imaginary norm twist of `χ.toUnitaryIdealWeight` has cancellation if and only if `χ ≠ 1`. -/
@[simp]
theorem hasCancellation_imaginaryNormTwist_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪}
    (t : ℝ) :
    HasCancellation (imaginaryNormTwist χ.toUnitaryIdealWeight t) ↔ χ ≠ 1 := by
  simp [imaginaryNormTwist_def]

/-- **Ray class characters of any modulus `𝔪` form a unitary character family.** -/
theorem isUnitaryCharacterFamily_toUnitaryIdealWeight (𝔪 : Modulus K) :
    IsUnitaryCharacterFamily (toUnitaryIdealWeight (𝔪 := 𝔪)) :=
  IsUnitaryCharacterFamily.of_mul
    (by
      rw [val_toUnitaryIdealWeight, toMultiplicativeIdealWeight_one]
      exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes 𝔪.support.finite_toSet)
    toUnitaryIdealWeight_mul
    (fun hχ t ↦ (hasCancellation_imaginaryNormTwist_toUnitaryIdealWeight_iff t).mpr hχ)

/-- Every nontrivial ray class character's unitary weight satisfies `UnitaryCancelling`. -/
theorem unitaryCancelling_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) :
    UnitaryCancelling χ.toUnitaryIdealWeight :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).unitaryCancelling hχ

/-- The unitary weight of the trivial ray class character never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_toUnitaryIdealWeight_one :
    ¬ UnitaryCancelling (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).not_unitaryCancelling_one

/-- A ray class character's unitary weight satisfies `UnitaryCancelling` if and only if `χ ≠ 1`. -/
@[simp]
theorem unitaryCancelling_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪} :
    UnitaryCancelling χ.toUnitaryIdealWeight ↔ χ ≠ 1 :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).unitaryCancelling_iff

/-- **Boundary nonvanishing for the continued L-function of a nontrivial ray class character** on
`Re s ≥ 1`, away from `s = 1` in the quadratic case `χ ^ 2 = 1`. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) (hquad : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).continuedLFunctionOfWeight_ne_zero hχ hs hquad

private theorem eventuallyEq_nhdsNE_of_meromorphicAt_of_analyticAt
    {L F : ℂ → ℂ} {s : ℂ} (hs : s.re = 1) (hLF : EqOn L F {z | 1 < z.re})
    (hLM : MeromorphicAt L s) (hF : AnalyticAt ℂ F s) :
    L =ᶠ[𝓝[≠] s] F :=
  TauCeti.eventuallyEq_of_differentiableAt_nhdsNE_of_eventuallyEq_re_gt
    (hLM.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (hF.meromorphicAt.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (eventually_nhdsWithin_of_forall fun _ hz ↦ hLF (hs ▸ hz))

/-- **Shared punctured-germ comparison on `Re s = 1` away from `χ ^ 2 = 1 ∧ s = 1`.** Any
`L : ℂ → ℂ` that is meromorphic at `s` and agrees with the `L`-series of `χ` on `Re z > 1` shares
its punctured germ at `s` with an analytic nonvanishing function:
* `dedekindZetaC K * (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪` when `χ = 1`,
* `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` when `χ ≠ 1`. -/
theorem exists_analyticAt_ne_zero_eventuallyEq_nhdsNE_of_eqOn_LSeries
    {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : s.re = 1) (hcase : χ ^ 2 ≠ 1 ∨ s ≠ 1) (hLM : MeromorphicAt L s) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F s ∧ F s ≠ 0 ∧ L =ᶠ[𝓝[≠] s] F := by
  by_cases hχ : χ = 1
  · subst hχ
    have hs1 : s ≠ 1 := hcase.resolve_left (not_not.mpr (by ext; simp))
    set F : ℂ → ℂ := fun z ↦
      dedekindZetaC K z * (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔪 z
    have hζ : AnalyticAt ℂ (dedekindZetaC K) s := analyticAt_dedekindZetaC K hs1
    have hF : AnalyticAt ℂ F s :=
      hζ.mul (((1 : RayClassCharacter (Modulus.one K)).differentiable_eulerCorrection
        𝔪).analyticAt s)
    have hFne : F s ≠ 0 := mul_ne_zero
      (ne_zero_of_eqOn_dedekindZeta hs hs1 hζ.differentiableAt
        fun _ hz ↦ dedekindZetaC_eq_dedekindZeta K hz)
      ((1 : RayClassCharacter (Modulus.one K)).eulerCorrection_ne_zero 𝔪 (by norm_num [hs]))
    have hLF : EqOn L F {z | 1 < z.re} := fun z hz ↦ by
      dsimp only [F]
      rw [hLL hz]
      conv_lhs => rw [← map_one (induced (Modulus.one_dvd 𝔪))]
      rw [RayClassCharacter.LSeries_induced (Modulus.one_dvd 𝔪) 1 hz,
        RayClassCharacter.toUnitaryIdealWeight_one,
        UnitaryIdealWeight.toIdealArithmeticFunction_one,
        ← dedekindZeta_eq_LSeries_normCoeff_one, dedekindZetaC_eq_dedekindZeta K hz]
    exact ⟨F, hF, hFne, eventuallyEq_nhdsNE_of_meromorphicAt_of_analyticAt hs hLF hLM hF⟩
  · set F : ℂ → ℂ := continuedLFunctionOfWeight χ.toUnitaryIdealWeight
    have hUopen : IsOpen {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hF : AnalyticAt ℂ F s :=
      ((differentiableOn_continuedLFunctionOfWeight
        (hasCancellation_toUnitaryIdealWeight hχ)).analyticOnNhd hUopen) s
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K hs.ge)
    have hFne : F s ≠ 0 := continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero hχ hs.ge hcase
    have hLF : EqOn L F {z | 1 < z.re} := fun z hz ↦ by
      dsimp only [F]
      rw [hLL hz, continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hz]
    exact ⟨F, hF, hFne, eventuallyEq_nhdsNE_of_meromorphicAt_of_analyticAt hs hLF hLM hF⟩

/-- **Pointwise nonvanishing criterion on `Re s ≥ 1` for ray class L-functions.**
For any `L : ℂ → ℂ` agreeing with the `L`-series of `χ` on `{z | 1 < z.re}` and any `s` with
`1 ≤ s.re`, `L s ≠ 0` under branch-minimal hypotheses:
* on `1 < s.re`, series agreement alone suffices by the Euler product;
* on `s.re = 1` away from `χ ^ 2 = 1 ∧ s = 1`, complex differentiability of `L` at `s` suffices
  by `3-4-1` (supplying `continuedLFunctionOfWeight (χ ^ 2).toUnitaryIdealWeight` when
  `χ ^ 2 ≠ 1`);
* at `χ ^ 2 = 1 ∧ s = 1`, Landau's theorem applies given a continuation `Z` of `dedekindZeta K`
  holomorphic on `{z | 1 / 2 < z.re} \ {1}`, holomorphy of `L` on `{z | 1 / 2 < z.re}`, and the
  sharp boundary condition that `(Z σ * L σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`.
-/
theorem ne_zero_of_one_le_re {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hLs : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → DifferentiableAt ℂ L s)
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · rw [hLL hsgt, ← continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hsgt]
    exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ.toUnitaryIdealWeight hsgt
  · by_cases hsq : χ ^ 2 = 1
    · have hLL' : EqOn L
          (LSeries (normCoeff K χ.toMultiplicativeIdealWeight.toIdealArithmeticFunction))
          {z | 1 < z.re} := by
        simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
          val_toUnitaryIdealWeight] using hLL
      exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_isTrivialOnGood_sq
        (χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq) hLL' hs
        (fun hre hs1 ↦ hLs hre (.inr hs1)) (hlandau hsq)
    · exact χ.toUnitaryIdealWeight.ne_zero_of_eqOn_LSeries hseq.symm
        (hLs hseq.symm (.inl hsq)) hLL
        (differentiableAt_continuedLFunctionOfWeight (hasCancellation_toUnitaryIdealWeight hsq)
          (by norm_num [← hseq])).continuousAt
        fun z hz ↦ by
          rw [← toUnitaryIdealWeight_pow χ two_ne_zero]
          exact continuedLFunctionOfWeight_eq_LSeries (χ ^ 2).toUnitaryIdealWeight hz

/-- **Pointwise meromorphic order zero on `Re s ≥ 1` for ray class L-functions.** Under series
agreement on `Re z > 1`, `MeromorphicAt L s` away from `χ ^ 2 = 1 ∧ s = 1`, and the Landau
conditions at `χ ^ 2 = 1 ∧ s = 1`, `meromorphicOrderAt L s = 0`. -/
theorem meromorphicOrderAt_eq_zero_of_one_le_re {χ : RayClassCharacter 𝔪} {L : ℂ → ℂ}
    (hLL : EqOn L
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hLM : s.re = 1 → χ ^ 2 ≠ 1 ∨ s ≠ 1 → MeromorphicAt L s)
    (hlandau : χ ^ 2 = 1 → s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt L s = 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · exact (χ.toUnitaryIdealWeight.analyticAt_of_eqOn_LSeries hLL hsgt
      ).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr <| by
      rw [hLL hsgt, ← continuedLFunctionOfWeight_eq_LSeries χ.toUnitaryIdealWeight hsgt]
      exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ.toUnitaryIdealWeight hsgt
  · by_cases hboth : χ ^ 2 = 1 ∧ s = 1
    · obtain ⟨_, _, _, hL, _⟩ := hlandau hboth.1 hboth.2
      have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hne : L s ≠ 0 := ne_zero_of_one_le_re hLL hs
        (fun _ hcase ↦ hcase.elim (absurd hboth.1) (absurd hboth.2))
        hlandau
      exact (hL.analyticAt
        (hopen.mem_nhds (by simp only [mem_ofPred_eq]; linarith))).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hne
    · obtain ⟨F, hF, hFne, hgerm⟩ :=
        exists_analyticAt_ne_zero_eventuallyEq_nhdsNE_of_eqOn_LSeries hLL hseq.symm
          (not_and_or.mp hboth) (hLM hseq.symm (not_and_or.mp hboth))
      rw [meromorphicOrderAt_congr hgerm]
      exact hF.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hFne

/-- **Nonvanishing on `Re s ≥ 1` of the cancellation-continued ray class L-function.**
For any ray class character `χ` of any modulus `𝔪`,
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0` for every `s` with `1 ≤ s.re` provided
`χ ≠ 1` on `Re s = 1`, requiring `[K : ℚ] = 1` only in the exceptional case `χ ^ 2 = 1 ∧ s = 1`
(via Landau's theorem). On `Re s > 1`, nonvanishing holds for every `χ` (including `χ = 1`) via
the Euler product. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re
    {χ : RayClassCharacter 𝔪} {s : ℂ} (hχ : s.re = 1 → χ ≠ 1)
    (hK : χ ^ 2 = 1 → s = 1 → Module.finrank ℚ K = 1) (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re _ hsgt
  · have hχne : χ ≠ 1 := hχ hseq.symm
    by_cases hboth : χ ^ 2 = 1 ∧ s = 1
    · have htriv : (χ.toUnitaryIdealWeight ^ 2).val.IsTrivialOnGood := by
        rw [UnitaryIdealWeight.val_pow, val_toUnitaryIdealWeight]
        exact χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hboth.1
      exact hboth.2 ▸ continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one
        (hK hboth.1 hboth.2) (hasCancellation_toUnitaryIdealWeight hχne) htriv (hboth.2 ▸ hs)
    · exact continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero hχne hs (not_and_or.mp hboth)

end TauCeti.GlobalNumberFields.RayClassCharacter
