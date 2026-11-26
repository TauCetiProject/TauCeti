/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
public import TauCeti.NumberTheory.LFunctions.Hecke.ChangeModulus
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
import TauCeti.NumberTheory.LFunctions.DedekindZeta.WeightedClassSum
import TauCeti.NumberTheory.LFunctions.Hecke.Orthogonality

/-!
# Continuation for characters of the ordinary ideal class group

At the unit modulus, Hecke's completed partial zeta functions (Neukirch, *Algebraic Number
Theory*, VII §5) give a continuation of every character L-series. The residues at `0` and
`1` do not depend on the ideal class. For a nonprincipal character, the character weights
sum to zero, so these two poles cancel and the uncompleted L-function is entire as well.
The principal character gives the continued Dedekind zeta function.
-/

public section

open Complex Finset NumberField Set
open scoped nonZeroDivisors

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The continued Hecke L-function of a nonprincipal character at the unit modulus is entire
and agrees with the defining L-series on `Re s > 1`. -/
private theorem analyticAt_and_eq_LSeries_heckeLFunctionC_of_modulus_one
    {χ : RayClassCharacter (Modulus.one K)} (hχ : χ ≠ 1) :
    (∀ s, AnalyticAt ℂ (heckeLFunctionC χ) s) ∧
      ∀ s : ℂ, 1 < s.re → heckeLFunctionC χ s =
        LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  classical
  let _ := Fintype.ofFinite (RayClassGroup (Modulus.one K))
  choose J hJ using ClassGroup.mk0_surjective (R := 𝓞 K)
  let I (c : RayClassGroup (Modulus.one K)) :=
    FractionalIdeal.mk0 K (J (oneEquivClassGroup c)⁻¹)
  have hI (c : RayClassGroup (Modulus.one K)) :
      oneEquivClassGroup.symm (ClassGroup.mk K (I c))⁻¹ = c := by
    simp [I, ClassGroup.mk_mk0, hJ]
  have hsum : ∑ c : RayClassGroup (Modulus.one K), (χ c : ℂ) = 0 :=
    sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) (by
      rwa [← MonoidHom.comp_one (Units.coeHom ℂ), ne_eq,
        MonoidHom.cancel_left Units.coeHom_injective])
  let g (z : ℂ) := ∑ c, (χ c : ℂ) * completedPartialZeta (I c) z
  let F := invDedekindZetaCompletionFactor K * toMeromorphicNFOn g univ
  have hF (s : ℂ) : AnalyticAt ℂ F s :=
    (analyticAt_invDedekindZetaCompletionFactor K s).mul
      (analyticAt_toMeromorphicNFOn_sum_mul_completedPartialZeta univ I _ hsum s)
  have hagree (s : ℂ) (hs : 1 < s.re) : F s =
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
    have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs₁ : s ≠ 1 := by rintro rfl; norm_num at hs
    have hg : Meromorphic g := by dsimp only [g]; fun_prop
    have hga : AnalyticAt ℂ g s := Finset.analyticAt_fun_sum _ fun c _ ↦
      analyticAt_const.mul (analyticAt_completedPartialZeta (I c) hs₀ hs₁)
    dsimp only [F]
    rw [Pi.mul_apply, toMeromorphicNFOn_apply_of_analyticAt hg hga]
    simp_rw [g, completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one _ hs, hI,
      mul_left_comm (χ _ : ℂ)]
    rw [← Finset.mul_sum, ← mul_assoc,
      invDedekindZetaCompletionFactor_mul_eq_one K (zero_lt_one.trans hs), one_mul,
      sum_mul_LSeries_rayClassCoeff _ hs]
  rw [heckeLFunctionC_def, meromorphicContinuation_eq (fun z _ ↦ (hF z).meromorphicNFAt) hagree]
  exact ⟨hF, hagree⟩

/-- For every character of the ordinary ideal class group, the continued Hecke L-function
agrees with its Dirichlet series on the half-plane of absolute convergence. -/
theorem heckeLFunctionC_eq_LSeries_of_modulus_one (χ : RayClassCharacter (Modulus.one K))
    {s : ℂ} (hs : 1 < s.re) : heckeLFunctionC χ s =
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · rw [heckeLFunctionC_one_modulus_one, dedekindZetaC_eq_dedekindZeta K hs,
      RayClassCharacter.toUnitaryIdealWeight_one, UnitaryIdealWeight.toIdealArithmeticFunction_one,
      dedekindZeta_eq_LSeries_normCoeff_one]
  · exact (analyticAt_and_eq_LSeries_heckeLFunctionC_of_modulus_one hχ).2 s hs

/-- The Hecke L-function of a nonprincipal character of the ordinary ideal class group
is entire. -/
theorem analyticAt_heckeLFunctionC_of_modulus_one {χ : RayClassCharacter (Modulus.one K)}
    (hχ : χ ≠ 1) (s : ℂ) : AnalyticAt ℂ (heckeLFunctionC χ) s :=
  (analyticAt_and_eq_LSeries_heckeLFunctionC_of_modulus_one hχ).1 s

/-- On the larger half-plane supplied by cancellation, the entire Hecke L-function of a
nonprincipal ideal class character agrees with the partial-summation continuation. -/
theorem heckeLFunctionC_eq_continuedLFunctionOfWeight_of_modulus_one
    {χ : RayClassCharacter (Modulus.one K)} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) :
    heckeLFunctionC χ s = continuedLFunctionOfWeight χ.toUnitaryIdealWeight s := by
  have hc := RayClassCharacter.hasCancellation_toUnitaryIdealWeight_iff.mpr hχ
  have hF : Differentiable ℂ (heckeLFunctionC χ) := fun z ↦
    (analyticAt_heckeLFunctionC_of_modulus_one hχ z).differentiableAt
  refine hF.differentiableOn.eqOn_of_eqOn_re_gt (differentiableOn_continuedLFunctionOfWeight hc)
    (b := 1) (fun z hz ↦ ?_) hs
  rw [heckeLFunctionC_eq_LSeries_of_modulus_one χ hz, continuedLFunctionOfWeight_eq_LSeries _ hz]

end TauCeti.LFunctions
