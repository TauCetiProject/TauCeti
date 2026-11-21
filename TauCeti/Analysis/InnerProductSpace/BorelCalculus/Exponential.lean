/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.Unitary

/-!
# Exponentials, real symbols, and unitary transport in the Borel functional calculus

For a normal bounded operator `a` on a complex Hilbert space `H`, the Borel functional calculus
`a.borelCalculus` is continuous (`ContinuousLinearMap.continuous_borelCalculus`), so by
`NormedSpace.map_exp` it commutes with the Banach-algebra exponential `NormedSpace.exp`:
`(exp f)(a) = exp (f(a))`.

A bounded measurable real-valued function `g : spectrum ℂ a → ℝ` defines a self-adjoint bounded
Borel symbol `BoundedBorelFunction.ofRealFunction g hg hbound`. When `g` is nonnegative everywhere,
`BoundedBorelFunction.exists_star_mul_self_ofRealFunction` factors it as `star s * s`; since every
star homomorphism into `H →L[ℂ] H` sends `star s * s` to a nonnegative operator in the Loewner
order, pointwise bounds `m ≤ g ≤ M` on the spectrum become operator inequalities
`m • 1 ≤ g(a) ≤ M • 1`.

Finally, conjugating a normal operator `a` by a linear isometric equivalence `U : H ≃ₗᵢ[ℂ] H'`
preserves its spectrum and conjugates its Borel functional calculus.

## Main declarations

* `ContinuousLinearMap.borelCalculus_exp`: `a.borelCalculus (exp f) = exp (a.borelCalculus f)`.
* `ContinuousLinearMap.isSelfAdjoint_borelCalculus_ofRealFunction`: real-valued symbols produce
  self-adjoint operators.
* `ContinuousLinearMap.borelCalculus_ofRealFunction_nonneg`,
  `ContinuousLinearMap.smul_one_le_borelCalculus_ofRealFunction`,
  `ContinuousLinearMap.borelCalculus_ofRealFunction_le_smul_one`: Loewner order bounds for real
  Borel symbols.
* `ContinuousLinearMap.borelCalculus_conj`: unitary conjugation of the Borel functional calculus.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.24.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped CStarAlgebra InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- **Exponential compatibility of the Borel functional calculus.** For every bounded Borel symbol
`f` on the spectrum of a normal operator `a`, `(exp f)(a) = exp (f(a))`. -/
theorem borelCalculus_exp (f : BoundedBorelFunction (spectrum ℂ a)) :
    a.borelCalculus (NormedSpace.exp f) = NormedSpace.exp (a.borelCalculus f) := by
  let +nondep : NormedAlgebra ℚ (BoundedBorelFunction (spectrum ℂ a)) := .restrictScalars ℚ ℂ _
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp a.borelCalculus a.continuous_borelCalculus f

/-- The Borel functional calculus sends real-valued symbols to self-adjoint operators. -/
theorem isSelfAdjoint_borelCalculus_ofRealFunction (g : spectrum ℂ a → ℝ) (hg : Measurable g)
    (hbound) :
    IsSelfAdjoint (a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound)) :=
  (BoundedBorelFunction.isSelfAdjoint_ofRealFunction g hg hbound).map a.borelCalculus

/-- A nonnegative real-valued Borel symbol produces a nonnegative operator in the Loewner order. -/
theorem borelCalculus_ofRealFunction_nonneg {g : spectrum ℂ a → ℝ} (hg : Measurable g) (hbound)
    (h0 : ∀ x, 0 ≤ g x) :
    0 ≤ a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  obtain ⟨s, hs⟩ := BoundedBorelFunction.exists_star_mul_self_ofRealFunction hg hbound h0
  rw [hs, map_mul, map_star]
  exact star_mul_self_nonneg (a.borelCalculus s)

/-- A lower bound `m ≤ g x` on the spectrum gives the Loewner lower bound `m • 1 ≤ g(a)`. -/
theorem smul_one_le_borelCalculus_ofRealFunction {g : spectrum ℂ a → ℝ} (hg : Measurable g)
    (hbound) {m : ℝ} (hm : ∀ x, m ≤ g x) :
    m • (1 : H →L[ℂ] H) ≤ a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  obtain ⟨M, _, hgM⟩ := id hbound
  have hsub_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x - m| ≤ C :=
    ⟨M + |m|, by positivity, fun x ↦ (abs_sub _ _).trans (add_le_add (hgM x) le_rfl)⟩
  have hsym : BoundedBorelFunction.ofRealFunction g hg hbound -
      algebraMap ℂ (BoundedBorelFunction (spectrum ℂ a)) m =
      BoundedBorelFunction.ofRealFunction (fun x ↦ g x - m)
        (hg.sub measurable_const) hsub_bound := by
    ext x
    simp
  rw [← sub_nonneg]
  have hop : a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) -
      m • (1 : H →L[ℂ] H) =
      a.borelCalculus (BoundedBorelFunction.ofRealFunction (fun x ↦ g x - m)
        (hg.sub measurable_const) hsub_bound) := by
    have := congrArg a.borelCalculus hsym
    rwa [map_sub, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at this
  rw [hop]
  exact a.borelCalculus_ofRealFunction_nonneg _ hsub_bound fun x ↦ sub_nonneg.2 (hm x)

/-- An upper bound `g x ≤ M` on the spectrum gives the Loewner upper bound `g(a) ≤ M • 1`. -/
theorem borelCalculus_ofRealFunction_le_smul_one {g : spectrum ℂ a → ℝ} (hg : Measurable g)
    (hbound) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) ≤ M • (1 : H →L[ℂ] H) := by
  obtain ⟨B, _, hgB⟩ := id hbound
  have hsub_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |M - g x| ≤ C :=
    ⟨|M| + B, by positivity, fun x ↦ (abs_sub _ _).trans (add_le_add le_rfl (hgB x))⟩
  have hsym : algebraMap ℂ (BoundedBorelFunction (spectrum ℂ a)) M -
      BoundedBorelFunction.ofRealFunction g hg hbound =
      BoundedBorelFunction.ofRealFunction (fun x ↦ M - g x)
        (measurable_const.sub hg) hsub_bound := by
    ext x
    simp
  rw [← sub_nonneg]
  have hop : M • (1 : H →L[ℂ] H) -
      a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) =
      a.borelCalculus (BoundedBorelFunction.ofRealFunction (fun x ↦ M - g x)
        (measurable_const.sub hg) hsub_bound) := by
    have := congrArg a.borelCalculus hsym
    rwa [map_sub, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at this
  rw [hop]
  exact a.borelCalculus_ofRealFunction_nonneg _ hsub_bound fun x ↦ sub_nonneg.2 (hM x)

section UnitaryConj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Unitary conjugation of the Borel functional calculus.** For a linear isometric equivalence
`U : H ≃ₗᵢ[ℂ] H'` and a normal operator `a : H →L[ℂ] H`, the Borel functional calculus of
`U a U⁻¹` is `U · U⁻¹` applied to the Borel functional calculus of `a`, after identifying the two
equal spectra. -/
theorem borelCalculus_conj (U : H ≃ₗᵢ[ℂ] H')
    (f : BoundedBorelFunction (spectrum ℂ (U.conjStarAlgEquiv a))) :
    (U.conjStarAlgEquiv a).borelCalculus f =
      U.conjStarAlgEquiv (a.borelCalculus
        (BoundedBorelFunction.compStarAlgHom'
          (Set.inclusion (AlgEquiv.spectrum_eq U.conjStarAlgEquiv a).ge)
          measurable_subtypeVal.subtype_mk f)) := by
  let a' : H' →L[ℂ] H' := U.conjStarAlgEquiv a
  let σc : C(spectrum ℂ a, spectrum ℂ a') :=
    ⟨Set.inclusion (AlgEquiv.spectrum_eq U.conjStarAlgEquiv a).ge, continuous_inclusion _⟩
  have hσ : Measurable ⇑σc := measurable_subtypeVal.subtype_mk
  -- Push `a.spectralPVM` along `σc` and conjugate its representation by `U`; uniqueness of the
  -- spectral measure on continuous symbols identifies the result with `a'.spectralPVM`.
  let π' : C(spectrum ℂ a', ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (cfcHom (a := a) ‹_›).comp (ContinuousMap.compStarAlgHom' ℂ ℂ σc)
  have hid : ((ContinuousMap.id ℂ).restrict (spectrum ℂ a')).comp σc =
      (ContinuousMap.id ℂ).restrict (spectrum ℂ a) := by
    ext x
    rfl
  have hcfc : cfcHom (R := ℂ) (p := IsStarNormal) (a := a') inferInstance =
      U.conjStarAlgEquiv.toStarAlgHom.comp π' := by
    refine cfcHom_eq_of_continuous_of_map_id _ _
      (map_continuous (U.conjStarAlgEquiv.toStarAlgHom.comp π')) ?_
    simp only [a', π', StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply, hid, cfcHom_id,
      StarAlgEquiv.toStarAlgHom_apply]
  have hreg (Q : ProjValMeasure (spectrum ℂ a') H) (ξ : H) :
      (Q.diag ξ).Regular := inferInstance
  have hpvm : a.spectralPVM.map ⇑σc hσ = ProjValMeasure.ofRepresentation π' := by
    refine (ProjValMeasure.eq_ofRepresentation_iff π' _ (hreg _)).2 fun g ↦ ?_
    rw [ProjValMeasure.integral_map, BoundedBorelFunction.compStarAlgHom'_ofContinuousMap σc hσ,
      a.integral_spectralPVM, a.borelCalculus_ofContinuousMap]
    simp only [π', StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
  calc a'.borelCalculus f
      = a'.spectralPVM.integral f := by rw [a'.integral_spectralPVM]
    _ = (ProjValMeasure.ofRepresentation (U.conjStarAlgEquiv.toStarAlgHom.comp π')).integral f :=
          congrArg (fun P : ProjValMeasure (spectrum ℂ a') H' ↦ P.integral f)
            (a'.spectralPVM_eq_ofRepresentation.trans
              (congrArg ProjValMeasure.ofRepresentation hcfc))
    _ = U.conjStarAlgEquiv ((ProjValMeasure.ofRepresentation π').integral f) :=
          StarAlgHom.integral_ofRepresentation_conj π' U f
    _ = U.conjStarAlgEquiv ((a.spectralPVM.map ⇑σc hσ).integral f) := by rw [← hpvm]
    _ = U.conjStarAlgEquiv (a.borelCalculus (BoundedBorelFunction.compStarAlgHom' ⇑σc hσ f)) := by
          rw [ProjValMeasure.integral_map, a.integral_spectralPVM]

end UnitaryConj

end ContinuousLinearMap
