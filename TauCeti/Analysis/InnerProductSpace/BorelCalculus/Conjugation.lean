/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.Unitary

/-!
# Unitary conjugation of the Borel functional calculus

Conjugating a normal bounded operator `a : H →L[ℂ] H` by a Hilbert-space linear isometric
equivalence `U : H ≃ₗᵢ[ℂ] H'` preserves its spectrum and conjugates its Borel functional
calculus.

## Main declarations

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
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

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

end ContinuousLinearMap
