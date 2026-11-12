/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.DiagonalMeasure

/-!
# The diagonal measure of a normal operator

Let `a` be a normal bounded operator on a complex Hilbert space `H` and let `ξ ∈ H`. The
functional `f ↦ ⟪ξ, f(a) ξ⟫` on continuous functions on `spectrum ℂ a` is positive, because the
continuous functional calculus sends nonnegative functions to positive operators. By the
Riesz–Markov–Kakutani theorem it is integration against a unique finite Borel measure `μ_ξ` on the
spectrum:

`⟪ξ, f(a) ξ⟫ = ∫ f dμ_ξ`.

This measure is the scalar spectral measure of `a` at `ξ`. Its total mass is `‖ξ‖²`, and it
computes `‖f(a) ξ‖²` as the squared `L²(μ_ξ)` norm of `f`. Polarizing these diagonal measures
gives the matrix elements of the bounded Borel functional calculus, which extends the continuous
calculus from continuous to bounded Borel symbols.

The diagonal measure and its integration identities specialize
`StarAlgHom.representationDiagMeasure` to the continuous functional calculus `cfcHom`.

`LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq` gives the analogous representation
on the character space of a commutative C⋆-algebra, as an existence statement. Here the measure
lives on the spectrum itself and is a named definition, so later constructions can refer to it.

## Main declarations

* `ContinuousLinearMap.diagMeasure a ξ`: the diagonal measure of a normal operator `a` at `ξ`, a
  finite measure on `spectrum ℂ a`.
* `ContinuousLinearMap.integral_diagMeasure_eq_inner_cfcHom`,
  `ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc`: `∫ f dμ_ξ = ⟪ξ, f(a) ξ⟫`.
* `ContinuousLinearMap.eq_diagMeasure_iff`: `μ_ξ` is the only finite measure with this property.
* `ContinuousLinearMap.diagMeasure_univ`: the total mass of `μ_ξ` is `‖ξ‖²`.
* `ContinuousLinearMap.integral_norm_sq_diagMeasure`: `∫ |f|² dμ_ξ = ‖f(a) ξ‖²`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  rev. ed., Academic Press (1980), §VII.2.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
-/

public section

noncomputable section

open MeasureTheory ContinuousMap
open scoped InnerProductSpace ComplexOrder CompactlySupported

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- The **diagonal measure** `μ_ξ` of a normal operator `a` at a vector `ξ`: the diagonal
Riesz measure for its unital continuous functional calculus, characterized by the identity
`∫ f dμ_ξ = ⟪ξ, f(a) ξ⟫`. -/
def diagMeasure (ξ : H) : Measure (spectrum ℂ a) :=
  (cfcHom (a := a) ‹_›).representationDiagMeasure ξ

instance (ξ : H) : IsFiniteMeasure (a.diagMeasure ξ) := by
  unfold diagMeasure
  infer_instance

/-- Integration against the diagonal measure `μ_ξ` computes the diagonal matrix element
of the continuous functional calculus: `∫ f dμ_ξ = ⟪ξ, f(a) ξ⟫`. -/
theorem integral_diagMeasure_eq_inner_cfcHom (ξ : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ x, f x ∂(a.diagMeasure ξ) = ⟪ξ, cfcHom ‹_› f ξ⟫_ℂ :=
  (cfcHom (a := a) ‹_›).integral_representationDiagMeasure ξ f

/-- The `cfc` form of `integral_diagMeasure_eq_inner_cfcHom`: for `f` continuous on the spectrum
of a normal operator `a`, `∫ f dμ_ξ = ⟪ξ, cfc f a ξ⟫`. -/
theorem integral_diagMeasure_eq_inner_cfc (ξ : H) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    ∫ x, f x ∂(a.diagMeasure ξ) = ⟪ξ, cfc f a ξ⟫_ℂ := by
  rw [cfc_apply f a, ← integral_diagMeasure_eq_inner_cfcHom]
  simp

/-- The diagonal measure `μ_ξ` is the unique finite measure on the spectrum of a normal
operator `a` that represents `f ↦ ⟪ξ, f(a) ξ⟫` on continuous functions. -/
theorem eq_diagMeasure_iff (ξ : H) (μ : Measure (spectrum ℂ a)) [IsFiniteMeasure μ] :
    μ = a.diagMeasure ξ ↔ ∀ f : C(spectrum ℂ a, ℂ), ∫ x, f x ∂μ = ⟪ξ, cfcHom ‹_› f ξ⟫_ℂ := by
  exact (cfcHom (a := a) ‹_›).eq_representationDiagMeasure_iff ξ μ

/-- The total mass of the diagonal measure `μ_ξ`, as a real number, is `‖ξ‖²`. -/
@[simp]
theorem diagMeasure_real_univ (ξ : H) : (a.diagMeasure ξ).real Set.univ = ‖ξ‖ ^ 2 :=
  (cfcHom (a := a) ‹_›).representationDiagMeasure_real_univ ξ

/-- The total mass of the diagonal measure `μ_ξ` is `‖ξ‖²`. -/
@[simp]
theorem diagMeasure_univ (ξ : H) : a.diagMeasure ξ Set.univ = ‖ξ‖ₑ ^ 2 :=
  (cfcHom (a := a) ‹_›).representationDiagMeasure_univ ξ

/-- The diagonal measure `μ_ξ` computes `‖f(a) ξ‖²` as the squared `L²(μ_ξ)` norm of `f`:
`∫ |f|² dμ_ξ = ‖f(a) ξ‖²`. -/
theorem integral_norm_sq_diagMeasure (ξ : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ x, ‖f x‖ ^ 2 ∂(a.diagMeasure ξ) = ‖cfcHom ‹_› f ξ‖ ^ 2 :=
  (cfcHom (a := a) ‹_›).integral_norm_sq_representationDiagMeasure ξ f

end ContinuousLinearMap
