/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import TauCeti.Analysis.InnerProductSpace.OperatorIdentities

/-!
# Polarized diagonal integrals

For a normal bounded operator `a` on a complex Hilbert space, the diagonal spectral
measures determine the matrix elements of the continuous functional calculus.
The **polarized diagonal pairing** uses a four-term combination of diagonal
integrals. For a continuous symbol, the pairing equals
`⟪ψ, cfcHom (a := a) _ f ξ⟫_ℂ`.

The pairing can also be formed for symbols that are not continuous, although
its identification with an operator requires additional hypotheses.

## Source

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean`.
-/
public section

open MeasureTheory
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The polarized pairing of a symbol on the spectrum of a normal bounded
operator. For a continuous symbol, this equals the corresponding matrix element
of the continuous functional calculus. -/
noncomputable def pair (a : H →L[ℂ] H) [IsStarNormal a]
    (f : spectrum ℂ a → ℂ) (ψ ξ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ((∫ x, f x ∂(a.diagMeasure (ξ + ψ)))
      + Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ + Complex.I • ψ)))
      - (∫ x, f x ∂(a.diagMeasure (ξ - ψ)))
      - Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ - Complex.I • ψ))))

/-- The four diagonal integrals defining the polarized pairing. -/
theorem pair_def (a : H →L[ℂ] H) [IsStarNormal a]
    (f : spectrum ℂ a → ℂ) (ψ ξ : H) :
    pair a f ψ ξ = (1 / 4 : ℂ) *
      ((∫ x, f x ∂(a.diagMeasure (ξ + ψ)))
        + Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ + Complex.I • ψ)))
        - (∫ x, f x ∂(a.diagMeasure (ξ - ψ)))
        - Complex.I * (∫ x, f x ∂(a.diagMeasure (ξ - Complex.I • ψ)))) :=
  (rfl)

/-- For continuous symbols, the polarized pairing is the matrix element of
the continuous functional calculus. -/
theorem pair_of_continuous (a : H →L[ℂ] H) [IsStarNormal a]
    (f : C(spectrum ℂ a, ℂ)) (ψ ξ : H) :
    pair a (fun x => f x) ψ ξ = ⟪ψ, cfcHom (a := a) ‹_› f ξ⟫_ℂ := by
  rw [pair_def,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ + ψ) f,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ + Complex.I • ψ) f,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ - ψ) f,
    a.integral_diagMeasure_eq_inner_cfcHom (ξ - Complex.I • ψ) f]
  exact inner_polarization (cfcHom (a := a) ‹_› f) ψ ξ

end ContinuousLinearMap
