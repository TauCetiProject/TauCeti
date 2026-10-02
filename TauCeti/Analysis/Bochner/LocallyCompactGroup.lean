/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.PontryaginMeasure
import TauCeti.Analysis.Fourier.Pontryagin.StronglyContinuous
import TauCeti.Analysis.PositiveDefinite.Function.GNS

/-!
# Bochner's theorem on locally compact abelian groups

A positive-definite function `φ` on a second-countable locally compact abelian group `G` that is
continuous at `0` is the Fourier–Stieltjes transform `φ(g) = ∫ χ(g) dμ(χ)` of a finite positive
measure `μ` on the Pontryagin dual of `G`.

The measure comes from the GNS construction. The function `φ` is a matrix coefficient
`φ(g) = ⟪v, U(-g) v⟫` of the unitary translation representation `U` on its GNS Hilbert space,
which is strongly continuous because `φ` is continuous at `0`. The cyclic spectral theorem for
strongly continuous unitary representations,
`ContRepresentation.exists_pontryaginMeasureTransform_eq_inner`, writes such a matrix coefficient
as a Fourier–Stieltjes transform.

Second countability of `G` is assumed because that spectral theorem rests on the integrated form
of a strongly continuous representation, which is constructed only when the group or the
Hilbert space is second countable; the GNS space carries no such hypothesis, so it is imposed on
`G`. Discrete groups of any cardinality are covered separately in
`TauCeti.Analysis.Bochner.DiscreteGroup`.

## Main declarations

* `TauCeti.IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt`: a
  positive-definite function, continuous at `0`, on a second-countable locally compact abelian
  group is the Fourier–Stieltjes transform of a finite measure on the dual group.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016),
  Theorem 4.18.
-/

public section

open MeasureTheory

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- **Bochner's theorem on a second-countable locally compact abelian group**, existence half.
A positive-definite function that is continuous at `0` is the Fourier–Stieltjes transform of a
finite measure on the Pontryagin dual. -/
theorem IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt {φ : G → ℂ}
    (hφ : IsPositiveDefiniteSub φ) (hφ₀ : ContinuousAt φ 0) :
    ∃ μ : FiniteMeasure (PontryaginDual (Multiplicative G)), μ.pontryaginMeasureTransform = φ := by
  -- `φ g = ⟪U(g) v, v⟫ = ⟪v, U(-g) v⟫` for the GNS representation `U` and the vector `v` at `0`,
  -- so `φ` is a matrix coefficient of the representation `g ↦ U(-g)`.
  let π : ContRepresentation ℂ (Multiplicative G) hφ.gnsSpace := .ofMonoidHom <|
    (unitary _).subtype.comp <|
      Unitary.linearIsometryEquiv.symm.toMonoidHom.comp (hφ.gnsRepresentation.comp invMonoidHom)
  have hπ_apply (g : G) (v : hφ.gnsSpace) : π (.ofAdd g) v = hφ.gnsTranslation (-g) v := by
    rw [← ContRepresentation.toMonoidHom_apply]
    simp [π, ← ofAdd_neg]
  have hπ : ContRepresentation.IsUnitary π :=
    (ContRepresentation.isUnitary_iff_mem_unitary π).mpr fun g ↦ Subtype.prop _
  have hcont (v : hφ.gnsSpace) : Continuous fun g : G ↦ π (.ofAdd g) v := by
    simp_rw [hπ_apply]
    exact (hφ.continuous_gnsTranslation_apply hφ₀ v).comp continuous_neg
  obtain ⟨μ, hμ⟩ := π.exists_pontryaginMeasureTransform_eq_inner hcont hπ (hφ.gnsVector 0)
  refine ⟨μ, funext fun g ↦ ?_⟩
  rw [hμ, hπ_apply, ← hφ.gnsRepresentation_ofAdd, hφ.gnsRepresentation_gnsVector, add_zero,
    hφ.inner_gnsVector, zero_sub, neg_neg]

end TauCeti
