/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.PontryaginMeasure
import TauCeti.Analysis.Fourier.Pontryagin.UnitaryRepresentation
import TauCeti.Analysis.PositiveDefinite.Function.GNS

/-!
# Bochner's theorem on discrete abelian groups

A function `φ` on a discrete abelian group `G` is positive definite,
`∑ᵢ ∑ⱼ cᵢ conj(cⱼ) φ(gᵢ - gⱼ) ≥ 0` for every finite family, if and only if it is the
Fourier–Stieltjes transform `φ(g) = ∫ χ(g) dμ(χ)` of a finite positive measure `μ` on the
Pontryagin dual of `G`. Every function on a discrete group is continuous, so no continuity
hypothesis appears.

The measure comes from the GNS construction. The positive-definite function `φ` is a matrix
coefficient `φ(g) = ⟪U(g) v, v⟫` of the unitary translation representation `U` on its GNS Hilbert
space, and the cyclic spectral theorem for unitary representations of discrete abelian groups,
`MonoidHom.exists_pontryaginMeasureTransform_eq_inner`, writes such a matrix coefficient as a
Fourier–Stieltjes transform.

For `G = ℤ` this recovers Herglotz's theorem, proved separately by Fejér means in
`TauCeti.Analysis.Bochner.Herglotz`.

## Main declarations

* `TauCeti.IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq`: a positive-definite
  function on a discrete abelian group is the Fourier–Stieltjes transform of a finite measure on
  the dual group.
* `TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq`: **Bochner's theorem**
  for discrete abelian groups.

## References

* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), §1.4.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.3
  and §4.2.
-/

public section

open MeasureTheory

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- A positive-definite function on a discrete abelian group is the Fourier–Stieltjes transform
of a finite measure on the Pontryagin dual. -/
theorem IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq {φ : G → ℂ}
    (hφ : IsPositiveDefiniteSub φ) :
    ∃ μ : FiniteMeasure (PontryaginDual (Multiplicative G)), μ.pontryaginMeasureTransform = φ := by
  -- `φ g = ⟪U(g) v, v⟫ = ⟪v, U(-g) v⟫` for the GNS representation `U` and the vector `v` at `0`,
  -- so `φ` is a matrix coefficient of the representation `g ↦ U(-g)`.
  let ρ : Multiplicative G →* unitary (hφ.gnsSpace →L[ℂ] hφ.gnsSpace) :=
    Unitary.linearIsometryEquiv.symm.toMonoidHom.comp (hφ.gnsRepresentation.comp invMonoidHom)
  obtain ⟨μ, hμ⟩ := ρ.exists_pontryaginMeasureTransform_eq_inner (hφ.gnsVector 0)
  refine ⟨μ, funext fun g ↦ ?_⟩
  simp [hμ, ρ, ← ofAdd_neg]

/-- **Bochner's theorem on a discrete abelian group.** A function on a discrete abelian group is
positive definite if and only if it is the Fourier–Stieltjes transform of a finite measure on the
Pontryagin dual. -/
theorem isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq (φ : G → ℂ) :
    IsPositiveDefiniteSub φ ↔
      ∃ μ : FiniteMeasure (PontryaginDual (Multiplicative G)),
        μ.pontryaginMeasureTransform = φ :=
  ⟨IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq,
    fun ⟨μ, hμ⟩ ↦ hμ ▸ μ.isPositiveDefiniteSub_pontryaginMeasureTransform⟩

end TauCeti
