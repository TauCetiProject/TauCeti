/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Algebra.Module.ZLattice.Dual

/-!
# Summing Schwartz functions over a lattice

A Schwartz function decays faster than every power of `‖x‖`, while the power `‖x‖ ^ r` is
summable over a discrete subgroup `L` of a finite-dimensional real normed space as soon as
`r < -rank L` (Mathlib's `ZLattice.summable_norm_sub_rpow`). Comparing the two, every translate
`ℓ ↦ f (v + ℓ)` of a Schwartz function is absolutely summable over `L`.

These are the two summability statements behind Poisson summation over a full lattice `L` in a
finite-dimensional real inner product space, which is not proved here,

`∑' ℓ : L, f (v + ℓ) = (covolume L)⁻¹ * ∑' m : L^∨, exp (2πi ⟪v, m⟫) • 𝓕 f m`,

for a Schwartz function `f`. The lattice side is summable by the comparison above, and the dual
side because the Fourier transform of a Schwartz function is again a Schwartz function and the
phases `exp (2πi ⟪v, m⟫)` have norm one. Both are recorded on their own, in absolute form and in
the plain form for a complete codomain, so that each side can be manipulated on its own.

## Main statements

* `ZLattice.summable_norm_poisson_left`, `ZLattice.summable_poisson_left`: the translates of a
  Schwartz function are (absolutely) summable over a discrete subgroup `L`.
* `ZLattice.summable_norm_poisson_right_smul`, `ZLattice.summable_poisson_right_smul`: the
  Fourier transform of a Schwartz function, twisted by the phases `exp (2πi ⟪v, m⟫)`, is
  (absolutely) summable over the dual `L^∨` of a full lattice `L`.
* `ZLattice.summable_norm_poisson_right`, `ZLattice.summable_poisson_right`: the same for a
  complex-valued Schwartz function, with the summand `𝓕 f m * exp (2πi ⟪v, m⟫)`.
-/

public section

open Complex Filter Module Topology
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform

namespace ZLattice

section Left

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The translates `ℓ ↦ f (v + ℓ)` of a Schwartz function are absolutely summable over a discrete
subgroup `L` of a finite-dimensional real normed space. -/
theorem summable_norm_poisson_left (f : 𝓢(E, F)) (v : E) :
    Summable fun ℓ : L ↦ ‖f (v + ℓ)‖ := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r < -finrank ℤ L := ⟨-finrank ℤ L - 1, by linarith⟩
  -- The points `v + ℓ` leave every compact set of `E`, because `L` is closed and discrete.
  have hL : Tendsto ((↑) : L → E) cofinite (cocompact E) :=
    L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›)
  have ht : Tendsto (fun ℓ : L ↦ v + (ℓ : E)) cofinite (cocompact E) :=
    (Homeomorph.addLeft v).isClosedEmbedding.tendsto_cocompact.comp hL
  refine summable_of_isBigO ((summable_norm_sub_rpow L r hr (-v)).congr fun ℓ ↦ ?_)
    ((f.isBigO_cocompact_rpow r).comp_tendsto ht).norm_left
  simp [add_comm]

/-- The translates `ℓ ↦ f (v + ℓ)` of a Schwartz function with values in a Banach space are
summable over a discrete subgroup `L` of a finite-dimensional real normed space. -/
theorem summable_poisson_left [CompleteSpace F] (f : 𝓢(E, F)) (v : E) :
    Summable fun ℓ : L ↦ f (v + ℓ) :=
  (summable_norm_poisson_left L f v).of_norm

end Left

section Right

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The Fourier transform of a Schwartz function, twisted by the phases `exp (2πi ⟪v, m⟫)`, is
absolutely summable over the dual `L^∨` of a full lattice `L`: the dual side of Poisson
summation. -/
theorem summable_norm_poisson_right_smul (f : 𝓢(E, F)) (v : E) :
    Summable fun m : dual L ↦ ‖cexp (2 * π * I * ⟪v, (m : E)⟫) • 𝓕 (f : E → F) m‖ := by
  have hphase (m : dual L) : ‖cexp (2 * π * I * ⟪v, (m : E)⟫)‖ = 1 := by
    rw [norm_exp]
    simp
  simpa [norm_smul, hphase, SchwartzMap.fourier_coe] using
    summable_norm_poisson_left (dual L) (𝓕 f) 0

/-- The Fourier transform of a Schwartz function with values in a complex Banach space, twisted by
the phases `exp (2πi ⟪v, m⟫)`, is summable over the dual `L^∨` of a full lattice `L`. -/
theorem summable_poisson_right_smul [CompleteSpace F] (f : 𝓢(E, F)) (v : E) :
    Summable fun m : dual L ↦ cexp (2 * π * I * ⟪v, (m : E)⟫) • 𝓕 (f : E → F) m :=
  (summable_norm_poisson_right_smul L f v).of_norm

/-- The Fourier transform of a complex-valued Schwartz function, times the phases
`exp (2πi ⟪v, m⟫)`, is absolutely summable over the dual `L^∨` of a full lattice `L`. -/
theorem summable_norm_poisson_right (f : 𝓢(E, ℂ)) (v : E) :
    Summable fun m : dual L ↦ ‖𝓕 (f : E → ℂ) m * cexp (2 * π * I * ⟪v, (m : E)⟫)‖ :=
  (summable_norm_poisson_right_smul L f v).congr fun m ↦ by rw [smul_eq_mul, mul_comm]

/-- The Fourier transform of a complex-valued Schwartz function, times the phases
`exp (2πi ⟪v, m⟫)`, is summable over the dual `L^∨` of a full lattice `L`: the dual side of
Poisson summation. -/
theorem summable_poisson_right (f : 𝓢(E, ℂ)) (v : E) :
    Summable fun m : dual L ↦ 𝓕 (f : E → ℂ) m * cexp (2 * π * I * ⟪v, (m : E)⟫) :=
  (summable_norm_poisson_right L f v).of_norm

end Right

end ZLattice
