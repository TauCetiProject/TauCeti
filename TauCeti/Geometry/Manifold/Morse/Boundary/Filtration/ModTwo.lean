/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Filtration.Basic

/-!
# The critical-value filtration of the mod-two Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a Morse–Smale
pseudo-gradient adapted to `f`. The numbers of trajectories between critical points modulo two
lower the Morse index by one, strictly lower the critical value and square to zero, so they form
boundary coefficients `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeffs` in the
sense of `TauCeti.MorseBoundaryCoeffs`. The general construction of
`TauCeti.Geometry.Manifold.Morse.Boundary.Filtration.Basic` then filters the mod-two Morse complex
by critical values: its complex with all critical values is the mod-two Morse complex
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeffsComplexOnUnivIso`), so the
critical-value spectral sequence converges to mod-two Morse homology
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseFiltrationAbutmentIso`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseBoundaryCoeffs`: the mod-two trajectory counts as boundary coefficients.
* `morseBoundaryCoeffsComplexOnUnivIso`: their complex with all critical values is the mod-two
  Morse complex.
* `morseFiltrationAbutmentIso`: the abutment of their critical-value spectral sequence is mod-two
  Morse homology.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.4 (the filtration of the Morse complex by critical values
  and its spectral sequence).
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **The mod-two trajectory counts as boundary coefficients.** The coefficient of `q` in the
boundary of `p` is the number of trajectories from `p` to `q` modulo two
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeff`). -/
def morseBoundaryCoeffs : MorseBoundaryCoeffs E f (ZMod 2) where
  coeff := h.morseBoundaryCoeff hf
  finite_criticalPoints := hf.finite_criticalPoints
  morseIndex_eq_add_one_of_coeff_ne_zero := h.morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero hf
  value_lt_of_coeff_ne_zero := h.value_lt_of_morseBoundaryCoeff_ne_zero hf
  finsum_coeff_mul_coeff p r := by
    have := hf.finite_criticalPoints.to_subtype
    let _ := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
    rw [finsum_eq_sum_of_fintype]
    exact h.sum_morseBoundaryCoeff_mul_morseBoundaryCoeff hf p r

@[simp]
theorem morseBoundaryCoeffs_coeff : (h.morseBoundaryCoeffs hf).coeff = h.morseBoundaryCoeff hf :=
  (rfl)

/-- **The mod-two Morse complex with all critical values is the mod-two Morse complex.** -/
def morseBoundaryCoeffsComplexOnUnivIso :
    (h.morseBoundaryCoeffs hf).complexOn univ ≅ h.morseComplex hf :=
  (h.morseBoundaryCoeffs hf).complexOnUnivIso (h.morseBoundaryAt hf)
    (fun _ c q ↦ by rw [morseBoundaryCoeffs_coeff, h.morseBoundaryAt_apply hf c q])
    (h.morseBoundaryAt_comp_morseBoundaryAt hf)

/-- The identification of the mod-two Morse complex with all critical values with the mod-two
Morse complex sends a chain to the same chain. -/
@[simp]
theorem morseBoundaryCoeffsComplexOnUnivIso_hom_f_apply (n : ℕ)
    (c : MorseGenerators E f n univ →₀ ZMod 2) :
    (h.morseBoundaryCoeffsComplexOnUnivIso hf).hom.f n c =
      c.mapDomain (MorseGenerators.univEquiv E f n) :=
  MorseBoundaryCoeffs.complexOnUnivIso_hom_f_apply _ _ _ _ n c

/-- The inverse identification of the mod-two Morse complex with the mod-two Morse complex with
all critical values sends a chain to the same chain. -/
@[simp]
theorem morseBoundaryCoeffsComplexOnUnivIso_inv_f_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ZMod 2) :
    (h.morseBoundaryCoeffsComplexOnUnivIso hf).inv.f n c =
      c.mapDomain (MorseGenerators.univEquiv E f n).symm :=
  MorseBoundaryCoeffs.complexOnUnivIso_inv_f_apply _ _ _ _ n c

variable {a : ℤ → ℝ} (ha : Monotone a)

/-- **The abutment of the critical-value spectral sequence of the mod-two Morse complex** in
degree `-n` is the mod-two Morse homology in degree `n`. -/
def morseFiltrationAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((h.morseBoundaryCoeffs hf).monotone_filtration ha))).abutment (-n) ≅
      (h.morseComplex hf).homology n :=
  (h.morseBoundaryCoeffs hf).filtrationAbutmentIsoOfIso ha
    (h.morseBoundaryCoeffsComplexOnUnivIso hf) n

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
