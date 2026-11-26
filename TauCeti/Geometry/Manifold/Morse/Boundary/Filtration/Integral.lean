/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Filtration.Basic

/-!
# The critical-value filtration of the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, and `𝔬` orientations of the unstable manifolds. Suppose that the integral Morse boundary
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` with coefficients in a ring `R` squares to
zero, so that it is the differential of the integral Morse complex
`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex`. The integral boundary coefficients
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff` (the signed counts of trajectories
between critical points when `X` is Morse–Smale) lower the Morse index by one and strictly lower
the critical value, so they form boundary coefficients
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeffs` in the sense of
`TauCeti.MorseBoundaryCoeffs`.

The general construction of `TauCeti.Geometry.Manifold.Morse.Boundary.Filtration.Basic` then
filters the integral Morse complex by critical values. Its complex with all critical values is the
integral Morse complex
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeffsComplexOnUnivIso`). So the
critical-value spectral sequence, whose first page is free over `R` on the critical points in each
band when each band contains a single critical value
(`TauCeti.MorseBoundaryCoeffs.spectralSequenceFirstPageXIsoOfSubsingleton`), converges to the
homology of the integral Morse complex `signedMorseComplex` with coefficients in `R`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseFiltrationAbutmentIso`). The vanishing of `∂ ∘ ∂` is
a hypothesis here, as it is for the integral Morse complex itself.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedMorseBoundaryCoeffs`: the integral boundary coefficients as boundary coefficients
  over `R`.
* `signedMorseBoundaryCoeffsComplexOnUnivIso`: their complex with all critical values is the
  integral Morse complex.
* `signedMorseFiltrationAbutmentIso`: the abutment of their critical-value spectral sequence is
  the homology of the integral Morse complex with coefficients in `R`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ`) and §6.4 (the filtration of
  the Morse complex by critical values and its spectral sequence).
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

variable {hX : IsAdaptedPseudoGradient f X} {𝔬 : MorseOrientation f X}
  {hf : IsMorse 𝓘(ℝ, E) f} {R : Type*} [Ring R]

variable (hX 𝔬 hf R) in
/-- **The integral boundary coefficients as boundary coefficients.** When the integral Morse
boundary with coefficients in `R` squares to zero, the coefficient of `q` in the boundary of `p` is
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff`, read in `R`. When `X` is Morse–Smale
this is the signed count of trajectories from `p` to `q`. -/
def signedMorseBoundaryCoeffs
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    MorseBoundaryCoeffs E f R where
  coeff p q := hX.signedMorseBoundaryCoeff 𝔬 p q
  finite_criticalPoints := hf.finite_criticalPoints
  morseIndex_eq_add_one_of_coeff_ne_zero {p q} hpq :=
    morseIndex_eq_add_one_of_signedMorseBoundaryCoeff_ne_zero fun h0 ↦
      hpq (by rw [h0, Int.cast_zero])
  value_lt_of_coeff_ne_zero {p q} hpq :=
    value_lt_of_signedMorseBoundaryCoeff_ne_zero fun h0 ↦ hpq (by rw [h0, Int.cast_zero])
  finsum_coeff_mul_coeff p r := by
    have := hf.finite_criticalPoints.to_subtype
    let _ := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
    -- Evaluate `∂ (∂ p) = 0` at `r`.
    have h := DFunLike.congr_fun (LinearMap.congr_fun hsq (Finsupp.single p 1)) r
    rw [LinearMap.comp_apply, signedMorseBoundary_apply,
      Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _] at h
    rw [finsum_eq_sum_of_fintype]
    simpa using h

variable (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0)

@[simp]
theorem signedMorseBoundaryCoeffs_coeff (p q : criticalPoints 𝓘(ℝ, E) f) :
    (hX.signedMorseBoundaryCoeffs 𝔬 hf R hsq).coeff p q = hX.signedMorseBoundaryCoeff 𝔬 p q := by
  rfl

/-- **The integral Morse complex with all critical values is the integral Morse complex.** -/
def signedMorseBoundaryCoeffsComplexOnUnivIso :
    (hX.signedMorseBoundaryCoeffs 𝔬 hf R hsq).complexOn univ ≅ hX.signedMorseComplex 𝔬 hf R hsq :=
  (hX.signedMorseBoundaryCoeffs 𝔬 hf R hsq).complexOnUnivIso (hX.signedMorseBoundaryAt 𝔬 hf R)
    (fun _ c q ↦ by
      simp only [signedMorseBoundaryCoeffs_coeff]
      exact signedMorseBoundaryAt_apply hf c q)
    ((signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff hf).2 hsq)

/-- The identification of the integral Morse complex with all critical values with the integral
Morse complex sends a chain to the same chain. -/
@[simp]
theorem signedMorseBoundaryCoeffsComplexOnUnivIso_hom_f_apply (n : ℕ)
    (c : MorseGenerators E f n univ →₀ R) :
    (signedMorseBoundaryCoeffsComplexOnUnivIso hsq).hom.f n c =
      c.mapDomain (MorseGenerators.univEquiv E f n) :=
  MorseBoundaryCoeffs.complexOnUnivIso_hom_f_apply _ _ _ _ n c

/-- The inverse identification of the integral Morse complex with the integral Morse complex with
all critical values sends a chain to the same chain. -/
@[simp]
theorem signedMorseBoundaryCoeffsComplexOnUnivIso_inv_f_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (signedMorseBoundaryCoeffsComplexOnUnivIso hsq).inv.f n c =
      c.mapDomain (MorseGenerators.univEquiv E f n).symm :=
  MorseBoundaryCoeffs.complexOnUnivIso_inv_f_apply _ _ _ _ n c

variable {a : ℤ → ℝ} (ha : Monotone a)

/-- **The abutment of the critical-value spectral sequence of the integral Morse complex** in
degree `-n` is the homology of the integral Morse complex `signedMorseComplex` with coefficients
in `R` in degree `n`. -/
def signedMorseFiltrationAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        ((hX.signedMorseBoundaryCoeffs 𝔬 hf R hsq).monotone_filtration ha))).abutment (-n) ≅
      (hX.signedMorseComplex 𝔬 hf R hsq).homology n :=
  (hX.signedMorseBoundaryCoeffs 𝔬 hf R hsq).filtrationAbutmentIsoOfIso ha
    (signedMorseBoundaryCoeffsComplexOnUnivIso hsq) n

end IsAdaptedPseudoGradient

end TauCeti
