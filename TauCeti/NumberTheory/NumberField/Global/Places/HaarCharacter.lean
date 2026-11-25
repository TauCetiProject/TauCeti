/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar.Basic
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Borel
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
import TauCeti.NumberTheory.NumberField.Global.Places.PowerClasses

/-!
# The Haar character at a place of a number field

Let `K` be a number field and `v` a finite place of `K`. The completion `K_v` is a
nonarchimedean local field, and multiplication by a unit `x` of `K_v` scales additive Haar
measure on `K_v` by its Haar character `MeasureTheory.distribHaarChar K_v x`. This file identifies
that character with Mathlib's norm on `K_v`, which sends `x` to `(N v) ^ (-v(x))`: the residue
field of `K_v` has `N v = Ideal.absNorm v` elements, so this norm is the normalized absolute value
of `K_v` as a local field
(`IsDedekindDomain.HeightOneSpectrum.coe_normalizedAbsoluteValue_adicCompletion`).

The local factors of the Haar measures on the finite adeles and on the finite ideles of `K` are
these completions, and this is the form in which their scaling is read off place by place. A
uniformizer of `K_v` has character `(N v)⁻¹`, by `MeasureTheory.distribHaarChar_of_isUniformizer`
and `IsDedekindDomain.HeightOneSpectrum.natCard_residueField_adicCompletion_eq_absNorm`; at a
place of residue degree `f` above `p` this is `p ^ (-f)`, not `p⁻¹`.

At an infinite place `w`, the completion `K_w` is isometric to `ℝ` or `ℂ`, and multiplication by
a unit `x` scales Haar measure by `‖x‖ ^ m_w`, the multiplicity `m_w` being `1` at a real place and
`2` at a complex place.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion`: the Haar character of
  `x ∈ K_vˣ` is `‖x‖₊`.
* `IsDedekindDomain.HeightOneSpectrum.addHaarMeasure_adicCompletionIntegers`: the normalized Haar
  measure of the local field `K_v` gives `𝒪_v` mass `1`.
* `NumberField.InfinitePlace.distribHaarChar_completion`: the Haar character of `x ∈ K_wˣ` is
  `‖x‖₊ ^ m_w`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism).
* The FLT project (`ImperialCollegeLondon/FLT`, Apache 2.0) computes the Haar characters of `ℝ`
  and `ℂ` in `FLT/HaarMeasure/HaarChar/RealComplex.lean` (by Yaël Dillies and Javier
  López-Contreras), and uses them place by place at the infinite places in
  `FLT/HaarMeasure/HaarChar/AdeleRing.lean` (by Kevin Buzzard, Bryan Wang Peng Jun, Salvatore
  Mercuri, Pietro Monticone and Ruben Van de Velde); `distribHaarChar_completion` follows that
  computation, transported along the isometries of `K_w` with `ℝ` or `ℂ`.
-/

public section

open MeasureTheory MeasureTheory.Measure NumberField
open scoped NNReal

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The Haar character at a finite place.** Multiplication by `x ∈ K_vˣ` scales additive Haar
measure on the completion `K_v` of a number field by the norm `‖x‖₊ = (N v) ^ (-v(x))`. -/
theorem distribHaarChar_adicCompletion (x : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) x = ‖(x : v.adicCompletion K)‖₊ := by
  rw [distribHaarChar_eq_normalizedAbsoluteValue]
  ext
  simpa using v.coe_normalizedAbsoluteValue_adicCompletion (x : v.adicCompletion K)

/-- The normalized local Haar measure `μ_v = addHaarMeasure (integerPositiveCompacts K_v)` of the
local field `K_v` gives `𝒪_v` mass `1`. -/
@[simp]
theorem addHaarMeasure_adicCompletionIntegers :
    addHaarMeasure (TauCeti.integerPositiveCompacts (v.adicCompletion K))
      (v.adicCompletionIntegers K) = 1 := by
  have h : ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) =
      (TauCeti.integerPositiveCompacts (v.adicCompletion K) : Set (v.adicCompletion K)) := by
    rw [TauCeti.coe_integerPositiveCompacts, v.integer_eq_adicCompletionIntegers]
    ext x
    exact (ValuationSubring.mem_toSubring _ x).symm
  rw [h]
  exact addHaarMeasure_self

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K]

/-- **The Haar character at an infinite place.** Multiplication by `x ∈ K_wˣ` scales Haar measure
on `K_w` by `‖x‖ ^ m_w`, where `m_w` is `1` at a real place and `2` at a complex place. -/
@[simp]
theorem distribHaarChar_completion (w : InfinitePlace K) (x : w.Completionˣ) :
    distribHaarChar w.Completion x = ‖(x : w.Completion)‖₊ ^ w.mult := by
  by_cases hw : w.IsReal
  · have h := distribHaarChar_map_ringEquiv (Completion.ringEquivRealOfIsReal hw)
      (Completion.isometryEquivRealOfIsReal hw).continuous
      (Completion.isometryEquivRealOfIsReal hw).symm.continuous x
    rw [← h, distribHaarChar_real_eq, Module.finrank_self, pow_one, mult_isReal ⟨w, hw⟩, pow_one]
    ext
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · have hc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have h := distribHaarChar_map_ringEquiv (Completion.ringEquivComplexOfIsComplex hc)
      (Completion.isometryEquivComplexOfIsComplex hc).continuous
      (Completion.isometryEquivComplexOfIsComplex hc).symm.continuous x
    rw [← h, distribHaarChar_complex_eq, Complex.finrank_real_complex, mult_isComplex ⟨w, hc⟩]
    congr 1
    ext
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

end NumberField.InfinitePlace
