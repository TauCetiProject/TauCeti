/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.NumberTheory.NumberField.Global.Places.PowerClasses

/-!
# The Haar character at a finite place of a number field

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

## Main results

* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion`: the Haar character of
  `x ∈ K_vˣ` is `‖x‖₊`.
-/

public section

open MeasureTheory NumberField
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

end IsDedekindDomain.HeightOneSpectrum
