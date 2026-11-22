/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.GlueingSquare
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglySheafy
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc

/-!
# End-to-end checks for simple Laurent glueing squares

* Non-vacuous field check: `ℚ_[p]` at `f = p`, using the canonical `ratLoc` constructor
  `GlueingSquare.of_simpleLaurent_ratLoc`.
* Non-vacuous geometric check: the `1`-variable Tate algebra `ℚ_p⟨X⟩` at its coordinate variable
  `X`, glueing the closed unit disc `Spa(ℚ_p⟨X⟩)` across `{|X| ≤ 1}` and `{|X| ≥ 1}` over the unit
  circle `{|X| = 1}` on canonical `ratLoc` carriers, together with flat module recovery for
  `ℚ_p⟨X⟩ × ℚ_p⟨X⟩`.
-/

public section

namespace TauCeti.Huber.LaurentGlueingSquareChecks

variable (p : ℕ) [Fact p.Prime]

open Classical in
open scoped TauCeti.Huber.Laurent in
/-- **Field check**: `ℚ_[p]` admits a simple Laurent `GlueingSquare` at `f = p` on the canonical
`ratLoc` carriers with all hypotheses discharged unconditionally. -/
example :
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
    let hden₁ := P.hasDenominatorPower_of_isOpen_span ({(p : ℚ_[p]), 1} : Finset ℚ_[p]) 1
      (Localization.Away (1 : ℚ_[p])) (isOpen_span_of_one_mem (by simp))
    let hden₂ := P.hasDenominatorPower_of_isOpen_span ({1} : Finset ℚ_[p]) (p : ℚ_[p])
      (Localization.Away (p : ℚ_[p])) (isOpen_span_of_one_mem (by simp))
    let hden₁₂ := P.hasDenominatorPower_of_isOpen_span ({(p : ℚ_[p]) * p, 1} : Finset ℚ_[p])
      (p : ℚ_[p]) (Localization.Away (p : ℚ_[p])) (isOpen_span_of_one_mem (by simp))
    GlueingSquare ℚ_[p] (ratLoc P {(p : ℚ_[p]), 1} 1 hden₁)
      (ratLoc P {1} (p : ℚ_[p]) hden₂)
      (ratLoc P {(p : ℚ_[p]) * p, 1} (p : ℚ_[p]) hden₁₂) :=
  GlueingSquare.of_simpleLaurent_ratLoc IsStronglySheafy.of_isStronglyNoetherian.isSheafyRing
    (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some (p : ℚ_[p])

open Classical in
open scoped TauCeti.Huber.Laurent in
/-- **Tate algebra and module glueing check**: on the `1`-variable Tate algebra `ℚ_p⟨X⟩`, the simple
Laurent cover by `{|X| ≤ 1}` and `{|X| ≥ 1}` at the coordinate variable `X` forms a `GlueingSquare`
on the canonical `ratLoc` carriers and recovers the rank-`2` free module `ℚ_p⟨X⟩ × ℚ_p⟨X⟩` from
the sections of its induced glueing datum, with all hypotheses discharged unconditionally. -/
example :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
    let X : A := Pair.polydiscVar 1 ℚ_[p] 0
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := A)).some
    let hden₁ := P.hasDenominatorPower_of_isOpen_span ({X, 1} : Finset A) 1
      (Localization.Away (1 : A)) (isOpen_span_of_one_mem (by simp))
    let hden₂ := P.hasDenominatorPower_of_isOpen_span ({1} : Finset A) X
      (Localization.Away X) (isOpen_span_of_one_mem (by simp))
    let hden₁₂ := P.hasDenominatorPower_of_isOpen_span ({X * X, 1} : Finset A) X
      (Localization.Away X) (isOpen_span_of_one_mem (by simp))
    GlueingSquare A (ratLoc P {X, 1} 1 hden₁) (ratLoc P {1} X hden₂)
        (ratLoc P {X * X, 1} X hden₁₂) ∧
      Nonempty ((A × A) ≃ₗ[A]
        (GlueingDatum.ofModule (ratLoc P {X, 1} 1 hden₁) (ratLoc P {1} X hden₂)
          (ratLoc P {X * X, 1} X hden₁₂) A (A × A)).sections A) := by
  let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
  let X : A := Pair.polydiscVar 1 ℚ_[p] 0
  let P := (IsHuberRing.nonempty_pairOfDefinition (A := A)).some
  have hsq := GlueingSquare.of_simpleLaurent_ratLoc
    ((IsStronglySheafy.of_isStronglyNoetherian (A := ℚ_[p])).restrictedMvPowerSeriesCompletion
      1).isSheafyRing
    P X
  exact ⟨hsq, ⟨hsq.equivSectionsOfModule (A × A)⟩⟩

end TauCeti.Huber.LaurentGlueingSquareChecks

end
