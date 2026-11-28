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

* Degenerate field check: `ℚ_[p]` at `f = p`, using `GlueingSquare.of_simpleLaurent_ratLoc`.
* Tate algebra check: `ℚ_p⟨X⟩` at `X`, with flat module recovery for `ℚ_p⟨X⟩ × ℚ_p⟨X⟩`.
-/

public section

namespace TauCeti.Huber.LaurentGlueingSquareChecks

variable (p : ℕ) [Fact p.Prime]

open scoped TauCeti.Huber.Laurent

open Classical in
/-- **Field check**: `ℚ_[p]` admits a simple Laurent `GlueingSquare` at `f = p`. -/
example : let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
    let h (T : Finset ℚ_[p]) (s : ℚ_[p]) (h : (1 : ℚ_[p]) ∈ T) :=
      P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) (isOpen_span_of_one_mem h)
    GlueingSquare ℚ_[p] (ratLoc P _ 1 (h {(p : ℚ_[p]), 1} 1 (by simp)))
      (ratLoc P _ (p : ℚ_[p]) (h {1} (p : ℚ_[p]) (by simp)))
      (ratLoc P _ (p : ℚ_[p]) (h {(p : ℚ_[p]) * p, 1} (p : ℚ_[p]) (by simp))) :=
  GlueingSquare.of_simpleLaurent_ratLoc IsStronglySheafy.of_isStronglyNoetherian.isSheafyRing
    (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some (p : ℚ_[p])

open Classical in
/-- **Tate algebra and module glueing check**: `ℚ_p⟨X⟩` at `X` forms a `GlueingSquare` and
recovers `ℚ_p⟨X⟩ × ℚ_p⟨X⟩`. -/
example :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]; let X : A := Pair.polydiscVar 1 ℚ_[p] 0
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := A)).some
    let h (T : Finset A) (s : A) (h : (1 : A) ∈ T) :=
      P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) (isOpen_span_of_one_mem h)
    let L₁ := ratLoc P _ 1 (h {X, 1} 1 (by simp)); let L₂ := ratLoc P _ X (h {1} X (by simp))
    let L₁₂ := ratLoc P _ X (h {X * X, 1} X (by simp))
    GlueingSquare A L₁ L₂ L₁₂ ∧
      Nonempty ((A × A) ≃ₗ[A] (GlueingDatum.ofModule L₁ L₂ L₁₂ A (A × A)).sections A) := by
  let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]; let X : A := Pair.polydiscVar 1 ℚ_[p] 0
  have hsq := GlueingSquare.of_simpleLaurent_ratLoc
    ((IsStronglySheafy.of_isStronglyNoetherian (A := ℚ_[p])).restrictedMvPowerSeriesCompletion
      1).isSheafyRing (IsHuberRing.nonempty_pairOfDefinition (A := A)).some X
  exact ⟨hsq, ⟨hsq.equivSectionsOfModule (A × A)⟩⟩

end TauCeti.Huber.LaurentGlueingSquareChecks

end
