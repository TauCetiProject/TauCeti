/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace.Basic

/-!
# Trace recovery clauses for matrix approximation

`TauCeti.RecoverOn` and `TauCeti.RecoverUniform` express recovery of a positive functional by
normalized matrix traces, on finite test sets and uniformly in the dual norm, respectively.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The recovery clause of amenable and quasidiagonal traces: `tr_k ∘ φ` is `ε`-close to `τ` on
`F`. -/
def RecoverOn (τ : A →P[ℂ] ℂ) (F : Finset A) (ε : ℝ) (k : ℕ)
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε

/-- Characterization of trace recovery on a finite test set. -/
theorem recoverOn_iff {τ : A →P[ℂ] ℂ} {F : Finset A} {ε : ℝ} {k : ℕ}
    {φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ} : RecoverOn τ F ε k φ ↔
      ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε :=
  Iff.rfl

/-- The recovery clause of uniform amenable traces: `tr_k ∘ φ` is `ε`-close to `τ` in the norm of
the dual. -/
def RecoverUniform (τ : A →P[ℂ] ℂ) (_F : Finset A) (ε : ℝ) (k : ℕ)
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε * ‖a‖

/-- Characterization of trace recovery in the norm of the dual. -/
theorem recoverUniform_iff {τ : A →P[ℂ] ℂ} {F : Finset A} {ε : ℝ} {k : ℕ}
    {φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ} : RecoverUniform τ F ε k φ ↔
      ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε * ‖a‖ :=
  Iff.rfl

end TauCeti
