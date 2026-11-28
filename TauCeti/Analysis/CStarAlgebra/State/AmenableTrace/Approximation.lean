/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace.Basic

/-!
# Trace recovery clauses for matrix approximation

`PositiveContinuousLinearMap.RecoverOn` and `PositiveContinuousLinearMap.RecoverUniform` express
recovery of a positive functional by normalized matrix traces, on finite test sets and uniformly
in the dual norm, respectively.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

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

/-- Recovery on a larger finite set at a smaller error gives recovery on the requested set. -/
theorem RecoverOn.mono {τ : A →P[ℂ] ℂ} {F F' : Finset A} {ε ε' : ℝ} {k : ℕ}
    {φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ} (h : τ.RecoverOn F' ε' k φ)
    (hF : F ⊆ F') (hε : ε' ≤ ε) : τ.RecoverOn F ε k φ :=
  recoverOn_iff.2 fun a ha => (recoverOn_iff.1 h a (hF ha)).trans_le hε

/-- Finite-set trace recovery passes to composites with completely positive maps. -/
theorem RecoverOn.comp {B H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [FunLike H A B] [LinearMapClass H ℂ A B]
    [CompletelyPositiveMapClass H A B] [DecidableEq B] {σ : B →P[ℂ] ℂ}
    (f : H) {S : Finset A} {ε : ℝ} {k : ℕ}
    {φ : B →CP CStarMatrix (Fin k) (Fin k) ℂ} (h : σ.RecoverOn (S.image f) ε k φ) :
    (σ.comp (.ofClass f)).RecoverOn S ε k (φ.comp (f : A →CP B)) := by
  rw [recoverOn_iff] at h ⊢
  intro a ha
  simpa using h (f a) (Finset.mem_image_of_mem f ha)

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

end PositiveContinuousLinearMap
