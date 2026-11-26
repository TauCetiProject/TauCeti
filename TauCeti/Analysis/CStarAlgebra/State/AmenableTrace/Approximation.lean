/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace

/-!
# Matrix approximation for trace predicates

The amenable, quasidiagonal and uniform amenable trace proofs share a matrix approximation
predicate and transport its witnesses along maps of the test sets.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The approximation property shared by the three trace predicates: completely positive
contractions into `M_k` whose multiplicativity defect, measured by `d`, is `< ε` on `F` and which
satisfy the recovery clause `R F ε`. -/
@[expose] def ApproxBy (d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ)
    (R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop)
    (F : Finset A) (ε : ℝ) : Prop :=
  ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
    (∀ a ∈ F, ∀ b ∈ F, d k (φ (a * b) - φ a * φ b) < ε) ∧ R F ε k φ

/-- The recovery clause of amenable and quasidiagonal traces: `tr_k ∘ φ` is `ε`-close to `τ` on
`F`. -/
@[expose] def RecoverOn (τ : A →P[ℂ] ℂ) (F : Finset A) (ε : ℝ) (k : ℕ)
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ a ∈ F, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ < ε

/-- The recovery clause of uniform amenable traces: `tr_k ∘ φ` is `ε`-close to `τ` in the norm of
the dual. -/
@[expose] def RecoverUniform (τ : A →P[ℂ] ℂ) (_F : Finset A) (ε : ℝ) (k : ℕ)
    (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ a, ‖CStarMatrix.normalizedTrace (φ a) - τ a‖ ≤ ε * ‖a‖

/-- Transport an approximant from the image of a finite test set when the new witness is
contractive, satisfies the new recovery clause, and has no larger defect on corresponding pairs. -/
theorem ApproxBy.transport {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B]
    {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {RA : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    {RB : Finset B → ℝ → ∀ k : ℕ, (B →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    [DecidableEq B] (f : A → B) {S : Finset A} {δ ε : ℝ} (hδε : δ ≤ ε)
    (transfer : ∀ (k : ℕ) (φ : B →CP CStarMatrix (Fin k) (Fin k) ℂ),
      (∀ b, ‖φ b‖ ≤ ‖b‖) → RB (S.image f) δ k φ →
      ∃ (l : ℕ) (ψ : A →CP CStarMatrix (Fin l) (Fin l) ℂ),
        (∀ a, ‖ψ a‖ ≤ ‖a‖) ∧
        (∀ a b, d l (ψ (a * b) - ψ a * ψ b) ≤
          d k (φ (f a * f b) - φ (f a) * φ (f b))) ∧
        RA S ε l ψ)
    (h : ApproxBy d RB (S.image f) δ) : ApproxBy d RA S ε := by
  obtain ⟨k, φ, hφ, hmul, hrec⟩ := h
  obtain ⟨l, ψ, hψ, hdefect, hrec'⟩ := transfer k φ hφ hrec
  refine ⟨l, ψ, hψ, fun a ha b hb => (hdefect a b).trans_lt ?_, hrec'⟩
  exact (hmul _ (Finset.mem_image_of_mem f ha) _ (Finset.mem_image_of_mem f hb)).trans_le hδε

end TauCeti
