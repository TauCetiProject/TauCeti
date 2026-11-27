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
def ApproxBy (d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ)
    (R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop)
    (F : Finset A) (ε : ℝ) : Prop :=
  ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
    (∀ a ∈ F, ∀ b ∈ F, d k (φ (a * b) - φ a * φ b) < ε) ∧ R F ε k φ

/-- Characterization of a matrix approximant by its contraction, defect, and recovery clauses. -/
theorem approxBy_iff {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    {F : Finset A} {ε : ℝ} : ApproxBy d R F ε ↔
      ∃ (k : ℕ) (φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ), (∀ a, ‖φ a‖ ≤ ‖a‖) ∧
        (∀ a ∈ F, ∀ b ∈ F, d k (φ (a * b) - φ a * φ b) < ε) ∧ R F ε k φ :=
  Iff.rfl

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

/-- An approximant for `(F', ε')` is one for every `F ⊆ F'` and `ε' ≤ ε`, as soon as the recovery
clause is antitone in the finite set and monotone in the error. -/
theorem ApproxBy.mono {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {R : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    {F F' : Finset A} {ε ε' : ℝ} (h : ApproxBy d R F' ε')
    (hR : ∀ ⦃F F' : Finset A⦄ ⦃ε ε' : ℝ⦄ ⦃k : ℕ⦄ ⦃φ : A →CP CStarMatrix (Fin k) (Fin k) ℂ⦄,
      F ⊆ F' → ε' ≤ ε → R F' ε' k φ → R F ε k φ)
    (hF : F ⊆ F') (hε : ε' ≤ ε) : ApproxBy d R F ε := by
  obtain ⟨k, φ, hφ, hmul, hrec⟩ := h
  exact ⟨k, φ, hφ, fun a ha b hb => (hmul a (hF ha) b (hF hb)).trans_le hε, hR hF hε hrec⟩

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

/-- Composing an approximant `φ` for `(S.image f, ε)` with a star homomorphism `f : A → B` gives an
approximant for `(S, ε)`, for any measure `d` of the multiplicativity defect, as soon as the
recovery clause passes from `φ` on `S.image f` to `φ ∘ f` on `S`. -/
theorem ApproxBy.comp {B H : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {RA : Finset A → ℝ → ∀ k : ℕ, (A →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    {RB : Finset B → ℝ → ∀ k : ℕ, (B →CP CStarMatrix (Fin k) (Fin k) ℂ) → Prop}
    [FunLike H A B] [NonUnitalAlgHomClass H ℂ A B] [StarHomClass H A B]
    [DecidableEq B] (f : H) {S : Finset A} {ε : ℝ} (h : ApproxBy d RB (S.image f) ε)
    (hR : ∀ ⦃k : ℕ⦄ ⦃φ : B →CP CStarMatrix (Fin k) (Fin k) ℂ⦄,
      RB (S.image f) ε k φ → RA S ε k (φ.comp (f : A →CP B))) : ApproxBy d RA S ε := by
  refine h.transport f le_rfl fun k φ hφ hrec => ⟨k, φ.comp (f : A →CP B),
    fun a => by simpa using (hφ (f a)).trans (NonUnitalStarAlgHom.norm_apply_le f a),
    fun a b => by simp,
    hR hrec⟩

/-- On `M_k` the identity map is an exact approximant: it is a contraction, its multiplicativity
defect is `d k 0`, and it satisfies any recovery clause that holds for it. -/
theorem ApproxBy.id {k : ℕ} {d : ∀ k : ℕ, CStarMatrix (Fin k) (Fin k) ℂ → ℝ}
    {R : Finset (CStarMatrix (Fin k) (Fin k) ℂ) → ℝ →
      ∀ l : ℕ, (CStarMatrix (Fin k) (Fin k) ℂ →CP CStarMatrix (Fin l) (Fin l) ℂ) → Prop}
    {F : Finset (CStarMatrix (Fin k) (Fin k) ℂ)} {ε : ℝ} (hd : d k 0 < ε)
    (hR : R F ε k (CompletelyPositiveMap.id _)) : ApproxBy d R F ε :=
  ⟨k, CompletelyPositiveMap.id _, fun _ => by simp, fun _ _ _ _ => by simpa using hd, hR⟩

end TauCeti
