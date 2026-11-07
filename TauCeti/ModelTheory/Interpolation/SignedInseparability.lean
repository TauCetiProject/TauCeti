/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Polarity
public import TauCeti.ModelTheory.Infinitary.Satisfiability

/-!
# Signed inseparability of infinitary theories

Two theories are signed-inseparable if no sentence in prescribed positive and negative relation
vocabularies, and using only prescribed constants, separates their models. Swapping the theories
swaps the two relation budgets: negating a separator reverses its polarities.

This file proves the propositional decomposition rules needed for a signed paired-inseparability
construction. In particular, a countable disjunction entailed on the left has a disjunct that can
be added without destroying inseparability. This does not assert closure under unions of chains
or compactness. The proof combines putative separators into one countable disjunction, preserving
both polarity budgets and the constant budget exactly. Right-hand rules follow by symmetry.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas* (1965).
* David Marker, *Lectures on Infinitary Model Theory* (2016), Chapter 4.

The countable-choice argument refines the unsigned paired-inseparability argument in
`TauCeti.ModelTheory.Interpolation.Craig`, itself following the interpolation construction of
Cameron Freer's `cameronfreer/infinitary-logic` at checkpoint `518a366`. Here the two signed
relation budgets are independent, the constant type is arbitrary, and no finiteness of the
pair or relationality of the language is needed for propositional decomposition.
-/

public section

universe u v z w

namespace FirstOrder.Language.Theoryω

open BoundedFormulaInf

variable {L : Language.{u, v}} {γ : Type z}
  {Γ Δ Γ' Δ' : L[[γ]].Theoryω}
  {R R' : Bool → Set (Σ n, L[[γ]].Relations n)} {K K' : Set γ}

/-- No sentence with signed relation occurrences in `R` and constants in `K` is entailed by `Γ`
and refuted by `Δ`. The budget `R true` is positive and `R false` is negative. Function symbols
are unrestricted; in a relational base language the expansion has only the added constants. -/
def SignedInseparable (Γ Δ : L[[γ]].Theoryω)
    (R : Bool → Set (Σ n, L[[γ]].Relations n)) (K : Set γ) : Prop :=
  ∀ θ : L[[γ]].Sentenceω, (∀ s, θ.relationsInSigned s ⊆ R s) → θ.constantSupport ⊆ K →
    Γ.Entails θ → ¬ Δ.Entails θ.not

/-- The separator-exclusion characterization of signed inseparability. -/
theorem signedInseparable_iff : SignedInseparable Γ Δ R K ↔
    ∀ θ : L[[γ]].Sentenceω, (∀ s, θ.relationsInSigned s ⊆ R s) → θ.constantSupport ⊆ K →
      Γ.Entails θ → ¬ Δ.Entails θ.not := Iff.rfl

/-- Theories with a common nonempty model small in the entailment universe cannot be separated,
with any budgets. In particular this applies to countable models in any universe. -/
theorem signedInseparable_of_model {M : Type w} [L[[γ]].Structure M] [Nonempty M]
    [Small.{max u v z} M] (hΓ : Γ.Model M) (hΔ : Δ.Model M) : SignedInseparable Γ Δ R K := by
  intro θ _ _ h₁ h₂
  exact SentenceInf.realize_not.1 (h₂.realize_of_small M hΔ) (h₁.realize_of_small M hΓ)

namespace SignedInseparable

/-- Weakening either theory preserves inseparability. -/
theorem mono (h : SignedInseparable Γ Δ R K) (hΓ : Γ' ⊆ Γ) (hΔ : Δ' ⊆ Δ) :
    SignedInseparable Γ' Δ' R K :=
  fun θ hr hk h₁ h₂ => h θ hr hk (h₁.mono hΓ) (h₂.mono hΔ)

/-- Restricting either vocabulary budget or the constant budget preserves inseparability. -/
theorem mono_budget (h : SignedInseparable Γ Δ R K) (hr : ∀ s, R' s ⊆ R s) (hk : K' ⊆ K) :
    SignedInseparable Γ Δ R' K' :=
  fun θ hθ hK => h θ (fun s => (hθ s).trans (hr s)) (hK.trans hk)

/-- Swapping the theories flips the signed vocabulary budget. -/
theorem symm (h : SignedInseparable Γ Δ R K) :
    SignedInseparable Δ Γ (fun s => R (!s)) K := by
  intro θ hr hk hΔ hΓ
  apply h θ.not (fun s => by simpa using hr (!s)) (by simpa using hk) hΓ
  exact entails_iff.2 fun M _ _ hM => by
    simpa only [SentenceInf.realize_not, not_not] using (entails_iff.1 hΔ) M hM

/-- The left theory of an inseparable pair is satisfiable. -/
theorem isSatisfiable_left (h : SignedInseparable Γ Δ R K) : Γ.IsSatisfiable := by
  rw [isSatisfiable_iff_not_entails_bot]
  intro hbot
  exact h ⊥ (by simp) (by simp) hbot (entails_iff.2 fun _ _ _ _ => by
    simp [SentenceInf.realize_not])

/-- The right theory of an inseparable pair is satisfiable. -/
theorem isSatisfiable_right (h : SignedInseparable Γ Δ R K) : Δ.IsSatisfiable :=
  h.symm.isSatisfiable_left

/-- Adding an already entailed sentence to the left preserves inseparability. -/
theorem insert_left_of_entails (h : SignedInseparable Γ Δ R K) {φ : L[[γ]].Sentenceω}
    (hφ : Γ.Entails φ) : SignedInseparable (insert φ Γ) Δ R K :=
  fun θ hr hk hθ => h θ hr hk (hφ.cut hθ)

/-- Adding an already entailed sentence to the right preserves inseparability. -/
theorem insert_right_of_entails (h : SignedInseparable Γ Δ R K) {φ : L[[γ]].Sentenceω}
    (hφ : Δ.Entails φ) : SignedInseparable Γ (insert φ Δ) R K :=
  fun θ hr hk hθ hneg => h θ hr hk hθ (hφ.cut hneg)

/-- If the left theory entails a countable disjunction, some disjunct can be added on the left
without producing a signed separator. The disjuncts themselves need not satisfy the budgets. -/
theorem exists_insert_left (h : SignedInseparable Γ Δ R K) (φs : ℕ → L[[γ]].Sentenceω)
    (hφs : Γ.Entails (.iSup φs)) : ∃ k, SignedInseparable (insert (φs k) Γ) Δ R K := by
  classical
  by_contra! hnone
  simp only [signedInseparable_iff, not_forall, not_not] at hnone
  choose θs hr hk hΓ hΔ using hnone
  apply h (.iSup θs) (fun s => by simpa using Set.iUnion_subset (fun k => hr k s))
    (by simpa using Set.iUnion_subset hk)
  · exact entails_iff.2 fun M _ _ hM => by
      obtain ⟨k, hφ⟩ := SentenceInf.realize_iSup.1 ((entails_iff.1 hφs) M hM)
      exact SentenceInf.realize_iSup.2
        ⟨k, (entails_iff.1 (hΓ k)) M (model_insert_iff.2 ⟨hφ, hM⟩)⟩
  · exact entails_iff.2 fun M _ _ hM => by
      rw [SentenceInf.realize_not, SentenceInf.realize_iSup]
      rintro ⟨k, hθ⟩
      exact SentenceInf.realize_not.1 ((entails_iff.1 (hΔ k)) M hM) hθ

/-- If the right theory entails a countable disjunction, some disjunct can be added on the right
without producing a signed separator. -/
theorem exists_insert_right (h : SignedInseparable Γ Δ R K) (φs : ℕ → L[[γ]].Sentenceω)
    (hφs : Δ.Entails (.iSup φs)) : ∃ k, SignedInseparable Γ (insert (φs k) Δ) R K := by
  obtain ⟨k, hk⟩ := h.symm.exists_insert_left φs hφs
  exact ⟨k, by simpa only [Bool.not_not] using hk.symm⟩

/-- An implication on the left admits either its false antecedent or its true consequent as an
inseparability-preserving extension. -/
theorem imp_left (h : SignedInseparable Γ Δ R K) {φ ψ : L[[γ]].Sentenceω}
    (himp : φ.imp ψ ∈ Γ) :
    SignedInseparable (insert φ.not Γ) Δ R K ∨ SignedInseparable (insert ψ Γ) Δ R K := by
  let χs : ℕ → L[[γ]].Sentenceω := fun k => if k = 0 then φ.not else ψ
  have he : Γ.Entails (.iSup χs) := entails_iff.2 fun M _ _ hM => by
    rcases hM.realize_of_imp_mem himp with hφ | hψ
    · exact SentenceInf.realize_iSup.2 ⟨0, by simpa [χs] using hφ⟩
    · exact SentenceInf.realize_iSup.2 ⟨1, by simpa [χs] using hψ⟩
  obtain ⟨k, hk⟩ := h.exists_insert_left χs he
  by_cases hzero : k = 0
  · exact .inl (by simpa [χs, hzero] using hk)
  · exact .inr (by simpa [χs, hzero] using hk)

/-- Both components of a negated implication can be added on the left. -/
theorem not_imp_left (h : SignedInseparable Γ Δ R K) {φ ψ : L[[γ]].Sentenceω}
    (himp : (φ.imp ψ).not ∈ Γ) :
    SignedInseparable (insert φ Γ) Δ R K ∧ SignedInseparable (insert ψ.not Γ) Δ R K := by
  exact ⟨h.insert_left_of_entails (entails_iff.2 fun _ _ _ hM =>
    (hM.realize_of_not_imp_mem himp).1),
    h.insert_left_of_entails (entails_iff.2 fun _ _ _ hM =>
    (hM.realize_of_not_imp_mem himp).2)⟩

/-- Each conjunct of a conjunction on the left can be added on the left. -/
theorem iInf_left (h : SignedInseparable Γ Δ R K) {φs : ℕ → L[[γ]].Sentenceω}
    (hφs : BoundedFormulaInf.iInf φs ∈ Γ) (k : ℕ) :
    SignedInseparable (insert (φs k) Γ) Δ R K :=
  h.insert_left_of_entails (entails_iff.2 fun _ _ _ hM =>
    SentenceInf.realize_iInf.1 (hM.realize_of_mem hφs) k)

/-- Some negated conjunct of a negated conjunction on the left can be added on the left. -/
theorem not_iInf_left (h : SignedInseparable Γ Δ R K) {φs : ℕ → L[[γ]].Sentenceω}
    (hφs : (BoundedFormulaInf.iInf φs).not ∈ Γ) :
    ∃ k, SignedInseparable (insert (φs k).not Γ) Δ R K :=
  h.exists_insert_left (fun k => (φs k).not) (entails_iff.2 fun _ _ _ hM =>
    SentenceInf.realize_iSup.2 (hM.realize_of_not_iInf_mem hφs))

/-- Some disjunct of a disjunction on the left can be added on the left. -/
theorem iSup_left (h : SignedInseparable Γ Δ R K) {φs : ℕ → L[[γ]].Sentenceω}
    (hφs : BoundedFormulaInf.iSup φs ∈ Γ) :
    ∃ k, SignedInseparable (insert (φs k) Γ) Δ R K :=
  h.exists_insert_left φs (entails_of_mem hφs)

/-- Each negated disjunct of a negated disjunction on the left can be added on the left. -/
theorem not_iSup_left (h : SignedInseparable Γ Δ R K) {φs : ℕ → L[[γ]].Sentenceω}
    (hφs : (BoundedFormulaInf.iSup φs).not ∈ Γ) (k : ℕ) :
    SignedInseparable (insert (φs k).not Γ) Δ R K :=
  h.insert_left_of_entails (entails_iff.2 fun _ _ _ hM => hM.realize_of_not_iSup_mem hφs k)

end SignedInseparable

/-- A theory is inseparable from itself, with any budgets, exactly when it is satisfiable. -/
@[simp]
theorem signedInseparable_self_iff : SignedInseparable Γ Γ R K ↔ Γ.IsSatisfiable := by
  refine ⟨SignedInseparable.isSatisfiable_left, fun h => ?_⟩
  obtain ⟨M, _, _, hM⟩ := isSatisfiable_iff.1 h
  exact signedInseparable_of_model hM hM

end FirstOrder.Language.Theoryω
