/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Tautology

/-!
# Valid sequents and valid formulas

A sequent `Γ ⇒ Δ` of first-order formulas, with `Γ` and `Δ` finite sets of formulas whose free
variables are natural numbers, is read as "the conjunction of `Γ` implies the disjunction of
`Δ`". It is *valid* when, in every structure on a carrier in the universe `max u v` of the
language, every assignment of the free variables that makes all of `Γ` true makes some formula of
`Δ` true. An assignment `ℕ → M` exists only when `M` is nonempty, so validity is decided on
nonempty structures, as Mathlib's `FirstOrder.Language.Theory.ModelsBoundedFormula` is. Validity
is the semantic notion against which a sequent calculus is shown sound and complete.

A formula is valid when the sequent with empty antecedent and the formula as its only succedent
formula is valid. Every tautology is valid, and a quantifier-free formula without equations is
valid exactly when it is a tautology: validity of such a formula is a purely propositional
matter. With equations this fails, since `t = t` is valid but not a tautology.

## Main definitions

* `TauCeti.SequentCalculus.Valid`: validity of a sequent.
* `FirstOrder.Language.BoundedFormula.IsValid`: validity of a formula.

## Main results

* `FirstOrder.Language.BoundedFormula.IsTautology.isValid`: a tautology is valid.
* `FirstOrder.Language.BoundedFormula.isValid_iff_isTautology`: a quantifier-free, equality-free
  formula is valid exactly when it is a tautology.

## References

* Samuel R. Buss, *An introduction to proof theory*, in *Handbook of Proof Theory*, Elsevier,
  1998, §2.3 (validity of sequents) and the paragraph after the proof of Theorem 2.5.1.
-/

public section

universe u v

open FirstOrder Language

namespace TauCeti.SequentCalculus

variable {L : Language.{u, v}} {Γ Γ' Δ Δ' : Finset (L.Formula ℕ)}

/-- A sequent `Γ ⇒ Δ` is valid when, in every structure on a carrier in the universe `max u v`,
every assignment of the free variables that makes every formula of `Γ` true makes some formula of
`Δ` true. -/
def Valid (Γ Δ : Finset (L.Formula ℕ)) : Prop :=
  ∀ (M : Type (max u v)) [L.Structure M] (v : ℕ → M), (∀ φ ∈ Γ, φ.Realize v) →
    ∃ ψ ∈ Δ, ψ.Realize v

theorem valid_iff : Valid Γ Δ ↔ ∀ (M : Type (max u v)) [L.Structure M] (v : ℕ → M),
    (∀ φ ∈ Γ, φ.Realize v) → ∃ ψ ∈ Δ, ψ.Realize v :=
  Iff.rfl

/-- Validity is preserved by enlarging the antecedent and the succedent. -/
theorem Valid.mono (h : Valid Γ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : Valid Γ' Δ' :=
  fun M _ v hv =>
    let ⟨ψ, hψ, hψv⟩ := h M v fun φ hφ => hv φ (hΓ hφ)
    ⟨ψ, hΔ hψ, hψv⟩

/-- A sequent whose antecedent and succedent share a formula is valid. -/
theorem valid_of_mem_of_mem {φ : L.Formula ℕ} (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) : Valid Γ Δ :=
  fun _ _ _ hv => ⟨φ, hΔ, hv φ hΓ⟩

/-- A sequent with `⊥` in its antecedent is valid. -/
theorem valid_of_bot_mem (h : (⊥ : L.Formula ℕ) ∈ Γ) : Valid Γ Δ :=
  fun _ _ v hv => (Formula.realize_bot (v := v)).1 (hv ⊥ h) |>.elim

end TauCeti.SequentCalculus

namespace FirstOrder.Language

variable {L : Language.{u, v}}

open TauCeti.SequentCalculus

/-- A formula is valid when the sequent with empty antecedent and the formula as its only
succedent formula is valid: it holds in every structure on a carrier in the universe `max u v`
under every assignment of its free variables. -/
def BoundedFormula.IsValid (φ : L.Formula ℕ) : Prop :=
  Valid ∅ {φ}

theorem BoundedFormula.isValid_iff_valid {φ : L.Formula ℕ} : φ.IsValid ↔ Valid ∅ {φ} :=
  Iff.rfl

/-- A formula is valid exactly when it holds in every structure on a carrier in the universe
`max u v` under every assignment. -/
theorem BoundedFormula.isValid_iff {φ : L.Formula ℕ} :
    φ.IsValid ↔ ∀ (M : Type (max u v)) [L.Structure M] (v : ℕ → M), φ.Realize v := by
  simp [IsValid, valid_iff]

/-- `⊥` is not valid. -/
theorem BoundedFormula.not_isValid_bot : ¬(⊥ : L.Formula ℕ).IsValid := fun h =>
  letI : L.Structure (ULift.{max u v} Unit) := Inhabited.trivialStructure L
  (Formula.realize_bot (v := fun _ => ULift.up ())).1 (isValid_iff.1 h _ _)

/-- A tautology is valid. -/
theorem BoundedFormula.IsTautology.isValid {φ : L.Formula ℕ} (h : φ.IsTautology) :
    φ.IsValid :=
  isValid_iff.2 fun _ _ v => h.realize v default

/-- A quantifier-free formula without equations is valid exactly when it is a tautology. -/
theorem BoundedFormula.isValid_iff_isTautology {φ : L.Formula ℕ} (hφ : φ.IsQF)
    (he : φ.IsEqualityFree) : φ.IsValid ↔ φ.IsTautology := by
  rw [hφ.isTautology_iff_forall_realize.{u, v, v} he, isValid_iff]
  refine forall₂_congr fun M _ => ⟨fun h v xs => ?_, fun h v => h v default⟩
  rw [Subsingleton.elim xs default]
  exact h v

end FirstOrder.Language
