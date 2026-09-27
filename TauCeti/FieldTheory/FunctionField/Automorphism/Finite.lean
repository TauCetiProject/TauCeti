/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Automorphism.Rigidity
public import Mathlib.Data.Fintype.Perm

/-!
# Finite automorphism groups from invariant places

A finite, automorphism-invariant set of sufficiently many rational places detects every
automorphism of a function field. Restricting the action to this set embeds the full
automorphism group in its symmetric group, and in particular makes it finite. This is the
group-theoretic step in the Weierstrass-point argument for finiteness of the automorphism
group in genus at least two. The finite invariant set is an explicit input; the result
applies to Weierstrass points once their invariance and cardinality are established.

## References

* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser,
  2006, Chapter 9.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Restricting the action on places to an invariant finite set gives an action by
permutations of that set. -/
noncomputable def placePermHomOfInvariant {S : Finset (Place k F)}
    (hS : ∀ (σ : F ≃ₐ[k] F) (P : Place k F), P ∈ S → σ • P ∈ S) :
    (F ≃ₐ[k] F) →* Equiv.Perm S where
  toFun σ := {
    toFun P := ⟨σ • P, hS σ P.1 P.2⟩
    invFun P := ⟨σ⁻¹ • P, hS σ⁻¹ P.1 P.2⟩
    left_inv P := by
      apply Subtype.ext
      exact inv_smul_smul σ P.1
    right_inv P := by
      apply Subtype.ext
      exact smul_inv_smul σ P.1 }
  map_one' := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    simp
  map_mul' σ τ := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    simp [mul_smul]

/-- Evaluating the restricted permutation recovers the action on places. -/
@[simp] theorem placePermHomOfInvariant_apply {S : Finset (Place k F)}
    (hS : ∀ (σ : F ≃ₐ[k] F) (P : Place k F), P ∈ S → σ • P ∈ S)
    (σ : F ≃ₐ[k] F) (P : S) :
    ((placePermHomOfInvariant hS σ) P).1 = σ • P.1 := (rfl)

/-- The restricted action is faithful when the invariant set contains at least `2g + 3`
rational places. -/
theorem placePermHomOfInvariant_injective (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (S : Finset (Place k F))
    (hS : ∀ (σ : F ≃ₐ[k] F) (P : Place k F), P ∈ S → σ • P ∈ S)
    (hrat : ∀ P ∈ S, P.degree = 1)
    (hcard : 2 * genus k F + 3 ≤ S.card) :
    Function.Injective (placePermHomOfInvariant hS) := by
  intro σ τ heq
  apply eq_of_forall_smul_eq_of_two_mul_genus_add_three_le_card hF hex
    (S := S) (hcard := hcard)
  intro P hP
  refine ⟨hrat P hP, ?_⟩
  have h := congrArg (fun e : Equiv.Perm S ↦ (e ⟨P, hP⟩).1) heq
  simpa only [placePermHomOfInvariant_apply] using h

/-- An invariant set of at least `2g + 3` rational places forces the full automorphism
group to be finite. -/
theorem finite_algEquiv_of_invariant_rational_places (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (S : Finset (Place k F))
    (hS : ∀ (σ : F ≃ₐ[k] F) (P : Place k F), P ∈ S → σ • P ∈ S)
    (hrat : ∀ P ∈ S, P.degree = 1)
    (hcard : 2 * genus k F + 3 ≤ S.card) :
    Finite (F ≃ₐ[k] F) :=
  Finite.of_injective (placePermHomOfInvariant hS)
    (placePermHomOfInvariant_injective hF hex S hS hrat hcard)

/-- The finite invariant set also bounds the automorphism group's order by the order of
its symmetric group. -/
theorem card_algEquiv_le_factorial_of_invariant_rational_places (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (S : Finset (Place k F))
    (hS : ∀ (σ : F ≃ₐ[k] F) (P : Place k F), P ∈ S → σ • P ∈ S)
    (hrat : ∀ P ∈ S, P.degree = 1)
    (hcard : 2 * genus k F + 3 ≤ S.card) :
    Nat.card (F ≃ₐ[k] F) ≤ S.card.factorial := by
  have hle := Nat.card_le_card_of_injective (placePermHomOfInvariant hS)
    (placePermHomOfInvariant_injective hF hex S hS hrat hcard)
  simpa only [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe] using hle

end TauCeti
