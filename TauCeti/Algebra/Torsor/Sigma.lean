/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Abel

/-!
# Equivariant functions on finite unions of torsors

Let `P i` be torsors under a group `H`, indexed by `i : ι`. A function `d` on the union
`Σ i, P i` that is constant on each orbit has at most one value per orbit, so it has finitely
many values when `ι` is finite. The main source of such functions is the residue of an
equivariant degree: if translating by `h` shifts `d` by `δ h` for a homomorphism `δ : H →+ D`,
then `d` modulo the range of `δ` is constant on orbits.

The opposite extreme is an injective shift homomorphism `δ`. Then an equivariant degree is
injective on each torsor, so each orbit meets each degree at most once, and a finite union of
torsors has only finitely many elements of any given degree. Moreover, if `f` is a second
equivariant function, shifted by a homomorphism `N : H →+ A`, then the differences
`f₀ p₀ - f₁ p₁` over all pairs with a fixed degree relation `d₀ p₀ = d₁ p₁ + ε` take only
finitely many values: translating both elements by the same `h` changes neither the degree
difference nor the difference of values, and up to such a translation there are only finitely
many pairs. The same holds for triples with `d₀ p₀ = d₁ p₁ + d₂ p₂ + ε` and the differences
`f₀ p₀ - (f₁ p₁ + f₂ p₂)`.

For the capped generators of a Hamiltonian Floer complex on a spherically monotone target, `d`
is the grading and `f` is the action, so this bounds the action change of all configurations of a
fixed index.

## Main results

* `TauCeti.AddTorsor.finite_range_sigma_of_forall_vadd_eq`: an orbit-invariant function on a
  finite union of torsors has finite range.
* `TauCeti.AddTorsor.injective_of_forall_vadd_eq_add`: a degree shifted by an injective
  homomorphism is injective on a torsor.
* `TauCeti.AddTorsor.finite_setOf_sigma_eq`: on a finite union of torsors, such a degree has
  finitely many elements of each degree.
* `TauCeti.AddTorsor.finite_image_sub_setOf_eq_add`,
  `TauCeti.AddTorsor.finite_image_sub_add_setOf_eq_add_add`: equivariant differences over pairs
  and triples with a fixed degree relation take finitely many values.

-/

public section

namespace TauCeti.AddTorsor

open Function Set

variable {H ι D : Type*} [AddGroup H] {P : ι → Type*} [∀ i, AddTorsor H (P i)]

/-- A function that is constant on each orbit of a finite union of torsors has finitely many
values. -/
theorem finite_range_sigma_of_forall_vadd_eq [Finite ι] {d : (Σ i, P i) → D}
    (hd : ∀ i (h : H) (p : P i), d ⟨i, h +ᵥ p⟩ = d ⟨i, p⟩) : (range d).Finite := by
  let r := fun i => Classical.arbitrary (P i)
  refine (finite_range fun i => d ⟨i, r i⟩).subset ?_
  rintro _ ⟨⟨i, p⟩, rfl⟩
  exact ⟨i, by rw [← vsub_vadd p (r i), hd]⟩

section Injective

variable [AddGroup D] {δ : H →+ D}

/-- If translating by `h` shifts a degree `d` on a torsor by `δ h` for an injective homomorphism
`δ`, then `d` is injective: two elements of the same degree coincide. -/
theorem injective_of_forall_vadd_eq_add {Q : Type*} [AddTorsor H Q] {d : Q → D}
    (hd : ∀ (h : H) (q : Q), d (h +ᵥ q) = δ h + d q) (hδ : Injective δ) : Injective d := by
  intro p q hpq
  have h := hd (p -ᵥ q) q
  rw [vsub_vadd, hpq, right_eq_add, ← map_zero δ] at h
  exact vsub_eq_zero_iff_eq.1 (hδ h)

/-- If translating by `h` shifts a degree `d` on a finite union of torsors by `δ h` for an
injective homomorphism `δ`, then only finitely many elements have any given degree: at most one
in each orbit. -/
theorem finite_setOf_sigma_eq [Finite ι] {d : (Σ i, P i) → D}
    (hd : ∀ i (h : H) (p : P i), d ⟨i, h +ᵥ p⟩ = δ h + d ⟨i, p⟩) (hδ : Injective δ) (k : D) :
    {p | d p = k}.Finite := by
  refine Finite.of_finite_image (f := Sigma.fst) (toFinite _) ?_
  rintro ⟨i, x⟩ hx ⟨j, y⟩ hy (rfl : i = j)
  exact congrArg (Sigma.mk i)
    (injective_of_forall_vadd_eq_add (d := fun x => d ⟨i, x⟩) (hd i) hδ (hx.trans hy.symm))

end Injective

section Differences

variable {A : Type*} [AddCommGroup A] {N : H →+ A}
  {ι₁ ι₀ : Type*} [Finite ι₁] [Finite ι₀] {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  {f₁ : (Σ i, P₁ i) → A} {f₀ : (Σ k, P₀ k) → A}

section Pair

variable [AddGroup D] {δ : H →+ D} {d₁ : (Σ i, P₁ i) → D} {d₀ : (Σ k, P₀ k) → D}

/-- Let `f` and `d` be functions on two finite unions of torsors, shifted by translations through
homomorphisms `N` and `δ`, with `δ` injective. Then the differences `f₀ p₀ - f₁ p₁` over all
pairs with `d₀ p₀ = d₁ p₁ + ε` take only finitely many values. -/
theorem finite_image_sub_setOf_eq_add
    (hf₁ : ∀ i (h : H) (p : P₁ i), f₁ ⟨i, h +ᵥ p⟩ = N h + f₁ ⟨i, p⟩)
    (hf₀ : ∀ k (h : H) (p : P₀ k), f₀ ⟨k, h +ᵥ p⟩ = N h + f₀ ⟨k, p⟩)
    (hd₁ : ∀ i (h : H) (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
    (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)
    (hδ : Injective δ) (ε : D) :
    ((fun q : (Σ i, P₁ i) × (Σ k, P₀ k) => f₀ q.2 - f₁ q.1) ''
      {q | d₀ q.2 = d₁ q.1 + ε}).Finite := by
  let r := fun i => Classical.arbitrary (P₁ i)
  -- Up to translating both elements by the same `h`, the first element is a chosen lift.
  refine (finite_iUnion fun i => (finite_setOf_sigma_eq hd₀ hδ (d₁ ⟨i, r i⟩ + ε)).image
    fun p₀ => f₀ p₀ - f₁ ⟨i, r i⟩).subset ?_
  rintro _ ⟨⟨⟨i, x₁⟩, ⟨k, x₀⟩⟩, hq, rfl⟩
  set h := x₁ -ᵥ r i
  have e₁ : x₁ = h +ᵥ r i := (vsub_vadd x₁ (r i)).symm
  have e₀ : x₀ = h +ᵥ (-h +ᵥ x₀) := (vadd_neg_vadd h x₀).symm
  refine mem_iUnion.2 ⟨i, ⟨k, -h +ᵥ x₀⟩, ?_, ?_⟩
  · apply add_left_cancel (a := δ h)
    simp only [mem_ofPred_eq] at hq ⊢
    rw [← hd₀, ← e₀, hq, e₁, hd₁, add_assoc]
  · dsimp only
    rw [hf₀, e₁, hf₁, map_neg]
    abel

end Pair

section Triple

variable [AddCommGroup D] {δ : H →+ D} {ι₂ : Type*} [Finite ι₂] {P₂ : ι₂ → Type*}
  [∀ j, AddTorsor H (P₂ j)] {f₂ : (Σ j, P₂ j) → A}
  {d₁ : (Σ i, P₁ i) → D} {d₂ : (Σ j, P₂ j) → D} {d₀ : (Σ k, P₀ k) → D}

/-- Let `f` and `d` be functions on three finite unions of torsors, shifted by translations
through homomorphisms `N` and `δ`, with `δ` injective and degrees in a commutative group. Then the
differences `f₀ p₀ - (f₁ p₁ + f₂ p₂)` over all triples with `d₀ p₀ = d₁ p₁ + d₂ p₂ + ε` take
only finitely many values. -/
theorem finite_image_sub_add_setOf_eq_add_add
    (hf₁ : ∀ i (h : H) (p : P₁ i), f₁ ⟨i, h +ᵥ p⟩ = N h + f₁ ⟨i, p⟩)
    (hf₂ : ∀ j (h : H) (p : P₂ j), f₂ ⟨j, h +ᵥ p⟩ = N h + f₂ ⟨j, p⟩)
    (hf₀ : ∀ k (h : H) (p : P₀ k), f₀ ⟨k, h +ᵥ p⟩ = N h + f₀ ⟨k, p⟩)
    (hd₁ : ∀ i (h : H) (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
    (hd₂ : ∀ j (h : H) (p : P₂ j), d₂ ⟨j, h +ᵥ p⟩ = δ h + d₂ ⟨j, p⟩)
    (hd₀ : ∀ k (h : H) (p : P₀ k), d₀ ⟨k, h +ᵥ p⟩ = δ h + d₀ ⟨k, p⟩)
    (hδ : Injective δ) (ε : D) :
    ((fun q : ((Σ i, P₁ i) × (Σ j, P₂ j)) × (Σ k, P₀ k) =>
        f₀ q.2 - (f₁ q.1.1 + f₂ q.1.2)) ''
      {q | d₀ q.2 = d₁ q.1.1 + d₂ q.1.2 + ε}).Finite := by
  let r₁ := fun i => Classical.arbitrary (P₁ i)
  let r₂ := fun j => Classical.arbitrary (P₂ j)
  -- Up to translating the output by the sum of the two input translations, both inputs are
  -- chosen lifts.
  refine (finite_iUnion fun ij : ι₁ × ι₂ =>
    (finite_setOf_sigma_eq hd₀ hδ (d₁ ⟨ij.1, r₁ ij.1⟩ + d₂ ⟨ij.2, r₂ ij.2⟩ + ε)).image
      fun p₀ => f₀ p₀ - (f₁ ⟨ij.1, r₁ ij.1⟩ + f₂ ⟨ij.2, r₂ ij.2⟩)).subset ?_
  rintro _ ⟨⟨⟨⟨i, x₁⟩, ⟨j, x₂⟩⟩, ⟨k, x₀⟩⟩, hq, rfl⟩
  set h₁ := x₁ -ᵥ r₁ i
  set h₂ := x₂ -ᵥ r₂ j
  have e₁ : x₁ = h₁ +ᵥ r₁ i := (vsub_vadd x₁ (r₁ i)).symm
  have e₂ : x₂ = h₂ +ᵥ r₂ j := (vsub_vadd x₂ (r₂ j)).symm
  have e₀ : x₀ = (h₁ + h₂) +ᵥ (-(h₁ + h₂) +ᵥ x₀) := (vadd_neg_vadd (h₁ + h₂) x₀).symm
  refine mem_iUnion.2 ⟨(i, j), ⟨k, -(h₁ + h₂) +ᵥ x₀⟩, ?_, ?_⟩
  · apply add_left_cancel (a := δ (h₁ + h₂))
    simp only [mem_ofPred_eq] at hq ⊢
    rw [← hd₀, ← e₀, hq, e₁, e₂, hd₁, hd₂, map_add]
    abel
  · dsimp only
    rw [hf₀, e₁, e₂, hf₁, hf₂, map_neg, map_add]
    abel

end Triple

end Differences

end TauCeti.AddTorsor
