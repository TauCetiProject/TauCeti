/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Basic.Denumerable

/-!
# Finite and extended cardinalities

Mathlib's `Nat.card_pi` computes the cardinality of a product `∀ i, X i` over a finite index type.
This file allows an arbitrary index type, provided that all factors outside a finite set `s` have
exactly one element: the product then has the cardinality of its factors over `s`. Such products
arise as restricted-product-like objects, for instance a cohomology group of a product of modules
in which only finitely many factors contribute.

The file also compares the ranges of two maps `f` and `f'` with `e' ∘ f = f' ∘ e`, where `e` is
surjective and `e'` is injective on the range of `f`: `e'` maps the range of `f` bijectively onto
the range of `f'`.
For instance, two linear maps intertwined by linear equivalences on the source and on the target
have ranges of the same cardinality; this is a counting step of exact-sequence arguments.

For countable types, equality of extended natural cardinalities also gives an equivalence,
including when both types are infinite.

## Main results

* `Nat.card_pi_eq_prod_of_card_eq_one`: `Nat.card (∀ i, X i) = ∏ i ∈ s, Nat.card (X i)` when every
  factor outside `s` has cardinality one.
* `Nat.card_sigma_eq_finsum`: `Nat.card (Σ i, β i) = ∑ᶠ i, Nat.card (β i)` for finite fibres, where
  both sides are `0` if infinitely many fibres are nonempty.
* `Nat.card_sigma_of_forall_card_eq`: `Nat.card (Sigma β) = d * Nat.card α` when every fibre has
  `Nat.card` equal to `d`, for arbitrary (possibly infinite) types, where `Nat.card` of an infinite
  type is `0`.
* `Nat.card_range_eq_card_range_of_comp_eq`: `Nat.card (Set.range f) = Nat.card (Set.range f')`
  when `e' ∘ f = f' ∘ e` with `e` surjective and `e'` injective on the range of `f`.
-/

public section

namespace Nat

/-- The cardinality of a product over an arbitrary index type is the product of the
cardinalities of the factors over a finite set `s`, when every factor outside `s` has exactly one
element. -/
theorem card_pi_eq_prod_of_card_eq_one {ι : Type*} {X : ι → Type*} (s : Finset ι)
    (hX : ∀ i ∉ s, Nat.card (X i) = 1) :
    Nat.card (∀ i, X i) = ∏ i ∈ s, Nat.card (X i) := by
  classical
  have h (i : {i // i ∉ s}) := Nat.card_eq_one_iff_unique.mp (hX i.1 i.2)
  have (i : {i // i ∉ s}) : Subsingleton (X i) := (h i).1
  have (i : {i // i ∉ s}) : Nonempty (X i) := (h i).2
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (· ∈ s) X), Nat.card_prod,
    Nat.card_unique (α := ∀ i : {i // i ∉ s}, X i), mul_one, Nat.card_pi]
  exact Finset.prod_coe_sort s fun i ↦ Nat.card (X i)

/-- The cardinality of a sigma type of finite fibres is the finite sum of the fibre cardinalities:
if infinitely many fibres are nonempty, both sides are `0`. -/
theorem card_sigma_eq_finsum {ι : Type*} (β : ι → Type*) [∀ i, Finite (β i)] :
    Nat.card (Σ i, β i) = ∑ᶠ i, Nat.card (β i) := by
  set s := Function.support fun i ↦ Nat.card (β i)
  have e : (Σ i : s, β i) ≃ Σ i, β i := Equiv.sigmaSubtypeEquivOfSubset β (· ∈ s)
    fun i x ↦ have : Nonempty (β i) := ⟨x⟩; Nat.card_pos.ne'
  rw [← Nat.card_congr e]
  by_cases hs : s.Finite
  · have := hs.fintype
    rw [Nat.card_sigma, ← finsum_mem_support, ← finsum_set_coe_eq_finsum_mem,
      finsum_eq_sum_of_fintype]
  · have : Infinite s := Set.infinite_coe_iff.mpr hs
    have (i : s) : Nonempty (β i) := (Nat.card_ne_zero.mp i.2).1
    rw [Nat.card_eq_zero_of_infinite, finsum_of_infinite_support hs]

/-- **A sigma type with constant fibre cardinality.** If every fibre `β a` has `Nat.card` equal to
`d`, then `Nat.card (Sigma β) = d * Nat.card α`. This holds for arbitrary types, with `Nat.card` of
an infinite type equal to `0`: an infinite fibre forces `d = 0`, and with `d = 0` the fibres are
empty or infinite, while with `d > 0` an infinite base makes the sigma type infinite. -/
theorem card_sigma_of_forall_card_eq {α : Type*} {β : α → Type*} {d : ℕ}
    (h : ∀ a, Nat.card (β a) = d) : Nat.card (Sigma β) = d * Nat.card α := by
  by_cases hfib : ∀ a, Finite (β a)
  · by_cases hα : Finite α
    · have := Fintype.ofFinite α
      rw [Nat.card_sigma]
      simp [h, mul_comm]
    · have := not_finite_iff_infinite.1 hα
      rw [Nat.card_eq_zero_of_infinite (α := α), mul_zero]
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · have hempty (a : α) : IsEmpty (β a) :=
          (Nat.card_eq_zero.1 (h a)).resolve_right (not_infinite_iff_finite.2 (hfib a))
        have : IsEmpty (Sigma β) := ⟨fun c ↦ (hempty c.1).false c.2⟩
        exact Nat.card_of_isEmpty
      · have hne (a : α) : Nonempty (β a) := (Nat.card_pos_iff.1 (h a ▸ hpos)).1
        have : Infinite (Sigma β) :=
          Infinite.of_surjective Sigma.fst fun a ↦ ⟨⟨a, (hne a).some⟩, rfl⟩
        exact Nat.card_eq_zero_of_infinite
  · obtain ⟨a, ha⟩ := not_forall.1 hfib
    have := not_finite_iff_infinite.1 ha
    have hd0 : d = 0 := (h a).symm.trans Nat.card_eq_zero_of_infinite
    have : Infinite (Sigma β) := Infinite.of_injective (Sigma.mk a) sigma_mk_injective
    rw [hd0, zero_mul]
    exact Nat.card_eq_zero_of_infinite

/-- Two maps `f` and `f'` with `e' ∘ f = f' ∘ e`, where `e` is surjective and `e'` is injective
on the range of `f`, have ranges of the same cardinality. -/
theorem card_range_eq_card_range_of_comp_eq {α β γ δ : Type*} {f : α → β} {f' : γ → δ}
    {e : α → γ} {e' : β → δ} (he : Function.Surjective e) (he' : Set.InjOn e' (Set.range f))
    (h : e' ∘ f = f' ∘ e) :
    Nat.card (Set.range f) = Nat.card (Set.range f') := by
  rw [← he.range_comp f', ← h, Set.range_comp, Nat.card_image_of_injOn he']

end Nat

namespace TauCeti

/-- Countable types with equal extended natural cardinalities admit an equivalence. -/
theorem nonempty_equiv_of_enatCard_eq {α β : Type*} [Countable α] [Countable β]
    (h : ENat.card α = ENat.card β) : Nonempty (α ≃ β) := by
  classical
  cases finite_or_infinite α with
  | inl hfin =>
    have := hfin
    have : Finite β := ENat.card_lt_top.1 (by rw [← h]; exact ENat.card_lt_top.2 hfin)
    let := Fintype.ofFinite α
    let := Fintype.ofFinite β
    exact Fintype.card_eq.1 (by simpa [ENat.card_eq_coe_fintype_card] using h)
  | inr hinf =>
    have := hinf
    have : Infinite β := ENat.card_eq_top.1 (by rw [← h]; simp)
    exact nonempty_equiv_of_countable

end TauCeti
