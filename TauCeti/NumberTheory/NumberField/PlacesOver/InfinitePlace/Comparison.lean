/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Inertia
public import TauCeti.NumberTheory.NumberField.PlacesOver.Place

/-!
# Decomposition and inertia groups at infinite places

Let `L / K` be a field extension with `L` of characteristic zero, of any degree. An infinite place
of `L` in the sense of `AbsoluteValue.Place` (an archimedean `ℚ`-normalised absolute value) is the
underlying absolute value of a Mathlib `NumberField.InfinitePlace L`
(`AbsoluteValue.Place.infinitePlaceEquiv`), and the action of `L ≃ₐ[K] L` on places restricts to
Mathlib's action on infinite places (`NumberField.InfinitePlace.toPlace_smul`). This file
transfers Mathlib's stabiliser lemmas
(`Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean`) to the decomposition and
inertia groups of `TauCeti/Analysis/AbsoluteValue/Inertia.lean`, where the inertia group of an
infinite place is its whole decomposition group.

For `v = |φ ·|` with `φ : L →+* ℂ`, an element `σ` of `L ≃ₐ[K] L` lies in the decomposition (and
inertia) group of `v` exactly when `σ = 1` or `φ ∘ σ = conj ∘ φ`
(`NumberField.InfinitePlace.mem_inertia_toPlace_mk_iff`): the nontrivial elements are the complex
conjugations at `v`. If such a `σ` exists, the group is `{1, σ}`. For `L / K` Galois it is trivial
exactly when `v` is unramified over `K`, that is, when `v` is real or its restriction to `K` is
complex, and otherwise it has order two. None of this needs `L / K` to be finite, so it applies to
`L = F^alg` and `K = F` for a number field `F`.

## Main results

* `NumberField.InfinitePlace.stabilizer_toPlace`,
  `NumberField.InfinitePlace.inertia_toPlace`: the decomposition and inertia groups of the place
  of an infinite place `v` are Mathlib's stabiliser of `v`.
* `NumberField.InfinitePlace.mem_inertia_toPlace_mk_iff`,
  `NumberField.ComplexEmbedding.IsConj.coe_inertia_toPlace_mk`: complex conjugations.
* `NumberField.InfinitePlace.inertia_toPlace_eq_bot_iff`,
  `NumberField.InfinitePlace.card_inertia_toPlace`: triviality and order.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. II, §8.
-/

public section

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- **Decomposition groups at infinite places.** The stabiliser of the place underlying an
infinite place `v` is Mathlib's stabiliser of `v`. -/
@[simp]
theorem stabilizer_toPlace (v : InfinitePlace L) :
    MulAction.stabilizer (L ≃ₐ[K] L) v.toPlace = MulAction.stabilizer (L ≃ₐ[K] L) v := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, ← toPlace_smul, toPlace_injective.eq_iff]

/-- **Inertia groups at infinite places.** The inertia group of the place underlying an infinite
place `v` is Mathlib's stabiliser of `v`. -/
theorem inertia_toPlace (v : InfinitePlace L) :
    v.toPlace.val.inertia (L ≃ₐ[K] L) = MulAction.stabilizer (L ≃ₐ[K] L) v := by
  rw [AbsoluteValue.inertia_eq_stabilizer v.not_isNonarchimedean_toPlace,
    ← AbsoluteValue.Place.stabilizer_eq, stabilizer_toPlace]

/-- **Complex conjugations.** For `φ : L →+* ℂ`, an element `σ` of `L ≃ₐ[K] L` lies in the
inertia (equivalently, decomposition) group of the place `|φ ·|` exactly when `σ = 1` or
`φ ∘ σ = conj ∘ φ`. -/
theorem mem_inertia_toPlace_mk_iff (φ : L →+* ℂ) (σ : L ≃ₐ[K] L) :
    σ ∈ (mk φ).toPlace.val.inertia (L ≃ₐ[K] L) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ := by
  rw [inertia_toPlace, mem_stabilizer_mk_iff]

/-- For `L / K` Galois, the inertia group of the place underlying an infinite place `v` is trivial
exactly when `v` is unramified over `K`. -/
theorem inertia_toPlace_eq_bot_iff [IsGalois K L] (v : InfinitePlace L) :
    v.toPlace.val.inertia (L ≃ₐ[K] L) = ⊥ ↔ v.IsUnramified K := by
  rw [inertia_toPlace, isUnramified_iff_stabilizer_eq_bot]

/-- For `L / K` Galois, the inertia group of the place underlying an infinite place `v` has order
`1` if `v` is unramified over `K` and `2` otherwise. -/
theorem card_inertia_toPlace [IsGalois K L] (v : InfinitePlace L) [Decidable (v.IsUnramified K)] :
    Nat.card (v.toPlace.val.inertia (L ≃ₐ[K] L)) = if v.IsUnramified K then 1 else 2 := by
  rw [inertia_toPlace]
  convert card_stabilizer (k := K) (w := v)

end NumberField.InfinitePlace

/-- **Complex conjugation generates the inertia group.** If `φ ∘ σ = conj ∘ φ` for some
`σ : L ≃ₐ[K] L` and `φ : L →+* ℂ`, the inertia (equivalently, decomposition) group of the place
`|φ ·|` is `{1, σ}`. -/
theorem NumberField.ComplexEmbedding.IsConj.coe_inertia_toPlace_mk {K L : Type*} [Field K]
    [Field L] [CharZero L] [Algebra K L] {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} (h : IsConj φ σ) :
    ((InfinitePlace.mk φ).toPlace.val.inertia (L ≃ₐ[K] L) : Set (L ≃ₐ[K] L)) = {1, σ} := by
  rw [InfinitePlace.inertia_toPlace, h.coe_stabilizer_mk]
