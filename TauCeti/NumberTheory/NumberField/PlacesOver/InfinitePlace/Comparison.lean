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

The comparison with Mathlib's stabilisers, the membership criterion, the description `{1, σ}`
and the triviality criterion also hold for an arbitrary infinite place
`w : AbsoluteValue.Place L`, not only one given as `v.toPlace`: `w` is the place of the infinite
place `infinitePlaceEquiv L ⟨w, hw⟩`, and `w x = ‖φ x‖` for an embedding `φ : L →+* ℂ`
(`AbsoluteValue.Place.exists_forall_apply_eq_norm`). The inertia group of `w` is trivial when
`w.under K` is complex, and for `L / K` Galois it is `{1, c}` with `φ ∘ c = conj ∘ φ` when
`w.under K` is real.

## Main results

* `NumberField.InfinitePlace.stabilizer_toPlace`,
  `NumberField.InfinitePlace.inertia_toPlace`: the decomposition and inertia groups of the place
  of an infinite place `v` are Mathlib's stabiliser of `v`.
* `NumberField.InfinitePlace.mem_inertia_toPlace_mk_iff`,
  `NumberField.ComplexEmbedding.IsConj.coe_inertia_toPlace_mk`: complex conjugations.
* `NumberField.InfinitePlace.inertia_toPlace_eq_bot_iff`,
  `NumberField.InfinitePlace.card_inertia_toPlace`: triviality and order.
* `AbsoluteValue.Place.stabilizer_eq_stabilizer_infinitePlaceEquiv`,
  `AbsoluteValue.Place.inertia_eq_stabilizer_infinitePlaceEquiv`: the same comparison for an
  arbitrary infinite place `w`.
* `AbsoluteValue.Place.mem_inertia_iff_of_forall_apply_eq_norm`,
  `AbsoluteValue.Place.coe_inertia_of_isConj`: complex conjugations at `w = |φ ·|`.
* `AbsoluteValue.Place.inertia_eq_bot_iff_isReal_or_isComplex_under`,
  `AbsoluteValue.Place.inertia_eq_bot_of_isComplex_under`,
  `AbsoluteValue.Place.exists_isConj_coe_inertia_eq`: the inertia group of `w` in terms of its
  restriction to `K`.

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

/-! ### Arbitrary infinite places -/

namespace AbsoluteValue.Place

open NumberField

variable {K L : Type*} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- **Decomposition groups at infinite places.** The decomposition group of an infinite place `w`
of `L` in `L ≃ₐ[K] L` is Mathlib's stabiliser of the corresponding infinite place. -/
theorem stabilizer_eq_stabilizer_infinitePlaceEquiv (w : Place L)
    (hw : ¬ IsNonarchimedean w.val) :
    MulAction.stabilizer (L ≃ₐ[K] L) w =
      MulAction.stabilizer (L ≃ₐ[K] L) (infinitePlaceEquiv L ⟨w, hw⟩) := by
  rw [← InfinitePlace.stabilizer_toPlace, toPlace_infinitePlaceEquiv]

/-- **Inertia groups at infinite places.** The inertia group of an infinite place `w` of `L` in
`L ≃ₐ[K] L` is Mathlib's stabiliser of the corresponding infinite place. -/
theorem inertia_eq_stabilizer_infinitePlaceEquiv (w : Place L) (hw : ¬ IsNonarchimedean w.val) :
    w.val.inertia (L ≃ₐ[K] L) =
      MulAction.stabilizer (L ≃ₐ[K] L) (infinitePlaceEquiv L ⟨w, hw⟩) := by
  rw [← InfinitePlace.inertia_toPlace, toPlace_infinitePlaceEquiv]

/-- **Complex conjugations.** If `w x = ‖φ x‖` for all `x`, an element `σ` of `L ≃ₐ[K] L` lies in
the inertia (equivalently, decomposition) group of `w` exactly when `σ = 1` or
`φ ∘ σ = conj ∘ φ`. -/
theorem mem_inertia_iff_of_forall_apply_eq_norm {w : Place L} {φ : L →+* ℂ}
    (hφ : ∀ x, w x = ‖φ x‖) (σ : L ≃ₐ[K] L) :
    σ ∈ w.val.inertia (L ≃ₐ[K] L) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ := by
  rw [eq_toPlace_mk hφ, InfinitePlace.mem_inertia_toPlace_mk_iff]

/-- **Complex conjugation generates the inertia group.** If `w x = ‖φ x‖` for all `x` and
`φ ∘ σ = conj ∘ φ`, the inertia (equivalently, decomposition) group of `w` is `{1, σ}`. -/
theorem coe_inertia_of_isConj {w : Place L} {φ : L →+* ℂ} (hφ : ∀ x, w x = ‖φ x‖)
    {σ : L ≃ₐ[K] L} (h : ComplexEmbedding.IsConj φ σ) :
    (w.val.inertia (L ≃ₐ[K] L) : Set (L ≃ₐ[K] L)) = {1, σ} := by
  rw [eq_toPlace_mk hφ, h.coe_inertia_toPlace_mk]

section under

variable [CharZero K]

/-- **Infinite places above a complex place.** The inertia group of an infinite place of `L` whose
restriction to `K` is complex is trivial. -/
theorem inertia_eq_bot_of_isComplex_under (w : Place L) (hw : ¬ IsNonarchimedean w.val)
    (h : (infinitePlaceEquiv K ⟨w.under K, not_isNonarchimedean_under K hw⟩).IsComplex) :
    w.val.inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [inertia_eq_stabilizer_infinitePlaceEquiv w hw]
  exact InfinitePlace.IsUnramified.stabilizer_eq_bot
    (InfinitePlace.isUnramified_iff.mpr (.inr (by rwa [comap_infinitePlaceEquiv])))

variable [IsGalois K L]

/-- **Unramified infinite places.** For `L / K` Galois, the inertia group of an infinite place `w`
of `L` is trivial exactly when `w` is real or its restriction to `K` is complex. -/
theorem inertia_eq_bot_iff_isReal_or_isComplex_under (w : Place L)
    (hw : ¬ IsNonarchimedean w.val) :
    w.val.inertia (L ≃ₐ[K] L) = ⊥ ↔ (infinitePlaceEquiv L ⟨w, hw⟩).IsReal ∨
      (infinitePlaceEquiv K ⟨w.under K, not_isNonarchimedean_under K hw⟩).IsComplex := by
  rw [inertia_eq_stabilizer_infinitePlaceEquiv, ← InfinitePlace.isUnramified_iff_stabilizer_eq_bot,
    InfinitePlace.isUnramified_iff, comap_infinitePlaceEquiv]

/-- **Infinite places above a real place.** For `L / K` Galois, let `w` be an infinite place of
`L` with `w x = ‖φ x‖` for all `x`, whose restriction to `K` is real. Then the inertia
(equivalently, decomposition) group of `w` is `{1, c}` for some `c` with `φ ∘ c = conj ∘ φ`. -/
theorem exists_isConj_coe_inertia_eq {w : Place L} (hw : ¬ IsNonarchimedean w.val) {φ : L →+* ℂ}
    (hφ : ∀ x, w x = ‖φ x‖)
    (h : (infinitePlaceEquiv K ⟨w.under K, not_isNonarchimedean_under K hw⟩).IsReal) :
    ∃ c : L ≃ₐ[K] L, ComplexEmbedding.IsConj φ c ∧
      (w.val.inertia (L ≃ₐ[K] L) : Set (L ≃ₐ[K] L)) = {1, c} := by
  suffices ∃ c : L ≃ₐ[K] L, ComplexEmbedding.IsConj φ c from
    this.imp fun c hc ↦ ⟨hc, coe_inertia_of_isConj hφ hc⟩
  by_cases hr : (InfinitePlace.mk φ).IsReal
  · exact ⟨1, ComplexEmbedding.isConj_one_iff.mpr (InfinitePlace.isReal_mk_iff.mp hr)⟩
  · refine InfinitePlace.exists_isConj_of_isRamified (InfinitePlace.isRamified_iff.mpr ⟨?_, ?_⟩)
    · exact InfinitePlace.not_isReal_iff_isComplex.mp hr
    · rwa [← infinitePlaceEquiv_eq_mk hw hφ, comap_infinitePlaceEquiv]

end under

end AbsoluteValue.Place
