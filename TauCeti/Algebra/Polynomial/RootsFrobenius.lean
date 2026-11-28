/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Roots of a polynomial under Frobenius endomorphisms

If a ring endomorphism `σ : L →+* L` is compatible with an endomorphism `φ : K →+* K` of a field
`K` over `L` in which `P : L[X]` splits, then the multiset of roots of `P.map σ` in `K` is the
image under `φ` of the multiset of roots of `P` in `K`.

Specialising `φ` to an iterate of the Frobenius endomorphism yields the root multiset of `P.map σ`
when `σ` is the `p ^ i`-th power map in exponential characteristic `p`, and in particular when `σ`
is the `|k| ^ i`-th power map over a finite field `k`.

## Main results

* `Polynomial.aroots_map_eq_map_of_splits`: if `φ ∘ algebraMap L K = algebraMap L K ∘ σ` and
  `P.map (algebraMap L K)` splits in `K`, then `(P.map σ).aroots K = (P.aroots K).map φ`.
* `Polynomial.aroots_map_frobenius_pow`: if `K` has exponential characteristic `p`,
  `σ y = y ^ p ^ i` for all `y : L`, and `P.map (algebraMap L K)` splits in `K`, then the roots of
  `P.map σ` in `K` are the `p ^ i`-th powers of the roots of `P`.
* `TauCeti.FiniteField.aroots_map_pow_card_pow`: for a finite field `k`, if `σ y = y ^ |k| ^ i`
  for all `y : L` and `P.map (algebraMap L K)` splits in `K`, then the roots of `P.map σ` in `K`
  are the `|k| ^ i`-th powers of the roots of `P`.

## Provenance

Adapted from grh-lean
(https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/LocalGL/Green/TauFunctions.lean` (`New.aroots_map_frobenius_pow`).
-/

public section

open Polynomial

namespace Polynomial

/-- If `φ : K →+* K` extends `σ : L →+* L` along `algebraMap L K` and `P` splits in `K`, then the
roots of `P.map σ` in `K` are the images under `φ` of the roots of `P` in `K`. -/
theorem aroots_map_eq_map_of_splits {L K : Type*} [CommRing L] [Field K] [Algebra L K]
    {σ : L →+* L} {φ : K →+* K} (hcomm : φ.comp (algebraMap L K) = (algebraMap L K).comp σ)
    {P : L[X]} (hP : (P.map (algebraMap L K)).Splits) :
    (P.map σ).aroots K = (P.aroots K).map φ := by
  have hmap : (P.map σ).map (algebraMap L K) = (P.map (algebraMap L K)).map φ := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomm]
  rw [aroots_def, aroots_def, hmap, hP.roots_map]

/-- If `K` has exponential characteristic `p`, `σ : L →+* L` is the `p ^ i`-th power map, and `P`
splits in `K`, then the roots of `P.map σ` in `K` are the `p ^ i`-th powers of the roots of `P`. -/
theorem aroots_map_frobenius_pow {L K : Type*} [CommRing L] [Field K] [Algebra L K] (p : ℕ)
    [ExpChar K p] {i : ℕ} {σ : L →+* L} (hσ : ∀ y : L, σ y = y ^ p ^ i) {P : L[X]}
    (hP : (P.map (algebraMap L K)).Splits) :
    (P.map σ).aroots K = (P.aroots K).map fun z : K ↦ z ^ p ^ i := by
  have hcomm : (iterateFrobenius K p i).comp (algebraMap L K) = (algebraMap L K).comp σ := by
    ext y
    simp [hσ, iterateFrobenius_def]
  rw [aroots_map_eq_map_of_splits hcomm hP]
  exact Multiset.map_congr rfl fun z _ ↦ iterateFrobenius_def p i z

end Polynomial

namespace TauCeti.FiniteField

/-- If `k` is a finite field, `σ : L →+* L` is the `|k| ^ i`-th power map, and `P : L[X]` splits
in `K`, then the roots of `P.map σ` in `K` are the `|k| ^ i`-th powers of the roots of `P`. -/
theorem aroots_map_pow_card_pow {k L K : Type*} [Field k] [Finite k] [CommRing L] [Field K]
    [Algebra k K] [Algebra L K] {i : ℕ} {σ : L →+* L}
    (hσ : ∀ y : L, σ y = y ^ Nat.card k ^ i) {P : L[X]} (hP : (P.map (algebraMap L K)).Splits) :
    (P.map σ).aroots K = (P.aroots K).map fun z : K ↦ z ^ Nat.card k ^ i := by
  let _ : Fintype k := Fintype.ofFinite k
  have hcomm : ((_root_.FiniteField.frobeniusAlgHom k K ^ i).toRingHom).comp (algebraMap L K) =
      (algebraMap L K).comp σ := by
    ext y
    simp [hσ, _root_.FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [Polynomial.aroots_map_eq_map_of_splits hcomm hP]
  exact Multiset.map_congr rfl fun z _ ↦ by
    simp [_root_.FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]

end TauCeti.FiniteField
