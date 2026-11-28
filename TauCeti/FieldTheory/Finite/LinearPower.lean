/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Additive power maps over finite fields

Let `F` be a finite field and `k` an separably closed extension of `F`. If the power map
`a ↦ a ^ i` on `k` is `F`-linear, then `i` is a power of `Nat.card F`.

## Main results

* `TauCeti.mem_powers_card_of_isLinearMap_pow`: if `a ↦ a ^ i` is `F`-linear on an algebraically
  closed extension `k` of a finite field `F`, then `i ∈ Submonoid.powers (Nat.card F)`.

## Proof idea

Let `q = #F`. The fixed points of the `F`-linear endomorphism `a ↦ (a ^ q) ^ i = a ^ (q * i)` are
precisely the roots in `k` of the separable polynomial `X ^ (q * i) - X`. Since `k` is algebraically
closed, this polynomial splits over `k` and has `q * i` distinct roots, which form a finite
`F`-subspace of `k`, hence have cardinality `q ^ d` for some `d ≥ 1`. Dividing by `q` yields
`i = q ^ (d - 1)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Deformation/TangentCount.lean` (`mem_powers_card_of_isLinearMap_pow`).
-/

@[expose] public section

open Module Polynomial

namespace TauCeti

/-- If the power map `a ↦ a ^ i` is `F`-linear on an separably closed extension `k` of a
finite field `F`, then `i` is a power of `Nat.card F`. -/
theorem mem_powers_card_of_isLinearMap_pow (F : Type*) {k : Type*} {i : ℕ}
    [Field F] [Finite F] [Field k] [Algebra F k] [IsSepClosed k]
    (h_lin : IsLinearMap F fun a : k ↦ a ^ i) :
    i ∈ Submonoid.powers (Nat.card F) := by
  classical
  cases nonempty_fintype F
  let q := Fintype.card F
  let P : F[X] := X ^ (q * i) - X
  have h_sep : P.Separable := galois_poly_separable _ _ (ringChar.dvd (by simp [q]))
  have h_ne : q * i ≠ 0 ∧ q * i ≠ 1 := by
    have hi : i ≠ 0 := by
      intro h0
      have := h_lin.map_zero
      simp [h0] at this
    exact ⟨mul_ne_zero Fintype.card_ne_zero hi,
      fun h ↦ (Fintype.one_lt_card.ne') (Nat.eq_one_of_mul_eq_one_right h)⟩
  have h_two : 2 ≤ q * i := (Nat.two_le_iff _).mpr h_ne
  let Φ : k →ₗ[F] k := h_lin.mk' _ ∘ₗ (FiniteField.frobeniusAlgHom F k).toLinearMap
  have h_roots : P.rootSet k = (Φ.fixedSubmodule : Set k) := by
    ext a
    simp [q, Φ, P, Polynomial.mem_rootSet, h_sep.ne_zero, sub_eq_zero, ← pow_mul]
  let V : Submodule F k := Φ.fixedSubmodule.copy (P.rootSet k) h_roots
  let _ : Fintype V := Polynomial.rootSetFintype P k
  have h_card : q * i = q ^ finrank F V := calc
    q * i = P.natDegree := (Polynomial.natDegree_X_pow_sub_X h_two).symm
    _ = Fintype.card V :=
      (Polynomial.card_rootSet_eq_natDegree h_sep (IsSepClosed.splits_codomain P h_sep)).symm
    _ = q ^ finrank F V := Module.card_eq_pow_finrank
  have h_pos : finrank F V ≠ 0 := fun h_zero ↦ by simp [h_card, h_zero] at h_two
  have h_pow : q * q ^ (finrank F V - 1) = q * i :=
    (mul_pow_sub_one h_pos q).trans h_card.symm
  exact ⟨finrank F V - 1, by simpa [q, Nat.card_eq_fintype_card] using
    Nat.eq_of_mul_eq_mul_left Fintype.card_pos h_pow⟩

end TauCeti
