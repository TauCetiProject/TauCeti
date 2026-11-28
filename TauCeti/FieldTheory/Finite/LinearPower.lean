/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Additive power maps over finite fields

Let `F` be a finite field and `k` an infinite extension of `F`. If the power map
`a ↦ a ^ i` on `k` is `F`-linear, then `i` is a power of `Nat.card F`.

## Main results

* `TauCeti.mem_powers_card_of_isLinearMap_pow`: if `a ↦ a ^ i` is `F`-linear on an infinite field
  extension `k` of a finite field `F`, then `i ∈ Submonoid.powers (Nat.card F)`.

## Proof idea

Since `k` is infinite, the polynomial `(X + 1) ^ i - X ^ i - 1 ∈ k[X]` vanishes on `k` and hence
identically, so `a ↦ a ^ i` extends to an `F`-linear map on `K := AlgebraicClosure k`. Let
`q = #F`. The fixed points of the `F`-linear endomorphism `a ↦ (a ^ q) ^ i = a ^ (q * i)` on `K`
are precisely the roots of the separable polynomial `X ^ (q * i) - X`, which splits over `K`. Its
`q * i` roots form a finite `F`-subspace of `K`, hence have cardinality `q ^ d` for some `d ≥ 1`.
Dividing by `q` yields `i = q ^ (d - 1)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Deformation/TangentCount.lean` (`mem_powers_card_of_isLinearMap_pow`).
-/

@[expose] public section

open Module Polynomial

namespace TauCeti

/-- If the power map `a ↦ a ^ i` is `F`-linear on an infinite field extension `k` of a finite
field `F`, then `i` is a power of `Nat.card F`. -/
theorem mem_powers_card_of_isLinearMap_pow (F : Type*) {k : Type*} {i : ℕ}
    [Field F] [Finite F] [Field k] [Algebra F k] [Infinite k]
    (h_lin : IsLinearMap F fun a : k ↦ a ^ i) :
    i ∈ Submonoid.powers (Nat.card F) := by
  classical
  cases nonempty_fintype F
  let K := AlgebraicClosure k
  let _ : Algebra F K := Algebra.compHom K (algebraMap F k)
  have h_poly : ((X + 1 : k[X]) ^ i - X ^ i - 1) = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_univ.mono fun a _ ↦ by
      simp [Polynomial.IsRoot, h_lin.map_add a 1])
  have h_linK : IsLinearMap F fun a : K ↦ a ^ i := by
    refine ⟨fun x y ↦ ?_, fun c x ↦ ?_⟩
    · by_cases hy : y = 0
      · simp [hy, show i ≠ 0 from fun h0 ↦ by simpa [h0] using h_lin.map_zero]
      · have heval := congrArg (Polynomial.aeval (x / y)) h_poly
        simp only [map_sub, map_add, map_pow, map_one, aeval_X, map_zero, sub_eq_zero] at heval
        have hmul : (x / y + 1) ^ i * y ^ i - (x / y) ^ i * y ^ i = y ^ i := by
          simpa [sub_mul, one_mul] using congrArg (· * y ^ i) heval
        have hxy : (x / y + 1) * y = x + y := by rw [add_mul, div_mul_cancel₀ x hy, one_mul]
        rw [← mul_pow, hxy, ← mul_pow, div_mul_cancel₀ x hy] at hmul
        exact eq_add_of_sub_eq' hmul
    · have hc : (algebraMap F k c) ^ i = algebraMap F k c := by
        simpa [Algebra.smul_def] using h_lin.map_smul c 1
      have hcK : (algebraMap F K c) ^ i = algebraMap F K c := by
        simpa [← map_pow] using congrArg (algebraMap k K) hc
      rw [Algebra.smul_def, mul_pow, hcK, Algebra.smul_def]
  let q := Fintype.card F
  let P : F[X] := X ^ (q * i) - X
  have h_sep : P.Separable := galois_poly_separable _ _ (ringChar.dvd (by simp [q]))
  have hi : i ≠ 0 := fun h0 ↦ by simpa [h0] using h_lin.map_zero
  have h_two : 2 ≤ q * i := (Nat.two_le_iff _).mpr
    ⟨mul_ne_zero Fintype.card_ne_zero hi,
      fun h ↦ Fintype.one_lt_card.ne' (Nat.eq_one_of_mul_eq_one_right h)⟩
  let Φ : K →ₗ[F] K := h_linK.mk' _ ∘ₗ (FiniteField.frobeniusAlgHom F K).toLinearMap
  have h_roots : P.rootSet K = (Φ.fixedSubmodule : Set K) := by
    ext a
    simp [q, Φ, P, Polynomial.mem_rootSet, h_sep.ne_zero, sub_eq_zero, ← pow_mul]
  let V : Submodule F K := Φ.fixedSubmodule.copy (P.rootSet K) h_roots
  let _ : Fintype V := Polynomial.rootSetFintype P K
  have h_card : q * i = q ^ finrank F V := calc
    q * i = P.natDegree := (Polynomial.natDegree_X_pow_sub_X h_two).symm
    _ = Fintype.card V :=
      (Polynomial.card_rootSet_eq_natDegree h_sep (IsAlgClosed.splits _)).symm
    _ = q ^ finrank F V := Module.card_eq_pow_finrank
  have h_pos : finrank F V ≠ 0 := fun h_zero ↦ by simp [h_card, h_zero] at h_two
  have h_pow : q * q ^ (finrank F V - 1) = q * i :=
    (mul_pow_sub_one h_pos q).trans h_card.symm
  exact ⟨finrank F V - 1, by simpa [q, Nat.card_eq_fintype_card] using
    Nat.eq_of_mul_eq_mul_left Fintype.card_pos h_pow⟩

end TauCeti
