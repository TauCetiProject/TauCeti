/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Adjoin.Basic

import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Adjoin.PowerBasis

/-!
# Nilpotent generators of augmented algebras over a field

Let `B` be a commutative `k`-algebra equipped with an augmentation `z : B →ₐ[k] k`, and let
`τ : B` be a nilpotent element (`τ ^ N = 0`) that divides every element of `ker z`. Then:

* `Algebra.adjoin_singleton_eq_top_of_nilpotent_dvd_ker`: `τ` generates `B` as a `k`-algebra, i.e.
  `Algebra.adjoin k {τ} = ⊤`.
* `Algebra.exists_algHom_apply_eq_smul_of_nilpotent_dvd_ker`: for every scalar `a : k`, there is a
  `k`-algebra endomorphism `σ : B →ₐ[k] B` sending `τ` to `a • τ`.

## Proof idea

Descending induction on `m ≤ N` shows `∀ b, τ ^ m * b ∈ Algebra.adjoin k {τ}`: the base case `m = N`
is trivial since `τ ^ N = 0`, and for the step one writes `b - z b • 1 = τ * d` using the
divisibility hypothesis on `ker z`. Since `minpoly k τ` divides `X ^ N`, it is a power `X ^ m`, so
`a • τ` is also a root of `minpoly k τ`; `PowerBasis.ofAdjoinEqTop` then produces `σ` with
`σ τ = a • τ`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Deformation/TangentCount.lean` (`adjoin_eq_top_and_exists_algHom_eq_smul`).
-/

@[expose] public section

open Polynomial

namespace Algebra

/-- If `z : B →ₐ[k] k` is an augmentation of a commutative `k`-algebra `B` and `τ : B` satisfies
`τ ^ N = 0` and divides every element of `ker z`, then `τ` generates `B` as a `k`-algebra. -/
theorem adjoin_singleton_eq_top_of_nilpotent_dvd_ker {k B : Type*} [CommRing k] [CommRing B]
    [Algebra k B] (z : B →ₐ[k] k) {τ : B} {N : ℕ} (hN : τ ^ N = 0)
    (h_dvd : ∀ b : B, z b = 0 → τ ∣ b) :
    adjoin k ({τ} : Set B) = ⊤ := by
  have h_rec : ∀ m : ℕ, (∀ b : B, τ ^ m * b ∈ adjoin k ({τ} : Set B)) →
      adjoin k ({τ} : Set B) = ⊤ := by
    intro m
    induction m with
    | zero =>
      intro h
      exact SetLike.ext fun b ↦
        ⟨fun _ ↦ trivial, fun _ ↦ by simpa only [pow_zero, one_mul] using h b⟩
    | succ m ih =>
      intro h
      apply ih
      intro b
      obtain ⟨d, hd⟩ := h_dvd (b - algebraMap k B (z b)) (by simp)
      have hb : b = τ * d + algebraMap k B (z b) := eq_add_of_sub_eq hd
      rw [hb, mul_add, ← mul_assoc, ← pow_succ]
      refine add_mem (h d) (mul_mem (pow_mem (subset_adjoin rfl) m) (algebraMap_mem _ _))
  exact h_rec N fun b ↦ by simp [hN]

/-- If `z : B →ₐ[k] k` is an augmentation of a commutative `k`-algebra `B` over a field `k` and
`τ : B` satisfies `τ ^ N = 0` and divides every element of `ker z`, then every scaling `τ ↦ a • τ`
extends to a `k`-algebra endomorphism of `B`. -/
theorem exists_algHom_apply_eq_smul_of_nilpotent_dvd_ker {k B : Type*} [Field k] [CommRing B]
    [Algebra k B] (z : B →ₐ[k] k) {τ : B} {N : ℕ} (hN : τ ^ N = 0)
    (h_dvd : ∀ b : B, z b = 0 → τ ∣ b) (a : k) :
    ∃ σ : B →ₐ[k] B, σ τ = a • τ := by
  have h_top : adjoin k ({τ} : Set B) = ⊤ :=
    adjoin_singleton_eq_top_of_nilpotent_dvd_ker z hN h_dvd
  have h_dvd_min : minpoly k τ ∣ X ^ N := minpoly.dvd k τ (by simp [hN])
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow prime_X N).mp h_dvd_min
  have h_ne : minpoly k τ ≠ 0 := fun h0 ↦ pow_ne_zero m X_ne_zero (hm.eq_zero_iff.mp h0)
  let pb := PowerBasis.ofAdjoinEqTop (minpoly.ne_zero_iff.mp h_ne) h_top
  have hτm : τ ^ m = 0 := by
    have : aeval τ (X ^ m : k[X]) = 0 := by
      have hdvd := hm.dvd
      simpa [minpoly.dvd_iff] using hdvd
    simpa using this
  have h_aeval : aeval (a • τ) (minpoly k τ) = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero hm.dvd' (by simp [smul_pow, hτm])
  exact ⟨pb.lift (a • τ) h_aeval, pb.lift_gen _ _⟩

end Algebra
