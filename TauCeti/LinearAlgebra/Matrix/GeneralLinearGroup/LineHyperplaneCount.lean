/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi

/-!
# Counting linear forms on coordinate lines and hyperplanes over finite fields

Over a finite field `F` of cardinality `q` and a finite index set `n`, we count linear forms
`ξ : n → F` normalized by `ξ i = 1` (corresponding to hyperplanes missing the basis line `F • eᵢ`)
and those additionally satisfying `ξ ⬝ᵥ z = 1` for a vector `z` off the line `F • eᵢ`. These
elementary incidence counts underlie the quadratic Hecke relation for the stabilizer of a line in
`GL_n`.

## Main results

* `TauCeti.card_forms_eval_eq_one_mul`: `#{ξ : n → F | ξ i = 1} * q = q ^ |n|`.
* `TauCeti.card_forms_eval_eq_one_and_dotProduct_eq_one_mul_sq`: for `j ≠ i` with `z j ≠ 0`,
  `#{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} * q ^ 2 = q ^ |n|`.
* `TauCeti.card_coordLine`: `#{z : n → F | ∀ j ≠ i, z j = 0} = q`.
* `TauCeti.sum_forms_sum_dotProduct_eq_sum_card_smul`: double-counting identity exchanging the
  sums over `ξ` with `ξ i = 1` and `z` with `ξ ⬝ᵥ z = 1`.

## Provenance

Adapted from `New.card_forms_missing_line`, `New.card_forms_taking_one_at_two_vectors_mul_sq`,
`New.card_line`, and `New.sum_forms_sum_eq_sum_card_smul` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/Adelic/TraceFormula/LineCount.lean`).
-/

public section

namespace TauCeti

open Finset

variable {F n : Type*} [Fintype n] [DecidableEq n]

/-- Over a finite commutative ring `F`, the number of linear forms `ξ : n → F` with `ξ i = 1`
satisfies `#{ξ | ξ i = 1} * |F| = |F| ^ |n|`. -/
theorem card_forms_eval_eq_one_mul [CommRing F] [Fintype F] [DecidableEq F] (i : n) :
    #{ξ : n → F | ξ i = 1} * Fintype.card F = Fintype.card F ^ Fintype.card n := by
  let φ : (n → F) →+ F := Pi.evalAddMonoidHom (fun _ : n ↦ F) i
  have hsurj : Function.Surjective φ := Function.surjective_eval i
  have hconst (b : F) : #{ξ : n → F | φ ξ = b} = #{ξ : n → F | φ ξ = 1} :=
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj b) (hsurj 1)
  have hsum : Fintype.card (n → F) = ∑ b : F, #{ξ : n → F | φ ξ = b} :=
    card_eq_sum_card_fiberwise fun ξ _ ↦ mem_univ (φ ξ)
  rw [Finset.sum_congr rfl fun b _ ↦ hconst b] at hsum
  simpa [φ, Fintype.card_fun, mul_comm] using hsum.symm

/-- Over a finite field `F`, if `z : n → F` has a nonzero coordinate `z j ≠ 0` at some `j ≠ i`
(so `z` lies off the line `F • eᵢ`), then the number of forms `ξ` with `ξ i = 1` and `ξ ⬝ᵥ z = 1`
satisfies `#{ξ | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} * |F| ^ 2 = |F| ^ |n|`. -/
theorem card_forms_eval_eq_one_and_dotProduct_eq_one_mul_sq [Field F] [Fintype F] [DecidableEq F]
    {i j : n} {z : n → F} (hj : j ≠ i) (hz : z j ≠ 0) :
    #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} * Fintype.card F ^ 2 =
      Fintype.card F ^ Fintype.card n := by
  let φ : (n → F) →+ F × F :=
    (Pi.evalAddMonoidHom (fun _ : n ↦ F) i).prod
      (AddMonoidHom.mk' (· ⬝ᵥ z) fun ξ η : n → F ↦ add_dotProduct ξ η z)
  have hφ_apply (ξ : n → F) : φ ξ = (ξ i, ξ ⬝ᵥ z) := rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, b⟩
    refine ⟨Pi.single i a + Pi.single j ((b - a * z i) / z j), ?_⟩
    simp [hφ_apply, hj.symm, hz]
  have hconst (p : F × F) : #{ξ : n → F | φ ξ = p} = #{ξ : n → F | φ ξ = (1, 1)} :=
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj p) (hsurj (1, 1))
  have hsum : Fintype.card (n → F) = ∑ p : F × F, #{ξ : n → F | φ ξ = p} :=
    card_eq_sum_card_fiberwise fun ξ _ ↦ mem_univ (φ ξ)
  rw [Finset.sum_congr rfl fun p _ ↦ hconst p] at hsum
  simpa [hφ_apply, Prod.mk.injEq, Fintype.card_prod, Fintype.card_fun, sq,
    mul_comm] using hsum.symm

/-- Over a finite ring `F`, the coordinate line `{z : n → F | ∀ j ≠ i, z j = 0}` has cardinality
`|F|`. -/
theorem card_coordLine [Ring F] [Fintype F] [DecidableEq F] (i : n) :
    #{z : n → F | ∀ j ≠ i, z j = 0} = Fintype.card F := by
  have hline : ({z : n → F | ∀ j ≠ i, z j = 0} : Finset (n → F)) =
      univ.image fun c : F ↦ Pi.single i c := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_image]
    refine ⟨fun hz ↦ ⟨z i, by ext j; by_cases hj : j = i <;> simp [hj, hz]⟩, ?_⟩
    rintro ⟨c, rfl⟩ j hj
    simp [hj]
  rw [hline, card_image_of_injective _ (Pi.single_injective (M := fun _ : n ↦ F) i), card_univ]

/-- Double-counting identity for pairs `(ξ, z)` with `ξ i = 1` and `ξ ⬝ᵥ z = 1`. -/
theorem sum_forms_sum_dotProduct_eq_sum_card_smul [Semiring F] [Fintype F] [DecidableEq F]
    {W : Type*} [AddCommMonoid W] (i : n) (f : (n → F) → W) :
    ∑ ξ : n → F with ξ i = 1, ∑ z : n → F with ξ ⬝ᵥ z = 1, f z =
      ∑ z : n → F, #{ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1} • f z := by
  simp [sum_comm' (t' := univ) (s' := fun z ↦ {ξ : n → F | ξ i = 1 ∧ ξ ⬝ᵥ z = 1})]

end TauCeti
