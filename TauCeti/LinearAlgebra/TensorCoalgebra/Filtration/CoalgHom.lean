/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coderivation

/-!
# Coalgebra morphisms of reduced tensor coalgebras close to the identity

Let `φ : Tᶜ(M) ⟶ M` vanish on the words of length at most `e`.  The coalgebra morphism
`F = coalgHom (letter + φ)`, whose Taylor components are those of the identity perturbed by `φ`,
sends a word to the sum, over all ways of cutting it into consecutive blocks, of the word in which
some blocks are collapsed by `φ`.  A collapsed block has more than `e` letters, so `F` is the
identity on the words of length at most `e`, and on a word of length at most `2 e + 1` at most one
block is collapsed, so `F` agrees there with `id + coderiv φ`, the identity plus the coderivation
collapsing one block by `φ`.

This is the length bound behind gauge transformations of `A∞` structures: such a transformation
changes the Taylor map on short words only through one insertion of `φ`.

## Main results

* `TauCeti.ReducedTensorWords.coalgHom_letter_add_apply_eq_self_of_mem_filtration`: the coalgebra
  morphism with Taylor components `letter + φ` is the identity on the words of length at most `e`.
* `TauCeti.ReducedTensorWords.coalgHom_letter_add_apply_of_mem_filtration`: the coalgebra
  morphism with Taylor components `letter + φ` is `id + coderiv φ` on the words of length at most
  `2 e + 1`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, for gauge transformations of `A∞` structures.
-/

public section

open scoped TensorProduct

universe uR uM

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- An endomorphism of the reduced tensor coalgebra vanishes on the words of length at most `n`
when, for every `k < n`, vanishing on the words of length at most `k` forces its values on the
words of length at most `k + 1` to have zero letter and zero deconcatenation. -/
private theorem apply_eq_zero_of_mem_filtration_of_succ
    {Y : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (n : ℕ)
    (hstep : ∀ k < n, (∀ z ∈ filtration R M k, Y z = 0) → ∀ z ∈ filtration R M (k + 1),
      letter R M (Y z) = 0 ∧ deconcatenation R M (Y z) = 0) :
    ∀ z ∈ filtration R M n, Y z = 0 := by
  induction n with
  | zero =>
      intro z hz
      rw [filtration_zero, Submodule.mem_bot] at hz
      rw [hz, map_zero]
  | succ k ih =>
      intro z hz
      obtain ⟨hl, hd⟩ := hstep k (Nat.lt_succ_self k) (ih fun i hi ↦ hstep i (by omega)) z hz
      exact eq_of_deconcatenation_eq_of_letter_eq R M (by rw [hd, map_zero])
        (by rw [hl, map_zero])

/-- The letter of the value of the coalgebra morphism with Taylor components `letter + φ`. -/
private theorem letter_coalgHom_letter_add_apply (φ : ReducedTensorWords R M →ₗ[R] M)
    (z : ReducedTensorWords R M) :
    letter R M (coalgHom R (letter R M + φ) z) = letter R M z + φ z := by
  rw [← LinearMap.comp_apply (letter R M), letter_comp_coalgHom, LinearMap.add_apply]

/-- The coalgebra morphism with Taylor components `letter + φ` is the identity on the words of
length at most `e`, when `φ` vanishes on them: there its Taylor components are those of the
identity. -/
theorem coalgHom_letter_add_apply_eq_self_of_mem_filtration
    {φ : ReducedTensorWords R M →ₗ[R] M} {e : ℕ} (hφ : ∀ z ∈ filtration R M e, φ z = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M e) :
    coalgHom R (letter R M + φ) z = z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_id M)
    (fun w hw ↦ by rw [letter_coalgHom_letter_add_apply, hφ w hw, add_zero, LinearMap.id_apply])
    hz

/- The proof below does not expand `coalgHom`.  It shows by induction along the conilpotence
filtration that `F - id - coderiv φ` vanishes on the words of length at most `2 e + 1`, where
`F = coalgHom (letter + φ)`.  The letter component of `F - id - coderiv φ` is zero, and the
co-Leibniz rules of `F` and `coderiv φ` express the deconcatenation of a value through values on
shorter words.  This leaves the term `(F - id) ⊗ (F - id)`, which vanishes since every cut of a
word of length at most `2 e + 1` has a half of length at most `e`, on which `F - id` vanishes. -/

/-- **A coalgebra morphism close to the identity.**  If `φ` vanishes on the words of length at most
`e`, then the coalgebra morphism with Taylor components `letter + φ` is `id + coderiv φ` on the
words of length at most `2 e + 1`: collapsing two blocks by `φ` needs at least `2 (e + 1)`
letters. -/
theorem coalgHom_letter_add_apply_of_mem_filtration {φ : ReducedTensorWords R M →ₗ[R] M} {e : ℕ}
    (hφ : ∀ z ∈ filtration R M e, φ z = 0) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (2 * e + 1)) :
    coalgHom R (letter R M + φ) z = z + coderiv R φ z := by
  have hF : IsCoalgHom R (coalgHom R (letter R M + φ)) := isCoalgHom_coalgHom _
  have hD : IsCoderivation R (coderiv R φ) := isCoderivation_coderiv R φ
  have hX : ∀ z ∈ filtration R M e,
      (coalgHom R (letter R M + φ) - LinearMap.id : Module.End R (ReducedTensorWords R M)) z =
        0 := fun z hz ↦ by
    rw [LinearMap.sub_apply, LinearMap.id_apply,
      coalgHom_letter_add_apply_eq_self_of_mem_filtration hφ hz, sub_self]
  suffices h : ∀ z ∈ filtration R M (2 * e + 1),
      (coalgHom R (letter R M + φ) - LinearMap.id - coderiv R φ :
        Module.End R (ReducedTensorWords R M)) z = 0 by
    have hz' := h z hz
    rwa [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply, sub_sub,
      sub_eq_zero] at hz'
  refine apply_eq_zero_of_mem_filtration_of_succ (2 * e + 1) fun k hk ih z hz ↦ ⟨?_, ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, map_sub,
      letter_coalgHom_letter_add_apply, LinearMap.id_apply, ← LinearMap.comp_apply (letter R M),
      letter_comp_coderiv, add_sub_cancel_left, sub_self]
  · -- The terms `(F - id - D) ⊗ id` and `id ⊗ (F - id - D)` vanish on the cuts of `z` by
    -- induction, and `(F - id) ⊗ (F - id)` since every cut of a word of length at most `2 e + 1`
    -- has a half of length at most `e`.
    generalize coalgHom R (letter R M + φ) = F at hF hX ih ⊢
    have hr : TensorProduct.map (F - LinearMap.id) (LinearMap.id (M := ReducedTensorWords R M)) =
        TensorProduct.map (F - LinearMap.id - coderiv R φ) LinearMap.id +
          TensorProduct.map (coderiv R φ) LinearMap.id := by
      rw [← TensorProduct.map_add_left]
      congr 1
      abel
    have hl : TensorProduct.map (LinearMap.id (M := ReducedTensorWords R M)) (F - LinearMap.id) =
        TensorProduct.map LinearMap.id (F - LinearMap.id - coderiv R φ) +
          TensorProduct.map LinearMap.id (coderiv R φ) := by
      rw [← TensorProduct.map_add_right]
      congr 1
      abel
    have h : TensorProduct.map F F (deconcatenation R M z) - deconcatenation R M z -
          (LinearMap.rTensor _ (coderiv R φ) (deconcatenation R M z) +
            LinearMap.lTensor _ (coderiv R φ) (deconcatenation R M z)) =
        TensorProduct.map (F - LinearMap.id - coderiv R φ) LinearMap.id (deconcatenation R M z) +
          TensorProduct.map LinearMap.id (F - LinearMap.id - coderiv R φ)
            (deconcatenation R M z) +
          TensorProduct.map (F - LinearMap.id) (F - LinearMap.id) (deconcatenation R M z) := by
      conv_lhs => rw [← add_sub_cancel LinearMap.id F]
      rw [TensorProduct.map_add_left, TensorProduct.map_add_right, TensorProduct.map_add_right,
        TensorProduct.map_id, hr, hl]
      simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.rTensor_def,
        LinearMap.lTensor_def]
      abel
    rw [map_deconcatenation_eq_zero_of_mem_filtration R M ih
        (apply_eq_zero_of_mem_filtration_zero R M _) (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M
        (apply_eq_zero_of_mem_filtration_zero R M _) ih
        (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M hX hX
        (filtration_monotone R M (by omega) hz), add_zero, add_zero,
      ← hF.deconcatenation_apply, ← hD.deconcatenation_apply] at h
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, map_sub, LinearMap.id_apply, h]

end TauCeti.ReducedTensorWords
