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
some blocks are collapsed by `φ`.  A collapsed block has more than `e` letters, so on a word of
length at most `2 e + 1` at most one block is collapsed, and `F` agrees there with
`id + coderiv φ`, the identity plus the coderivation collapsing one block by `φ`.

This is the length bound behind gauge transformations of `A∞` structures: such a transformation
changes the Taylor map on short words only through one insertion of `φ`.

The proof does not expand `coalgHom`.  Both `F - id - coderiv φ` and `F - id` have vanishing letter
component, and the co-Leibniz rules of `F - id` and `coderiv φ` express the deconcatenation of
their values through shorter words, so both vanish by induction along the conilpotence filtration.

## Main results

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

/-- `F ⊗ F - id = (F - id) ⊗ id + F ⊗ (F - id)`, evaluated on a tensor. -/
private theorem map_apply_sub_eq (F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (w : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :
    TensorProduct.map F F w - w =
      TensorProduct.map (F - LinearMap.id) LinearMap.id w +
        TensorProduct.map F (F - LinearMap.id) w := by
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.sub_apply, LinearMap.id_apply,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
  | add w₁ w₂ h₁ h₂ =>
      calc TensorProduct.map F F (w₁ + w₂) - (w₁ + w₂)
          = (TensorProduct.map F F w₁ - w₁) + (TensorProduct.map F F w₂ - w₂) := by
            rw [map_add]
            abel
        _ = _ := by
            rw [h₁, h₂, map_add, map_add]
            abel

/-- `F ⊗ F - id - (D ⊗ id + id ⊗ D) = (F - id - D) ⊗ id + id ⊗ (F - id - D) + (F - id) ⊗ (F - id)`,
evaluated on a tensor. -/
private theorem map_apply_sub_sub_eq (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (w : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :
    TensorProduct.map F F w - w -
        (LinearMap.rTensor (ReducedTensorWords R M) D w +
          LinearMap.lTensor (ReducedTensorWords R M) D w) =
      TensorProduct.map (F - LinearMap.id - D) LinearMap.id w +
        TensorProduct.map LinearMap.id (F - LinearMap.id - D) w +
        TensorProduct.map (F - LinearMap.id) (F - LinearMap.id) w := by
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
      abel
  | add w₁ w₂ h₁ h₂ =>
      calc TensorProduct.map F F (w₁ + w₂) - (w₁ + w₂) -
            (LinearMap.rTensor (ReducedTensorWords R M) D (w₁ + w₂) +
              LinearMap.lTensor (ReducedTensorWords R M) D (w₁ + w₂))
          = (TensorProduct.map F F w₁ - w₁ -
              (LinearMap.rTensor (ReducedTensorWords R M) D w₁ +
                LinearMap.lTensor (ReducedTensorWords R M) D w₁)) +
            (TensorProduct.map F F w₂ - w₂ -
              (LinearMap.rTensor (ReducedTensorWords R M) D w₂ +
                LinearMap.lTensor (ReducedTensorWords R M) D w₂)) := by
            simp only [map_add]
            abel
        _ = _ := by
            rw [h₁, h₂]
            simp only [map_add]
            abel

/-- The coalgebra morphism with Taylor components `letter + φ` is the identity on the words of
length at most `e`, when `φ` vanishes on them. -/
private theorem coalgHom_letter_add_sub_id_apply_eq_zero {φ : ReducedTensorWords R M →ₗ[R] M}
    {e : ℕ} (hφ : ∀ z ∈ filtration R M e, φ z = 0) :
    ∀ z ∈ filtration R M e,
      (coalgHom R (letter R M + φ) - LinearMap.id : Module.End R (ReducedTensorWords R M)) z =
        0 := by
  have hF : IsCoalgHom R (coalgHom R (letter R M + φ)) := isCoalgHom_coalgHom _
  refine apply_eq_zero_of_mem_filtration_of_succ e fun k hk ih z hz ↦ ⟨?_, ?_⟩
  · rw [LinearMap.sub_apply, map_sub, letter_coalgHom_letter_add_apply, LinearMap.id_apply,
      add_sub_cancel_left, hφ z (filtration_monotone R M (by omega) hz)]
  · -- Each cut of `z` has a half of length at most `k`, on which `F - id` vanishes.
    have h := map_apply_sub_eq (coalgHom R (letter R M + φ)) (deconcatenation R M z)
    rw [map_deconcatenation_eq_zero_of_mem_filtration R M ih
        (apply_eq_zero_of_mem_filtration_zero R M _) (by simpa using hz),
      map_deconcatenation_eq_zero_of_mem_filtration R M
        (apply_eq_zero_of_mem_filtration_zero R M _) ih
        (by simpa using hz), add_zero, ← hF.deconcatenation_apply] at h
    rw [LinearMap.sub_apply, map_sub, LinearMap.id_apply, h]

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
  have hX := coalgHom_letter_add_sub_id_apply_eq_zero hφ
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
    have h := map_apply_sub_sub_eq (coalgHom R (letter R M + φ)) (coderiv R φ)
      (deconcatenation R M z)
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
