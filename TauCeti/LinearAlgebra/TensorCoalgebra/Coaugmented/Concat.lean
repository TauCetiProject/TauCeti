/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Prepend

/-!
# Concatenation behind a fixed first factor

For a module `X`, `TauCeti.TensorWords.tmulConcat` sends `x : X` to the linear map
`A ⊗ Tᶜ(A) → X ⊗ Tᶜ(A)`, `y ⊗ w ↦ x ⊗ y w`, where `y w` is the word `w` with the letter `y`
prepended.  On cofree bar comodules `X ⊗ Tᶜ(A)` it is the map through which representable
`A∞` modules are compared with the underlying complex of a module.

## Main definitions

* `TauCeti.TensorWords.tmulConcat`: concatenation behind a fixed first factor.

## Main results

* `TauCeti.TensorWords.cofreeLift_comp_tmulConcat`: the cofree lift of a linear map after
  concatenation splits into the cut before the first letter and the cofree lift of the
  concatenated map.
* `TauCeti.TensorWords.isHomogeneous_tmulConcat`: concatenation behind an element of degree `q`
  raises the total degree by `q`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uX uN

attribute [local instance] Comodule.cofree

namespace TensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

variable (R A) in
/-- Concatenation after a fixed first factor: `x` sends `y ⊗ w` to `x ⊗ y w`, where `y w` is the
word `w` with the letter `y` prepended. -/
noncomputable def tmulConcat (X : Type uX) [AddCommGroup X] [Module R X] :
    X →ₗ[R] A ⊗[R] TensorWords R A →ₗ[R] X ⊗[R] TensorWords R A :=
  (TensorProduct.mk R X (TensorWords R A)).compl₂
    (reducedInclusion R A ∘ₗ TensorProduct.lift (prepend R A))

variable {X : Type uX} [AddCommGroup X] [Module R X]

/-- Concatenation behind `x` applies prepending, followed by the inclusion of the nonempty words,
behind `x`. -/
theorem tmulConcat_apply (x : X) (z : A ⊗[R] TensorWords R A) :
    tmulConcat R A X x z = x ⊗ₜ[R] reducedInclusion R A (TensorProduct.lift (prepend R A) z) :=
  (rfl)

/-- Concatenation behind `x` sends `y ⊗ w` to `x ⊗ y w`. -/
@[simp]
theorem tmulConcat_tmul (x : X) (y : A) (w : TensorWords R A) :
    tmulConcat R A X x (y ⊗ₜ[R] w) = x ⊗ₜ[R] reducedInclusion R A (prepend R A y w) :=
  (rfl)

/-- The cofree lift of `φ` after concatenation behind `z`: the cut before the first letter of the
concatenated word gives `φ (z ⊗ 1)` in front of the whole word, and every other cut falls inside
the concatenated word. -/
theorem cofreeLift_comp_tmulConcat {N : Type uN} [AddCommGroup N] [Module R N]
    (φ : X ⊗[R] TensorWords R A →ₗ[R] N) (z : X) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A) φ).toLinearMap ∘ₗ tmulConcat R A X z =
      tmulConcat R A N (φ (z ⊗ₜ[R] 1)) +
        (Comodule.Hom.cofreeLift (C := TensorWords R A)
          (φ ∘ₗ tmulConcat R A X z)).toLinearMap := by
  refine TensorProduct.ext' fun y w ↦ ?_
  have hΔ := deconcatenation_reducedInclusion_prepend (R := R) y w
  simp only [LinearMap.comp_apply, LinearMap.add_apply, tmulConcat_tmul,
    Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact_tmul, comul_eq_deconcatenation]
  rw [hΔ]
  simp only [TensorProduct.tmul_add, map_add, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul]
  congr 1
  induction deconcatenation R A w using TensorProduct.inductionOn with
  | tmul u v => simp
  | add s t hs ht => simp only [map_add, TensorProduct.tmul_add, hs, ht]

/-- Concatenation behind an element of degree `q` raises the total degree by `q`. -/
theorem isHomogeneous_tmulConcat (G : InternalGrading R A) (H : InternalGrading R X) {q : ℤ}
    {x : X} (hx : x ∈ H.piece q) :
    LinearMap.IsHomogeneous (tmulConcat R A X x) (G.tensorProduct (grading G)).piece
      (H.tensorProduct (grading G)).piece q := by
  rw [LinearMap.isHomogeneous_def]
  intro d z hz
  have hc := (isHomogeneous_lift_prepend G).map_mem hz
  rw [add_zero] at hc
  have hw : reducedInclusion R A (TensorProduct.lift (prepend R A) z) ∈ (grading G).piece d := by
    rw [grading_piece]
    exact mem_gradedPiece_of_reducedInclusion hc
  rw [add_comm]
  exact InternalGrading.tmul_mem_tensorProduct H (grading G) hx hw

end TensorWords

end TauCeti
