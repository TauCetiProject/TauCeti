/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Matrix.IntegralCast

/-!
# Transferring integral matrix Serre relations

An integral matrix Serre system determines the images of opposite-root brackets under
any matrix realization sending the root vectors to the cast integral generators. When the
realization is injective, all Serre relations transfer to the source Lie algebra. These
results let integral matrix representations supply Serre comparisons over arbitrary
commutative rings.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R L I : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {CM : Matrix I I ℤ} {H E F : I → Matrix n n ℤ} {e f : I → L}

/-- A matrix realization sending root vectors to cast integral Serre generators sends
opposite-root brackets to the corresponding cast Cartan generators. -/
theorem IsSerreSystem.map_lie_eq_intCast
    (hZ : IsSerreSystem ℤ CM H E F) (φ : L →ₗ⁅R⁆ Matrix n n R)
    (he : ∀ i, φ (e i) = (E i).map (Int.cast : ℤ → R))
    (hf : ∀ i, φ (f i) = (F i).map (Int.cast : ℤ → R)) (i : I) :
    φ ⁅e i, f i⁆ = (H i).map (Int.cast : ℤ → R) := by
  rw [LieHom.map_lie, he, hf]
  simpa only [Function.comp_apply, matrixIntCastLieHom_eq_map] using
    (hZ.map (matrixIntCastLieHom R)).lie_E_F_self i

/-- An integral matrix Serre system gives Serre relations for opposite-root brackets in
any Lie algebra with an injective matrix realization sending its root vectors to the cast
integral generators. -/
theorem IsSerreSystem.of_injective_intCast
    (hZ : IsSerreSystem ℤ CM H E F) (φ : L →ₗ⁅R⁆ Matrix n n R)
    (hφ : Function.Injective φ)
    (he : ∀ i, φ (e i) = (E i).map (Int.cast : ℤ → R))
    (hf : ∀ i, φ (f i) = (F i).map (Int.cast : ℤ → R)) :
    IsSerreSystem R CM (fun i ↦ ⁅e i, f i⁆) e f := by
  apply IsSerreSystem.of_injective φ hφ
  simpa only [Function.comp_def, hZ.map_lie_eq_intCast φ he hf, he, hf,
    matrixIntCastLieHom_eq_map] using
    (hZ.map (matrixIntCastLieHom R)).changeScalars (S := R)

/-- Casting integral matrix Serre generators back to integer matrices leaves their
Serre lift unchanged. -/
theorem serreLift_intCast [DecidableEq I] (hZ : IsSerreSystem ℤ CM H E F) :
    serreLift ((hZ.map (matrixIntCastLieHom ℤ)).changeScalars (S := ℤ)) =
      serreLift hZ := by
  apply serre_hom_ext <;> intro i <;>
    simp only [serreLift_serreH, serreLift_serreE, serreLift_serreF,
      Function.comp_apply, matrixIntCastLieHom_eq_map] <;>
    exact Matrix.ext fun _ _ ↦ Int.cast_id

end TauCeti
