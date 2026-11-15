/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.SpecialIsogeny
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Character pullback of the rank-two symplectic special isogeny

The special isogeny of the rank-two standard carrier sends fundamental-weight torus parameters
`(s₀, s₁)` in type-C numbering to `(s₁, s₀²)`. To read the same carrier in Bourbaki type-B₂
numbering, both the simple nodes and the fundamental-weight coordinates must be swapped.
The resulting torus parameters transform as `(s₀, s₁) ↦ (s₁², s₀)`, whose character pullback is
exactly `DynkinType.b2SpecialIsogeny.weightMap`, not its transpose.

These identities compare the independently constructed matrix-of-minors endomorphism with the
integral root-datum map. They retain the actual torus parametrization used for this comparison.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.

The matrix endomorphism and its point-group transport are those of
`Matrix.symplecticSpecialIsogeny` and `SpStd.specialIsogeny`.
-/

public section

namespace TauCeti.SpStd

open _root_.Matrix

universe v

variable (K : Type v) [Field K] [CharP K 2]

/-- In type-C fundamental-weight coordinates the special isogeny sends `(s₀, s₁)` to
`(s₁, s₀²)`. -/
@[simp]
theorem specialIsogeny_weightTorusPoints (s : Fin 2 → Kˣ) :
    specialIsogeny K (weightTorusPoints 1 K s) =
      weightTorusPoints 1 K ![s 1, s 0 ^ 2] := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_specialIsogeny, coe_weightTorusPoints, coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
  rw [diagGL_coe, diagGL_coe, symplecticSpecialIsogeny_diagonal]
  apply congrArg diagonal
  have hfin : (⇑(finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm) =
      ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1] := by decide
  simp only [basisWeight_apply, hfin]
  funext i
  fin_cases i <;>
    simp [DynkinType.TypeC.weight_apply,
      torusCharacter_def, Fin.prod_univ_two, pow_two, mul_comm, mul_assoc]

/-- The weight torus of the rank-two symplectic carrier in type-B₂ fundamental-weight
coordinates. The swap is the B₂-to-C₂ node adapter. -/
noncomputable def b2WeightTorusPoints (A : Type v) [CommRing A] :
    (Fin 2 → Aˣ) →* points 1 A :=
  (weightTorusPoints 1 A).comp (MonoidHom.pi fun i =>
    Pi.evalMonoidHom (fun _ : Fin 2 => Aˣ) (Equiv.swap 0 1 i))

/-- Type-B₂ torus parameters become swapped type-C fundamental-weight parameters.
This is not a simp lemma: retaining the type-B₂ torus lets its action formulas apply. -/
theorem b2WeightTorusPoints_apply (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) :
    b2WeightTorusPoints A s = weightTorusPoints 1 A ![s 1, s 0] := by
  rw [b2WeightTorusPoints, MonoidHom.comp_apply]
  congr 1
  ext i
  fin_cases i <;> simp

/-- In type-B₂ fundamental-weight coordinates the special isogeny sends `(s₀, s₁)` to
`(s₁², s₀)`. -/
@[simp]
theorem specialIsogeny_b2WeightTorusPoints (s : Fin 2 → Kˣ) :
    specialIsogeny K (b2WeightTorusPoints K s) =
      b2WeightTorusPoints K ![s 1 ^ 2, s 0] := by
  simp only [b2WeightTorusPoints_apply, specialIsogeny_weightTorusPoints,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The character pullback of the represented special isogeny, in type-B₂ numbering, is the
weight map of the native special root-datum isogeny. -/
theorem isCharacterMap_specialIsogeny :
    IsCharacterMap (b2WeightTorusPoints K) (specialIsogeny K)
      DynkinType.b2SpecialIsogeny.weightMap := by
  rw [isCharacterMap_iff]
  intro s
  rw [specialIsogeny_b2WeightTorusPoints]
  congr 1
  ext i
  fin_cases i <;>
    simp [torusPointMap_apply, DynkinType.b2SpecialIsogeny_weightMap,
      DynkinType.b2SpecialIsogenyMatrix_def, torusCharacter_def, Fin.prod_univ_two]

end TauCeti.SpStd
