/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Tangent.Basic

/-!
# Differential of the central isogeny `SLₙ → PGLₙ` on `sl₂`

This file records the effect of the differential of `SL₂ ⟶ PGL₂`
(`TauCeti.SpecialLinear.conjugationMap 2 R`) on the standard `sl₂` triple in `Lie(SL₂)`.
When `2 ≠ 0` in the base ring, the Cartan element `E₀₀ - E₁₁` maps non-trivially into
`Lie(PGL₂)`, so the standard `sl₂` triple pushes forward to an `sl₂` triple in `Lie(PGL₂)`
(`TauCeti.SpecialLinear.isSl2Triple_derivationCompLieHom_conjugationMap`).

## Main declarations

* `TauCeti.SpecialLinear.derivationCompLieHom_conjugationMap_two_ne_zero`: the differential of
  `SL₂ ⟶ PGL₂` does not annihilate `E₀₀ - E₁₁` when `2 ≠ 0`.
* `TauCeti.SpecialLinear.isSl2Triple_derivationCompLieHom_conjugationMap`: the standard `sl₂`
  triple in `Lie(PGL₂)`, pushed forward along `SL₂ ⟶ PGL₂`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 21.
-/

public section

open CategoryTheory LieAlgebra

namespace TauCeti.SpecialLinear

universe u

variable (R : Type u) [CommRing R] [NeZero (2 : R)]

/-- The differential of `SL₂ ⟶ PGL₂` does not annihilate the standard Cartan element
`E₀₀ - E₁₁` when `2 ≠ 0` in `R`. -/
theorem derivationCompLieHom_conjugationMap_two_ne_zero :
    derivationCompLieHom (B := R) (conjugationMap 2 R).hom ((tangentLieEquivSl (R := R)
      (B := R) 2).symm (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)) ≠ 0 := by
  intro h0
  let d₀ := (tangentLieEquivSl (R := R) (B := R) 2).symm
    (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)
  have hd : ProjectiveGeneralLinear.tangentEnd 2
      (derivationComp (B := R) (conjugationMap 2 R).hom d₀) = 0 := by
    rw [← derivationCompLieHom_apply, h0, map_zero]
  have hmat : GeneralLinear.tangentMatrix 2 (derivationComp (B := R) (coordinateMap R 2).hom d₀) =
      (LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 2) 1 (1 : R)).val := by
    rw [coordinateMap, CommHopfAlgCat.hom_mkQuotient, ← HopfIdeal.quotientLieHom_apply,
      ← tangentMatrix_apply_coe, ← tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
  rw [conjugationMap_def, CommHopfAlgCat.hom_comp, derivationComp_comp, LinearMap.comp_apply,
    ProjectiveGeneralLinear.tangentEnd_derivationComp_conjugationMap, hmat] at hd
  have heval : (2 : R) = 0 := by
    simpa [LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.mul_apply, Fin.sum_univ_two,
      sub_neg_eq_add, one_add_one_eq_two] using
      congr_fun (congr_fun (LinearMap.congr_fun hd (Matrix.single (0 : Fin 2) 1 (1 : R))) 0) 1
  exact NeZero.ne (2 : R) heval

/-- **The standard `sl₂` triple in `Lie(PGL₂)`**, pushed forward along `SL₂ ⟶ PGL₂`. -/
theorem isSl2Triple_derivationCompLieHom_conjugationMap :
    IsSl2Triple
      (derivationCompLieHom (B := R) (conjugationMap 2 R).hom
        ((tangentLieEquivSl (R := R) (B := R) 2).symm
          (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1)))
      (derivationCompLieHom (B := R) (conjugationMap 2 R).hom
        ((tangentLieEquivSl (R := R) (B := R) 2).symm
          (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1)))
      (derivationCompLieHom (B := R) (conjugationMap 2 R).hom
        ((tangentLieEquivSl (R := R) (B := R) 2).symm
          (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1))) :=
  have : Nontrivial R := ⟨⟨2, 0, NeZero.ne (2 : R)⟩⟩
  (isSl2Triple_tangentLieEquivSl_symm_single R).map _
    (derivationCompLieHom_conjugationMap_two_ne_zero R)

end TauCeti.SpecialLinear
