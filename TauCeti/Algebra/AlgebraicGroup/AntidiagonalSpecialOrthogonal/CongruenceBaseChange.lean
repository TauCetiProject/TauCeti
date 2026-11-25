/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Congruence
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ConjugationBaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.BaseChange

/-!
# Naturality of `O(SO_l^J) ≅ O(SO_l)` in the base ring

Over a ring `R` containing `1/2` and a square root `i` of `-1`, conjugation by the congruence
matrix `P = (1 - i)/2 · 1 + (1 + i)/2 · J_l` identifies the coordinate Hopf algebras of `SO_l^J`
and of the special orthogonal group `SO_l` of the identity form
(`TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraIsoSpecialOrthogonal`). For an
`R`-algebra `K` containing `1/2`, the congruence matrix maps to the congruence matrix of the image
of `i` (`TauCeti.AntidiagonalSpecialOrthogonal.map_congrUnit`), so along the base-change
isomorphisms of `SO_l^J` and `SO_l` the scalar extension of the identification over `R` is the
identification over `K`
(`baseChangeMap_coordinateHopfAlgebraIsoSpecialOrthogonal_hom_comp`).
The proof reduces, through the quotient maps from `O(GL_l)`, to the naturality of conjugation on
`GL_l` (`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`).
-/

public section

open CategoryTheory Matrix

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u v

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) {i : R}
variable (K : Type max u v) [CommRing K] [Algebra R K] [Invertible (2 : K)]

/-- The image of `½` in an `R`-algebra containing `½` is `½`. -/
private theorem algebraMap_invOf_two : algebraMap R K ⅟2 = ⅟2 :=
  (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap R K) 2, ← map_mul, mul_invOf_self,
    map_one])).symm

omit [Invertible (2 : R)] [Invertible (2 : K)] in
/-- The image of a square root of `-1` is a square root of `-1`. -/
theorem algebraMap_mul_algebraMap_eq_neg_one (hi : i * i = -1) :
    algebraMap R K i * algebraMap R K i = -1 := by
  rw [← map_mul, hi, map_neg, map_one]

/-- **The congruence matrix is natural in the base ring.** -/
theorem map_congrUnit (hi : i * i = -1) :
    GeneralLinearGroup.map (algebraMap R K) (congrUnit l hi) =
      congrUnit l (algebraMap_mul_algebraMap_eq_neg_one K hi) := by
  apply Units.ext
  ext p q
  rw [GeneralLinearGroup.map_apply, coe_congrUnit, coe_congrUnit, congrMatrix_apply,
    congrMatrix_apply]
  simp only [map_add, apply_ite (algebraMap R K), map_mul, map_sub, map_one, map_zero]
  rw [algebraMap_invOf_two K]

omit [Invertible (2 : R)] [Invertible (2 : K)] in
/-- The inverse base-change isomorphism of `SO_l^J` is compatible with the quotient maps from
`O(GL_l)`. -/
private theorem coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv :
    coordinateMap K l ≫ (coordinateHopfAlgebraBaseChangeIso R l K).inv =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R l) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom, Iso.inv_hom_id_assoc]

/-- **The identification `O(SO_l^J) ≅ O(SO_l)` is natural in the base ring.** Along the
base-change isomorphisms of `SO_l^J` and `SO_l`, the scalar extension of the identification over
`R` is the identification over `K`, for the image of `i`. -/
theorem baseChangeMap_coordinateHopfAlgebraIsoSpecialOrthogonal_hom_comp (hi : i * i = -1) :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).hom ≫
        (SpecialOrthogonal.coordinateHopfAlgebraBaseChangeIso R K l).hom =
      (coordinateHopfAlgebraBaseChangeIso R l K).hom ≫
        (coordinateHopfAlgebraIsoSpecialOrthogonal l
          (algebraMap_mul_algebraMap_eq_neg_one K hi)).hom := by
  rw [← Iso.inv_comp_eq]
  apply CommHopfAlgCat.mkQuotient_hom_ext
  have hGL := GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp K (congrUnit l hi)⁻¹
  rw [← coordinateMap_def, ← Category.assoc,
    coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.baseChangeMap (coordinateMap R l)),
    ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_hom,
    coordinateMap_comp_coordinateHopfAlgebraIsoSpecialOrthogonal_hom,
    (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp, CommHopfAlgCat.baseChangeFunctor_map,
    CommHopfAlgCat.baseChangeFunctor_map, Category.assoc,
    SpecialOrthogonal.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom,
    reassoc_of% hGL, Iso.inv_hom_id_assoc, map_inv, map_congrUnit]

end TauCeti.AntidiagonalSpecialOrthogonal
