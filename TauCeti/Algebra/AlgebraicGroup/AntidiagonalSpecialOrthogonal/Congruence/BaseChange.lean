/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Congruence.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.BaseChange
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
The proof specializes the naturality of quotient isomorphisms under base change
(`TauCeti.CommHopfAlgCat.baseChangeMap_quotientIsoOfComapEq_hom_comp`)
to the naturality of conjugation on `GL_l`
(`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`).
-/

public section

open CategoryTheory Matrix

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u v

variable {R : Type u} [CommRing R] [Invertible (2 : R)] (l : ℕ) {i : R}
variable (K : Type max u v) [CommRing K] [Algebra R K] [Invertible (2 : K)]

/-- **The congruence matrix is natural in the base ring.** -/
theorem map_congrUnit (hi : i * i = -1) :
    GeneralLinearGroup.map (algebraMap R K) (congrUnit l hi) =
      congrUnit l (by rw [← map_mul, hi, map_neg, map_one] :
        algebraMap R K i * algebraMap R K i = -1) := by
  have h2 : algebraMap R K ⅟2 = ⅟2 :=
    (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap R K) 2, ← map_mul, mul_invOf_self,
      map_one])).symm
  apply Units.ext
  ext p q
  rw [GeneralLinearGroup.map_apply, coe_congrUnit, coe_congrUnit, congrMatrix_apply,
    congrMatrix_apply]
  simp only [map_add, apply_ite (algebraMap R K), map_mul, map_sub, map_one, map_zero, h2]

/-- **The identification `O(SO_l^J) ≅ O(SO_l)` is natural in the base ring.** Along the
base-change isomorphisms of `SO_l^J` and `SO_l`, the scalar extension of the identification over
`R` is the identification over `K`, for the image of `i`. -/
@[reassoc]
theorem baseChangeMap_coordinateHopfAlgebraIsoSpecialOrthogonal_hom_comp (hi : i * i = -1) :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateHopfAlgebraIsoSpecialOrthogonal l hi).hom ≫
        (SpecialOrthogonal.coordinateHopfAlgebraBaseChangeIso R K l).hom =
      (coordinateHopfAlgebraBaseChangeIso R l K).hom ≫
        (coordinateHopfAlgebraIsoSpecialOrthogonal l (by rw [← map_mul, hi, map_neg, map_one] :
          algebraMap R K i * algebraMap R K i = -1)).hom := by
  rw [coordinateHopfAlgebraIsoSpecialOrthogonal_def, coordinateHopfAlgebraIsoSpecialOrthogonal_def]
  have h₁ := baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom R l K
  have h₂ :=
    SpecialOrthogonal.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom R K l
  rw [coordinateMap_def, coordinateMap_def] at h₁
  rw [SpecialOrthogonal.coordinateMap_def, SpecialOrthogonal.coordinateMap_def] at h₂
  refine CommHopfAlgCat.baseChangeMap_quotientIsoOfComapEq_hom_comp _ _ _ _ _ _ h₁ h₂ ?_
  rw [← map_congrUnit, ← map_inv]
  exact GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp K (congrUnit l hi)⁻¹

end TauCeti.AntidiagonalSpecialOrthogonal
