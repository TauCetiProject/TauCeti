/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
public import TauCeti.LinearAlgebra.Matrix.AlgEquiv.Center

/-!
# The scheme-theoretic center of the projective general linear group

The center of `PGLₙ = Aut(Mₙ)` is trivial, in every rank and characteristic. We first prove
that every universally central algebra-valued point is the identity, over an arbitrary
commutative base ring. Over a field, the represented center is therefore the identity
subgroup scheme. Testing dual-number-valued points retains the infinitesimal information
that would be lost by checking only points over fields.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v

variable (n : ℕ) {R : Type u} [CommRing R]

/-- Every universally central point of the projective general linear group is the identity.
The value algebra may have nilpotents, and the base may be any commutative ring. -/
theorem eq_one_of_isCentralPoint (A : CommAlgCat.{max u v} R)
    (q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra n R) A)
    (hq : HopfAlgebra.IsCentralPoint q) : q = 1 := by
  let B := CommAlgCat.of R (DualNumber A)
  let φ : A ⟶ B := CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom R A A)
  let q' := HopfAlgebra.mapPoints φ q
  have he : pointsMulEquiv n R A q = 1 := by
    apply AlgEquiv.eq_one_of_commute_innerAut_dualNumber _ (pointsMulEquiv n R B q')
    · intro Y
      exact pointsMulEquiv_mapPoints n φ q Y
    · intro g
      let p := (GeneralLinear.pointsMulEquiv (R := R) n).symm g
      have hc := (HopfAlgebra.isCentralPoint_def q).mp hq φ.hom
        (toConv (p.ofConv.comp (conjugationMap n R).hom.toAlgHom))
      have hc' := hc.map (pointsMulEquiv n R B)
      have hp := pointsMulEquiv_conjugationMap n R B p
      have hq' : AlgHom.mapValue φ.hom q = q' :=
        (AlgHom.mapValue_apply φ.hom q).trans (HopfAlgebra.mapPoints_apply φ q).symm
      rw [hp, hq'] at hc'
      simpa only [p, MulEquiv.apply_symm_apply] using hc'
  exact (pointsMulEquiv n R A).injective (he.trans (map_one _).symm)

/-- The full scheme-theoretic center of `PGLₙ` over a field is the identity subgroup.
This also rules out nontrivial infinitesimal central subgroup schemes in positive characteristic. -/
theorem centerDefiningIdeal_eq_augmentation (k : Type u) [Field k] :
    CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra n k) =
      HopfIdeal.augmentation k (coordinateHopfAlgebra n k) := by
  apply (CommHopfAlgCat.centerDefiningIdeal_eq_augmentation_iff_forall_isCentralPoint_eq_one
    (coordinateHopfAlgebra n k)).mpr
  exact fun A q hq ↦ eq_one_of_isCentralPoint n A q hq

end TauCeti.ProjectiveGeneralLinear
