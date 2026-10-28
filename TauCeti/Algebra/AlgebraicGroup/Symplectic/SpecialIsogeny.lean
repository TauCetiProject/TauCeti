/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Scheme
public import TauCeti.Algebra.CharP.Frobenius.Bialgebra
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
import TauCeti.RingTheory.RingHom.Power

/-!
# The exceptional endomorphism of the symplectic group scheme

The polynomial special endomorphism of `Sp₄` in characteristic two is represented by an
endomorphism of its coordinate Hopf algebra over `𝔽₂`. Its square is Frobenius, and it is
finite and faithfully flat. Thus the
minor construction acts on the group scheme, including its infinitesimal points, rather
than just on points over fields.

The construction uses the naturality of `TauCeti.specialIsogeny` and full faithfulness of
`CommHopfAlgCat.pointsFunctor`. The matrix construction and its root equations are in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SpecialIsogeny`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

noncomputable section

local notation "𝔽₂" => ZMod 2
local notation "S" => coordinateHopfAlgebra 𝔽₂ 2

/-- The polynomial special endomorphism on algebra-valued points, including the zero algebra. -/
private def specialIsogenyPoints (A : CommAlgCat.{0} 𝔽₂) :
    HopfAlgebra.points (H := S) A →* HopfAlgebra.points (H := S) A := by
  classical
  exact if h : Nontrivial A then
    let _ := h
    let _ : CharP A 2 := charP_of_injective_algebraMap (algebraMap 𝔽₂ A).injective 2
    (pointsMulEquiv (A := A) 𝔽₂ 2).symm.toMonoidHom.comp
      (TauCeti.specialIsogeny.comp (pointsMulEquiv (A := A) 𝔽₂ 2).toMonoidHom)
  else 1

private theorem pointsMulEquiv_specialIsogenyPoints (A : CommAlgCat.{0} 𝔽₂) [Nontrivial A]
    [CharP A 2] (q : HopfAlgebra.points (H := S) A) :
    pointsMulEquiv (A := A) 𝔽₂ 2 (specialIsogenyPoints A q) =
      TauCeti.specialIsogeny (pointsMulEquiv (A := A) 𝔽₂ 2 q) := by
  classical
  simp [specialIsogenyPoints, (inferInstance : Nontrivial A)]

private theorem mapValue_specialIsogenyPoints {A B : CommAlgCat.{0} 𝔽₂} (f : A ⟶ B)
    (q : HopfAlgebra.points (H := S) A) :
    AlgHom.mapValue f.hom (specialIsogenyPoints A q) =
      specialIsogenyPoints B (AlgHom.mapValue f.hom q) := by
  cases subsingleton_or_nontrivial B with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    have : Nontrivial A := f.hom.toRingHom.domain_nontrivial
    let _ : CharP A 2 := charP_of_injective_algebraMap (algebraMap 𝔽₂ A).injective 2
    let _ : CharP B 2 := charP_of_injective_algebraMap (algebraMap 𝔽₂ B).injective 2
    apply (pointsMulEquiv (A := B) 𝔽₂ 2).injective
    rw [pointsMulEquiv_mapValue (R := 𝔽₂) (m := 2) f.hom,
      pointsMulEquiv_specialIsogenyPoints,
      pointsMulEquiv_specialIsogenyPoints, map_specialIsogeny, pointsMulEquiv_mapValue]

private def specialIsogenyPointsMap :
    HopfAlgebra.pointsFunctor (R := 𝔽₂) (H := S) ⟶
      HopfAlgebra.pointsFunctor (R := 𝔽₂) (H := S) where
  app A := GrpCat.ofHom (specialIsogenyPoints A)
  naturality {A B} f := by
    ext q
    have hmap (p : HopfAlgebra.points (H := S) A) :
        (HopfAlgebra.pointsFunctor.map f) p = AlgHom.mapValue f.hom p := by
      apply WithConv.ofConv_injective
      ext x
      rw [HopfAlgebra.pointsFunctor_map_apply_apply, AlgHom.mapValue_apply,
        ofConv_toConv, AlgHom.comp_apply]
    -- Evaluate categorical composition before rewriting the functor's action on points.
    change specialIsogenyPoints B ((HopfAlgebra.pointsFunctor.map f) q) =
      (HopfAlgebra.pointsFunctor.map f) (specialIsogenyPoints A q)
    exact (congrArg (specialIsogenyPoints B) (hmap q)).trans
      ((mapValue_specialIsogenyPoints f q).symm.trans
        (hmap (specialIsogenyPoints A q)).symm)

/-- The coordinate Hopf-algebra endomorphism of the exceptional `Sp₄` isogeny over `𝔽₂`. -/
def specialIsogenyCoordinateMap : S ⟶ S :=
  CommHopfAlgCat.homOfPointsMap specialIsogenyPointsMap

private theorem mapDomain_specialIsogenyCoordinateMap (A : CommAlgCat.{0} 𝔽₂)
    (q : HopfAlgebra.points (H := S) A) :
    BialgHom.mapDomain specialIsogenyCoordinateMap.hom q = specialIsogenyPoints A q := by
  have h : (CommHopfAlgCat.Hom.mapPointsFunctor specialIsogenyCoordinateMap).app A q =
      specialIsogenyPoints A q := by
    rw [specialIsogenyCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap]
    rfl
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at h
  apply WithConv.ofConv_injective
  ext x
  have hx := congrArg (fun p : (HopfAlgebra.pointsFunctor (R := 𝔽₂) (H := S)).obj A =>
    p.ofConv x) h
  simpa only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply] using hx

/-- On every nonzero algebra, the coordinate morphism induces the explicit minor isogeny. -/
@[simp↓]
theorem pointsMulEquiv_mapDomain_specialIsogenyCoordinateMap
    (A : Type) [CommRing A] [Algebra 𝔽₂ A] [CharP A 2]
    (q : HopfAlgebra.points (H := S) (CommAlgCat.of 𝔽₂ A)) :
    pointsMulEquiv (A := A) 𝔽₂ 2 (BialgHom.mapDomain specialIsogenyCoordinateMap.hom q) =
      TauCeti.specialIsogeny (pointsMulEquiv (A := A) 𝔽₂ 2 q) := by
  let _ : Nontrivial A := CharP.nontrivial_of_char_ne_one (by decide : 2 ≠ 1)
  rw [mapDomain_specialIsogenyCoordinateMap]
  exact pointsMulEquiv_specialIsogenyPoints _ q

private theorem specialIsogenyPoints_square (A : CommAlgCat.{0} 𝔽₂)
    (q : HopfAlgebra.points (H := S) A) :
    specialIsogenyPoints A (specialIsogenyPoints A q) =
      AlgHom.mapValue (FiniteField.frobeniusAlgHom 𝔽₂ A) q := by
  cases subsingleton_or_nontrivial A with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    let _ : CharP A 2 := charP_of_injective_algebraMap (algebraMap 𝔽₂ A).injective 2
    apply (pointsMulEquiv (A := A) 𝔽₂ 2).injective
    rw [pointsMulEquiv_specialIsogenyPoints, pointsMulEquiv_specialIsogenyPoints,
      pointsMulEquiv_mapValue, TauCeti.specialIsogeny_specialIsogeny]
    congr 1

/-- The square of the exceptional coordinate endomorphism is the Frobenius morphism. -/
@[simp]
theorem specialIsogenyCoordinateMap_comp_self :
    specialIsogenyCoordinateMap ≫ specialIsogenyCoordinateMap =
      CommHopfAlgCat.ofHom (frobeniusBialgHom 𝔽₂ S) := by
  let q : HopfAlgebra.points (H := S) (CommAlgCat.of 𝔽₂ S) := toConv (AlgHom.id 𝔽₂ S)
  have h := specialIsogenyPoints_square (CommAlgCat.of 𝔽₂ S) q
  rw [← mapDomain_specialIsogenyCoordinateMap,
    ← mapDomain_specialIsogenyCoordinateMap] at h
  have hfun := congrArg ofConv h
  apply CommHopfAlgCat.hom_ext
  ext x
  have hx := AlgHom.congr_fun hfun x
  simpa only [q, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    AlgHom.id_apply, AlgHom.mapValue_apply, CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    CommHopfAlgCat.hom_ofHom, frobeniusBialgHom_apply,
    FiniteField.coe_frobeniusAlgHom, BialgHom.coe_toAlgHom] using hx

private theorem specialIsogenyCoordinateMap_apply_apply (x : S) :
    specialIsogenyCoordinateMap.hom (specialIsogenyCoordinateMap.hom x) = x ^ 2 := by
  have h := congrArg (fun f => f.hom x) specialIsogenyCoordinateMap_comp_self
  simpa only [CommHopfAlgCat.hom_comp, BialgHom.comp_apply, CommHopfAlgCat.hom_ofHom,
    frobeniusBialgHom_apply, ZMod.card] using h

/-- The exceptional coordinate morphism is finite. -/
theorem finite_specialIsogenyCoordinateMap : specialIsogenyCoordinateMap.hom.toAlgHom.Finite :=
  specialIsogenyCoordinateMap.hom.toAlgHom.finite_of_comp_self_eq_pow (by decide)
    specialIsogenyCoordinateMap_apply_apply

/-- The exceptional morphism is finite and faithfully flat, hence an isogeny. -/
theorem isIsogeny_specialIsogenyCoordinateMap :
    CommHopfAlgCat.IsIsogeny specialIsogenyCoordinateMap := by
  let _ : Algebra.IsGeometricallyReduced 𝔽₂ S := isGeometricallyReduced_of_smooth 𝔽₂ S
  have hinv := RingHom.comap_involutive_of_comp_self_eq_pow
    specialIsogenyCoordinateMap.hom.toAlgHom.toRingHom (by decide : 0 < 2)
      specialIsogenyCoordinateMap_apply_apply
  exact (CommHopfAlgCat.isIsogeny_iff_finite_and_dominant specialIsogenyCoordinateMap).mpr
    ⟨finite_specialIsogenyCoordinateMap, hinv.surjective.denseRange⟩

/-- The special endomorphism of the group scheme `Sp₄` over `𝔽₂`. -/
def specialIsogenyHom : groupScheme 𝔽₂ 2 ⟶ groupScheme 𝔽₂ 2 :=
  eqToHom (groupScheme_def 𝔽₂ 2) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of 𝔽₂)).map specialIsogenyCoordinateMap.op ≫
      eqToHom (groupScheme_def 𝔽₂ 2).symm

/-- The exceptional group-scheme endomorphism is relative spectrum of its coordinate map. -/
theorem specialIsogenyHom_def :
    specialIsogenyHom =
      eqToHom (groupScheme_def 𝔽₂ 2) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of 𝔽₂)).map specialIsogenyCoordinateMap.op ≫
          eqToHom (groupScheme_def 𝔽₂ 2).symm :=
  (rfl)

/-- The square relation as an equality of group-scheme morphisms. -/
theorem specialIsogenyHom_comp_self :
    specialIsogenyHom ≫ specialIsogenyHom =
      eqToHom (groupScheme_def 𝔽₂ 2) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of 𝔽₂)).map
          (CommHopfAlgCat.ofHom (frobeniusBialgHom 𝔽₂ S)).op ≫
            eqToHom (groupScheme_def 𝔽₂ 2).symm := by
  simp only [specialIsogenyHom, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp, ← op_comp, specialIsogenyCoordinateMap_comp_self]

/-- The exceptional group-scheme endomorphism is an isogeny. -/
theorem isIsogeny_specialIsogenyHom : GroupScheme.IsIsogeny specialIsogenyHom := by
  rw [specialIsogenyHom]
  apply GroupScheme.IsIsogeny.comp
  · exact GroupScheme.isIsogeny_of_isIso _
  · apply GroupScheme.IsIsogeny.comp
    · exact (CommHopfAlgCat.isIsogeny_iff_isIsogeny_hopfSpec_map
        specialIsogenyCoordinateMap).mp isIsogeny_specialIsogenyCoordinateMap
    · exact GroupScheme.isIsogeny_of_isIso _

private theorem groupSchemePointMulEquiv_comp_specialIsogenyHom
    (A : Type) [CommRing A] [Algebra 𝔽₂ A]
    (q : HopfAlgebra.points (H := S) (CommAlgCat.of 𝔽₂ A)) :
    groupSchemePointMulEquiv 2 A q ≫ specialIsogenyHom.hom.hom =
      groupSchemePointMulEquiv 2 A
        (BialgHom.mapDomain specialIsogenyCoordinateMap.hom q) := by
  rw [specialIsogenyHom]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := 𝔽₂) A (groupScheme_def 𝔽₂ 2) (groupScheme_def 𝔽₂ 2)
      (groupSchemePointMulEquiv 2 A) (groupSchemePointMulEquiv 2 A)
      (groupSchemePointMulEquiv_apply_left 2 A) (groupSchemePointMulEquiv_apply_left 2 A)
      specialIsogenyCoordinateMap q

/-- On scheme-valued points the exceptional isogeny is the explicit minor map. -/
theorem schemePointsMulEquiv_comp_specialIsogenyHom
    (A : Type) [CommRing A] [Algebra 𝔽₂ A] [CharP A 2]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of 𝔽₂)) ⟶
      (groupScheme 𝔽₂ 2).X) :
    schemePointsMulEquiv 2 A (p ≫ specialIsogenyHom.hom.hom) =
      TauCeti.specialIsogeny (schemePointsMulEquiv 2 A p) := by
  obtain ⟨q, rfl⟩ := (groupSchemePointMulEquiv 2 A).surjective p
  rw [groupSchemePointMulEquiv_comp_specialIsogenyHom,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    pointsMulEquiv_mapDomain_specialIsogenyCoordinateMap]

end

end TauCeti.Symplectic
