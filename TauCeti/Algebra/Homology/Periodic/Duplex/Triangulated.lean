/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import TauCeti.Algebra.Homology.Curved.Cone.Triangle
public import TauCeti.Algebra.Homology.Periodic.ParityShift
public import TauCeti.Algebra.Homology.Periodic.Triangulated

/-!
# The triangle equivalence between duplexes and two-periodic complexes

Curved duplexes of curvature zero and genuine two-periodic complexes are equivalent, and both
homotopy categories carry mapping-cone triangulations. This file proves that their existing
equivalence respects the coherent integral shifts and distinguished triangles. Thus the two
constructions give the same triangulated category, rather than merely equivalent additive
categories.

## References

* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and
  Weyl group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3.
* T. Stai, *The triangulated hull of periodic complexes*, Math. Res. Lett. **25** (2018),
  199–236, Section 3.
-/

public section

namespace TauCeti.CurvedDuplex

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w} [Semiring R] [Linear R C]
  {X Y : CurvedDuplex C (0 : R)}

/-- Mathlib's homotopy cofiber of the two-periodic complex map is canonically the periodic
complex obtained from the corresponding curvature-zero duplex cone. -/
noncomputable def homotopyCofiberIsoToPeriodicComplexCone (f : X ⟶ Y) :
    HomologicalComplex.homotopyCofiber ((toPeriodicComplex C R).map f) ≅
      (toPeriodicComplex C R).obj (cone f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 => HomologicalComplex.homotopyCofiber.XIsoBiprod
          ((toPeriodicComplex C R).map f) 0 1 (ComplexShape.up_mk 0 1 rfl)
      | 1 => HomologicalComplex.homotopyCofiber.XIsoBiprod
          ((toPeriodicComplex C R).map f) 1 0 (ComplexShape.up_mk 1 0 rfl))
    (fun
      | 0, 0, h => absurd h (by rw [ComplexShape.up_Rel]; decide)
      | 0, 1, _ => by
          dsimp only
          apply HomologicalComplex.homotopyCofiber.ext_from_X
              ((toPeriodicComplex C R).map f) 1 0 (ComplexShape.up_mk 0 1 rfl)
          · dsimp only [HomologicalComplex.homotopyCofiber]
            rw [HomologicalComplex.homotopyCofiber.inlX_d_assoc
              ((toPeriodicComplex C R).map f) 0 1 0
              (ComplexShape.up_mk 0 1 rfl) (ComplexShape.up_mk 1 0 rfl)]
            simp [biprod_inl_comp_coneD₀]
          · simp [biprod_inr_comp_coneD₀]
      | 1, 0, _ => by
          dsimp only
          apply HomologicalComplex.homotopyCofiber.ext_from_X
              ((toPeriodicComplex C R).map f) 0 1 (ComplexShape.up_mk 1 0 rfl)
          · dsimp only [HomologicalComplex.homotopyCofiber]
            rw [HomologicalComplex.homotopyCofiber.inlX_d_assoc
              ((toPeriodicComplex C R).map f) 1 0 1
              (ComplexShape.up_mk 1 0 rfl) (ComplexShape.up_mk 0 1 rfl)]
            simp [biprod_inl_comp_coneD₁]
          · simp [biprod_inr_comp_coneD₁]
      | 1, 1, h => absurd h (by rw [ComplexShape.up_Rel]; decide))

/-- The cone comparison carries Mathlib's cofiber inclusion to the duplex cone inclusion. -/
@[reassoc]
theorem homotopyCofiber_inr_comp_homotopyCofiberIsoToPeriodicComplexCone_hom
    (f : X ⟶ Y) :
    HomologicalComplex.homotopyCofiber.inr ((toPeriodicComplex C R).map f) ≫
        (homotopyCofiberIsoToPeriodicComplexCone f).hom =
      (toPeriodicComplex C R).map (coneInclusion f) := by
  apply HomologicalComplex.hom_ext_two <;> simp [homotopyCofiberIsoToPeriodicComplexCone]

/-- The cone comparison carries Mathlib's cofiber projection to the duplex cone projection,
followed by the canonical identification of parity shift with signed cyclic shift. -/
@[reassoc]
theorem homotopyCofiberIsoToPeriodicComplexCone_hom_comp_coneProjection (f : X ⟶ Y) :
    (homotopyCofiberIsoToPeriodicComplexCone f).hom ≫
        (toPeriodicComplex C R).map (coneProjection f) ≫
          (parityShiftToPeriodicComplexIso C R).hom.app X =
      PeriodicComplex.coneProjection ((toPeriodicComplex C R).map f) := by
  apply HomologicalComplex.hom_ext_two
  · simp only [HomologicalComplex.comp_f, PeriodicComplex.coneProjection_f]
    simp only [homotopyCofiberIsoToPeriodicComplexCone,
      HomologicalComplex.homotopyCofiber.fstX, HomologicalComplex.homotopyCofiber_X,
      Functor.comp_obj, PeriodicComplex.shiftFunctor_obj_X', toPeriodicComplex_obj_X_zero,
      parityShift_obj_X₀, toPeriodicComplex_map_f_zero, coneProjection_f₀,
      parityShiftToPeriodicComplexIso_hom_f_zero]
    congr!
    exact Category.comp_id _
  · simp only [HomologicalComplex.comp_f, PeriodicComplex.coneProjection_f]
    simp only [homotopyCofiberIsoToPeriodicComplexCone,
      HomologicalComplex.homotopyCofiber.fstX, HomologicalComplex.homotopyCofiber_X,
      Functor.comp_obj, PeriodicComplex.shiftFunctor_obj_X', toPeriodicComplex_obj_X_one,
      parityShift_obj_X₁, toPeriodicComplex_map_f_one, coneProjection_f₁,
      parityShiftToPeriodicComplexIso_hom_f_one]
    congr!
    exact Category.comp_id _

end TauCeti.CurvedDuplex

namespace TauCeti.CurvedDuplex.HomotopyCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (R : Type w) [Semiring R] [Linear R C]

/-- The equivalence from curvature-zero duplexes to two-periodic complexes commutes coherently
with integral shifts. In degree one this is the comparison between parity shift and signed cyclic
shift. -/
noncomputable instance periodicComplexEquivalenceFunctorCommShift :
    (periodicComplexEquivalence C R).functor.CommShift ℤ :=
  Shift.commShiftOfIntertwiningToShift _ (parityShiftEquivalence C (0 : R))
    (periodicComplexEquivalence C R).functor (parityShiftToPeriodicComplexIso C R)

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- In degree one, the shift comparison of the homotopy-category equivalence is the previously
constructed comparison between parity shift and signed cyclic shift. -/
theorem periodicComplexEquivalenceFunctor_commShiftIso_one :
    ((periodicComplexEquivalence C R).functor.commShiftIso (1 : ℤ)) =
      Functor.isoWhiskerRight (shiftFunctorOneIso C (0 : R))
          (periodicComplexEquivalence C R).functor ≪≫
        parityShiftToPeriodicComplexIso C R := by
  rw [shiftFunctorOneIso_def]
  exact Shift.commShiftOfIntertwiningToShift_iso_one _ (parityShiftEquivalence C (0 : R))
    (periodicComplexEquivalence C R).functor (parityShiftToPeriodicComplexIso C R)

variable {C R}

omit [HasZeroObject C] in
/-- After transport to two-periodic complexes, the third morphism of a duplex cone triangle is
the third morphism of Mathlib's mapping-cone triangle, read through the cone comparison. -/
theorem periodicComplexEquivalenceFunctor_mapTriangle_coneTriangle_mor₃
    {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    ((periodicComplexEquivalence C R).functor.mapTriangle.obj (coneTriangle f)).mor₃ =
      eqToHom (by simp) ≫
        (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
          (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone f).inv ≫
        (PeriodicComplex.mappingConeTriangle ((CurvedDuplex.toPeriodicComplex C R).map f)).mor₃ ≫
        eqToHom (by simp) := by
  -- The complex-level comparison of cone projections, passed to the quotient.
  have h := (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).congr_map
    ((Iso.eq_inv_comp _).2
      (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone_hom_comp_coneProjection f))
  rw [Functor.map_comp, Functor.map_comp] at h
  simp [coneTriangle, periodicComplexEquivalenceFunctor_commShiftIso_one,
    Functor.congr_hom periodicComplexEquivalence_functor, eqToHom_map, reassoc_of% h]

/-- The image of a duplex cone triangle under the periodic-complex equivalence is canonically
isomorphic to the corresponding mapping-cone triangle of two-periodic complexes. -/
noncomputable def mapConeTriangleIso {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (periodicComplexEquivalence C R).functor.mapTriangle.obj (coneTriangle f) ≅
      PeriodicComplex.mappingConeTriangle ((CurvedDuplex.toPeriodicComplex C R).map f) := by
  let F := (periodicComplexEquivalence C R).functor
  let G := toPeriodicComplex C R
  let hF : F = G := periodicComplexEquivalence_functor
  let e₁ : F.obj ((nullHomotopic C (0 : R)).quotientFunctor.obj X) ≅
      G.obj ((nullHomotopic C (0 : R)).quotientFunctor.obj X) :=
    eqToIso (Functor.congr_obj hF _)
  let e₂ : F.obj ((nullHomotopic C (0 : R)).quotientFunctor.obj Y) ≅
      G.obj ((nullHomotopic C (0 : R)).quotientFunctor.obj Y) :=
    eqToIso (Functor.congr_obj hF _)
  let e₃ : F.obj ((nullHomotopic C (0 : R)).quotientFunctor.obj (cone f)) ≅
      G.obj ((nullHomotopic C (0 : R)).quotientFunctor.obj (cone f)) :=
    eqToIso (Functor.congr_obj hF _)
  refine Triangle.isoMk _ _ e₁ e₂
    (e₃ ≪≫
      (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).mapIso
        (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone f).symm) ?_ ?_ ?_
  · simp [e₁, e₂, F, G, Functor.congr_hom hF]
  · simp [e₂, e₃, F, G, Functor.congr_hom hF, ← Functor.map_comp,
      ← CurvedDuplex.homotopyCofiber_inr_comp_homotopyCofiberIsoToPeriodicComplexCone_hom]
  · rw [periodicComplexEquivalenceFunctor_mapTriangle_coneTriangle_mor₃]
    simp [e₁, e₃, eqToHom_map]

omit [HasZeroObject C] in
/-- The first component of the cone-triangle comparison is the canonical transport. -/
@[simp]
theorem mapConeTriangleIso_hom_hom₁ {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (mapConeTriangleIso f).hom.hom₁ = eqToHom (by simp) := by
  unfold mapConeTriangleIso; rfl

omit [HasZeroObject C] in
/-- The second component of the cone-triangle comparison is the canonical transport. -/
@[simp]
theorem mapConeTriangleIso_hom_hom₂ {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (mapConeTriangleIso f).hom.hom₂ = eqToHom (by simp) := by
  unfold mapConeTriangleIso; rfl

omit [HasZeroObject C] in
/-- The third component of the cone-triangle comparison is the canonical transport followed by
the inverse of the cone comparison, passed to the homotopy category. -/
@[simp]
theorem mapConeTriangleIso_hom_hom₃ {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (mapConeTriangleIso f).hom.hom₃ =
      eqToHom (by simp) ≫ (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
        (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone f).inv := by
  unfold mapConeTriangleIso; rfl

omit [HasZeroObject C] in
/-- The first component of the inverse cone-triangle comparison is the canonical transport. -/
@[simp]
theorem mapConeTriangleIso_inv_hom₁ {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (mapConeTriangleIso f).inv.hom₁ = eqToHom (by simp) := by
  unfold mapConeTriangleIso; rfl

omit [HasZeroObject C] in
/-- The second component of the inverse cone-triangle comparison is the canonical transport. -/
@[simp]
theorem mapConeTriangleIso_inv_hom₂ {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (mapConeTriangleIso f).inv.hom₂ = eqToHom (by simp) := by
  unfold mapConeTriangleIso; rfl

omit [HasZeroObject C] in
/-- The third component of the inverse cone-triangle comparison is the cone comparison, passed to
the homotopy category, followed by the canonical transport. -/
@[simp]
theorem mapConeTriangleIso_inv_hom₃ {X Y : CurvedDuplex C (0 : R)} (f : X ⟶ Y) :
    (mapConeTriangleIso f).inv.hom₃ =
      (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
          (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone f).hom ≫ eqToHom (by simp) := by
  unfold mapConeTriangleIso; rfl

/-- The equivalence from curvature-zero duplexes to two-periodic complexes preserves
distinguished triangles. -/
noncomputable instance periodicComplexEquivalenceFunctorIsTriangulated :
    (periodicComplexEquivalence C R).functor.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨X, Y, f, ⟨e⟩⟩ := (mem_distTriang_iff_nonempty_iso_coneTriangle T).1 hT
    exact isomorphic_distinguished _
      (PeriodicComplex.mappingCone_mem_distTriang ((CurvedDuplex.toPeriodicComplex C R).map f)) _
      ((periodicComplexEquivalence C R).functor.mapTriangle.mapIso e ≪≫ mapConeTriangleIso f)

/-- **Curvature-zero duplexes and two-periodic complexes have triangle-equivalent homotopy
categories.** The forward functor uses the explicit parity-shift comparison, and the inverse
shift comparison is its canonical mate. -/
theorem periodicComplexEquivalenceIsTriangulated :
    letI := (periodicComplexEquivalence C R).commShiftInverse ℤ
    letI := (periodicComplexEquivalence C R).commShift_of_functor ℤ
    (periodicComplexEquivalence C R).IsTriangulated := by
  let := (periodicComplexEquivalence C R).commShiftInverse ℤ
  let := (periodicComplexEquivalence C R).commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ inferInstance

end TauCeti.CurvedDuplex.HomotopyCategory
