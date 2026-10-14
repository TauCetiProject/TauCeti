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
  · dsimp only [coneTriangle, Triangle.mk_obj₁, Triangle.mk_mor₃]
    -- The shift comparison was generated from parity shift, so its degree-one component
    -- cancels the inverse comparison occurring in the duplex cone projection.
    simp only [e₁, e₃, F, G, Functor.congr_hom hF,
      periodicComplexEquivalenceFunctor_commShiftIso_one,
      Functor.comp_obj, Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_obj₂,
      Triangle.mk_obj₃, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      PeriodicComplex.mappingConeTriangle_obj₁, parityShiftCompQuotientFunctorIso_hom_app,
      Functor.map_neg, Preadditive.neg_comp, Category.assoc, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, eqToIso.hom,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_map,
      PeriodicComplex.mappingConeTriangle_obj₃, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, PeriodicComplex.mappingConeTriangle_mor₃, Preadditive.comp_neg, neg_inj]
    rw [← G.map_comp_assoc]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    simp only [G, eqToHom_map, toPeriodicComplex_obj_quotientFunctor_obj,
      toPeriodicComplex_map_quotientFunctor_map, Functor.map_comp,
      parityShiftToPeriodicComplexIso_hom_app_quotient_obj, Functor.comp_obj, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc]
    simp only [Category.id_comp]
    rw [cancel_epi]
    -- It remains to transport the complex-level projection identity through the quotient.
    have h :
        (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
              ((CurvedDuplex.toPeriodicComplex C R).map (coneProjection f)) ≫
            (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
              ((CurvedDuplex.parityShiftToPeriodicComplexIso C R).hom.app X) =
          (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
                (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone f).inv ≫
            (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
              (PeriodicComplex.coneProjection ((CurvedDuplex.toPeriodicComplex C R).map f)) := by
      simp only [← Functor.map_comp]
      apply congrArg
      rw [← cancel_epi (CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone f).hom]
      simp [CurvedDuplex.homotopyCofiberIsoToPeriodicComplexCone_hom_comp_coneProjection]
    rw [← Category.assoc, h]
    simp only [Category.assoc]

/-- The equivalence from curvature-zero duplexes to two-periodic complexes preserves
distinguished triangles. -/
noncomputable instance periodicComplexEquivalenceFunctorIsTriangulated :
    (periodicComplexEquivalence C R).functor.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨X, Y, f, ⟨e⟩⟩ := (mem_distTriang_iff_nonempty_iso_coneTriangle T).1 hT
    exact isomorphic_distinguished _
      (PeriodicComplex.mappingCone_mem_distTriang ((CurvedDuplex.toPeriodicComplex C R).map f)) _
      ((periodicComplexEquivalence C R).functor.mapTriangle.mapIso e ≪≫ mapConeTriangleIso f)

/-- The inverse periodic-complex equivalence commutes with integral shifts via the canonical
mate of the forward shift comparison. -/
@[instance_reducible]
noncomputable def periodicComplexEquivalenceInverseCommShift :
    (periodicComplexEquivalence C R).inverse.CommShift ℤ :=
  (periodicComplexEquivalence C R).commShiftInverse ℤ

/-- **Curvature-zero duplexes and two-periodic complexes have triangle-equivalent homotopy
categories.** The forward functor uses the explicit parity-shift comparison, and the inverse
shift comparison is its canonical mate. -/
theorem periodicComplexEquivalenceIsTriangulated :
    letI := periodicComplexEquivalenceInverseCommShift (C := C) (R := R)
    letI := (periodicComplexEquivalence C R).commShift_of_functor ℤ
    (periodicComplexEquivalence C R).IsTriangulated := by
  let := periodicComplexEquivalenceInverseCommShift (C := C) (R := R)
  let := (periodicComplexEquivalence C R).commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ inferInstance

end TauCeti.CurvedDuplex.HomotopyCategory
