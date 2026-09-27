/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Duplex
public import TauCeti.Algebra.Homology.Periodic.Shift

/-!
# Parity shift and the shift of two-periodic complexes

Under the equivalence between curvature-zero duplexes and two-periodic complexes, swapping
the parity pieces and negating both differentials is the shift by one. The same comparison
descends through null homotopies to the equivalence of homotopy categories.

The two shift conventions follow I. Frenkel, M. Khovanov, and O. Schiffmann,
*Homological realization of Nakajima varieties and Weyl group actions*, Compos. Math. 141
(2005), §§2–3, and T. Stai, *The triangulated hull of periodic complexes*, Math. Res. Lett. 25
(2018), §3, respectively.
-/

public section

universe w v u

namespace TauCeti.CurvedDuplex

open CategoryTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  (R : Type w) [Semiring R] [Linear R C]

/-- The periodic complex of the parity shift is canonically isomorphic to the degree-one
shift of the periodic complex. The components of this isomorphism are identities. -/
def parityShiftToPeriodicComplexIso :
    parityShift C (0 : R) ⋙ toPeriodicComplex C R ≅
      toPeriodicComplex C R ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ) :=
  NatIso.ofComponents (fun X => HomologicalComplex.Hom.isoOfComponents
    (fun
      | 0 => Iso.refl _
      | 1 => Iso.refl _)
    (fun
      | 0, 0, h => absurd h (by rw [ComplexShape.up_Rel]; decide)
      | 0, 1, _ => by
          -- Reduce the dependent `ZMod 2` indexing before simplifying the identity maps.
          change 𝟙 X.X₁ ≫ ((1 : ℤ).negOnePow • X.d₁) = (-X.d₁) ≫ 𝟙 X.X₀
          simp
      | 1, 0, _ => by
          -- Reduce the dependent `ZMod 2` indexing before simplifying the identity maps.
          change 𝟙 X.X₀ ≫ ((1 : ℤ).negOnePow • X.d₀) = (-X.d₀) ≫ 𝟙 X.X₁
          simp
      | 1, 1, h => absurd h (by rw [ComplexShape.up_Rel]; decide)))
    (fun f => by
      apply HomologicalComplex.hom_ext_two
      · -- The two components are `f₁` and `f₀` after cyclic reindexing.
        change f.f₁ ≫ 𝟙 _ = 𝟙 _ ≫ f.f₁
        simp
      · change f.f₀ ≫ 𝟙 _ = 𝟙 _ ≫ f.f₀
        simp)

/-- The even component of the shift comparison is the identity on the old odd component. -/
@[simp]
theorem parityShiftToPeriodicComplexIso_hom_f_zero (X : CurvedDuplex C (0 : R)) :
    ((parityShiftToPeriodicComplexIso C R).hom.app X).f 0 = 𝟙 X.X₁ := by
  simp [parityShiftToPeriodicComplexIso]
  rfl

/-- The odd component of the shift comparison is the identity on the old even component. -/
@[simp]
theorem parityShiftToPeriodicComplexIso_hom_f_one (X : CurvedDuplex C (0 : R)) :
    ((parityShiftToPeriodicComplexIso C R).hom.app X).f 1 = 𝟙 X.X₀ := by
  simp [parityShiftToPeriodicComplexIso]
  rfl

@[simp]
theorem parityShiftToPeriodicComplexIso_inv_f_zero (X : CurvedDuplex C (0 : R)) :
    ((parityShiftToPeriodicComplexIso C R).inv.app X).f 0 = 𝟙 X.X₁ := by
  simp [parityShiftToPeriodicComplexIso]
  rfl

@[simp]
theorem parityShiftToPeriodicComplexIso_inv_f_one (X : CurvedDuplex C (0 : R)) :
    ((parityShiftToPeriodicComplexIso C R).inv.app X).f 1 = 𝟙 X.X₀ := by
  simp [parityShiftToPeriodicComplexIso]
  rfl

namespace HomotopyCategory

/-- The homotopy-category equivalence transports the parity shift to the degree-one
periodic shift. -/
noncomputable def parityShiftToPeriodicComplexIso :
    (parityShiftEquivalence C (0 : R)).functor ⋙ (periodicComplexEquivalence C R).functor ≅
      (periodicComplexEquivalence C R).functor ⋙
        CategoryTheory.shiftFunctor
          (_root_.HomotopyCategory C (ComplexShape.up (ZMod 2))) (1 : ℤ) :=
  Quotient.natIsoLift (nullHomotopic C (0 : R)).rel
    -- On the quotient functor, replace parity shift and the duplex equivalence by their
    -- complex-level functors, apply the comparison above, then commute shift with quotient.
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso (HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor
          (C := C) (R := R) (w := (0 : R)))) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (eqToIso (quotientFunctor_comp_periodicComplexEquivalence_functor
          (C := C) (R := R))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CurvedDuplex.parityShiftToPeriodicComplexIso C R) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).commShiftIso 1) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso (quotientFunctor_comp_periodicComplexEquivalence_functor
          (C := C) (R := R)).symm) _ ≪≫
      Functor.associator _ _ _)

/-- On a duplex, the homotopy-category comparison is the image of the complex-level
comparison, followed by the quotient's shift comparison. -/
@[simp]
theorem parityShiftToPeriodicComplexIso_hom_app_quotient_obj
    (X : CurvedDuplex C (0 : R)) :
    (parityShiftToPeriodicComplexIso C R).hom.app
        ((nullHomotopic C (0 : R)).quotientFunctor.obj X) =
      eqToHom (by simp [periodicComplexEquivalence_functor]) ≫
        (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
          ((CurvedDuplex.parityShiftToPeriodicComplexIso C R).hom.app X) ≫
        ((_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).commShiftIso
          (1 : ℤ)).hom.app ((CurvedDuplex.toPeriodicComplex C R).obj X) ≫
        eqToHom (by simp [periodicComplexEquivalence_functor]) := by
  simp [parityShiftToPeriodicComplexIso, eqToHom_map]

/-- On a duplex, the inverse homotopy-category comparison is the quotient's inverse shift
comparison followed by the image of the inverse complex-level comparison. -/
@[simp]
theorem parityShiftToPeriodicComplexIso_inv_app_quotient_obj
    (X : CurvedDuplex C (0 : R)) :
    (parityShiftToPeriodicComplexIso C R).inv.app
        ((nullHomotopic C (0 : R)).quotientFunctor.obj X) =
      eqToHom (by simp [periodicComplexEquivalence_functor]) ≫
        ((_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).commShiftIso
          (1 : ℤ)).inv.app ((CurvedDuplex.toPeriodicComplex C R).obj X) ≫
        (_root_.HomotopyCategory.quotient C (ComplexShape.up (ZMod 2))).map
          ((CurvedDuplex.parityShiftToPeriodicComplexIso C R).inv.app X) ≫
        eqToHom (by simp [periodicComplexEquivalence_functor]) := by
  simp [parityShiftToPeriodicComplexIso, eqToHom_map, Category.assoc]

end HomotopyCategory

end TauCeti.CurvedDuplex
