/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Action
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Module.QuasiIso

/-!
# The derived vertex autoequivalences

The positive and inverse vertex tensor functors on the homotopy category of unbounded
cochain complexes of internally graded zigzag modules descend through the standard
localization `DerivedCategory.Qh`. The two descended functors form an autoequivalence
of the ordinary derived category of graded modules supplied by `HasDerivedCategory`.

The inverse functor is the separately descended inverse tensor functor. The unit identifies
the identity functor with the positive functor followed by the inverse, and the counit
identifies the inverse followed by the positive functor with the identity. The lifting
isomorphisms express compatibility of both descended functors with `DerivedCategory.Qh`.

The internal integer grading belongs to the graded modules; the independent external
integer index is the cohomological degree of their cochain complexes. The derived category
is formed from these complexes in `GradedModuleCat`, whose differentials preserve the
internal grading. The coefficient ring, finite graph and module universe are those of
the vertex homotopy autoequivalence, with the derived category chosen through the supplied
`HasDerivedCategory` interface.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Functor _root_.HomologicalComplex

universe u w z

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "c" => ComplexShape.up ℤ

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev Mod := GradedModuleCat.{max u w} (Γ).piece

/-- The existing vertex homotopy functor preserves quasi-isomorphisms. -/
theorem zigzagBraidAutoequivalence_map_mem_quasiIso (i : V)
    {K L : HomotopyCategory (GradedModuleCat.{max u w} (Γ).piece) c} (f : K ⟶ L)
    (hf : HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c f) :
    HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c
      ((zigzagBraidAutoequivalence k G i).functor.map f) := by
  obtain ⟨K⟩ := K
  obtain ⟨L⟩ := L
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (Mod.{u, w} k G) c).map_surjective f
  have hg := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).mp hf
  let : QuasiIso g := hg
  -- The homotopy tensor action is a public reducible abbreviation; use its map equation.
  rw [zigzagBraidAutoequivalence_functor, Functor.map₂HomotopyCategory_obj_map]
  -- Retain the bundled totalized endpoints used by the tensor-map QI theorem.
  -- Rewriting only the map leaves its implicit HasHomology arguments indexed by
  -- different endpoint expressions, so normalize the whole quotient-map type first.
  change HomotopyCategory.quasiIso (Mod.{u, w} k G) c
    ((HomotopyCategory.quotient (Mod.{u, w} k G) c).map
      (((GradedModuleCat.bimoduleModuleTensor.{max u w, max u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidComplex k G i)).map g))
  apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
  exact (HomologicalComplex.mem_quasiIso_iff _).mpr
    (quasiIso_zigzagBraidTensor_map.{u, max u w, w} k G i g)

/-- The inverse vertex homotopy functor preserves quasi-isomorphisms. -/
theorem zigzagBraidAutoequivalence_inverse_map_mem_quasiIso (i : V)
    {K L : HomotopyCategory (GradedModuleCat.{max u w} (Γ).piece) c} (f : K ⟶ L)
    (hf : HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c f) :
    HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c
      ((zigzagBraidAutoequivalence k G i).inverse.map f) := by
  obtain ⟨K⟩ := K
  obtain ⟨L⟩ := L
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (Mod.{u, w} k G) c).map_surjective f
  have hg := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).mp hf
  let : QuasiIso g := hg
  -- The public map equation exposes the inverse totalized map before using its QI theorem.
  rw [zigzagBraidAutoequivalence_inverse, Functor.map₂HomotopyCategory_obj_map]
  -- Retain the bundled totalized endpoints used by the tensor-map QI theorem.
  -- Rewriting only the map leaves its implicit HasHomology arguments indexed by
  -- different endpoint expressions, so normalize the whole quotient-map type first.
  change HomotopyCategory.quasiIso (Mod.{u, w} k G) c
    ((HomotopyCategory.quotient (Mod.{u, w} k G) c).map
      (((GradedModuleCat.bimoduleModuleTensor.{max u w, max u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidInverseComplex k G i)).map g))
  apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
  exact (HomologicalComplex.mem_quasiIso_iff _).mpr
    (quasiIso_zigzagBraidInverseTensor_map.{u, max u w, w} k G i g)

private def positiveLocalizer (i : V) :
    LocalizerMorphism (HomotopyCategory.quasiIso (Mod.{u, w} k G) c)
      (HomotopyCategory.quasiIso (Mod.{u, w} k G) c) where
  functor := (zigzagBraidAutoequivalence k G i).functor
  map _ _ f hf := zigzagBraidAutoequivalence_map_mem_quasiIso k G i f hf

private def inverseLocalizer (i : V) :
    LocalizerMorphism (HomotopyCategory.quasiIso (Mod.{u, w} k G) c)
      (HomotopyCategory.quasiIso (Mod.{u, w} k G) c) where
  functor := (zigzagBraidAutoequivalence k G i).inverse
  map _ _ f hf := zigzagBraidAutoequivalence_inverse_map_mem_quasiIso k G i f hf

-- Keep the grading parameters explicit in the section instance binder.
variable [HasDerivedCategory.{z}
  (GradedModuleCat.{max u w} (zigzagAlgebraInternalGrading k G).piece)]

/-- The positive vertex homotopy functor descends to the standard derived category. -/
def zigzagBraidDerivedFunctor (i : V) :
    _root_.DerivedCategory.{z} (GradedModuleCat.{max u w} (Γ).piece) ⥤
      _root_.DerivedCategory.{z} (GradedModuleCat.{max u w} (Γ).piece) :=
  (positiveLocalizer k G i).localizedFunctor
    _root_.DerivedCategory.Qh.{z} _root_.DerivedCategory.Qh.{z}

/-- The inverse vertex homotopy functor descends to the standard derived category. -/
def zigzagBraidDerivedInverseFunctor (i : V) :
    _root_.DerivedCategory.{z} (GradedModuleCat.{max u w} (Γ).piece) ⥤
      _root_.DerivedCategory.{z} (GradedModuleCat.{max u w} (Γ).piece) :=
  (inverseLocalizer k G i).localizedFunctor
    _root_.DerivedCategory.Qh.{z} _root_.DerivedCategory.Qh.{z}

-- These data-valued instances retain the private localizer constructions.
@[no_expose]
instance zigzagBraidDerivedFunctorLifting (i : V) :
    Localization.Lifting (_root_.DerivedCategory.Qh.{z} (C :=
      GradedModuleCat.{max u w} (Γ).piece))
      (HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c)
      ((zigzagBraidAutoequivalence k G i).functor ⋙ _root_.DerivedCategory.Qh.{z})
      (zigzagBraidDerivedFunctor k G i) :=
  (positiveLocalizer k G i).liftingLocalizedFunctor
    _root_.DerivedCategory.Qh.{z} _root_.DerivedCategory.Qh.{z}

@[no_expose]
instance zigzagBraidDerivedInverseFunctorLifting (i : V) :
    Localization.Lifting (_root_.DerivedCategory.Qh.{z} (C :=
      GradedModuleCat.{max u w} (Γ).piece))
      (HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c)
      ((zigzagBraidAutoequivalence k G i).inverse ⋙ _root_.DerivedCategory.Qh.{z})
      (zigzagBraidDerivedInverseFunctor k G i) :=
  (inverseLocalizer k G i).liftingLocalizedFunctor
    _root_.DerivedCategory.Qh.{z} _root_.DerivedCategory.Qh.{z}

/-- The existing vertex homotopy autoequivalence descends, with its inverse, through `Qh`. -/
def zigzagBraidDerivedAutoequivalence (i : V) :
    _root_.DerivedCategory.{z} (GradedModuleCat.{max u w} (Γ).piece) ≌
      _root_.DerivedCategory.{z} (GradedModuleCat.{max u w} (Γ).piece) :=
  -- Localization.equivalence retains the two specified descended functors. Its first
  -- comparison needs functor then inverse to contract to Qh, hence unitIso.symm;
  -- the second needs inverse then functor, hence counitIso.
  Localization.equivalence
    _root_.DerivedCategory.Qh.{z} (HomotopyCategory.quasiIso (Mod.{u, w} k G) c)
    _root_.DerivedCategory.Qh.{z} (HomotopyCategory.quasiIso (Mod.{u, w} k G) c)
    ((zigzagBraidAutoequivalence k G i).functor ⋙ _root_.DerivedCategory.Qh.{z})
    (zigzagBraidDerivedFunctor k G i)
    ((zigzagBraidAutoequivalence k G i).inverse ⋙ _root_.DerivedCategory.Qh.{z})
    (zigzagBraidDerivedInverseFunctor k G i)
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (zigzagBraidAutoequivalence k G i).functor
        (Localization.Lifting.iso _ (HomotopyCategory.quasiIso (Mod.{u, w} k G) c)
          ((zigzagBraidAutoequivalence k G i).inverse ⋙ _root_.DerivedCategory.Qh.{z})
          (zigzagBraidDerivedInverseFunctor k G i)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (zigzagBraidAutoequivalence k G i).unitIso.symm
        _root_.DerivedCategory.Qh.{z} ≪≫ Functor.leftUnitor _)
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (zigzagBraidAutoequivalence k G i).inverse
        (Localization.Lifting.iso _ (HomotopyCategory.quasiIso (Mod.{u, w} k G) c)
          ((zigzagBraidAutoequivalence k G i).functor ⋙ _root_.DerivedCategory.Qh.{z})
          (zigzagBraidDerivedFunctor k G i)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (zigzagBraidAutoequivalence k G i).counitIso
        _root_.DerivedCategory.Qh.{z} ≪≫ Functor.leftUnitor _)

@[simp]
theorem zigzagBraidDerivedAutoequivalence_functor (i : V) :
    (zigzagBraidDerivedAutoequivalence k G i).functor = zigzagBraidDerivedFunctor k G i := (rfl)

@[simp]
theorem zigzagBraidDerivedAutoequivalence_inverse (i : V) :
    (zigzagBraidDerivedAutoequivalence k G i).inverse =
      zigzagBraidDerivedInverseFunctor k G i := (rfl)

end TauCeti
