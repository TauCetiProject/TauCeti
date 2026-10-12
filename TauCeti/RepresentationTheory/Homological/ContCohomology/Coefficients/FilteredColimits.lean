/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FilteredColimits
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Filtered coefficient colimits in explicit low-degree cohomology

The explicit groups `H0 G M`, `H1 G M` and `H2 G M` form functors from smooth discrete
representations to additive groups. Their arrows are the explicit coefficient maps, so their
image cocones retain the calculational maps on invariant elements and cocycle representatives.

The natural comparison isomorphisms identify these functors with canonical continuous
cohomology after forgetting topology and scalars. The comparisons in degrees zero and one
apply to any topological group; the degree-two comparison requires local compactness.

For a compact topological group all three explicit functors preserve filtered coefficient
colimits. Thus a filtered colimit cocone of smooth discrete representations gives a colimit
cocone of explicit cohomology groups in each of these degrees. No total disconnectedness
assumption is needed.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.5.1).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §2.2, Proposition 8.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ContCohomology

universe w' w v u

variable {R : Type v} [Ring R] [TopologicalSpace R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction

private instance (X : SmoothDiscreteTopRep.{v, u, u} R G) : DiscreteTopology X.obj.V :=
  X.property.discreteTopology

private instance (X : SmoothDiscreteTopRep.{v, u, u} R G) : ContinuousSMul G X.obj.V :=
  X.property.continuousSMul

/-- The coefficient map of a morphism in the smooth discrete category, forgetting scalars. -/
private def coeff {X Y : SmoothDiscreteTopRep.{v, u, u} R G} (f : X ⟶ Y) :
    X.obj.V →+[G] Y.obj.V :=
  { f.hom.hom.toLinearMap.toAddMonoidHom with
    map_smul' := fun g x ↦ TopRep.hom_comm_apply f.hom g x }

/-- Explicit degree-zero cohomology, functorial in smooth discrete coefficients. -/
def explicitH0Functor : SmoothDiscreteTopRep.{v, u, u} R G ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (H0 G X.obj.V)
  map {X Y} f := AddCommGrpCat.ofHom (explicitCoeff0 G X.obj.V (coeff G f))
  map_id X := by
    apply AddCommGrpCat.hom_ext
    exact explicitCoeff0_id G X.obj.V
  map_comp {X Y Z} f g := by
    apply AddCommGrpCat.hom_ext
    exact explicitCoeff0_comp G X.obj.V (coeff G f) (coeff G g)

/-- Explicit degree-one cohomology, functorial in smooth discrete coefficients. -/
def explicitH1Functor : SmoothDiscreteTopRep.{v, u, u} R G ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (H1 G X.obj.V)
  map {X Y} f := AddCommGrpCat.ofHom
    (explicitCoeff1 G X.obj.V (coeff G f) continuous_of_discreteTopology)
  map_id X := by
    apply AddCommGrpCat.hom_ext
    exact explicitCoeff1_id G X.obj.V
  map_comp {X Y Z} f g := by
    apply AddCommGrpCat.hom_ext
    exact explicitCoeff1_comp G X.obj.V (coeff G f) (coeff G g)
      continuous_of_discreteTopology continuous_of_discreteTopology

/-- Explicit degree-two cohomology, functorial in smooth discrete coefficients. -/
def explicitH2Functor : SmoothDiscreteTopRep.{v, u, u} R G ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (H2 G X.obj.V)
  map {X Y} f := AddCommGrpCat.ofHom
    (explicitCoeff2 G X.obj.V (coeff G f) continuous_of_discreteTopology)
  map_id X := by
    apply AddCommGrpCat.hom_ext
    exact explicitCoeff2_id G X.obj.V
  map_comp {X Y Z} f g := by
    apply AddCommGrpCat.hom_ext
    exact explicitCoeff2_comp G X.obj.V (coeff G f) (coeff G g)
      continuous_of_discreteTopology continuous_of_discreteTopology

/-- The degree-zero explicit-to-canonical comparison is natural in the coefficient module. -/
def explicitH0FunctorIsoContinuousCohomology : explicitH0Functor (R := R) G ≅
    (smoothDiscreteι R G ⋙ ContinuousCohomology.continuousCohomologyFunctor R G 0) ⋙
      (forget₂ (TopModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
  let F := forget₂ (TopModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat
  let e : explicitH0Functor (R := R) G ≅
      (smoothDiscreteι R G ⋙ TopRep.invariantsFunctor R G) ⋙ F :=
    NatIso.ofComponents (fun X ↦ Iso.refl (AddCommGrpCat.of (H0 G X.obj.V))) (by
      intro X Y f
      ext x
      apply Subtype.ext
      exact coe_explicitCoeff0 G X.obj.V (coeff G f) x)
  e ≪≫ Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (smoothDiscreteι R G)
      (ContinuousCohomology.zeroIsoNatIso R G).symm) F

/-- The degree-one explicit-to-canonical comparison is natural in the coefficient module. -/
def explicitH1FunctorIsoContinuousCohomology : explicitH1Functor (R := R) G ≅
    (smoothDiscreteι R G ⋙ ContinuousCohomology.continuousCohomologyFunctor R G 1) ⋙
      (forget₂ (TopModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
  NatIso.ofComponents (fun X ↦
    X.obj.explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddCommGrpIso) (by
    intro X Y f
    ext x
    -- Expose the new functor's map and the forgetful-functor wrappers; neither changes values.
    change Y.obj.explicitH1AddEquivContinuousCohomologyOfDiscrete
      (explicitCoeff1 G X.obj.V (coeff G f) continuous_of_discreteTopology x) =
      (ContinuousCohomology.coeffMap f.hom 1)
        (X.obj.explicitH1AddEquivContinuousCohomologyOfDiscrete x)
    rw [explicitCoeff1_eq_explicitMap1, ContinuousCohomology.coeffMap_def]
    exact (X.obj.explicitH1AddEquivContinuousCohomologyOfDiscrete_map Y.obj
      (ContinuousMonoidHom.id G) f.hom (coeff G f).toAddMonoidHom (fun _ ↦ rfl)
      (map_smul (coeff G f)) x).symm)

/-- The degree-two explicit-to-canonical comparison is natural in the coefficient module. -/
def explicitH2FunctorIsoContinuousCohomology [LocallyCompactSpace G] :
    explicitH2Functor (R := R) G ≅
    (smoothDiscreteι R G ⋙ ContinuousCohomology.continuousCohomologyFunctor R G 2) ⋙
      (forget₂ (TopModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) :=
  NatIso.ofComponents (fun X ↦
    X.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete.toAddCommGrpIso) (by
    intro X Y f
    ext x
    -- Expose the new functor's map and the forgetful-functor wrappers; neither changes values.
    change Y.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete
      (explicitCoeff2 G X.obj.V (coeff G f) continuous_of_discreteTopology x) =
      (ContinuousCohomology.coeffMap f.hom 2)
        (X.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete x)
    rw [explicitCoeff2_eq_explicitMap2, ContinuousCohomology.coeffMap_def]
    exact (X.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete_map Y.obj
      (ContinuousMonoidHom.id G) f.hom (coeff G f).toAddMonoidHom (fun _ ↦ rfl)
      (map_smul (coeff G f)) x).symm)

omit [IsTopologicalGroup G] in
/-- The degree-zero functor takes a coefficient module to its invariant subgroup. -/
@[simp]
theorem explicitH0Functor_obj (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    (explicitH0Functor G).obj X = AddCommGrpCat.of (H0 G X.obj.V) :=
  (rfl)

/-- The degree-one functor takes a coefficient module to its explicit cocycle quotient. -/
@[simp]
theorem explicitH1Functor_obj (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    letI := X.property.continuousSMul
    (explicitH1Functor G).obj X = AddCommGrpCat.of (H1 G X.obj.V) :=
  (rfl)

/-- The degree-two functor takes a coefficient module to its explicit cocycle quotient. -/
@[simp]
theorem explicitH2Functor_obj (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    letI := X.property.continuousSMul
    (explicitH2Functor G).obj X = AddCommGrpCat.of (H2 G X.obj.V) :=
  (rfl)

omit [IsTopologicalGroup G] in
/-- The degree-zero functor acts by the explicit coefficient map on invariant elements. -/
@[simp]
theorem explicitH0Functor_map {X Y : SmoothDiscreteTopRep.{v, u, u} R G} (f : X ⟶ Y) :
    eqToHom (explicitH0Functor_obj G X).symm ≫ (explicitH0Functor G).map f ≫
      eqToHom (explicitH0Functor_obj G Y) = AddCommGrpCat.ofHom
      (explicitCoeff0 G X.obj.V
        { f.hom.hom.toLinearMap.toAddMonoidHom with
          map_smul' := fun g x ↦ TopRep.hom_comm_apply f.hom g x }) :=
  (rfl)

/-- The degree-one functor acts by the explicit coefficient map of the underlying additive map. -/
@[simp]
theorem explicitH1Functor_map {X Y : SmoothDiscreteTopRep.{v, u, u} R G} (f : X ⟶ Y) :
    letI := X.property.discreteTopology
    letI := X.property.continuousSMul
    letI := Y.property.continuousSMul
    eqToHom (explicitH1Functor_obj G X).symm ≫ (explicitH1Functor G).map f ≫
      eqToHom (explicitH1Functor_obj G Y) = AddCommGrpCat.ofHom
      (explicitCoeff1 G X.obj.V
        { f.hom.hom.toLinearMap.toAddMonoidHom with
          map_smul' := fun g x ↦ TopRep.hom_comm_apply f.hom g x }
        continuous_of_discreteTopology) :=
  (rfl)

/-- The degree-two functor acts by the explicit coefficient map of the underlying additive map. -/
@[simp]
theorem explicitH2Functor_map {X Y : SmoothDiscreteTopRep.{v, u, u} R G} (f : X ⟶ Y) :
    letI := X.property.discreteTopology
    letI := X.property.continuousSMul
    letI := Y.property.continuousSMul
    eqToHom (explicitH2Functor_obj G X).symm ≫ (explicitH2Functor G).map f ≫
      eqToHom (explicitH2Functor_obj G Y) = AddCommGrpCat.ofHom
      (explicitCoeff2 G X.obj.V
        { f.hom.hom.toLinearMap.toAddMonoidHom with
          map_smul' := fun g x ↦ TopRep.hom_comm_apply f.hom g x }
        continuous_of_discreteTopology) :=
  (rfl)

/-- The degree-zero natural comparison is the inverse of the canonical invariants comparison. -/
@[simp]
theorem explicitH0FunctorIsoContinuousCohomology_hom_app
    (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    eqToHom (explicitH0Functor_obj G X).symm ≫
      (explicitH0FunctorIsoContinuousCohomology G).hom.app X =
      (forget₂ (TopModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat).map
        (_root_.ContinuousCohomology.zeroIso X.obj).inv :=
  congrArg (forget₂ (TopModuleCat R) (ModuleCat R) ⋙
    forget₂ (ModuleCat R) AddCommGrpCat).map
      (ContinuousCohomology.zeroIsoNatIso_inv_app X.obj)

/-- The inverse degree-zero natural comparison is the canonical invariants comparison. -/
@[simp]
theorem explicitH0FunctorIsoContinuousCohomology_inv_app
    (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    (explicitH0FunctorIsoContinuousCohomology G).inv.app X ≫ eqToHom (explicitH0Functor_obj G X) =
      (forget₂ (TopModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat).map
        (_root_.ContinuousCohomology.zeroIso X.obj).hom :=
  congrArg (forget₂ (TopModuleCat R) (ModuleCat R) ⋙
    forget₂ (ModuleCat R) AddCommGrpCat).map
      (ContinuousCohomology.zeroIsoNatIso_hom_app X.obj)

/-- The degree-one natural comparison acts by the existing additive comparison. -/
@[simp]
theorem explicitH1FunctorIsoContinuousCohomology_hom_app (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    letI := X.property.discreteTopology
    letI := X.property.continuousSMul
    eqToHom (explicitH1Functor_obj G X).symm ≫
      (explicitH1FunctorIsoContinuousCohomology G).hom.app X =
      X.obj.explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddCommGrpIso.hom :=
  (rfl)

/-- The inverse degree-one natural comparison acts by the inverse additive comparison. -/
@[simp]
theorem explicitH1FunctorIsoContinuousCohomology_inv_app (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    letI := X.property.discreteTopology
    letI := X.property.continuousSMul
    (explicitH1FunctorIsoContinuousCohomology G).inv.app X ≫ eqToHom (explicitH1Functor_obj G X) =
      X.obj.explicitH1AddEquivContinuousCohomologyOfDiscrete.toAddCommGrpIso.inv :=
  (rfl)

/-- The degree-two natural comparison acts by the existing additive comparison. -/
@[simp]
theorem explicitH2FunctorIsoContinuousCohomology_hom_app [LocallyCompactSpace G]
    (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    letI := X.property.discreteTopology
    letI := X.property.continuousSMul
    eqToHom (explicitH2Functor_obj G X).symm ≫
      (explicitH2FunctorIsoContinuousCohomology G).hom.app X =
      X.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete.toAddCommGrpIso.hom :=
  (rfl)

/-- The inverse degree-two natural comparison acts by the inverse additive comparison. -/
@[simp]
theorem explicitH2FunctorIsoContinuousCohomology_inv_app [LocallyCompactSpace G]
    (X : SmoothDiscreteTopRep.{v, u, u} R G) :
    letI := X.property.discreteTopology
    letI := X.property.continuousSMul
    (explicitH2FunctorIsoContinuousCohomology G).inv.app X ≫ eqToHom (explicitH2Functor_obj G X) =
      X.obj.explicitH2AddEquivContinuousCohomologyOfDiscrete.toAddCommGrpIso.inv :=
  (rfl)

/-- Explicit degree-zero continuous cohomology of a compact group preserves filtered coefficient
colimits, with the explicit coefficient maps as cocone legs. -/
theorem explicitH0Functor_preservesFilteredColimits [CompactSpace G]
    [UnivLE.{w', u}] [UnivLE.{w, u}] :
    PreservesFilteredColimitsOfSize.{w', w} (explicitH0Functor (R := R) G) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesFilteredColimitsOfSize.{w', w}
        (smoothDiscreteι.{v, u, u} R G ⋙
          ContinuousCohomology.continuousCohomologyFunctor R G 0) :=
      ContinuousCohomology.continuousCohomology_preservesFilteredColimits.{w', w, v, u} 0
    exact preservesColimitsOfShape_of_natIso
      (explicitH0FunctorIsoContinuousCohomology (R := R) G).symm

/-- Explicit first continuous cohomology of a compact group preserves filtered coefficient
colimits, with the explicit coefficient maps as cocone legs. -/
theorem explicitH1Functor_preservesFilteredColimits [CompactSpace G]
    [UnivLE.{w', u}] [UnivLE.{w, u}] :
    PreservesFilteredColimitsOfSize.{w', w} (explicitH1Functor (R := R) G) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesFilteredColimitsOfSize.{w', w}
        (smoothDiscreteι.{v, u, u} R G ⋙
          ContinuousCohomology.continuousCohomologyFunctor R G 1) :=
      ContinuousCohomology.continuousCohomology_preservesFilteredColimits.{w', w, v, u} 1
    exact preservesColimitsOfShape_of_natIso
      (explicitH1FunctorIsoContinuousCohomology (R := R) G).symm

/-- Explicit second continuous cohomology of a compact group preserves filtered coefficient
colimits, with the explicit coefficient maps as cocone legs. -/
theorem explicitH2Functor_preservesFilteredColimits [CompactSpace G]
    [UnivLE.{w', u}] [UnivLE.{w, u}] :
    PreservesFilteredColimitsOfSize.{w', w} (explicitH2Functor (R := R) G) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesFilteredColimitsOfSize.{w', w}
        (smoothDiscreteι.{v, u, u} R G ⋙
          ContinuousCohomology.continuousCohomologyFunctor R G 2) :=
      ContinuousCohomology.continuousCohomology_preservesFilteredColimits.{w', w, v, u} 2
    exact preservesColimitsOfShape_of_natIso
      (explicitH2FunctorIsoContinuousCohomology (R := R) G).symm

end TauCeti.ContCohomology
