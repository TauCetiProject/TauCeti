/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.SimpleResolution
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Module
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Simple

/-!
# The vertex simple as a path algebra module

The equivalence between quiver representations and left modules over the path algebra carries
the vertex simple `Sᵢ` to a module and transports its length-one projective resolution.  Thus
the path algebra module `Sᵢ` has projective dimension at most one, without an acyclicity
assumption.  This is the short exact sequence used to calculate its `Ext` groups and Euler
pairings against other modules.

The resolution is the standard first-arrow sequence
`0 ⟶ ⨁_{e : i ⟶ j} Pⱼ ⟶ Pᵢ ⟶ Sᵢ ⟶ 0`; see Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter III, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe v w

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-- The left path algebra module corresponding to the vertex simple representation `Sᵢ`. -/
noncomputable def vertexSimpleModule (i : Q) : ModuleCat (pathAlgebra k Q) :=
  (quiverRepFunctor k Q).objPreimage (simpleRep k Q i)

/-- The representation associated with `vertexSimpleModule` is the vertex simple. -/
noncomputable def vertexSimpleModuleIso (i : Q) :
    (quiverRepFunctor k Q).obj (vertexSimpleModule k Q i) ≅ simpleRep k Q i :=
  (quiverRepFunctor k Q).objObjPreimageIso _

/-- The vertex simple is a simple object of the path algebra module category. -/
instance vertexSimpleModule_simple (i : Q) : Simple (vertexSimpleModule k Q i) :=
  simple_obj (quiverRepFunctor k Q).inv (simpleRep k Q i)

variable {Q}

/-- The first-arrow projective resolution of the vertex simple, transported from quiver
representations to path algebra modules. -/
noncomputable def vertexSimpleModuleResolution (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] : ShortComplex (ModuleCat (pathAlgebra k Q)) :=
  (ShortComplex.mk _ _ (arrowSumToIndecProjRep_comp_indecProjRepToSimpleRep k i)).map
    (quiverRepFunctor k Q).inv

/-- The transported first-arrow sequence is short exact. -/
theorem vertexSimpleModuleResolution_shortExact (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (vertexSimpleModuleResolution k i).ShortExact :=
  (shortExact_arrowSumToIndecProjRep k i).map_of_exact (quiverRepFunctor k Q).inv

/-- The middle term of the transported resolution is the vertex projective module. -/
noncomputable def vertexSimpleModuleResolutionX₂Iso (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (vertexSimpleModuleResolution k i).X₂ ≅ indecProjModule k Q i :=
  by
    exact (quiverRepFunctor k Q).preimageIso
      ((quiverRepFunctor k Q).objObjPreimageIso (indecProjRep k Q i) ≪≫
        (indecProjModuleIso k Q i).symm)

/-- The first term of the resolution is the direct sum of the vertex projective modules at
the heads of the arrows leaving `i`. -/
noncomputable def vertexSimpleModuleResolutionX₁Iso (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (vertexSimpleModuleResolution k i).X₁ ≅
      ⨁ fun a : (j : Q) × (i ⟶ j) ↦ indecProjModule k Q a.1 := by
  letI : PreservesBiproduct (fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1)
      (quiverRepFunctor k Q).inv :=
    preservesBiproduct_of_preservesProduct
      (f := fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1)
      (quiverRepFunctor k Q).inv
  exact ((quiverRepFunctor k Q).inv.mapBiproduct
      (fun a : (j : Q) × (i ⟶ j) ↦ indecProjRep k Q a.1)) ≪≫
    biproduct.mapIso (fun a ↦ (quiverRepFunctor k Q).preimageIso
      ((quiverRepFunctor k Q).objObjPreimageIso (indecProjRep k Q a.1) ≪≫
        (indecProjModuleIso k Q a.1).symm))

/-- The quotient of the transported resolution is the vertex simple module. -/
noncomputable def vertexSimpleModuleResolutionX₃Iso (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (vertexSimpleModuleResolution k i).X₃ ≅ vertexSimpleModule k Q i :=
  Iso.refl _

/-- The first differential of the module resolution, expressed between the direct sum of
vertex projective modules and the vertex projective module. -/
noncomputable def arrowSumToIndecProjModule (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (⨁ fun a : (j : Q) × (i ⟶ j) ↦ indecProjModule k Q a.1) ⟶
      indecProjModule k Q i :=
  (vertexSimpleModuleResolutionX₁Iso k i).inv ≫
    (quiverRepFunctor k Q).inv.map (arrowSumToIndecProjRep k i) ≫
      (vertexSimpleModuleResolutionX₂Iso k i).hom

/-- The quotient map of the module resolution, from the vertex projective to the vertex simple. -/
noncomputable def indecProjModuleToVertexSimpleModule (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    indecProjModule k Q i ⟶ vertexSimpleModule k Q i :=
  (vertexSimpleModuleResolutionX₂Iso k i).inv ≫
    (quiverRepFunctor k Q).inv.map (indecProjRepToSimpleRep k i) ≫
      (vertexSimpleModuleResolutionX₃Iso k i).hom

/-- Under the term isomorphisms, the first differential is the module first-arrow map. -/
theorem vertexSimpleModuleResolution_f (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (vertexSimpleModuleResolution k i).f ≫ (vertexSimpleModuleResolutionX₂Iso k i).hom =
      (vertexSimpleModuleResolutionX₁Iso k i).hom ≫ arrowSumToIndecProjModule k i := by
  change (quiverRepFunctor k Q).inv.map (arrowSumToIndecProjRep k i) ≫
      (vertexSimpleModuleResolutionX₂Iso k i).hom =
    (vertexSimpleModuleResolutionX₁Iso k i).hom ≫
      ((vertexSimpleModuleResolutionX₁Iso k i).inv ≫
        (quiverRepFunctor k Q).inv.map (arrowSumToIndecProjRep k i) ≫
          (vertexSimpleModuleResolutionX₂Iso k i).hom)
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- Under the term isomorphisms, the second differential is the module quotient map. -/
theorem vertexSimpleModuleResolution_g (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    (vertexSimpleModuleResolution k i).g ≫ (vertexSimpleModuleResolutionX₃Iso k i).hom =
      (vertexSimpleModuleResolutionX₂Iso k i).hom ≫
        indecProjModuleToVertexSimpleModule k i := by
  change (quiverRepFunctor k Q).inv.map (indecProjRepToSimpleRep k i) ≫
      (vertexSimpleModuleResolutionX₃Iso k i).hom =
    (vertexSimpleModuleResolutionX₂Iso k i).hom ≫
      ((vertexSimpleModuleResolutionX₂Iso k i).inv ≫
        (quiverRepFunctor k Q).inv.map (indecProjRepToSimpleRep k i) ≫
          (vertexSimpleModuleResolutionX₃Iso k i).hom)
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- The first term of the first-arrow sequence is projective, being a finite biproduct of
vertex projectives, and equivalences preserve projective objects. -/
instance vertexSimpleModuleResolution_projective_X₁ (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    Projective (vertexSimpleModuleResolution k i).X₁ := by
  exact Projective.of_iso (vertexSimpleModuleResolutionX₁Iso k i).symm inferInstance

/-- The middle term of the first-arrow sequence is projective. -/
instance vertexSimpleModuleResolution_projective_X₂ (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    Projective (vertexSimpleModuleResolution k i).X₂ := by
  exact Projective.of_iso (vertexSimpleModuleResolutionX₂Iso k i).symm inferInstance

/-- A vertex simple of a path algebra has projective dimension less than two. This holds for
finite quivers with finitely many arrows leaving the given vertex, including quivers with cycles. -/
theorem vertexSimpleModule_hasProjectiveDimensionLT_two (i : Q)
    [Finite ((j : Q) × (i ⟶ j))] :
    HasProjectiveDimensionLT (vertexSimpleModule k Q i) 2 := by
  have h := (vertexSimpleModuleResolution_shortExact k i).hasProjectiveDimensionLT_X₃
    (n := 1) (hasProjectiveDimensionLT_of_ge _ 1 1 (by omega))
    (hasProjectiveDimensionLT_of_ge _ 1 2 (by omega))
  let _ := h
  exact hasProjectiveDimensionLT_of_iso (vertexSimpleModuleResolutionX₃Iso k i) 2

end TauCeti
