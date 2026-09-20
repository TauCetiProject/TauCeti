/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Geometry.Hodge.Category
public import TauCeti.Geometry.Hodge.InducedPolarization
public import TauCeti.Geometry.Hodge.Projection

/-!
# Rational Hodge substructures as categorical retracts

A rational Hodge substructure of a polarizable pure Hodge structure is itself a polarizable
object. Its rational and complex carriers are the corresponding subspaces, while its integral
lattice consists of the integral vectors that land in the rational subspace.

For a chosen polarization, the inclusion of this object admits a retraction. The underlying
rational map of the retraction is the orthogonal projector with codomain restricted to the
substructure. Thus the composite in the ambient object is the Hodge projector, while the composite
on the subobject is the identity. In particular, the inclusion is a split monomorphism.

This is the categorical form of the orthogonal-complement argument proving semisimplicity of
polarizable pure Hodge structures. See Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
§7.1.2, and Peters--Steenbrink, *Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat.ofSubstructure`: the polarizable object induced on a
  rational Hodge substructure.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.substructureInclusion`: its inclusion into the
  ambient object.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.substructureRetraction`: the retraction supplied by
  a polarization.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.isSplitMono_substructureInclusion`: the categorical
  splitting.
-/

public section

namespace TauCeti.Hodge.PolarizableHodgeStructureCat

open CategoryTheory

universe u

variable {n : ℤ} (X : PolarizableHodgeStructureCat.{u} n)

/-- A rational Hodge substructure, regarded as a polarizable Hodge structure in its own right.

The integral carrier is the inverse image of the rational subspace in the ambient lattice. The
rational and complex carriers are the corresponding subspaces, with the induced Hodge structure
and induced polarizability. -/
noncomputable abbrev ofSubstructure (W : RationalHodgeSubstructure X.isBaseChangeRat X.hs) :
    PolarizableHodgeStructureCat.{u} n := by
  let b := Submodule.basisOfPid (Module.Free.chooseBasis ℤ X.intCarrier)
    (integralSubmodule X.toRat W.WQ)
  letI : Module.Free ℤ (integralSubmodule X.toRat W.WQ) := Module.Free.of_basis b.2
  letI : Module.Finite ℤ (integralSubmodule X.toRat W.WQ) := Module.Finite.of_basis b.2
  exact .of (isBaseChange_integralSubmoduleToRational X.isBaseChangeRat W.WQ)
    (isBaseChange_integralSubmoduleToComplex X.isBaseChangeRat X.isBaseChangeComplex W.WQ)
    W.hodgeStructure (W.isPolarizable_hodgeStructure X.isPolarizable)

variable (W : RationalHodgeSubstructure X.isBaseChangeRat X.hs)

/-- The integral carrier of the induced object consists of the integral vectors whose rational
images lie in the substructure. -/
@[simp]
theorem ofSubstructure_intCarrier :
    (ofSubstructure X W).intCarrier = integralSubmodule X.toRat W.WQ :=
  rfl

/-- The rational carrier of the object induced on a rational Hodge substructure is the underlying
rational subspace. -/
@[simp]
theorem ofSubstructure_ratCarrier : (ofSubstructure X W).ratCarrier = W.WQ :=
  rfl

/-- The complex carrier of the induced object is the complexification of its rational subspace. -/
@[simp]
theorem ofSubstructure_complexCarrier :
    (ofSubstructure X W).complexCarrier =
      rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ :=
  rfl

/-- The pure Hodge structure on the induced object is the one obtained by restricting the ambient
filtration. -/
@[simp]
theorem ofSubstructure_hs : (ofSubstructure X W).hs = W.hodgeStructure :=
  rfl

/-- The inclusion of an induced rational Hodge substructure into its ambient object. -/
noncomputable def substructureInclusion : ofSubstructure X W ⟶ X :=
  Hom.ofIsMorphism W.WQ.subtype <| by
    rw [rationalMapToComplex_subtype]
    exact W.isMorphism_subtype

/-- The rational map underlying the inclusion is the subtype map. -/
@[simp]
theorem substructureInclusion_toRatLinearMap :
    (substructureInclusion X W).hom.toRatLinearMap = W.WQ.subtype := by
  rw [substructureInclusion, Hom.ofIsMorphism_toRatLinearMap]

/-- The complex map underlying the inclusion is the subtype map. -/
@[simp]
theorem substructureInclusion_toLinearMap :
    (substructureInclusion X W).hom.toLinearMap =
      (rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ).subtype := by
  rw [substructureInclusion, Hom.ofIsMorphism_toLinearMap, rationalMapToComplex_subtype]

variable (P : Polarization X.isBaseChangeComplex X.hs)

/-- The rational retraction onto a rational Hodge substructure: the orthogonal projector with its
codomain restricted to the subspace. -/
noncomputable def substructureRetractionRat : X.ratCarrier →ₗ[ℚ] W.WQ :=
  (W.projection P).codRestrict W.WQ fun x ↦ by
    rw [← W.range_projection P]
    exact LinearMap.mem_range_self (W.projection P) x

/-- The rational retraction is a morphism of pure Hodge structures. -/
theorem isMorphism_substructureRetractionRat :
    HodgeStructureOn.IsMorphism X.hs W.hodgeStructure
      (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        (isBaseChange_integralSubmoduleToRational X.isBaseChangeRat W.WQ)
        (isBaseChange_integralSubmoduleToComplex X.isBaseChangeRat X.isBaseChangeComplex W.WQ)
        (substructureRetractionRat X W P)) := by
  let g := rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
    (isBaseChange_integralSubmoduleToRational X.isBaseChangeRat W.WQ)
    (isBaseChange_integralSubmoduleToComplex X.isBaseChangeRat X.isBaseChangeComplex W.WQ)
    (substructureRetractionRat X W P)
  have hcomp : (rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ).subtype
      ∘ₗ g = rationalMapToComplex X.isBaseChangeRat
      X.isBaseChangeComplex X.isBaseChangeRat X.isBaseChangeComplex (W.projection P) := by
    rw [← rationalMapToComplex_subtype X.isBaseChangeRat X.isBaseChangeComplex W.WQ,
      ← rationalMapToComplex_comp, substructureRetractionRat,
      LinearMap.subtype_comp_codRestrict]
  have hproj := W.isMorphism_rationalMapToComplex_projection P
  refine {
    commutes_conj := fun x ↦ Subtype.ext ?_
    map_F_le := ?_ }
  -- Equality in the induced complex carrier is checked after its injective ambient inclusion.
  · change (rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ).subtype
        (g ((latticeConjugation X.isBaseChangeComplex).toEquiv x)) =
      (rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ).subtype
        ((latticeConjugation
          (isBaseChange_integralSubmoduleToComplex X.isBaseChangeRat X.isBaseChangeComplex W.WQ)
            ).toEquiv (g x))
    calc
      _ = rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex X.isBaseChangeRat
          X.isBaseChangeComplex (W.projection P)
          ((latticeConjugation X.isBaseChangeComplex).toEquiv x) :=
        LinearMap.congr_fun hcomp _
      _ = (latticeConjugation X.isBaseChangeComplex).toEquiv
          (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex X.isBaseChangeRat
            X.isBaseChangeComplex (W.projection P) x) :=
        hproj.commutes_conj _
      _ = (latticeConjugation X.isBaseChangeComplex).toEquiv
          ((rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ).subtype
            (g x)) := by
        exact congrArg (latticeConjugation X.isBaseChangeComplex).toEquiv
          (LinearMap.congr_fun hcomp x).symm
      _ = (rationalToComplexSubmodule X.isBaseChangeRat X.isBaseChangeComplex W.WQ).subtype
          ((latticeConjugation
            (isBaseChange_integralSubmoduleToComplex X.isBaseChangeRat X.isBaseChangeComplex W.WQ)
              ).toEquiv (g x)) := (W.isMorphism_subtype.commutes_conj _).symm
  · intro p y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [W.hodgeStructure_F, Submodule.mem_comap, ← LinearMap.comp_apply, hcomp]
    exact hproj.map_F_le p ⟨x, hx, rfl⟩

/-- The categorical retraction of a rational Hodge substructure inclusion supplied by a chosen
polarization. -/
noncomputable def substructureRetraction : X ⟶ ofSubstructure X W :=
  Hom.ofIsMorphism (substructureRetractionRat X W P)
    (isMorphism_substructureRetractionRat X W P)

/-- The rational map underlying the categorical retraction is the orthogonal projector with its
codomain restricted to the substructure. -/
@[simp]
theorem substructureRetraction_toRatLinearMap :
    (substructureRetraction X W P).hom.toRatLinearMap = substructureRetractionRat X W P := by
  rw [substructureRetraction, Hom.ofIsMorphism_toRatLinearMap]

/-- The inclusion followed by the orthogonal retraction is the identity on the induced Hodge
structure. -/
@[simp]
theorem substructureInclusion_comp_substructureRetraction :
    substructureInclusion X W ≫ substructureRetraction X W P = 𝟙 (ofSubstructure X W) := by
  apply Hom.ext
  rw [comp_toRatLinearMap, substructureRetraction_toRatLinearMap,
    substructureInclusion_toRatLinearMap, id_toRatLinearMap]
  ext x
  -- The remaining coercions hide precisely that the projector fixes the subspace.
  change W.projection P (x : W.WQ) = x
  exact W.projection_apply_of_mem P x.property

/-- The orthogonal retraction followed by the inclusion is the Hodge projector on the ambient
object. -/
@[simp]
theorem substructureRetraction_comp_substructureInclusion_toRatLinearMap :
    ((substructureRetraction X W P ≫ substructureInclusion X W).hom.toRatLinearMap) =
      W.projection P := by
  rw [comp_toRatLinearMap, substructureInclusion_toRatLinearMap,
    substructureRetraction_toRatLinearMap, substructureRetractionRat,
    LinearMap.subtype_comp_codRestrict]

/-- The inclusion of a rational Hodge substructure into a polarizable Hodge structure is a split
monomorphism. -/
theorem isSplitMono_substructureInclusion : IsSplitMono (substructureInclusion X W) :=
  let ⟨P⟩ := isPolarizable_iff_nonempty.1 X.isPolarizable
  IsSplitMono.mk' ⟨substructureRetraction X W P,
    substructureInclusion_comp_substructureRetraction X W P⟩

end TauCeti.Hodge.PolarizableHodgeStructureCat
