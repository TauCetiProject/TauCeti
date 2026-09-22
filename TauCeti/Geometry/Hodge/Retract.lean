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

More generally, no polarization is needed once a complement is given: a rational Hodge
substructure complementary to the chosen one already determines a retraction, namely the
projection onto the substructure along that complement. Its rational map is a morphism of Hodge
structures because it is idempotent with a Hodge structure as range and another as kernel. This is
the form used to split a substructure off an independent family, where the complement is the
supremum of the other members rather than an orthogonal complement.

This is the categorical form of the orthogonal-complement argument proving semisimplicity of
polarizable pure Hodge structures. See Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
§7.1.2, and Peters--Steenbrink, *Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat.ofSubstructure`: the polarizable object induced on a
  rational Hodge substructure.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.substructureInclusion`: its inclusion into the
  ambient object.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.substructureRetractionOfIsCompl`: the retraction
  supplied by a complementary rational Hodge substructure.
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
-- Deliberately a `def` rather than an `abbrev`: the carrier and Hodge-structure simp lemmas below
-- are the interface. Implicit reducibility only lets the dependent categorical types elaborate.
@[expose, implicit_reducible]
noncomputable def ofSubstructure (W : RationalHodgeSubstructure X.isBaseChangeRat X.hs) :
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

/-- Corestricting the rational map of a Hodge morphism to a rational Hodge substructure
preserves the morphism property. -/
theorem isMorphism_codRestrict
    {X Y : PolarizableHodgeStructureCat.{u} n}
    (W : RationalHodgeSubstructure Y.isBaseChangeRat Y.hs)
    (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier)
    (hf : HodgeStructureOn.IsMorphism X.hs Y.hs
      (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        Y.isBaseChangeRat Y.isBaseChangeComplex f))
    (hfw : ∀ x, f x ∈ W.WQ) :
    HodgeStructureOn.IsMorphism X.hs W.hodgeStructure
      (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        (isBaseChange_integralSubmoduleToRational Y.isBaseChangeRat W.WQ)
        (isBaseChange_integralSubmoduleToComplex Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ)
        (f.codRestrict W.WQ hfw)) := by
  let g := rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
    (isBaseChange_integralSubmoduleToRational Y.isBaseChangeRat W.WQ)
    (isBaseChange_integralSubmoduleToComplex Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ)
    (f.codRestrict W.WQ hfw)
  have hcomp : (rationalToComplexSubmodule Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ).subtype
      ∘ₗ g = rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        Y.isBaseChangeRat Y.isBaseChangeComplex f := by
    rw [← rationalMapToComplex_subtype Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ,
      ← rationalMapToComplex_comp, LinearMap.subtype_comp_codRestrict]
  refine {
    commutes_conj := fun x ↦ Subtype.ext ?_
    map_F_le := ?_ }
  -- Equality in the induced complex carrier is checked after its injective ambient inclusion.
  · change (rationalToComplexSubmodule Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ).subtype
        (g ((latticeConjugation X.isBaseChangeComplex).toEquiv x)) =
      (rationalToComplexSubmodule Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ).subtype
        ((latticeConjugation
          (isBaseChange_integralSubmoduleToComplex Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ)
            ).toEquiv (g x))
    calc
      _ = rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
          Y.isBaseChangeRat Y.isBaseChangeComplex f
          ((latticeConjugation X.isBaseChangeComplex).toEquiv x) :=
        LinearMap.congr_fun hcomp _
      _ = (latticeConjugation Y.isBaseChangeComplex).toEquiv
          (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
            Y.isBaseChangeRat Y.isBaseChangeComplex f x) :=
        hf.commutes_conj _
      _ = (latticeConjugation Y.isBaseChangeComplex).toEquiv
          ((rationalToComplexSubmodule Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ).subtype
            (g x)) := by
        exact congrArg (latticeConjugation Y.isBaseChangeComplex).toEquiv
          (LinearMap.congr_fun hcomp x).symm
      _ = (rationalToComplexSubmodule Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ).subtype
          ((latticeConjugation
            (isBaseChange_integralSubmoduleToComplex Y.isBaseChangeRat Y.isBaseChangeComplex W.WQ)
              ).toEquiv (g x)) := (W.isMorphism_subtype.commutes_conj _).symm
  · intro p y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [W.hodgeStructure_F, Submodule.mem_comap, ← LinearMap.comp_apply, hcomp]
    exact hf.map_F_le p ⟨x, hx, rfl⟩

/-! ### Retractions along complementary Hodge substructures -/

variable (W' : RationalHodgeSubstructure X.isBaseChangeRat X.hs)

/-- The rational projection onto `W` along a complementary rational Hodge substructure `W'`,
with codomain restricted to `W`. -/
noncomputable def substructureRetractionOfIsComplRat (h : IsCompl W W') :
    X.ratCarrier →ₗ[ℚ] W.WQ :=
  (W.WQ.projection W'.WQ (RationalHodgeSubstructure.isCompl_iff_WQ.1 h)).codRestrict W.WQ
    fun x ↦ Submodule.projection_apply_mem _ x

/-- Projection along complementary rational Hodge substructures is a morphism of the ambient
pure Hodge structure. -/
theorem isMorphism_substructureRetractionOfIsComplRat (h : IsCompl W W') :
    HodgeStructureOn.IsMorphism X.hs W.hodgeStructure
      (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        (isBaseChange_integralSubmoduleToRational X.isBaseChangeRat W.WQ)
        (isBaseChange_integralSubmoduleToComplex X.isBaseChangeRat X.isBaseChangeComplex W.WQ)
        (substructureRetractionOfIsComplRat X W W' h)) := by
  have hp : HodgeStructureOn.IsMorphism X.hs X.hs
      (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        X.isBaseChangeRat X.isBaseChangeComplex
        (W.WQ.projection W'.WQ (RationalHodgeSubstructure.isCompl_iff_WQ.1 h))) := by
    apply HodgeStructureOn.isMorphism_of_isIdempotentElem
      (isIdempotentElem_rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        (Submodule.isIdempotentElem_projection
          (RationalHodgeSubstructure.isCompl_iff_WQ.1 h)))
    · rw [range_rationalMapToComplex, Submodule.range_projection, ← W.WC_def]
      exact W.isSubstructure
    · rw [ker_rationalMapToComplex, Submodule.ker_projection, ← W'.WC_def]
      exact W'.isSubstructure
  exact isMorphism_codRestrict W _ hp fun x ↦ Submodule.projection_apply_mem _ x

/-- The categorical retraction onto `W` along a complementary rational Hodge substructure
`W'`. -/
noncomputable def substructureRetractionOfIsCompl (h : IsCompl W W') :
    X ⟶ ofSubstructure X W :=
  Hom.ofIsMorphism (substructureRetractionOfIsComplRat X W W' h)
    (isMorphism_substructureRetractionOfIsComplRat X W W' h)

/-- The rational map of the retraction along a complement is the corresponding subspace
projection with codomain restricted to `W`. -/
@[simp]
theorem substructureRetractionOfIsCompl_toRatLinearMap (h : IsCompl W W') :
    (substructureRetractionOfIsCompl X W W' h).hom.toRatLinearMap =
      substructureRetractionOfIsComplRat X W W' h := by
  rw [substructureRetractionOfIsCompl, Hom.ofIsMorphism_toRatLinearMap]

/-- Inclusion followed by retraction along a complementary substructure is the identity. -/
@[simp]
theorem substructureInclusion_comp_substructureRetractionOfIsCompl (h : IsCompl W W') :
    substructureInclusion X W ≫ substructureRetractionOfIsCompl X W W' h =
      𝟙 (ofSubstructure X W) := by
  apply Hom.ext
  rw [comp_toRatLinearMap, id_toRatLinearMap,
    substructureRetractionOfIsCompl_toRatLinearMap, substructureInclusion_toRatLinearMap]
  ext x
  apply Subtype.ext
  exact Submodule.projection_apply_of_mem_left _ x.property

/-- A substructure contained in the complementary summand is annihilated by the retraction. -/
@[simp]
theorem substructureInclusion_comp_substructureRetractionOfIsCompl_eq_zero
    {U : RationalHodgeSubstructure X.isBaseChangeRat X.hs} (h : IsCompl W W') (hU : U ≤ W') :
    substructureInclusion X U ≫ substructureRetractionOfIsCompl X W W' h = 0 := by
  apply Hom.ext
  rw [comp_toRatLinearMap, zero_toRatLinearMap,
    substructureRetractionOfIsCompl_toRatLinearMap, substructureInclusion_toRatLinearMap]
  ext x
  apply Subtype.ext
  exact Submodule.projection_apply_of_mem_right _ (hU x.property)

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
        (substructureRetractionRat X W P)) :=
  isMorphism_codRestrict W (W.projection P)
    (W.isMorphism_rationalMapToComplex_projection P) (fun x ↦ by
    rw [← W.range_projection P]
    exact LinearMap.mem_range_self (W.projection P) x)

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
  rw [comp_toRatLinearMap, id_toRatLinearMap, substructureRetraction_toRatLinearMap,
    substructureInclusion_toRatLinearMap]
  ext x
  -- The remaining coercions hide precisely that the projector fixes the subspace.
  apply Subtype.ext
  change W.projection P (W.WQ.subtype x) = W.WQ.subtype x
  exact W.projection_apply_of_mem P x.property

/-- The orthogonal retraction followed by the inclusion is the Hodge projector on the ambient
object. -/
theorem substructureRetraction_comp_substructureInclusion_toRatLinearMap :
    ((substructureRetraction X W P ≫ substructureInclusion X W).hom.toRatLinearMap) =
      W.projection P := by
  rw [comp_toRatLinearMap, substructureRetraction_toRatLinearMap,
    substructureInclusion_toRatLinearMap, substructureRetractionRat,
    LinearMap.subtype_comp_codRestrict]

/-- The inclusion of a rational Hodge substructure into a polarizable Hodge structure is a split
monomorphism. -/
theorem isSplitMono_substructureInclusion : IsSplitMono (substructureInclusion X W) :=
  let ⟨P⟩ := isPolarizable_iff_nonempty.1 X.isPolarizable
  IsSplitMono.mk' ⟨substructureRetraction X W P,
    substructureInclusion_comp_substructureRetraction X W P⟩

end TauCeti.Hodge.PolarizableHodgeStructureCat
