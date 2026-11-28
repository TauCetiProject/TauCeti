/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Expansion.Evaluation
public import TauCeti.CategoryTheory.DoubleCategory.Representation.Bicategory

/-!
# Strictness of represented generators in an expansion

The generators of an expanded strict double category are its original edges. Their chosen
composition and identity satisfy the original category laws. Evaluation identifies their
derived bicategory coherence with the equality isomorphisms of those laws.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Definition 3.12 and Proposition 3.13.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory DoubleCategoryStruct
open scoped Bicategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O H V)

private abbrev generatorEvaluation :
    D.expandHorizontalRepresentation.GeneratorBicategory ⥤ᵖ D.HorizontalBicategory :=
  D.expandHorizontalRepresentation.singletonPseudofunctor.comp
    D.expandEval.mapHorizontalBicategory.toPseudofunctor

private theorem generatorEvaluation_map_id
    (a : D.expandHorizontalRepresentation.GeneratorBicategory) :
    D.generatorEvaluation.map (𝟙 a) = 𝟙 (D.generatorEvaluation.obj a) :=
  HorizontalGlobular.ext (@composePath_toPath O H _ _ (edgeId H a.obj))

private theorem generatorEvaluation_map_comp
    {a b c : D.expandHorizontalRepresentation.GeneratorBicategory} (f : a ⟶ b) (g : b ⟶ c) :
    D.generatorEvaluation.map (f ≫ g) = D.generatorEvaluation.map f ≫ D.generatorEvaluation.map g :=
  HorizontalGlobular.ext ((@composePath_toPath O H _ _ (edgeComp H f g)).trans
    (congrArg₂ (edgeComp H) (@composePath_toPath O H _ _ f).symm
      (@composePath_toPath O H _ _ g).symm))

private theorem generatorEvaluation_mapId
    (a : D.expandHorizontalRepresentation.GeneratorBicategory) :
    D.generatorEvaluation.mapId a = eqToIso (D.generatorEvaluation_map_id a) := by
  rw [Pseudofunctor.comp_mapId]
  simp only [BicategoryInductionData.inclusion_mapId,
    HorizontalRepresentation.inductionData_mapUnit]
  rw [StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso]
  -- The local action is the evaluation functor; both maps have the same cell formula.
  change (D.expandHorizontalEval a.obj a.obj).mapIso
    (D.expandHorizontalRepresentation.unitIso a.obj).symm ≪≫ eqToIso _ = _
  rw [Functor.mapIso_symm, D.expandHorizontalRepresentation_unitIso]
  erw [D.expandHorizontalEval_mapIso]
  apply Iso.ext
  erw [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  dsimp only [eqToIso]
  erw [eqToHom_trans]
  rfl

private theorem generatorEvaluation_mapComp
    {a b c : D.expandHorizontalRepresentation.GeneratorBicategory} (f : a ⟶ b) (g : b ⟶ c) :
    D.generatorEvaluation.mapComp f g = eqToIso (D.generatorEvaluation_map_comp f g) := by
  rw [Pseudofunctor.comp_mapComp]
  simp only [BicategoryInductionData.inclusion_mapComp,
    HorizontalRepresentation.inductionData_mapMul]
  rw [StrictPseudofunctor.mapComp_eq_eqToIso]
  -- The local action is evaluation, including on the binary comparison isomorphism.
  change (D.expandHorizontalEval a.obj c.obj).mapIso
    (D.expandHorizontalRepresentation.mulIso f g).symm ≪≫ eqToIso _ = _
  rw [Functor.mapIso_symm, D.expandHorizontalRepresentation_mulIso]
  erw [D.expandHorizontalEval_mapIso]
  apply Iso.ext
  erw [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  dsimp only [eqToIso]
  erw [eqToHom_trans]
  rfl

/-- Evaluate represented generators as a strict pseudofunctor to the original globular
bicategory. The derived binary and nullary comparisons evaluate to equality isomorphisms.
The body is exposed so that object and cell maps compute in dependent cell formulas. -/
@[expose]
def expandGeneratorEval : StrictPseudofunctor
    D.expandHorizontalRepresentation.GeneratorBicategory D.HorizontalBicategory where
  __ := D.expandHorizontalRepresentation.singletonPseudofunctor.comp
    D.expandEval.mapHorizontalBicategory.toPseudofunctor
  map_id := by exact generatorEvaluation_map_id D
  mapId_eq_eqToIso := by exact generatorEvaluation_mapId D
  map_comp := by exact generatorEvaluation_map_comp D
  mapComp_eq_eqToIso := by exact generatorEvaluation_mapComp D

@[simp]
theorem expandGeneratorEval_obj_obj (a : D.expandHorizontalRepresentation.GeneratorBicategory) :
    (D.expandGeneratorEval.obj a).obj = a.obj := (rfl)

/-- A generator evaluates to its original edge. -/
@[simp]
theorem expandGeneratorEval_map_edge
    {a b : D.expandHorizontalRepresentation.GeneratorBicategory} (f : a ⟶ b) :
    (D.expandGeneratorEval.map f).edge = f :=
  @composePath_toPath O H _ _ f

@[simp]
theorem expandGeneratorEval_map₂_cell
    {a b : D.expandHorizontalRepresentation.GeneratorBicategory} {f g : a ⟶ b} (α : f ⟶ g) :
    (D.expandGeneratorEval.map₂ α).cell = α.hom.cell := (rfl)

/-- Evaluation is fully faithful on the hom-categories of represented generators. -/
def fullyFaithfulExpandGeneratorEval
    (a b : D.expandHorizontalRepresentation.GeneratorBicategory) :
    (D.expandGeneratorEval.mapFunctor a b).FullyFaithful where
  preimage α := InducedCategory.homMk ⟨α.cell⟩

instance (a b : D.expandHorizontalRepresentation.GeneratorBicategory) :
    (D.expandGeneratorEval.mapFunctor a b).Full :=
  (D.fullyFaithfulExpandGeneratorEval a b).full

instance (a b : D.expandHorizontalRepresentation.GeneratorBicategory) :
    (D.expandGeneratorEval.mapFunctor a b).Faithful :=
  (D.fullyFaithfulExpandGeneratorEval a b).faithful

private theorem generator_leftUnitor
    {a b : D.expandHorizontalRepresentation.GeneratorBicategory}
    (f : a ⟶ b) (e : 𝟙 a ≫ f = f) : λ_ f = eqToIso e := by
  apply (D.expandGeneratorEval.mapFunctor a b).mapIso_injective
  rw [eqToIso_map]
  apply Iso.ext
  erw [Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, Pseudofunctor.map₂_left_unitor]
  rw [StrictPseudofunctor.mapComp_eq_eqToIso,
    StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso]
  simp only [eqToIso.hom, Bicategory.eqToHom_whiskerRight,
    Bicategory.Strict.leftUnitor_eqToIso, eqToHom_trans]
  rfl

private theorem generator_rightUnitor
    {a b : D.expandHorizontalRepresentation.GeneratorBicategory}
    (f : a ⟶ b) (e : f ≫ 𝟙 b = f) : ρ_ f = eqToIso e := by
  apply (D.expandGeneratorEval.mapFunctor a b).mapIso_injective
  rw [eqToIso_map]
  apply Iso.ext
  erw [Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, Pseudofunctor.map₂_right_unitor]
  rw [StrictPseudofunctor.mapComp_eq_eqToIso,
    StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso]
  simp only [eqToIso.hom, Bicategory.whiskerLeft_eqToHom,
    Bicategory.Strict.rightUnitor_eqToIso, eqToHom_trans]
  rfl

private theorem generator_associator
    {a b c d : D.expandHorizontalRepresentation.GeneratorBicategory}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (e : (f ≫ g) ≫ h = f ≫ g ≫ h) :
    α_ f g h = eqToIso e := by
  apply (D.expandGeneratorEval.mapFunctor a d).mapIso_injective
  rw [eqToIso_map]
  apply Iso.ext
  erw [Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, Pseudofunctor.map₂_associator]
  simp only [StrictPseudofunctor.mapComp_eq_eqToIso,
    Bicategory.eqToHom_whiskerRight, Bicategory.whiskerLeft_eqToHom,
    Bicategory.Strict.associator_eqToIso, eqToIso, eqToHom_trans]
  rfl

/-- The bicategory induced by the horizontal representation of expansion is strict,
including its derived unitors and associators. -/
instance expandHorizontalRepresentation_strict :
    Bicategory.Strict D.expandHorizontalRepresentation.GeneratorBicategory where
  id_comp f := Category.id_comp (self := H) f
  comp_id f := Category.comp_id (self := H) f
  assoc f g h := Category.assoc (self := H) f g h
  leftUnitor_eqToIso f := generator_leftUnitor D f _
  rightUnitor_eqToIso f := generator_rightUnitor D f _
  associator_eqToIso f g h := generator_associator D f g h _

/-- The horizontal part of the chosen two-directional representation has a strict
induced bicategory. -/
instance expandRepresentation_horizontal_strict :
    Bicategory.Strict D.expandRepresentation.horizontal.GeneratorBicategory := by
  rw [D.expandRepresentation_horizontal]
  infer_instance

/-- The bicategory induced by the vertical representation of expansion is strict.
It is the horizontal result applied to the transposed original double category. -/
instance expandRepresentation_vertical_strict :
    Bicategory.Strict D.expandRepresentation.vertical.GeneratorBicategory := by
  rw [D.expandRepresentation_vertical]
  have transport {D₁ D₂ : StrictDoubleCategory.{s} O (pathCategory O V.toQuiver)
      (pathCategory O H.toQuiver)} (e : D₁ = D₂) (R : D₁.HorizontalRepresentation)
      (hR : Bicategory.Strict R.GeneratorBicategory) :
      Bicategory.Strict (e ▸ R).GeneratorBicategory := by
    cases e
    exact hR
  exact transport D.expand_transpose _ (expandHorizontalRepresentation_strict D.transpose)

end TauCeti.StrictDoubleCategory
