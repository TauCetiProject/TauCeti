/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Filtered colimits of smooth discrete representations

Let `X : J ⥤ SmoothDiscreteTopRep k G` be a filtered diagram of smooth discrete representations.
Its colimit exists and is computed on underlying modules: the colimit of the underlying actions in
`Action (ModuleCat k) G`, with the discrete topology.

Discreteness of the colimit is what makes this work. Every leg out of a discrete stage is then
continuous; scalar multiplication `r ↦ r • x` is continuous because `x` comes from a stage, where it
is; and the stabilizer of a point is open because, the diagram being filtered, it is the union of
the stabilizers of its representatives at the stages.

Consequently the functor to underlying modules and the forgetful functor to types preserve
filtered colimits: a colimit cocone in `SmoothDiscreteTopRep k G` of a filtered diagram is a colimit
on underlying sets. This is the form in which continuous cohomology of a compact group is shown to
commute with filtered colimits of coefficients.

## Main declarations

* `TauCeti.SmoothDiscreteTopRep.hasFilteredColimits`: smooth discrete representations have
  filtered colimits.
* `TauCeti.SmoothDiscreteTopRep.forget_preservesFilteredColimits`: the forgetful functor to types
  preserves them.
* `TauCeti.SmoothDiscreteTopRep.forget₂ModuleCat_preservesFilteredColimits`: so does the functor to
  underlying modules.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., §I.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.SmoothDiscreteTopRep

universe w v u

variable {k : Type v} [Ring k] [TopologicalSpace k] {G : Type u} [Monoid G] [TopologicalSpace G]

variable (k G) in
/-- The underlying `k`-linear action of a smooth discrete representation, as a functor. -/
private abbrev toAction : SmoothDiscreteTopRep.{v, u, w} k G ⥤ Action (ModuleCat.{w} k) G :=
  smoothDiscreteι k G ⋙ TopRep.toActionTopModFunc ⋙
    (forget₂ (TopModuleCat k) (ModuleCat k)).mapAction G

namespace FilteredColimits

variable {J : Type w} [SmallCategory J] (X : J ⥤ SmoothDiscreteTopRep.{v, u, w} k G)

/-- The colimit leg of the underlying actions at `j`, read on the underlying module of `X.obj j`. -/
private noncomputable abbrev ι (j : J) :
    (X.obj j).obj.V →ₗ[k] (colimit (X ⋙ toAction k G)).V :=
  (colimit.ι (X ⋙ toAction k G) j).hom.hom

/-- The legs of the colimit action are compatible with the transition maps. -/
private theorem ι_map_apply {i j : J} (f : i ⟶ j) (y : (X.obj i).obj.V) :
    ι X j ((X.map f).hom.hom y) = ι X i y :=
  ConcreteCategory.congr_hom (congrArg Action.Hom.hom (colimit.w (X ⋙ toAction k G) f)) y

/-- The action on the colimit restricts to the action at each stage. -/
private theorem ρ_ι_apply (g : G) {j : J} (y : (X.obj j).obj.V) :
    ((colimit (X ⋙ toAction k G)).ρ g).hom (ι X j y) = ι X j ((X.obj j).obj.ρ g y) :=
  (ConcreteCategory.congr_hom ((colimit.ι (X ⋙ toAction k G) j).comm g) y).symm

/-- The colimit module, with the discrete topology. -/
private local instance : TopologicalSpace (colimit (X ⋙ toAction k G)).V := ⊥

private local instance : DiscreteTopology (colimit (X ⋙ toAction k G)).V := ⟨rfl⟩

/-- The continuous representation of `G` on the discrete colimit module, given by the action of
the colimit in `Action (ModuleCat k) G`. -/
private noncomputable def colimitρ : ContRepresentation k G (colimit (X ⋙ toAction k G)).V :=
  .ofMonoidHom
    { toFun g := ⟨((colimit (X ⋙ toAction k G)).ρ g).hom, continuous_of_discreteTopology⟩
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }

/-- `colimitρ X` acts through the action of the colimit in `Action (ModuleCat k) G`. -/
private theorem colimitρ_apply (g : G) (x : (colimit (X ⋙ toAction k G)).V) :
    colimitρ X g x = ((colimit (X ⋙ toAction k G)).ρ g).hom x :=
  rfl

/-- The representation on the colimit restricts to the representation at each stage. -/
private theorem colimitρ_ι_apply (g : G) {j : J} (y : (X.obj j).obj.V) :
    colimitρ X g (ι X j y) = ι X j ((X.obj j).obj.ρ g y) := by
  rw [colimitρ_apply, ρ_ι_apply]

variable [IsFiltered J]

/-- The colimit of the underlying actions is a colimit on underlying sets. -/
private noncomputable def isColimitForget :
    IsColimit ((Action.forget (ModuleCat.{w} k) G ⋙ forget₂ (ModuleCat.{w} k) AddCommGrpCat ⋙
      forget AddCommGrpCat).mapCocone (colimit.cocone (X ⋙ toAction k G))) :=
  isColimitOfPreserves _ (colimit.isColimit _)

/-- Every element of the colimit comes from some stage. -/
private theorem exists_ι_eq (x : (colimit (X ⋙ toAction k G)).V) :
    ∃ (j : J) (y : (X.obj j).obj.V), ι X j y = x :=
  Types.jointly_surjective_of_isColimit (isColimitForget X) x

/-- Two elements of one stage with the same image in the colimit agree at a deeper stage. -/
private theorem exists_map_eq_of_ι_eq {j : J} {y y' : (X.obj j).obj.V} (h : ι X j y = ι X j y') :
    ∃ (l : J) (f : j ⟶ l), (X.map f).hom.hom y = (X.map f).hom.hom y' :=
  (Types.FilteredColimit.isColimit_eq_iff' (isColimitForget X) y y').1 h

/-- Scalar multiplication on the discrete colimit module is continuous: an element comes from a
stage, on which scalar multiplication is continuous. -/
private local instance : ContinuousSMul k (colimit (X ⋙ toAction k G)).V := by
  refine ⟨continuous_prod_of_discrete_right.2 fun x ↦ ?_⟩
  obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
  have := (X.obj j).property.discreteTopology
  simp_rw [← map_smul]
  exact continuous_of_discreteTopology.comp (continuous_id.smul continuous_const)

/-- The stabilizers of the colimit are open: the stabilizer of the image of `y` is the union of the
stabilizers of the images of `y` at the deeper stages. -/
private theorem isSmoothDiscrete_colimit : IsSmoothDiscrete k (TopRep.of (colimitρ X)) := by
  refine ⟨inferInstanceAs (DiscreteTopology (colimit (X ⋙ toAction k G)).V), fun x ↦ ?_⟩
  obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
  refine isOpen_iff_forall_mem_open.2 fun g hg ↦ ?_
  -- `g` fixes the image of `y` at some deeper stage `l`
  obtain ⟨l, f, hf⟩ := exists_map_eq_of_ι_eq X ((colimitρ_ι_apply X g y).symm.trans hg)
  rw [TopRep.hom_comm_apply] at hf
  refine ⟨{g' | (X.obj l).obj.ρ g' ((X.map f).hom.hom y) = (X.map f).hom.hom y},
    fun g' (hg' : _ = _) ↦ ?_, (X.obj l).property.stabilizer_isOpen _, hf⟩
  -- and the stabilizer of that image fixes the image of `y` in the colimit
  rw [Set.mem_ofPred_eq, TopRep.of_ρ, ← ι_map_apply X f, colimitρ_ι_apply, hg']

/-- The colimit of a filtered diagram of smooth discrete representations: the colimit of the
underlying actions, with the discrete topology. -/
private noncomputable def colimitObj : SmoothDiscreteTopRep.{v, u, w} k G :=
  ⟨TopRep.of (colimitρ X), isSmoothDiscrete_colimit X⟩

/-- The colimit cocone of a filtered diagram of smooth discrete representations, whose legs are the
colimit legs of the underlying actions. -/
private noncomputable def colimitCocone : Cocone X where
  pt := colimitObj X
  ι :=
    { app j :=
        have := (X.obj j).property.discreteTopology
        ObjectProperty.homMk <| ConcreteCategory.ofHom
          { toContinuousLinearMap := ⟨ι X j, continuous_of_discreteTopology⟩
            isIntertwining' g := ContinuousLinearMap.ext fun y ↦ (colimitρ_ι_apply X g y).symm }
      naturality _ _ f := ObjectProperty.hom_ext _ <| TopRep.hom_ext <|
        DFunLike.ext _ _ fun y ↦ ι_map_apply X f y }

/-- The morphism out of the colimit to the apex of a cocone `s`: the descended morphism of the
underlying actions, which is continuous because the colimit is discrete. -/
private noncomputable def desc (s : Cocone X) : colimitObj X ⟶ s.pt :=
  have : DiscreteTopology (colimitObj X).obj.V := (colimitObj X).property.discreteTopology
  ObjectProperty.homMk <| ConcreteCategory.ofHom
    { toContinuousLinearMap := ⟨(colimit.desc (X ⋙ toAction k G)
        ((toAction k G).mapCocone s)).hom.hom, continuous_of_discreteTopology⟩
      isIntertwining' g := ContinuousLinearMap.ext fun x ↦ ConcreteCategory.congr_hom
        ((colimit.desc (X ⋙ toAction k G) ((toAction k G).mapCocone s)).comm g) x }

/-- `desc X s` is the descended morphism of the underlying actions. -/
private theorem desc_hom_apply (s : Cocone X) (x : (colimit (X ⋙ toAction k G)).V) :
    (desc X s).hom.hom x =
      (colimit.desc (X ⋙ toAction k G) ((toAction k G).mapCocone s)).hom.hom x :=
  rfl

/-- The morphism out of the colimit restricts to the legs of `s`. -/
private theorem desc_ι_apply (s : Cocone X) (j : J) (y : (X.obj j).obj.V) :
    (desc X s).hom.hom (ι X j y) = (s.ι.app j).hom.hom y := by
  rw [desc_hom_apply]
  exact ConcreteCategory.congr_hom
    (congrArg Action.Hom.hom (colimit.ι_desc ((toAction k G).mapCocone s) j)) y

/-- The cocone `colimitCocone X` is a colimit in `SmoothDiscreteTopRep k G`. -/
private noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone X) where
  desc := desc X
  fac s j := ObjectProperty.hom_ext _ <| TopRep.hom_ext <| DFunLike.ext _ _ fun y ↦
    desc_ι_apply X s j y
  uniq s m hm := ObjectProperty.hom_ext _ <| TopRep.hom_ext <| DFunLike.ext _ _ fun x ↦ by
    obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
    exact (ConcreteCategory.congr_hom (congrArg (·.hom) (hm j)) y).trans (desc_ι_apply X s j y).symm

end FilteredColimits

open FilteredColimits

/-- **Smooth discrete representations have filtered colimits**, computed on underlying modules:
the colimit of the underlying actions in `Action (ModuleCat k) G`, with the discrete topology. -/
instance hasFilteredColimits : HasFilteredColimits (SmoothDiscreteTopRep.{v, u, w} k G) where
  HasColimitsOfShape _ _ _ := ⟨fun X ↦ ⟨_, colimitCoconeIsColimit X⟩⟩

/-- **The forgetful functor from smooth discrete representations to types preserves filtered
colimits.** A colimit cocone of a filtered diagram in `SmoothDiscreteTopRep k G` is a colimit on
underlying sets. -/
instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (smoothDiscreteι k G ⋙ forget (TopRep.{w} k G)) where
  preserves_filtered_colimits _ _ _ := ⟨fun {X} ↦
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit X) (isColimitForget X)⟩

/-- **Filtered colimits of smooth discrete representations are computed on underlying modules.**
The functor to the underlying `k`-modules preserves filtered colimits. -/
instance forget₂ModuleCat_preservesFilteredColimits :
    PreservesFilteredColimits (smoothDiscreteι k G ⋙ TopRep.toActionTopModFunc ⋙
      Action.forget _ G ⋙ forget₂ (TopModuleCat k) (ModuleCat.{w} k)) where
  preserves_filtered_colimits _ _ _ := ⟨fun {X} ↦
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit X)
      (isColimitOfPreserves (Action.forget (ModuleCat.{w} k) G) (colimit.isColimit _))⟩

end TauCeti.SmoothDiscreteTopRep
