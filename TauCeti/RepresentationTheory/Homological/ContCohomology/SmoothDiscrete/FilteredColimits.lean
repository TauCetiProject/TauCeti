/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Filtered colimits of smooth discrete representations

Let `X : J ⥤ SmoothDiscreteTopRep k G` be a filtered diagram of smooth discrete representations.
Its colimit exists and is computed on underlying modules: the colimit module of the underlying
`k`-modules, with the discrete topology and the action of `G` induced by the actions at the stages.

Discreteness of the colimit is what makes this work. Every leg out of a discrete stage is then
continuous; scalar multiplication `r ↦ r • x` is continuous because `x` comes from a stage, where it
is; and the stabilizer of a point is open because, the diagram being filtered, it is the union of
the stabilizers of its representatives at the stages.

Consequently the forgetful functor from smooth discrete representations to types preserves
filtered colimits: a colimit cocone in `SmoothDiscreteTopRep k G` of a filtered diagram is a colimit
on underlying sets. This is the form in which continuous cohomology of a compact group is shown to
commute with filtered colimits of coefficients.

## Main declarations

* `TauCeti.SmoothDiscreteTopRep.hasFilteredColimits`: smooth discrete representations have
  filtered colimits.
* `TauCeti.SmoothDiscreteTopRep.forget_preservesFilteredColimits`: the forgetful functor to types
  preserves them.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., §I.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.SmoothDiscreteTopRep

universe w v u

variable {k : Type v} [Ring k] [TopologicalSpace k] {G : Type u} [Monoid G] [TopologicalSpace G]

variable (k G) in
/-- The underlying module of a smooth discrete representation, as a functor. -/
private abbrev toModuleCat : SmoothDiscreteTopRep.{v, u, w} k G ⥤ ModuleCat.{w} k :=
  smoothDiscreteι k G ⋙ TopRep.toActionTopModFunc ⋙ Action.forget _ G ⋙
    forget₂ (TopModuleCat k) (ModuleCat k)

namespace FilteredColimits

variable {J : Type w} [SmallCategory J] (X : J ⥤ SmoothDiscreteTopRep.{v, u, w} k G)

/-- The colimit leg of the underlying modules at `j`, read on the underlying module of `X.obj j`. -/
private noncomputable abbrev ι (j : J) :
    (X.obj j).obj.V →ₗ[k] ↑(colimit (X ⋙ toModuleCat k G)) :=
  (colimit.ι (X ⋙ toModuleCat k G) j).hom

/-- The legs of the colimit module are compatible with the transition maps. -/
private theorem ι_map_apply {i j : J} (f : i ⟶ j) (y : (X.obj i).obj.V) :
    ι X j ((X.map f).hom.hom y) = ι X i y :=
  ConcreteCategory.congr_hom (colimit.w (X ⋙ toModuleCat k G) f) y

/-- The action of `g` at each stage, as an endomorphism of the diagram of underlying modules. -/
private noncomputable def actNatTrans (g : G) : X ⋙ toModuleCat k G ⟶ X ⋙ toModuleCat k G where
  app j := ModuleCat.ofHom ((X.obj j).obj.ρ g).toLinearMap
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun y ↦
    (TopRep.hom_comm_apply (X.map f).hom g y).symm)

/-- The action of `g` on the colimit module, induced by the actions at the stages. -/
private noncomputable def act (g : G) :
    ↑(colimit (X ⋙ toModuleCat k G)) →ₗ[k] ↑(colimit (X ⋙ toModuleCat k G)) :=
  (colimMap (actNatTrans X g)).hom

/-- The action on the colimit module restricts to the action at each stage. -/
private theorem act_ι_apply (g : G) {j : J} (y : (X.obj j).obj.V) :
    act X g (ι X j y) = ι X j ((X.obj j).obj.ρ g y) :=
  ConcreteCategory.congr_hom (ι_colimMap (actNatTrans X g) j) y

variable [IsFiltered J]

/-- The colimit of the underlying modules is a colimit on underlying sets. -/
private noncomputable def isColimitForget :
    IsColimit ((forget₂ (ModuleCat.{w} k) AddCommGrpCat ⋙ forget AddCommGrpCat).mapCocone
      (colimit.cocone (X ⋙ toModuleCat k G))) :=
  isColimitOfPreserves _ (colimit.isColimit _)

/-- Every element of the colimit module comes from some stage. -/
private theorem exists_ι_eq (x : ↑(colimit (X ⋙ toModuleCat k G))) :
    ∃ (j : J) (y : (X.obj j).obj.V), ι X j y = x :=
  Types.jointly_surjective_of_isColimit (isColimitForget X) x

/-- Two elements of one stage with the same image in the colimit module agree at a deeper stage. -/
private theorem exists_map_eq_of_ι_eq {j : J} {y y' : (X.obj j).obj.V} (h : ι X j y = ι X j y') :
    ∃ (l : J) (f : j ⟶ l), (X.map f).hom.hom y = (X.map f).hom.hom y' :=
  (Types.FilteredColimit.isColimit_eq_iff' (isColimitForget X) y y').1 h

/-- The colimit module, with the discrete topology. -/
private local instance : TopologicalSpace ↑(colimit (X ⋙ toModuleCat k G)) := ⊥

private local instance : DiscreteTopology ↑(colimit (X ⋙ toModuleCat k G)) := ⟨rfl⟩

/-- Scalar multiplication on the discrete colimit module is continuous: an element comes from a
stage, on which scalar multiplication is continuous. -/
private local instance : ContinuousSMul k ↑(colimit (X ⋙ toModuleCat k G)) := by
  refine ⟨continuous_prod_of_discrete_right.2 fun x ↦ ?_⟩
  obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
  have := (X.obj j).property.discreteTopology
  simp_rw [← map_smul]
  exact continuous_of_discreteTopology.comp (continuous_id.smul continuous_const)

/-- The continuous representation of `G` on the discrete colimit module. -/
private noncomputable def colimitρ : ContRepresentation k G ↑(colimit (X ⋙ toModuleCat k G)) :=
  .ofMonoidHom
    { toFun g := ⟨act X g, continuous_of_discreteTopology⟩
      map_one' := ContinuousLinearMap.ext fun x ↦ by
        obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
        simp only [ContinuousLinearMap.coe_mk', act_ι_apply, map_one,
          one_apply_eq_self]
      map_mul' g h := ContinuousLinearMap.ext fun x ↦ by
        obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
        simp only [ContinuousLinearMap.coe_mk', mul_apply_eq_comp, act_ι_apply,
          map_mul] }

/-- The representation on the colimit restricts to the representation at each stage. -/
private theorem colimitρ_ι_apply (g : G) {j : J} (y : (X.obj j).obj.V) :
    colimitρ X g (ι X j y) = ι X j ((X.obj j).obj.ρ g y) :=
  act_ι_apply X g y

/-- The stabilizers of the colimit are open: the stabilizer of the image of `y` is the union of the
stabilizers of the images of `y` at the deeper stages. -/
private theorem isSmoothDiscrete_colimit : IsSmoothDiscrete k (TopRep.of (colimitρ X)) := by
  refine ⟨inferInstanceAs (DiscreteTopology ↑(colimit (X ⋙ toModuleCat k G))), fun x ↦ ?_⟩
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
underlying modules, with the discrete topology and the induced action. -/
private noncomputable def colimitObj : SmoothDiscreteTopRep.{v, u, w} k G :=
  ⟨TopRep.of (colimitρ X), isSmoothDiscrete_colimit X⟩

/-- The colimit cocone of a filtered diagram of smooth discrete representations, whose legs are the
colimit legs of the underlying modules. -/
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

/-- The morphism out of the colimit to the apex of a cocone `s`: the descended map of the
underlying modules, which is continuous because the colimit is discrete. -/
private noncomputable def desc (s : Cocone X) : colimitObj X ⟶ s.pt :=
  have hdesc (j : J) (y : (X.obj j).obj.V) :
      (colimit.desc (X ⋙ toModuleCat k G) ((toModuleCat k G).mapCocone s)).hom (ι X j y) =
        (s.ι.app j).hom.hom y :=
    colimit.ι_desc_apply ((toModuleCat k G).mapCocone s) j y
  have : DiscreteTopology (colimitObj X).obj.V := (colimitObj X).property.discreteTopology
  ObjectProperty.homMk <| ConcreteCategory.ofHom
    { toContinuousLinearMap := ⟨(colimit.desc (X ⋙ toModuleCat k G)
        ((toModuleCat k G).mapCocone s)).hom, continuous_of_discreteTopology⟩
      isIntertwining' g := ContinuousLinearMap.ext fun x ↦ by
        obtain ⟨j, y, rfl⟩ := exists_ι_eq X x
        exact (congrArg _ (colimitρ_ι_apply X g y)).trans <| (hdesc j _).trans <|
          (TopRep.hom_comm_apply (s.ι.app j).hom g y).trans (congrArg _ (hdesc j y).symm) }

/-- The morphism out of the colimit restricts to the legs of `s`. -/
private theorem desc_ι_apply (s : Cocone X) (j : J) (y : (X.obj j).obj.V) :
    (desc X s).hom.hom (ι X j y) = (s.ι.app j).hom.hom y :=
  colimit.ι_desc_apply ((toModuleCat k G).mapCocone s) j y

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
the colimit of the underlying modules, with the discrete topology and the induced action. -/
instance hasFilteredColimits : HasFilteredColimits (SmoothDiscreteTopRep.{v, u, w} k G) where
  HasColimitsOfShape _ _ _ := ⟨fun X ↦ ⟨_, colimitCoconeIsColimit X⟩⟩

/-- **The forgetful functor from smooth discrete representations to types preserves filtered
colimits.** A colimit cocone of a filtered diagram in `SmoothDiscreteTopRep k G` is a colimit on
underlying sets. -/
instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (smoothDiscreteι k G ⋙ forget (TopRep.{w} k G)) where
  preserves_filtered_colimits _ _ _ := ⟨fun {X} ↦
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit X) (isColimitForget X)⟩

end TauCeti.SmoothDiscreteTopRep
