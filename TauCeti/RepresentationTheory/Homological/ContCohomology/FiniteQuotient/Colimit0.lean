/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Explicit

/-!
# The degree-zero finite-quotient colimit

For a profinite group `G` acting continuously on a discrete additive group `M`, the degree-zero
finite-level groups

```text
H⁰(G ⧸ U, M^U)
```

form a system as `U` ranges over open normal subgroups and shrinks. Every one of these groups is
canonically the group of global invariants `H⁰(G, M)`: invariance under the quotient action is
exactly invariance under `G`. Consequently the inflation legs and all transition maps are
isomorphisms, and the named comparison cocone is colimiting.

This is the degree-zero part of the finite-quotient description of continuous cohomology. The
positive-degree systems are separate because their transitions are not automatically isomorphisms;
in particular, degree one requires strict descent of continuous cocycles and degree two requires
uniform local constancy on a product.

## Main definitions

* `explicitFiniteQuotientTransition0`: the degree-zero transition for `V ≤ U`.
* `explicitFiniteQuotientSystem0`: the resulting functor on
  `(OpenNormalSubgroup G)ᵒᵖ`.
* `explicitFiniteQuotientComparison0` and `explicitFiniteQuotientCocone0`: the named inflation
  legs with apex `H⁰(G, M)`.

## Main statements

* `explicitFiniteQuotientTransition0_bijective`: every degree-zero transition is bijective.
* `explicitFiniteQuotientColimit0`: the comparison cocone is a colimit cocone.

The construction follows Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, (1.2.5),
and Ribes and Zalesskii, *Profinite Groups*, Corollary 6.5.6(a). It uses Mathlib's
`Functor.IsEventuallyConstantFrom` to express that the degree-zero system is already constant at
the top open normal subgroup.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ContCohomology

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

private def finiteLevelLift (U : OpenNormalSubgroup G) (m : M)
    (hm : ∀ g : G, g • m = m) :
    H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) :=
  let mU : FixedPoints.addSubgroup U.toSubgroup M :=
    ⟨m, (FixedPoints.mem_addSubgroup U.toSubgroup M m).2 (fun u => hm (u : G))⟩
  ⟨mU, (FixedPoints.mem_addSubgroup (G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M) mU).2 (by
    intro q
    induction q using QuotientGroup.induction_on with
    | _ g =>
      apply Subtype.ext
      simpa only [coe_quotient_smul_fixedPoints_addSubgroup,
        coe_smul_fixedPoints_addSubgroup] using hm g)⟩

omit [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
private theorem coe_finiteLevelLift (U : OpenNormalSubgroup G) (m : M)
    (hm : ∀ g : G, g • m = m) :
    (finiteLevelLift G M U m hm : M) = m :=
  rfl

section Transition

variable {U V W : OpenNormalSubgroup G}

/-- The degree-zero transition from the `U`-level to the `V`-level, for `V ≤ U`. -/
noncomputable def explicitFiniteQuotientTransition0 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
      H0 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  explicitMap0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
    (continuousFiniteQuotientMap G hVU)
    (by
      change AddMonoidHom (FixedPoints.addSubmonoid U.toSubgroup M)
        (FixedPoints.addSubmonoid V.toSubgroup M)
      exact fixedPointsInclusion hVU)
    (fun q m => by
      induction q using QuotientGroup.induction_on with
      | H g =>
        apply Subtype.ext
        have hmap :
            (continuousFiniteQuotientMap G hVU :
              (G ⧸ V.toSubgroup) →* (G ⧸ U.toSubgroup)) (g : G ⧸ V.toSubgroup) =
              (g : G ⧸ U.toSubgroup) := continuousFiniteQuotientMap_mk G hVU g
        rw [hmap]
        dsimp
        exact congrArg Subtype.val (fixedPointsInclusion_smul (M := M) hVU g m))

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem coe_explicitFiniteQuotientTransition0 (hVU : V ≤ U)
    (x : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    (explicitFiniteQuotientTransition0 G M U V hVU x : M) = (x : M) :=
  by
    unfold explicitFiniteQuotientTransition0
    rw [coe_explicitMap0]
    exact coe_fixedPointsInclusion hVU (x : FixedPoints.addSubgroup U.toSubgroup M)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem explicitFiniteQuotientTransition0_id (U : OpenNormalSubgroup G) :
    explicitFiniteQuotientTransition0 G M U U le_rfl = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  exact Subtype.ext (Subtype.ext (coe_explicitFiniteQuotientTransition0 G M le_rfl x))

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
theorem explicitFiniteQuotientTransition0_comp (U V W : OpenNormalSubgroup G)
    (hVU : V ≤ U) (hWV : W ≤ V) :
    explicitFiniteQuotientTransition0 G M U W (hWV.trans hVU) =
      (explicitFiniteQuotientTransition0 G M V W hWV).comp
        (explicitFiniteQuotientTransition0 G M U V hVU) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  simp only [AddMonoidHom.coe_comp, Function.comp_apply,
    coe_explicitFiniteQuotientTransition0]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
private theorem explicitFiniteQuotientTransition0_injective (hVU : V ≤ U) :
    Function.Injective (explicitFiniteQuotientTransition0 G M U V hVU) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  simpa only [coe_explicitFiniteQuotientTransition0 G M hVU] using
    congrArg (fun z : H0 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) =>
      ((z : FixedPoints.addSubgroup V.toSubgroup M) : M)) hxy

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
private theorem explicitFiniteQuotientTransition0_surjective (hVU : V ≤ U) :
    Function.Surjective (explicitFiniteQuotientTransition0 G M U V hVU) := by
  intro y
  have hyG : ∀ g : G, g • (y : M) = (y : M) := by
    intro g
    have hy := (FixedPoints.mem_addSubgroup (G ⧸ V.toSubgroup)
      (FixedPoints.addSubgroup V.toSubgroup M) (y : FixedPoints.addSubgroup V.toSubgroup M)).1
      y.2 (QuotientGroup.mk g)
    simpa only [coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup]
      using congrArg Subtype.val hy
  refine ⟨finiteLevelLift G M U (y : M) hyG, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [coe_explicitFiniteQuotientTransition0 G M hVU,
    coe_finiteLevelLift]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
/-- Every degree-zero transition is a bijection: both its source and target are the global
invariants, with the map acting as the identity on the underlying coefficient. -/
theorem explicitFiniteQuotientTransition0_bijective (hVU : V ≤ U) :
    Function.Bijective (explicitFiniteQuotientTransition0 G M U V hVU) :=
  ⟨explicitFiniteQuotientTransition0_injective G M hVU,
    explicitFiniteQuotientTransition0_surjective G M hVU⟩

end Transition

section System

/-- The degree-zero finite-quotient system of a discrete module. -/
noncomputable def explicitFiniteQuotientSystem0 :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj U := AddCommGrpCat.of
    (H0 (G ⧸ U.unop.toSubgroup) (FixedPoints.addSubgroup U.unop.toSubgroup M))
  map := fun {U V} f => AddCommGrpCat.ofHom
    (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop))
  map_id U := by
    rw [explicitFiniteQuotientTransition0_id]
    rfl
  map_comp f g := by
    rw [explicitFiniteQuotientTransition0_comp G M _ _ _
      (leOfHom f.unop) (leOfHom g.unop)]
    rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem explicitFiniteQuotientSystem0_obj (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientSystem0 G M).obj (Opposite.op U) =
      AddCommGrpCat.of (H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  by
    unfold explicitFiniteQuotientSystem0
    rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem explicitFiniteQuotientSystem0_map {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U.unop).symm ≫
        (explicitFiniteQuotientSystem0 G M).map f ≫
      eqToHom (explicitFiniteQuotientSystem0_obj G M V.unop) = AddCommGrpCat.ofHom
      (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop)) :=
  by
    unfold explicitFiniteQuotientSystem0
    rfl

end System

section Comparison

/-- The degree-zero comparison legs are inflation from the finite quotient to `G`. -/
noncomputable def explicitFiniteQuotientComparison0 :
    explicitFiniteQuotientSystem0 G M ⟶
      (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).obj (AddCommGrpCat.of (H0 G M)) where
  app U := AddCommGrpCat.ofHom (explicitInfl0 G M U.unop.toSubgroup)
  naturality := by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    let x' : H0 (G ⧸ U.unop.toSubgroup)
        (FixedPoints.addSubgroup U.unop.toSubgroup M) := x
    -- Expose the underlying additive maps before using the coefficient-level formulas.
    change explicitInfl0 G M V.unop.toSubgroup
        (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop) x') =
      explicitInfl0 G M U.unop.toSubgroup x'
    apply Subtype.ext
    calc
      (explicitInfl0 G M V.unop.toSubgroup
          (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop) x')) =
          (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop) x' : M) :=
        coe_explicitInfl0 G M V.unop.toSubgroup _
      _ = (x' : M) := coe_explicitFiniteQuotientTransition0 G M (leOfHom f.unop) x'
      _ = (explicitInfl0 G M U.unop.toSubgroup x' : M) :=
        (coe_explicitInfl0 G M U.unop.toSubgroup x').symm

/-- The named comparison cocone for degree zero, with apex `H⁰(G, M)`. -/
noncomputable def explicitFiniteQuotientCocone0 :
    Cocone (explicitFiniteQuotientSystem0 G M) where
  pt := AddCommGrpCat.of (H0 G M)
  ι := explicitFiniteQuotientComparison0 G M

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem explicitFiniteQuotientComparison0_app (U : OpenNormalSubgroup G) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U).symm ≫
        (explicitFiniteQuotientComparison0 G M).app (Opposite.op U) =
      AddCommGrpCat.ofHom (explicitInfl0 G M U.toSubgroup) := by
  unfold explicitFiniteQuotientComparison0
  rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem explicitFiniteQuotientCocone0_pt :
    (explicitFiniteQuotientCocone0 G M).pt = AddCommGrpCat.of (H0 G M) := by
  unfold explicitFiniteQuotientCocone0
  rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
@[simp]
theorem explicitFiniteQuotientCocone0_ι_app (U : OpenNormalSubgroup G) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U).symm ≫
        (explicitFiniteQuotientCocone0 G M).ι.app (Opposite.op U) ≫
      eqToHom (explicitFiniteQuotientCocone0_pt (G := G) (M := M)) =
      AddCommGrpCat.ofHom (explicitInfl0 G M U.toSubgroup) := by
  unfold explicitFiniteQuotientCocone0 explicitFiniteQuotientComparison0
  rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
private theorem explicitFiniteQuotientComparison0_bijective (U : OpenNormalSubgroup G) :
    Function.Bijective ((explicitFiniteQuotientComparison0 G M).app (Opposite.op U)) := by
  -- Identify the component of the comparison transformation with its inflation hom.
  change Function.Bijective (explicitInfl0 G M U.toSubgroup)
  exact explicitInfl0_bijective G M U.toSubgroup

private def topOpenNormalSubgroup : OpenNormalSubgroup G :=
  { toOpenSubgroup := ⊤
    isNormal' := Subgroup.normal_top }

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M] in
private theorem explicitFiniteQuotientSystem0_isEventuallyConstantFrom :
    (explicitFiniteQuotientSystem0 G M).IsEventuallyConstantFrom
      (Opposite.op (topOpenNormalSubgroup G)) := by
  let _ : Nonempty (OpenNormalSubgroup G) := ⟨topOpenNormalSubgroup G⟩
  intro U f
  unfold explicitFiniteQuotientSystem0
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (explicitFiniteQuotientTransition0_bijective G M (leOfHom f.unop))

/-- The degree-zero comparison cocone is colimiting. -/
noncomputable def explicitFiniteQuotientColimit0 :
    IsColimit (explicitFiniteQuotientCocone0 G M) := by
  letI : Nonempty (OpenNormalSubgroup G) := ⟨topOpenNormalSubgroup G⟩
  let h := explicitFiniteQuotientSystem0_isEventuallyConstantFrom G M
  letI : IsIso ((explicitFiniteQuotientCocone0 G M).ι.app
      (Opposite.op (topOpenNormalSubgroup G))) := by
    dsimp [explicitFiniteQuotientCocone0]
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (explicitFiniteQuotientComparison0_bijective G M (topOpenNormalSubgroup G))
  exact h.isColimitOfIsIso (explicitFiniteQuotientCocone0 G M)

end Comparison

end TauCeti.ContCohomology
