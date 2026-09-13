/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

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

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]

private def fixedPointsQuotientMapAddSubgroup {G : Type u} [Group G]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M]
    [DistribMulAction G N] (f : M →+[G] N) (H : Subgroup G) [H.Normal] :
    FixedPoints.addSubgroup H M →+[G ⧸ H] FixedPoints.addSubgroup H N := by
  letI : DistribMulAction (G ⧸ H) (FixedPoints.addSubgroup H M) :=
    inferInstanceAs <| DistribMulAction (G ⧸ H) (FixedPoints.addSubmonoid H M)
  letI : DistribMulAction (G ⧸ H) (FixedPoints.addSubgroup H N) :=
    inferInstanceAs <| DistribMulAction (G ⧸ H) (FixedPoints.addSubmonoid H N)
  refine {
    toAddMonoidHom := {
      toFun := fun m =>
        let m' : FixedPoints.addSubmonoid H M := ⟨(m : M), m.2⟩
        let n' := fixedPointsQuotientMap f H m'
        ⟨(n' : N), n'.2⟩
      map_zero' := by simp
      map_add' _ _ := by simp }
    map_smul' := ?_ }
  intro q m
  induction q using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    dsimp
    rw [coe_fixedPointsQuotientMap, coe_fixedPointsQuotientMap]
    -- The private bridge changes the carrier from `addSubgroup` to the generic fixed-point
    -- `addSubmonoid`; expose the underlying coefficient equality to apply equivariance of `f`.
    change f (g • (m : M)) = g • f (m : M)
    exact f.map_smul g (m : M)

private theorem coe_fixedPointsQuotientMapAddSubgroup {G : Type u} [Group G]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M]
    [DistribMulAction G N] (f : M →+[G] N) (H : Subgroup G) [H.Normal]
    (m : FixedPoints.addSubgroup H M) :
    (fixedPointsQuotientMapAddSubgroup f H m : N) = f (m : M) := by
  -- The bridge is defined through the generic `addSubmonoid` map, so this reduction exposes its
  -- underlying value before applying the generic coercion theorem.
  change (fixedPointsQuotientMap f H ⟨(m : M), m.2⟩ : N) = f (m : M)
  exact coe_fixedPointsQuotientMap f H ⟨(m : M), m.2⟩

private def fixedPointsInclusion_onAddSubgroup {G : Type u} [Group G]
    {M : Type v} [AddCommGroup M] [DistribMulAction G M]
    {H K : Subgroup G} (h : K ≤ H) :
    FixedPoints.addSubgroup H M →+ FixedPoints.addSubgroup K M where
  toFun m :=
    ⟨(fixedPointsInclusion h ⟨(m : M), m.2⟩ : M),
      (fixedPointsInclusion h ⟨(m : M), m.2⟩).2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

section Transition

variable {U V W : OpenNormalSubgroup G}

/-- The degree-zero transition from the `U`-level to the `V`-level, for `V ≤ U`. -/
noncomputable def explicitFiniteQuotientTransition0 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
    H0 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  by
    letI : DistribMulAction (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) :=
      inferInstanceAs <| DistribMulAction (G ⧸ U.toSubgroup)
        (FixedPoints.addSubmonoid U.toSubgroup M)
    letI : DistribMulAction (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
      inferInstanceAs <| DistribMulAction (G ⧸ V.toSubgroup)
        (FixedPoints.addSubmonoid V.toSubgroup M)
    exact explicitMap0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
      (QuotientGroup.mapOfLE hVU)
      (fixedPointsInclusion_onAddSubgroup hVU)
      (by
        intro q m
        induction q using QuotientGroup.induction_on with
        | H g =>
          apply Subtype.ext
          simp [fixedPointsInclusion_onAddSubgroup])

/-- Coercion of a degree-zero transition to the coefficient group. -/
@[simp]
theorem coe_explicitFiniteQuotientTransition0 (hVU : V ≤ U)
    (x : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    (explicitFiniteQuotientTransition0 G M U V hVU x : M) = (x : M) :=
  by
    unfold explicitFiniteQuotientTransition0
    rw [coe_explicitMap0]
    exact coe_fixedPointsInclusion hVU ⟨(x : M), x.1.2⟩

/-- The transition at an open normal subgroup is the identity. -/
@[simp]
theorem explicitFiniteQuotientTransition0_id (U : OpenNormalSubgroup G) :
    explicitFiniteQuotientTransition0 G M U U le_rfl = AddMonoidHom.id _ := by
  unfold explicitFiniteQuotientTransition0
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [coe_explicitMap0, AddMonoidHom.id_apply]
  apply Subtype.ext
  simp [fixedPointsInclusion_onAddSubgroup]

/-- Degree-zero transitions compose along inclusions of open normal subgroups. -/
theorem explicitFiniteQuotientTransition0_comp (U V W : OpenNormalSubgroup G)
    (hVU : V ≤ U) (hWV : W ≤ V) :
    explicitFiniteQuotientTransition0 G M U W (hWV.trans hVU) =
      (explicitFiniteQuotientTransition0 G M V W hWV).comp
        (explicitFiniteQuotientTransition0 G M U V hVU) := by
  unfold explicitFiniteQuotientTransition0
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [coe_explicitMap0, AddMonoidHom.comp_apply]
  apply Subtype.ext
  simp [fixedPointsInclusion_onAddSubgroup]

private theorem explicitFiniteQuotientTransition0_inflation (hVU : V ≤ U)
    (x : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    explicitInfl0 G M V.toSubgroup
        (explicitFiniteQuotientTransition0 G M U V hVU x) =
      explicitInfl0 G M U.toSubgroup x := by
  apply Subtype.ext
  simp only [coe_explicitInfl0, coe_explicitFiniteQuotientTransition0]

/-- Every degree-zero transition is a bijection: both its source and target are the global
invariants, with the map acting as the identity on the underlying coefficient. -/
theorem explicitFiniteQuotientTransition0_bijective (hVU : V ≤ U) :
    Function.Bijective (explicitFiniteQuotientTransition0 G M U V hVU) := by
  have hU := TauCeti.ContCohomology.explicitInfl0_bijective G M U.toSubgroup
  have hV := TauCeti.ContCohomology.explicitInfl0_bijective G M V.toSubgroup
  constructor
  · intro x y hxy
    apply hU.1
    rw [← explicitFiniteQuotientTransition0_inflation G M hVU x,
      ← explicitFiniteQuotientTransition0_inflation G M hVU y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hU.2 (explicitInfl0 G M V.toSubgroup y)
    refine ⟨x, ?_⟩
    apply hV.1
    rw [explicitFiniteQuotientTransition0_inflation G M hVU, hx]

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

/-- The object at `U` of the degree-zero finite-quotient system. -/
@[simp]
theorem explicitFiniteQuotientSystem0_obj (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientSystem0 G M).obj (Opposite.op U) =
      AddCommGrpCat.of (H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  by
    unfold explicitFiniteQuotientSystem0
    rfl

/-- The map of the degree-zero finite-quotient system at a morphism `f`. -/
@[simp]
theorem explicitFiniteQuotientSystem0_map {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U.unop).symm ≫
        (explicitFiniteQuotientSystem0 G M).map f ≫
      eqToHom (explicitFiniteQuotientSystem0_obj G M V.unop) = AddCommGrpCat.ofHom
      (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop)) :=
  by
    unfold explicitFiniteQuotientSystem0
    rfl

/-- Every morphism in the degree-zero finite-quotient system is an isomorphism. -/
instance explicitFiniteQuotientSystem0_map_isIso
    {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    IsIso ((explicitFiniteQuotientSystem0 G M).map f) := by
  unfold explicitFiniteQuotientSystem0
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact explicitFiniteQuotientTransition0_bijective G M (leOfHom f.unop)

end System

section CoefficientFunctoriality

variable {N : Type v} [AddCommGroup N] [DistribMulAction G N]

/-- A coefficient homomorphism induces a natural transformation between the degree-zero
finite-quotient systems. -/
noncomputable def explicitFiniteQuotientSystem0CoeffNatTrans (f : M →+[G] N) :
    explicitFiniteQuotientSystem0 G M ⟶ explicitFiniteQuotientSystem0 G N where
  app U := AddCommGrpCat.ofHom (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
    (FixedPoints.addSubgroup U.unop.toSubgroup M)
    (fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup))
  naturality := by
    intro U V h
    dsimp [explicitFiniteQuotientSystem0, Functor.const_obj_map]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    simp only [coe_explicitCoeff0, coe_explicitFiniteQuotientTransition0,
      coe_fixedPointsQuotientMapAddSubgroup]

@[simp]
theorem explicitFiniteQuotientSystem0_coeffNatTrans_app (f : M →+[G] N)
    (U : OpenNormalSubgroup G) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U).symm ≫
        (explicitFiniteQuotientSystem0CoeffNatTrans G M f).app (Opposite.op U) ≫
      eqToHom (explicitFiniteQuotientSystem0_obj G N U) =
      AddCommGrpCat.ofHom (explicitCoeff0 (G ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M)
        (by
          letI : DistribMulAction (G ⧸ U.toSubgroup)
              (FixedPoints.addSubgroup U.toSubgroup M) :=
            inferInstanceAs <| DistribMulAction (G ⧸ U.toSubgroup)
              (FixedPoints.addSubmonoid U.toSubgroup M)
          letI : DistribMulAction (G ⧸ U.toSubgroup)
              (FixedPoints.addSubgroup U.toSubgroup N) :=
            inferInstanceAs <| DistribMulAction (G ⧸ U.toSubgroup)
              (FixedPoints.addSubmonoid U.toSubgroup N)
          exact fixedPointsQuotientMap f U.toSubgroup)) := by
  unfold explicitFiniteQuotientSystem0CoeffNatTrans
  rfl

@[simp]
theorem explicitFiniteQuotientSystem0_coeffNatTrans_id :
    explicitFiniteQuotientSystem0CoeffNatTrans G M
        (DistribMulActionHom.id G) = 𝟙 (explicitFiniteQuotientSystem0 G M) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  dsimp [explicitFiniteQuotientSystem0CoeffNatTrans]
  let x' : H0 (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M) := x
  -- Extensionality has reduced the natural-transformation and cohomology wrappers to the
  -- underlying coefficient map; this is the carrier expected by the coercion lemma below.
  change
    (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M)
      (fixedPointsQuotientMapAddSubgroup (DistribMulActionHom.id G) U.unop.toSubgroup)
      x' : M) = (x' : M)
  simp only [coe_explicitCoeff0, coe_fixedPointsQuotientMapAddSubgroup]
  rfl

theorem explicitFiniteQuotientSystem0_coeffNatTrans_comp
    {P : Type v} [AddCommGroup P] [DistribMulAction G P]
    (f : M →+[G] N) (q : N →+[G] P) :
    explicitFiniteQuotientSystem0CoeffNatTrans G M (q.comp f) =
      explicitFiniteQuotientSystem0CoeffNatTrans G M f ≫
        explicitFiniteQuotientSystem0CoeffNatTrans G N q := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  dsimp [explicitFiniteQuotientSystem0CoeffNatTrans]
  let x' : H0 (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M) := x
  -- As above, expose the underlying coefficient values after removing the categorical wrappers.
  change
    (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M)
      (fixedPointsQuotientMapAddSubgroup (q.comp f) U.unop.toSubgroup)
      x' : P) =
      (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
          (FixedPoints.addSubgroup U.unop.toSubgroup N)
          (fixedPointsQuotientMapAddSubgroup q U.unop.toSubgroup)
        (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
          (FixedPoints.addSubgroup U.unop.toSubgroup M)
          (fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup)
          x') : P)
  simp only [coe_explicitCoeff0, coe_fixedPointsQuotientMapAddSubgroup]
  rfl

end CoefficientFunctoriality

section Comparison

variable {N : Type v} [AddCommGroup N] [DistribMulAction G N]

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
    dsimp [explicitFiniteQuotientSystem0, Functor.const_obj_map]
    exact explicitFiniteQuotientTransition0_inflation G M (leOfHom f.unop) x'

/-- Coefficient maps commute with the degree-zero comparison maps. -/
@[simp]
theorem explicitFiniteQuotientComparison0_coeffNatTrans_naturality
    (f : M →+[G] N) :
    explicitFiniteQuotientSystem0CoeffNatTrans G M f ≫
        explicitFiniteQuotientComparison0 G N =
      explicitFiniteQuotientComparison0 G M ≫
        (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).map
          (AddCommGrpCat.ofHom (explicitCoeff0 G M f)) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  let x' : H0 (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M) := x
  -- The comparison square is an equality of underlying coefficients after subtype extensionality;
  -- this reduction makes the two explicit coefficient maps visible.
  change ((explicitInfl0 G N U.unop.toSubgroup
      (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
        (FixedPoints.addSubgroup U.unop.toSubgroup M)
        (fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup) x')) : N) =
    (explicitCoeff0 G M f (explicitInfl0 G M U.unop.toSubgroup x') : N)
  calc
    ((explicitInfl0 G N U.unop.toSubgroup
        (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
          (FixedPoints.addSubgroup U.unop.toSubgroup M)
          (fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup) x')) : N) =
      (explicitCoeff0 (G ⧸ U.unop.toSubgroup)
        (FixedPoints.addSubgroup U.unop.toSubgroup M)
        (fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup) x' : N) :=
      coe_explicitInfl0 G N U.unop.toSubgroup _
    _ = (fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup x' : N) := by
      exact congrArg (fun z : FixedPoints.addSubgroup U.unop.toSubgroup N => (z : N))
        (coe_explicitCoeff0 (G := G ⧸ U.unop.toSubgroup)
          (M := FixedPoints.addSubgroup U.unop.toSubgroup M)
          (f := fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup) x')
    _ = f (x' : M) := coe_fixedPointsQuotientMapAddSubgroup f U.unop.toSubgroup x'
    _ = f (explicitInfl0 G M U.unop.toSubgroup x' : M) := by rw [coe_explicitInfl0]
    _ = (explicitCoeff0 G M f (explicitInfl0 G M U.unop.toSubgroup x') : N) :=
      (coe_explicitCoeff0 G M f _).symm

/-- The named comparison cocone for degree zero, with apex `H⁰(G, M)`. -/
noncomputable def explicitFiniteQuotientCocone0 :
    Cocone (explicitFiniteQuotientSystem0 G M) where
  pt := AddCommGrpCat.of (H0 G M)
  ι := explicitFiniteQuotientComparison0 G M

/-- The degree-zero comparison map at `U` is inflation from the quotient level. -/
@[simp]
theorem explicitFiniteQuotientComparison0_app (U : OpenNormalSubgroup G) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U).symm ≫
        (explicitFiniteQuotientComparison0 G M).app (Opposite.op U) =
      AddCommGrpCat.ofHom (explicitInfl0 G M U.toSubgroup) := by
  unfold explicitFiniteQuotientComparison0
  rfl

/-- The apex of the named degree-zero comparison cocone is `H⁰(G, M)`. -/
@[simp]
theorem explicitFiniteQuotientCocone0_pt :
    (explicitFiniteQuotientCocone0 G M).pt = AddCommGrpCat.of (H0 G M) := by
  unfold explicitFiniteQuotientCocone0
  rfl

private theorem explicitFiniteQuotientSystem0_isEventuallyConstantFrom :
    (explicitFiniteQuotientSystem0 G M).IsEventuallyConstantFrom
      (Opposite.op (⊤ : OpenNormalSubgroup G)) := by
  let _ : Nonempty (OpenNormalSubgroup G) := ⟨⊤⟩
  intro U f
  infer_instance

/-- The degree-zero comparison cocone is colimiting. -/
noncomputable def explicitFiniteQuotientColimit0 :
    IsColimit (explicitFiniteQuotientCocone0 G M) := by
  letI : Nonempty (OpenNormalSubgroup G) := ⟨⊤⟩
  let h := explicitFiniteQuotientSystem0_isEventuallyConstantFrom G M
  letI : IsIso ((explicitFiniteQuotientCocone0 G M).ι.app
      (Opposite.op (⊤ : OpenNormalSubgroup G))) := by
    dsimp [explicitFiniteQuotientCocone0]
    apply (ConcreteCategory.isIso_iff_bijective _).2
    dsimp [explicitFiniteQuotientSystem0, explicitFiniteQuotientComparison0]
    exact explicitInfl0_bijective G M (⊤ : OpenNormalSubgroup G).toSubgroup
  exact h.isColimitOfIsIso (explicitFiniteQuotientCocone0 G M)

end Comparison

end TauCeti.ContCohomology
