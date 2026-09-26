/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Invariants

/-!
# The explicit low-degree finite-quotient systems

For a topological group `G` acting on a discrete additive group `M`, the explicit
cohomology groups in degrees zero, one, and two

```text
Hⁱ(G ⧸ U, M^U),  i = 0, 1, 2,
```

form a directed system as the open normal subgroup `U` shrinks.  If `V ≤ U`, its transition
map is the compatible-pair pullback along the quotient homomorphism `G ⧸ V → G ⧸ U` and the
coefficient inclusion `M^U → M^V`.
When `G` is compact these discrete quotient groups are finite; the construction itself requires
neither compactness nor continuity of the action of `G` on `M`.

`TauCeti.finiteQuotientSystem` already packages the corresponding system in Mathlib's discrete
`groupCohomology`.  The systems here are instead constructed directly with
`TauCeti.ContCohomology.explicitMap0`, `explicitMap1`, and `explicitMap2`. In particular they are
universe-polymorphic and do not transport their arrows through the universe-restricted comparison
with discrete group cohomology.  They are the source diagrams for the explicit finite-quotient
colimit theorems in degrees zero, one, and two.

## Main definitions

* `TauCeti.ContCohomology.explicitFiniteQuotientTransition0`: the transition
  `H⁰(G ⧸ U, M^U) → H⁰(G ⧸ V, M^V)` for `V ≤ U`.
* `TauCeti.ContCohomology.explicitFiniteQuotientSystem0`: the resulting functor on
  `(OpenNormalSubgroup G)ᵒᵖ`.
* `TauCeti.ContCohomology.explicitFiniteQuotientTransition1`: the transition
  `H¹(G ⧸ U, M^U) → H¹(G ⧸ V, M^V)` for `V ≤ U`.
* `TauCeti.ContCohomology.explicitFiniteQuotientSystem1`: the resulting functor on
  `(OpenNormalSubgroup G)ᵒᵖ`.
* `TauCeti.ContCohomology.explicitFiniteQuotientTransition2` and
  `explicitFiniteQuotientSystem2`: the corresponding transition and functor in degree two.

## Main statements

* `explicitFiniteQuotientTransition0_eq_explicitMap0` identifies the degree-zero transition with
  compatible-pair pullback; its identity, composition, object, and arrow lemmas give the same
  characteristic API as the positive-degree systems.
* `explicitFiniteQuotientTransition1_eq_explicitMap1` identifies a transition map with the
  compatible-pair pullback it is built from.
* `explicitFiniteQuotientTransition1_id` and `explicitFiniteQuotientTransition1_comp` are the
  identity and composition laws for the transition maps.
* `explicitFiniteQuotientSystem1_obj` and `explicitFiniteQuotientSystem1_map` identify the
  objects and arrows of the packaged functor.
* The corresponding declarations ending in `2` give the same characteristic API in degree two.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Cor. 6.5.6(a).
-/

public section

namespace TauCeti.ContCohomology

open CategoryTheory

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]

section Transition

variable {U V W : OpenNormalSubgroup G}

/-! ### Degree zero -/

/-- The explicit degree-zero transition from the `U`-level to the `V`-level, for `V ≤ U`.

It is compatible-pair pullback along `G ⧸ V → G ⧸ U` and the inclusion `M^U → M^V`.
On underlying coefficients it is just that inclusion. -/
def explicitFiniteQuotientTransition0 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
      H0 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  explicitMap0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
    (continuousFiniteQuotientMap G hVU)
    (fixedPointsInclusion (M := M) hVU : FixedPoints.addSubgroup U.toSubgroup M →+
      FixedPoints.addSubgroup V.toSubgroup M)
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] in
/-- A degree-zero finite-quotient transition does not change the underlying coefficient. -/
@[simp]
theorem coe_explicitFiniteQuotientTransition0 (hVU : V ≤ U)
    (m : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    ((explicitFiniteQuotientTransition0 G M U V hVU m :
        FixedPoints.addSubgroup V.toSubgroup M) : M) = (m : M) := by
  exact (congrArg (fun x : FixedPoints.addSubgroup V.toSubgroup M ↦ (x : M))
    (coe_explicitMap0 _ _ _ _ _ m)).trans (coe_fixedPointsInclusion hVU (m :
      FixedPoints.addSubgroup U.toSubgroup M))

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] in
/-- A degree-zero transition is the compatible-pair pullback along the quotient map and the
inclusion of invariant coefficients. -/
theorem explicitFiniteQuotientTransition0_eq_explicitMap0 (hVU : V ≤ U) :
    explicitFiniteQuotientTransition0 G M U V hVU =
      explicitMap0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (N := FixedPoints.addSubgroup V.toSubgroup M)
        (continuousFiniteQuotientMap G hVU)
        (fixedPointsInclusion (M := M) hVU : FixedPoints.addSubgroup U.toSubgroup M →+
          FixedPoints.addSubgroup V.toSubgroup M)
        (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) := (rfl)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] in
/-- The degree-zero transition from a level to itself is the identity. -/
@[simp]
theorem explicitFiniteQuotientTransition0_id (U : OpenNormalSubgroup G) :
    explicitFiniteQuotientTransition0 G M U U le_rfl = AddMonoidHom.id _ := by
  ext m
  exact coe_explicitFiniteQuotientTransition0 G M le_rfl m

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] in
/-- For `W ≤ V ≤ U`, the degree-zero transition from the `U`-level to the `W`-level is the
composite through the `V`-level. -/
theorem explicitFiniteQuotientTransition0_comp (U V W : OpenNormalSubgroup G)
    (hVU : V ≤ U) (hWV : W ≤ V) :
    explicitFiniteQuotientTransition0 G M U W (hWV.trans hVU) =
      (explicitFiniteQuotientTransition0 G M V W hWV).comp
        (explicitFiniteQuotientTransition0 G M U V hVU) := by
  ext m
  rw [AddMonoidHom.comp_apply, coe_explicitFiniteQuotientTransition0,
    coe_explicitFiniteQuotientTransition0, coe_explicitFiniteQuotientTransition0]

/-! ### Degree one -/

/-- The explicit degree-one transition from the `U`-level to the `V`-level, for `V ≤ U`.

It is defined directly by compatible-pair functoriality from the quotient homomorphism
`G ⧸ V → G ⧸ U` and the inclusion of invariant coefficients `M^U → M^V`. -/
noncomputable def explicitFiniteQuotientTransition1 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
      H1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  explicitMap1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
    (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
    (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
    continuous_of_discreteTopology
      (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)

/-- A degree-one finite-quotient transition sends the class of a cocycle to its compatible-pair
pullback. -/
@[simp]
theorem explicitFiniteQuotientTransition1_mk (hVU : V ≤ U)
    (c : Z1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    explicitFiniteQuotientTransition1 G M U V hVU
        (c : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) =
      H1pi (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (cocyclesMap1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) c) :=
  explicitMap1_mk _ _ _ _ _ _ _ _ c

/-- A degree-one finite-quotient transition is the compatible-pair pullback along the quotient
homomorphism `G ⧸ V → G ⧸ U` and the inclusion of invariant coefficients `M ^ U → M ^ V`. -/
-- The pullback is ascribed its type because `fixedPointsInclusion` is stated on
-- `FixedPoints.addSubmonoid`, so the coefficient instances of the right-hand side are fixed by the
-- left-hand side rather than synthesized on their own.
theorem explicitFiniteQuotientTransition1_eq_explicitMap1 (hVU : V ≤ U) :
    explicitFiniteQuotientTransition1 G M U V hVU =
      (explicitMap1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) :
        H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
          H1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)) := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    exact (explicitFiniteQuotientTransition1_mk G M hVU c).trans
      (explicitMap1_mk _ _ _ _ _ _ _ _ c).symm

/-- The transition from an open normal subgroup to itself is the identity. -/
@[simp]
theorem explicitFiniteQuotientTransition1_id (U : OpenNormalSubgroup G) :
    explicitFiniteQuotientTransition1 G M U U le_rfl = AddMonoidHom.id _ := by
  rw [explicitFiniteQuotientTransition1]
  calc
    _ = explicitMap1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (ContinuousMonoidHom.id _) (AddMonoidHom.id _) continuous_id (fun _ _ => rfl) := by
      apply explicitMap1_congr_of_eq
      · exact continuousFiniteQuotientMap_refl G U
      · exact fixedPointsInclusion_self M U.toSubgroup
    _ = AddMonoidHom.id _ := explicitMap1_id _ _ _

/-- For `W ≤ V ≤ U`, the transition from the `U`-level to the `W`-level is the composite
through the `V`-level. -/
theorem explicitFiniteQuotientTransition1_comp (U V W : OpenNormalSubgroup G)
    (hVU : V ≤ U) (hWV : W ≤ V) :
    explicitFiniteQuotientTransition1 G M U W (hWV.trans hVU) =
      (explicitFiniteQuotientTransition1 G M V W hWV).comp
        (explicitFiniteQuotientTransition1 G M U V hVU) :=
  (explicitMap1_congr_of_eq (hφeq := (continuousFiniteQuotientMap_comp G hWV hVU).symm)
    (hfeq := (fixedPointsInclusion_comp_fixedPointsInclusion hVU hWV).symm)).trans
      (explicitMap1_comp (hcomp := comp_apply_smul _ _ _ _
        (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)
        (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hWV)) ..)

end Transition

section System

/-! ### Degree zero -/

/-- The explicit degree-zero finite-quotient system. It sends an open normal subgroup `U` to
`H⁰(G ⧸ U, M^U)` and an inclusion `V ≤ U` to compatible-pair pullback from the `U`-level to
the `V`-level. -/
@[expose] def explicitFiniteQuotientSystem0 :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj U :=
    AddCommGrpCat.of
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

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] in
/-- The object at `U` of the degree-zero finite-quotient system is `H⁰(G ⧸ U, M^U)`. -/
@[simp]
theorem explicitFiniteQuotientSystem0_obj (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientSystem0 G M).obj (Opposite.op U) =
      AddCommGrpCat.of
        (H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  by rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] in
/-- Every arrow of the degree-zero finite-quotient system is the direct compatible-pair
transition. -/
@[simp]
theorem explicitFiniteQuotientSystem0_map
    {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    eqToHom (explicitFiniteQuotientSystem0_obj G M U.unop).symm ≫
        (explicitFiniteQuotientSystem0 G M).map f ≫
      eqToHom (explicitFiniteQuotientSystem0_obj G M V.unop) = AddCommGrpCat.ofHom
      (explicitFiniteQuotientTransition0 G M U.unop V.unop (leOfHom f.unop)) :=
  by rfl

/-! ### Degree one -/

/-- The explicit degree-one finite-quotient system of a discrete module.  It sends an open normal
subgroup `U` to `H¹(G ⧸ U, M^U)` and an inclusion `V ≤ U` to the direct explicit transition from
the `U`-level to the `V`-level. -/
-- The body is exposed because a cocone on this system is written with `H¹(G ⧸ U, M^U)` for its
-- source objects and `explicitFiniteQuotientTransition1` for its arrows, so both fields have to
-- reduce outside this module.
@[expose] noncomputable def explicitFiniteQuotientSystem1 :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U :=
    AddCommGrpCat.of
      (H1 (G ⧸ U.unop.toSubgroup) (FixedPoints.addSubgroup U.unop.toSubgroup M))
  map := fun {U V} f => AddCommGrpCat.ofHom
    (explicitFiniteQuotientTransition1 G M U.unop V.unop (leOfHom f.unop))
  map_id U := by
    rw [explicitFiniteQuotientTransition1_id]
    rfl
  map_comp f g := by
    rw [explicitFiniteQuotientTransition1_comp G M _ _ _
      (leOfHom f.unop) (leOfHom g.unop)]
    rfl

/-- The object at `U` of the explicit degree-one finite-quotient system is
`H¹(G ⧸ U, M^U)`. -/
@[simp]
theorem explicitFiniteQuotientSystem1_obj (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientSystem1 G M).obj (Opposite.op U) =
      AddCommGrpCat.of (H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  by rfl

/-- Under the object identifications above, every arrow of the explicit degree-one finite-quotient
system is the direct transition built from `explicitMap1`. -/
@[simp]
theorem explicitFiniteQuotientSystem1_map
    {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    eqToHom (explicitFiniteQuotientSystem1_obj G M U.unop).symm ≫
        (explicitFiniteQuotientSystem1 G M).map f ≫
      eqToHom (explicitFiniteQuotientSystem1_obj G M V.unop) = AddCommGrpCat.ofHom
      (explicitFiniteQuotientTransition1 G M U.unop V.unop (leOfHom f.unop)) :=
  by rfl

/-! ### Degree two -/

/-- The explicit degree-two transition from the `U`-level to the `V`-level, for `V ≤ U`.

It is defined directly by compatible-pair functoriality from the quotient homomorphism
`G ⧸ V → G ⧸ U` and the inclusion of invariant coefficients `M^U → M^V`. -/
noncomputable def explicitFiniteQuotientTransition2 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
      H2 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  explicitMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
    (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
    (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
    continuous_of_discreteTopology
      (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)

/-- A degree-two finite-quotient transition sends the class of a cocycle to its compatible-pair
pullback. -/
@[simp]
theorem explicitFiniteQuotientTransition2_mk {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (c : Z2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    explicitFiniteQuotientTransition2 G M U V hVU
        (c : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) =
      H2pi (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (cocyclesMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) c) :=
  explicitMap2_mk _ _ _ _ _ _ _ _ c

/-- A degree-two finite-quotient transition is the compatible-pair pullback along the quotient
homomorphism `G ⧸ V → G ⧸ U` and the inclusion of invariant coefficients `M^U → M^V`. -/
theorem explicitFiniteQuotientTransition2_eq_explicitMap2 {U V : OpenNormalSubgroup G}
    (hVU : V ≤ U) :
    explicitFiniteQuotientTransition2 G M U V hVU =
      (explicitMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) :
        H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
          H2 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)) := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    exact (explicitFiniteQuotientTransition2_mk G M hVU c).trans
      (explicitMap2_mk _ _ _ _ _ _ _ _ c).symm

/-- The degree-two transition from an open normal subgroup to itself is the identity. -/
@[simp]
theorem explicitFiniteQuotientTransition2_id (U : OpenNormalSubgroup G) :
    explicitFiniteQuotientTransition2 G M U U le_rfl = AddMonoidHom.id _ := by
  rw [explicitFiniteQuotientTransition2]
  calc
    _ = explicitMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (ContinuousMonoidHom.id _) (AddMonoidHom.id _) continuous_id (fun _ _ => rfl) := by
      apply explicitMap2_congr_of_eq
      · exact continuousFiniteQuotientMap_refl G U
      · exact fixedPointsInclusion_self M U.toSubgroup
    _ = AddMonoidHom.id _ := explicitMap2_id _ _

/-- For `W ≤ V ≤ U`, the degree-two transition from the `U`-level to the `W`-level is the
composite through the `V`-level. -/
theorem explicitFiniteQuotientTransition2_comp (U V W : OpenNormalSubgroup G)
    (hVU : V ≤ U) (hWV : W ≤ V) :
    explicitFiniteQuotientTransition2 G M U W (hWV.trans hVU) =
      (explicitFiniteQuotientTransition2 G M V W hWV).comp
        (explicitFiniteQuotientTransition2 G M U V hVU) :=
  (explicitMap2_congr_of_eq (hφeq := (continuousFiniteQuotientMap_comp G hWV hVU).symm)
    (hfeq := (fixedPointsInclusion_comp_fixedPointsInclusion hVU hWV).symm)).trans
      (explicitMap2_comp ..)

/-- The explicit degree-two finite-quotient system of a discrete module. It sends an open normal
subgroup `U` to `H²(G ⧸ U, M^U)` and an inclusion `V ≤ U` to the direct explicit transition from
the `U`-level to the `V`-level. -/
-- The body is exposed because a cocone on this system is written with `H²(G ⧸ U, M^U)` for its
-- source objects and `explicitFiniteQuotientTransition2` for its arrows, so both fields have to
-- reduce outside this module.
@[expose] noncomputable def explicitFiniteQuotientSystem2 :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U :=
    AddCommGrpCat.of
      (H2 (G ⧸ U.unop.toSubgroup) (FixedPoints.addSubgroup U.unop.toSubgroup M))
  map := fun {U V} f => AddCommGrpCat.ofHom
    (explicitFiniteQuotientTransition2 G M U.unop V.unop (leOfHom f.unop))
  map_id U := by
    rw [explicitFiniteQuotientTransition2_id]
    rfl
  map_comp f g := by
    rw [explicitFiniteQuotientTransition2_comp G M _ _ _
      (leOfHom f.unop) (leOfHom g.unop)]
    rfl

/-- The object at `U` of the explicit degree-two finite-quotient system is
`H²(G ⧸ U, M^U)`. -/
@[simp]
theorem explicitFiniteQuotientSystem2_obj (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientSystem2 G M).obj (Opposite.op U) =
      AddCommGrpCat.of (H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  by rfl

/-- Under the object identifications above, every arrow of the explicit degree-two finite-quotient
system is the direct transition built from `explicitMap2`. -/
@[simp]
theorem explicitFiniteQuotientSystem2_map
    {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    eqToHom (explicitFiniteQuotientSystem2_obj G M U.unop).symm ≫
        (explicitFiniteQuotientSystem2 G M).map f ≫
      eqToHom (explicitFiniteQuotientSystem2_obj G M V.unop) = AddCommGrpCat.ofHom
      (explicitFiniteQuotientTransition2 G M U.unop V.unop (leOfHom f.unop)) :=
  by rfl

end System

end TauCeti.ContCohomology
