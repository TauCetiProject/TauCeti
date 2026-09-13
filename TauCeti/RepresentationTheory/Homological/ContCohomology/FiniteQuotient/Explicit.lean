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

For a topological group `G` acting continuously on a discrete additive group `M`, the explicit
cohomology groups in degrees one and two

```text
Hⁱ(G ⧸ U, M^U),  i = 1, 2,
```

form a directed system as the open normal subgroup `U` shrinks.  If `V ≤ U`, its transition
map is the compatible-pair pullback along the quotient homomorphism `G ⧸ V → G ⧸ U` and the
coefficient inclusion `M^U → M^V`.
When `G` is compact these discrete quotient groups are finite; the construction itself does not
require compactness.

`TauCeti.finiteQuotientSystem` already packages the corresponding system in Mathlib's discrete
`groupCohomology`.  The systems here are instead constructed directly with
`TauCeti.ContCohomology.explicitMap1` and `explicitMap2`.  In particular they are
universe-polymorphic and do not transport their arrows through the universe-restricted comparison
with discrete group cohomology.  They are the source diagrams for the explicit finite-quotient
colimit theorems in degrees one and two.

## Main definitions

* `TauCeti.ContCohomology.explicitFiniteQuotientTransition1`: the transition
  `H¹(G ⧸ U, M^U) → H¹(G ⧸ V, M^V)` for `V ≤ U`.
* `TauCeti.ContCohomology.explicitFiniteQuotientSystem1`: the resulting functor on
  `(OpenNormalSubgroup G)ᵒᵖ`.
* `TauCeti.ContCohomology.explicitFiniteQuotientTransition2` and
  `explicitFiniteQuotientSystem2`: the corresponding transition and functor in degree two.

## Main statements

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
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

section Transition

variable {U V W : OpenNormalSubgroup G}

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

omit [ContinuousSMul G M] in
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

omit [ContinuousSMul G M] in
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

omit [ContinuousSMul G M] in
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
        (explicitFiniteQuotientTransition1 G M U V hVU) := by
  rw [explicitFiniteQuotientTransition1, explicitFiniteQuotientTransition1,
    explicitFiniteQuotientTransition1]
  have hcomp : ∀ (q : G ⧸ W.toSubgroup)
      (m : FixedPoints.addSubgroup U.toSubgroup M),
      (fixedPointsInclusion hWV :
          FixedPoints.addSubgroup V.toSubgroup M →+
            FixedPoints.addSubgroup W.toSubgroup M)
          ((fixedPointsInclusion hVU :
            FixedPoints.addSubgroup U.toSubgroup M →+
              FixedPoints.addSubgroup V.toSubgroup M)
            (continuousFiniteQuotientMap G hVU
              (continuousFiniteQuotientMap G hWV q) • m)) =
        q • (fixedPointsInclusion hWV :
          FixedPoints.addSubgroup V.toSubgroup M →+
            FixedPoints.addSubgroup W.toSubgroup M)
          ((fixedPointsInclusion hVU :
            FixedPoints.addSubgroup U.toSubgroup M →+
              FixedPoints.addSubgroup V.toSubgroup M) m) := by
    intro q m
    rw [fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU]
    exact fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hWV q
      ((fixedPointsInclusion hVU :
        FixedPoints.addSubgroup U.toSubgroup M →+
          FixedPoints.addSubgroup V.toSubgroup M) m)
  calc
    _ = @explicitMap1
        (G ⧸ U.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup U.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M U.toSubgroup)
        (G ⧸ W.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup W.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M W.toSubgroup)
        ((continuousFiniteQuotientMap G hVU).comp (continuousFiniteQuotientMap G hWV))
        ((fixedPointsInclusion hWV :
          FixedPoints.addSubgroup V.toSubgroup M →+
            FixedPoints.addSubgroup W.toSubgroup M).comp
          (fixedPointsInclusion hVU :
            FixedPoints.addSubgroup U.toSubgroup M →+
              FixedPoints.addSubgroup V.toSubgroup M))
        (continuous_of_discreteTopology.comp continuous_of_discreteTopology)
        (fun q m ↦ hcomp q m) := by
      apply explicitMap1_congr_of_eq
      · exact (continuousFiniteQuotientMap_comp G hWV hVU).symm
      · exact (fixedPointsInclusion_comp_fixedPointsInclusion hVU hWV).symm
    _ = _ := by
      convert @explicitMap1_comp
        (G ⧸ U.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup U.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M U.toSubgroup)
        (G ⧸ V.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup V.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M V.toSubgroup)
        (continuousFiniteQuotientMap G hVU)
        (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
          FixedPoints.addSubgroup V.toSubgroup M)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)
        (G ⧸ W.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup W.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M W.toSubgroup)
        (continuousFiniteQuotientMap G hWV)
        (fixedPointsInclusion hWV : FixedPoints.addSubgroup V.toSubgroup M →+
          FixedPoints.addSubgroup W.toSubgroup M)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hWV)
        (fun q m ↦ hcomp q m) using 1
      apply explicitMap1_congr_of_eq <;> rfl

end Transition

section System

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

omit [ContinuousSMul G M] in
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

omit [ContinuousSMul G M] in
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

omit [ContinuousSMul G M] in
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
        (explicitFiniteQuotientTransition2 G M U V hVU) := by
  rw [explicitFiniteQuotientTransition2, explicitFiniteQuotientTransition2,
    explicitFiniteQuotientTransition2]
  have hcomp : ∀ (q : G ⧸ W.toSubgroup)
      (m : FixedPoints.addSubgroup U.toSubgroup M),
      (fixedPointsInclusion hWV :
          FixedPoints.addSubgroup V.toSubgroup M →+
            FixedPoints.addSubgroup W.toSubgroup M)
          ((fixedPointsInclusion hVU :
            FixedPoints.addSubgroup U.toSubgroup M →+
              FixedPoints.addSubgroup V.toSubgroup M)
            (continuousFiniteQuotientMap G hVU
              (continuousFiniteQuotientMap G hWV q) • m)) =
        q • (fixedPointsInclusion hWV :
          FixedPoints.addSubgroup V.toSubgroup M →+
            FixedPoints.addSubgroup W.toSubgroup M)
          ((fixedPointsInclusion hVU :
            FixedPoints.addSubgroup U.toSubgroup M →+
              FixedPoints.addSubgroup V.toSubgroup M) m) := by
    intro q m
    rw [fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU]
    exact fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hWV q
      ((fixedPointsInclusion hVU :
        FixedPoints.addSubgroup U.toSubgroup M →+
          FixedPoints.addSubgroup V.toSubgroup M) m)
  calc
    _ = @explicitMap2
        (G ⧸ U.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup U.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M U.toSubgroup)
        (G ⧸ W.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup W.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M W.toSubgroup)
        inferInstance inferInstance
        ((continuousFiniteQuotientMap G hVU).comp (continuousFiniteQuotientMap G hWV))
        ((fixedPointsInclusion hWV :
          FixedPoints.addSubgroup V.toSubgroup M →+
            FixedPoints.addSubgroup W.toSubgroup M).comp
          (fixedPointsInclusion hVU :
            FixedPoints.addSubgroup U.toSubgroup M →+
              FixedPoints.addSubgroup V.toSubgroup M))
        (continuous_of_discreteTopology.comp continuous_of_discreteTopology)
        (fun q m ↦ hcomp q m) := by
      apply explicitMap2_congr_of_eq
      · exact (continuousFiniteQuotientMap_comp G hWV hVU).symm
      · exact (fixedPointsInclusion_comp_fixedPointsInclusion hVU hWV).symm
    _ = _ := by
      convert @explicitMap2_comp
        (G ⧸ U.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup U.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M U.toSubgroup)
        (G ⧸ V.toSubgroup) inferInstance inferInstance
        (FixedPoints.addSubgroup V.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M V.toSubgroup)
        inferInstance inferInstance
        (continuousFiniteQuotientMap G hVU)
        (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
          FixedPoints.addSubgroup V.toSubgroup M)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)
        (G ⧸ W.toSubgroup) inferInstance inferInstance inferInstance
        (FixedPoints.addSubgroup W.toSubgroup M) inferInstance inferInstance inferInstance
        inferInstance (continuousSMulQuotientFixedPointsOfContinuousSMul G M W.toSubgroup)
        (continuousFiniteQuotientMap G hWV)
        (fixedPointsInclusion hWV : FixedPoints.addSubgroup V.toSubgroup M →+
          FixedPoints.addSubgroup W.toSubgroup M)
        continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hWV) using 1
      apply explicitMap2_congr_of_eq <;> rfl

/-- The explicit degree-two finite-quotient system of a discrete module. It sends an open normal
subgroup `U` to `H²(G ⧸ U, M^U)` and an inclusion `V ≤ U` to the direct explicit transition from
the `U`-level to the `V`-level. -/
noncomputable def explicitFiniteQuotientSystem2 :
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
