/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison

/-!
# The canonical continuous-cohomology system over the open normal subgroups

Let `G` be a topological group acting on a discrete module `M`. For every open normal
subgroup `U`, the fixed points `M^U` are a discrete module over `G ⧸ U`, and hence have canonical
continuous cohomology in every degree. If `V ≤ U`, compatible-pair functoriality along
`G ⧸ V → G ⧸ U` and `M^U → M^V` gives a transition map

```text
Hⁿ(G ⧸ U, M^U) ⟶ Hⁿ(G ⧸ V, M^V).
```

This file assembles those maps into a functor on `(OpenNormalSubgroup G)ᵒᵖ` and constructs the
canonical cocone whose legs are inflation followed by inclusion of fixed points. The assertion that
this cocone is colimiting, `TauCeti.ContCohomology.continuousFiniteQuotientColimit` in
`FiniteQuotient.AllDegreeColimit`, needs compactness of `G`, continuity of the action and the
all-degree descent argument; it is deliberately separate from the construction here, which needs
neither.

Nothing below assumes that the quotients `G ⧸ U` are finite, and none of them need be: for an open
normal subgroup `U` the quotient `G ⧸ U` is discrete, so it is finite when `G` is compact, but
without compactness it may be finite or infinite.
The declarations nevertheless carry `finiteQuotient` in their names, after the tower of quotients
they are indexed by and in step with the explicit low-degree systems of `FiniteQuotient.Explicit`,
which are built under these same hypotheses.

The construction is the canonical, all-degree counterpart of the explicit systems in degrees zero,
one and two in `FiniteQuotient.Explicit`. It follows the finite-quotient system of Neukirch–Schmidt–
Wingberg, *Cohomology of Number Fields*, (1.2.5), and Ribes–Zalesskii, *Profinite Groups*,
Corollary 6.5.6(a).

## Main definitions

* `TauCeti.ContCohomology.continuousFiniteQuotientTransition`: the canonical transition map in
  every degree.
* `TauCeti.ContCohomology.continuousFiniteQuotientSystem`: the resulting system on
  `(OpenNormalSubgroup G)ᵒᵖ`.
* `TauCeti.ContCohomology.continuousFiniteQuotientComparison`: the inflation-and-inclusion legs.
* `TauCeti.ContCohomology.continuousFiniteQuotientCocone`: those legs as a cocone with apex
  `Hⁿ(G, M)`.

## Main statements

* `TauCeti.ContCohomology.continuousFiniteQuotientTransition_eq_map` and
  `TauCeti.ContCohomology.continuousFiniteQuotientComparisonApp_eq_map`: the characteristic
  equations of the two maps, identifying each with the compatible-pair pullback
  `ContinuousCohomology.map` it is built from, so that no consumer unfolds either body.
* `TauCeti.ContCohomology.continuousFiniteQuotientTransition_refl` and
  `continuousFiniteQuotientTransition_comp`: the two functor laws.
* `TauCeti.ContCohomology.continuousFiniteQuotientTransition_comp_comparisonApp`: comparison
  through a deeper quotient agrees with direct comparison, which is the cocone condition.

## Implementation notes

The comparison legs are *defined* as the existing all-degree inflation map
`TauCeti.ContinuousCohomology.infl` after the coefficient dictionary
`TauCeti.ofDiscreteModuleQuotient`, rather than rebuilt from a compatible pair;
`TauCeti.ContCohomology.coeffMap_ofDiscreteModuleQuotient_comp_infl` supplies the compatible-pair
presentation, which is what `continuousFiniteQuotientComparisonApp_eq_map` records.

Every definition keeps its body sealed and is characterized by lemmas. As for
`explicitFiniteQuotientSystem0_map` in `FiniteQuotient.Explicit`, the characteristic lemmas of the
system's arrows, the comparison legs and the cocone legs are stated across the `eqToHom`
transports given by the object and point equations, since with the bodies sealed a morphism out
of `F.obj U` (or into `c.pt`) does not have the type of the map it is built from.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M]

section Transition

variable {U V W : OpenNormalSubgroup G}

/-- The coefficient morphism in the canonical transition from the `U`-level to the `V`-level, for
`V ≤ U`. Its underlying map is the inclusion `M^U → M^V`. -/
def continuousFiniteQuotientPair (hVU : V ≤ U) :
    TopRep.res (continuousFiniteQuotientMap G hVU : G ⧸ V.toSubgroup →*
        G ⧸ U.toSubgroup)
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      ofDiscreteModule ℤ (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  let f : FixedPoints.addSubgroup U.toSubgroup M →ₗ[ℤ]
      FixedPoints.addSubgroup V.toSubgroup M :=
    (fixedPointsInclusion (M := M) hVU :
      FixedPoints.addSubgroup U.toSubgroup M →+
        FixedPoints.addSubgroup V.toSubgroup M).toIntLinearMap
  ofDiscreteModulePair (continuousFiniteQuotientMap G hVU : G ⧸ V.toSubgroup →*
      G ⧸ U.toSubgroup) f (by
    intro q m
    -- `change` rather than a rewrite: the goal is `f (↑φ q • m) = q • f m`, which differs from the
    -- reusable equivariance lemma only by the `ℤ`-linear wrapper `f` adds around
    -- `fixedPointsInclusion` — stated on `FixedPoints.addSubmonoid` — and by the `MonoidHom`
    -- coercion on `φ`. Both conversions are definitional and neither has a propositional form.
    change fixedPointsInclusion hVU (continuousFiniteQuotientMap G hVU q • m) =
      q • fixedPointsInclusion hVU m
    exact fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU q m)

/-- The coefficient pair acts as the inclusion `M^U → M^V` on underlying elements. -/
@[simp]
theorem continuousFiniteQuotientPair_hom_apply (hVU : V ≤ U)
    (m : FixedPoints.addSubgroup U.toSubgroup M) :
    (dsimp% only ((continuousFiniteQuotientPair G M hVU).hom m)) =
      fixedPointsInclusion hVU m := by
  rw [continuousFiniteQuotientPair]
  exact ofDiscreteModulePair_hom_apply _ _ _ m

/-- At a repeated level the coefficient pair is heterogeneously equal to the identity pair. -/
private theorem continuousFiniteQuotientPair_refl (U : OpenNormalSubgroup G) :
    continuousFiniteQuotientPair G M (le_refl U) ≍
      𝟙 (ofDiscreteModule ℤ (G ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M)) := by
  apply ofDiscreteModulePair_heq_of_hom_apply
    (congrArg ContinuousMonoidHom.toMonoidHom (continuousFiniteQuotientMap_refl G U))
  intro m
  exact (DFunLike.congr_fun (fixedPointsInclusion_self M U.toSubgroup) m).symm

/-- Coefficient pairs compose as the corresponding inclusions of fixed points. -/
private theorem continuousFiniteQuotientPair_comp (hWV : W ≤ V) (hVU : V ≤ U) :
    continuousFiniteQuotientPair G M (hWV.trans hVU) ≍
      (TopRep.resFunctor (continuousFiniteQuotientMap G hWV :
        G ⧸ W.toSubgroup →* G ⧸ V.toSubgroup)).map
          (continuousFiniteQuotientPair G M hVU) ≫
        continuousFiniteQuotientPair G M hWV := by
  apply ofDiscreteModulePair_heq_of_hom_apply
    (congrArg ContinuousMonoidHom.toMonoidHom
      (continuousFiniteQuotientMap_comp G hWV hVU).symm)
  intro m
  -- `change` rather than a rewrite: composition and restriction in `TopRep` leave the underlying
  -- map a composite by definition, and the evaluation lemma below is stated on the nested
  -- application. No propositional rewrite reaches the step: the evaluation lemmas of a compatible
  -- pair are `dsimp% only`-normalized (#8315), so neither `simp` nor `rw` fires on the composite.
  change (continuousFiniteQuotientPair G M hWV).hom
      ((continuousFiniteQuotientPair G M hVU).hom m) =
    fixedPointsInclusion (hWV.trans hVU) m
  rw [continuousFiniteQuotientPair_hom_apply (G := G) (M := M) hVU m,
    continuousFiniteQuotientPair_hom_apply (G := G) (M := M) hWV
      (fixedPointsInclusion hVU m)]
  exact DFunLike.congr_fun (fixedPointsInclusion_comp_fixedPointsInclusion hVU hWV) m

/-- The canonical continuous-cohomology transition
`Hⁿ(G ⧸ U, M^U) ⟶ Hⁿ(G ⧸ V, M^V)` for `V ≤ U`. -/
noncomputable def continuousFiniteQuotientTransition (hVU : V ≤ U) (n : ℕ) :
    continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)) :=
  _root_.ContinuousCohomology.map (continuousFiniteQuotientMap G hVU)
    (continuousFiniteQuotientPair G M hVU) n

/-- **The characteristic equation of the canonical transition**: it is the compatible-pair pullback
along the quotient homomorphism `G ⧸ V → G ⧸ U` and the inclusion `M^U → M^V`. -/
theorem continuousFiniteQuotientTransition_eq_map (hVU : V ≤ U) (n : ℕ) :
    continuousFiniteQuotientTransition G M hVU n =
      _root_.ContinuousCohomology.map (continuousFiniteQuotientMap G hVU)
        (continuousFiniteQuotientPair G M hVU) n :=
  (rfl)

/-- The canonical transition from a level to itself is the identity. -/
@[simp]
theorem continuousFiniteQuotientTransition_refl (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousFiniteQuotientTransition G M (le_refl U) n = 𝟙 _ := by
  rw [continuousFiniteQuotientTransition_eq_map,
    ← _root_.ContinuousCohomology.map_id
      (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) n]
  refine TauCeti.ContinuousCohomology.map_congr
    (continuousFiniteQuotientMap_refl G U) (continuousFiniteQuotientPair_refl G M U) n

/-- For `W ≤ V ≤ U`, the canonical transition from the `U`-level to the `W`-level is the
composite through the `V`-level. -/
@[reassoc]
theorem continuousFiniteQuotientTransition_comp (hWV : W ≤ V) (hVU : V ≤ U) (n : ℕ) :
    continuousFiniteQuotientTransition G M (hWV.trans hVU) n =
      continuousFiniteQuotientTransition G M hVU n ≫
        continuousFiniteQuotientTransition G M hWV n := by
  rw [continuousFiniteQuotientTransition_eq_map, continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientTransition_eq_map, ← _root_.ContinuousCohomology.map_comp]
  refine TauCeti.ContinuousCohomology.map_congr
    (continuousFiniteQuotientMap_comp G hWV hVU).symm
      (continuousFiniteQuotientPair_comp G M hWV hVU) n

end Transition

section System

/-- The canonical system over the open normal subgroups of `G` in degree `n`. It sends `U` to
`Hⁿ(G ⧸ U, M^U)` and an inclusion `V ≤ U` to compatible-pair pullback from the `U`-level to
the `V`-level. -/
noncomputable def continuousFiniteQuotientSystem (n : ℕ) :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ TopModuleCat.{u} ℤ where
  obj U := continuousCohomology n
    (ofDiscreteModule ℤ (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M))
  map := fun f ↦ continuousFiniteQuotientTransition G M (leOfHom f.unop) n
  map_id U := continuousFiniteQuotientTransition_refl G M U.unop n
  map_comp f g := continuousFiniteQuotientTransition_comp G M
    (leOfHom g.unop) (leOfHom f.unop) n

/-- The object at `U` of the canonical system is `Hⁿ(G ⧸ U, M^U)`. -/
@[simp]
theorem continuousFiniteQuotientSystem_obj (n : ℕ) (U : OpenNormalSubgroup G) :
    (continuousFiniteQuotientSystem G M n).obj (Opposite.op U) =
      continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  (rfl)

/-- Under the object identifications above, every arrow of the canonical system is the
compatible-pair transition. -/
@[simp]
theorem continuousFiniteQuotientSystem_map (n : ℕ)
    {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    eqToHom (continuousFiniteQuotientSystem_obj G M n U.unop).symm ≫
        (continuousFiniteQuotientSystem G M n).map f ≫
      eqToHom (continuousFiniteQuotientSystem_obj G M n V.unop) =
      continuousFiniteQuotientTransition G M (leOfHom f.unop) n :=
  (rfl)

end System

section Cocone

variable {U V : OpenNormalSubgroup G}

/-- The comparison map from the `U`-level into `Hⁿ(G, M)`: the coefficient dictionary
`TauCeti.ofDiscreteModuleQuotient`, which reads `M^U` as the canonical `U`-invariants of `M`,
followed by canonical inflation along `G → G ⧸ U`. -/
noncomputable def continuousFiniteQuotientComparisonApp (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      continuousCohomology n (ofDiscreteModule ℤ G M) :=
  TauCeti.ContinuousCohomology.coeffMap (ofDiscreteModuleQuotient G M U.toSubgroup) n ≫
    TauCeti.ContinuousCohomology.infl U.toSubgroup (ofDiscreteModule ℤ G M) n

/-- **The characteristic equation of the comparison map**: in every degree it is the
compatible-pair pullback along the quotient homomorphism `G → G ⧸ U` and the inclusion
`M^U → M`. -/
theorem continuousFiniteQuotientComparisonApp_eq_map (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousFiniteQuotientComparisonApp G M U n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.quotientMk U.toSubgroup)
        (ofDiscreteModulePair
          (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
          (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
          (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m)) n :=
  coeffMap_ofDiscreteModuleQuotient_comp_infl G M U.toSubgroup n

/-- Passing from the `U`-level through a deeper `V`-level and then comparing with `Hⁿ(G, M)`
is the direct comparison from the `U`-level. -/
@[reassoc]
theorem continuousFiniteQuotientTransition_comp_comparisonApp (hVU : V ≤ U) (n : ℕ) :
    continuousFiniteQuotientTransition G M hVU n ≫
        continuousFiniteQuotientComparisonApp G M V n =
      continuousFiniteQuotientComparisonApp G M U n := by
  rw [continuousFiniteQuotientTransition_eq_map,
    continuousFiniteQuotientComparisonApp_eq_map, continuousFiniteQuotientComparisonApp_eq_map,
    ← _root_.ContinuousCohomology.map_comp]
  refine TauCeti.ContinuousCohomology.map_congr
    (continuousFiniteQuotientMap_comp_quotientMk G hVU) ?_ n
  refine (ofDiscreteModulePair_heq_of_hom_apply
    (congrArg ContinuousMonoidHom.toMonoidHom
      (continuousFiniteQuotientMap_comp_quotientMk G hVU)).symm _ _ _ ?_).symm
  intro m
  -- `change`: the same definitional composition as in `continuousFiniteQuotientPair_comp`.
  change (ofDiscreteModulePair
      (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
      (FixedPoints.addSubgroup V.toSubgroup M).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G M V.toSubgroup g m)).hom
      ((continuousFiniteQuotientPair G M hVU).hom m) = (m : M)
  rw [continuousFiniteQuotientPair_hom_apply (G := G) (M := M) hVU m,
    ofDiscreteModulePair_hom_apply
      (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
      (FixedPoints.addSubgroup V.toSubgroup M).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G M V.toSubgroup g m) (fixedPointsInclusion hVU m)]
  exact coe_fixedPointsInclusion hVU m

/-- The inflation-and-inclusion comparison maps from every level into `Hⁿ(G, M)`, assembled as a
natural transformation to the constant functor. -/
noncomputable def continuousFiniteQuotientComparison (n : ℕ) :
    continuousFiniteQuotientSystem G M n ⟶
      (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).obj
        (continuousCohomology n (ofDiscreteModule ℤ G M)) where
  app U := continuousFiniteQuotientComparisonApp G M U.unop n
  naturality _ _ f := continuousFiniteQuotientTransition_comp_comparisonApp G M
    (leOfHom f.unop) n

/-- Under the object identification at `U`, the comparison natural transformation at `U` is
canonical inflation and inclusion from the `U`-level. -/
@[simp]
theorem continuousFiniteQuotientComparison_app (n : ℕ) (U : OpenNormalSubgroup G) :
    eqToHom (continuousFiniteQuotientSystem_obj G M n U).symm ≫
        (continuousFiniteQuotientComparison G M n).app (Opposite.op U) =
      continuousFiniteQuotientComparisonApp G M U n :=
  (rfl)

/-- The canonical cocone over the open-normal-subgroup system in degree `n`, with point `Hⁿ(G, M)`
and legs the inflation-and-inclusion comparisons. -/
noncomputable def continuousFiniteQuotientCocone (n : ℕ) :
    Limits.Cocone (continuousFiniteQuotientSystem G M n) where
  pt := continuousCohomology n (ofDiscreteModule ℤ G M)
  ι := continuousFiniteQuotientComparison G M n

/-- The point of the canonical cocone is `Hⁿ(G, M)`. -/
@[simp]
theorem continuousFiniteQuotientCocone_pt (n : ℕ) :
    (continuousFiniteQuotientCocone G M n).pt =
      continuousCohomology n (ofDiscreteModule ℤ G M) :=
  (rfl)

/-- Under the object and point identifications, the leg of the canonical cocone at `U` is canonical
inflation and inclusion from the `U`-level. -/
@[simp]
theorem continuousFiniteQuotientCocone_ι_app (n : ℕ) (U : OpenNormalSubgroup G) :
    eqToHom (continuousFiniteQuotientSystem_obj G M n U).symm ≫
        (continuousFiniteQuotientCocone G M n).ι.app (Opposite.op U) ≫
      eqToHom (continuousFiniteQuotientCocone_pt G M n) =
      continuousFiniteQuotientComparisonApp G M U n :=
  (rfl)

end Cocone

end TauCeti.ContCohomology
