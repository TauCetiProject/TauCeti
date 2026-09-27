/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison

/-!
# The canonical continuous-cohomology system over finite quotients

Let `G` be a topological group acting on a discrete module `M`. For every open normal
subgroup `U`, the fixed points `M^U` are a discrete module over `G ⧸ U`, and hence have canonical
continuous cohomology in every degree. If `V ≤ U`, compatible-pair functoriality along
`G ⧸ V → G ⧸ U` and `M^U → M^V` gives a transition map

```text
Hⁿ(G ⧸ U, M^U) ⟶ Hⁿ(G ⧸ V, M^V).
```

This file assembles those maps into a functor on `(OpenNormalSubgroup G)ᵒᵖ` and constructs the
canonical cocone whose legs are inflation followed by inclusion of fixed points. The assertion that
this cocone is colimiting requires the profinite hypotheses and the all-degree descent argument; it
is deliberately separate from the construction here, which needs neither compactness nor total
disconnectedness.

The construction is the canonical, all-degree counterpart of the explicit systems in degrees zero,
one and two in `FiniteQuotient.Explicit`. It follows the finite-quotient system of Neukirch–Schmidt–
Wingberg, *Cohomology of Number Fields*, (1.2.5), and Ribes–Zalesskii, *Profinite Groups*,
Corollary 6.5.6(a).

## Main definitions

* `TauCeti.ContCohomology.continuousFiniteQuotientTransition`: the canonical transition map in
  every degree.
* `TauCeti.ContCohomology.continuousFiniteQuotientSystem`: the resulting finite-quotient system.
* `TauCeti.ContCohomology.continuousFiniteQuotientComparison`: the inflation-and-inclusion legs.
* `TauCeti.ContCohomology.continuousFiniteQuotientCocone`: those legs as a cocone with apex
  `Hⁿ(G, M)`.
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

/-- Compatible-pair morphisms with equal group maps and equal underlying coefficient maps are
heterogeneously equal. -/
private theorem ofDiscreteModulePair_heq_of_eq
    {H K : Type u} [Group H] [Monoid K]
    {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction H A]
    {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction K B]
    {φ ψ : K →* H} (hφ : φ = ψ) (f : A →ₗ[ℤ] B)
    (hf : ∀ (k : K) (a : A), f (φ k • a) = k • f a)
    (g : TopRep.res ψ (ofDiscreteModule ℤ H A) ⟶ ofDiscreteModule ℤ K B)
    (hg : ∀ a : A, (dsimp% only (g.hom a)) = f a) :
    ofDiscreteModulePair (G := H) (H := K) φ f hf ≍ g := by
  subst hφ
  exact heq_of_eq (ofDiscreteModulePair_eq_of_hom_apply (G := H) (H := K) φ f _ g fun a ↦ hg a)

/-- The coefficient morphism in the canonical finite-quotient transition from the `U`-level to
the `V`-level, for `V ≤ U`. Its underlying map is the inclusion `M^U → M^V`. -/
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
    change fixedPointsInclusion hVU (continuousFiniteQuotientMap G hVU q • m) =
      q • fixedPointsInclusion hVU m
    exact fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU q m)

/-- The coefficient pair acts as the inclusion `M^U → M^V` on underlying elements. -/
@[simp]
theorem continuousFiniteQuotientPair_hom_apply (hVU : V ≤ U)
    (m : FixedPoints.addSubgroup U.toSubgroup M) :
    (dsimp% only ((continuousFiniteQuotientPair G M hVU).hom m)) =
      fixedPointsInclusion hVU m :=
  by
    rw [continuousFiniteQuotientPair]
    exact ofDiscreteModulePair_hom_apply _ _ _ m

/-- At a repeated level the coefficient pair is heterogeneously equal to the identity pair. -/
private theorem continuousFiniteQuotientPair_refl (U : OpenNormalSubgroup G) :
    continuousFiniteQuotientPair G M (le_refl U) ≍
      𝟙 (ofDiscreteModule ℤ (G ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M)) := by
  apply ofDiscreteModulePair_heq_of_eq
    (congrArg ContinuousMonoidHom.toMonoidHom (continuousFiniteQuotientMap_refl G U))
  intro m
  change m = fixedPointsInclusion (le_refl U) m
  apply Subtype.ext
  exact (coe_fixedPointsInclusion (M := M) (le_refl U.toSubgroup) m).symm

/-- Coefficient pairs compose as the corresponding inclusions of fixed points. -/
private theorem continuousFiniteQuotientPair_comp (hWV : W ≤ V) (hVU : V ≤ U) :
    continuousFiniteQuotientPair G M (hWV.trans hVU) ≍
      (TopRep.resFunctor (continuousFiniteQuotientMap G hWV :
        G ⧸ W.toSubgroup →* G ⧸ V.toSubgroup)).map
          (continuousFiniteQuotientPair G M hVU) ≫
        continuousFiniteQuotientPair G M hWV := by
  apply ofDiscreteModulePair_heq_of_eq
    (congrArg ContinuousMonoidHom.toMonoidHom
      (continuousFiniteQuotientMap_comp G hWV hVU).symm)
  intro m
  change (continuousFiniteQuotientPair G M hWV).hom
      ((continuousFiniteQuotientPair G M hVU).hom m) =
    fixedPointsInclusion (hWV.trans hVU) m
  rw [continuousFiniteQuotientPair_hom_apply (G := G) (M := M) hVU m,
    continuousFiniteQuotientPair_hom_apply (G := G) (M := M) hWV
      (fixedPointsInclusion hVU m)]
  apply Subtype.ext
  exact (coe_fixedPointsInclusion hWV (fixedPointsInclusion hVU m)).trans <|
    (coe_fixedPointsInclusion hVU m).trans <|
      (coe_fixedPointsInclusion (hWV.trans hVU) m).symm

/-- The canonical continuous-cohomology transition
`Hⁿ(G ⧸ U, M^U) ⟶ Hⁿ(G ⧸ V, M^V)` for `V ≤ U`. -/
noncomputable def continuousFiniteQuotientTransition (hVU : V ≤ U) (n : ℕ) :
    continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)) :=
  _root_.ContinuousCohomology.map (continuousFiniteQuotientMap G hVU)
    (continuousFiniteQuotientPair G M hVU) n

/-- The canonical finite-quotient transition from a level to itself is the identity. -/
@[simp]
theorem continuousFiniteQuotientTransition_refl (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousFiniteQuotientTransition G M (le_refl U) n = 𝟙 _ := by
  rw [continuousFiniteQuotientTransition,
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
  rw [continuousFiniteQuotientTransition, continuousFiniteQuotientTransition,
    continuousFiniteQuotientTransition, ← _root_.ContinuousCohomology.map_comp]
  refine TauCeti.ContinuousCohomology.map_congr
    (continuousFiniteQuotientMap_comp G hWV hVU).symm
      (continuousFiniteQuotientPair_comp G M hWV hVU) n

end Transition

section System

/-- The canonical finite-quotient system in degree `n`. It sends `U` to
`Hⁿ(G ⧸ U, M^U)` and an inclusion `V ≤ U` to compatible-pair pullback from the `U`-level to
the `V`-level. -/
@[expose] noncomputable def continuousFiniteQuotientSystem (n : ℕ) :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ TopModuleCat.{u} ℤ where
  obj U := continuousCohomology n
    (ofDiscreteModule ℤ (G ⧸ U.unop.toSubgroup)
      (FixedPoints.addSubgroup U.unop.toSubgroup M))
  map := fun f ↦ continuousFiniteQuotientTransition G M (leOfHom f.unop) n
  map_id U := continuousFiniteQuotientTransition_refl G M U.unop n
  map_comp f g := continuousFiniteQuotientTransition_comp G M
    (leOfHom g.unop) (leOfHom f.unop) n

/-- The object at `U` of the canonical finite-quotient system is `Hⁿ(G ⧸ U, M^U)`. -/
@[simp]
theorem continuousFiniteQuotientSystem_obj (n : ℕ) (U : OpenNormalSubgroup G) :
    (continuousFiniteQuotientSystem G M n).obj (Opposite.op U) =
      continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :=
  rfl

/-- Every arrow of the canonical finite-quotient system is the compatible-pair transition. -/
@[simp]
theorem continuousFiniteQuotientSystem_map (n : ℕ)
    {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    (continuousFiniteQuotientSystem G M n).map f =
      continuousFiniteQuotientTransition G M (leOfHom f.unop) n :=
  rfl

end System

section Cocone

variable {U V : OpenNormalSubgroup G}

/-- The coefficient pair for comparison with `Hⁿ(G, M)`: quotient projection together with the
inclusion `M^U → M`. -/
def continuousFiniteQuotientInflationPair (U : OpenNormalSubgroup G) :
    TopRep.res (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      ofDiscreteModule ℤ G M :=
  ofDiscreteModulePair (ContinuousMonoidHom.quotientMk U.toSubgroup :
      G →* G ⧸ U.toSubgroup)
    (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
    (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m)

omit [IsTopologicalGroup G] in
/-- The comparison coefficient pair is the inclusion of fixed points on underlying elements. -/
@[simp]
theorem continuousFiniteQuotientInflationPair_hom_apply (U : OpenNormalSubgroup G)
    (m : FixedPoints.addSubgroup U.toSubgroup M) :
    (dsimp% only ((continuousFiniteQuotientInflationPair G M U).hom m)) = (m : M) := by
  rw [continuousFiniteQuotientInflationPair]
  exact ofDiscreteModulePair_hom_apply _ _ _ m

/-- The comparison map from the `U`-level into `Hⁿ(G, M)`: canonical compatible-pair
functoriality along `G → G ⧸ U` and the inclusion `M^U → M`. -/
noncomputable def continuousFiniteQuotientComparisonApp (U : OpenNormalSubgroup G) (n : ℕ) :
    continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      continuousCohomology n (ofDiscreteModule ℤ G M) :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.quotientMk U.toSubgroup)
    (continuousFiniteQuotientInflationPair G M U) n

/-- Passing from the `U`-level through a deeper `V`-level and then comparing with `Hⁿ(G, M)`
is the direct comparison from the `U`-level. -/
@[reassoc]
theorem continuousFiniteQuotientTransition_comp_comparisonApp (hVU : V ≤ U) (n : ℕ) :
    continuousFiniteQuotientTransition G M hVU n ≫
        continuousFiniteQuotientComparisonApp G M V n =
      continuousFiniteQuotientComparisonApp G M U n := by
  rw [continuousFiniteQuotientTransition, continuousFiniteQuotientComparisonApp,
    continuousFiniteQuotientComparisonApp, ← _root_.ContinuousCohomology.map_comp]
  refine TauCeti.ContinuousCohomology.map_congr ?_ ?_ n
  · ext g
    simp
  · refine (ofDiscreteModulePair_heq_of_eq
      (show (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup) =
          (continuousFiniteQuotientMap G hVU : G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup).comp
            (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup) by
          ext g
          simp)
      (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
      (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m)
      ((TopRep.resFunctor (ContinuousMonoidHom.quotientMk V.toSubgroup :
          G →* G ⧸ V.toSubgroup)).map (continuousFiniteQuotientPair G M hVU) ≫
        continuousFiniteQuotientInflationPair G M V) ?_).symm
    intro m
    change (continuousFiniteQuotientInflationPair G M V).hom
        ((continuousFiniteQuotientPair G M hVU).hom m) = (m : M)
    rw [continuousFiniteQuotientPair_hom_apply (G := G) (M := M) hVU m,
      continuousFiniteQuotientInflationPair_hom_apply (G := G) (M := M) V
        (fixedPointsInclusion hVU m)]
    exact coe_fixedPointsInclusion hVU m

/-- The inflation-and-inclusion comparison maps from every finite level into `Hⁿ(G, M)`,
assembled as a natural transformation to the constant functor. -/
@[expose] noncomputable def continuousFiniteQuotientComparison (n : ℕ) :
    continuousFiniteQuotientSystem G M n ⟶
      (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).obj
        (continuousCohomology n (ofDiscreteModule ℤ G M)) where
  app U := continuousFiniteQuotientComparisonApp G M U.unop n
  naturality _ _ f := continuousFiniteQuotientTransition_comp_comparisonApp G M
    (leOfHom f.unop) n

/-- The comparison natural transformation at `U` is canonical inflation and inclusion from the
`U`-level. -/
@[simp]
theorem continuousFiniteQuotientComparison_app (n : ℕ) (U : OpenNormalSubgroup G) :
    (continuousFiniteQuotientComparison G M n).app (Opposite.op U) =
      continuousFiniteQuotientComparisonApp G M U n :=
  rfl

/-- The canonical finite-quotient cocone in degree `n`, with point `Hⁿ(G, M)` and legs the
inflation-and-inclusion comparisons. -/
@[expose] noncomputable def continuousFiniteQuotientCocone (n : ℕ) :
    Limits.Cocone (continuousFiniteQuotientSystem G M n) where
  pt := continuousCohomology n (ofDiscreteModule ℤ G M)
  ι := continuousFiniteQuotientComparison G M n

/-- The point of the canonical finite-quotient cocone is `Hⁿ(G, M)`. -/
@[simp]
theorem continuousFiniteQuotientCocone_pt (n : ℕ) :
    (continuousFiniteQuotientCocone G M n).pt =
      continuousCohomology n (ofDiscreteModule ℤ G M) :=
  rfl

/-- The legs of the canonical finite-quotient cocone are the comparison maps. -/
@[simp]
theorem continuousFiniteQuotientCocone_ι (n : ℕ) :
    (continuousFiniteQuotientCocone G M n).ι = continuousFiniteQuotientComparison G M n :=
  rfl

end Cocone

end TauCeti.ContCohomology
