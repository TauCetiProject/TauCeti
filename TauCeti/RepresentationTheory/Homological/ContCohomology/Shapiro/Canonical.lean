/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Exact

/-!
# The canonical Shapiro map in every degree

For a compact group `G`, a subgroup `U` and a discrete `U`-module `A`, the coinduced module
`Coind_U^G A` of `TauCeti.DiscreteCoind` comes with the compatible pair consisting of the inclusion
`U ↪ G` and the counit `Coind_U^G A → A`, evaluation at `1`. Mathlib's functoriality of continuous
cohomology in compatible pairs turns it into a cochain map
`TauCeti.ContinuousCohomology.shapiroCochainMap` of homogeneous cochain complexes, and so into a
map in every degree,

```text
Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A),
```

the **canonical Shapiro map** `TauCeti.ContinuousCohomology.shapiroMap`. It is restriction to `U`
followed by the coefficient map of the counit, and Shapiro's lemma is the statement that it is
bijective. This file defines the map on the canonical carrier and proves three things about it:

* in degrees `0`, `1` and `2` it is carried by the comparison isomorphisms of the explicit
  low-degree model to the explicit Shapiro maps `TauCeti.ContCohomology.explicitShapiro0`,
  `explicitShapiroMap1` and `explicitShapiroMap2`, so it is bijective there for a closed subgroup
  of a profinite group;
* it is natural in the coefficient module: for a `U`-equivariant homomorphism `A → B` of discrete
  `U`-modules, the coefficient maps of the homomorphism and of its coinduction to `G` commute with
  the Shapiro maps of `A` and `B`;
* it commutes with the connecting maps of the long exact sequence: for a short exact sequence of
  discrete `U`-modules and its coinduction to `G`, the square of Shapiro maps and connecting maps
  commutes in every degree.

Shapiro's lemma in every degree follows from the low-degree bijectivity and the commuting square
with the connecting maps by induction on the degree, given
the acyclicity of `Coind_1^G A` in every positive degree: for `n ≥ 1` the connecting maps
`Hⁿ(-, Q) → Hⁿ⁺¹(-, A)` of `0 → A → Coind_1^U A → Q → 0` and of its coinduction to `G` are then
bijective (in degree `0` they are only surjective, since `H⁰` of the middle term need not vanish),
transitivity of coinduction identifies `Coind_U^G (Coind_1^U A)` with `Coind_1^G A`, and the
commuting square carries bijectivity of the Shapiro map in degree `n ≥ 1` to bijectivity in degree
`n + 1`. The degrees `0` and `1` proved here directly are the base cases of this induction, which is
carried out in `TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.AllDegrees`.

## Main definitions

* `TauCeti.ContinuousCohomology.shapiroCochainMap`: the cochain map
  `σ ↦ ev₁ ∘ σ ∘ ι` from the homogeneous cochains of `G` with coefficients `Coind_U^G A` to those
  of `U` with coefficients `A`.
* `TauCeti.ContinuousCohomology.shapiroMap`: the canonical Shapiro map
  `Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` in `TopModuleCat ℤ`, the map `shapiroCochainMap` induces on
  homology.

## Main results

* `TauCeti.ContinuousCohomology.shapiroMap_eq_res_comp_coeffMap`: the Shapiro map is restriction
  followed by the coefficient map of the counit.
* `TauCeti.ContinuousCohomology.shapiroMap_naturality`: the Shapiro map is natural in the
  coefficient module.
* `TauCeti.ContinuousCohomology.explicitH0Iso_shapiroMap`,
  `TauCeti.ContinuousCohomology.explicitH1AddEquivContinuousCohomology_shapiroMap`,
  `TauCeti.ContinuousCohomology.explicitH2AddEquivContinuousCohomology_shapiroMap`: agreement with
  the explicit Shapiro maps in degrees `0`, `1` and `2` under the comparison isomorphisms.
* `TauCeti.ContinuousCohomology.bijective_shapiroMap_zero`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap_one`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap_two`: Shapiro's lemma on the canonical carrier
  in degrees `0`, `1` and `2`, for a closed subgroup of a profinite group.
* `TauCeti.ContCohomology.DiscreteShortExact.delta_shapiroMap`: the Shapiro maps commute with
  the connecting maps.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.6.4), with the footnote on p. 61 recording that NSW write `Ind` for the coinduced module.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

section CanonicalMap

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A]

/-- **The Shapiro cochain map**: the map of homogeneous cochain complexes induced by the
compatible pair of the inclusion `ι : U ↪ G` and the counit `ev₁ : Coind_U^G A → A`, evaluation at
`1`, sending a homogeneous cochain `σ` of `G` with coefficients `Coind_U^G A` to the homogeneous
cochain `ev₁ ∘ σ ∘ ι` of `U` with coefficients `A`. Its map on homology is the canonical Shapiro
map (`homologyMap_shapiroCochainMap`). For a closed subgroup of a profinite group it is a
quasi-isomorphism (`TauCeti.ContinuousCohomology.quasiIso_shapiroCochainMap`), but in general
not an isomorphism of complexes: a degree-`0` homogeneous cochain is determined by its value at
`1`, so for the discrete group `G` of order `2`, `U = ⊥` and `A = ZMod 2` the degree-`0` terms
have orders `4` and `2`. -/
noncomputable def shapiroCochainMap :
    TopRep.homogeneousCochains (ofDiscreteModule ℤ G (DiscreteCoind G U A)) ⟶
      TopRep.homogeneousCochains (ofDiscreteModule ℤ U A) :=
  _root_.ContinuousCohomology.cochainsMap (ContinuousMonoidHom.subgroupSubtype U)
    (ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (DiscreteCoind.eval G U A).toIntLinearMap fun u f => eval_subgroupSubtype_smul G U A u f)

/-- The Shapiro cochain map is Mathlib's cochain map of the compatible pair of the inclusion and
the counit. -/
theorem shapiroCochainMap_def :
    shapiroCochainMap U A = _root_.ContinuousCohomology.cochainsMap
      (ContinuousMonoidHom.subgroupSubtype U)
      (ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
        (DiscreteCoind.eval G U A).toIntLinearMap fun u f => eval_subgroupSubtype_smul G U A u f) :=
  (rfl)

/-- **The canonical Shapiro map** `Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` in every degree: the map on
continuous cohomology induced by the compatible pair of the inclusion `U ↪ G` and the counit
`Coind_U^G A → A`, evaluation at `1`, that is, the map `shapiroCochainMap` induces on homology.
It is defined for any topological group `G` and any subgroup `U`; Shapiro's lemma is the
statement that it is bijective, proved here in degree `0` in this generality
(`bijective_shapiroMap_zero`) and in degrees at most `2` for a closed subgroup of a profinite
group (`bijective_shapiroMap_of_le_two`). -/
noncomputable def shapiroMap (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U A)) ⟶
      continuousCohomology n (ofDiscreteModule ℤ U A) :=
  HomologicalComplex.homologyMap (shapiroCochainMap U A) n

/-- The canonical Shapiro map is the map induced on homology by the Shapiro cochain map. -/
@[simp]
theorem homologyMap_shapiroCochainMap (n : ℕ) :
    HomologicalComplex.homologyMap (shapiroCochainMap U A) n = shapiroMap U A n := (rfl)

/-- The canonical Shapiro map is the compatible-pair map of the inclusion and the counit. -/
theorem shapiroMap_def (n : ℕ) :
    shapiroMap U A n = _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U)
      (ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
        (DiscreteCoind.eval G U A).toIntLinearMap fun u f => eval_subgroupSubtype_smul G U A u f)
          n := (rfl)

/-- **The Shapiro map is restriction followed by the counit**: restrict from `G` to `U`, then apply
the coefficient map induced by evaluation at `1`. The two sides compose because the restriction of
the canonical object of a discrete `G`-module to `U` is the canonical object of the same module
over `U` (`TauCeti.res_ofDiscreteModule`). -/
theorem shapiroMap_eq_res_comp_coeffMap (n : ℕ) :
    shapiroMap U A n =
      res U (ofDiscreteModule ℤ G (DiscreteCoind G U A)) n ≫
        coeffMap (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
          fun u f => DiscreteCoind.eval_smul u f) n := by
  rw [res_def, coeffMap_def]
  -- The composite of the two compatible pairs is the pair of the inclusion and the counit: both
  -- act on a coinduced function by evaluation at `1`.
  refine (map_congr rfl (heq_of_eq (ofDiscreteModulePair_eq_of_hom_apply _ _ _ _
    fun f => ?_)) n).trans
    (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ G (DiscreteCoind G U A))
      (ContinuousMonoidHom.subgroupSubtype U) (ContinuousMonoidHom.id U) (𝟙 _)
      (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
        fun u f => DiscreteCoind.eval_smul u f) n)
  -- Not `rfl`: unfolding the composite through `TopRep.resFunctor` exhausts the heartbeat
  -- budget, and `simp` does not rewrite the composite either, its middle object being
  -- `TopRep.res U.subtype (ofDiscreteModule ℤ G _)` on one side and `ofDiscreteModule ℤ U _` on
  -- the other. The two evaluation lemmas need their morphisms spelled out for the same reason.
  exact (TopRep.comp_apply ((TopRep.resFunctor (ContinuousMonoidHom.id U : U →* U)).map
    (𝟙 (TopRep.res (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (ofDiscreteModule ℤ G (DiscreteCoind G U A)))))
    (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
      fun u f => DiscreteCoind.eval_smul u f) f).trans
    (ofDiscreteModuleMap_hom_apply (G := U) (DiscreteCoind.eval G U A).toIntLinearMap
      (fun u f => DiscreteCoind.eval_smul u f) f)

/-- **The Shapiro map is natural in the coefficient module**: for a `U`-equivariant homomorphism
`f : A → B` of discrete `U`-modules, the coefficient map of its coinduction
`Coind_U^G A → Coind_U^G B` followed by the Shapiro map of `B` is the Shapiro map of `A` followed by
the coefficient map of `f`. The coinduced homomorphism is the one
`TauCeti.ContCohomology.DiscreteShortExact.coind` applies to the maps of a short exact sequence. -/
@[reassoc]
theorem shapiroMap_naturality {B : Type u} [AddCommGroup B] [TopologicalSpace B]
    [DiscreteTopology B] [DistribMulAction U B] (f : A →+ B)
    (hf : ∀ (u : U) (a : A), f (u • a) = u • f a) (n : ℕ) :
    coeffMap (ofDiscreteModuleMap
        (DiscreteCoind.map f.toIntLinearMap hf).toAddMonoidHom.toIntLinearMap
        fun g φ => DiscreteCoind.map_smul f.toIntLinearMap hf g φ) n ≫ shapiroMap U B n =
      shapiroMap U A n ≫ coeffMap (ofDiscreteModuleMap f.toIntLinearMap hf) n := by
  rw [shapiroMap_eq_res_comp_coeffMap, shapiroMap_eq_res_comp_coeffMap]
  -- Restriction is natural in the coefficients (`coeffMap_comp_res`), so both sides are restriction
  -- followed by the coefficient map of a composite, and the two composites agree: each acts on a
  -- coinduced function `φ` by `f (φ 1)`. The composites are reassociated by hand, since their
  -- middle objects `TopRep.res U.subtype (ofDiscreteModule ℤ G _)` and `ofDiscreteModule ℤ U _`
  -- agree only up to `res_ofDiscreteModule`, which stops `rw [Category.assoc]` from matching.
  refine (coeffMap_comp_res_assoc U _ n _).trans
    (((congrArg (res U _ n ≫ ·) (coeffMap_comp _ _ n).symm).trans
      (congrArg (res U _ n ≫ coeffMap · n) ?_)).trans
      ((congrArg (res U _ n ≫ ·) (coeffMap_comp _ _ n)).trans (Category.assoc _ _ _).symm))
  refine TopRep.hom_ext (DFunLike.ext _ _ fun φ => ?_)
  -- Not `rfl`: `DiscreteCoind.eval` and `DiscreteCoind.map` are not exposed, so the two sides are
  -- not definitionally equal outside their module, and the evaluation lemmas need their morphisms
  -- spelled out, since `rw`/`simp` cannot match a composite whose middle object is
  -- `TopRep.res U.subtype (ofDiscreteModule ℤ G _)` on one side and `ofDiscreteModule ℤ U _` on
  -- the other.
  exact ((TopRep.comp_apply ((TopRep.resFunctor (U.subtype : U →* G)).map (ofDiscreteModuleMap
        (DiscreteCoind.map f.toIntLinearMap hf).toAddMonoidHom.toIntLinearMap
        fun g φ => DiscreteCoind.map_smul f.toIntLinearMap hf g φ))
      (ofDiscreteModuleMap (DiscreteCoind.eval G U B).toIntLinearMap
        fun u f => DiscreteCoind.eval_smul u f) φ).trans
    ((ofDiscreteModuleMap_hom_apply (G := U) (DiscreteCoind.eval G U B).toIntLinearMap
        (fun u f => DiscreteCoind.eval_smul u f) (DiscreteCoind.map f.toIntLinearMap hf φ)).trans
      ((DiscreteCoind.eval_apply (DiscreteCoind.map f.toIntLinearMap hf φ)).trans
        (DiscreteCoind.map_apply f.toIntLinearMap hf φ 1)))).trans
    ((TopRep.comp_apply (ofDiscreteModuleMap (DiscreteCoind.eval G U A).toIntLinearMap
        fun u f => DiscreteCoind.eval_smul u f)
      (ofDiscreteModuleMap f.toIntLinearMap hf : ofDiscreteModule ℤ U A ⟶ ofDiscreteModule ℤ U B)
        φ).trans
      ((ofDiscreteModuleMap_hom_apply (G := U) f.toIntLinearMap hf _).trans
        (congrArg f (DiscreteCoind.eval_apply φ)))).symm

/-! ### Degree zero -/

/-- In degree zero the canonical Shapiro map is the explicit one, `H⁰(G, Coind_U^G A) ≃+ H⁰(U, A)`
by evaluation at `1`, under the comparisons with the canonical carrier. -/
@[simp]
theorem explicitH0Iso_shapiroMap (x : H0 G (DiscreteCoind G U A)) :
    shapiroMap U A 0 ((explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)).hom x) =
      (explicitH0IsoContinuousCohomology U A).hom (explicitShapiro0 G U A x) := by
  rw [shapiroMap_def, explicitH0Iso_map]
  exact congrArg _ (Subtype.ext (((coe_explicitMap0 _ _ _ _ _ x).trans
    (DiscreteCoind.eval_apply _)).trans (explicitShapiro0_apply x).symm))

/-- **Shapiro's lemma in degree zero on the canonical carrier**: the canonical Shapiro map
`H⁰(G, Coind_U^G A) ⟶ H⁰(U, A)` is bijective. No closedness of `U` is needed in this degree. -/
theorem bijective_shapiroMap_zero : Function.Bijective (shapiroMap U A 0) := by
  -- Precomposing with the source comparison gives the explicit map followed by the target
  -- comparison, a composite of bijections.
  rw [← Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso
    (explicitH0IsoContinuousCohomology G (DiscreteCoind G U A)).hom), Function.comp_def,
    funext (explicitH0Iso_shapiroMap U A)]
  exact (ConcreteCategory.bijective_of_isIso (explicitH0IsoContinuousCohomology U A).hom).comp
    (explicitShapiro0 G U A).bijective

/-! ### Degrees one and two -/

variable [CompactSpace G] [ContinuousSMul U A]

/-- In degree one the canonical Shapiro map is the explicit forward Shapiro map
`TauCeti.ContCohomology.explicitShapiroMap1` under the comparisons with the canonical carrier. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_shapiroMap
    (x : H1 G (DiscreteCoind G U A)) :
    shapiroMap U A 1 (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U A) x) =
      explicitH1AddEquivContinuousCohomology U A (explicitShapiroMap1 G U A x) := by
  rw [shapiroMap_def]
  exact explicitH1AddEquivContinuousCohomology_map G (DiscreteCoind G U A) U A
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    (eval_subgroupSubtype_smul G U A) x

/-- In degree two the canonical Shapiro map is the explicit forward Shapiro map
`TauCeti.ContCohomology.explicitShapiroMap2` under the comparisons with the canonical carrier. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_shapiroMap [LocallyCompactSpace U]
    (x : H2 G (DiscreteCoind G U A)) :
    shapiroMap U A 2 (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U A) x) =
      explicitH2AddEquivContinuousCohomology U A (explicitShapiroMap2 G U A x) := by
  rw [shapiroMap_def, explicitShapiroMap2_def]
  exact explicitH2AddEquivContinuousCohomology_map G (DiscreteCoind G U A) U A
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A)
    (eval_subgroupSubtype_smul G U A) x

variable [TotallyDisconnectedSpace G]

/-- **Shapiro's lemma in degree one on the canonical carrier**: for a closed subgroup `U` of a
profinite group `G`, the canonical Shapiro map `H¹(G, Coind_U^G A) ⟶ H¹(U, A)` is bijective. -/
theorem bijective_shapiroMap_one (hU : IsClosed (U : Set G)) :
    Function.Bijective (shapiroMap U A 1) := by
  rw [← Function.Bijective.of_comp_iff _
    (explicitH1AddEquivContinuousCohomology G (DiscreteCoind G U A)).bijective, Function.comp_def,
    funext (explicitH1AddEquivContinuousCohomology_shapiroMap U A)]
  exact (explicitH1AddEquivContinuousCohomology U A).bijective.comp
    (bijective_explicitShapiroMap1 G U A hU)

/-- **Shapiro's lemma in degree two on the canonical carrier**: for a closed subgroup `U` of a
profinite group `G`, the canonical Shapiro map `H²(G, Coind_U^G A) ⟶ H²(U, A)` is bijective. -/
theorem bijective_shapiroMap_two (hU : IsClosed (U : Set G)) :
    Function.Bijective (shapiroMap U A 2) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  rw [← Function.Bijective.of_comp_iff _
    (explicitH2AddEquivContinuousCohomology G (DiscreteCoind G U A)).bijective, Function.comp_def,
    funext (explicitH2AddEquivContinuousCohomology_shapiroMap U A)]
  exact (explicitH2AddEquivContinuousCohomology U A).bijective.comp
    (bijective_explicitShapiroMap2 G U A hU)

/-- **Shapiro's lemma in degrees at most two on the canonical carrier**, in one statement: for a
closed subgroup `U` of a profinite group `G` and `n ≤ 2`, the canonical Shapiro map
`Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` is bijective. -/
theorem bijective_shapiroMap_of_le_two (hU : IsClosed (U : Set G)) {n : ℕ} (hn : n ≤ 2) :
    Function.Bijective (shapiroMap U A n) := by
  match n, hn with
  | 0, _ => exact bijective_shapiroMap_zero U A
  | 1, _ => exact bijective_shapiroMap_one U A hU
  | 2, _ => exact bijective_shapiroMap_two U A hU

end CanonicalMap

end TauCeti.ContinuousCohomology

/-! ### Compatibility with the connecting maps -/

namespace TauCeti.ContCohomology.DiscreteShortExact

open TauCeti.ContinuousCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {U : Subgroup G}
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction U A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction U B]
  [ContinuousSMul U B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction U C]
  (S : DiscreteShortExact U A B C)

/-- **The Shapiro maps commute with the connecting maps.** For a short exact sequence
`0 → A → B → C → 0` of discrete `U`-modules and its coinduction
`0 → Coind A → Coind B → Coind C → 0` to `G`, the square

```text
Hⁿ(G, Coind_U^G C) ---δ---> Hⁿ⁺¹(G, Coind_U^G A)
       |                            |
   shapiroMap                   shapiroMap
       v                            v
    Hⁿ(U, C) ----------δ--------> Hⁿ⁺¹(U, A)
```

commutes in every degree. This is the naturality of the connecting map in the compatible pair of
the inclusion and the counit; once the middle terms are acyclic in every positive degree, it is
the step that carries bijectivity of the Shapiro map from degree `n ≥ 1` to degree `n + 1` (both
connecting maps are then bijective; in degree `0` they are only surjective, so the degrees `0` and
`1` are separate base cases). The connecting map of `U` needs `U` compact, which follows from its
closedness in the compact group `G`. -/
@[reassoc]
theorem delta_shapiroMap (hU : IsClosed (U : Set G)) (n : ℕ) :
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
    (coind U hU S).delta n ≫ shapiroMap U A (n + 1) = shapiroMap U C n ≫ S.delta n := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  rw [shapiroMap_def, shapiroMap_def]
  exact (coind U hU S).delta_map S (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B) (DiscreteCoind.eval G U C)
    (eval_subgroupSubtype_smul G U A) (eval_subgroupSubtype_smul G U B)
    (eval_subgroupSubtype_smul G U C)
    (fun a => by rw [DiscreteCoind.eval_apply, DiscreteCoind.eval_apply, coind_incl_apply])
    (fun b => by rw [DiscreteCoind.eval_apply, DiscreteCoind.eval_apply, coind_proj_apply])
    n

end TauCeti.ContCohomology.DiscreteShortExact
