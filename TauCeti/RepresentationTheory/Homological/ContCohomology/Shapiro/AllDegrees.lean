/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Canonical
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Transitivity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DimensionShifting.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars

/-!
# Shapiro's lemma in every degree

For a closed subgroup `U` of a profinite group `G` and a discrete `U`-module `A`, the canonical
Shapiro map `TauCeti.ContinuousCohomology.shapiroMap`,

```text
Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A),
```

is an isomorphism in every degree `n`. This is **Shapiro's lemma** for Mathlib's canonical
continuous cohomology; the isomorphism is `TauCeti.ContinuousCohomology.shapiroIso`. On the level
of complexes, it says that the Shapiro cochain map `TauCeti.ContinuousCohomology.shapiroCochainMap`,
of which `shapiroMap` is the map on homology, is a quasi-isomorphism. In general the two complexes
are not isomorphic at all (already their degree-`0` terms differ in size for the discrete group
`G` of order `2`, `U = ⊥` and `A = ZMod 2`); only the maps induced on cohomology are isomorphisms.

The degrees `0` and `1` are the base cases, where the canonical map agrees with the explicit
low-degree Shapiro isomorphisms (`TauCeti.ContinuousCohomology.bijective_shapiroMap_of_le_two`).
The step from degree `n + 1` to degree `n + 2` is dimension shifting. The short exact sequence
`0 → A → Coind_1^U A → Q → 0` of `TauCeti.ContCohomology.coindBotShortExact`, with
`Q = Coind_1^U A ⧸ A`, and its coinduction to `G` fit into the commuting square

```text
Hⁿ⁺¹(G, Coind_U^G Q) ---δ---> Hⁿ⁺²(G, Coind_U^G A)
         |                             |
     shapiroMap                    shapiroMap
         v                             v
     Hⁿ⁺¹(U, Q) ----------δ--------> Hⁿ⁺²(U, A)
```

of `TauCeti.ContCohomology.DiscreteShortExact.delta_shapiroMap`. Both connecting maps are
isomorphisms, because both middle terms are acyclic in positive degrees: `Coind_1^U A` by
`TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int`, and
`Coind_U^G (Coind_1^U A)` because transitivity of coinduction identifies it with `Coind_1^G A`
(`TauCeti.DiscreteCoind.transIsoBot`). The left vertical map is an isomorphism by induction, applied
to the module `Q`, so the right one is too.

Closedness of `U` enters through the base cases, which use the explicit Shapiro isomorphisms for a
closed subgroup, and through the coinduction of a short exact sequence, whose surjectivity on the
right needs a closed subgroup.

The last section transfers the result to a smooth discrete `A : TopRep R U` over an arbitrary ring
`R`. The generic Shapiro map `TauCeti.ContinuousCohomology.shapiroMapTopRep` is restriction to `U`
together with the coinduction counit `TauCeti.coindCounit`. Forgetting the scalars
(`TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntIso`) turns it into the canonical
Shapiro map of the underlying discrete `U`-module, by naturality of scalar restriction under
simultaneous change of group and coefficients
(`TauCeti.ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom`). Since the canonical map is
bijective, so is the generic one, and a bijective map between discrete topological modules is an
isomorphism.

## Main definitions

* `TauCeti.ContinuousCohomology.shapiroIso`: **Shapiro's lemma in every degree**,
  `Hⁿ(G, Coind_U^G A) ≅ Hⁿ(U, A)` for a closed subgroup `U` of a profinite group `G`, with forward
  map the canonical Shapiro map (`shapiroIso_hom`).
* `TauCeti.ContinuousCohomology.shapiroCochainMapTopRep`,
  `TauCeti.ContinuousCohomology.shapiroMapTopRep`,
  `TauCeti.ContinuousCohomology.shapiroIsoTopRep`: the Shapiro cochain map, the Shapiro map and
  Shapiro's isomorphism for a smooth discrete representation over an arbitrary ring.

## Main results

* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_discreteCoind_bot`:
  `Coind_U^G (Coind_1^U A)` is acyclic in every positive degree.
* `TauCeti.ContinuousCohomology.isIso_shapiroMap`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap`: the canonical Shapiro map is an isomorphism,
  resp. bijective, in every degree.
* `TauCeti.ContinuousCohomology.quasiIso_shapiroCochainMap`: equivalently, the Shapiro cochain map
  is a quasi-isomorphism of homogeneous cochain complexes.
* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_iff`: `Hⁿ(U, A)`
  vanishes exactly when `Hⁿ(G, Coind_U^G A)` does.
* `TauCeti.ContinuousCohomology.coeffMap_unit_comp_shapiroMap`,
  `TauCeti.ContinuousCohomology.res_comp_shapiroIso_inv`: for a discrete `G`-module `M`,
  restriction to `U` is the coefficient map of the unit `M → Coind_U^G M` of coinduction followed
  by the Shapiro map, so restriction followed by the inverse of Shapiro's isomorphism is the
  coefficient map of the unit.
* `TauCeti.ContinuousCohomology.isIso_shapiroMapTopRep`,
  `TauCeti.ContinuousCohomology.quasiIso_shapiroCochainMapTopRep`: the generic Shapiro map is an
  isomorphism in every degree, and the generic Shapiro cochain map a quasi-isomorphism, for a closed
  subgroup of a profinite group and an arbitrary coefficient ring.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.6.4), with the footnote on p. 61 recording that NSW write `Ind` for the coinduced module, and
  (1.3.7) for the dimension-shifting argument.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.5.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

/-! ### Acyclicity of `Coind_U^G (Coind_1^U A)` -/

section Acyclic

variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A]

/-- **`Coind_U^G (Coind_1^U A)` is acyclic in every positive degree**, for a compact group `G` and
any subgroup `U`: transitivity of coinduction identifies it with `Coind_1^G A`, whose
positive-degree cohomology vanishes. -/
instance subsingleton_continuousCohomology_discreteCoind_discreteCoind_bot (n : ℕ) :
    Subsingleton (continuousCohomology (n + 1)
      (ofDiscreteModule ℤ G (DiscreteCoind G U (DiscreteCoind U (⊥ : Subgroup U) A)))) :=
  -- `Coind_1^G A` needs an action of the trivial subgroup of `G` on `A`; any one will do, and
  -- `A` carries none by default, so the trivial action is supplied.
  letI : DistribMulAction (⊥ : Subgroup G) A :=
    { smul := fun _ a => a
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  subsingleton_continuousCohomology_of_iso
    (DiscreteCoind.transIsoBot U A isClosed_closure.isCompact) (n + 1)

end Acyclic

/-! ### Restriction through the unit of coinduction -/

section Unit

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [CompactSpace G] in
/-- **Restriction factors through the unit of coinduction and the Shapiro map**: the coefficient
map `Hⁿ(G, M) ⟶ Hⁿ(G, Coind_U^G M)` of the unit `m ↦ (g ↦ g • m)`, followed by the Shapiro map
`Hⁿ(G, Coind_U^G M) ⟶ Hⁿ(U, M)`, is restriction to `U`. Evaluation at `1` retracts the unit, and
the Shapiro map is restriction followed by evaluation at `1`. This holds for every subgroup `U` of
every topological group `G`. -/
@[reassoc]
theorem coeffMap_unit_comp_shapiroMap (n : ℕ) :
    coeffMap (ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
        fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m) n ≫ shapiroMap U M n =
      res U (ofDiscreteModule ℤ G M) n := by
  -- The restriction of the unit followed by the counit is the identity of `M` over `U`.
  have hcomp : (TopRep.resFunctor (U.subtype : U →* G)).map
      (ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
        fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m) ≫
      ofDiscreteModuleMap (DiscreteCoind.eval G U M).toIntLinearMap
        (fun u f => DiscreteCoind.eval_smul u f) = 𝟙 (ofDiscreteModule ℤ U M) := by
    refine TopRep.hom_ext (DFunLike.ext _ _ fun (m : M) => ?_)
    -- Not `rfl`: `DiscreteCoind.eval` and `DiscreteCoind.unit` are not exposed, so the evaluation
    -- lemmas are needed, with their morphisms spelled out because the source of the second factor
    -- is `TopRep.res U.subtype (ofDiscreteModule ℤ G _)` on one side and
    -- `ofDiscreteModule ℤ U _` on the other.
    exact (TopRep.comp_apply ((TopRep.resFunctor (U.subtype : U →* G)).map
        (ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
          fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m))
        (ofDiscreteModuleMap (DiscreteCoind.eval G U M).toIntLinearMap
          fun u f => DiscreteCoind.eval_smul u f) m).trans
      ((ofDiscreteModuleMap_hom_apply (G := U) (DiscreteCoind.eval G U M).toIntLinearMap
        (fun u f => DiscreteCoind.eval_smul u f) _).trans
        ((congrArg (DiscreteCoind.eval G U M) (ofDiscreteModuleMap_hom_apply
          (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
          (fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m) m)).trans
          (DiscreteCoind.eval_unit m)))
  rw [shapiroMap_eq_res_comp_coeffMap]
  -- Restriction is natural in the coefficients, and the two coefficient maps then compose to the
  -- coefficient map of `hcomp`, which is the identity. The composites are reassociated by hand,
  -- since their middle objects agree only up to `res_ofDiscreteModule`.
  refine (coeffMap_comp_res_assoc U _ n _).trans ?_
  exact ((congrArg (res U _ n ≫ ·) ((coeffMap_comp _ _ n).symm.trans
    (congrArg (coeffMap · n) hcomp))).trans
      ((congrArg (res U _ n ≫ ·) (coeffMap_id _ n)).trans (Category.comp_id _)))

end Unit

/-! ### Shapiro's lemma -/

section Shapiro

variable [TotallyDisconnectedSpace G] (hU : IsClosed (U : Set G))
  (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]

include hU

/-- **Shapiro's lemma in every degree, as an isomorphism of `TopModuleCat ℤ`**: for a closed
subgroup `U` of a profinite group `G` and a discrete `U`-module `A`, the canonical Shapiro map
`Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` is an isomorphism. -/
theorem isIso_shapiroMap (n : ℕ) : IsIso (shapiroMap U A n) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  induction n generalizing A with
  | zero => exact TopModuleCat.isIso_of_bijective _ (bijective_shapiroMap_zero U A)
  | succ n ih =>
    cases n with
    | zero => exact TopModuleCat.isIso_of_bijective _ (bijective_shapiroMap_one U A hU)
    | succ n =>
      -- The Shapiro map in degree `n + 2` is conjugate, through the connecting maps of
      -- `0 → A → Coind_1^U A → Q → 0` and of its coinduction to `G`, to the Shapiro map of
      -- `Q = Coind_1^U A ⧸ A` in degree `n + 1`, which is an isomorphism by induction.
      have := ih (DimensionShiftQuotient U A)
      have := isIso_coindBotShortExact_delta U A (n + 1) n.succ_pos
      have := ((coindBotShortExact U A).coind U hU).isIso_delta (n + 1)
      rw [(IsIso.eq_inv_comp _).2 ((coindBotShortExact U A).delta_shapiroMap hU (n + 1))]
      infer_instance

/-- **Shapiro's lemma in every degree**: for a closed subgroup `U` of a profinite group `G` and a
discrete `U`-module `A`, the canonical Shapiro map `Hⁿ(G, Coind_U^G A) ⟶ Hⁿ(U, A)` is bijective. -/
theorem bijective_shapiroMap (n : ℕ) : Function.Bijective (shapiroMap U A n) :=
  haveI := isIso_shapiroMap U hU A n
  ConcreteCategory.bijective_of_isIso _

/-- **Shapiro's lemma in every degree, on cochains**: for a closed subgroup `U` of a profinite group
`G` and a discrete `U`-module `A`, the Shapiro cochain map `σ ↦ ev₁ ∘ σ ∘ ι` from the homogeneous
cochains of `G` with coefficients `Coind_U^G A` to those of `U` with coefficients `A` is a
quasi-isomorphism. -/
theorem quasiIso_shapiroCochainMap : QuasiIso (shapiroCochainMap U A) :=
  (quasiIso_iff _).2 fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 <| by
    rw [homologyMap_shapiroCochainMap]
    exact isIso_shapiroMap U hU A n

/-- **The Shapiro isomorphism** `Hⁿ(G, Coind_U^G A) ≅ Hⁿ(U, A)` in every degree, for a closed
subgroup `U` of a profinite group `G` and a discrete `U`-module `A`. Its forward map is the
canonical Shapiro map, restriction to `U` followed by evaluation at `1` on the coefficients
(`shapiroIso_hom`, `TauCeti.ContinuousCohomology.shapiroMap_eq_res_comp_coeffMap`). -/
noncomputable def shapiroIso (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U A)) ≅
      continuousCohomology n (ofDiscreteModule ℤ U A) :=
  haveI := isIso_shapiroMap U hU A n
  asIso (shapiroMap U A n)

/-- The forward map of the Shapiro isomorphism is the canonical Shapiro map. -/
@[simp]
theorem shapiroIso_hom (n : ℕ) : (shapiroIso U hU A n).hom = shapiroMap U A n := (rfl)

/-- The inverse of the Shapiro isomorphism followed by the canonical Shapiro map is the identity. -/
@[simp]
theorem shapiroIso_inv_shapiroMap (n : ℕ) :
    (shapiroIso U hU A n).inv ≫ shapiroMap U A n = 𝟙 _ := by
  rw [← shapiroIso_hom U hU A n, Iso.inv_hom_id]

/-- The canonical Shapiro map followed by the inverse of the Shapiro isomorphism is the identity. -/
@[simp]
theorem shapiroMap_shapiroIso_inv (n : ℕ) :
    shapiroMap U A n ≫ (shapiroIso U hU A n).inv = 𝟙 _ := by
  rw [← shapiroIso_hom U hU A n, Iso.hom_inv_id]

/-- **Vanishing transfers along Shapiro's lemma**: `Hⁿ(U, A)` vanishes exactly when
`Hⁿ(G, Coind_U^G A)` does. -/
theorem subsingleton_continuousCohomology_discreteCoind_iff (n : ℕ) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G (DiscreteCoind G U A))) ↔
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ U A)) :=
  (Equiv.ofBijective _ (bijective_shapiroMap U hU A n)).subsingleton_congr

/-- Restriction of a discrete `G`-module `M` to a closed subgroup `U` of a profinite group,
followed by the inverse of Shapiro's isomorphism, is the coefficient map of the unit
`M → Coind_U^G M` of coinduction. -/
theorem res_comp_shapiroIso_inv (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] (n : ℕ) :
    res U (ofDiscreteModule ℤ G M) n ≫ (shapiroIso U hU M n).inv =
      coeffMap (ofDiscreteModuleMap (DiscreteCoind.unit G U M).toAddMonoidHom.toIntLinearMap
        fun g m => _root_.map_smul (DiscreteCoind.unit G U M) g m) n := by
  refine (Iso.comp_inv_eq _).2 ?_
  rw [shapiroIso_hom]
  exact (coeffMap_unit_comp_shapiroMap U M n).symm

end Shapiro

end TauCeti.ContinuousCohomology

namespace TauCeti.ContinuousCohomology

open CategoryTheory TauCeti.ContCohomology

universe u v

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {R : Type v} [Ring R] [TopologicalSpace R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)

local instance instDiscreteTopologyTopRep (A : SmoothDiscreteTopRep.{v, u, u} R U) :
    DiscreteTopology A.obj.V := A.property.discreteTopology

local instance instContinuousSMulTopRep (A : SmoothDiscreteTopRep.{v, u, u} R U) :
    ContinuousSMul U A.obj.V := A.property.continuousSMul

local instance instDiscreteTopologyTopRepAmbient (A : SmoothDiscreteTopRep.{v, u, u} R G) :
    DiscreteTopology A.obj.V := A.property.discreteTopology

/-- The Shapiro cochain map for a smooth discrete topological representation over any ring: the
cochain map `σ ↦ ev₁ ∘ σ ∘ ι` of the compatible pair of the inclusion `ι : U ↪ G` and the
coinduction counit `ev₁` (evaluation at `1`). -/
noncomputable def shapiroCochainMapTopRep (A : SmoothDiscreteTopRep.{v, u, u} R U) :
    TopRep.homogeneousCochains (coindTopRep R G U A).obj ⟶ TopRep.homogeneousCochains A.obj :=
  _root_.ContinuousCohomology.cochainsMap (ContinuousMonoidHom.subgroupSubtype U)
    (TopRep.ofHom (coindCounit R G U A))

/-- The defining equation of `shapiroCochainMapTopRep`: Mathlib's cochain map of the inclusion
`U → G` and the coinduction counit. -/
theorem shapiroCochainMapTopRep_def (A : SmoothDiscreteTopRep.{v, u, u} R U) :
    shapiroCochainMapTopRep U A =
      _root_.ContinuousCohomology.cochainsMap (ContinuousMonoidHom.subgroupSubtype U)
        (TopRep.ofHom (coindCounit R G U A)) := (rfl)

/-- The canonical Shapiro map for a smooth discrete topological representation over any ring:
restriction from `G` to `U` together with the coinduction counit (evaluation at `1`), that is, the
map `shapiroCochainMapTopRep` induces on homology. -/
noncomputable def shapiroMapTopRep (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    continuousCohomology n (coindTopRep R G U A).obj ⟶ continuousCohomology n A.obj :=
  HomologicalComplex.homologyMap (shapiroCochainMapTopRep U A) n

/-- The generic Shapiro map is the map induced on homology by the generic Shapiro cochain map. -/
@[simp]
theorem homologyMap_shapiroCochainMapTopRep (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    HomologicalComplex.homologyMap (shapiroCochainMapTopRep U A) n = shapiroMapTopRep U A n :=
  (rfl)

-- Not `@[simp]`: `shapiroMapTopRep` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `shapiroMapTopRep`: the compatible-pair map of the inclusion
`U → G` and the coinduction counit. -/
theorem shapiroMapTopRep_def (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    shapiroMapTopRep U A n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U)
        (TopRep.ofHom (coindCounit R G U A)) n := (rfl)

/-- The coefficient square behind the comparison of the two Shapiro maps: transporting a
coinduced function from the discrete `ℤ`-module model to the scalar-restricted representation
and then evaluating at `1` agrees with evaluating first and transporting afterwards. Both
transports are the identity on carriers (`cast_ofDiscreteModule_eq_restrictScalarsInt_obj`), and
both counits are evaluation at `1`. -/
private theorem shapiro_coeff_square (A : SmoothDiscreteTopRep.{v, u, u} R U) :
    (TopRep.resFunctor (U.subtype : U →* G)).map
        (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj (coindTopRep R G U A).obj)) ≫
        TopRep.resRestrictScalarsIntMap (U.subtype : U →* G)
          (TopRep.ofHom (coindCounit R G U A)) =
      ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
          (DiscreteCoind.eval G U A.obj.V).toIntLinearMap
          (fun u f => eval_subgroupSubtype_smul G U A.obj.V u f) ≫
        eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj A.obj) := by
  let fNew := TopRep.resRestrictScalarsIntMap (U.subtype : U →* G)
    (TopRep.ofHom (coindCounit R G U A))
  let fOld := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
    (DiscreteCoind.eval G U A.obj.V).toIntLinearMap
    (fun u f => eval_subgroupSubtype_smul G U A.obj.V u f)
  ext f
  -- `(resFunctor _).map a` and a composite of `TopRep` morphisms act by their underlying
  -- functions; this is the only definitional unfolding in the proof.
  change fNew ((eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj (coindTopRep R G U A).obj)).hom
      f) = (eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj A.obj)).hom (fOld.hom f)
  rw [TopRep.eqToHom_hom_apply, TopRep.eqToHom_hom_apply,
    cast_ofDiscreteModule_eq_restrictScalarsInt_obj,
    cast_ofDiscreteModule_eq_restrictScalarsInt_obj]
  -- Both sides evaluate the coinduced function `f` at `1`.
  let fR : DiscreteCoind G U A.obj.V := f
  have hleft : fNew f = fR 1 :=
    (TopRep.resRestrictScalarsIntMap_hom_apply (U.subtype : U →* G)
      (TopRep.ofHom (coindCounit R G U A)) fR).trans (coindCounit_apply R G U A fR)
  have hright : fOld.hom f = fR 1 :=
    (ofDiscreteModulePair_hom_apply (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (DiscreteCoind.eval G U A.obj.V).toIntLinearMap
        (fun u f => eval_subgroupSubtype_smul G U A.obj.V u f) fR).trans (by
      rw [AddMonoidHom.coe_toIntLinearMap, DiscreteCoind.eval_apply])
  exact hleft.trans hright.symm

private theorem shapiroMap_comp_ofDiscreteModuleRestrictScalarsIntIso_hom
    (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    shapiroMap U A.obj.V n ≫
        (ContCohomology.ofDiscreteModuleRestrictScalarsIntIso A.obj n).hom =
        (ContCohomology.ofDiscreteModuleRestrictScalarsIntIso
          (coindTopRep R G U A).obj n).hom ≫
        TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n) := by
  -- Move the coefficient transports past the change-of-group maps (`shapiro_coeff_square`), then
  -- move scalar restriction past the generic Shapiro map
  -- (`map_comp_restrictScalarsIntIso_hom_of_hom`).
  have hsquare := map_comp_coeffMap (ContinuousMonoidHom.subgroupSubtype U) _ _ _ _
    (shapiro_coeff_square U A) n
  have hscalar := ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom
    (ContinuousMonoidHom.subgroupSubtype U) (TopRep.ofHom (coindCounit R G U A)) n
  rw [ContCohomology.ofDiscreteModuleRestrictScalarsIntIso_hom,
    ContCohomology.ofDiscreteModuleRestrictScalarsIntIso_hom,
    ← coeffMap_eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj A.obj) n,
    ← coeffMap_eqToHom (ofDiscreteModule_eq_restrictScalarsInt_obj (coindTopRep R G U A).obj) n,
    shapiroMap_def]
  -- The two squares agree with the goal only up to the coercion of `subgroupSubtype U` to a
  -- monoid hom, so they are chained by `trans` rather than by rewriting.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hsquare).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hscalar).trans (Category.assoc _ _ _).symm

/-- The generic Shapiro map is an isomorphism for a closed subgroup of a profinite group. -/
theorem isIso_shapiroMapTopRep [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    IsIso (shapiroMapTopRep U A n) := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  let eX := ContCohomology.ofDiscreteModuleRestrictScalarsIntIso
    (coindTopRep R G U A).obj n
  let eA := ContCohomology.ofDiscreteModuleRestrictScalarsIntIso A.obj n
  have hcomm := shapiroMap_comp_ofDiscreteModuleRestrictScalarsIntIso_hom U A n
  have : IsIso (shapiroMap U A.obj.V n) := isIso_shapiroMap U hU A.obj.V n
  have : IsIso eX.hom := by
    dsimp [eX]
    infer_instance
  have : IsIso eA.hom := by
    dsimp [eA]
    infer_instance
  have hcomp : IsIso
      (eX.hom ≫ TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n)) := by
    rw [← hcomm]
    exact IsIso.comp_isIso' (isIso_shapiroMap U hU A.obj.V n)
      (inferInstance : IsIso
        (ContCohomology.ofDiscreteModuleRestrictScalarsIntIso A.obj n).hom)
  have : IsIso (TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n)) :=
    IsIso.of_isIso_comp_left eX.hom _
  have hbijRestricted := ConcreteCategory.bijective_of_isIso
    (TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n))
  have hbij : Function.Bijective (shapiroMapTopRep U A n) := hbijRestricted
  let : DiscreteTopology
      (continuousCohomology n (ofDiscreteModule ℤ U A.obj.V)) := inferInstance
  let hdisc : DiscreteTopology
      (TopModuleCat.restrictScalarsInt.obj (continuousCohomology n A.obj)) :=
    eA.toContinuousLinearEquiv.toHomeomorph.symm.isEmbedding.discreteTopology
  let : DiscreteTopology (continuousCohomology n A.obj) := hdisc
  exact TopModuleCat.isIso_of_bijective _ hbij

/-- **Shapiro's lemma on cochains for smooth discrete representations over any ring**: for a closed
subgroup `U` of a profinite group `G`, the generic Shapiro cochain map is a quasi-isomorphism. -/
theorem quasiIso_shapiroCochainMapTopRep [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) :
    QuasiIso (shapiroCochainMapTopRep U A) :=
  (quasiIso_iff _).2 fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 <| by
    rw [homologyMap_shapiroCochainMapTopRep]
    exact isIso_shapiroMapTopRep U hU A n

/-- Shapiro's lemma for smooth discrete topological representations over any ring. -/
noncomputable def shapiroIsoTopRep [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    continuousCohomology n (coindTopRep R G U A).obj ≅ continuousCohomology n A.obj :=
  have := isIso_shapiroMapTopRep U hU A n
  asIso (shapiroMapTopRep U A n)

@[simp]
theorem shapiroIsoTopRep_hom [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    (shapiroIsoTopRep U hU A n).hom = shapiroMapTopRep U A n := by
  rw [shapiroIsoTopRep, asIso_hom]

@[simp]
theorem shapiroMapTopRep_comp_shapiroIsoTopRep_inv [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    shapiroMapTopRep U A n ≫ (shapiroIsoTopRep U hU A n).inv = 𝟙 _ := by
  rw [← shapiroIsoTopRep_hom U hU A n, Iso.hom_inv_id]

@[simp]
theorem shapiroIsoTopRep_inv_comp_shapiroMapTopRep [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    (shapiroIsoTopRep U hU A n).inv ≫ shapiroMapTopRep U A n = 𝟙 _ := by
  rw [← shapiroIsoTopRep_hom U hU A n, Iso.inv_hom_id]

/-- Applying Shapiro after its inverse returns the original cohomology class. -/
theorem shapiroMapTopRep_shapiroIsoTopRep_inv_apply [TotallyDisconnectedSpace G]
    (hU : IsClosed (U : Set G)) (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ)
    (b : continuousCohomology n A.obj) :
    shapiroMapTopRep U A n ((shapiroIsoTopRep U hU A n).inv b) = b := by
  have h := ConcreteCategory.congr_hom
    (shapiroIsoTopRep_inv_comp_shapiroMapTopRep U hU A n) b
  exact h.trans rfl

end TauCeti.ContinuousCohomology
