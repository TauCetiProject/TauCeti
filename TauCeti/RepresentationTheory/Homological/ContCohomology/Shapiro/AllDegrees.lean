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
continuous cohomology; the isomorphism is `TauCeti.ContinuousCohomology.shapiroIso`.

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

## Main definitions

* `TauCeti.ContinuousCohomology.shapiroIso`: **Shapiro's lemma in every degree**,
  `Hⁿ(G, Coind_U^G A) ≅ Hⁿ(U, A)` for a closed subgroup `U` of a profinite group `G`, with forward
  map the canonical Shapiro map (`shapiroIso_hom`).

## Main results

* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_discreteCoind_bot`:
  `Coind_U^G (Coind_1^U A)` is acyclic in every positive degree.
* `TauCeti.ContinuousCohomology.isIso_shapiroMap`,
  `TauCeti.ContinuousCohomology.bijective_shapiroMap`: the canonical Shapiro map is an isomorphism,
  resp. bijective, in every degree.
* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_iff`: `Hⁿ(U, A)`
  vanishes exactly when `Hⁿ(G, Coind_U^G A)` does.
* `TauCeti.ContinuousCohomology.coeffMap_unit_comp_shapiroMap`,
  `TauCeti.ContinuousCohomology.res_comp_shapiroIso_inv`: for a discrete `G`-module `M`,
  restriction to `U` is the coefficient map of the unit `M → Coind_U^G M` of coinduction followed
  by the Shapiro map, so restriction followed by the inverse of Shapiro's isomorphism is the
  coefficient map of the unit.

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

open CategoryTheory TauCeti
open TauCeti.ContCohomology _root_.ContinuousCohomology

namespace TauCeti

universe u v w

/-- Restriction of a bundled smooth discrete representation to a subgroup. -/
noncomputable abbrev smoothDiscreteResTopRep {R : Type u} [Ring R] [TopologicalSpace R]
    {G : Type v} [Group G] [TopologicalSpace G] (U : Subgroup G)
    (A : SmoothDiscreteTopRep.{u, v, w} R G) : SmoothDiscreteTopRep.{u, v, w} R U :=
  ⟨TopRep.res (U.subtype : U →* G) A.obj, A.property.res continuous_subtype_val⟩

end TauCeti

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

/-- The canonical Shapiro map for a smooth discrete topological representation over any ring. -/
@[expose] noncomputable def shapiroMapTopRep (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    continuousCohomology n (coindTopRep R G U A).obj ⟶ continuousCohomology n A.obj :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U)
    (TopRep.ofHom (coindCounit R G U A)) n

omit [CompactSpace G] in
/-- Naturality of continuous cohomology under simultaneous change of group and coefficients. -/
private theorem map_naturality
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {X X' : TopRep.{u} R G} {Y Y' : TopRep.{u} R H}
    (phi : H →ₜ* G) (f : TopRep.res (phi : H →* G) X ⟶ Y)
    (f' : TopRep.res (phi : H →* G) X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : (TopRep.resFunctor (phi : H →* G)).map a ≫ f' = f ≫ b) (n : ℕ) :
    _root_.ContinuousCohomology.map phi f n ≫ coeffMap b n =
      coeffMap a n ≫ _root_.ContinuousCohomology.map phi f' n := by
  rw [coeffMap_def, coeffMap_def,
    ← _root_.ContinuousCohomology.map_comp phi (ContinuousMonoidHom.id H) f b n,
    ← _root_.ContinuousCohomology.map_comp (ContinuousMonoidHom.id G) phi a f' n]
  apply map_congr
  · ext x
    rfl
  · exact heq_of_eq h.symm

private theorem shapiroMap_comp_ofDiscreteModuleRestrictScalarsIntIso_hom
    (A : SmoothDiscreteTopRep.{v, u, u} R U) (n : ℕ) :
    shapiroMap U A.obj.V n ≫
        (ContCohomology.ofDiscreteModuleRestrictScalarsIntIso A.obj n).hom =
        (ContCohomology.ofDiscreteModuleRestrictScalarsIntIso
          (coindTopRep R G U A).obj n).hom ≫
        TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n) := by
  let hA := ContCohomology.ofDiscreteModule_eq_restrictScalarsInt_obj A.obj
  let hX := ContCohomology.ofDiscreteModule_eq_restrictScalarsInt_obj
    (coindTopRep R G U A).obj
  let fOld := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
      (DiscreteCoind.eval G U A.obj.V).toIntLinearMap
        (eval_subgroupSubtype_smul G U A.obj.V)
  let fNew := TopRep.resRestrictScalarsIntMap (U.subtype : U →* G)
    (TopRep.ofHom (coindCounit R G U A))
  have hcoeff :
      (TopRep.resFunctor (U.subtype : U →* G)).map (eqToHom hX) ≫ fNew =
        fOld ≫ eqToHom hA := by
    ext f
    change fNew ((eqToHom hX).hom f) = (eqToHom hA).hom (fOld.hom f)
    dsimp only [hX, hA]
    rw [TopRep.eqToHom_hom_apply, TopRep.eqToHom_hom_apply,
      ContCohomology.cast_ofDiscreteModule_eq_restrictScalarsInt_obj,
      ContCohomology.cast_ofDiscreteModule_eq_restrictScalarsInt_obj]
    have hleft : fNew f = (show DiscreteCoind G U A.obj.V from f) 1 := by
      let fR : DiscreteCoind G U A.obj.V := f
      have hmap : fNew f = (TopRep.ofHom (coindCounit R G U A)).hom fR := by
        exact TopRep.resRestrictScalarsIntMap_hom_apply (U.subtype : U →* G)
          (TopRep.ofHom (coindCounit R G U A)) fR
      have heval : (TopRep.ofHom (coindCounit R G U A)).hom fR = fR 1 :=
        coindCounit_apply R G U A fR
      exact hmap.trans heval
    have hright : fOld.hom f = (show DiscreteCoind G U A.obj.V from f) 1 := by
      let fR : DiscreteCoind G U A.obj.V := f
      have hpair := ofDiscreteModulePair_hom_apply
        (ContinuousMonoidHom.subgroupSubtype U : U →* G)
        (DiscreteCoind.eval G U A.obj.V).toIntLinearMap
          (eval_subgroupSubtype_smul G U A.obj.V) fR
      exact hpair.trans (by
        rw [AddMonoidHom.coe_toIntLinearMap, DiscreteCoind.eval_apply])
    exact hleft.trans hright.symm
  have hsquare := map_naturality
    (ContinuousMonoidHom.subgroupSubtype U) fOld fNew (eqToHom hX) (eqToHom hA) hcoeff n
  have hscalar := ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom
    (ContinuousMonoidHom.subgroupSubtype U) (TopRep.ofHom (coindCounit R G U A)) n
  have hscalar' :
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U) fNew n ≫
          (ContCohomology.restrictScalarsIntIso A.obj n).hom =
        (ContCohomology.restrictScalarsIntIso (coindTopRep R G U A).obj n).hom ≫
          TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n) := by
    exact hscalar
  rw [ContCohomology.ofDiscreteModuleRestrictScalarsIntIso_hom,
    ContCohomology.ofDiscreteModuleRestrictScalarsIntIso_hom]
  change shapiroMap U A.obj.V n ≫
      (eqToHom (congrArg (continuousCohomology n) hA) ≫
        (ContCohomology.restrictScalarsIntIso A.obj n).hom) =
    (eqToHom (congrArg (continuousCohomology n) hX) ≫
        (ContCohomology.restrictScalarsIntIso (coindTopRep R G U A).obj n).hom) ≫
      TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n)
  rw [← coeffMap_eqToHom hA n, ← coeffMap_eqToHom hX n]
  rw [shapiroMap_def]
  change _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U) fOld n ≫
      (coeffMap (eqToHom hA) n ≫ (ContCohomology.restrictScalarsIntIso A.obj n).hom) =
    (coeffMap (eqToHom hX) n ≫
        (ContCohomology.restrictScalarsIntIso (coindTopRep R G U A).obj n).hom) ≫
      TopModuleCat.restrictScalarsInt.map (shapiroMapTopRep U A n)
  rw [← Category.assoc, hsquare, Category.assoc, hscalar', ← Category.assoc]
  rfl

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
