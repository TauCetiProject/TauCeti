/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
public import TauCeti.GroupTheory.Index.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Transitivity of all-degree corestriction

For open subgroups `V ≤ U ≤ G` of finite index, corestriction on canonical continuous cohomology
is transitive in every degree:

```text
cor_V^G = cor_U^G ∘ cor_V^U.
```

The relative map `corestrictionLe` first transports cohomology from `V` to its copy
`V.subgroupOf U` inside `U`, then applies corestriction there. Transitivity gives all-degree
corestriction coherent transfer maps along subgroup towers: a transfer may be assembled through
intermediate open subgroups without depending on how the inclusion is factored.

## Main definitions

* `TauCeti.ContinuousCohomology.subgroupOfMap`: transport from a subgroup to its canonical copy
  inside an intermediate subgroup.
* `TauCeti.ContinuousCohomology.corestrictionLe`: all-degree corestriction along an inclusion.

## Main results

* `TauCeti.ContinuousCohomology.shapiroMap_trans`: transitivity of the Shapiro map.
* `TauCeti.ContinuousCohomology.corestriction_trans`: transitivity of corestriction in every
  degree.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U V : Subgroup G) (hVU : V ≤ U)
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] in
private theorem id_subgroupOf_smul (x : V.subgroupOf U) (m : M) :
    (LinearMap.id : M →ₗ[ℤ] M)
        ((Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V) x • m) =
      x • m := rfl

/-- Transport continuous cohomology from a subgroup `V` to its canonical copy
`V.subgroupOf U` inside a larger subgroup `U`. -/
noncomputable def subgroupOfMap (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ V M) ⟶
      continuousCohomology n (ofDiscreteModule ℤ (V.subgroupOf U) M) :=
  _root_.ContinuousCohomology.map
    (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
    (ofDiscreteModulePair
      (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →* V)
      (LinearMap.id : M →ₗ[ℤ] M) (id_subgroupOf_smul U V hVU M)) n

omit [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G M] in
/-- The defining equation for transport to the canonical copy `V.subgroupOf U`. -/
theorem subgroupOfMap_def (n : ℕ) :
    subgroupOfMap U V hVU M n =
      _root_.ContinuousCohomology.map
        (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →ₜ* V)
        (ofDiscreteModulePair
          (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U →* V)
          (LinearMap.id : M →ₗ[ℤ] M) (by intro x m; rfl)) n := by
  rfl

/-- **All-degree corestriction along an inclusion** `V ≤ U`: transport the cohomology of `V` to
its canonical copy `V.subgroupOf U`, then apply corestriction inside `U`. The intermediate subgroup
`U` need only be closed in the compact group `G`; the lower subgroup is required to be open in
`U` and of finite index there. -/
noncomputable def corestrictionLe (hU : IsClosed (U : Set G))
    [(V.subgroupOf U).FiniteIndex]
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U)) (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ V M) ⟶
      continuousCohomology n (ofDiscreteModule ℤ U M) := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  exact subgroupOfMap U V hVU M n ≫
    corestriction (G := U) (V.subgroupOf U) M hV n

/-- The defining equation for relative corestriction: transport to `V.subgroupOf U`, then apply
corestriction inside `U`. -/
theorem corestrictionLe_def (hU : IsClosed (U : Set G))
    [(V.subgroupOf U).FiniteIndex]
    (hV : IsOpen ((V.subgroupOf U : Subgroup U) : Set U)) (n : ℕ) :
    letI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
    corestrictionLe U V hVU M hU hV n =
      subgroupOfMap U V hVU M n ≫
        corestriction (G := U) (V.subgroupOf U) M hV n := by
  rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul G M] in
private theorem traceIntLinearMap_smul [(V.subgroupOf U).FiniteIndex]
    (u : U) (φ : DiscreteCoind U (V.subgroupOf U) M) :
    (DiscreteCoind.trace U (V.subgroupOf U) M).toIntLinearMap (u • φ) =
      u • (DiscreteCoind.trace U (V.subgroupOf U) M).toIntLinearMap φ := by
  exact _root_.map_smul (DiscreteCoind.trace U (V.subgroupOf U) M) u φ

omit [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] in
private theorem trace_transEquiv_symm
    [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]
    (f : DiscreteCoind G V M) :
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    let e := DiscreteCoind.transEquiv (A := M) (U := U) (V := V.subgroupOf U) (W := V)
      (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
      isClosed_closure.isCompact
    DiscreteCoind.trace G V M f =
      DiscreteCoind.trace G U M
        (DiscreteCoind.map (DiscreteCoind.trace U (V.subgroupOf U) M).toIntLinearMap
          (traceIntLinearMap_smul U V M)
          (e.symm f)) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let e := Subgroup.quotientEquivProdOfLE' hVU Quotient.out Quotient.out_eq
  let c := DiscreteCoind.transEquiv (A := M) (U := U) (V := V.subgroupOf U) (W := V)
    (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
    isClosed_closure.isCompact
  dsimp only
  -- Reindex the direct trace by `(G ⧸ U) × (U ⧸ V)` and compare its summands with the
  -- corresponding outer and inner traces.
  rw [DiscreteCoind.trace_eq_sum_transversal
    (Subgroup.compositeTransversal G U V hVU Quotient.out Quotient.out_eq Quotient.out)
    (Subgroup.compositeTransversal_spec G U V hVU Quotient.out Quotient.out_eq
      Quotient.out Quotient.out_eq), DiscreteCoind.trace_apply, ← e.symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [DiscreteCoind.map_apply]
  -- `DiscreteCoind.map` leaves the outer action folded into its function coercion.
  change _ = a.out • DiscreteCoind.trace U (V.subgroupOf U) M (c.symm f a.out⁻¹)
  rw [DiscreteCoind.trace_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Subgroup.compositeTransversal_apply, e, e.apply_symm_apply, mul_smul,
    c, DiscreteCoind.transEquiv_symm_apply, Subgroup.smul_def]
  congr 2
  rw [mul_inv_rev]
  rfl

omit [TotallyDisconnectedSpace G] [ContinuousSMul G M] in
/-- **Shapiro's map is transitive.** For subgroups `V ≤ U` of a compact group `G`, the Shapiro
map of `V` followed by the transport to the copy `V.subgroupOf U` of `V` inside `U` is the
identification `Coind_V^G M ≅ Coind_U^G (Coind_{V ⊓ U}^U M)` of coinduced modules followed by the
Shapiro maps of `U` in `G` and of `V.subgroupOf U` in `U`. -/
theorem shapiroMap_trans (n : ℕ) :
    let c := DiscreteCoind.transIso (A := M) (U := U) (V := V.subgroupOf U) (W := V)
      (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
      isClosed_closure.isCompact
    coeffMap c.inv n ≫ shapiroMap U (DiscreteCoind U (V.subgroupOf U) M) n ≫
        shapiroMap (V.subgroupOf U) M n =
      shapiroMap V M n ≫ subgroupOfMap U V hVU M n := by
  dsimp only
  let e := DiscreteCoind.transEquiv (A := M) (U := U) (V := V.subgroupOf U) (W := V)
    (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
    isClosed_closure.isCompact
  have he_smul (g : G) (φ : DiscreteCoind G V M) :
      e.symm.toAddMonoidHom.toIntLinearMap ((ContinuousMonoidHom.id G : G →* G) g • φ) =
        g • e.symm.toAddMonoidHom.toIntLinearMap φ := by
    exact DiscreteCoind.transEquiv_symm_smul (Subgroup.map_subgroupOf_eq_of_le hVU)
      (Subgroup.subgroupOf_smul_eq U V M)
      isClosed_closure.isCompact g φ
  let c := DiscreteCoind.transIso (A := M) (U := U) (V := V.subgroupOf U) (W := V)
    (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
    isClosed_closure.isCompact
  let p := ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
    e.symm.toAddMonoidHom.toIntLinearMap he_smul
  have hp : _root_.ContinuousCohomology.map (ContinuousMonoidHom.id G) p n =
      coeffMap c.inv n := by
    rw [coeffMap_def]
    apply map_congr rfl
    apply ofDiscreteModulePair_heq_of_hom_apply rfl
    intro φ
    exact (DiscreteCoind.transIso_inv_apply
      (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
      isClosed_closure.isCompact φ).trans rfl
  rw [← hp]
  -- Both routes are maps of compatible pairs whose underlying coefficient map evaluates an
  -- element of `Coind_V^G M` at `1`; functoriality reduces the comparison to that observation.
  let pU := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype U : U →* G)
    (DiscreteCoind.eval G U (DiscreteCoind U (V.subgroupOf U) M)).toIntLinearMap
      (fun u f => by exact TauCeti.ContCohomology.eval_subgroupSubtype_smul G U _ u f)
  let pVU := ofDiscreteModulePair
    (ContinuousMonoidHom.subgroupSubtype (V.subgroupOf U) : V.subgroupOf U →* U)
    (DiscreteCoind.eval U (V.subgroupOf U) M).toIntLinearMap
      (fun v f => by
        exact TauCeti.ContCohomology.eval_subgroupSubtype_smul U (V.subgroupOf U) M v f)
  let pV := ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype V : V →* G)
    (DiscreteCoind.eval G V M).toIntLinearMap
      (fun v f => by exact TauCeti.ContCohomology.eval_subgroupSubtype_smul G V M v f)
  let τ : V.subgroupOf U →ₜ* V :=
    (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : V.subgroupOf U ≃ₜ* V)
  let pT := ofDiscreteModulePair (τ : V.subgroupOf U →* V)
    (LinearMap.id : M →ₗ[ℤ] M) (id_subgroupOf_smul U V hVU M)
  simp only [shapiroMap_def, subgroupOfMap]
  -- Expose the compatible-pair maps hidden by the Shapiro and coefficient-map wrappers.
  change _root_.ContinuousCohomology.map (ContinuousMonoidHom.id G) p n ≫
        _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U) pU n ≫
          _root_.ContinuousCohomology.map
            (ContinuousMonoidHom.subgroupSubtype (V.subgroupOf U)) pVU n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype V) pV n ≫
        _root_.ContinuousCohomology.map τ pT n
  rw [← _root_.ContinuousCohomology.map_comp]
  conv_rhs => rw [← _root_.ContinuousCohomology.map_comp]
  rw [← _root_.ContinuousCohomology.map_comp]
  let φL := (ContinuousMonoidHom.id G).comp
    ((ContinuousMonoidHom.subgroupSubtype U).comp
      (ContinuousMonoidHom.subgroupSubtype (V.subgroupOf U)))
  let φR := (ContinuousMonoidHom.subgroupSubtype V).comp τ
  have hφ : φL = φR := by
    ext x
    rfl
  let qL :=
    (TopRep.resFunctor
      ((ContinuousMonoidHom.subgroupSubtype U).comp
        (ContinuousMonoidHom.subgroupSubtype (V.subgroupOf U)) :
          V.subgroupOf U →* G)).map p ≫
      (TopRep.resFunctor
        (ContinuousMonoidHom.subgroupSubtype (V.subgroupOf U) : V.subgroupOf U →* U)).map pU ≫
        pVU
  let qR := (TopRep.resFunctor (τ : V.subgroupOf U →* V)).map pV ≫ pT
  -- Fold the two expanded composites into the local compatible-pair abbreviations.
  change _root_.ContinuousCohomology.map φL qL n =
    _root_.ContinuousCohomology.map φR qR n
  refine map_congr hφ ?_ n
  subst φR
  apply heq_of_eq
  refine TopRep.hom_ext (DFunLike.ext _ _ fun f => ?_)
  let f' : DiscreteCoind G V M := f
  -- Composition in `TopRep` evaluates by composing the underlying homomorphisms.
  change pVU.hom (pU.hom (p.hom f)) = pT.hom (pV.hom f)
  have hp_apply : p.hom f = e.symm f' := by
    exact ofDiscreteModulePair_hom_apply _ _ _ f'
  have hpU_apply (x : DiscreteCoind G U (DiscreteCoind U (V.subgroupOf U) M)) :
      pU.hom x = x 1 :=
    (ofDiscreteModulePair_hom_apply _ _ _ x).trans (DiscreteCoind.eval_apply x)
  have hpVU_apply (x : DiscreteCoind U (V.subgroupOf U) M) : pVU.hom x = x 1 :=
    (ofDiscreteModulePair_hom_apply _ _ _ x).trans (DiscreteCoind.eval_apply x)
  have hpV_apply (x : DiscreteCoind G V M) : pV.hom x = x 1 :=
    (ofDiscreteModulePair_hom_apply _ _ _ x).trans (DiscreteCoind.eval_apply x)
  have hpT_apply (x : M) : pT.hom x = x :=
    (ofDiscreteModulePair_hom_apply _ _ _ x).trans (LinearMap.id_apply x)
  rw [hp_apply, hpU_apply, hpVU_apply]
  -- The remaining coinduction evaluations are hidden behind function-like coercions.
  change (e.symm f' (1 : G)) (1 : U) = pT.hom (pV.hom f')
  rw [hpV_apply, hpT_apply]
  rw [DiscreteCoind.transEquiv_symm_apply]
  simp

omit [TotallyDisconnectedSpace G] [ContinuousSMul G M] in
private theorem transIso_inv_comp_trace
    [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex] :
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    let c := DiscreteCoind.transIso (A := M) (U := U) (V := V.subgroupOf U) (W := V)
      (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
      isClosed_closure.isCompact
    c.inv ≫
        ofDiscreteModuleMap
          (DiscreteCoind.map
            (DiscreteCoind.trace U (V.subgroupOf U) M).toAddMonoidHom.toIntLinearMap
            (traceIntLinearMap_smul U V M)).toAddMonoidHom.toIntLinearMap
          (fun g φ => DiscreteCoind.map_smul
            (DiscreteCoind.trace U (V.subgroupOf U) M).toAddMonoidHom.toIntLinearMap
            (traceIntLinearMap_smul U V M) g φ) ≫
      ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        (fun g φ => _root_.map_smul (DiscreteCoind.trace G U M) g φ) =
      ofDiscreteModuleMap (DiscreteCoind.trace G V M).toAddMonoidHom.toIntLinearMap
        (fun g φ => _root_.map_smul (DiscreteCoind.trace G V M) g φ) := by
  dsimp only
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let c := DiscreteCoind.transIso (A := M) (U := U) (V := V.subgroupOf U) (W := V)
    (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
    isClosed_closure.isCompact
  let tVU := ofDiscreteModuleMap
    (DiscreteCoind.map
      (DiscreteCoind.trace U (V.subgroupOf U) M).toAddMonoidHom.toIntLinearMap
      (traceIntLinearMap_smul U V M)).toAddMonoidHom.toIntLinearMap
    (fun g φ => DiscreteCoind.map_smul
      (DiscreteCoind.trace U (V.subgroupOf U) M).toAddMonoidHom.toIntLinearMap
      (traceIntLinearMap_smul U V M) g φ)
  let tU := ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
    (fun g φ => _root_.map_smul (DiscreteCoind.trace G U M) g φ)
  let tV := ofDiscreteModuleMap (DiscreteCoind.trace G V M).toAddMonoidHom.toIntLinearMap
    (fun g φ => _root_.map_smul (DiscreteCoind.trace G V M) g φ)
  -- Fold the displayed trace morphisms into the local names used in the extensionality proof.
  change c.inv ≫ tVU ≫ tU = tV
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (f : DiscreteCoind G V M) => ?_)
  have h₁ : (c.inv ≫ tVU ≫ tU).hom f = tU.hom (tVU.hom (c.inv.hom f)) :=
    (TopRep.comp_apply (c.inv ≫ tVU) tU f).trans
      (congrArg (fun x => tU.hom x) (TopRep.comp_apply c.inv tVU f))
  have h₂ : c.inv.hom f =
      (DiscreteCoind.transEquiv (A := M) (U := U) (V := V.subgroupOf U) (W := V)
        (Subgroup.map_subgroupOf_eq_of_le hVU) (Subgroup.subgroupOf_smul_eq U V M)
        isClosed_closure.isCompact).symm f :=
    DiscreteCoind.transIso_inv_apply _ _ _ f
  have h₃ : tU.hom (tVU.hom (c.inv.hom f)) = DiscreteCoind.trace G V M f :=
    (congrArg (fun x => tU.hom (tVU.hom x)) h₂).trans
      ((congrArg (fun x => tU.hom x) (ofDiscreteModuleMap_hom_apply _ _ _)).trans
        ((ofDiscreteModuleMap_hom_apply _ _ _).trans
          (trace_transEquiv_symm U V hVU M f).symm))
  have h₄ : tV.hom f = DiscreteCoind.trace G V M f :=
    ofDiscreteModuleMap_hom_apply _ _ f
  exact h₁.trans (h₃.trans h₄.symm)

/-- **Transitivity of corestriction in every degree.** For open finite-index subgroups
`V ≤ U ≤ G`, direct corestriction from `V` to `G` equals corestriction from `V` to `U` followed by
corestriction from `U` to `G`. -/
theorem corestriction_trans (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))
    [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex] (n : ℕ) :
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    corestriction V M hV n =
      corestrictionLe U V hVU M (U.isClosed_of_isOpen hU)
          (Subgroup.subgroupOf_isOpen U V hV) n ≫
        corestriction U M hU n := by
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  have := isIso_shapiroMap V (V.isClosed_of_isOpen hV) M n
  -- Cancel direct Shapiro. Iterated Shapiro turns the two corestrictions into the two trace maps;
  -- naturality moves the inner trace through Shapiro, and the trace tower identity finishes.
  rw [← cancel_epi (shapiroMap V M n), shapiroMap_comp_corestriction]
  rw [corestrictionLe]
  simp only [← Category.assoc]
  rw [← shapiroMap_trans U V hVU M n]
  simp only [Category.assoc, shapiroMap_comp_corestriction]
  rw [← shapiroMap_naturality_assoc U (DiscreteCoind U (V.subgroupOf U) M)
    (DiscreteCoind.trace U (V.subgroupOf U) M).toAddMonoidHom
    (fun u φ => _root_.map_smul (DiscreteCoind.trace U (V.subgroupOf U) M) u φ) n]
  simp only [shapiroMap_comp_corestriction]
  rw [← coeffMap_comp, ← coeffMap_comp]
  rw [transIso_inv_comp_trace U V hVU M]

end TauCeti.ContinuousCohomology
