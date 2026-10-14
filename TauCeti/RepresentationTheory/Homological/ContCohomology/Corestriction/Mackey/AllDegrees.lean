/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegreeTransitivity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Conjugation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# The Mackey double-coset formula in every degree

Let `U` be an open subgroup and `V` a closed subgroup of a profinite group `G`, and `M` a discrete
`G`-module. The Mackey double-coset formula (NSW (1.5.6)) computes restriction to `V` of the
corestriction from `U` on Mathlib's canonical continuous cohomology, in every degree `n`:

```text
res^G_V ∘ cor^G_U = ∑_{VsU ∈ V \ G / U} cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res^U_{U ⊓ s⁻¹Vs},
```

for any choice `r` of representatives `s = r D` of the double cosets. As in degrees `0`, `1`, `2`
(`TauCeti.ContCohomology.explicitCor0_mackey` and its companions), the composite
`(s)_* ∘ res^U_{U ⊓ s⁻¹Vs}` is the single compatible-pair map along
`Subgroup.continuousMackeyToH : V ⊓ sUs⁻¹ → U`, `y ↦ s⁻¹ y s`, with coefficient map `m ↦ s • m`,
and the summand `TauCeti.ContinuousCohomology.mackeyTerm` follows it with the all-degree
corestriction from the Mackey subgroup `V ⊓ sUs⁻¹`, which is open in the profinite group `V`.

There is no cochain formula in arbitrary degree; the formula is read off from coinduced modules.
Corestriction is the inverse of Shapiro's isomorphism followed by the coefficient map of the trace
`Coind_U^G M → M`, so after Shapiro's isomorphism for `U` both sides become coefficient maps
`Hⁿ(G, Coind_U^G M) ⟶ Hⁿ(G, Coind_V^G M)` followed by the Shapiro map of `V`:

* on the left, by `TauCeti.ContinuousCohomology.coeffMap_unit_comp_shapiroMap`, the coefficient
  map of the trace followed by the unit `M → Coind_V^G M`;
* on the right, the coefficient map of `Φ ↦ (x ↦ ∑_w w s • Φ (s⁻¹ w⁻¹ x))`, the sum over
  `V ⧸ (V ⊓ sUs⁻¹)`: conjugation of coinduced modules
  (`TauCeti.ContinuousCohomology.shapiroMap_comp_map_of_conj`, which rests on inner automorphisms
  acting trivially), transitivity of the Shapiro map
  (`TauCeti.ContinuousCohomology.shapiroMap_trans`) and its naturality move the summand there.

The two module maps agree by the double-coset splitting of `G ⧸ U`
(`TauCeti.mackeyQuotientEquiv`), the trace being computed along the adapted transversal
`Subgroup.mackeyTransversal`. This follows the coinduced-module treatment of the transfer in
Brown, *Cohomology of Groups*, III §9.

## Main definitions

* `TauCeti.ContinuousCohomology.mackeyTerm`: the summand `cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res`
  attached to `s`, in every degree.

## Main results

* `TauCeti.ContinuousCohomology.corestriction_mackey`: **the Mackey double-coset formula** in
  every degree, for any choice of double-coset representatives.
* `TauCeti.ContinuousCohomology.mackeyTerm_eq_of_mk_eq`: each summand depends only on the double
  coset of its representative.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.6).
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U V : Subgroup G) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G)) (hV : IsClosed (V : Set G)) [U.FiniteIndex]

/-- **One summand of the Mackey double-coset formula**, `cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res`, in
every degree: the map of the compatible pair of `V ⊓ sUs⁻¹ → U`, `y ↦ s⁻¹ y s`, and of the action
of `s` on `M`, followed by corestriction from the Mackey subgroup `V ⊓ sUs⁻¹` up to `V`. The
subgroup `U` is open and `V` is closed in the profinite group `G`, so that `V` is profinite and the
Mackey subgroup is open in `V`. -/
noncomputable def mackeyTerm (s : G) (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ U M) ⟶
      continuousCohomology n (ofDiscreteModule ℤ V M) :=
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  _root_.ContinuousCohomology.map (U.continuousMackeyToH V s)
      (ofDiscreteModulePair
        (U.continuousMackeyToH V s : (mackeySubgroup s U V).subgroupOf V →* U)
        (DistribSMul.toAddMonoidHom M s).toIntLinearMap
        (smul_continuousMackeyToH_smul G M U V s)) n ≫
    corestriction ((mackeySubgroup s U V).subgroupOf V) M
      (U.isOpen_mackeySubgroup_subgroupOf V hU s) n

-- Not `@[simp]`: `mackeyTerm` is the intended normal form, and this lemma unfolds it.
/-- The defining equation of `mackeyTerm`: the map of the compatible pair of conjugation by `s`
and the action of `s`, followed by corestriction from the Mackey subgroup up to `V`. -/
theorem mackeyTerm_def (s : G) (n : ℕ) :
    letI : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
    mackeyTerm U V M hU hV s n =
      _root_.ContinuousCohomology.map (U.continuousMackeyToH V s)
          (ofDiscreteModulePair
            (U.continuousMackeyToH V s : (mackeySubgroup s U V).subgroupOf V →* U)
            (DistribSMul.toAddMonoidHom M s).toIntLinearMap
            (smul_continuousMackeyToH_smul G M U V s)) n ≫
        corestriction ((mackeySubgroup s U V).subgroupOf V) M
          (U.isOpen_mackeySubgroup_subgroupOf V hU s) n :=
  (rfl)

/-- The `G`-equivariant map `Coind_U^G M → Coind_V^G M` underlying the summand of `s`: conjugation
`Coind_U^G M → Coind_{V ⊓ sUs⁻¹}^G M`, the transitivity identification with
`Coind_V^G (Coind_{V ⊓ sUs⁻¹}^V M)`, and the coinduction of the trace from the Mackey subgroup to
`V`. It sends `Φ` to `x ↦ ∑_{w} w • s • Φ (s⁻¹ w⁻¹ x)`, the sum over `V ⧸ (V ⊓ sUs⁻¹)`. -/
private noncomputable def mackeyCoindMap (s : G) :
    ofDiscreteModule ℤ G (DiscreteCoind G U M) ⟶ ofDiscreteModule ℤ G (DiscreteCoind G V M) :=
  ofDiscreteModuleMap (DiscreteCoind.conj U (mackeySubgroup s U V) M s
      mackeySubgroup_le_conj).toAddMonoidHom.toIntLinearMap
      (fun g Φ => _root_.map_smul (DiscreteCoind.conj U (mackeySubgroup s U V) M s
        mackeySubgroup_le_conj) g Φ) ≫
    (DiscreteCoind.transIso (A := M) (U := V) (V := (mackeySubgroup s U V).subgroupOf V)
      (W := mackeySubgroup s U V) (Subgroup.map_subgroupOf_eq_of_le mackeySubgroup_le_right)
      (Subgroup.subgroupOf_smul_eq V (mackeySubgroup s U V) M) isClosed_closure.isCompact).inv ≫
    ofDiscreteModuleMap
      (DiscreteCoind.map
        (DiscreteCoind.trace V ((mackeySubgroup s U V).subgroupOf V) M).toIntLinearMap
        (fun v φ => _root_.map_smul (DiscreteCoind.trace V ((mackeySubgroup s U V).subgroupOf V) M)
          v φ)).toAddMonoidHom.toIntLinearMap
      (fun g φ => DiscreteCoind.map_smul _ _ g φ)

/-- **The Shapiro map turns a Mackey summand into a coefficient map**: the Shapiro map of `U`
followed by the summand of `s` is the coefficient map of `mackeyCoindMap` followed by the Shapiro
map of `V`. -/
private theorem shapiroMap_comp_mackeyTerm (s : G) (n : ℕ) :
    shapiroMap U M n ≫ mackeyTerm U V M hU hV s n =
      coeffMap (mackeyCoindMap U V M s) n ≫ shapiroMap V M n := by
  let _ : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have hWV : mackeySubgroup s U V ≤ V := mackeySubgroup_le_right
  -- The summand's compatible pair factors through the Mackey subgroup read inside `G`.
  let κ : mackeySubgroup s U V →ₜ* U := (U.continuousMackeyToH V s).comp
    ((Subgroup.subgroupOfContinuousMulEquivOfLe hWV).symm :
      mackeySubgroup s U V ≃ₜ* (mackeySubgroup s U V).subgroupOf V)
  have hκ (w : mackeySubgroup s U V) : ((κ : mackeySubgroup s U V →* U) w : G) =
      s⁻¹ * w * s := by
    simp [κ]
  let f := ofDiscreteModulePair (κ : mackeySubgroup s U V →* U)
    (DistribSMul.toAddMonoidHom M s).toIntLinearMap
    (fun w m => by
      simp only [AddMonoidHom.coe_toIntLinearMap, DistribSMul.toAddMonoidHom_apply,
        Subgroup.smul_def, hκ, smul_smul]
      group)
  have hf (m : M) : f.hom m = s • m := ofDiscreteModulePair_hom_apply _ _ _ m
  have hpair : _root_.ContinuousCohomology.map (U.continuousMackeyToH V s)
      (ofDiscreteModulePair
        (U.continuousMackeyToH V s : (mackeySubgroup s U V).subgroupOf V →* U)
        (DistribSMul.toAddMonoidHom M s).toIntLinearMap
        (smul_continuousMackeyToH_smul G M U V s)) n =
      _root_.ContinuousCohomology.map κ f n ≫
        subgroupOfMap V (mackeySubgroup s U V) hWV M n := by
    rw [subgroupOfMap_def]
    refine (map_congr (ContinuousMonoidHom.ext fun w => ?_) ?_ n).trans
      (_root_.ContinuousCohomology.map_comp (X := ofDiscreteModule ℤ U M) κ
        (Subgroup.subgroupOfContinuousMulEquivOfLe hWV :
          (mackeySubgroup s U V).subgroupOf V →ₜ* mackeySubgroup s U V) f _ n)
    · simp [κ]
    · refine ofDiscreteModulePair_heq_of_hom_apply (MonoidHom.ext fun w => ?_) _ _ _
        fun m => ?_
      · simp [κ]
      · exact (TopRep.comp_apply ((TopRep.resFunctor _).map f) (ofDiscreteModulePair _ _ _)
          m).trans ((ofDiscreteModulePair_hom_apply _ _ _ _).trans (hf m))
  -- Conjugation moves the summand to the Shapiro map of the Mackey subgroup in `G`, transitivity
  -- of the Shapiro map passes to the Shapiro map of `V`, and naturality of the latter absorbs the
  -- trace from the Mackey subgroup to `V`.
  rw [mackeyTerm_def, hpair]
  simp only [← Category.assoc]
  rw [shapiroMap_comp_map_of_conj U (mackeySubgroup s U V) M s κ (fun w => hκ w) f hf
    mackeySubgroup_le_conj n, Category.assoc (coeffMap _ n),
    ← shapiroMap_trans V (mackeySubgroup s U V) hWV M n]
  simp only [Category.assoc, shapiroMap_comp_corestriction]
  rw [← shapiroMap_naturality V (DiscreteCoind V ((mackeySubgroup s U V).subgroupOf V) M)
    (DiscreteCoind.trace V ((mackeySubgroup s U V).subgroupOf V) M).toAddMonoidHom
    (fun v φ => _root_.map_smul (DiscreteCoind.trace V ((mackeySubgroup s U V).subgroupOf V) M)
      v φ) n]
  simp only [mackeyCoindMap, coeffMap_comp, Category.assoc]

omit [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- `mackeyCoindMap` sends `Φ` to `x ↦ ∑_{w} w • s • Φ (s⁻¹ w⁻¹ x)`, the sum over the canonical
transversal of the Mackey subgroup in `V`. -/
private theorem mackeyCoindMap_apply (s : G) (Φ : DiscreteCoind G U M) (x : G) :
    DFunLike.coe (F := DiscreteCoind G V M) ((mackeyCoindMap U V M s).hom Φ) x =
      ∑ w : V ⧸ (mackeySubgroup s U V).subgroupOf V,
        ((w.out : V) : G) • s • Φ (s⁻¹ * (((w.out : V) : G)⁻¹ * x)) := by
  let W' := (mackeySubgroup s U V).subgroupOf V
  let c := DiscreteCoind.conj U (mackeySubgroup s U V) M s mackeySubgroup_le_conj
  let t := DiscreteCoind.transIso (A := M) (U := V) (V := W') (W := mackeySubgroup s U V)
    (Subgroup.map_subgroupOf_eq_of_le mackeySubgroup_le_right)
    (Subgroup.subgroupOf_smul_eq V (mackeySubgroup s U V) M) isClosed_closure.isCompact
  let m := DiscreteCoind.map (DiscreteCoind.trace V W' M).toAddMonoidHom.toIntLinearMap
    (fun v φ => _root_.map_smul (DiscreteCoind.trace V W' M) v φ)
  let e := DiscreteCoind.transEquiv (A := M) (U := V) (V := W') (W := mackeySubgroup s U V)
    (Subgroup.map_subgroupOf_eq_of_le mackeySubgroup_le_right)
    (Subgroup.subgroupOf_smul_eq V (mackeySubgroup s U V) M) isClosed_closure.isCompact
  -- A composite of morphisms of `TopRep` evaluates as the composite of their underlying maps.
  have h : (mackeyCoindMap U V M s).hom Φ =
      (ofDiscreteModuleMap m.toAddMonoidHom.toIntLinearMap
          (fun g φ => DiscreteCoind.map_smul _ _ g φ)).hom
        (t.inv.hom ((ofDiscreteModuleMap c.toAddMonoidHom.toIntLinearMap
          (fun g Φ => _root_.map_smul c g Φ)).hom Φ)) :=
    rfl
  have h' : (mackeyCoindMap U V M s).hom Φ = m (e.symm (c Φ)) :=
    h.trans ((ofDiscreteModuleMap_hom_apply _ _ _).trans (congrArg m
      ((DiscreteCoind.transIso_inv_apply _ _ _ _).trans
        (congrArg e.symm (ofDiscreteModuleMap_hom_apply _ _ Φ)))))
  refine (congrArg (fun y : DiscreteCoind G V M => y x) h').trans ?_
  refine ((DiscreteCoind.map_apply _ _ _ x).trans (DiscreteCoind.trace_apply _)).trans
    (Finset.sum_congr rfl fun w _ => ?_)
  rw [DiscreteCoind.transEquiv_symm_apply]
  simp only [c, Subgroup.smul_def, Subgroup.coe_inv]
  exact congrArg (((w.out : V) : G) • ·) (DiscreteCoind.conj_apply s _ Φ _)

variable (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)

omit [TotallyDisconnectedSpace G] in
include hr in
/-- **The Mackey formula for coinduced modules**: the trace `Coind_U^G M → M` followed by the unit
`M → Coind_V^G M` is the sum of the maps `mackeyCoindMap` over the double cosets `V \ G / U`. -/
private theorem trace_comp_unit_eq_sum :
    letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
    ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
        (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) ≫
      ofDiscreteModuleMap (DiscreteCoind.unit G V M).toAddMonoidHom.toIntLinearMap
        (fun g m => _root_.map_smul (DiscreteCoind.unit G V M) g m) =
      ∑ D, mackeyCoindMap U V M (r D) := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  refine TopRep.hom_ext (DFunLike.ext _ _ fun (Φ : DiscreteCoind G U M) =>
    DiscreteCoind.ext fun x => ?_)
  -- Evaluation at `Φ` and then at `x` is additive in the morphism.
  let ev : (ofDiscreteModule ℤ G (DiscreteCoind G U M) ⟶
      ofDiscreteModule ℤ G (DiscreteCoind G V M)) →+ M :=
    AddMonoidHom.mk' (fun f => DFunLike.coe (F := DiscreteCoind G V M) (f.hom Φ) x)
      fun _ _ => rfl
  have hl : DFunLike.coe (F := DiscreteCoind G V M)
      ((ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
          (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) ≫
        ofDiscreteModuleMap (DiscreteCoind.unit G V M).toAddMonoidHom.toIntLinearMap
          (fun g m => _root_.map_smul (DiscreteCoind.unit G V M) g m)).hom Φ) x =
      DiscreteCoind.trace G U M (x • Φ) := by
    rw [_root_.map_smul]
    exact DiscreteCoind.unit_apply _ x
  refine hl.trans ((map_sum ev _ _).trans ?_).symm
  -- Compute the trace along the transversal adapted to the double cosets, and sort its terms.
  rw [DiscreteCoind.trace_eq_sum_transversal (U.mackeyTransversal V r hr)
      (U.mk_mackeyTransversal V r hr), sum_mackeyQuotientEquiv U V r hr]
  refine Finset.sum_congr rfl fun D _ => ?_
  refine (mackeyCoindMap_apply U V M (r D) Φ x).trans
    (Finset.sum_congr rfl fun w _ => ?_)
  rw [Subgroup.mackeyTransversal_mackeyQuotientEquiv, DiscreteCoind.coe_smul, mul_smul,
    mul_inv_rev, mul_assoc]

include hr in
/-- **The Mackey double-coset formula in every degree** (NSW (1.5.6)). For an open subgroup `U`
of finite index and a closed subgroup `V` of a profinite group `G`, and a discrete `G`-module `M`,
restriction to `V` of the corestriction from `U` is the sum over the double cosets `V \ G / U` of
the summands `cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res`, for any choice `r` of representatives `s = r D` of
the double cosets:

```text
res^G_V ∘ cor^G_U = ∑_{VsU ∈ V \ G / U} cor^V_{V ⊓ sUs⁻¹} ∘ (s)_* ∘ res^U_{U ⊓ s⁻¹Vs}.
```
-/
theorem corestriction_mackey (n : ℕ) :
    letI := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
    corestriction U M hU n ≫ res V (ofDiscreteModule ℤ G M) n =
      ∑ D, mackeyTerm U V M hU hV (r D) n := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  have := isIso_shapiroMap U (U.isClosed_of_isOpen hU) M n
  -- After the Shapiro isomorphism of `U`, both sides are coefficient maps followed by the Shapiro
  -- map of `V`, and the two coefficient maps agree by the Mackey formula for coinduced modules.
  -- The two sides are compared in term mode: their codomains `Hⁿ(V, res_V M)` and `Hⁿ(V, M)`
  -- agree only up to `res_ofDiscreteModule`, which stops `rw` from abstracting them.
  have hleft : shapiroMap U M n ≫ corestriction U M hU n ≫ res V (ofDiscreteModule ℤ G M) n =
      coeffMap (ofDiscreteModuleMap (DiscreteCoind.trace G U M).toAddMonoidHom.toIntLinearMap
          (fun g f => _root_.map_smul (DiscreteCoind.trace G U M) g f) ≫
        ofDiscreteModuleMap (DiscreteCoind.unit G V M).toAddMonoidHom.toIntLinearMap
          (fun g m => _root_.map_smul (DiscreteCoind.unit G V M) g m)) n ≫ shapiroMap V M n :=
    (shapiroMap_comp_corestriction_assoc U M hU n _).trans <| by
      rw [coeffMap_comp, Category.assoc]
      exact congrArg _ (coeffMap_unit_comp_shapiroMap V M n).symm
  have hright : shapiroMap U M n ≫ ∑ D, mackeyTerm U V M hU hV (r D) n =
      coeffMap (∑ D, mackeyCoindMap U V M (r D)) n ≫ shapiroMap V M n := by
    have hsum := (continuousCohomologyFunctor ℤ G n).map_sum
      (fun D => mackeyCoindMap U V M (r D)) Finset.univ
    simp only [continuousCohomologyFunctor_map] at hsum
    rw [Preadditive.comp_sum, hsum]
    exact (Finset.sum_congr rfl fun D _ =>
      shapiroMap_comp_mackeyTerm U V M hU hV (r D) n).trans (Preadditive.sum_comp _ _ _).symm
  exact (cancel_epi (shapiroMap U M n)).1 (hleft.trans ((congrArg (coeffMap · n ≫ _)
    (trace_comp_unit_eq_sum U V M r hr)).trans hright.symm))

/-- **Each summand of the Mackey formula depends only on the double coset** `VsU` of `s`, in
every degree. -/
theorem mackeyTerm_eq_of_mk_eq {s s' : G} (h : DoubleCoset.mk V U s = DoubleCoset.mk V U s')
    (n : ℕ) : mackeyTerm U V M hU hV s n = mackeyTerm U V M hU hV s' n := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  exact eq_of_sum_doubleCoset_rep_eq V U (fun s => mackeyTerm U V M hU hV s n)
    (fun r hr => (corestriction_mackey U V M hU hV r hr n).symm.trans
      (corestriction_mackey U V M hU hV Quotient.out DoubleCoset.out_eq' n)) h

end TauCeti.ContinuousCohomology
