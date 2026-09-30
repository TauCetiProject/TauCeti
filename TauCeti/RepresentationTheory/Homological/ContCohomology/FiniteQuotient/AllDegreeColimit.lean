/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.FilteredColimits
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Canonical
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.GroupAction.Discrete

/-!
# The finite-quotient colimit theorem in every degree

Let `G` be a compact group acting continuously on a discrete module `M`. In every degree `n`, the
canonical continuous cohomology `Hⁿ(G, M)` is the colimit of the cohomology groups
`Hⁿ(G ⧸ U, M^U)` of the finite quotients, over the open normal subgroups `U` of `G`:

```text
Hⁿ(G, M) = colim_U Hⁿ(G ⧸ U, M^U),
```

through the inflation-and-inclusion maps. This file proves that the named comparison cocone
`TauCeti.ContCohomology.continuousFiniteQuotientCocone` of
`TauCeti.ContCohomology.continuousFiniteQuotientSystem` is colimiting in `TopModuleCat ℤ`.

The argument is on Mathlib's homogeneous cochains, the invariant elements of the iterated function
spaces `C(G, C(G, …, M))`, and it is uniform in the degree. The map induced by the comparison pair
at `U` on these function spaces reads a function on `G ⧸ U` with values in `M^U` as a function on
`G` with values in `M`.

* **Descent of cochains.** Every element `F` of `C(G, C(G, …, M))` comes from the finite level `U`
  for every sufficiently small open normal `U`: a continuous map from the compact group `G` into a
  discrete space is uniformly locally constant and has finite image, and each of its finitely many
  values comes from a finite level by induction on the depth; in depth zero an element of `M` is
  fixed by an open normal subgroup. Since the map on function spaces is injective, the descended
  cochain of an invariant cochain is invariant, and the descended cochain of a cocycle is a
  cocycle.
* **Surjectivity.** Hence every cocycle of `G` is *itself* inflated from a finite level, with no
  coboundary subtracted, and every class of `Hⁿ(G, M)` comes from a finite level
  (`TauCeti.ContCohomology.exists_continuousFiniteQuotientComparisonApp_eq`).
* **Injectivity.** If a finite-level class `[z]` inflates to a coboundary `d b`, the primitive `b`
  descends to some deeper level `V`, where it is a primitive of the transition of `z`
  (`TauCeti.ContCohomology.exists_continuousFiniteQuotientTransition_eq_zero`).

Every term of the canonical complex of a compact group with discrete coefficients is discrete, so
`Hⁿ(G, M)` is a discrete topological module and the colimit statement in `TopModuleCat ℤ` reduces
to these two elementwise statements (`TauCeti.TopModuleCat.isColimitOfJointlySurjective`).

Of the profinite hypotheses only compactness of `G` is used, together with continuity of the
action; total disconnectedness of `G` is not needed.

## Main statements

* `TauCeti.ContCohomology.exists_continuousFiniteQuotientComparisonApp_eq`: every class of
  `Hⁿ(G, M)` is inflated from a finite level.
* `TauCeti.ContCohomology.exists_continuousFiniteQuotientTransition_eq_zero`: a finite-level class
  inflating to zero dies at some deeper finite level.
* `TauCeti.ContCohomology.continuousFiniteQuotientColimit`: the comparison cocone is colimiting.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Corollary 6.5.6(a).
* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.2, Proposition 8.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ContCohomology

open _root_.ContinuousCohomology TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]

/-! ### Cochains through the finite quotients -/

section Cochains

variable (G M) in
/-- The compatible pair of the comparison leg at `U`: the quotient map `G → G ⧸ U` together with
the inclusion `M^U → M`. -/
private noncomputable abbrev legPair (U : OpenNormalSubgroup G) :
    TopRep.res (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) ⟶
      ofDiscreteModule ℤ G M :=
  ofDiscreteModulePair (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
    (FixedPoints.addSubgroup U.toSubgroup M).subtype.toIntLinearMap
    (fun g m ↦ subtype_quotientMk_smul G M U.toSubgroup g m)

omit [IsTopologicalGroup G] in
/-- The comparison pair acts on underlying modules as the inclusion `M^U → M`. -/
private theorem legPair_hom_apply (U : OpenNormalSubgroup G)
    (m : FixedPoints.addSubgroup U.toSubgroup M) : (legPair G M U).hom m = (m : M) :=
  ofDiscreteModulePair_hom_apply _ _ _ m

/-- The comparison pair induces injective maps on the coinduced resolutions: the quotient map is
surjective and the inclusion of fixed points is injective. -/
private theorem legPair_resolutionMap_injective (U : OpenNormalSubgroup G) :
    ∀ i : ℕ, Function.Injective
      (resolutionMap (ContinuousMonoidHom.quotientMk U.toSubgroup) (legPair G M U) i).hom
  | 0 => fun a b h ↦ Subtype.ext <| (legPair_hom_apply U a).symm.trans (h.trans
      (legPair_hom_apply U b))
  | i + 1 => fun F F' h ↦ ContinuousMap.ext fun q ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact legPair_resolutionMap_injective U i (DFunLike.congr_fun h g)

/-- On the coinduced resolutions, the transition from the `U`-level to a deeper `V`-level followed
by the comparison map of the `V`-level is the comparison map of the `U`-level. -/
private theorem legPair_resolutionMap_transition {U V : OpenNormalSubgroup G} (hVU : V ≤ U) :
    ∀ (i : ℕ) (F : (TopRep.resolutionX (ofDiscreteModule ℤ (G ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M)) i).V),
      (resolutionMap (ContinuousMonoidHom.quotientMk V.toSubgroup) (legPair G M V) i).hom
          ((resolutionMap (continuousFiniteQuotientMap G hVU)
            (continuousFiniteQuotientPair G M hVU) i).hom F) =
        (resolutionMap (ContinuousMonoidHom.quotientMk U.toSubgroup) (legPair G M U) i).hom F
  | 0, m => by
    -- `change`: the level-zero maps are the coefficient pairs themselves, whose evaluation lemmas
    -- are stated on the pairs rather than on `resolutionMap _ _ 0`.
    change (legPair G M V).hom ((continuousFiniteQuotientPair G M hVU).hom m) =
      (legPair G M U).hom m
    exact (legPair_hom_apply V _).trans
      ((congrArg Subtype.val (continuousFiniteQuotientPair_hom_apply G M hVU m)).trans
        ((coe_fixedPointsInclusion hVU m).trans (legPair_hom_apply U m).symm))
  | i + 1, F => ContinuousMap.ext fun g ↦ by
    rw [resolutionMap_succ_apply, resolutionMap_succ_apply, resolutionMap_succ_apply]
    -- `G → G ⧸ V → G ⧸ U` is `G → G ⧸ U`
    have hg : continuousFiniteQuotientMap G hVU
        (ContinuousMonoidHom.quotientMk V.toSubgroup g) =
          ContinuousMonoidHom.quotientMk U.toSubgroup g :=
      continuousFiniteQuotientMap_mk G hVU g
    rw [hg]
    exact legPair_resolutionMap_transition hVU i _

variable [CompactSpace G] [ContinuousSMul G M]

/-- **Descent of the coinduced resolution to finite quotients.** For a compact group `G` and a
discrete module `M` with continuous action, every element `F` of the iterated function space
`C(G, C(G, …, M))` comes from `C(G ⧸ V, C(G ⧸ V, …, M^V))` for every sufficiently small open
normal subgroup `V`: it is `f ∘ F' ∘ π` for the quotient map `π : G → G ⧸ V` and the inclusion
`f : M^V → M`. -/
private theorem exists_openNormalSubgroup_resolutionMap_quotientMk_eq :
    ∀ (i : ℕ) (F : (TopRep.resolutionX (ofDiscreteModule ℤ G M) i).V),
      ∃ U : OpenNormalSubgroup G, ∀ V : OpenNormalSubgroup G, V ≤ U →
        ∃ F', (resolutionMap (ContinuousMonoidHom.quotientMk V.toSubgroup)
          (legPair G M V) i).hom F' = F
  | 0, m => by
    -- an element of `M` is fixed by an open normal subgroup
    obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq_self (G := G) (M := M) m
    exact ⟨U, fun V hVU ↦ ⟨⟨m, (FixedPoints.mem_addSubgroup V.toSubgroup M _).2
      fun v ↦ hU v (hVU v.2)⟩, legPair_hom_apply V _⟩⟩
  | i + 1, F => by
    let F' : C(G, (TopRep.resolutionX (ofDiscreteModule ℤ G M) i).V) := F
    -- the continuous map `F'` from the compact group `G` to a discrete space has finite image,
    -- each point of which descends below some open normal subgroup
    have : Finite (Set.range F') :=
      (isCompact_range F'.continuous).finite_of_discrete.to_subtype
    choose U hU using fun y : Set.range F' ↦
      exists_openNormalSubgroup_resolutionMap_quotientMk_eq i y.1
    -- and `F'` is invariant under right translation by an open subgroup
    have hstab : IsOpen (rightTranslationStabilizer F' : Set G) :=
      isOpen_rightTranslationStabilizer ((IsLocallyConstant.iff_continuous _).2 F'.continuous)
    obtain ⟨W, hW⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      (W := (rightTranslationStabilizer F' : Set G) ∩ ⋂ y, (U y : Set G))
      (IsClopen.inter ⟨(rightTranslationStabilizer F').isClosed_of_isOpen hstab, hstab⟩
        (isClopen_iInter_of_finite fun y ↦ (U y).toOpenSubgroup.isClopen))
      ⟨(rightTranslationStabilizer F').one_mem, Set.mem_iInter.2 fun y ↦ (U y).one_mem⟩
    refine ⟨W, fun V hVW ↦ ?_⟩
    have hV : ∀ v ∈ V, v ∈ rightTranslationStabilizer F' ∧ ∀ y, v ∈ U y := fun v hv ↦
      ⟨(hW (hVW hv)).1, fun y ↦ Set.mem_iInter.1 (hW (hVW hv)).2 y⟩
    -- descend the value at a representative of each coset of `V`
    have hlift (q : G ⧸ V.toSubgroup) := hU ⟨F' q.out, q.out, rfl⟩ V fun v hv ↦ (hV v hv).2 _
    refine ⟨⟨fun q ↦ (hlift q).choose, continuous_of_discreteTopology⟩,
      ContinuousMap.ext fun g ↦ ?_⟩
    rw [resolutionMap_succ_apply]
    refine ((hlift (g : G ⧸ V.toSubgroup)).choose_spec).trans ?_
    -- the representative of the coset of `g` is `g * v` with `v ∈ V`, and `F' (g * v) = F' g`
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V.toSubgroup g
    exact (congrArg F' hv).trans (mem_rightTranslationStabilizer.1 (hV v v.2).1 g)

/-- **Descent of homogeneous cochains to finite quotients.** Every homogeneous `n`-cochain of `G`
with values in `M` is the image of a homogeneous `n`-cochain of `G ⧸ V` with values in `M^V` for
every sufficiently small open normal subgroup `V`. -/
private theorem exists_openNormalSubgroup_cochainsMap_eq (n : ℕ)
    (F : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).X n) :
    ∃ U : OpenNormalSubgroup G, ∀ V : OpenNormalSubgroup G, V ≤ U →
      ∃ F', (cochainsMap (ContinuousMonoidHom.quotientMk V.toSubgroup)
        (legPair G M V)).f n F' = F := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_resolutionMap_quotientMk_eq (n + 1) F.1
  refine ⟨U, fun V hVU ↦ ?_⟩
  obtain ⟨F', hF'⟩ := hU V hVU
  -- the descended element is invariant, because the map it is sent along is injective and
  -- equivariant along the surjection `G → G ⧸ V`
  refine ⟨⟨F', fun q ↦ ?_⟩, Subtype.ext hF'⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  apply legPair_resolutionMap_injective V (n + 1)
  exact (TopRep.hom_comm_apply (resolutionMap (ContinuousMonoidHom.quotientMk V.toSubgroup)
    (legPair G M V) (n + 1)) g F').trans ((congrArg _ hF').trans (F.2 g) |>.trans hF'.symm)

end Cochains

/-! ### The cochain maps of the comparison and the transition -/

section CochainMaps

/-- The cochain map of the comparison pair is injective in every degree. -/
private theorem legPair_cochainsMap_f_injective (U : OpenNormalSubgroup G) (n : ℕ) :
    Function.Injective ((cochainsMap (ContinuousMonoidHom.quotientMk U.toSubgroup)
      (legPair G M U)).f n).hom := fun _ _ h ↦
  Subtype.ext (legPair_resolutionMap_injective U (n + 1) (congrArg Subtype.val h))

/-- On homogeneous cochains, the transition to a deeper level followed by the comparison of that
level is the comparison of the original level. -/
private theorem legPair_cochainsMap_f_transition {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (n : ℕ) (c : (TopRep.homogeneousCochains (ofDiscreteModule ℤ (G ⧸ U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M))).X n) :
    (cochainsMap (ContinuousMonoidHom.quotientMk V.toSubgroup) (legPair G M V)).f n
        ((cochainsMap (continuousFiniteQuotientMap G hVU)
          (continuousFiniteQuotientPair G M hVU)).f n c) =
      (cochainsMap (ContinuousMonoidHom.quotientMk U.toSubgroup) (legPair G M U)).f n c :=
  Subtype.ext (legPair_resolutionMap_transition hVU (n + 1) c.1)

end CochainMaps

/-! ### Surjectivity and injectivity -/

section Cohomology

variable [CompactSpace G] [ContinuousSMul G M]

/-- **Every class is inflated from a finite level.** For a compact group `G` and a discrete module
`M` with continuous action, every class of `Hⁿ(G, M)` is the image, under inflation along
`G → G ⧸ U` followed by the inclusion `M^U → M`, of a class of `Hⁿ(G ⧸ U, M^U)` for some open
normal subgroup `U`. This is the surjectivity half of the finite-quotient colimit theorem; a
representing cocycle is itself inflated, with no coboundary subtracted. -/
theorem exists_continuousFiniteQuotientComparisonApp_eq {n : ℕ}
    (x : continuousCohomology n (ofDiscreteModule ℤ G M)) :
    ∃ (U : OpenNormalSubgroup G) (y : continuousCohomology n
        (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))),
      (continuousFiniteQuotientComparisonApp G M U n).hom y = x := by
  set K := TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective n x
  -- descend a representing cocycle to a finite level
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_cochainsMap_eq n (K.iCycles n z)
  set KU := TopRep.homogeneousCochains
    (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
  obtain ⟨c, hc⟩ := hU U le_rfl
  -- the descended cochain is a cocycle, since its image is one and the cochain map is injective
  have hd : (KU.d n (n + 1)).hom c = 0 := by
    apply legPair_cochainsMap_f_injective U (n + 1)
    have h := ConcreteCategory.congr_hom
      ((cochainsMap (ContinuousMonoidHom.quotientMk U.toSubgroup) (legPair G M U)).comm n (n + 1)) c
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm.trans ((congrArg _ hc).trans
      ((K.d_iCycles_apply (n + 1) z).trans (map_zero _).symm))
  refine ⟨U, KU.homologyπ n (KU.cyclesMkOfEq c (n + 1) (CochainComplex.next ℕ n) hd), ?_⟩
  rw [continuousFiniteQuotientComparisonApp_eq_map, map_π_apply]
  refine congrArg (K.homologyπ n).hom (K.iCycles_injective n ?_)
  rw [iCycles_cocyclesMap_apply, KU.iCycles_cyclesMkOfEq]
  exact hc

/-- **A class inflating to zero dies at a deeper finite level.** For a compact group `G` and a
discrete module `M` with continuous action, a class of `Hⁿ(G ⧸ U, M^U)` whose image in `Hⁿ(G, M)`
vanishes already vanishes in `Hⁿ(G ⧸ V, M^V)` for some open normal subgroup `V ≤ U`. This is the
injectivity half of the finite-quotient colimit theorem. -/
theorem exists_continuousFiniteQuotientTransition_eq_zero {n : ℕ} (U : OpenNormalSubgroup G)
    (y : continuousCohomology n
      (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)))
    (hy : (continuousFiniteQuotientComparisonApp G M U n).hom y = 0) :
    ∃ (V : OpenNormalSubgroup G) (hVU : V ≤ U),
      (continuousFiniteQuotientTransition G M hVU n).hom y = 0 := by
  set K := TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)
  set KU := TopRep.homogeneousCochains
    (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
  obtain ⟨z, rfl⟩ := KU.homologyπ_surjective n y
  obtain ⟨m, hm⟩ : ∃ m, (ComplexShape.up ℕ).prev n = m := ⟨_, rfl⟩
  -- the inflated cocycle is the coboundary of some cochain `w`
  rw [continuousFiniteQuotientComparisonApp_eq_map, map_π_apply] at hy
  obtain ⟨w, hw⟩ := (K.homologyπ_eq_zero_iff n hm).1 hy
  -- which descends to a deeper finite level `V`
  obtain ⟨W, hW⟩ := exists_openNormalSubgroup_cochainsMap_eq m w
  set V := U ⊓ W
  set KV := TopRep.homogeneousCochains
    (ofDiscreteModule ℤ (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M))
  obtain ⟨w', hw'⟩ := hW V inf_le_right
  refine ⟨V, inf_le_left, ?_⟩
  rw [continuousFiniteQuotientTransition_eq_map, map_π_apply]
  -- there `w'` is a primitive of the transition of `z`, as both sides have the same image in `G`
  refine (KV.homologyπ_eq_zero_iff n hm).2 ⟨w', KV.iCycles_injective n ?_⟩
  rw [KV.iCycles_toCycles_apply, iCycles_cocyclesMap_apply]
  apply legPair_cochainsMap_f_injective V n
  have h := ConcreteCategory.congr_hom
    ((cochainsMap (ContinuousMonoidHom.quotientMk V.toSubgroup) (legPair G M V)).comm m n) w'
  simp only [ConcreteCategory.comp_apply] at h
  exact h.symm.trans ((congrArg _ hw').trans ((K.iCycles_toCycles_apply m w).symm.trans
    ((congrArg _ hw).trans ((iCycles_cocyclesMap_apply _ _ n z).trans
      (legPair_cochainsMap_f_transition inf_le_left n _).symm))))

/-- Two finite-level classes with the same image in `Hⁿ(G, M)` agree after transition to a common
deeper finite level. -/
private theorem exists_continuousFiniteQuotientTransition_eq {n : ℕ} {U U' : OpenNormalSubgroup G}
    (y : continuousCohomology n
      (ofDiscreteModule ℤ (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)))
    (y' : continuousCohomology n
      (ofDiscreteModule ℤ (G ⧸ U'.toSubgroup) (FixedPoints.addSubgroup U'.toSubgroup M)))
    (h : (continuousFiniteQuotientComparisonApp G M U n).hom y =
      (continuousFiniteQuotientComparisonApp G M U' n).hom y') :
    ∃ (V : OpenNormalSubgroup G) (hVU : V ≤ U) (hVU' : V ≤ U'),
      (continuousFiniteQuotientTransition G M hVU n).hom y =
        (continuousFiniteQuotientTransition G M hVU' n).hom y' := by
  set W := U ⊓ U'
  -- the difference of the two transitions to `W` inflates to zero
  obtain ⟨V, hVW, hV⟩ := exists_continuousFiniteQuotientTransition_eq_zero W
    ((continuousFiniteQuotientTransition G M (inf_le_left : W ≤ U) n).hom y -
      (continuousFiniteQuotientTransition G M (inf_le_right : W ≤ U') n).hom y') (by
      rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        continuousFiniteQuotientTransition_comp_comparisonApp,
        continuousFiniteQuotientTransition_comp_comparisonApp, h, sub_self])
  refine ⟨V, hVW.trans inf_le_left, hVW.trans inf_le_right, ?_⟩
  rw [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← continuousFiniteQuotientTransition_comp, ← continuousFiniteQuotientTransition_comp] at hV
  exact hV

end Cohomology

/-! ### The colimit theorem -/

section Colimit

/-- The leg of the comparison cocone at `U`, read through the identifications of its source and
target, is the comparison map of the `U`-level. -/
private theorem continuousFiniteQuotientCocone_ι_app_apply (n : ℕ) (U : OpenNormalSubgroup G)
    (y : (continuousFiniteQuotientSystem G M n).obj (Opposite.op U)) :
    (eqToHom (continuousFiniteQuotientCocone_pt G M n)).hom
        (((continuousFiniteQuotientCocone G M n).ι.app (Opposite.op U)).hom y) =
      (continuousFiniteQuotientComparisonApp G M U n).hom
        ((eqToHom (continuousFiniteQuotientSystem_obj G M n U)).hom y) := by
  rw [← continuousFiniteQuotientCocone_ι_app G M n U]
  simp only [ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply (eqToHom _) (eqToHom _), eqToHom_trans, eqToHom_refl,
    ConcreteCategory.id_apply]

/-- An arrow of the system, read through the identifications of its source and target, is the
transition between the two levels. -/
private theorem continuousFiniteQuotientSystem_map_apply (n : ℕ) {U V : OpenNormalSubgroup G}
    (hVU : V ≤ U) (y : (continuousFiniteQuotientSystem G M n).obj (Opposite.op U)) :
    (eqToHom (continuousFiniteQuotientSystem_obj G M n V)).hom
        (((continuousFiniteQuotientSystem G M n).map (homOfLE hVU).op).hom y) =
      (continuousFiniteQuotientTransition G M hVU n).hom
        ((eqToHom (continuousFiniteQuotientSystem_obj G M n U)).hom y) := by
  rw [← continuousFiniteQuotientSystem_map G M n (homOfLE hVU).op]
  simp only [ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply (eqToHom _) (eqToHom _), eqToHom_trans, eqToHom_refl,
    ConcreteCategory.id_apply]

variable [CompactSpace G] [ContinuousSMul G M]

variable (G M) in
/-- **The finite-quotient colimit theorem in every degree.** For a compact group `G` and a discrete
module `M` with continuous action, the inflation-and-inclusion cocone exhibits the canonical
continuous cohomology `Hⁿ(G, M)` as the colimit, in `TopModuleCat ℤ`, of the cohomology groups
`Hⁿ(G ⧸ U, M^U)` of the finite quotients over the open normal subgroups `U` of `G`. -/
noncomputable def continuousFiniteQuotientColimit (n : ℕ) :
    IsColimit (continuousFiniteQuotientCocone G M n) := by
  have : DiscreteTopology (continuousFiniteQuotientCocone G M n).pt := by
    rw [continuousFiniteQuotientCocone_pt]
    infer_instance
  refine TopModuleCat.isColimitOfJointlySurjective (continuousFiniteQuotientCocone G M n)
    (fun x ↦ ?_) fun i j yi yj h ↦ ?_
  · obtain ⟨U, y, hy⟩ := exists_continuousFiniteQuotientComparisonApp_eq
      ((eqToHom (continuousFiniteQuotientCocone_pt G M n)).hom x)
    obtain ⟨y', rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (eqToHom (continuousFiniteQuotientSystem_obj G M n U))).2 y
    refine ⟨Opposite.op U, y', (ConcreteCategory.bijective_of_isIso
      (eqToHom (continuousFiniteQuotientCocone_pt G M n))).1 ?_⟩
    rw [continuousFiniteQuotientCocone_ι_app_apply, hy]
  · obtain ⟨V, hVi, hVj, hV⟩ := exists_continuousFiniteQuotientTransition_eq
      ((eqToHom (continuousFiniteQuotientSystem_obj G M n i.unop)).hom yi)
      ((eqToHom (continuousFiniteQuotientSystem_obj G M n j.unop)).hom yj) (by
        rw [← continuousFiniteQuotientCocone_ι_app_apply,
          ← continuousFiniteQuotientCocone_ι_app_apply]
        exact congrArg _ h)
    refine ⟨Opposite.op V, (homOfLE hVi).op, (homOfLE hVj).op, (ConcreteCategory.bijective_of_isIso
      (eqToHom (continuousFiniteQuotientSystem_obj G M n V))).1 ?_⟩
    rw [continuousFiniteQuotientSystem_map_apply, continuousFiniteQuotientSystem_map_apply, hV]

end Colimit

end TauCeti.ContCohomology
