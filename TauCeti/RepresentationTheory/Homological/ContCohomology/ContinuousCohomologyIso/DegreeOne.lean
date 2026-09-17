/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CochainComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The explicit `H¹` against the canonical continuous cohomology

The explicit low-degree model presents `H¹(G, M)` as the quotient of the continuous
one-cocycles `Z¹(G, M)` by the coboundaries `B¹(G, M)`, while the canonical object is Mathlib's
`continuousCohomology 1 X` for `X` a topological representation. This file identifies the two
in degree one, for `X` the image `ofDiscreteModule ℤ G M` of a discrete module `M` under the
coefficient dictionary, as an isomorphism of topological `ℤ`-modules.

The comparison descends the cochain comparison of `CochainComparison.lean`, which identifies
inhomogeneous cochains with the canonical homogeneous cochains and carries `d1` to the canonical
differential. On cocycles it is the concrete kernel, by `cocycleEquiv1Ker`; explicit coboundaries
correspond to the image of `toCycles 0 1`, by `Z1AddEquivContinuousCocycles_d0`. The class map
`canonicalH1pi` sends an inhomogeneous cocycle to its canonical cohomology class; it is
surjective (`canonicalH1pi_surjective`) and its kernel is exactly `B¹`
(`canonicalH1pi_eq_zero_iff`), which descends it to the comparison
`explicitH1IsoContinuousCohomology` between the explicit quotient and the canonical object.

The additive comparison requires local compactness, used by the degree-two cochain comparison.
For compact groups, the canonical side is discrete by `CompactDiscrete.lean`. The topological
comparison therefore uses `DiscreteH1`, the explicit quotient equipped with the discrete
topology, rather than the quotient topology inherited from pointwise cochains. This lets one
transport explicit cocycle computations into canonical continuous cohomology.

The comparison is natural in compatible pairs (`explicitH1Iso_map`); restriction and
coefficient maps are recorded as `explicitH1Iso_res` and `explicitH1Iso_coeffMap`.

The formulas follow Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed.,
Chapter I §2, as in `CochainComparison.lean`.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology
universe u

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

section LocallyCompact

variable [LocallyCompactSpace G]

/-- Inhomogeneous one-cocycles identify with the kernel of the canonical differential. -/
private def cocycleEquiv1Ker : Z1 G M ≃+
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom.ker where
  toFun z := ⟨cochainEquiv1 G M ⟨z.val, Z1_le_C1 G M z.property⟩, by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      d_cochainEquiv1]
    have hz : d1 G M z.val = 0 := d1_apply_eq_zero_iff.2 (mem_Z1_iff.1 z.property).2
    simp only [hz]
    exact (cochainEquiv2 G M).map_zero⟩
  invFun z := ⟨((cochainEquiv1 G M).symm z.val).val, by
    apply mem_Z1_iff.2
    refine ⟨mem_C1_iff.1 ((cochainEquiv1 G M).symm z.val).property,
      d1_apply_eq_zero_iff.1 ?_⟩
    have h := cochainEquiv2_symm_d G M z.val
    have hz :
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).d 1 2).hom z.val = 0 := z.property
    rw [hz, map_zero] at h
    exact (congrArg Subtype.val h).symm⟩
  left_inv z := by simp
  right_inv z := by apply Subtype.ext; simp
  map_add' z w := by
    apply Subtype.ext
    exact (cochainEquiv1 G M).map_add
      (⟨z.val, Z1_le_C1 G M z.property⟩ : C1 G M)
      (⟨w.val, Z1_le_C1 G M w.property⟩ : C1 G M)

/-- Continuous one-cocycles in inhomogeneous and canonical coordinates. -/
noncomputable def Z1AddEquivContinuousCocycles :
    Z1 G M ≃+ _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1 :=
  (cocycleEquiv1Ker G M).trans
    ((TopModuleCat.isLimitKer _).conePointUniqueUpToIso
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).cyclesIsKernel 1 2
        (by simp))).toContinuousLinearEquiv.toAddEquiv

/-- The canonical inclusion of the corresponding cocycle is the homogeneous cochain. -/
@[simp]
theorem iCycles_Z1AddEquivContinuousCocycles (z : Z1 G M) :
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).sc 1).iCycles.hom
        (Z1AddEquivContinuousCocycles G M z) =
      cochainEquiv1 G M ⟨z.val, Z1_le_C1 G M z.property⟩ := by
  exact ConcreteCategory.congr_hom
    (CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
      (TopModuleCat.isLimitKer _)
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).cyclesIsKernel 1 2 (by simp))
      CategoryTheory.Limits.WalkingParallelPair.zero) (cocycleEquiv1Ker G M z)

/-- Send a continuous one-cocycle to its canonical cohomology class. -/
noncomputable def canonicalH1pi : Z1 G M →+
    continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  ((_root_.ContinuousCohomology.π (ofDiscreteModule ℤ G M) 1).hom.toAddMonoidHom).comp
    (Z1AddEquivContinuousCocycles G M).toAddMonoidHom

/-- The class map applies the canonical quotient projection to the corresponding cocycle. -/
theorem canonicalH1pi_apply (z : Z1 G M) :
    canonicalH1pi G M z =
      (_root_.ContinuousCohomology.π (ofDiscreteModule ℤ G M) 1)
        (Z1AddEquivContinuousCocycles G M z) := by
  rfl

/-- The cocycle comparison sends explicit coboundaries to canonical boundaries. -/
theorem Z1AddEquivContinuousCocycles_d0 (m : M) :
    Z1AddEquivContinuousCocycles G M
      ⟨d0 G M m, B1_le_Z1 G M (d0_mem_B1 m)⟩ =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles 0 1).hom
        (cochainEquiv0 G M m) := by
  apply CategoryTheory.ShortComplex.topModuleCat_iCycles_injective
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).sc 1)
  rw [iCycles_Z1AddEquivContinuousCocycles]
  have h := DFunLike.congr_fun
    (congrArg TopModuleCat.Hom.hom
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).toCycles_i 0 1))
    (cochainEquiv0 G M m)
  exact (d_cochainEquiv0 G M m).symm.trans h.symm

section Descent

/-- The class map kills exactly the explicit coboundaries. -/
theorem canonicalH1pi_eq_zero_iff (z : Z1 G M) :
    canonicalH1pi G M z = 0 ↔ (z : G → M) ∈ B1 G M := by
  have hz := HomologicalComplex.topModuleCat_homologyπ_eq_zero_iff
    (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)) 0 1 (by simp)
      (Z1AddEquivContinuousCocycles G M z)
  constructor
  · intro h
    obtain ⟨u, hu⟩ := hz.1 h
    have h1 : Z1AddEquivContinuousCocycles G M
        ⟨d0 G M ((cochainEquiv0 G M).symm u), B1_le_Z1 G M (d0_mem_B1 _)⟩ =
        Z1AddEquivContinuousCocycles G M z :=
      (Z1AddEquivContinuousCocycles_d0 G M _).trans
        ((congrArg _ ((cochainEquiv0 G M).apply_symm_apply u)).trans hu)
    have hsub : ((⟨d0 G M ((cochainEquiv0 G M).symm u),
        B1_le_Z1 G M (d0_mem_B1 _)⟩ : Z1 G M) : G → M) = (z : G → M) :=
      congrArg Subtype.val ((Z1AddEquivContinuousCocycles G M).injective h1)
    rw [mem_B1_iff]
    exact ⟨_, fun g => (d0_apply (G := G) (M := M) _ g).symm.trans (congrFun hsub g)⟩
  · intro h
    obtain ⟨m, hm⟩ := mem_B1_iff.1 h
    have hm' : d0 G M m = (z : G → M) := funext fun g =>
      (d0_apply (G := G) (M := M) m g).trans (hm g)
    refine hz.2 ⟨cochainEquiv0 G M m, ?_⟩
    have hzEq : Z1AddEquivContinuousCocycles G M z =
        Z1AddEquivContinuousCocycles G M
          ⟨d0 G M m, B1_le_Z1 G M (d0_mem_B1 m)⟩ :=
      congrArg _ (Subtype.ext hm'.symm)
    rw [hzEq, Z1AddEquivContinuousCocycles_d0]

/-- Every canonical degree-one class has an inhomogeneous representative. -/
theorem canonicalH1pi_surjective : Function.Surjective (canonicalH1pi G M) :=
  (HomologicalComplex.topModuleCat_homologyπ_surjective
    (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)) 1).comp
      (Z1AddEquivContinuousCocycles G M).surjective

/-- The comparison of the explicit `H¹` with the canonical object, on the underlying groups:
it sends the class of a cocycle to its canonical class. -/
noncomputable def explicitH1AddEquivContinuousCohomology :
    H1 G M ≃+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.liftEquiv ((B1 G M).addSubgroupOf (Z1 G M))
    (canonicalH1pi_surjective G M) (by
      ext z
      exact (canonicalH1pi_eq_zero_iff G M z).symm)

/-- The comparison sends the class of a cocycle to its canonical class. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_mk (z : Z1 G M) :
    explicitH1AddEquivContinuousCohomology G M (z : H1 G M) = canonicalH1pi G M z := by
  rfl

end Descent

end LocallyCompact

section Compact

variable [CompactSpace G]

-- Unfold the coefficient dictionary's carrier for typeclass search.
local instance : DiscreteTopology (ofDiscreteModule ℤ G M).V :=
  show DiscreteTopology M from inferInstance

/-- The comparison as an isomorphism of topological `ℤ`-modules, using the discrete
carrier `DiscreteH1` for the explicit quotient. -/
noncomputable def explicitH1IsoContinuousCohomology :
    TopModuleCat.of ℤ (DiscreteH1 G M) ≅
      continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso
    { ((discreteH1Equiv G M).trans
        (explicitH1AddEquivContinuousCohomology G M)).toIntLinearEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The comparison sends an explicit cocycle class to its canonical class. -/
@[simp]
theorem explicitH1IsoContinuousCohomology_hom_apply (z : Z1 G M) :
    ((explicitH1IsoContinuousCohomology G M).hom :
        TopModuleCat.of ℤ (DiscreteH1 G M) ⟶
          continuousCohomology 1 (ofDiscreteModule ℤ G M))
      ((discreteH1Equiv G M).symm (H1pi G M z)) = canonicalH1pi G M z := by
  -- Unfold the categorical packaging, then cancel the change of carrier.
  change explicitH1AddEquivContinuousCohomology G M
    ((discreteH1Equiv G M) ((discreteH1Equiv G M).symm (H1pi G M z))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end Compact

section Naturality

variable [LocallyCompactSpace G]

section CompatiblePairs

variable (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction H N] [ContinuousSMul H N] [LocallyCompactSpace H]
  (φ : H →ₜ* G) (f : M →+ N)
  (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)

/-- The comparison of one-cocycles is natural in compatible pairs. -/
theorem Z1AddEquivContinuousCocycles_naturality (z : Z1 G M) :
    _root_.ContinuousCohomology.cocyclesMap φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)) 1
        (Z1AddEquivContinuousCocycles G M z) =
      Z1AddEquivContinuousCocycles H N
        (cocyclesMap1 G M H N φ f continuous_of_discreteTopology hf z) := by
  apply CategoryTheory.ShortComplex.topModuleCat_iCycles_injective
    ((TopRep.homogeneousCochains (ofDiscreteModule ℤ H N)).sc 1)
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (_root_.ContinuousCohomology.cochainsMap φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m))) 1)
    (Z1AddEquivContinuousCocycles G M z)
  simp only [ConcreteCategory.comp_apply] at hi
  refine hi.trans ((congrArg
    ((_root_.ContinuousCohomology.cochainsMap φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m))).f 1)
    (iCycles_Z1AddEquivContinuousCocycles G M z)).trans ?_)
  rw [iCycles_Z1AddEquivContinuousCocycles]
  refine (cochainEquiv1_naturality G M H N φ f hf
    ⟨z.val, Z1_le_C1 G M z.property⟩).trans ?_
  apply congrArg (cochainEquiv1 H N)
  exact Subtype.ext (cocyclesMap1_coe G M H N φ f
    continuous_of_discreteTopology hf z).symm

/-- Passing an explicit cocycle to its canonical class commutes with compatible-pair maps. -/
theorem canonicalH1pi_naturality (z : Z1 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)) 1
        (canonicalH1pi G M z) =
      canonicalH1pi H N (cocyclesMap1 G M H N φ f continuous_of_discreteTopology hf z) := by
  have hp := ConcreteCategory.congr_hom
    (_root_.ContinuousCohomology.π_map φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)) 1)
    (Z1AddEquivContinuousCocycles G M z)
  simp only [ConcreteCategory.comp_apply] at hp
  simpa only [canonicalH1pi_apply,
    Z1AddEquivContinuousCocycles_naturality G M H N φ f hf] using hp

variable [CompactSpace G] [CompactSpace H]

omit [LocallyCompactSpace G] [LocallyCompactSpace H] in
/-- The degree-one comparison carries explicit compatible-pair pullbacks to canonical maps. -/
theorem explicitH1Iso_map (x : H1 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)) 1
        ((explicitH1IsoContinuousCohomology G M).hom ((discreteH1Equiv G M).symm x)) =
      (explicitH1IsoContinuousCohomology H N).hom
        ((discreteH1Equiv H N).symm
          (explicitMap1 G M H N φ f continuous_of_discreteTopology hf x)) := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitMap1_mk]
    simpa only [H1pi, QuotientAddGroup.mk'_apply] using
      (congrArg (_root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap (fun h m ↦ hf h m)) 1)
        (explicitH1IsoContinuousCohomology_hom_apply G M z)).trans
          ((canonicalH1pi_naturality G M H N φ f hf z).trans
            (explicitH1IsoContinuousCohomology_hom_apply H N
              (cocyclesMap1 G M H N φ f continuous_of_discreteTopology hf z)).symm)

end CompatiblePairs

variable [CompactSpace G]
omit [LocallyCompactSpace G]

/-- The degree-one comparison carries explicit restriction to canonical restriction.
The subgroup is assumed compact so that its canonical cohomology is discrete. -/
theorem explicitH1Iso_res (S : Subgroup G) [CompactSpace S] (x : H1 G M) :
    TauCeti.ContinuousCohomology.res S (ofDiscreteModule ℤ G M) 1
        ((explicitH1IsoContinuousCohomology G M).hom ((discreteH1Equiv G M).symm x)) =
      (explicitH1IsoContinuousCohomology S M).hom
        ((discreteH1Equiv S M).symm (explicitRes1 G M S x)) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype S : S →* G)
      (AddMonoidHom.id M).toIntLinearMap (id_subgroupSubtype_smul G M S) =
      𝟙 (TopRep.res (S.subtype : S →* G) (ofDiscreteModule ℤ G M)) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ => rfl
  rw [TauCeti.ContinuousCohomology.res_def, ← hpair]
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitRes1_mk]
    have h := explicitH1Iso_map G M S M (ContinuousMonoidHom.subgroupSubtype S)
      (AddMonoidHom.id M) (id_subgroupSubtype_smul G M S) (z : H1 G M)
    rwa [explicitMap1_mk] at h

/-- The degree-one comparison carries explicit coefficient maps to canonical coefficient maps. -/
theorem explicitH1Iso_coeffMap (N : Type u) [AddCommGroup N] [TopologicalSpace N]
    [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
    (f : M →+[G] N) (x : H1 G M) :
    TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m => map_smul f g m) 1
        ((explicitH1IsoContinuousCohomology G M).hom ((discreteH1Equiv G M).symm x)) =
      (explicitH1IsoContinuousCohomology G N).hom
        ((discreteH1Equiv G N).symm (explicitCoeff1 G M f continuous_of_discreteTopology x)) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      f.toAddMonoidHom.toIntLinearMap (fun g m => map_smul f g m) =
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap (fun g m => map_smul f g m) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ => rfl
  rw [TauCeti.ContinuousCohomology.coeffMap_def, ← hpair]
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitCoeff1_mk]
    have h := explicitH1Iso_map G M G N (ContinuousMonoidHom.id G) f.toAddMonoidHom
      (fun g m => map_smul f g m) (z : H1 G M)
    exact h.trans (congrArg
      (fun y => (explicitH1IsoContinuousCohomology G N).hom ((discreteH1Equiv G N).symm y))
      (explicitMap1_mk G M G N (ContinuousMonoidHom.id G) f.toAddMonoidHom
        continuous_of_discreteTopology (fun g m => map_smul f g m) z))

end Naturality

end TauCeti.ContCohomology
