/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CocycleComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars

/-!
# The explicit model against the canonical object, in degrees one and two

The explicit low-degree complex presents `H¹(G, M)` and `H²(G, M)` as `Z¹/B¹` and `Z²/B²`, honest
subquotients of the continuous functions on `G` and on `G × G`, while the canonical object is
Mathlib's `continuousCohomology n X` for `X` the image `TauCeti.ofDiscreteModule ℤ G M` of `M`
under the coefficient dictionary. This file identifies the two in degrees one and two.

The passage happens one level at a time. `CochainComparison.lean` identifies the inhomogeneous
cochains with the canonical homogeneous ones, and `CocycleComparison.lean` cuts that down to the
cocycles in degrees one and two. What remains, and is the content of this file, is the passage from
cocycles to classes: the
canonical homology is the cokernel of `HomologicalComplex.toCycles`, so a cocycle has trivial
canonical class exactly when it is a canonical boundary, and
`TauCeti.ContCohomology.mem_B1_iff_cocycleEquiv1_mem_range` together with its landed degree-two
counterpart says that those are precisely the explicit coboundaries.

The comparison is stated twice, and the two statements are not interchangeable. The additive
equivalence holds over an arbitrary topological group in degree one, and over a locally compact one
in degree two, the local compactness being what supplies `ContinuousMap.uncurry` for the degree-two
cochain comparison. The isomorphism in `TopModuleCat ℤ` needs `G` compact, and its source is the
**discrete** carrier `TauCeti.ContCohomology.DiscreteH1`, not the quotient topology that `H¹`
inherits from the pointwise topology on `G → M`: that inherited topology is not discrete in
general, so discreteness cannot be assumed, whereas the canonical side is discrete by
`TauCeti.discreteTopology_continuousCohomology`. A comparison stated in `TopModuleCat ℤ` against
the inherited topology would be false while its underlying additive statement stayed true, which
is why the discrete synonyms exist.

## Main definitions

* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` and
  `explicitH2AddEquivContinuousCohomology`: the comparisons as additive equivalences.
* `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` and
  `explicitH2IsoContinuousCohomology`: the comparisons as isomorphisms in `TopModuleCat ℤ`.
* `TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and
  `TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`: the comparisons for the carrier of a
  discrete smooth representation over any scalars, obtained from the `ℤ`-comparisons by restricting
  scalars.

## Main results

* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_apply` and
  `explicitH2AddEquivContinuousCohomology_apply`: the comparisons send the class of an explicit
  cocycle to the homology class of the cocycle it corresponds to.
* `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_map` and
  `explicitH1AddEquivContinuousCohomology_coeffMap`: the degree-one comparison carries the
  explicit pullback along a compatible pair, and in particular the explicit coefficient map, to the
  canonical one.
* `TauCeti.ContCohomology.explicitIso_map`: the same naturality in compatible pairs for the
  degree-one comparison in `TopModuleCat ℤ`, with `explicitIso_res` and `explicitIso_coeffMap` as
  its restriction and coefficient-map specializations.
* `TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_map` and
  `explicitH2AddEquivContinuousCohomology_coeffMap`: the degree-two comparison carries the explicit
  pullback along a compatible pair, and in particular the explicit coefficient map, to the
  canonical one; `TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_map` is the same
  naturality for discrete representations over any scalars.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  identification of the inhomogeneous description of continuous cohomology with the homogeneous
  one. The isomorphisms built here are the degree-one and degree-two cases.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

/-- An additive equivalence followed by transport between equal `TopModuleCat` objects preserves
nonzero elements. This applies to the explicit-to-canonical cohomology comparison. -/
theorem addEquiv_eqToHom_ne_zero {A : Type*} [AddCommGroup A]
    {B C : TopModuleCat ℤ} (e : B = C) (f : A ≃+ B) (x : A) (hx : x ≠ 0) :
    (eqToHom e).hom (f x) ≠ 0 := by
  have hinj : Function.Injective (eqToHom e).hom :=
    Function.LeftInverse.injective ((eqToIso e).hom_inv_id_apply)
  have hzero : (eqToHom e).hom (0 : B) = 0 := by
    cases e
    rfl
  intro h
  apply hx
  apply f.injective
  exact (hinj (h.trans hzero.symm)).trans f.map_zero.symm

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The canonical homology class of a continuous one-cocycle. -/
private noncomputable def cohomologyClass1 :
    Z1 G M →+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ
      1).hom.toLinearMap.toAddMonoidHom.comp (cocycleEquiv1 G M).toAddMonoidHom

private theorem cohomologyClass1_eq_zero_iff (c : Z1 G M) :
    cohomologyClass1 G M c = 0 ↔ (c : G → M) ∈ B1 G M := by
  rw [mem_B1_iff_cocycleEquiv1_mem_range]
  exact HomologicalComplex.homologyπ_eq_zero_iff _ 1 (by simp)

private theorem cohomologyClass1_surjective : Function.Surjective (cohomologyClass1 G M) := by
  intro y
  obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 1 y
  refine ⟨(cocycleEquiv1 G M).symm x, ?_⟩
  simpa [cohomologyClass1] using hx

private theorem cohomologyClass1_ker :
    (B1 G M).addSubgroupOf (Z1 G M) = (cohomologyClass1 G M).ker := by
  ext c
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, cohomologyClass1_eq_zero_iff]

/-- The explicit `H¹(G, M)` is Mathlib's `continuousCohomology 1` of the canonical object attached
to `M`, as an additive equivalence.

No hypothesis on `G` beyond being a topological group is used: the cochain comparison in degree one
is a currying with no local-compactness condition, and passing to a subquotient needs none either.
The companion `TauCeti.ContCohomology.explicitH1IsoContinuousCohomology` upgrades this to
`TopModuleCat ℤ`, and that upgrade does need `G` compact. -/
noncomputable def explicitH1AddEquivContinuousCohomology :
    H1 G M ≃+ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.liftEquiv _ (cohomologyClass1_surjective G M) (cohomologyClass1_ker G M)

/-- The comparison sends the class of a continuous one-cocycle to the canonical homology class of
the cocycle it corresponds to. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_apply (c : Z1 G M) :
    explicitH1AddEquivContinuousCohomology G M (c : H1 G M) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1
        (cocycleEquiv1 G M c) := by
  exact QuotientAddGroup.liftEquiv_coe _ _ _ c

/-- The inverse comparison sends a canonical homology class to the explicit class of the
corresponding inhomogeneous cocycle. -/
@[simp]
theorem explicitH1AddEquivContinuousCohomology_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1) :
    (explicitH1AddEquivContinuousCohomology G M).symm
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1 c) =
      (((cocycleEquiv1 G M).symm c : Z1 G M) : H1 G M) := by
  apply (explicitH1AddEquivContinuousCohomology G M).injective
  rw [AddEquiv.apply_symm_apply, explicitH1AddEquivContinuousCohomology_apply,
    AddEquiv.apply_symm_apply]

/-- **Naturality of the degree-one comparison.** The comparison carries the explicit
pullback along a compatible pair to Mathlib's canonical continuous-cohomology map along the same
pair. Restriction and coefficient maps below are specializations of this square. -/
theorem explicitH1AddEquivContinuousCohomology_map
    (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction H N] [ContinuousSMul H N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : H1 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 1
        (explicitH1AddEquivContinuousCohomology G M x) =
      explicitH1AddEquivContinuousCohomology H N
        (explicitMap1 G M H N φ f continuous_of_discreteTopology hf x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitMap1_mk, explicitH1AddEquivContinuousCohomology_apply,
      explicitH1AddEquivContinuousCohomology_apply, ← cocycleEquiv1_naturality]
    exact congr($(_root_.ContinuousCohomology.π_map φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 1)
      (cocycleEquiv1 G M c))

/-- The degree-one comparison carries the explicit coefficient map to the canonical coefficient
map `TauCeti.ContinuousCohomology.coeffMap` attached to the same equivariant homomorphism, the
degree-one counterpart of `TauCeti.ContCohomology.explicitH0Iso_coeffMap`. -/
theorem explicitH1AddEquivContinuousCohomology_coeffMap
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N) (x : H1 G M) :
    TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m) 1
        (explicitH1AddEquivContinuousCohomology G M x) =
      explicitH1AddEquivContinuousCohomology G N
        (explicitCoeff1 G M f continuous_of_discreteTopology x) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      f.toAddMonoidHom.toIntLinearMap (fun g m ↦ map_smul f g m) =
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [TauCeti.ContinuousCohomology.coeffMap_def, explicitCoeff1_eq_explicitMap1, ← hpair]
  exact explicitH1AddEquivContinuousCohomology_map G M G N (ContinuousMonoidHom.id G)
    f.toAddMonoidHom (fun g m ↦ map_smul f g m) x

/-! ### Degree two -/

section LocallyCompact

variable [LocallyCompactSpace G]

/-- The canonical homology class of a continuous two-cocycle. -/
private noncomputable def cohomologyClass2 :
    Z2 G M →+ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ
      2).hom.toLinearMap.toAddMonoidHom.comp (cocycleEquiv2 G M).toAddMonoidHom

private theorem cohomologyClass2_eq_zero_iff (c : Z2 G M) :
    cohomologyClass2 G M c = 0 ↔ (c : G × G → M) ∈ B2 G M := by
  rw [mem_B2_iff_cocycleEquiv2_mem_range]
  exact HomologicalComplex.homologyπ_eq_zero_iff _ 2 (by simp)

private theorem cohomologyClass2_surjective : Function.Surjective (cohomologyClass2 G M) := by
  intro y
  obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 2 y
  refine ⟨(cocycleEquiv2 G M).symm x, ?_⟩
  simpa [cohomologyClass2] using hx

private theorem cohomologyClass2_ker :
    (B2 G M).addSubgroupOf (Z2 G M) = (cohomologyClass2 G M).ker := by
  ext c
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, cohomologyClass2_eq_zero_iff]

/-- The explicit `H²(G, M)` is Mathlib's `continuousCohomology 2` of the canonical object attached
to `M`, as an additive equivalence.

The group is locally compact because the inverse of the degree-two cochain comparison uncurries,
which is where the compact-open exponential law enters; a profinite group qualifies. -/
noncomputable def explicitH2AddEquivContinuousCohomology :
    H2 G M ≃+ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  QuotientAddGroup.liftEquiv _ (cohomologyClass2_surjective G M) (cohomologyClass2_ker G M)

/-- The comparison sends the class of a continuous two-cocycle to the canonical homology class of
the cocycle it corresponds to. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_apply (c : Z2 G M) :
    explicitH2AddEquivContinuousCohomology G M (c : H2 G M) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2
        (cocycleEquiv2 G M c) := by
  exact QuotientAddGroup.liftEquiv_coe _ _ _ c

/-- The inverse comparison sends a canonical homology class to the explicit class of the
corresponding inhomogeneous cocycle. -/
@[simp]
theorem explicitH2AddEquivContinuousCohomology_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) :
    (explicitH2AddEquivContinuousCohomology G M).symm
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 c) =
      (((cocycleEquiv2 G M).symm c : Z2 G M) : H2 G M) := by
  apply (explicitH2AddEquivContinuousCohomology G M).injective
  rw [AddEquiv.apply_symm_apply, explicitH2AddEquivContinuousCohomology_apply,
    AddEquiv.apply_symm_apply]

/-- The degree-two comparison carries the explicit pullback `TauCeti.ContCohomology.explicitMap2`
along a compatible pair to Mathlib's `ContinuousCohomology.map` along the same pair. This is the
naturality equation used to transport general compatible-pair maps between the two models. -/
theorem explicitH2AddEquivContinuousCohomology_map
    (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction H N]
    [ContinuousSMul H N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : H2 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 2
        (explicitH2AddEquivContinuousCohomology G M x) =
      explicitH2AddEquivContinuousCohomology H N
        (explicitMap2 G M H N φ f continuous_of_discreteTopology hf x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitMap2_mk, explicitH2AddEquivContinuousCohomology_apply,
      explicitH2AddEquivContinuousCohomology_apply, ← cocycleEquiv2_naturality]
    exact congr($(_root_.ContinuousCohomology.π_map φ
      (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 2)
      (cocycleEquiv2 G M c))

/-- The degree-two comparison carries the explicit coefficient map to the canonical coefficient
map `TauCeti.ContinuousCohomology.coeffMap` attached to the same equivariant homomorphism. This
naturality equation transports coefficient maps between the two models. -/
theorem explicitH2AddEquivContinuousCohomology_coeffMap
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N) (x : H2 G M) :
    TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m) 2
        (explicitH2AddEquivContinuousCohomology G M x) =
      explicitH2AddEquivContinuousCohomology G N
        (explicitCoeff2 G M f continuous_of_discreteTopology x) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.id G : G →* G)
      f.toAddMonoidHom.toIntLinearMap (fun g m ↦ map_smul f g m) =
      ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  -- The explicit coefficient map is the explicit pullback at the identity, class by class.
  have hcoeff : explicitCoeff2 G M f continuous_of_discreteTopology x =
      explicitMap2 G M G N (ContinuousMonoidHom.id G) f.toAddMonoidHom
        continuous_of_discreteTopology (fun g m ↦ map_smul f g m) x := by
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      rw [explicitCoeff2_mk]
      -- `explicitCoeff2_mk` coerces `f` to `M →+ N`, which is `f.toAddMonoidHom` by definition;
      -- `exact` rather than `rw` lets the two spellings of the same map unify.
      exact (explicitMap2_mk G M G N _ _ _ _ c).symm
  rw [TauCeti.ContinuousCohomology.coeffMap_def, ← hpair, hcoeff]
  exact explicitH2AddEquivContinuousCohomology_map G M G N (ContinuousMonoidHom.id G)
    f.toAddMonoidHom (fun g m ↦ map_smul f g m) x

end LocallyCompact

/-! ### The comparisons as isomorphisms of topological modules -/

section Compact

/-! Compactness of `G` enters only here, and only through
`TauCeti.discreteTopology_continuousCohomology`: it makes the canonical side discrete, so that the
additive equivalences above are automatically homeomorphisms onto it. Local compactness, which
degree two needs, follows from compactness for a topological group. -/

variable [CompactSpace G]

/-- The degree-one comparison in `TopModuleCat ℤ`. The source is the discrete carrier
`TauCeti.ContCohomology.DiscreteH1`, and not `H¹` with the quotient topology inherited from the
pointwise topology on `G → M`, which is not discrete in general.

The canonical side is the image of `M` under the coefficient dictionary and **not** an arbitrary
object of `TopRep ℤ G`: a general object need not be discrete, and the explicit complex is not a
description of its cohomology. -/
noncomputable def explicitH1IsoContinuousCohomology :
    TopModuleCat.of ℤ (DiscreteH1 G M) ≅ continuousCohomology 1 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso
    { ((discreteH1Equiv G M).trans
        (explicitH1AddEquivContinuousCohomology G M)).toIntLinearEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
/-- The degree-one isomorphism of topological modules is the additive comparison, read on the
discrete carrier. -/
theorem explicitH1IsoContinuousCohomology_hom_apply (x : DiscreteH1 G M) :
    (explicitH1IsoContinuousCohomology G M).hom x =
      explicitH1AddEquivContinuousCohomology G M (discreteH1Equiv G M x) := (rfl)

-- `simp` reduces the carriers of `TopModuleCat.of ℤ (DiscreteH1 G M)` and of its degree-two
-- analogue in implicit type arguments before it looks a term up, so the `simp` lemmas evaluating
-- the inverse comparisons state their left-hand sides through `dsimp% only`, as in #8315.
/-- The inverse degree-one isomorphism sends a canonical homology class to the discrete carrier
of the corresponding explicit cocycle class. -/
@[simp]
theorem explicitH1IsoContinuousCohomology_inv_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 1) :
    (dsimp% only ((explicitH1IsoContinuousCohomology G M).inv
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1 c))) =
      (discreteH1Equiv G M).symm
        (((cocycleEquiv1 G M).symm c : Z1 G M) : H1 G M) := by
  -- Unfold the `TopModuleCat.ofIso` inverse to expose the two composed additive equivalences.
  change (discreteH1Equiv G M).symm
    ((explicitH1AddEquivContinuousCohomology G M).symm
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 1 c)) = _
  rw [explicitH1AddEquivContinuousCohomology_symm_apply]

/-! ### Transport in degree one -/

/-- **Transport of compatible-pair pullback in degree one.** The isomorphisms of
topological modules carry the explicit pullback to Mathlib's canonical map. Compactness is needed
only to equip the canonical cohomology objects with their discrete topology. -/
theorem explicitIso_map
    (H N : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction H N] [ContinuousSMul H N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (x : DiscreteH1 G M) :
    _root_.ContinuousCohomology.map φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) 1
        ((explicitH1IsoContinuousCohomology G M).hom x) =
      (explicitH1IsoContinuousCohomology H N).hom
        ((discreteH1Equiv H N).symm
          (explicitMap1 G M H N φ f continuous_of_discreteTopology hf
            (discreteH1Equiv G M x))) := by
  rw [explicitH1IsoContinuousCohomology_hom_apply,
    explicitH1IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply]
  exact explicitH1AddEquivContinuousCohomology_map G M H N φ f hf
    (discreteH1Equiv G M x)

/-- **Transport of restriction in degree one.** The comparison carries restriction of
explicit cohomology classes to canonical restriction along the subgroup inclusion. -/
theorem explicitIso_res (S : Subgroup G) [CompactSpace S] (x : DiscreteH1 G M) :
    TauCeti.ContinuousCohomology.res S (ofDiscreteModule ℤ G M) 1
        ((explicitH1IsoContinuousCohomology G M).hom x) =
      (explicitH1IsoContinuousCohomology S M).hom
        ((discreteH1Equiv S M).symm
          (explicitRes1 G M S (discreteH1Equiv G M x))) := by
  have hpair : ofDiscreteModulePair (ContinuousMonoidHom.subgroupSubtype S : S →* G)
      (AddMonoidHom.id M).toIntLinearMap (fun _ _ ↦ rfl) =
      𝟙 (TopRep.res (S.subtype : S →* G) (ofDiscreteModule ℤ G M)) :=
    ofDiscreteModulePair_eq_of_hom_apply _ _ _ _ fun _ ↦ rfl
  rw [TauCeti.ContinuousCohomology.res_def, explicitRes1_eq_explicitMap1, ← hpair]
  exact explicitIso_map G M S M (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M)
    (fun _ _ ↦ rfl) x

/-- **Transport of coefficient maps in degree one.** The comparison carries the
explicit coefficient map to the canonical map induced by the same equivariant homomorphism. -/
theorem explicitIso_coeffMap
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N) (x : DiscreteH1 G M) :
    TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap fun g m ↦ map_smul f g m) 1
        ((explicitH1IsoContinuousCohomology G M).hom x) =
      (explicitH1IsoContinuousCohomology G N).hom
        ((discreteH1Equiv G N).symm
          (explicitCoeff1 G M f continuous_of_discreteTopology (discreteH1Equiv G M x))) := by
  rw [explicitH1IsoContinuousCohomology_hom_apply,
    explicitH1IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply]
  exact explicitH1AddEquivContinuousCohomology_coeffMap G M N f (discreteH1Equiv G M x)

/-- The degree-two comparison in `TopModuleCat ℤ`. -/
noncomputable def explicitH2IsoContinuousCohomology :
    TopModuleCat.of ℤ (DiscreteH2 G M) ≅ continuousCohomology 2 (ofDiscreteModule ℤ G M) :=
  TopModuleCat.ofIso
    { ((discreteH2Equiv G M).trans
        (explicitH2AddEquivContinuousCohomology G M)).toIntLinearEquiv with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
/-- The degree-two isomorphism of topological modules is the additive comparison, read on the
discrete carrier. -/
theorem explicitH2IsoContinuousCohomology_hom_apply (x : DiscreteH2 G M) :
    (explicitH2IsoContinuousCohomology G M).hom x =
      explicitH2AddEquivContinuousCohomology G M (discreteH2Equiv G M x) := (rfl)

-- `dsimp% only` on the left-hand side: see the comment on
-- `explicitH1IsoContinuousCohomology_inv_apply`.
/-- The inverse degree-two isomorphism sends a canonical homology class to the discrete carrier
of the corresponding explicit cocycle class. -/
@[simp]
theorem explicitH2IsoContinuousCohomology_inv_apply
    (c : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G M) 2) :
    (dsimp% only ((explicitH2IsoContinuousCohomology G M).inv
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 c))) =
      (discreteH2Equiv G M).symm
        (((cocycleEquiv2 G M).symm c : Z2 G M) : H2 G M) := by
  -- Unfold the `TopModuleCat.ofIso` inverse to expose the two composed additive equivalences.
  change (discreteH2Equiv G M).symm
    ((explicitH2AddEquivContinuousCohomology G M).symm
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).homologyπ 2 c)) = _
  rw [explicitH2AddEquivContinuousCohomology_symm_apply]

end Compact

section OfDiscrete

/-! ### Discrete smooth representations over any scalars

The continuous cohomology of a discrete `X : TopRep k G` is that of its carrier `X.V` as a discrete
`ℤ`-module (`TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv`), so the
`ℤ`-comparisons above identify the explicit `H¹` and `H²` of `X.V` with `continuousCohomology 1 X`
and `continuousCohomology 2 X`. -/

variable {G} {k : Type*} [Ring k] [TopologicalSpace k] (X : TopRep k G) [DiscreteTopology X.V]

attribute [local instance] TopRep.distribMulAction

variable [ContinuousSMul G X.V]

/-- The explicit `H¹` of the carrier of a discrete smooth representation `X` over any scalars, with
the action read off from `X`, is Mathlib's `continuousCohomology 1 X`. -/
noncomputable def _root_.TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete :
    H1 G X.V ≃+ continuousCohomology 1 X :=
  (explicitH1AddEquivContinuousCohomology G X.V).trans (ofDiscreteModuleRestrictScalarsIntEquiv X 1)

/-- The degree-one comparison for a discrete `X` is the `ℤ`-comparison of its carrier followed by
`ofDiscreteModuleRestrictScalarsIntEquiv`. -/
-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
theorem _root_.TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply (x : H1 G X.V) :
    X.explicitH1AddEquivContinuousCohomologyOfDiscrete x =
      ofDiscreteModuleRestrictScalarsIntEquiv X 1
        (explicitH1AddEquivContinuousCohomology G X.V x) :=
  (rfl)

/-- The explicit `H²` of the carrier of a discrete smooth representation `X` over any scalars, with
the action read off from `X`, is Mathlib's `continuousCohomology 2 X`. -/
noncomputable def _root_.TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete
    [LocallyCompactSpace G] :
    H2 G X.V ≃+ continuousCohomology 2 X :=
  (explicitH2AddEquivContinuousCohomology G X.V).trans (ofDiscreteModuleRestrictScalarsIntEquiv X 2)

/-- The degree-two comparison for a discrete `X` is the `ℤ`-comparison of its carrier followed by
`ofDiscreteModuleRestrictScalarsIntEquiv`. -/
-- Not `@[simp]`: the comparison is the intended normal form, and this lemma unfolds it.
theorem _root_.TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply
    [LocallyCompactSpace G] (x : H2 G X.V) :
    X.explicitH2AddEquivContinuousCohomologyOfDiscrete x =
      ofDiscreteModuleRestrictScalarsIntEquiv X 2
        (explicitH2AddEquivContinuousCohomology G X.V x) :=
  (rfl)

omit [ContinuousSMul G X.V] in
/-- In degree two, `ofDiscreteModuleCocyclesRestrictScalarsIntIso` does not change the values of
a homogeneous cocycle. -/
-- Not a `simp` lemma, for the same reason as `iCycles_cocyclesRestrictScalarsIntEquiv_one_apply`.
theorem iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_two_apply
    (w : _root_.ContinuousCohomology.cocycles (ofDiscreteModule ℤ G X.V) 2) (g₀ g₁ g₂ : G) :
    ((TopRep.homogeneousCochains X).iCycles 2
        ((ofDiscreteModuleCocyclesRestrictScalarsIntIso X 2).hom w)).val g₀ g₁ g₂ =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G X.V)).iCycles 2 w).val g₀ g₁ g₂ := by
  rw [ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply]
  refine (iCycles_cocyclesRestrictScalarsIntEquiv_two_apply X _ g₀ g₁ g₂).trans ?_
  -- The transport along the equality of objects is a `cast` of values once that equality has a
  -- variable side; here both carriers are `X.V`, so the `cast` is the identity.
  have hev : ∀ (B : TopRep ℤ G) (h : ofDiscreteModule ℤ G X.V = B),
      ((TopRep.homogeneousCochains B).iCycles 2
          (eqToHom (congrArg (_root_.ContinuousCohomology.cocycles · 2) h) w)).val g₀ g₁ g₂ =
        cast (congrArg TopRep.V h)
          (((TopRep.homogeneousCochains (ofDiscreteModule ℤ G X.V)).iCycles 2 w).val g₀ g₁ g₂) := by
    rintro B rfl
    simp only [eqToHom_refl, CategoryTheory.id_apply, cast_eq]
  exact (hev _ (ofDiscreteModule_eq_restrictScalarsInt_obj X)).trans (cast_eq _ _)

/-- The degree-two comparison for discrete representations is natural in compatible pairs: it
carries the explicit pullback along `φ` and the underlying additive map `f` of a morphism
`F : res φ X ⟶ Y` to Mathlib's `ContinuousCohomology.map φ F`. -/
theorem _root_.TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_map
    [LocallyCompactSpace G] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (Y : TopRep k H) [DiscreteTopology Y.V] [ContinuousSMul H Y.V]
    (φ : H →ₜ* G) (F : TopRep.res (φ : H →* G) X ⟶ Y) (f : X.V →+ Y.V)
    (hF : ∀ m, F.hom m = f m) (hf : ∀ (h : H) (m : X.V), f (φ h • m) = h • f m)
    (x : H2 G X.V) :
    _root_.ContinuousCohomology.map φ F 2 (X.explicitH2AddEquivContinuousCohomologyOfDiscrete x) =
      Y.explicitH2AddEquivContinuousCohomologyOfDiscrete
        (explicitMap2 G X.V H Y.V φ f continuous_of_discreteTopology hf x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply,
      TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply,
      ← explicitH2AddEquivContinuousCohomology_map, explicitH2AddEquivContinuousCohomology_apply,
      TauCeti.ContinuousCohomology.map_π_apply, ofDiscreteModuleRestrictScalarsIntEquiv_π,
      ofDiscreteModuleRestrictScalarsIntEquiv_π]
    -- Applied as a term: the cocycle sits in `restrictScalarsInt.obj (cocycles X 2)`, which `rw`
    -- does not identify with the source `cocycles X 2` of `map φ F 2`.
    refine (TauCeti.ContinuousCohomology.map_π_apply φ F 2 _).trans ?_
    congr 1
    apply (TopRep.homogeneousCochains Y).iCycles_injective 2
    apply Subtype.ext
    ext g₀ g₁ g₂
    have hF' (m : X.V) :
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap
          (fun h m ↦ hf h m)).hom m = f m :=
      ofDiscreteModulePair_hom_apply (φ : H →* G) f.toIntLinearMap
        (fun h m ↦ hf h m) m
    -- Applied as a term because the cocycle is definitionally in the restriction of scalars of
    -- `cocycles X 2`, which `rw` does not identify with the source of `cocyclesMap φ F 2`.
    refine (TauCeti.ContinuousCohomology.iCycles_cocyclesMap_two_apply φ F _ f hF
      g₀ g₁ g₂).trans ?_
    rw [iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_two_apply,
      iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_two_apply,
      TauCeti.ContinuousCohomology.iCycles_cocyclesMap_two_apply φ
        (ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m ↦ hf h m) _ f
        hF']
    rfl

end OfDiscrete

end TauCeti.ContCohomology
