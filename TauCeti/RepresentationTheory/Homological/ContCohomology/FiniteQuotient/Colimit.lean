/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import TauCeti.Algebra.Category.Grp.FilteredColimits
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Descent
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Explicit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# Finite-quotient comparison in degrees zero, one and two

For a profinite group `G` acting continuously on a discrete module `M`, the explicit continuous
cohomology groups in degrees zero, one and two are colimits of the finite-level groups over the open
normal subgroups:

```text
Hⁱ(G, M) = colim_U Hⁱ(G ⧸ U, M^U),  i = 0, 1, 2.
```

This file names the comparison maps into `Hⁱ(G, M)` for `i = 0, 1, 2` and assembles them into
cocones on the systems `TauCeti.ContCohomology.explicitFiniteQuotientSystem0`,
`explicitFiniteQuotientSystem1` and `explicitFiniteQuotientSystem2`. It proves that all three
cocones are colimiting; those statements are universality of the named maps, not bare
isomorphisms.

## Main definitions

* `TauCeti.ContCohomology.explicitFiniteQuotientComparison0` and
  `explicitFiniteQuotientCocone0`: degree-zero inflation assembled as a cocone.
* `TauCeti.ContCohomology.explicitFiniteQuotientColimit0`: that cocone is colimiting.
* `TauCeti.ContCohomology.explicitFiniteQuotientComparison1`: the leg family, inflation along
  `G → G ⧸ U`.
* `TauCeti.ContCohomology.explicitFiniteQuotientCocone1`: the cocone those legs form, with apex
  `H¹(G, M)`.
* `TauCeti.ContCohomology.explicitFiniteQuotientColimit1`: that cocone is colimiting.
* `TauCeti.ContCohomology.explicitFiniteQuotientComparison2`: the degree-two leg family, again
  given by inflation.
* `TauCeti.ContCohomology.explicitFiniteQuotientCocone2`: the degree-two comparison cocone with
  apex `H²(G, M)`.
* `TauCeti.ContCohomology.explicitFiniteQuotientColimit2`: that cocone is colimiting.

## Main statements

* `TauCeti.ContCohomology.explicitInfl0_comp_explicitFiniteQuotientTransition0`: degree-zero
  inflation is compatible with the finite-level transitions.
* `TauCeti.ContCohomology.explicitFiniteQuotientTransition0_bijective`: every degree-zero
  transition is bijective.
* `TauCeti.ContCohomology.explicitInfl1_comp_explicitFiniteQuotientTransition1` and its
  elementwise form `explicitInfl1_explicitFiniteQuotientTransition1`: inflating through a deeper
  level is inflating directly, which is the cocone condition.
* `TauCeti.ContCohomology.exists_openNormalSubgroup_apply_eq_zero`: a continuous `1`-cocycle of a
  profinite group with discrete coefficients vanishes on an open normal subgroup.
* `TauCeti.ContCohomology.exists_explicitInfl1_eq`: every class in `H¹(G, M)` is inflated from a
  finite level.
* `TauCeti.ContCohomology.subsingleton_H1_of_forall_openNormalSubgroup`: if every finite layer has
  trivial first cohomology, so does `H¹(G, M)`.
* `TauCeti.ContCohomology.explicitInfl2_comp_explicitFiniteQuotientTransition2`: degree-two
  inflation is compatible with the finite-level transitions.
* `TauCeti.ContCohomology.exists_explicitFiniteQuotientTransition2_eq_zero`: a finite-level class
  which inflates to zero vanishes after transition to a sufficiently deep finite level.

## Implementation notes

The comparison map from the `U`-level is inflation along `G → G ⧸ U`, already built as
`TauCeti.ContCohomology.explicitInfl0`, `explicitInfl1` or `explicitInfl2`; they are used under
those names, and the comparison natural transformations assemble the maps rather than introducing
second names for individual legs.

In degree zero every comparison leg is an additive equivalence: being fixed by the quotient on
`M^U` is exactly being fixed by `G` on `M`. Every transition is therefore bijective, so the
degree-zero system is eventually constant in the sense of
`CategoryTheory.Functor.IsEventuallyConstantFrom` and the colimit statement is Mathlib's
`CategoryTheory.Functor.IsEventuallyConstantFrom.isColimitOfIsIso` applied at the whole-group
level. Consequently the degree-zero cocone is already colimiting for any topological group; no
compactness or discreteness hypothesis enters that proof.

Surjectivity of the comparison is *strict*. The zero set of a continuous `1`-cocycle is an open
neighbourhood of `1`, so `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` puts an open
normal subgroup `U` inside it, and the cocycle is then the inflation of its descent to `G ⧸ U`
(`TauCeti.ContCohomology.explicitInfl1_descendZ1`): no coboundary is subtracted. Injectivity of
each comparison map is `TauCeti.ContCohomology.explicitInfl1_injective`, which holds for an
arbitrary normal subgroup and needs neither compactness nor discreteness, so the colimit is a
directed union and the descent of an arbitrary cocone is defined by choosing any level a class
comes from.

In the degree-one argument, compactness and total disconnectedness of `G` are used only to put an
open normal subgroup inside the open zero set supplied by discreteness of `M`.

In degree two, strict descent supplies surjectivity. For injectivity, a continuous primitive of an
inflated coboundary is uniformly constant on right cosets of some open normal subgroup and has
finite image. Passing to a still smaller subgroup which fixes that image descends the primitive,
so the original finite-level class becomes a coboundary at that deeper level.

The degree-two colimit statement is then read off from
`TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`: the comparison legs are jointly surjective,
and two finite-level classes with the same inflation already agree after transition to a common
deeper level.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.2.5).
* L. Ribes and P. Zalesskii, *Profinite Groups*, Cor. 6.5.6(a).
-/

public section

namespace TauCeti.ContCohomology

open CategoryTheory CategoryTheory.Limits

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

section DegreeZero

variable {G M}

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- Inflating from the `U`-level through the `V`-level, for `V ≤ U`, is the same as inflating
from the `U`-level directly. -/
theorem explicitInfl0_comp_explicitFiniteQuotientTransition0 (U V : OpenNormalSubgroup G)
    (hVU : V ≤ U) :
    (explicitInfl0 G M V.toSubgroup).comp (explicitFiniteQuotientTransition0 G M U V hVU) =
      explicitInfl0 G M U.toSubgroup := by
  ext m
  simp only [AddMonoidHom.comp_apply]
  exact (coe_explicitInfl0 G M V.toSubgroup _).trans
    ((coe_explicitFiniteQuotientTransition0 G M hVU m).trans
      (coe_explicitInfl0 G M U.toSubgroup m).symm)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- Inflating a degree-zero class through a deeper finite level does not change it. -/
theorem explicitInfl0_explicitFiniteQuotientTransition0 {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (m : H0 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    explicitInfl0 G M V.toSubgroup (explicitFiniteQuotientTransition0 G M U V hVU m) =
      explicitInfl0 G M U.toSubgroup m := by
  rw [← AddMonoidHom.comp_apply, explicitInfl0_comp_explicitFiniteQuotientTransition0]

variable (G M)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The degree-zero comparison maps into `H⁰(G, M)`, assembled from inflation at every open
normal subgroup. -/
noncomputable def explicitFiniteQuotientComparison0 :
    explicitFiniteQuotientSystem0 G M ⟶
      (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).obj (AddCommGrpCat.of (H0 G M)) where
  app U := AddCommGrpCat.ofHom (explicitInfl0 G M U.unop.toSubgroup)
  naturality U V f :=
    AddCommGrpCat.hom_ext (explicitInfl0_comp_explicitFiniteQuotientTransition0
      U.unop V.unop (leOfHom f.unop))

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The degree-zero comparison map at `U` is inflation along `G → G ⧸ U`. -/
@[simp]
theorem explicitFiniteQuotientComparison0_app (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientComparison0 G M).app (Opposite.op U) =
      AddCommGrpCat.ofHom (explicitInfl0 G M U.toSubgroup) := by
  rw [explicitFiniteQuotientComparison0]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The degree-zero finite-quotient cocone, whose point is `H⁰(G, M)`. -/
@[expose] noncomputable def explicitFiniteQuotientCocone0 :
    Cocone (explicitFiniteQuotientSystem0 G M) where
  pt := AddCommGrpCat.of (H0 G M)
  ι := explicitFiniteQuotientComparison0 G M

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The apex of the degree-zero finite-quotient cocone is `H⁰(G, M)`. -/
@[simp]
theorem explicitFiniteQuotientCocone0_pt :
    (explicitFiniteQuotientCocone0 G M).pt = AddCommGrpCat.of (H0 G M) :=
  rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The legs of the degree-zero finite-quotient cocone are the comparison maps. -/
@[simp]
theorem explicitFiniteQuotientCocone0_ι :
    (explicitFiniteQuotientCocone0 G M).ι = explicitFiniteQuotientComparison0 G M :=
  rfl

variable {G M}

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- Every degree-zero finite-quotient transition is bijective: inflation is an equivalence at
both levels, and inflating through the deeper level is inflating directly. -/
theorem explicitFiniteQuotientTransition0_bijective {U V : OpenNormalSubgroup G} (hVU : V ≤ U) :
    Function.Bijective (explicitFiniteQuotientTransition0 G M U V hVU) := by
  refine ⟨fun x y h ↦ explicitInfl0_injective G M U.toSubgroup ?_, fun x ↦ ?_⟩
  · rw [← explicitInfl0_explicitFiniteQuotientTransition0 hVU x,
      ← explicitInfl0_explicitFiniteQuotientTransition0 hVU y, h]
  · obtain ⟨y, hy⟩ := explicitInfl0_surjective G M U.toSubgroup (explicitInfl0 G M V.toSubgroup x)
    exact ⟨y, explicitInfl0_injective G M V.toSubgroup
      ((explicitInfl0_explicitFiniteQuotientTransition0 hVU y).trans hy)⟩

variable (G M)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- The degree-zero finite-quotient system is eventually constant from the whole-group level:
every transition out of that level is an isomorphism. -/
private theorem isEventuallyConstantFrom_explicitFiniteQuotientSystem0 :
    (explicitFiniteQuotientSystem0 G M).IsEventuallyConstantFrom
      (Opposite.op (openNormalSubgroupTop G)) := by
  intro U f
  rw [ConcreteCategory.isIso_iff_bijective]
  exact explicitFiniteQuotientTransition0_bijective (leOfHom f.unop)

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  [ContinuousSMul G M] in
/-- **The degree-zero finite-quotient colimit theorem**: `H⁰(G, M)` is the colimit of
`H⁰(G ⧸ U, M^U)` over the open normal subgroups, through the inflation maps.

Every transition is an isomorphism, so the system is eventually constant and the whole-group
level — where the comparison leg is the equivalence
`TauCeti.ContCohomology.explicitInfl0Equiv` — already computes the colimit. -/
noncomputable def explicitFiniteQuotientColimit0 :
    IsColimit (explicitFiniteQuotientCocone0 G M) :=
  haveI : Nonempty (OpenNormalSubgroup G) := ⟨openNormalSubgroupTop G⟩
  haveI : IsIso ((explicitFiniteQuotientCocone0 G M).ι.app
      (Opposite.op (openNormalSubgroupTop G))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨explicitInfl0_injective G M _, explicitInfl0_surjective G M _⟩
  (isEventuallyConstantFrom_explicitFiniteQuotientSystem0 G M).isColimitOfIsIso _

end DegreeZero

section Cocone

variable {G M}

/-- Inflating from the `U`-level through the `V`-level, for `V ≤ U`, is inflating from the
`U`-level directly. This is the cocone condition for
`TauCeti.ContCohomology.explicitFiniteQuotientCocone1`. -/
theorem explicitInfl1_comp_explicitFiniteQuotientTransition1 (U V : OpenNormalSubgroup G)
    (hVU : V ≤ U) :
    (explicitInfl1 G M V.toSubgroup).comp (explicitFiniteQuotientTransition1 G M U V hVU) =
      explicitInfl1 G M U.toSubgroup := by
  -- Both maps are compatible-pair pullbacks, so the composite is the pullback along the composite
  -- pair by `explicitMap1_comp`, and that pair is the one defining `explicitInfl1` at `U`.
  have hquot : (continuousFiniteQuotientMap G hVU).comp
      (ContinuousMonoidHom.quotientMk V.toSubgroup) =
      ContinuousMonoidHom.quotientMk U.toSubgroup := by
    ext g
    simp
  have hincl : ((FixedPoints.addSubgroup V.toSubgroup M).subtype).comp
      (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
        FixedPoints.addSubgroup V.toSubgroup M) =
      (FixedPoints.addSubgroup U.toSubgroup M).subtype :=
    AddMonoidHom.ext fun m => coe_fixedPointsInclusion hVU m
  rw [explicitInfl1_eq_explicitMap1, explicitFiniteQuotientTransition1_eq_explicitMap1,
    explicitInfl1_eq_explicitMap1]
  refine (explicitMap1_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_).symm.trans
    (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ hquot hincl)
  exact fun g m => comp_apply_smul _ _ _ _
    (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)
    (subtype_quotientMk_smul G M V.toSubgroup) g m

/-- Inflating a class from a level to a deeper one does not change it: the elementwise form of
`TauCeti.ContCohomology.explicitInfl1_comp_explicitFiniteQuotientTransition1`. -/
theorem explicitInfl1_explicitFiniteQuotientTransition1 {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    explicitInfl1 G M V.toSubgroup (explicitFiniteQuotientTransition1 G M U V hVU y) =
      explicitInfl1 G M U.toSubgroup y := by
  rw [← AddMonoidHom.comp_apply, explicitInfl1_comp_explicitFiniteQuotientTransition1]

variable (G M)

/-- The degree-one comparison maps into `H¹(G, M)`: inflation along `G → G ⧸ U`, assembled into
the leg family of a cocone. They are named because the colimit theorem below says that *these*
maps are universal, not that some isomorphism exists. -/
noncomputable def explicitFiniteQuotientComparison1 :
    explicitFiniteQuotientSystem1 G M ⟶
      (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).obj (AddCommGrpCat.of (H1 G M)) where
  app U := AddCommGrpCat.ofHom (explicitInfl1 G M U.unop.toSubgroup)
  naturality U V f :=
    AddCommGrpCat.hom_ext (explicitInfl1_comp_explicitFiniteQuotientTransition1
      U.unop V.unop (leOfHom f.unop))

/-- The degree-one comparison map at `U` is inflation along `G → G ⧸ U`. -/
@[simp]
theorem explicitFiniteQuotientComparison1_app (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientComparison1 G M).app (Opposite.op U) =
      AddCommGrpCat.ofHom (explicitInfl1 G M U.toSubgroup) := by
  rw [explicitFiniteQuotientComparison1]

/-- The degree-one finite-quotient cocone, whose point is `H¹(G, M)` itself. -/
-- The body is exposed because the apex is a dependent object type: the legs and every map out of
-- the cocone, `explicitFiniteQuotientColimit1.desc` included, are typed by `pt`, so it has to
-- reduce outside this module.  The comparison transformation above is sealed instead, its
-- components being recovered from `explicitFiniteQuotientComparison1_app`.
@[expose] noncomputable def explicitFiniteQuotientCocone1 :
    Cocone (explicitFiniteQuotientSystem1 G M) where
  pt := AddCommGrpCat.of (H1 G M)
  ι := explicitFiniteQuotientComparison1 G M

/-- The apex of the degree-one finite-quotient cocone is `H¹(G, M)`. -/
@[simp]
theorem explicitFiniteQuotientCocone1_pt :
    (explicitFiniteQuotientCocone1 G M).pt = AddCommGrpCat.of (H1 G M) :=
  rfl

/-- The legs of the degree-one finite-quotient cocone are the comparison maps. -/
@[simp]
theorem explicitFiniteQuotientCocone1_ι :
    (explicitFiniteQuotientCocone1 G M).ι = explicitFiniteQuotientComparison1 G M :=
  rfl

/-! ### Degree two -/

variable {G M}

/-- Inflating from the `U`-level through the `V`-level, for `V ≤ U`, is inflating from the
`U`-level directly in degree two. This is the cocone condition for
`TauCeti.ContCohomology.explicitFiniteQuotientCocone2`. -/
theorem explicitInfl2_comp_explicitFiniteQuotientTransition2 (U V : OpenNormalSubgroup G)
    (hVU : V ≤ U) :
    (explicitInfl2 G M V.toSubgroup).comp (explicitFiniteQuotientTransition2 G M U V hVU) =
      explicitInfl2 G M U.toSubgroup := by
  have hquot : (continuousFiniteQuotientMap G hVU).comp
      (ContinuousMonoidHom.quotientMk V.toSubgroup) =
      ContinuousMonoidHom.quotientMk U.toSubgroup := by
    ext g
    simp
  have hincl : ((FixedPoints.addSubgroup V.toSubgroup M).subtype).comp
      (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
        FixedPoints.addSubgroup V.toSubgroup M) =
      (FixedPoints.addSubgroup U.toSubgroup M).subtype :=
    AddMonoidHom.ext fun m => coe_fixedPointsInclusion hVU m
  rw [explicitInfl2_eq_explicitMap2, explicitFiniteQuotientTransition2_eq_explicitMap2,
    explicitInfl2_eq_explicitMap2]
  refine (explicitMap2_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm.trans
    (explicitMap2_congr_of_eq _ _ _ _ _ _ _ _ hquot hincl)

/-- Inflating a degree-two class from a level to a deeper one does not change it: the elementwise
form of `TauCeti.ContCohomology.explicitInfl2_comp_explicitFiniteQuotientTransition2`. -/
theorem explicitInfl2_explicitFiniteQuotientTransition2 {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (y : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    explicitInfl2 G M V.toSubgroup (explicitFiniteQuotientTransition2 G M U V hVU y) =
      explicitInfl2 G M U.toSubgroup y := by
  rw [← AddMonoidHom.comp_apply, explicitInfl2_comp_explicitFiniteQuotientTransition2]

variable (G M)

/-- The degree-two comparison maps into `H²(G, M)`: inflation along `G → G ⧸ U`, assembled into
the leg family of a cocone. -/
noncomputable def explicitFiniteQuotientComparison2 :
    explicitFiniteQuotientSystem2 G M ⟶
      (Functor.const ((OpenNormalSubgroup G)ᵒᵖ)).obj (AddCommGrpCat.of (H2 G M)) where
  app U := AddCommGrpCat.ofHom (explicitInfl2 G M U.unop.toSubgroup)
  naturality U V f :=
    AddCommGrpCat.hom_ext (explicitInfl2_comp_explicitFiniteQuotientTransition2
      U.unop V.unop (leOfHom f.unop))

/-- The degree-two comparison map at `U` is inflation along `G → G ⧸ U`. -/
@[simp]
theorem explicitFiniteQuotientComparison2_app (U : OpenNormalSubgroup G) :
    (explicitFiniteQuotientComparison2 G M).app (Opposite.op U) =
      AddCommGrpCat.ofHom (explicitInfl2 G M U.toSubgroup) := by
  rw [explicitFiniteQuotientComparison2]

/-- The degree-two finite-quotient cocone, whose point is `H²(G, M)` itself. -/
-- As in degree one, the apex is a dependent object type, so maps out of the cocone need this
-- body to reduce outside the module. Its legs are recovered from the component lemma above.
@[expose] noncomputable def explicitFiniteQuotientCocone2 :
    Cocone (explicitFiniteQuotientSystem2 G M) where
  pt := AddCommGrpCat.of (H2 G M)
  ι := explicitFiniteQuotientComparison2 G M

/-- The apex of the degree-two finite-quotient cocone is `H²(G, M)`. -/
@[simp]
theorem explicitFiniteQuotientCocone2_pt :
    (explicitFiniteQuotientCocone2 G M).pt = AddCommGrpCat.of (H2 G M) :=
  rfl

/-- The legs of the degree-two finite-quotient cocone are the comparison maps. -/
@[simp]
theorem explicitFiniteQuotientCocone2_ι :
    (explicitFiniteQuotientCocone2 G M).ι = explicitFiniteQuotientComparison2 G M :=
  rfl

end Cocone

section Colimit

variable [CompactSpace G] [TotallyDisconnectedSpace G]

omit [ContinuousSMul G M] in
/-- A continuous `1`-cocycle of a profinite group with discrete coefficients vanishes on an open
normal subgroup: its zero set is open and contains `1`. -/
theorem exists_openNormalSubgroup_apply_eq_zero (z : Z1 G M) :
    ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, (z : G → M) g = 0 := by
  have hopen : IsOpen ((z : G → M) ⁻¹' {0}) :=
    ((mem_Z1_iff.1 z.2).1).isOpen_preimage _ (isOpen_discrete _)
  have hone : (1 : G) ∈ (z : G → M) ⁻¹' {0} := map_one_of_mem_Z1 z.2
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  exact ⟨U, fun g hg => hU hg⟩

variable {G M}

/-- **Strict surjectivity of the comparison maps**: every class in `H¹(G, M)` is inflated from a
finite level. The representing cocycle itself vanishes on an open normal subgroup `U`, so it *is*
the inflation of its descent to `G ⧸ U` and no coboundary is subtracted. -/
theorem exists_explicitInfl1_eq (x : H1 G M) :
    ∃ (U : OpenNormalSubgroup G)
      (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)),
      explicitInfl1 G M U.toSubgroup y = x := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    obtain ⟨U, hU⟩ := exists_openNormalSubgroup_apply_eq_zero G M z
    exact ⟨U, descendZ1 z fun n => hU (n : G) n.2, explicitInfl1_descendZ1 z _⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Restricting a cocone leg through a transition map gives the leg one level up. This is the
naturality of the cocone, read on elements. -/
private theorem cocone_ι_explicitFiniteQuotientTransition1
    (s : Cocone (explicitFiniteQuotientSystem1 G M)) {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    (s.ι.app (Opposite.op V)).hom (explicitFiniteQuotientTransition1 G M U V hVU y) =
      (s.ι.app (Opposite.op U)).hom y :=
  congrArg (fun w : (explicitFiniteQuotientSystem1 G M).obj (Opposite.op U) ⟶ s.pt => w.hom y)
    ((s.ι.naturality (homOfLE hVU).op).trans (Category.comp_id _))

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Two finite-level classes with the same inflation have the same image under every cocone: they
already agree at the intersection of the two levels, where inflation is injective. -/
private theorem cocone_ι_eq_of_explicitInfl1_eq
    (s : Cocone (explicitFiniteQuotientSystem1 G M)) {U V : OpenNormalSubgroup G}
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (y' : H1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M))
    (h : explicitInfl1 G M U.toSubgroup y = explicitInfl1 G M V.toSubgroup y') :
    (s.ι.app (Opposite.op U)).hom y = (s.ι.app (Opposite.op V)).hom y' := by
  have hkey : explicitFiniteQuotientTransition1 G M U (U ⊓ V) inf_le_left y =
      explicitFiniteQuotientTransition1 G M V (U ⊓ V) inf_le_right y' := by
    refine explicitInfl1_injective G M (U ⊓ V).toSubgroup ?_
    rw [← AddMonoidHom.comp_apply, explicitInfl1_comp_explicitFiniteQuotientTransition1,
      ← AddMonoidHom.comp_apply, explicitInfl1_comp_explicitFiniteQuotientTransition1]
    exact h
  rw [← cocone_ι_explicitFiniteQuotientTransition1 s (inf_le_left : U ⊓ V ≤ U) y,
    ← cocone_ι_explicitFiniteQuotientTransition1 s (inf_le_right : U ⊓ V ≤ V) y', hkey]

/-- The descent of a cocone to `H¹(G, M)`, as a bare function: a class is inflated from some
finite level, and its value is the cocone leg applied to any such witness. -/
private noncomputable def coconeDescFun (s : Cocone (explicitFiniteQuotientSystem1 G M))
    (x : H1 G M) : s.pt :=
  (s.ι.app (Opposite.op (exists_explicitInfl1_eq x).choose)).hom
    (exists_explicitInfl1_eq x).choose_spec.choose

/-- The descent of a cocone is computed by any level a class is inflated from. -/
private theorem coconeDescFun_explicitInfl1 (s : Cocone (explicitFiniteQuotientSystem1 G M))
    (U : OpenNormalSubgroup G)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    coconeDescFun s (explicitInfl1 G M U.toSubgroup y) = (s.ι.app (Opposite.op U)).hom y :=
  cocone_ι_eq_of_explicitInfl1_eq s _ y
    (exists_explicitInfl1_eq (explicitInfl1 G M U.toSubgroup y)).choose_spec.choose_spec

/-- The descent of a cocone is additive: two classes are inflated from a common level. -/
private theorem coconeDescFun_add (s : Cocone (explicitFiniteQuotientSystem1 G M))
    (x x' : H1 G M) :
    coconeDescFun s (x + x') = coconeDescFun s x + coconeDescFun s x' := by
  obtain ⟨U, y, rfl⟩ := exists_explicitInfl1_eq x
  obtain ⟨V, y', rfl⟩ := exists_explicitInfl1_eq x'
  rw [← explicitInfl1_explicitFiniteQuotientTransition1 (inf_le_left : U ⊓ V ≤ U) y,
    ← explicitInfl1_explicitFiniteQuotientTransition1 (inf_le_right : U ⊓ V ≤ V) y', ← map_add,
    coconeDescFun_explicitInfl1, coconeDescFun_explicitInfl1, coconeDescFun_explicitInfl1]
  exact map_add _ _ _

/-- The descent of a cocone to `H¹(G, M)`, as an additive homomorphism. -/
private noncomputable def coconeDesc (s : Cocone (explicitFiniteQuotientSystem1 G M)) :
    H1 G M →+ s.pt :=
  AddMonoidHom.mk' (coconeDescFun s) (coconeDescFun_add s)

/-- The homomorphism form of the descent is still computed by any level a class is inflated
from. -/
private theorem coconeDesc_explicitInfl1 (s : Cocone (explicitFiniteQuotientSystem1 G M))
    (U : OpenNormalSubgroup G)
    (y : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) :
    coconeDesc s (explicitInfl1 G M U.toSubgroup y) = (s.ι.app (Opposite.op U)).hom y :=
  coconeDescFun_explicitInfl1 s U y

variable (G M)

/-- **The degree-one finite-quotient colimit theorem**: `H¹(G, M)` is the colimit of the
finite-level first cohomology groups `H¹(G ⧸ U, M^U)`, through the inflation maps. -/
noncomputable def explicitFiniteQuotientColimit1 :
    IsColimit (explicitFiniteQuotientCocone1 G M) where
  desc s := AddCommGrpCat.ofHom (coconeDesc s)
  fac s U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
    exact coconeDesc_explicitInfl1 s U.unop y
  uniq s m hm := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    obtain ⟨U, y, rfl⟩ := exists_explicitInfl1_eq x
    refine Eq.trans ?_ (coconeDesc_explicitInfl1 s U y).symm
    exact congrArg
      (fun w : (explicitFiniteQuotientSystem1 G M).obj (Opposite.op U) ⟶ s.pt => w.hom y)
      (hm (Opposite.op U))

variable {G M}

/-- **Vanishing descends from the finite levels**: if every finite layer has trivial first
cohomology, so does `H¹(G, M)`. Every class comes from a finite level, and two classes are
compared at the intersection of their levels. This is the form in which Hilbert 90 and the Kummer
isomorphism pass from finite Galois layers to the absolute Galois group. -/
theorem subsingleton_H1_of_forall_openNormalSubgroup
    (h : ∀ U : OpenNormalSubgroup G,
      Subsingleton (H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))) :
    Subsingleton (H1 G M) := by
  refine ⟨fun x x' => ?_⟩
  obtain ⟨U, y, rfl⟩ := exists_explicitInfl1_eq x
  obtain ⟨V, y', rfl⟩ := exists_explicitInfl1_eq x'
  rw [← explicitInfl1_explicitFiniteQuotientTransition1 (inf_le_left : U ⊓ V ≤ U) y,
    ← explicitInfl1_explicitFiniteQuotientTransition1 (inf_le_right : U ⊓ V ≤ V) y']
  exact congrArg _ (@Subsingleton.elim _ (h (U ⊓ V)) _ _)

/-! ### Degree two -/

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M] [ContinuousSMul G M]
  [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Pulling a degree-two cochain back along a finite-level transition and then to `G` is pulling
it back to `G` directly: the composite pair is the pair defining inflation from `G ⧸ U`. -/
private theorem cochainsMap2_quotientMk_comp_transition {U V : OpenNormalSubgroup G}
    (hVU : V ≤ U)
    (c : (G ⧸ U.toSubgroup) × (G ⧸ U.toSubgroup) → FixedPoints.addSubgroup U.toSubgroup M) :
    cochainsMap2 (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup M).subtype
        (cochainsMap2 (continuousFiniteQuotientMap G hVU : G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup)
          (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
            FixedPoints.addSubgroup V.toSubgroup M) c) =
      cochainsMap2 (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M).subtype c := by
  have hquot : (continuousFiniteQuotientMap G hVU : G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup).comp
      (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup) =
      (ContinuousMonoidHom.quotientMk U.toSubgroup : G →* G ⧸ U.toSubgroup) := by
    ext g
    simp
  have hincl : ((FixedPoints.addSubgroup V.toSubgroup M).subtype).comp
      (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
        FixedPoints.addSubgroup V.toSubgroup M) =
      (FixedPoints.addSubgroup U.toSubgroup M).subtype :=
    AddMonoidHom.ext fun m ↦ coe_fixedPointsInclusion hVU m
  exact (DFunLike.congr_fun (cochainsMap2_comp _ _ _ _) c).symm.trans
    (congrArg₂ (fun φ f ↦ cochainsMap2 φ f c) hquot hincl)

omit [ContinuousSMul G M] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Naturality of `d1` identifies the descended primitive with the transition of the original
cocycle. -/
private theorem d1_descend_eq_cocyclesMap2 {U V : OpenNormalSubgroup G} (hVU : V ≤ U)
    (c : Z2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (b : G → M) (bV : G ⧸ V.toSubgroup → FixedPoints.addSubgroup V.toSubgroup M)
    (hbV_apply : ∀ g : G, (bV (g : G ⧸ V.toSubgroup) : M) = b g)
    (hd : d1 G M b =
      cocyclesMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) G M
        (ContinuousMonoidHom.quotientMk U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M).subtype
        (continuous_fixedPoints_addSubgroup_subtype G M U.toSubgroup)
        (subtype_quotientMk_smul G M U.toSubgroup) c) :
    d1 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) bV =
      cocyclesMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
        (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
        (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
        continuous_of_discreteTopology
        (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) c := by
  apply cochainsMap2_injective
    (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
    (FixedPoints.addSubgroup V.toSubgroup M).subtype
    (fun q ↦ QuotientGroup.induction_on q fun g ↦ ⟨g, rfl⟩) Subtype.coe_injective
  have hbV_eq :
      cochainsMap1 (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup M).subtype bV = b := by
    funext g
    rw [cochainsMap1_apply]
    exact hbV_apply g
  -- The transition followed by pullback to `G` is the inflation from `G ⧸ U`.
  have htransition :
      cochainsMap2 (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
        (FixedPoints.addSubgroup V.toSubgroup M).subtype
        (cocyclesMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
          (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
          (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
          continuous_of_discreteTopology
          (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) c) =
      (cocyclesMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) G M
        (ContinuousMonoidHom.quotientMk U.toSubgroup)
        (FixedPoints.addSubgroup U.toSubgroup M).subtype
        (continuous_fixedPoints_addSubgroup_subtype G M U.toSubgroup)
        (subtype_quotientMk_smul G M U.toSubgroup) c : G × G → M) := by
    refine (congrArg _ (cocyclesMap2_coe _ _ _ _ _ _ _ _ c)).trans ?_
    exact (cochainsMap2_quotientMk_comp_transition (M := M) hVU c).trans
      (cocyclesMap2_coe _ _ _ _ _ _ _ _ c).symm
  -- Pulling back to `G`, `d1` commutes with the pullback and `bV` becomes `b`.
  refine (cochainsMap2_d1
    (ContinuousMonoidHom.quotientMk V.toSubgroup : G →* G ⧸ V.toSubgroup)
    (FixedPoints.addSubgroup V.toSubgroup M).subtype
    (subtype_quotientMk_smul G M V.toSubgroup) bV).trans ?_
  rw [hbV_eq, htransition]
  exact hd

/-- A degree-two class at a finite quotient which inflates to zero becomes zero after transition
to a sufficiently deep finite quotient. This is the injectivity half of the degree-two
finite-quotient colimit theorem. -/
theorem exists_explicitFiniteQuotientTransition2_eq_zero (U : OpenNormalSubgroup G)
    (x : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (hx : explicitInfl2 G M U.toSubgroup x = 0) :
    ∃ (V : OpenNormalSubgroup G) (hVU : V ≤ U),
      explicitFiniteQuotientTransition2 G M U V hVU x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitInfl2_mk, H2pi_eq_zero_iff] at hx
    obtain ⟨b, hb, hd⟩ := mem_B2_iff.1 hx
    -- Uniform local constancy and finite-image stabilization descend the primitive `b`.
    obtain ⟨V, hVU, bV, hbV, hbV_apply⟩ :=
      exists_openNormalSubgroup_descendContinuous U b hb
    refine ⟨V, hVU, ?_⟩
    rw [explicitFiniteQuotientTransition2_mk]
    apply H2pi_eq_zero_iff.2
    refine mem_B2_iff.2 ⟨bV, hbV, ?_⟩
    exact d1_descend_eq_cocyclesMap2 hVU c b bV hbV_apply hd

/-- Two finite-level degree-two classes with the same inflation agree after transition to a
common deeper level: their difference inflates to zero, hence dies at a sufficiently deep
level. -/
private theorem exists_explicitFiniteQuotientTransition2_eq_of_explicitInfl2_eq
    {U V : OpenNormalSubgroup G}
    (y : H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M))
    (y' : H2 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M))
    (h : explicitInfl2 G M U.toSubgroup y = explicitInfl2 G M V.toSubgroup y') :
    ∃ (W : OpenNormalSubgroup G) (hWU : W ≤ U) (hWV : W ≤ V),
      explicitFiniteQuotientTransition2 G M U W hWU y =
        explicitFiniteQuotientTransition2 G M V W hWV y' := by
  let W := U ⊓ V
  let z := explicitFiniteQuotientTransition2 G M U W inf_le_left y -
    explicitFiniteQuotientTransition2 G M V W inf_le_right y'
  have hz : explicitInfl2 G M W.toSubgroup z = 0 := by
    simp only [z, map_sub, explicitInfl2_explicitFiniteQuotientTransition2, h, sub_self]
  obtain ⟨T, hTW, hzero⟩ :=
    exists_explicitFiniteQuotientTransition2_eq_zero W z hz
  refine ⟨T, hTW.trans inf_le_left, hTW.trans inf_le_right, ?_⟩
  have htransition :
      explicitFiniteQuotientTransition2 G M W T hTW z = 0 := hzero
  simp only [z, map_sub, sub_eq_zero] at htransition
  exact (congrArg (fun f => f y)
    (explicitFiniteQuotientTransition2_comp G M U W T inf_le_left hTW)).trans
      (htransition.trans (congrArg (fun f => f y')
        (explicitFiniteQuotientTransition2_comp G M V W T inf_le_right hTW)).symm)

variable (G M)

/-- **The degree-two finite-quotient colimit theorem**: `H²(G, M)` is the colimit of the
finite-level second cohomology groups `H²(G ⧸ U, M^U)`, through the inflation maps. -/
noncomputable def explicitFiniteQuotientColimit2 :
    IsColimit (explicitFiniteQuotientCocone2 G M) :=
  AddCommGrpCat.isColimitOfJointlySurjective (explicitFiniteQuotientCocone2 G M)
    (fun x ↦ by
      obtain ⟨U, y, hy⟩ := exists_explicitInfl2_eq x
      exact ⟨Opposite.op U, y, hy⟩)
    fun U V y y' h ↦ by
      obtain ⟨W, hWU, hWV, hW⟩ :=
        exists_explicitFiniteQuotientTransition2_eq_of_explicitInfl2_eq y y' h
      exact ⟨Opposite.op W, (homOfLE hWU).op, (homOfLE hWV).op, hW⟩

end Colimit

end TauCeti.ContCohomology
