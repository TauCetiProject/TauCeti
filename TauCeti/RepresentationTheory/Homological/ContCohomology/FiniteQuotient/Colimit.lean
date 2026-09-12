/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Explicit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation

/-!
# The degree-one finite-quotient colimit

For a profinite group `G` acting continuously on a discrete module `M`, the first continuous
cohomology group is the colimit of the finite-level groups over the open normal subgroups:

```text
H¹(G, M) = colim_U H¹(G ⧸ U, M^U).
```

This file names the comparison maps into `H¹(G, M)`, assembles them into a cocone on the system
`TauCeti.ContCohomology.explicitFiniteQuotientSystem1`, and proves that the cocone is colimiting.
The statement is universality of those named maps, not a bare isomorphism.

## Main definitions

* `TauCeti.ContCohomology.explicitFiniteQuotientComparison1`: the leg family, inflation along
  `G → G ⧸ U`.
* `TauCeti.ContCohomology.explicitFiniteQuotientCocone1`: the cocone those legs form, with apex
  `H¹(G, M)`.
* `TauCeti.ContCohomology.explicitFiniteQuotientColimit1`: that cocone is colimiting.

## Main statements

* `TauCeti.ContCohomology.explicitInfl1_comp_explicitFiniteQuotientTransition1` and its
  elementwise form `explicitInfl1_explicitFiniteQuotientTransition1`: inflating through a deeper
  level is inflating directly, which is the cocone condition.
* `TauCeti.ContCohomology.exists_openNormalSubgroup_apply_eq_zero`: a continuous `1`-cocycle of a
  profinite group with discrete coefficients vanishes on an open normal subgroup.
* `TauCeti.ContCohomology.exists_explicitInfl1_eq`: every class in `H¹(G, M)` is inflated from a
  finite level.
* `TauCeti.ContCohomology.subsingleton_H1_of_forall_openNormalSubgroup`: if every finite layer has
  trivial first cohomology, so does `H¹(G, M)`.

## Implementation notes

The comparison map from the `U`-level is inflation along `G → G ⧸ U`, already built as
`TauCeti.ContCohomology.explicitInfl1`; it is used under that name, and
`explicitFiniteQuotientComparison1` is the natural transformation assembling those maps, not a
second name for a single one.

Surjectivity of the comparison is *strict*. The zero set of a continuous `1`-cocycle is an open
neighbourhood of `1`, so `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` puts an open
normal subgroup `U` inside it, and the cocycle is then the inflation of its descent to `G ⧸ U`
(`TauCeti.ContCohomology.explicitInfl1_descendZ1`): no coboundary is subtracted. Injectivity of
each comparison map is `TauCeti.ContCohomology.explicitInfl1_injective`, which holds for an
arbitrary normal subgroup and needs neither compactness nor discreteness, so the colimit is a
directed union and the descent of an arbitrary cocone is defined by choosing any level a class
comes from.

Compactness and total disconnectedness of `G` are used only for that open normal subgroup:
discreteness of `M` makes the zero set open, and the two topological hypotheses make the open
normal subgroups a neighbourhood basis of `1`.

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

section Cocone

variable {G M}

/-- Inflating from the `U`-level through the `V`-level, for `V ≤ U`, is inflating from the
`U`-level directly. This is the cocone condition for
`TauCeti.ContCohomology.explicitFiniteQuotientCocone1`. -/
theorem explicitInfl1_comp_explicitFiniteQuotientTransition1 (U V : OpenNormalSubgroup G)
    (hVU : V ≤ U) :
    (explicitInfl1 G M V.toSubgroup).comp (explicitFiniteQuotientTransition1 G M U V hVU) =
      explicitInfl1 G M U.toSubgroup := by
  -- The two composable compatible pairs compose to the pair defining `explicitInfl1` at `U`.
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
  have hcomp : ∀ (g : G) (m : FixedPoints.addSubgroup U.toSubgroup M),
      (((FixedPoints.addSubgroup V.toSubgroup M).subtype).comp
          (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
            FixedPoints.addSubgroup V.toSubgroup M))
        (((continuousFiniteQuotientMap G hVU).comp
          (ContinuousMonoidHom.quotientMk V.toSubgroup)) g • m) =
      g • (((FixedPoints.addSubgroup V.toSubgroup M).subtype).comp
          (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
            FixedPoints.addSubgroup V.toSubgroup M)) m := by
    intro g m
    rw [hquot, hincl]
    exact subtype_quotientMk_smul G M U.toSubgroup g m
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    have htrans : explicitFiniteQuotientTransition1 G M U V hVU
        (c : H1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)) =
        H1pi (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
          (cocyclesMap1 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
            (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
            (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
            continuous_of_discreteTopology
            (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) c) :=
      explicitFiniteQuotientTransition1_mk G M hVU c
    refine (congrArg (explicitInfl1 G M V.toSubgroup) htrans).trans ?_
    refine (explicitInfl1_mk G M V.toSubgroup _).trans ?_
    refine Eq.trans ?_ (explicitInfl1_mk G M U.toSubgroup c).symm
    refine congrArg (fun w : Z1 G M => (w : H1 G M)) ?_
    -- Functoriality of the cocycle pullback is `cocyclesMap1_comp`; only the identification of the
    -- composite pair with the inflation pair at `U` is left.
    have hfunct := DFunLike.congr_fun (cocyclesMap1_comp
      (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
      (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
      (continuousFiniteQuotientMap G hVU)
      (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
        FixedPoints.addSubgroup V.toSubgroup M)
      continuous_of_discreteTopology
      (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU) G M
      (ContinuousMonoidHom.quotientMk V.toSubgroup)
      (FixedPoints.addSubgroup V.toSubgroup M).subtype
      (continuous_fixedPoints_addSubgroup_subtype G M V.toSubgroup)
      (subtype_quotientMk_smul G M V.toSubgroup) hcomp) c
    rw [AddMonoidHom.comp_apply] at hfunct
    refine hfunct.symm.trans (Subtype.ext (funext fun g => ?_))
    -- The two evaluations are spelled with all their arguments because the coefficient map of a
    -- transition is `fixedPointsInclusion`, stated on `FixedPoints.addSubmonoid`, so the cocycle
    -- below does not unify with the pattern of `cocyclesMap1_apply` at reducible transparency.
    have hA := cocyclesMap1_apply (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) G M
      ((continuousFiniteQuotientMap G hVU).comp (ContinuousMonoidHom.quotientMk V.toSubgroup))
      (((FixedPoints.addSubgroup V.toSubgroup M).subtype).comp
        (fixedPointsInclusion hVU : FixedPoints.addSubgroup U.toSubgroup M →+
          FixedPoints.addSubgroup V.toSubgroup M))
      ((continuous_fixedPoints_addSubgroup_subtype G M V.toSubgroup).comp
        continuous_of_discreteTopology) hcomp c g
    have hB := cocyclesMap1_apply (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) G M
      (ContinuousMonoidHom.quotientMk U.toSubgroup)
      (FixedPoints.addSubgroup U.toSubgroup M).subtype
      (continuous_fixedPoints_addSubgroup_subtype G M U.toSubgroup)
      (subtype_quotientMk_smul G M U.toSubgroup) c g
    rw [hA, hB, hquot]
    exact coe_fixedPointsInclusion hVU _

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

end Colimit

end TauCeti.ContCohomology
