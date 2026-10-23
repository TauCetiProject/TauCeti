/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.ChartedSpace
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Ramification
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Transport
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover
public import TauCeti.Topology.Covering.Clopen

/-!
# The filled cover as a topological branched cover of the sphere

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres, and let
`TauCeti.FilledCover.fillMap p : FilledCover p → OnePoint ℂ` be its extension to the filled
cover, sending the added point of each component of `p ⁻¹' D_q*` to its puncture `q`. Over the
complement of the three marked points `fillMap p` is a covering map, whose fibre over a point `z`
of `ℂ ∖ {0, 1}` is the fibre of `p` over `z` (`TauCeti.FilledCover.isCoveringMapOn_fillMap`,
`TauCeti.FilledCover.fillMap_preimage_toOnePoint`). This file proves the remaining local property
that makes it a branched cover with branch values in `{0, 1, ∞}`: at the added point of a
component `i`, it is `w ↦ w ^ e` for `e = FilledCover.degree p i`, in the chart of the filled
cover centred at that point and the inverse of the standard sphere coordinate
`TauCeti.ThricePuncturedSphere.Puncture.sphereCoordInv` at the puncture.

Consequently every connected degree-`n` cover `C` of `ℂ ∖ {0, 1}` fills to a topological branched
cover of degree `n` (`TauCeti.ConnectedCover.toTopBranchedCover`), whose local degree at the added
point of a component is the local degree of that component. Isomorphic covers fill to isomorphic
branched covers (`TauCeti.ConnectedCover.toTopBranchedCoverIso`), so filling is defined on
isomorphism classes (`TauCeti.ConnectedCoverClass.toTopBranchedCover`). Deleting the marked fibres
again recovers `C` up to isomorphism (`TauCeti.ConnectedCover.connectedCoverIso`), so filling is a
right inverse of the restriction map from isomorphism classes of topological branched covers of
degree `n` to isomorphism classes of connected degree-`n` covers of `ℂ ∖ {0, 1}`
(`TauCeti.ConnectedCoverClass.restrict_toTopBranchedCover`), which is therefore surjective
(`TauCeti.TopBranchedCover.IsoClass.restrict_surjective`). Since a branched cover is determined by
its unbranched part (`TauCeti.TopBranchedCover.IsoClass.restrict_injective`), every topological
branched cover is isomorphic to the filled cover of its unbranched part
(`TauCeti.TopBranchedCover.isoFilledCover`), and restriction is a bijection on isomorphism classes
(`TauCeti.TopBranchedCover.IsoClass.restrict_bijective`).

Through this isomorphism the ramification of a topological branched cover is read off its
monodromy: over `0`, `1` and `∞` the ramification partition, formed by the local degrees at the
points of the fibre, is the full cycle type of `σ0`, `σ1` and `σinf` in the monodromy triple of the
unbranched part (`TauCeti.TopBranchedCover.parts_ramificationPartition_zero`), since the points over
a puncture of a filled cover are the added points over it, whose local degrees are the cycle
lengths (`TauCeti.FilledCover.map_degree_overZero`).

## Main results

* `TauCeti.FilledCover.isLocalPowerAt_fillMap_center`: at the added point of a component,
  `fillMap p` is locally the power map of exponent the local degree of the component.
* `TauCeti.ConnectedCover.toTopBranchedCover`: the filled cover of a connected degree-`n` cover,
  as a topological branched cover of degree `n`.
* `TauCeti.ConnectedCover.localDegree_toTopBranchedCover_center`: its local degrees at the added
  points.
* `TauCeti.ConnectedCover.toTopBranchedCoverIso`: an isomorphism of covers extends to an
  isomorphism of their filled branched covers.
* `TauCeti.ConnectedCoverClass.toTopBranchedCover`: the filled branched cover of an isomorphism
  class of covers.
* `TauCeti.ConnectedCover.connectedCoverIso`: deleting the marked fibres of the filled cover
  gives back the original cover.
* `TauCeti.ConnectedCoverClass.restrict_toTopBranchedCover`: on isomorphism classes, restriction
  undoes filling.
* `TauCeti.TopBranchedCover.IsoClass.restrict_surjective`: every connected degree-`n` cover of
  `ℂ ∖ {0, 1}` is the restriction of a topological branched cover of degree `n`.
* `TauCeti.TopBranchedCover.isoFilledCover`: every topological branched cover is isomorphic to
  the filled cover of its unbranched part.
* `TauCeti.TopBranchedCover.IsoClass.restrict_bijective`: topological branched covers of degree
  `n` and connected degree-`n` covers of `ℂ ∖ {0, 1}` have the same isomorphism classes.
* `TauCeti.TopBranchedCover.parts_ramificationPartition_zero`,
  `TauCeti.TopBranchedCover.parts_ramificationPartition_one`,
  `TauCeti.TopBranchedCover.parts_ramificationPartition_inf`: the ramification partitions over
  `0`, `1` and `∞` are the full cycle types of `σ0`, `σ1` and `σinf`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (Lemma 1.80: a finite unramified cover of a punctured surface extends to a branched
  cover of the compact surface).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8, Theorem 8.4.
-/

public noncomputable section

namespace TauCeti

open Function Metric Set Topology ThricePuncturedSphere PunctureFilling

namespace FilledCover

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- **The local model at a filled point.** At the added point of the component `i` over the
puncture `q`, the extended projection is `w ↦ w ^ degree p i`, in the chart of the filled cover
centred at that point and the inverse of the extended coordinate `q.sphereCoordInv` of the sphere
at `q`. -/
theorem isLocalPowerAt_fillMap_center (i : FilledPoint p) :
    IsLocalPowerAt (fillMap p) (center (chart p) i) (degree p i) := by
  let := chartedSpace hp hfin
  have hq := (FilledPoint.sigmaEquiv p i).1.isOpenEmbedding_sphereCoordInv
  refine isLocalPowerAt_iff.2 ⟨chartAt ℂ (center (chart p) i),
    (hq.toOpenPartialHomeomorph _).symm, mem_chart_source ℂ _, ?_,
    chartAt_center_apply_center hp hfin i, ?_, fun w hw => ?_⟩
  · intro y hy
    rw [chartAt_center_source hp hfin] at hy
    obtain ⟨w, rfl⟩ := hy
    rw [OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      fillMap_disc hp hfin]
    exact mem_range_self _
  · rw [fillMap_center, ← Puncture.sphereCoordInv_apply_zero]
    exact hq.toOpenPartialHomeomorph_left_inv
  · rw [chartAt_center_target] at hw
    lift w to ball (0 : ℂ) 1 using hw
    rw [chartAt_center_symm_apply, fillMap_disc hp hfin]
    exact hq.toOpenPartialHomeomorph_left_inv

end FilledCover

namespace ConnectedCover

open FilledCover

variable {n : ℕ} (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

/-- **The filled cover as a topological branched cover.** Filling the punctures of a connected
degree-`n` cover `C` of `ℂ ∖ {0, 1}`, and extending its projection to the added points, gives a
topological branched cover of the sphere of degree `n` with branch values in `{0, 1, ∞}`. Its
total space is `FilledCover C.cover.proj` and its projection is `FilledCover.fillMap`
(`TauCeti.ConnectedCover.toTopBranchedCover_π_apply`). -/
-- The body is exposed so that the total space of the branched cover is the filled cover by
-- definition.
@[expose]
def toTopBranchedCover : TopBranchedCover n where
  Z := FilledCover ⇑C.cover.proj
  instCompactSpace :=
    FilledCover.compactSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  instConnectedSpace := PunctureFilling.connectedSpace
  instT2Space := FilledCover.t2Space C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  instSecondCountableTopology :=
    letI := FilledCover.chartedSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
    letI := FilledCover.compactSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
    ChartedSpace.secondCountable_of_sigmaCompact ℂ _
  π := ⟨fillMap _, continuous_fillMap C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton⟩
  surjective := surjective_fillMap C.cover.isCoveringMap_proj.surjective
  isCoveringMapOn :=
    isCoveringMapOn_fillMap C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  natCard_preimage_singleton y hy := by
    rw [← mem_compl_iff, ← range_toOnePoint] at hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨ν⟩ := C.nonempty_equiv_fin_of_mem_connectedComponent
      (y := z) (by simp [PreconnectedSpace.connectedComponent_eq_univ])
    exact (natCard_fillMap_preimage_toOnePoint z).trans ((Nat.card_congr ν).trans (Nat.card_fin n))
  exists_isLocalPowerAt_of_mem_marked y hy := by
    induction y using PunctureFilling.induction with
    | incl x =>
      rw [ContinuousMap.coe_mk, fillMap_incl, ← notMem_compl_iff, ← range_toOnePoint] at hy
      exact absurd (mem_range_self _) hy
    | center i =>
      exact ⟨_, isLocalPowerAt_fillMap_center C.cover.isCoveringMap_proj
        C.finite_proj_preimage_singleton i⟩

/-- The projection of the filled branched cover is the extension of the projection of `C`. -/
@[simp]
theorem toTopBranchedCover_π_apply (y : FilledCover ⇑C.cover.proj) :
    C.toTopBranchedCover.π y = fillMap _ y :=
  (rfl)

/-- The local degree of the filled branched cover at the added point of a component is the local
degree `FilledCover.degree` of that component. -/
@[simp]
theorem localDegree_toTopBranchedCover_center (i : FilledPoint ⇑C.cover.proj) :
    C.toTopBranchedCover.localDegree (center (chart _) i) = degree _ i :=
  C.toTopBranchedCover.localDegree_eq_iff.2
    (isLocalPowerAt_fillMap_center C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton i)

/-- The total space of `C` is homeomorphic to the total space of the cover obtained by deleting
the marked fibres from its filled branched cover, by the inclusion `E ↪ FilledCover`. -/
def connectedCoverHomeomorph :
    (C.cover : TopCat) ≃ₜ (C.toTopBranchedCover.connectedCover.cover : TopCat) :=
  (unpuncturedHomeomorph C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton).trans
    C.toTopBranchedCover.connectedCoverHomeomorph.symm

/-- The homeomorphism `TauCeti.ConnectedCover.connectedCoverHomeomorph` is the inclusion of the
total space of `C` into its filled cover. -/
@[simp]
theorem coe_connectedCoverHomeomorph_apply (x : (C.cover : TopCat)) :
    (C.toTopBranchedCover.connectedCoverHomeomorph (C.connectedCoverHomeomorph x) :
      C.toTopBranchedCover.Z) = incl (chart _) x :=
  (congrArg Subtype.val (Homeomorph.apply_symm_apply _ _)).trans
    (coe_unpuncturedHomeomorph C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton x)

/-- **Deleting the marked fibres of the filled cover recovers the cover.** The connected cover of
`ℂ ∖ {0, 1}` underlying the filled branched cover of `C` is isomorphic to `C`, by the inclusion of
the total space of `C` into its filled cover. -/
def connectedCoverIso : C.cover ≅ C.toTopBranchedCover.connectedCover.cover :=
  CoveringSpace.FullSubcategory.isoMk (TopCat.isoOfHomeo C.connectedCoverHomeomorph) (by
    ext1 x
    rw [TopCat.comp_app, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply, ContinuousMap.coe_ofClass,
      ← TopBranchedCover.restrict_connectedCoverHomeomorph]
    apply isOpenEmbedding_toOnePoint.injective
    rw [toOnePoint_apply, TopBranchedCover.coe_restrict_apply, coe_connectedCoverHomeomorph_apply]
    exact fillMap_incl _ x)

/-- The map of total spaces underlying `TauCeti.ConnectedCover.connectedCoverIso`. -/
@[simp]
theorem connectedCoverIso_hom_hom_left :
    C.connectedCoverIso.hom.hom.left = (TopCat.isoOfHomeo C.connectedCoverHomeomorph).hom :=
  CoveringSpace.FullSubcategory.isoMk_hom_hom_left _ _

/-- The inverse map of total spaces underlying `TauCeti.ConnectedCover.connectedCoverIso`. -/
@[simp]
theorem connectedCoverIso_inv_hom_left :
    C.connectedCoverIso.inv.hom.left = (TopCat.isoOfHomeo C.connectedCoverHomeomorph).inv :=
  CoveringSpace.FullSubcategory.isoMk_inv_hom_left _ _

variable {C} {D : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n}

/-- **Isomorphic covers have isomorphic filled branched covers.** An isomorphism `f` of connected
covers of `ℂ ∖ {0, 1}` extends to an isomorphism of their filled branched covers, which is `f` on
the total space of `C` (`TauCeti.ConnectedCover.toTopBranchedCoverIso_apply_incl`). -/
def toTopBranchedCoverIso (f : C.cover ≅ D.cover) :
    TopBranchedCover.Iso C.toTopBranchedCover D.toTopBranchedCover where
  -- The homeomorphism `TopCat.homeoOfIso ((totalSpace _ _).mapIso f)` of total spaces is
  -- definitionally `f.hom.hom.left` on points, since `homeoOfIso` and `Functor.mapIso` apply the
  -- forward morphism and `CoveringSpace.FullSubcategory.totalSpace_map` holds by `rfl`. So the
  -- commutation `FullSubcategory.w f.hom` of `f` with the projections is the hypothesis
  -- `p' ∘ h = p` of `FilledCover.congr`.
  toHomeomorph := FilledCover.congr C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
    (TopCat.homeoOfIso ((CoveringSpace.FullSubcategory.totalSpace _ _).mapIso f))
    (funext (CategoryTheory.ConcreteCategory.congr_hom (CoveringSpace.FullSubcategory.w f.hom)))
  π_apply := fillMap_congr_apply _ _ _ _

/-- The isomorphism `TauCeti.ConnectedCover.toTopBranchedCoverIso f` is `f` on the total space of
`C`. -/
@[simp]
theorem toTopBranchedCoverIso_apply_incl (f : C.cover ≅ D.cover) (x : (C.cover : TopCat)) :
    (toTopBranchedCoverIso f).toHomeomorph (incl (chart _) x) = incl (chart _) (f.hom.hom.left x) :=
  -- The homeomorphism of total spaces is `f.hom.hom.left` by definition, as in
  -- `TauCeti.ConnectedCover.toTopBranchedCoverIso`.
  congr_apply_incl _ _ _ _ x

end ConnectedCover

/-- **The filled branched cover of an isomorphism class of covers.** Filling the punctures of a
connected degree-`n` cover of `ℂ ∖ {0, 1}` is well defined on isomorphism classes, by
`TauCeti.ConnectedCover.toTopBranchedCoverIso`. -/
def ConnectedCoverClass.toTopBranchedCover {n : ℕ} :
    ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n →
      TopBranchedCover.IsoClass.{0} n :=
  lift (fun C ↦ .mk C.toTopBranchedCover) fun _ _ ⟨f⟩ ↦
    TopBranchedCover.IsoClass.mk_eq_mk_iff.2 ⟨ConnectedCover.toTopBranchedCoverIso f⟩

/-- The filled branched cover of the class of `C` is the class of the filled branched cover of
`C`. -/
@[simp]
theorem ConnectedCoverClass.toTopBranchedCover_mk {n : ℕ}
    (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (mk C).toTopBranchedCover = .mk C.toTopBranchedCover :=
  lift_mk _ _ C

/-- Restricting the filled branched cover of `C` over `ℂ ∖ {0, 1}` gives back the isomorphism
class of `C`. -/
@[simp]
theorem ConnectedCoverClass.mk_connectedCover_toTopBranchedCover {n : ℕ}
    (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    mk C.toTopBranchedCover.connectedCover = mk C :=
  (mk_eq_mk_iff.2 ⟨C.connectedCoverIso⟩).symm

/-- **Restriction undoes filling on isomorphism classes.** Restricting the filled branched cover
of a class of connected degree-`n` covers of `ℂ ∖ {0, 1}` over `ℂ ∖ {0, 1}` gives back that
class. -/
@[simp]
theorem ConnectedCoverClass.restrict_toTopBranchedCover {n : ℕ}
    (c : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    c.toTopBranchedCover.restrict = c := by
  obtain ⟨C, rfl⟩ := mk_surjective c
  simp

/-- **Every connected degree-`n` cover of `ℂ ∖ {0, 1}` extends to a topological branched cover of
the sphere**: restriction over `ℂ ∖ {0, 1}` is surjective on isomorphism classes, the filled cover
`TauCeti.ConnectedCoverClass.toTopBranchedCover` providing a preimage of each class. -/
theorem TopBranchedCover.IsoClass.restrict_surjective {n : ℕ} :
    Surjective (IsoClass.restrict : IsoClass.{0} n → _) :=
  RightInverse.surjective ConnectedCoverClass.restrict_toTopBranchedCover

/-- **A branched cover is the filling of its unbranched part.** Every topological branched cover
`X` of degree `n` is isomorphic to the filled cover of the connected cover of `ℂ ∖ {0, 1}` obtained
by deleting its marked fibres, by an isomorphism which on the unbranched part is the inclusion into
the filled cover
(`TauCeti.TopBranchedCover.toHomeomorph_isoFilledCover_connectedCoverHomeomorph`). By
`TauCeti.TopBranchedCover.Iso.restrict_injective`, it is the only such isomorphism. -/
def TopBranchedCover.isoFilledCover {n : ℕ} (X : TopBranchedCover.{0} n) :
    X.Iso X.connectedCover.toTopBranchedCover :=
  .ofConnectedCoverIso X.connectedCover.connectedCoverIso

open FilledCover in
/-- On the unbranched part, `TauCeti.TopBranchedCover.isoFilledCover` is the inclusion of the
total space of the connected cover into its filled cover. -/
@[simp]
theorem TopBranchedCover.toHomeomorph_isoFilledCover_connectedCoverHomeomorph {n : ℕ}
    (X : TopBranchedCover.{0} n) (x : (X.connectedCover.cover : TopCat)) :
    X.isoFilledCover.toHomeomorph (X.connectedCoverHomeomorph x) = incl (chart _) x := by
  rw [← Iso.coe_restrict_apply, isoFilledCover,
    Iso.restrict_ofConnectedCoverIso_connectedCoverHomeomorph,
    ConnectedCover.connectedCoverIso_hom_hom_left]
  exact X.connectedCover.coe_connectedCoverHomeomorph_apply x

/-- **Topological branched covers are classified by their unbranched parts**: restriction over
`ℂ ∖ {0, 1}` is a bijection from isomorphism classes of topological branched covers of degree `n`
to isomorphism classes of connected degree-`n` covers of `ℂ ∖ {0, 1}`. -/
theorem TopBranchedCover.IsoClass.restrict_bijective {n : ℕ} :
    Bijective (IsoClass.restrict : IsoClass.{0} n → _) :=
  ⟨restrict_injective, restrict_surjective⟩

/-! ### Ramification partitions over the punctures -/

namespace TopBranchedCover

open Equiv.Perm FilledCover
open scoped OnePoint

variable {n : ℕ} (X : TopBranchedCover.{0} n)

/-- Over a puncture `q`, the parts of the ramification partition of `X` are the local degrees of
the added points of its filled cover over `q`. -/
private theorem parts_ramificationPartition_toOnePoint (q : Puncture)
    [hq : Fintype (ConnectedComponents (X.connectedCover.cover.proj ⁻¹' q.neighborhood))] :
    (X.ramificationPartition q.toOnePoint).parts =
      Finset.univ.val.map fun c ↦
        degree ⇑X.connectedCover.cover.proj ((FilledPoint.sigmaEquiv _).symm ⟨q, c⟩) := by
  have h : (X.connectedCover.toTopBranchedCover.finite_preimage_singleton q.toOnePoint).toFinset =
      Finset.univ.map (⟨fun c ↦ center (chart _) ((FilledPoint.sigmaEquiv _).symm ⟨q, c⟩),
        PunctureFilling.center_injective.comp
          ((FilledPoint.sigmaEquiv _).symm.injective.comp (sigma_mk_injective (i := q)))⟩ :
        _ ↪ X.connectedCover.toTopBranchedCover.Z) := by
    ext y
    rw [Finite.mem_toFinset]
    refine (Set.ext_iff.1 (fillMap_preimage_puncture (⇑X.connectedCover.cover.proj) q) y).trans ?_
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    -- `Function.Embedding.coeFn_mk` does not fire, since the embedding was ascribed the codomain
    -- `X.connectedCover.toTopBranchedCover.Z`, which is the filled cover only by definition.
    exact Iff.rfl
  rw [← X.isoFilledCover.ramificationPartition_eq, parts_ramificationPartition, h, Finset.map_val,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun c _ ↦ X.connectedCover.localDegree_toTopBranchedCover_center _

/-- The monodromy triple of the cover obtained by deleting the marked fibres of `X` has the cycle
data of the monodromy triple of the restriction of `X`, whatever the numberings of the fibres. -/
private theorem cycleData_monodromyTriple_connectedCover (ν : X.restrict ⁻¹' {basePt} ≃ Fin n)
    (ν' : X.connectedCover.cover.proj ⁻¹' {basePt} ≃ Fin n) :
    (X.connectedCover.cover.isCoveringMap_proj.monodromyTriple ν').cycleData =
      (X.isCoveringMap_restrict.monodromyTriple ν).cycleData :=
  PermutationTriple.cycleData_eq_of_equivalent <| PermutationTriple.IsoClass.mk_eq_mk_iff.1 <|
    (X.connectedCover.cover.isCoveringMap_proj.isoClass_monodromyTriple_eq_of_homeomorph ν'
      X.isCoveringMap_restrict ν X.connectedCoverHomeomorph
      (funext X.restrict_connectedCoverHomeomorph)).symm

/-- **The ramification partition over `0`.** The local degrees of a topological branched cover at
the points over `0` are the cycle lengths of `σ0` in its monodromy triple, fixed points
included. -/
theorem parts_ramificationPartition_zero (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    (X.ramificationPartition ((0 : ℂ) : OnePoint ℂ)).parts =
      fullCycleType (X.isCoveringMap_restrict.monodromyTriple ν).σ0 := by
  obtain ⟨ν'⟩ := X.connectedCover.nonempty_equiv_fin
  have hp := X.connectedCover.cover.isCoveringMap_proj
  have := Finite.of_equiv _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν')
  have := Fintype.ofFinite
    (ConnectedComponents (X.connectedCover.cover.proj ⁻¹' puncturedNeighborhoodZero))
  -- The components over `zero.neighborhood` are those over `puncturedNeighborhoodZero` by
  -- definition, so the instance found for the latter is supplied for the former.
  rw [← Puncture.toOnePoint_zero, parts_ramificationPartition_toOnePoint X .zero (hq := this)]
  simp only [FilledPoint.sigmaEquiv_symm_zero]
  refine (map_degree_overZero hp ν').trans ?_
  rw [fullCycleType_def, fullCycleType_def, ← PermutationTriple.cycleData_σ0,
    ← PermutationTriple.cycleData_σ0, cycleData_monodromyTriple_connectedCover X ν ν']

/-- **The ramification partition over `1`.** The local degrees of a topological branched cover at
the points over `1` are the cycle lengths of `σ1` in its monodromy triple, fixed points
included. -/
theorem parts_ramificationPartition_one (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    (X.ramificationPartition ((1 : ℂ) : OnePoint ℂ)).parts =
      fullCycleType (X.isCoveringMap_restrict.monodromyTriple ν).σ1 := by
  obtain ⟨ν'⟩ := X.connectedCover.nonempty_equiv_fin
  have hp := X.connectedCover.cover.isCoveringMap_proj
  have := Finite.of_equiv _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν')
  have := Fintype.ofFinite
    (ConnectedComponents (X.connectedCover.cover.proj ⁻¹' puncturedNeighborhoodOne))
  -- As over `0`, the instance is supplied explicitly.
  rw [← Puncture.toOnePoint_one, parts_ramificationPartition_toOnePoint X .one (hq := this)]
  simp only [FilledPoint.sigmaEquiv_symm_one]
  refine (map_degree_overOne hp ν').trans ?_
  rw [fullCycleType_def, fullCycleType_def, ← PermutationTriple.cycleData_σ1,
    ← PermutationTriple.cycleData_σ1, cycleData_monodromyTriple_connectedCover X ν ν']

/-- **The ramification partition over `∞`.** The local degrees of a topological branched cover at
the points over `∞` are the cycle lengths of `σinf` in its monodromy triple, fixed points
included. -/
theorem parts_ramificationPartition_inf (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    (X.ramificationPartition (∞ : OnePoint ℂ)).parts =
      fullCycleType (X.isCoveringMap_restrict.monodromyTriple ν).σinf := by
  obtain ⟨ν'⟩ := X.connectedCover.nonempty_equiv_fin
  have hp := X.connectedCover.cover.isCoveringMap_proj
  have := Finite.of_equiv _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν')
  have := Fintype.ofFinite
    (ConnectedComponents (X.connectedCover.cover.proj ⁻¹' puncturedNeighborhoodInf))
  -- As over `0`, the instance is supplied explicitly.
  rw [← Puncture.toOnePoint_inf, parts_ramificationPartition_toOnePoint X .inf (hq := this)]
  simp only [FilledPoint.sigmaEquiv_symm_inf]
  refine (map_degree_overInf hp ν').trans ?_
  rw [fullCycleType_def, fullCycleType_def, ← PermutationTriple.cycleData_σinf,
    ← PermutationTriple.cycleData_σinf, cycleData_monodromyTriple_connectedCover X ν ν']

end TopBranchedCover

end TauCeti
