/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.NumberedFiber
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Topology.Covering.LocalPower

import Mathlib.Data.Set.Card.Arithmetic
import TauCeti.AlgebraicTopology.ThricePuncturedSphere.RestrictOver
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.ClusterSet
import TauCeti.Topology.OpenPartialHomeomorph.Continuity
import TauCeti.Topology.ConnectedComponents

/-!
# Topological branched covers of the sphere with branch values in `{0, 1, ∞}`

A *topological branched cover of degree `n`* (`TauCeti.TopBranchedCover n`) is a compact,
connected, Hausdorff, second countable space `Z` with a surjective continuous map
`π : Z → OnePoint ℂ` that is a covering map of degree `n` over the thrice-punctured sphere, the
complement of the three marked points `0`, `1` and `∞` (`TauCeti.ThricePuncturedSphere.marked`),
and that is locally `w ↦ w ^ e`, in charts, at every point over a marked point. These are the
objects that analytic Riemann existence for three-point covers classifies, by finite covers of
the thrice-punctured sphere on the topological side and by Belyi maps on the analytic side.

The local exponent is a topological invariant (`TauCeti.IsLocalPowerAt.unique`), so every point
`z` has a well-defined *local degree* `TauCeti.TopBranchedCover.localDegree`, equal to `1` off the
marked fibres. Every fibre of `π` is finite, and the local degrees over any point add up to the
degree: `∑ e = n`. Thus the local degrees in each fibre form a partition of the covering degree,
the *ramification partition* `TauCeti.TopBranchedCover.ramificationPartition`, recording how sheets
coalesce over branch values. It is `1ⁿ` away from the marked points and is invariant under
isomorphism.

Deleting the fibres over the three marked points leaves a connected cover of degree `n` of the
thrice-punctured sphere (`TauCeti.TopBranchedCover.connectedCover`), compatibly with isomorphisms,
so restriction descends to isomorphism classes. Conversely, a branched cover is determined by this
unbranched part: every continuous map over the thrice-punctured sphere between unbranched parts
extends uniquely to the total spaces (`TauCeti.TopBranchedCover.extend`), so every isomorphism of
unbranched parts extends to a unique isomorphism of branched covers, and restriction is injective
on isomorphism classes. This is the uniqueness of the compactification of a finite cover of the
thrice-punctured sphere. The extension exists because at a point of a marked fibre the values
of the map cluster in a connected subset of a finite fibre, hence at a single point. In
particular the deck group of `π` is the deck group of the unbranched cover
(`TauCeti.TopBranchedCover.deckMulEquivDeckRestrict`).

The data carries no atlas. The local models at marked points and the covering map elsewhere
already provide a chart around every point (`TauCeti.TopBranchedCover.exists_mem_source`), so `Z`
is a topological surface, and properness of `π` is a consequence of compactness
(`TauCeti.TopBranchedCover.isProperMap`).

## Main definitions

* `TauCeti.TopBranchedCover n`: a topological branched cover of the sphere of degree `n` with
  branch values in `{0, 1, ∞}`.
* `TauCeti.TopBranchedCover.Iso`: isomorphisms, homeomorphisms commuting with the projections.
* `TauCeti.TopBranchedCover.IsoClass n`: branched covers of degree `n` up to isomorphism.
* `TauCeti.TopBranchedCover.localDegree`: the local degree at a point.
* `TauCeti.TopBranchedCover.ramificationPartition`: the partition of the degree formed by the
  local degrees over a point.
* `TauCeti.TopBranchedCover.restrict`: the projection restricted to the complement of the marked
  fibres, as a map to the thrice-punctured sphere.
* `TauCeti.TopBranchedCover.connectedCover`: the connected finite cover of the
  thrice-punctured sphere obtained by deleting the marked fibres.
* `TauCeti.TopBranchedCover.IsoClass.restrict`: restriction on isomorphism classes, to
  isomorphism classes of connected covers of the thrice-punctured sphere.
* `TauCeti.TopBranchedCover.extend`: the extension of a continuous map over the
  thrice-punctured sphere between unbranched parts to the total spaces.
* `TauCeti.TopBranchedCover.Iso.ofRestrict`: the extension of a homeomorphism over the
  thrice-punctured sphere between unbranched parts to an isomorphism of branched covers.
* `TauCeti.TopBranchedCover.Iso.ofConnectedCoverIso`: the extension of an isomorphism of the
  unbranched connected covers to an isomorphism of branched covers, inverse to
  `TauCeti.TopBranchedCover.Iso.connectedCoverIso`.
* `TauCeti.TopBranchedCover.deckMulEquivDeckRestrict`: restriction identifies the deck group of a
  branched cover with the deck group of its unbranched part.
* `TauCeti.TopBranchedCover.sphere`: the sphere over itself, of degree `1`.

## Main results

* `TauCeti.TopBranchedCover.localDegree_eq_iff`: the local degree is the unique exponent of a
  local power model.
* `TauCeti.TopBranchedCover.localDegree_eq_one`: off the marked fibres the local degree is `1`.
* `TauCeti.TopBranchedCover.finite_preimage_singleton`: every fibre is finite.
* `TauCeti.TopBranchedCover.finsum_mem_preimage_singleton_localDegree`: the local degrees over
  any point sum to the degree.
* `TauCeti.TopBranchedCover.parts_ramificationPartition_of_notMem_marked`: off the marked points
  the ramification partition is `1ⁿ`.
* `TauCeti.TopBranchedCover.Iso.localDegree_apply`,
  `TauCeti.TopBranchedCover.Iso.ramificationPartition_eq`: isomorphisms preserve local degrees and
  ramification partitions.
* `TauCeti.TopBranchedCover.isConnected_preimage_range`: deleting the marked fibres leaves a
  connected space, which is moreover path connected
  (`TauCeti.TopBranchedCover.instPathConnectedSpacePreimageRange`).
* `TauCeti.TopBranchedCover.natCard_restrict_preimage_singleton`: the restricted cover has
  degree `n`.
* `TauCeti.TopBranchedCover.Iso.connectedCoverIso`: an isomorphism of branched covers restricts
  to an isomorphism of their unbranched connected covers.
* `TauCeti.TopBranchedCover.dense_preimage_range`: the unbranched part is dense.
* `TauCeti.TopBranchedCover.eq_extend`: the extension of a map of unbranched parts is unique.
* `TauCeti.TopBranchedCover.Iso.restrict_injective`: an isomorphism of branched covers is
  determined by its restriction to the unbranched parts.
* `TauCeti.TopBranchedCover.IsoClass.restrict_injective`: **uniqueness of the
  compactification**, a branched cover is determined up to isomorphism by its unbranched
  connected cover.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2 (branched coverings, their local degrees, and the compactification of finite covers of a
  punctured surface; Lemma 1.80 and Proposition 1.81 for its uniqueness).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4 (the multiplicities over every point of a proper map add up to its degree).
* `TauCeti.Analysis.Complex.RiemannSurface.Degree`, whose analytic fibre-sum argument supplies the
  proof plan adapted to the topological local-degree setting here.
-/

public section

noncomputable section

open Filter Set Topology OnePoint

namespace TauCeti

open ThricePuncturedSphere

universe u

/-- A **topological branched cover of the sphere of degree `n` with branch values in
`{0, 1, ∞}`**: a compact, connected, Hausdorff, second countable space `Z` with a surjective
continuous map `π : Z → OnePoint ℂ` which is a covering map with fibres of `n` points over the
complement of the marked points, and which is locally `w ↦ w ^ e`, in a chart at the source and
one at the target, at every point over a marked point.

The exponent `e` is not part of the data: it is unique (`TauCeti.IsLocalPowerAt.unique`), and is
recorded as `TauCeti.TopBranchedCover.localDegree`. The degree hypothesis only concerns unmarked
points: over a marked point the fibre has fewer points whenever `π` is branched there, and it is
the local degrees that add up to `n` instead
(`TauCeti.TopBranchedCover.finsum_mem_preimage_singleton_localDegree`). -/
structure TopBranchedCover (n : ℕ) : Type (u + 1) where
  /-- The total space. -/
  Z : Type u
  [instTopologicalSpace : TopologicalSpace Z]
  [instCompactSpace : CompactSpace Z]
  [instConnectedSpace : ConnectedSpace Z]
  [instT2Space : T2Space Z]
  [instSecondCountableTopology : SecondCountableTopology Z]
  /-- The branched covering map. -/
  π : C(Z, OnePoint ℂ)
  /-- The branched covering map is surjective. -/
  surjective : Function.Surjective π
  /-- Off the three marked points, `π` is a covering map. -/
  isCoveringMapOn : IsCoveringMapOn π markedᶜ
  /-- Off the three marked points, the fibres of `π` have `n` points. -/
  natCard_preimage_singleton : ∀ y ∉ marked, Nat.card (π ⁻¹' {y}) = n
  /-- Over each marked point, `π` is `w ↦ w ^ e` in some chart at the source and some chart at
  the target. -/
  exists_isLocalPowerAt_of_mem_marked : ∀ z, π z ∈ marked → ∃ e, IsLocalPowerAt π z e

namespace TopBranchedCover

attribute [instance] instTopologicalSpace instCompactSpace instConnectedSpace instT2Space
  instSecondCountableTopology

variable {n : ℕ} (X : TopBranchedCover n)

/-- The branched covering map is proper, since its source is compact. -/
theorem isProperMap : IsProperMap X.π :=
  X.π.continuous.isProperMap

/-- Over the complement of the marked points, `π` restricts to a covering map. -/
theorem isCoveringMap_restrictPreimage : IsCoveringMap (markedᶜ.restrictPreimage X.π) :=
  X.isCoveringMapOn.isCoveringMap_restrictPreimage

/-! ### The unbranched cover -/

/-- The projection `π` restricted to the complement of the fibres over `0`, `1` and `∞`, viewed
as a map to `ThricePuncturedSphere` through `toOnePoint`. -/
def restrict : X.π ⁻¹' range toOnePoint → ThricePuncturedSphere :=
  restrictOver X.π

/-- The restricted projection agrees with the branched covering map, read in the Riemann sphere. -/
@[simp]
theorem coe_restrict_apply (z : X.π ⁻¹' range toOnePoint) :
    (((X.restrict z : ThricePuncturedSphere) : ℂ) : OnePoint ℂ) = X.π z :=
  coe_restrictOver_apply X.π z

/-- Deleting the fibres over the three marked points leaves a covering of the
thrice-punctured sphere. -/
theorem isCoveringMap_restrict : IsCoveringMap X.restrict :=
  isCoveringMap_restrictOver X.isCoveringMapOn

/-- Off the marked fibres, `π` is locally the first power map. -/
theorem isLocalPowerAt_one {z : X.Z} (hz : X.π z ∉ marked) : IsLocalPowerAt X.π z 1 :=
  X.isCoveringMapOn.isLocalHomeomorphOn.isLocalPowerAt_one (mem_preimage.2 hz)
    (mem_chart_source ℂ (X.π z))

/-- At every point, `π` is locally a power map. -/
theorem exists_isLocalPowerAt (z : X.Z) : ∃ e, IsLocalPowerAt X.π z e := by
  by_cases hz : X.π z ∈ marked
  · exact X.exists_isLocalPowerAt_of_mem_marked z hz
  · exact ⟨1, X.isLocalPowerAt_one hz⟩

/-- Every point of the total space lies in the source of a chart to `ℂ`, so the total space is a
topological surface. -/
theorem exists_mem_source (z : X.Z) : ∃ φ : OpenPartialHomeomorph X.Z ℂ, z ∈ φ.source := by
  obtain ⟨e, he⟩ := X.exists_isLocalPowerAt z
  obtain ⟨φ, -, hz, -⟩ := isLocalPowerAt_iff.1 he
  exact ⟨φ, hz⟩

/-- The **local degree** of a branched cover at a point `z`: the exponent `e` for which `π` is
`w ↦ w ^ e` near `z`, in charts (`TauCeti.TopBranchedCover.localDegree_eq_iff`). It is `1` off
the marked fibres (`TauCeti.TopBranchedCover.localDegree_eq_one`). -/
def localDegree (z : X.Z) : ℕ :=
  (X.exists_isLocalPowerAt z).choose

/-- The branched covering map is locally `w ↦ w ^ e` at `z`, for `e` the local degree. -/
theorem isLocalPowerAt_localDegree (z : X.Z) : IsLocalPowerAt X.π z (X.localDegree z) :=
  (X.exists_isLocalPowerAt z).choose_spec

/-- The local degree is the unique exponent for which `π` is locally a power map. -/
theorem localDegree_eq_iff {z : X.Z} {e : ℕ} : X.localDegree z = e ↔ IsLocalPowerAt X.π z e :=
  ⟨fun h => h ▸ X.isLocalPowerAt_localDegree z,
    fun h => (X.isLocalPowerAt_localDegree z).unique h⟩

/-- Local degrees are positive. -/
theorem localDegree_pos (z : X.Z) : 0 < X.localDegree z :=
  Nat.pos_of_ne_zero (X.isLocalPowerAt_localDegree z).ne_zero

/-- Off the marked fibres, the local degree is `1`. -/
@[simp]
theorem localDegree_eq_one {z : X.Z} (hz : X.π z ∉ marked) : X.localDegree z = 1 :=
  X.localDegree_eq_iff.2 (X.isLocalPowerAt_one hz)

/-- Every fibre of a branched cover is finite: it is compact, and its points are isolated in it
by the local power models. -/
theorem finite_preimage_singleton (y : OnePoint ℂ) : (X.π ⁻¹' {y}).Finite := by
  refine (isClosed_singleton.preimage X.π.continuous).isCompact.finite
    (isDiscrete_iff_nhdsNE.2 fun z hz => inf_principal_eq_bot.2 ?_)
  filter_upwards [(X.isLocalPowerAt_localDegree z).eventually_ne] with z' hz' hyz'
  exact hz' (hyz'.trans hz.symm)

/-- The fibres over the three marked points are finite. -/
theorem finite_preimage_marked : (X.π ⁻¹' marked).Finite :=
  finite_marked.preimage' fun y _ ↦ X.finite_preimage_singleton y

/-- The complement of the marked fibres is dense in the total space: the marked fibres are finite,
and no point of the total space is isolated, since every point lies in a chart to `ℂ`. -/
theorem dense_preimage_range : Dense (X.π ⁻¹' range toOnePoint) := by
  have (z : X.Z) : (𝓝[≠] z).NeBot :=
    let ⟨φ, hz⟩ := X.exists_mem_source z
    φ.nhdsNE_neBot hz
  rw [range_toOnePoint, preimage_compl, compl_eq_univ_sdiff]
  exact dense_univ.sdiff_finite X.finite_preimage_marked

/-- The points over `z` in the restricted cover are exactly the points over `z` in the original
branched cover. -/
theorem image_val_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (Subtype.val : (X.π ⁻¹' range toOnePoint) → X.Z) '' (X.restrict ⁻¹' {z}) =
      X.π ⁻¹' {toOnePoint z} :=
  image_val_restrictOver_preimage_singleton X.π z

/-- Every fibre of the restricted cover is finite. -/
theorem finite_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    (X.restrict ⁻¹' {z}).Finite :=
  finite_restrictOver_preimage_singleton X.π (X.finite_preimage_singleton _)

/-- Every fibre of the restricted cover has `n` points. -/
theorem natCard_restrict_preimage_singleton (z : ThricePuncturedSphere) :
    Nat.card (X.restrict ⁻¹' {z}) = n := by
  rw [Nat.card_coe_set_eq, restrict, ncard_restrictOver_preimage_singleton]
  apply X.natCard_preimage_singleton
  have hz : toOnePoint z ∈ markedᶜ := by
    rw [← range_toOnePoint]
    exact mem_range_self z
  simpa only [mem_compl_iff] using hz

/-- Removing the fibres over `0`, `1` and `∞` from the connected total space leaves a connected
space. -/
theorem isConnected_preimage_range : IsConnected (X.π ⁻¹' range toOnePoint) := by
  have hfin := X.finite_preimage_marked
  have hpre : IsPreconnected (X.π ⁻¹' marked)ᶜ :=
    isPreconnected_compl_of_isDiscrete hfin.isClosed hfin.isDiscrete fun x _ _ hU ↦
      let ⟨φ, hx⟩ := X.exists_mem_source x
      exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source
        (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) φ hx hU
  have htwo : ((2 : ℂ) : OnePoint ℂ) ∉ marked := by
    norm_num [mem_marked]
  obtain ⟨z, hz⟩ := X.surjective ((2 : ℂ) : OnePoint ℂ)
  have hconn : IsConnected (X.π ⁻¹' marked)ᶜ :=
    ⟨⟨z, fun h ↦ htwo (hz ▸ h)⟩, hpre⟩
  simpa only [range_toOnePoint, preimage_compl] using hconn

/-- The total space of the restricted cover is path connected. -/
instance instPathConnectedSpacePreimageRange :
    PathConnectedSpace (X.π ⁻¹' range toOnePoint) := by
  have := X.isCoveringMap_restrict.isLocalHomeomorph.locallyPathConnectedSpace
  have := isConnected_iff_connectedSpace.1 X.isConnected_preimage_range
  exact pathConnectedSpace_iff_connectedSpace.2 this

/-- Every fibre of the restricted cover can be numbered by `Fin n`. -/
theorem nonempty_restrict_preimage_singleton_equiv (z : ThricePuncturedSphere) :
    Nonempty (X.restrict ⁻¹' {z} ≃ Fin n) := by
  have := (X.finite_restrict_preimage_singleton z).to_subtype
  exact ⟨(Finite.equivFin _).trans (finCongr (X.natCard_restrict_preimage_singleton z))⟩

/-- The connected degree-`n` cover of the thrice-punctured sphere obtained by deleting the
fibres over the three marked points. -/
def connectedCover : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n where
  cover := ConnectedCoveringSpace.mk
    (TopCat.ofHom ⟨X.restrict, X.isCoveringMap_restrict.continuous⟩)
    X.isCoveringMap_restrict
  nonempty_equiv_fin := X.nonempty_restrict_preimage_singleton_equiv basePt

/-- The canonical identification of the packaged connected cover's total space with the
complement of the marked fibres. -/
def connectedCoverHomeomorph :
    (X.connectedCover.cover : TopCat) ≃ₜ X.π ⁻¹' range toOnePoint := by
  unfold connectedCover
  exact Homeomorph.refl _

/-- Under the canonical identification, the packaged cover's projection is the restricted
branched-cover projection. -/
theorem restrict_connectedCoverHomeomorph (z : (X.connectedCover.cover : TopCat)) :
    X.restrict (X.connectedCoverHomeomorph z) = X.connectedCover.cover.proj z := by
  unfold connectedCoverHomeomorph connectedCover
  rfl

/-- Under the canonical identification, the branched-cover projection is the packaged cover's
projection, read in the Riemann sphere. -/
theorem π_connectedCoverHomeomorph (z : (X.connectedCover.cover : TopCat)) :
    X.π (X.connectedCoverHomeomorph z) =
      (((X.connectedCover.cover.proj z : ThricePuncturedSphere) : ℂ) : OnePoint ℂ) := by
  rw [← coe_restrict_apply, restrict_connectedCoverHomeomorph]

/-- **The local degrees over any point add up to the degree.** Over an unmarked point this is the
degree hypothesis; over a marked point `q`, it says that the multiset of local degrees over `q`
is a partition of `n`. -/
theorem finsum_mem_preimage_singleton_localDegree (y : OnePoint ℂ) :
    ∑ᶠ z ∈ X.π ⁻¹' {y}, X.localDegree z = n := by
  set F := X.π ⁻¹' {y}
  have hF : F.Finite := X.finite_preimage_singleton y
  -- Separate the points of the fibre `F` by pairwise disjoint neighbourhoods `V z`, on which the
  -- local degree counts the preimages of each point near `y`.
  obtain ⟨U, hU, hUdisj⟩ := hF.t2_separation
  choose V hVU hVo hzV hV using fun z =>
    (X.isLocalPowerAt_localDegree z).exists_ncard_inter_preimage_eq
      ((hU z).2.mem_nhds (hU z).1)
  -- Since `π` is closed, the fibres near `y` lie in the union of the `V z`.
  have ht : ∀ᶠ y' in 𝓝 y, X.π ⁻¹' {y'} ⊆ ⋃ z ∈ F, V z :=
    X.isProperMap.isClosedMap.eventually_nhds_fiber y fun z hz ↦
      Filter.Eventually.mono ((hVo z).mem_nhds (hzV z)) fun _ hV ↦ mem_biUnion hz hV
  have hnear : ∀ᶠ y' in 𝓝[≠] y, y' ∉ marked ∧ X.π ⁻¹' {y'} ⊆ ⋃ z ∈ F, V z ∧
      ∀ z ∈ F, (V z ∩ X.π ⁻¹' {y'}).ncard = X.localDegree z := by
    have hmarked : (marked \ {y})ᶜ ∈ 𝓝 y :=
      (finite_marked.sdiff).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds hmarked, self_mem_nhdsWithin, nhdsWithin_le_nhds ht,
      hF.eventually_all.2 fun z (hz : X.π z = y) => hz ▸ hV z] with y' hy'm hy'y hy't hy'V
    exact ⟨fun h => hy'm ⟨h, hy'y⟩, hy't, hy'V⟩
  -- Pick an unmarked `y'` near `y`: its `n` preimages are distributed among the `V z`.
  obtain ⟨y', hy'm, hy't, hy'V⟩ := hnear.exists
  have hcover : X.π ⁻¹' {y'} = ⋃ z ∈ F, V z ∩ X.π ⁻¹' {y'} := by
    refine Subset.antisymm (fun z' hz' => ?_) (iUnion₂_subset fun _ _ => inter_subset_right)
    obtain ⟨z, hz, hz'z⟩ := mem_iUnion₂.1 (hy't hz')
    exact mem_biUnion hz ⟨hz'z, hz'⟩
  refine Eq.trans ?_ (X.natCard_preimage_singleton y' hy'm)
  rw [Nat.card_coe_set_eq, hcover,
    hF.ncard_biUnion (fun _ _ => (X.finite_preimage_singleton y').subset inter_subset_right)
      (hUdisj.mono fun z => inter_subset_left.trans (hVU z))]
  exact (finsum_mem_congr rfl hy'V).symm

/-- The degree of a branched cover is positive: an unmarked point has a nonempty finite fibre. -/
theorem ne_zero (X : TopBranchedCover n) : n ≠ 0 := by
  have h2 : ((2 : ℂ) : OnePoint ℂ) ∉ marked := by norm_num [mem_marked]
  obtain ⟨z, hz⟩ := X.surjective ((2 : ℂ) : OnePoint ℂ)
  have := (X.finite_preimage_singleton ((2 : ℂ) : OnePoint ℂ)).to_subtype
  have : Nonempty (X.π ⁻¹' {((2 : ℂ) : OnePoint ℂ)}) := ⟨⟨z, hz⟩⟩
  exact X.natCard_preimage_singleton _ h2 ▸ Nat.card_pos.ne'

/-! ### Ramification partitions -/

/-- The **ramification partition** of a branched cover over a point `y` of the sphere: the
partition of the degree `n` whose parts are the local degrees at the points of the fibre over `y`
(`TauCeti.TopBranchedCover.parts_ramificationPartition`), one part for each point. It is a
partition of `n` because the local degrees over `y` add up to the degree
(`TauCeti.TopBranchedCover.finsum_mem_preimage_singleton_localDegree`). -/
def ramificationPartition (y : OnePoint ℂ) : n.Partition where
  parts := (X.finite_preimage_singleton y).toFinset.val.map X.localDegree
  parts_pos hi := by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hi
    exact X.localDegree_pos z
  parts_sum := by
    rw [← Finset.sum_eq_multiset_sum, ← finsum_mem_eq_finite_toFinset_sum,
      X.finsum_mem_preimage_singleton_localDegree]

/-- The parts of the ramification partition over `y` are the local degrees at the points of the
fibre over `y`. -/
theorem parts_ramificationPartition (y : OnePoint ℂ) :
    (X.ramificationPartition y).parts =
      (X.finite_preimage_singleton y).toFinset.val.map X.localDegree :=
  (rfl)

/-- A number is a part of the ramification partition over `y` exactly when it is the local degree
at some point over `y`. -/
@[simp]
theorem mem_parts_ramificationPartition {y : OnePoint ℂ} {e : ℕ} :
    e ∈ (X.ramificationPartition y).parts ↔ ∃ z, X.π z = y ∧ X.localDegree z = e := by
  simp [parts_ramificationPartition]

/-- The ramification partition over `y` has one part for each point of the fibre over `y`. -/
@[simp]
theorem card_parts_ramificationPartition (y : OnePoint ℂ) :
    (X.ramificationPartition y).parts.card = (X.π ⁻¹' {y}).ncard := by
  rw [parts_ramificationPartition, Multiset.card_map, Finset.card_val,
    ncard_eq_toFinset_card _ (X.finite_preimage_singleton y)]

/-- Away from the marked points the ramification partition is `1ⁿ`: the branched cover is
unramified there. -/
theorem parts_ramificationPartition_of_notMem_marked {y : OnePoint ℂ} (hy : y ∉ marked) :
    (X.ramificationPartition y).parts = Multiset.replicate n 1 := by
  refine Multiset.eq_replicate.2 ⟨?_, fun e he ↦ ?_⟩
  · rw [card_parts_ramificationPartition, ← Nat.card_coe_set_eq, X.natCard_preimage_singleton y hy]
  · obtain ⟨z, rfl, rfl⟩ := X.mem_parts_ramificationPartition.1 he
    exact X.localDegree_eq_one hy

/-! ### Isomorphisms -/

/-- An **isomorphism** of topological branched covers: a homeomorphism of the total spaces
commuting with the branched covering maps. -/
@[ext]
structure Iso (X Y : TopBranchedCover n) where
  /-- The homeomorphism of total spaces. -/
  toHomeomorph : X.Z ≃ₜ Y.Z
  /-- The homeomorphism commutes with the branched covering maps. -/
  π_apply : ∀ z, Y.π (toHomeomorph z) = X.π z

namespace Iso

attribute [simp] π_apply

variable {X} {Y W : TopBranchedCover n}

/-- The identity isomorphism. -/
def refl (X : TopBranchedCover n) : Iso X X :=
  ⟨Homeomorph.refl X.Z, fun _ => rfl⟩

@[simp]
theorem refl_toHomeomorph (X : TopBranchedCover n) :
    (refl X).toHomeomorph = Homeomorph.refl X.Z :=
  (rfl)

/-- The inverse of an isomorphism. -/
def symm (ι : Iso X Y) : Iso Y X :=
  ⟨ι.toHomeomorph.symm, fun z => by rw [← ι.π_apply, Homeomorph.apply_symm_apply]⟩

@[simp]
theorem symm_toHomeomorph (ι : Iso X Y) : ι.symm.toHomeomorph = ι.toHomeomorph.symm :=
  (rfl)

/-- The composite of two isomorphisms. -/
def trans (ι : Iso X Y) (κ : Iso Y W) : Iso X W :=
  ⟨ι.toHomeomorph.trans κ.toHomeomorph, fun z => (κ.π_apply _).trans (ι.π_apply z)⟩

@[simp]
theorem trans_toHomeomorph (ι : Iso X Y) (κ : Iso Y W) :
    (ι.trans κ).toHomeomorph = ι.toHomeomorph.trans κ.toHomeomorph :=
  (rfl)

/-- The homeomorphism of the restricted total spaces induced by an isomorphism of topological
branched covers. -/
def restrict (ι : Iso X Y) : X.π ⁻¹' range toOnePoint ≃ₜ Y.π ⁻¹' range toOnePoint :=
  ι.toHomeomorph.subtype fun z ↦ by simp

@[simp]
theorem coe_restrict_apply (ι : Iso X Y) (z : X.π ⁻¹' range toOnePoint) :
    (ι.restrict z : Y.Z) = ι.toHomeomorph z :=
  (rfl)

@[simp]
theorem refl_restrict (X : TopBranchedCover n) : (refl X).restrict = Homeomorph.refl _ :=
  (rfl)

@[simp]
theorem symm_restrict (ι : Iso X Y) : ι.symm.restrict = ι.restrict.symm :=
  (rfl)

@[simp]
theorem trans_restrict (ι : Iso X Y) (κ : Iso Y W) :
    (ι.trans κ).restrict = ι.restrict.trans κ.restrict :=
  (rfl)

/-- The restriction of an isomorphism of topological branched covers commutes with the
projections to the thrice-punctured sphere. -/
@[simp]
theorem restrict_restrict (ι : Iso X Y) (z : X.π ⁻¹' range toOnePoint) :
    Y.restrict (ι.restrict z) = X.restrict z := by
  apply isOpenEmbedding_toOnePoint.injective
  simp only [toOnePoint_apply, TopBranchedCover.coe_restrict_apply, coe_restrict_apply, π_apply]

/-- The homeomorphism between the packaged total spaces induced by restriction of an isomorphism
of topological branched covers, expressed through their canonical identifications with the
complements of the marked fibres. -/
def connectedCoverHomeomorph (ι : Iso X Y) :
    (X.connectedCover.cover : TopCat) ≃ₜ (Y.connectedCover.cover : TopCat) :=
  X.connectedCoverHomeomorph.trans (ι.restrict.trans Y.connectedCoverHomeomorph.symm)

/-- The restriction of an isomorphism of topological branched covers is an isomorphism of the
associated connected covers of the thrice-punctured sphere. -/
def connectedCoverIso (ι : Iso X Y) : X.connectedCover.cover ≅ Y.connectedCover.cover :=
  CoveringSpace.FullSubcategory.isoMk (TopCat.isoOfHomeo ι.connectedCoverHomeomorph) (by
    ext1 z
    rw [TopCat.comp_app, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply, ContinuousMap.coe_ofClass,
      ← Y.restrict_connectedCoverHomeomorph, ← X.restrict_connectedCoverHomeomorph]
    simp only [connectedCoverHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
      ι.restrict_restrict])

@[simp]
theorem connectedCoverIso_hom_hom_left (ι : Iso X Y) :
    ι.connectedCoverIso.hom.hom.left = (TopCat.isoOfHomeo ι.connectedCoverHomeomorph).hom :=
  CoveringSpace.FullSubcategory.isoMk_hom_hom_left _ _

@[simp]
theorem connectedCoverIso_inv_hom_left (ι : Iso X Y) :
    ι.connectedCoverIso.inv.hom.left = (TopCat.isoOfHomeo ι.connectedCoverHomeomorph).inv :=
  CoveringSpace.FullSubcategory.isoMk_inv_hom_left _ _

/-- Isomorphisms of branched covers preserve local degrees. -/
@[simp]
theorem localDegree_apply (ι : Iso X Y) (z : X.Z) :
    Y.localDegree (ι.toHomeomorph z) = X.localDegree z := by
  have h := (Y.isLocalPowerAt_localDegree (ι.toHomeomorph z)).comp_homeomorph ι.toHomeomorph
  have hπ : ⇑Y.π ∘ ι.toHomeomorph = X.π := funext ι.π_apply
  rw [hπ] at h
  exact (X.localDegree_eq_iff.2 h).symm

/-- Isomorphic branched covers have the same ramification partition over every point. -/
theorem ramificationPartition_eq (ι : Iso X Y) (y : OnePoint ℂ) :
    Y.ramificationPartition y = X.ramificationPartition y := by
  have h : (Y.finite_preimage_singleton y).toFinset =
      (X.finite_preimage_singleton y).toFinset.map ι.toHomeomorph.toEquiv.toEmbedding := by
    ext z
    simp only [Finite.mem_toFinset, mem_preimage, mem_singleton_iff, Finset.mem_map_equiv]
    simp [← ι.π_apply (ι.toHomeomorph.symm z)]
  ext1
  rw [parts_ramificationPartition, parts_ramificationPartition, h, Finset.map_val,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun z _ ↦ ι.localDegree_apply z

end Iso

/-- Branched covers related by isomorphism. -/
instance isoSetoid (n : ℕ) : Setoid (TopBranchedCover n) where
  r X Y := Nonempty (Iso X Y)
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨ι⟩ => ⟨ι.symm⟩, fun ⟨ι⟩ ⟨κ⟩ => ⟨ι.trans κ⟩⟩

/-- Topological branched covers of the sphere of degree `n` with branch values in `{0, 1, ∞}`,
up to isomorphism. -/
def IsoClass (n : ℕ) : Type (u + 1) :=
  Quotient (isoSetoid n)

/-- The isomorphism class of a branched cover. -/
def IsoClass.mk (X : TopBranchedCover n) : IsoClass n :=
  Quotient.mk _ X

/-- Two branched covers have the same isomorphism class exactly when they are isomorphic. -/
@[simp]
theorem IsoClass.mk_eq_mk_iff {X Y : TopBranchedCover n} :
    IsoClass.mk X = IsoClass.mk Y ↔ Nonempty (Iso X Y) :=
  Quotient.eq

/-- Restricting over the thrice-punctured sphere sends an isomorphism class of topological
branched covers to an isomorphism class of connected covers. -/
def IsoClass.restrict : IsoClass n →
    ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n :=
  Quotient.lift (fun X ↦ ConnectedCoverClass.mk X.connectedCover) fun _ _ ⟨ι⟩ ↦
    ConnectedCoverClass.mk_eq_mk_iff.2 ⟨ι.connectedCoverIso⟩

/-- Restriction on isomorphism classes is represented by restriction of branched covers. -/
@[simp]
theorem IsoClass.restrict_mk (X : TopBranchedCover n) :
    IsoClass.restrict (IsoClass.mk X) = ConnectedCoverClass.mk X.connectedCover :=
  (rfl)

/-- Every isomorphism class is the class of a branched cover. -/
theorem IsoClass.mk_surjective : Function.Surjective (IsoClass.mk (n := n)) :=
  Quotient.mk_surjective

/-! ### Uniqueness of the compactification

A branched cover is determined by its unbranched part: every continuous map over the
thrice-punctured sphere between the unbranched parts of two branched covers extends uniquely to
their total spaces. At a point `x` over a marked point `q`, the punctured neighbourhoods of `x` are
connected, so the cluster set of the map at `x` is a connected subset of the finite fibre over `q`:
a single point, which is the limit. -/

section Extend

variable {X} {m : ℕ} {Y : TopBranchedCover m}

/-- At a point `x` of a marked fibre, the unbranched part has preconnected approach regions: `x`
has arbitrarily small neighbourhoods `V` such that `V \ {x}` is connected and contained in the
unbranched part. -/
private theorem exists_mem_nhds_isPreconnected_inter {x : X.Z}
    (hx : x ∉ X.π ⁻¹' range toOnePoint) {s : Set X.Z} (hs : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝 x, t ⊆ s ∧ IsPreconnected (X.π ⁻¹' range toOnePoint ∩ t) := by
  obtain ⟨φ, hφ⟩ := X.exists_mem_source x
  obtain ⟨V, hV, hVs, hVconn⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source
    (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) φ hφ (inter_mem hs
      (X.finite_preimage_marked.sdiff.isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 (mem_singleton x)))
  refine ⟨V, hV, fun z hz ↦ (hVs hz).1, ?_⟩
  convert hVconn.isPreconnected using 1
  -- Within `V`, the only point of a marked fibre is `x` itself.
  ext z
  have hz := @hVs z
  simp only [range_toOnePoint, preimage_compl, mem_compl_iff, mem_preimage, mem_inter_iff,
    Set.mem_sdiff, mem_singleton_iff] at hx hz ⊢
  grind

/-- **Maps of unbranched parts have limits at the marked fibres.** A continuous map over the
thrice-punctured sphere from the unbranched part of `X` to that of `Y` converges, at every point of
the total space of `X`, to a point of the total space of `Y`. -/
private theorem exists_tendsto_comap_val_nhds
    {f : X.π ⁻¹' range toOnePoint → Y.π ⁻¹' range toOnePoint} (hf : Continuous f)
    (hπ : ∀ z, Y.π (f z) = X.π z) (x : X.Z) :
    ∃ y, Tendsto (Subtype.val ∘ f) (comap Subtype.val (𝓝 x)) (𝓝 y) := by
  by_cases hx : x ∈ X.π ⁻¹' range toOnePoint
  · refine ⟨f ⟨x, hx⟩, ?_⟩
    rw [← nhds_subtype_eq_comap]
    exact (continuous_subtype_val.comp hf).continuousAt
  -- At a point `x` of a marked fibre, the cluster set of `f` is connected, since the unbranched
  -- part has preconnected approach regions at `x`, and lies in the finite fibre of `Y` over
  -- `X.π x`. So it has at most one point, and compactness of `Y` turns it into a limit.
  -- Read `f` as a map `g` on the total space of `X`, continuous on the unbranched part.
  obtain ⟨g, hg⟩ : ∃ g : X.Z → Y.Z, ∀ z : X.π ⁻¹' range toOnePoint, g z = f z :=
    ⟨_, X.dense_preimage_range.extend_eq (continuous_subtype_val.comp hf)⟩
  have hgc : ContinuousOn g (X.π ⁻¹' range toOnePoint) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp hf).congr fun z ↦ (hg z).symm
  suffices h : ∃ y, Tendsto g (𝓝[X.π ⁻¹' range toOnePoint] x) (𝓝 y) by
    obtain ⟨y, hy⟩ := h
    refine ⟨y, ?_⟩
    rw [show Subtype.val ∘ f = g ∘ Subtype.val from funext fun z ↦ (hg z).symm,
      ← tendsto_map'_iff, subtype_coe_map_comap]
    exact hy
  refine exists_tendsto_of_clusterSetOn_subsingleton isCompact_univ (mapsTo_univ _ _)
    (X.dense_preimage_range.closure_eq ▸ mem_univ x) ?_
  -- The cluster set of `g` at `x` lies in the finite fibre of `Y` over `X.π x`.
  have hsub : clusterSetOn g (X.π ⁻¹' range toOnePoint) x ⊆ Y.π ⁻¹' {X.π x} := fun y hy ↦ by
    have h := (mem_clusterSetOn_iff.1 hy).continuousAt_comp Y.π.continuous.continuousAt
    have hπg : ⇑Y.π ∘ g =ᶠ[𝓝[X.π ⁻¹' range toOnePoint] x] X.π :=
      eventually_nhdsWithin_of_forall fun z hz ↦ by
        simp only [Function.comp_apply, hg ⟨z, hz⟩, hπ]
    rw [MapClusterPt, Filter.map_congr hπg] at h
    exact eq_of_nhds_neBot (h.neBot.mono (inf_le_inf_left _
      ((X.π.continuous.tendsto x).mono_left nhdsWithin_le_nhds)))
  exact (isPreconnected_clusterSetOn isCompact_univ (mapsTo_univ _ _) hgc
    fun _ ↦ X.exists_mem_nhds_isPreconnected_inter hx).isDiscrete_iff_subsingleton.1
      ((Y.finite_preimage_singleton _).subset hsub).isDiscrete

/-- The extension of a continuous map over the thrice-punctured sphere from the unbranched part of
`X` to that of `Y` to a continuous map of total spaces. It agrees with `f` on the unbranched part
(`TauCeti.TopBranchedCover.extend_apply_val`), commutes with the projections
(`TauCeti.TopBranchedCover.π_extend_apply`), and is the only continuous map with the first property
(`TauCeti.TopBranchedCover.eq_extend`). -/
def extend (f : C(X.π ⁻¹' range toOnePoint, Y.π ⁻¹' range toOnePoint))
    (hπ : ∀ z, Y.π (f z) = X.π z) : C(X.Z, Y.Z) :=
  ⟨X.dense_preimage_range.extend (Subtype.val ∘ f),
    X.dense_preimage_range.continuous_extend (exists_tendsto_comap_val_nhds f.continuous hπ)⟩

variable (f : C(X.π ⁻¹' range toOnePoint, Y.π ⁻¹' range toOnePoint))
  (hπ : ∀ z, Y.π (f z) = X.π z)

/-- On the unbranched part, the extension of `f` is `f`. -/
@[simp]
theorem extend_apply_val (z : X.π ⁻¹' range toOnePoint) : extend f hπ z = f z :=
  X.dense_preimage_range.extend_eq (continuous_subtype_val.comp f.continuous) z

/-- A continuous map of total spaces agreeing with `f` on the unbranched part is the extension
of `f`. -/
theorem eq_extend {g : C(X.Z, Y.Z)} (hg : ∀ z : X.π ⁻¹' range toOnePoint, g z = f z) :
    g = extend f hπ :=
  ContinuousMap.ext <| congrFun (X.dense_preimage_range.extend_unique hg g.continuous).symm

/-- The extension of `f` commutes with the projections. -/
@[simp]
theorem π_extend_apply (x : X.Z) : Y.π (extend f hπ x) = X.π x :=
  congrFun (Continuous.ext_on X.dense_preimage_range (Y.π.continuous.comp (extend f hπ).continuous)
    X.π.continuous fun z hz ↦ by
      simp only [Function.comp_apply]
      rw [← hπ ⟨z, hz⟩, ← extend_apply_val f hπ ⟨z, hz⟩]) x

/-- If `g` is a left inverse of `f` on the unbranched parts, the extension of `g` is a left
inverse of the extension of `f`. -/
theorem extend_apply_extend_apply (g : C(Y.π ⁻¹' range toOnePoint, X.π ⁻¹' range toOnePoint))
    (hg : ∀ z, X.π (g z) = Y.π z) (hgf : ∀ z, g (f z) = z) (x : X.Z) :
    extend g hg (extend f hπ x) = x := by
  have h₁ := eq_extend (ContinuousMap.id _) (fun _ ↦ rfl)
    (g := (extend g hg).comp (extend f hπ)) fun z ↦ by simp [hgf]
  have h₂ := eq_extend (ContinuousMap.id _) (fun _ ↦ rfl) (g := ContinuousMap.id X.Z) fun _ ↦ rfl
  exact DFunLike.congr_fun (h₁.trans h₂.symm) x

end Extend

namespace Iso

variable {X} {Y : TopBranchedCover n}

/-- **Uniqueness of the compactification.** A homeomorphism over the thrice-punctured sphere
between the unbranched parts of two branched covers extends to an isomorphism of the branched
covers. Its restriction is the given homeomorphism
(`TauCeti.TopBranchedCover.Iso.restrict_ofRestrict`), and it is the only isomorphism with this
property (`TauCeti.TopBranchedCover.Iso.restrict_injective`). -/
def ofRestrict (h : X.π ⁻¹' range toOnePoint ≃ₜ Y.π ⁻¹' range toOnePoint)
    (hπ : ∀ z, Y.π (h z) = X.π z) : Iso X Y where
  toHomeomorph :=
    have hπ' (z : Y.π ⁻¹' range toOnePoint) : X.π (h.symm z) = Y.π z := by
      rw [← hπ, Homeomorph.apply_symm_apply]
    { toFun := extend ⟨h, h.continuous⟩ hπ
      invFun := extend ⟨h.symm, h.symm.continuous⟩ hπ'
      left_inv := extend_apply_extend_apply _ _ _ _ h.symm_apply_apply
      right_inv := extend_apply_extend_apply _ _ _ _ h.apply_symm_apply
      continuous_toFun := (extend _ _).continuous
      continuous_invFun := (extend _ _).continuous }
  π_apply := π_extend_apply _ hπ

variable (h : X.π ⁻¹' range toOnePoint ≃ₜ Y.π ⁻¹' range toOnePoint) (hπ : ∀ z, Y.π (h z) = X.π z)

/-- On the unbranched part, the homeomorphism underlying
`TauCeti.TopBranchedCover.Iso.ofRestrict h hπ` is `h`. -/
@[simp]
theorem ofRestrict_toHomeomorph_apply_val (z : X.π ⁻¹' range toOnePoint) :
    (ofRestrict h hπ).toHomeomorph z = h z :=
  extend_apply_val ⟨h, h.continuous⟩ hπ z

/-- On the unbranched part, the inverse of the homeomorphism underlying
`TauCeti.TopBranchedCover.Iso.ofRestrict h hπ` is `h.symm`. -/
@[simp]
theorem ofRestrict_toHomeomorph_symm_apply_val (z : Y.π ⁻¹' range toOnePoint) :
    (ofRestrict h hπ).toHomeomorph.symm z = h.symm z :=
  (ofRestrict h hπ).toHomeomorph.symm_apply_eq.2 <| by
    rw [ofRestrict_toHomeomorph_apply_val, Homeomorph.apply_symm_apply]

/-- On the unbranched part, the extension `TauCeti.TopBranchedCover.Iso.ofRestrict h hπ` is
`h`. -/
@[simp]
theorem restrict_ofRestrict : (ofRestrict h hπ).restrict = h := by
  ext z
  exact ofRestrict_toHomeomorph_apply_val h hπ z

/-- An isomorphism of branched covers is determined by its restriction to the unbranched parts,
which are dense. -/
theorem restrict_injective : Function.Injective (restrict : Iso X Y → _) := by
  intro ι κ hικ
  ext x
  refine congrFun (Continuous.ext_on X.dense_preimage_range ι.toHomeomorph.continuous
    κ.toHomeomorph.continuous fun z hz ↦ ?_) x
  simpa using congrArg Subtype.val (DFunLike.congr_fun hικ ⟨z, hz⟩)

/-- An isomorphism of the connected covers obtained by deleting the marked fibres extends to an
isomorphism of the branched covers. -/
def ofConnectedCoverIso (e : X.connectedCover.cover ≅ Y.connectedCover.cover) : Iso X Y :=
  ofRestrict (X.connectedCoverHomeomorph.symm.trans <|
      (TopCat.homeoOfIso ((CoveringSpace.FullSubcategory.totalSpace _ _).mapIso e)).trans
        Y.connectedCoverHomeomorph) fun z ↦ by
    obtain ⟨w, rfl⟩ := X.connectedCoverHomeomorph.surjective z
    rw [Homeomorph.trans_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
      π_connectedCoverHomeomorph, π_connectedCoverHomeomorph]
    exact congrArg (fun z ↦ (((z : ThricePuncturedSphere) : ℂ) : OnePoint ℂ))
      (CategoryTheory.ConcreteCategory.congr_hom (CoveringSpace.FullSubcategory.w e.hom) w)

/-- On the unbranched parts, `TauCeti.TopBranchedCover.Iso.ofConnectedCoverIso e` is the map of
total spaces underlying `e`. -/
@[simp]
theorem restrict_ofConnectedCoverIso_connectedCoverHomeomorph
    (e : X.connectedCover.cover ≅ Y.connectedCover.cover) (x : (X.connectedCover.cover : TopCat)) :
    (ofConnectedCoverIso e).restrict (X.connectedCoverHomeomorph x) =
      Y.connectedCoverHomeomorph (e.hom.hom.left x) := by
  simp [ofConnectedCoverIso]

/-- Restricting the extension of an isomorphism of connected covers recovers it. -/
@[simp]
theorem connectedCoverIso_ofConnectedCoverIso
    (e : X.connectedCover.cover ≅ Y.connectedCover.cover) :
    (ofConnectedCoverIso e).connectedCoverIso = e := by
  ext x
  simp [connectedCoverHomeomorph]

/-- An isomorphism of branched covers is the extension of its restriction to the connected
covers. -/
@[simp]
theorem ofConnectedCoverIso_connectedCoverIso (ι : Iso X Y) :
    ofConnectedCoverIso ι.connectedCoverIso = ι := by
  refine restrict_injective (Homeomorph.ext fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := X.connectedCoverHomeomorph.surjective z
  simp [connectedCoverHomeomorph]

end Iso

/-- **Uniqueness of the compactification**, on isomorphism classes: a topological branched cover
is determined up to isomorphism by the connected cover of the thrice-punctured sphere obtained by
deleting its marked fibres. -/
theorem IsoClass.restrict_injective : Function.Injective (IsoClass.restrict (n := n)) := by
  intro c c' h
  obtain ⟨X, rfl⟩ := IsoClass.mk_surjective c
  obtain ⟨Y, rfl⟩ := IsoClass.mk_surjective c'
  rw [IsoClass.restrict_mk, IsoClass.restrict_mk, ConnectedCoverClass.mk_eq_mk_iff] at h
  obtain ⟨e⟩ := h
  exact IsoClass.mk_eq_mk_iff.2 ⟨Iso.ofConnectedCoverIso e⟩

/-! ### Deck transformations -/

/-- **The deck group of a branched cover is the deck group of its unbranched part.** A deck
transformation of `π` restricts to one of the unbranched cover `TauCeti.TopBranchedCover.restrict`,
and every deck transformation of the unbranched cover extends uniquely across the marked fibres
(`TauCeti.TopBranchedCover.Iso.ofRestrict`). -/
def deckMulEquivDeckRestrict : deck X.π ≃* deck X.restrict where
  toFun φ := ⟨(⟨φ.1, congrFun φ.2⟩ : Iso X X).restrict,
    deck.mem_iff.2 (funext (Iso.restrict_restrict _))⟩
  invFun ψ := ⟨(Iso.ofRestrict ψ.1 fun z ↦ by
      simpa using congrArg (fun w : ThricePuncturedSphere ↦ ((w : ℂ) : OnePoint ℂ))
        (deck.proj_smul ψ z)).toHomeomorph,
    deck.mem_iff.2 (funext (Iso.π_apply _))⟩
  left_inv φ := Subtype.ext <| congrArg Iso.toHomeomorph
    (Iso.restrict_injective (Iso.restrict_ofRestrict _ _) :
      Iso.ofRestrict _ _ = (⟨φ.1, congrFun φ.2⟩ : Iso X X))
  right_inv ψ := Subtype.ext (Iso.restrict_ofRestrict _ _)
  map_mul' _ _ := rfl

/-- On the unbranched part, the restriction of a deck transformation is the deck
transformation. -/
@[simp]
theorem coe_deckMulEquivDeckRestrict_apply (φ : deck X.π) (z : X.π ⁻¹' range toOnePoint) :
    ((X.deckMulEquivDeckRestrict φ : X.π ⁻¹' range toOnePoint ≃ₜ X.π ⁻¹' range toOnePoint) z :
      X.Z) = (φ : X.Z ≃ₜ X.Z) z :=
  (rfl)

/-- On the unbranched part, the extension of a deck transformation of the unbranched cover is that
deck transformation. -/
@[simp]
theorem coe_deckMulEquivDeckRestrict_symm_apply (ψ : deck X.restrict)
    (z : X.π ⁻¹' range toOnePoint) :
    (X.deckMulEquivDeckRestrict.symm ψ : X.Z ≃ₜ X.Z) z =
      ((ψ : X.π ⁻¹' range toOnePoint ≃ₜ X.π ⁻¹' range toOnePoint) z : X.Z) :=
  Iso.ofRestrict_toHomeomorph_apply_val _ _ z


/-! ### The sphere over itself -/

/-- The sphere `OnePoint ℂ` over itself by the identity: the topological branched cover of
degree `1`, unbranched everywhere. -/
def sphere : TopBranchedCover 1 where
  Z := OnePoint ℂ
  instSecondCountableTopology := ChartedSpace.secondCountable_of_sigmaCompact ℂ (OnePoint ℂ)
  π := ContinuousMap.id _
  surjective := Function.surjective_id
  isCoveringMapOn := (isLocalHomeomorph_iff_isCoveringMap.1
    (Homeomorph.refl (OnePoint ℂ)).isLocalHomeomorph).isCoveringMapOn.mono (subset_univ _)
  natCard_preimage_singleton _ _ := by simp
  exists_isLocalPowerAt_of_mem_marked z _ := ⟨1, isLocalPowerAt_id (mem_chart_source ℂ z)⟩

/-- The canonical homeomorphism from the total space of `sphere` to the Riemann sphere. -/
def sphereHomeomorph : sphere.Z ≃ₜ OnePoint ℂ :=
  Homeomorph.refl _

/-- The projection of `sphere` is its canonical homeomorphism to the Riemann sphere. -/
@[simp]
theorem sphere_π_apply (z : sphere.Z) : sphere.π z = sphereHomeomorph z := by rfl

/-- The sphere over itself is unbranched: all its local degrees are `1`. -/
@[simp]
theorem sphere_localDegree (z : sphere.Z) : sphere.localDegree z = 1 :=
  sphere.localDegree_eq_iff.2 (isLocalPowerAt_id (mem_chart_source (M := OnePoint ℂ) ℂ z))

end TopBranchedCover

end TauCeti
