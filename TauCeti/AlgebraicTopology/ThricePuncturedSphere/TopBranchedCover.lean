/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint
public import TauCeti.Topology.Covering.LocalPower

import Mathlib.Data.Set.Card.Arithmetic

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
recording how sheets coalesce over branch values.

The data carries no atlas. The local models at marked points and the covering map elsewhere
already provide a chart around every point (`TauCeti.TopBranchedCover.exists_mem_source`), so `Z`
is a topological surface, and properness of `π` is a consequence of compactness
(`TauCeti.TopBranchedCover.isProperMap`).

## Main definitions

* `TauCeti.ThricePuncturedSphere.marked`: the marked points `0`, `1`, `∞` of `OnePoint ℂ`.
* `TauCeti.TopBranchedCover n`: a topological branched cover of the sphere of degree `n` with
  branch values in `{0, 1, ∞}`.
* `TauCeti.TopBranchedCover.Iso`: isomorphisms, homeomorphisms commuting with the projections.
* `TauCeti.TopBranchedCover.localDegree`: the local degree at a point.
* `TauCeti.TopBranchedCover.sphere`: the sphere over itself, of degree `1`.

## Main results

* `TauCeti.TopBranchedCover.localDegree_eq_iff`: the local degree is the unique exponent of a
  local power model.
* `TauCeti.TopBranchedCover.localDegree_eq_one`: off the marked fibres the local degree is `1`.
* `TauCeti.TopBranchedCover.finite_preimage_singleton`: every fibre is finite.
* `TauCeti.TopBranchedCover.finsum_mem_preimage_singleton_localDegree`: the local degrees over
  any point sum to the degree.
* `TauCeti.TopBranchedCover.Iso.localDegree_apply`: isomorphisms preserve local degrees.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2 (branched coverings, their local degrees, and the compactification of finite covers of a
  punctured surface).
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
structure TopBranchedCover (n : ℕ) where
  /-- The total space. -/
  Z : Type
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
  -- Away from the `V z`, the image of `π` is a compact set missing `y`.
  have hK : IsClosed (X.π '' (⋃ z ∈ F, V z)ᶜ) :=
    ((isOpen_biUnion fun z _ => hVo z).isClosed_compl.isCompact.image X.π.continuous).isClosed
  have hyK : y ∉ X.π '' (⋃ z ∈ F, V z)ᶜ := fun ⟨z, hzK, hz⟩ => hzK (mem_biUnion hz (hzV z))
  have hnear : ∀ᶠ y' in 𝓝[≠] y, y' ∉ marked ∧ y' ∉ X.π '' (⋃ z ∈ F, V z)ᶜ ∧
      ∀ z ∈ F, (V z ∩ X.π ⁻¹' {y'}).ncard = X.localDegree z := by
    have hmarked : (marked \ {y})ᶜ ∈ 𝓝 y :=
      (finite_marked.sdiff).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds hmarked, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hK.isOpen_compl.mem_nhds hyK),
      hF.eventually_all.2 fun z (hz : X.π z = y) => hz ▸ hV z] with y' hy'm hy'y hy'K hy'V
    exact ⟨fun h => hy'm ⟨h, hy'y⟩, hy'K, hy'V⟩
  -- Pick an unmarked `y'` near `y`: its `n` preimages are distributed among the `V z`.
  obtain ⟨y', hy'm, hy'K, hy'V⟩ := hnear.exists
  have hcover : X.π ⁻¹' {y'} = ⋃ z ∈ F, V z ∩ X.π ⁻¹' {y'} := by
    refine Subset.antisymm (fun z' hz' => ?_) (iUnion₂_subset fun _ _ => inter_subset_right)
    have hz'V : z' ∈ ⋃ z ∈ F, V z := by_contra fun h => hy'K ⟨z', h, hz'⟩
    obtain ⟨z, hz, hz'z⟩ := mem_iUnion₂.1 hz'V
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

/-- Isomorphisms of branched covers preserve local degrees. -/
@[simp]
theorem localDegree_apply (ι : Iso X Y) (z : X.Z) :
    Y.localDegree (ι.toHomeomorph z) = X.localDegree z := by
  have h := (Y.isLocalPowerAt_localDegree (ι.toHomeomorph z)).comp_homeomorph ι.toHomeomorph
  have hπ : ⇑Y.π ∘ ι.toHomeomorph = X.π := funext ι.π_apply
  rw [hπ] at h
  exact (X.localDegree_eq_iff.2 h).symm

end Iso

/-! ### The sphere over itself -/

/-- The identity of the sphere is locally the first power map. -/
private theorem isLocalPowerAt_id (z : OnePoint ℂ) : IsLocalPowerAt (id : OnePoint ℂ → _) z 1 :=
  (Homeomorph.refl (OnePoint ℂ)).isLocalHomeomorph.isLocalHomeomorphOn.isLocalPowerAt_one
    (s := univ) (mem_univ z) (mem_chart_source ℂ z)

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
  exists_isLocalPowerAt_of_mem_marked z _ := ⟨1, isLocalPowerAt_id z⟩

/-- The canonical homeomorphism from the total space of `sphere` to the Riemann sphere. -/
def sphereHomeomorph : sphere.Z ≃ₜ OnePoint ℂ :=
  Homeomorph.refl _

/-- The projection of `sphere` is its canonical homeomorphism to the Riemann sphere. -/
@[simp]
theorem sphere_π_apply (z : sphere.Z) : sphere.π z = sphereHomeomorph z := by rfl

/-- The sphere over itself is unbranched: all its local degrees are `1`. -/
@[simp]
theorem sphere_localDegree (z : sphere.Z) : sphere.localDegree z = 1 :=
  sphere.localDegree_eq_iff.2 (isLocalPowerAt_id z)

end TopBranchedCover

end TauCeti
