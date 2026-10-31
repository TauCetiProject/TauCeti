/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Diffeology.Induced
public import TauCeti.Geometry.Diffeology.Manifold
public import TauCeti.Geometry.Diffeology.Quotient
public import TauCeti.Topology.Algebra.GroupAction.Quotient
public import TauCeti.Topology.Algebra.ProperAction.Slice

/-!
# Slice charts of orbit-space diffeologies

Let a group `G` act on a diffeological space `X` by smooth maps, and give the orbit space `X / G`
its quotient diffeology. Let `H` be a subgroup of `G` and `S` an `H`-invariant subset of `X` that
is open for the D-topology and is a slice for `H`: every element of `G` carrying a point of `S`
into `S` lies in `H`. This file proves that the map `S / H → X / G` sending the `H`-orbit of a
point to its `G`-orbit (`SubMulAction.orbitRelQuotientMap`) is an induction with open image
(`TauCeti.Diffeology.isInduction_orbitRelQuotientMap`,
`TauCeti.Diffeology.isOpen_range_orbitRelQuotientMap`). So near the orbits meeting `S`, the
quotient diffeology of `X / G` is the quotient diffeology of `S / H`. When `S` is also open for a
topology on `X` for which `G` acts continuously, the same map is an open embedding of orbit spaces
with their quotient topologies (`SubMulAction.isOpenEmbedding_orbitRelQuotientMap`).

The point is the converse of smoothness: a plot of `X / G` landing in the image of `S / H`
locally lifts to a plot `ℓ` of `X`. Near a parameter `z`, the point `ℓ z` is a translate `g • s`
of a point `s ∈ S`, so `g⁻¹ • ℓ` is a plot of `X` taking values in the open set `S` near `z`. It
is a local lift of the original plot through `S → S / H`, because points of `S` in the same
`G`-orbit lie in the same `H`-orbit.

For a proper action of a discrete group by smooth maps, `ProperSMul.exists_slice` supplies such
slices `S` for the finite stabilizer `G_x` inside every neighbourhood of every point `x`
(`TauCeti.Diffeology.exists_slice_isInduction_orbitRelQuotientMap`). Hence the quotient
diffeology of the coarse space `M / G` of the action presentation `G ⋉ M` of a smooth manifold `M`
is glued from the finite-chart quotient diffeologies `S / G_x`
(`TauCeti.Diffeology.exists_slice_isInduction_orbitRelQuotientMap_of_contMDiff`). Every element
of `G_x` is retained, including those acting trivially on `S`; the coarse diffeology does not see
this ineffective part of the isotropy.

## Main results

* `TauCeti.Diffeology.dSmooth_orbitRelQuotientMap`: the orbit map of an invariant subset is
  smooth.
* `TauCeti.Diffeology.isInduction_orbitRelQuotientMap`: the orbit map of an open slice is an
  induction.
* `TauCeti.Diffeology.isOpen_range_orbitRelQuotientMap`: its image is open for the D-topology.
* `TauCeti.Diffeology.exists_slice_isInduction_orbitRelQuotientMap`: local finite-quotient charts
  of the orbit space of a proper action of a discrete group by smooth maps.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 1, for inductions and quotient diffeologies.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2, for the local isotropy charts
  of a proper étale groupoid.
-/

public noncomputable section

open Function Set Topology MulAction
open scoped Manifold ContDiff

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {G X : Type*} [Group G] [MulAction G X] [DiffeologicalSpace X] {H : Subgroup G}
  {S : SubMulAction H X}

/-- The orbit map `S / H → X / G` of an invariant subset is smooth for the quotient
diffeologies. -/
theorem dSmooth_orbitRelQuotientMap :
    _root_.Diffeology.DSmooth S.orbitRelQuotientMap := by
  rw [(isSubduction_quotient_mk (orbitRel H S)).dSmooth_iff,
    SubMulAction.orbitRelQuotientMap_comp_mk]
  exact (dSmooth_quotient_mk _).comp dSmooth_subtype_val

/-- **Slice charts of orbit spaces.** Let `G` act on `X` by smooth maps, and let `S` be an
`H`-invariant subset of `X`, open for the D-topology, such that every element of `G` carrying a
point of `S` into `S` lies in `H`. Then the orbit map `S / H → X / G` is an induction: a map into
`S / H` is a plot exactly when its image in `X / G` is a plot. -/
theorem isInduction_orbitRelQuotientMap
    (hsmooth : ∀ g : G, _root_.Diffeology.DSmooth fun x : X ↦ g • x)
    (hS : IsOpen[_root_.Diffeology.dTopology] (S : Set X))
    (hslice : ∀ (g : G) (y : X), y ∈ S → g • y ∈ S → g ∈ H) :
    IsInduction S.orbitRelQuotientMap where
  injective := S.orbitRelQuotientMap_injective hslice
  isPlot_iff {n p} := by
    refine ⟨fun hp ↦ dSmooth_orbitRelQuotientMap n p hp, fun hp ↦ ?_⟩
    refine (isPlot_quotient_iff _).mpr (locallyLifts_iff.mpr fun z _ ↦ ?_)
    -- Near `z`, the image of `p` in `X / G` lifts to a plot `ℓ` of `X`.
    obtain ⟨v, hv, hzv, -, ℓ, hℓ, hℓp⟩ :=
      locallyLifts_iff.mp ((isPlot_quotient_iff _).mp hp) z (mem_univ z)
    obtain ⟨s, hs⟩ := Quotient.exists_rep (p z)
    -- The point `ℓ z` is a translate `g • s` of a representative `s ∈ S` of `p z`.
    have hzs : Quotient.mk (orbitRel G X) (ℓ z) = Quotient.mk (orbitRel G X) (s : X) := by
      rw [← S.orbitRelQuotientMap_mk, hs]
      exact hℓp hzv
    obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact hzs)
    replace hg : g • (s : X) = ℓ z := hg
    -- The plot `g⁻¹ • ℓ` passes through `s`, so it lies in the open set `S` near `z`.
    have hℓ' : IsPlotOn v (fun y ↦ g⁻¹ • ℓ y) := hℓ.dSmooth_comp (hsmooth g⁻¹)
    have hℓ'z : g⁻¹ • ℓ z = s := by rw [← hg, inv_smul_smul]
    have hw : IsOpen (v ∩ (fun y ↦ g⁻¹ • ℓ y) ⁻¹' (S : Set X)) :=
      let : TopologicalSpace X := _root_.Diffeology.dTopology
      (hℓ'.continuousOn hv).isOpen_inter_preimage hv hS
    classical
    let lift : 𝔼ⁿ → S := fun y ↦ if h : g⁻¹ • ℓ y ∈ S then ⟨g⁻¹ • ℓ y, h⟩ else s
    have hlift : ∀ y ∈ v ∩ (fun y ↦ g⁻¹ • ℓ y) ⁻¹' (S : Set X), (lift y : X) = g⁻¹ • ℓ y :=
      fun y hy ↦ by simp [lift, show g⁻¹ • ℓ y ∈ S from hy.2]
    refine ⟨_, hw, ⟨hzv, by simp [hℓ'z]⟩, subset_univ _, lift,
      isPlotOn_subtype_iff.mpr ((hℓ'.mono inter_subset_left).congr fun y hy ↦ (hlift y hy).symm),
      fun y hy ↦ S.orbitRelQuotientMap_injective hslice ?_⟩
    -- Points of `S` in the same `G`-orbit lie in the same `H`-orbit.
    rw [comp_apply, SubMulAction.orbitRelQuotientMap_mk, hlift y hy, ← comp_apply
      (f := S.orbitRelQuotientMap), ← hℓp hy.1]
    exact orbitRel.Quotient.quotient_smul_eq

/-- If `G` acts on `X` by smooth maps and `S` is open for the D-topology, then the image of the
orbit map `S / H → X / G`, the set of orbits meeting `S`, is open for the D-topology. -/
theorem isOpen_range_orbitRelQuotientMap
    (hsmooth : ∀ g : G, _root_.Diffeology.DSmooth fun x : X ↦ g • x)
    (hS : IsOpen[_root_.Diffeology.dTopology] (S : Set X)) :
    IsOpen[_root_.Diffeology.dTopology] (range S.orbitRelQuotientMap) := by
  -- The quotient diffeology is coinduced, so its D-topology is the quotient of the D-topology of
  -- `X`. Since `G` acts by homeomorphisms for the D-topology, the orbit projection is open. The
  -- D-topology is not an instance, so the topological arguments are passed explicitly.
  have htop : (_root_.Diffeology.dTopology : TopologicalSpace (orbitRel.Quotient G X)) =
      .coinduced (Quotient.mk _) _root_.Diffeology.dTopology :=
    dTopology_coinducedDiffeology _
  rw [SubMulAction.range_orbitRelQuotientMap, htop]
  exact @isOpenMap_quotient_mk'_mul G _ X _root_.Diffeology.dTopology _
    (@ContinuousConstSMul.mk G X _root_.Diffeology.dTopology _ fun g ↦ (hsmooth g).continuous) _ hS

/-- **Local finite-quotient charts of orbit spaces.** Let a discrete group `G` act properly on
`X` by smooth maps, where the topology of `X` is its D-topology. Every neighbourhood of a point
`x` contains an open neighbourhood `S` of `x`, invariant under the stabilizer `G_x`, whose orbit
map `S / G_x → X / G` is an induction and an open embedding. The stabilizer is finite, since a
proper action of a discrete group is properly discontinuous
(`ProperSMul.properlyDiscontinuousSMul`). -/
theorem exists_slice_isInduction_orbitRelQuotientMap [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X] [ProperSMul G X]
    (hsmooth : ∀ g : G, _root_.Diffeology.DSmooth fun x : X ↦ g • x) (x : X) {W : Set X}
    (hW : W ∈ 𝓝 x) :
    ∃ S : SubMulAction (stabilizer G x) X, IsOpen (S : Set X) ∧ x ∈ S ∧ (S : Set X) ⊆ W ∧
      IsInduction S.orbitRelQuotientMap ∧ IsOpenEmbedding S.orbitRelQuotientMap := by
  obtain ⟨S, hSo, hxS, hSW, hslice⟩ := ProperSMul.exists_slice G x hW
  exact ⟨S, hSo, hxS, hSW, isInduction_orbitRelQuotientMap hsmooth
    ((_root_.Diffeology.IsDTopologyCompatible.dTop_eq X).symm ▸ hSo) hslice,
    S.isOpenEmbedding_orbitRelQuotientMap hSo hslice⟩

/-- **Local finite-quotient charts of the coarse diffeology of a manifold action.** Let a
discrete group `G` act properly by smooth maps on a finite-dimensional smooth manifold `M`, whose
diffeology is its manifold diffeology. Every neighbourhood of a point `x` contains an open
neighbourhood `S` of `x`, invariant under the finite stabilizer `G_x`, whose orbit map
`S / G_x → M / G` is an induction and an open embedding. So the quotient diffeology of `M / G` is
glued from the quotient diffeologies of the finite quotient charts `S / G_x`. -/
theorem exists_slice_isInduction_orbitRelQuotientMap_of_contMDiff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [DiffeologicalSpace M] [IsContMDiffCompatible E M]
    [MulAction G M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ G M] [TopologicalSpace G] [DiscreteTopology G]
    [ProperSMul G M] (x : M) {W : Set M} (hW : W ∈ 𝓝 x) :
    ∃ S : SubMulAction (stabilizer G x) M, IsOpen (S : Set M) ∧ x ∈ S ∧ (S : Set M) ⊆ W ∧
      IsInduction S.orbitRelQuotientMap ∧ IsOpenEmbedding S.orbitRelQuotientMap :=
  exists_slice_isInduction_orbitRelQuotientMap
    (fun g ↦ (contMDiff_const_smul (I := 𝓘(ℝ, E)) (n := ∞) g).dSmooth) x hW

end TauCeti.Diffeology
