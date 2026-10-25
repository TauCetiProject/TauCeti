/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.WedgeSum
public import TauCeti.AlgebraicTopology.UniversalCover.Covering
public import TauCeti.Topology.CWComplex.Classical.Covering
public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated
public import TauCeti.Topology.CWComplex.Classical.WedgeCircles

/-!
# One-dimensional CW complexes are aspherical

A path-connected CW complex `X` with no cells of dimension at least `2`, that is a connected
graph, is aspherical (`TauCeti.isAspherical_of_forall_isEmpty_cell`). In particular a wedge of
circles indexed by `S` is a `K(F, 1)` for the free group `F` on `S`
(`TauCeti.WedgeSum.isEilenbergMacLaneSpaceOne_circle`), with no finiteness hypothesis on `S`.

The proof passes to the universal cover `Y` of `X`, which exists because `X` is locally
path-connected and semilocally simply connected. The CW structure of `X` lifts to `Y`, cell by
cell (`TauCeti.cwComplexPreimage`), so `Y` is again a CW complex with no cells of dimension at
least `2`. Its singular homology therefore vanishes in every degree at least `2`
(`TauCeti.isZero_singularHomology_complexBasePair_of_isEmpty_cell`), and since `Y` is simply
connected, the Hurewicz theorem shows that all of its homotopy groups vanish
(`TauCeti.subsingleton_homotopyGroup_of_isZero_homology_singularChains`). A covering map is an
isomorphism on homotopy groups in dimensions at least `2`, so those of `X` vanish too. This is a
homological form of the classical argument that the universal cover of a connected graph is a
tree, hence contractible.

Every CW complex is semilocally simply connected; here this is a hypothesis, which a wedge of
circles satisfies (`TauCeti.WedgeSum.instSemilocallySimplyConnectedSpaceCircle`). The spaces lie in
`Type`, as the Hurewicz theorem is available there.

## Main results

* `TauCeti.isAspherical_of_forall_isEmpty_cell`: a path-connected, semilocally simply connected
  CW complex with no cells of dimension at least `2` is aspherical.
* `TauCeti.WedgeSum.isEilenbergMacLaneSpaceOne_circle`: a wedge of circles is a `K(F, 1)` for the
  free group on its circles.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.A (covering spaces of graphs, and trees are contractible) and Section 1.B, the first
  examples of `K(G, 1)` spaces (a connected graph is a `K(G, 1)` with `G` free).
-/

public section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

/-- **A connected graph is aspherical.** A path-connected, semilocally simply connected Hausdorff
space with a CW structure having no cells of dimension at least `2` has trivial homotopy groups in
every dimension at least `2`. Its universal cover is a simply connected CW complex with no cells of
dimension at least `2`, so it has no homology in those degrees and, by the Hurewicz theorem, no
homotopy. -/
theorem isAspherical_of_forall_isEmpty_cell {X : Type} [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (h : ∀ n, IsEmpty (cell (univ : Set X) (n + 2))) (x : X) : IsAspherical X x := by
  have hp := UniversalCover.isCoveringMap x
  let := cwComplexPreimage (univ : Set X) hp
  have := hp.t2Space
  -- The lifted CW structure on the universal cover has no cells of dimension at least `2`.
  have hcell (n : ℕ) : IsEmpty (cell (UniversalCover.proj (x₀ := x) ⁻¹' (univ : Set X)) (n + 2)) :=
    (cellPreimageEquiv (univ : Set X) hp (n + 2)).isEmpty
  have : FiniteDimensional (UniversalCover.proj (x₀ := x) ⁻¹' (univ : Set X)) :=
    ⟨Filter.eventually_atTop.2 ⟨2, fun n hn ↦ by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact hcell m⟩⟩
  have hH (n : ℕ) :
      IsZero (((singularChains ℤ).obj (TopCat.of (UniversalCover x))).homology (n + 2)) := by
    -- The homology of the lifted CW complex relative to the empty set vanishes in degree `n + 2`,
    -- and it is the homology of the universal cover.
    have hC := (isZero_singularHomology_complexBasePair_of_isEmpty_cell
      (UniversalCover.proj (x₀ := x) ⁻¹' (univ : Set X)) (ModuleCat.of ℤ ℤ) (n + 2)).of_iso
      (asIso ((complexBasePair (UniversalCover.proj (x₀ := x) ⁻¹' (univ : Set X))).singularHomologyπ
        (ModuleCat.of ℤ ℤ) (n + 2)))
    exact hC.of_iso (((AlgebraicTopology.singularHomologyFunctor _ (n + 2)).obj _).mapIso
      (TopCat.isoOfHomeo ((Homeomorph.setCongr preimage_univ).trans
        (Homeomorph.Set.univ _)))).symm
  have hsurj : Function.Surjective (UniversalCover.proj (x₀ := x)) := by
    rw [← range_eq_univ, UniversalCover.range_proj]
    exact eq_univ_of_forall fun y ↦ PathConnectedSpace.joined x y
  have : Subsingleton (π_ 1 (UniversalCover x) (UniversalCover.basepointLift x)) :=
    HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.mpr inferInstance
  exact hp.isAspherical_of_subsingleton_homotopyGroup hsurj
    (UniversalCover.proj_basepointLift x) fun n ↦
      subsingleton_homotopyGroup_of_isZero_homology_singularChains _ hH (n + 2)

namespace WedgeSum

/-- **A wedge of circles is a `K(F, 1)`** for the free group `F` on the circles, with any number
of circles. The fundamental group is identified with `F` by
`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`, which sends the loop around the `i`-th circle to
the generator `i`. -/
theorem isEilenbergMacLaneSpaceOne_circle (S : Type) :
    IsEilenbergMacLaneSpaceOne (FreeGroup S) (WedgeSum fun _ : S ↦ (1 : Circle))
      (base fun _ : S ↦ (1 : Circle)) :=
  .mk (isAspherical_of_forall_isEmpty_cell (fun _ ↦ isEmpty_cell_circleCWComplex (by lia)) _)
    ⟨circleFundamentalGroupMulEquiv S⟩

end WedgeSum

end TauCeti
