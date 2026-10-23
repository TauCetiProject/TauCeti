/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.Topology.CWComplex.Classical.CWType
import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.Homotopy.Whitehead

/-!
# Uniqueness of `K(G, 1)` spaces of CW type

Two aspherical spaces of CW type with isomorphic fundamental groups are homotopy equivalent, and
the homotopy equivalence can be chosen to realize any prescribed isomorphism
`φ : π₁(X, x) ≃* π₁(Y, y)` (`TauCeti.IsAspherical.exists_homotopyEquiv`). A homotopy equivalence
`e` need not send `x` to `y`, so realizing `φ` means: there is a path `γ` from `e x` to `y` such
that the map induced by `e` on fundamental groups, followed by basepoint change along `γ`, is `φ`.
In particular any two `K(G, 1)` spaces of CW type are homotopy equivalent
(`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`), and every `K(G, 1)` space of CW
type is homotopy equivalent to Milnor's classifying space `TauCeti.classifyingSpace G`, compatibly
with the identifications of both fundamental groups with `G`
(`TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`). So the classifying space is well
defined up to homotopy equivalence among spaces of CW type.

The cellular classifying space of a presentation of `π₁(X, x)` maps into both spaces by pointed
maps realizing any homomorphism of fundamental groups
(`TauCeti.exists_mapOfEq_cellularClassifyingSpace`). Choosing these maps `f` into `X` and `g` into
`Y` to realize an identification `ψ` and `φ ∘ ψ`, both are weak homotopy equivalences, because all
the spaces are aspherical. Since `X` has CW type, the identity of `X` lifts through `f` up to
homotopy to a map `s` from `X` to the cellular classifying space, and `g ∘ s` is a weak homotopy
equivalence between spaces of CW type, hence a homotopy equivalence by Whitehead's theorem. The
homotopy from `f ∘ s` to the identity moves the base point, which is why the realization of `φ`
involves a change of base point
(`ContinuousMap.Homotopy.exists_path_fundamentalGroupMulEquivOfPath_map_comp`).

The hypothesis of CW type on both spaces cannot be dropped: a point and the Warsaw circle are both
path connected with trivial homotopy groups, but they are not homotopy equivalent.

## Main results

* `TauCeti.IsAspherical.exists_homotopyEquiv`: **aspherical spaces of CW type are homotopy
  equivalent by a homotopy equivalence realizing any prescribed isomorphism of fundamental
  groups.**
* `TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`: two `K(G, 1)` spaces of CW type are
  homotopy equivalent.
* `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`: an aspherical space of CW type
  with fundamental group identified with `G` is homotopy equivalent to `classifyingSpace G`,
  compatibly with the identifications of fundamental groups.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Theorem 1B.8
  and Proposition 1B.9, and Section 4.1, Theorem 4.5 and Proposition 4.22.
* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. 9
  (2009), 1585--1622, for the Warsaw circle.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u v

namespace TauCeti

/-- **Uniqueness of aspherical spaces of CW type.** Two aspherical spaces of CW type are homotopy
equivalent by a homotopy equivalence realizing any prescribed isomorphism `φ` of their fundamental
groups: there is a homotopy equivalence `e` and a path `γ` from `e x` to `y` such that the map
induced by `e` on fundamental groups, followed by basepoint change along `γ`, is `φ`.

The hypothesis of CW type on both spaces cannot be dropped: a point and the Warsaw circle are
aspherical with trivial fundamental groups, but they are not homotopy equivalent. -/
theorem IsAspherical.exists_homotopyEquiv {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y} (hX : IsAspherical X x)
    (hY : IsAspherical Y y) (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (e : X ≃ₕ Y) (γ : Path (e.toFun x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map e.toFun x a) = φ a := by
  obtain ⟨R, hC⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
  obtain ⟨ψ⟩ := hC.nonempty_fundamentalGroupMulEquiv
  have : PathConnectedSpace (cellularClassifyingSpace R) := hC.isAspherical.pathConnectedSpace
  have hπ {Z : Type u} [TopologicalSpace Z] {z : Z} (hZ : IsAspherical Z z) :
      ∀ k, 2 ≤ k → Subsingleton (π_ k Z z) := fun k hk ↦ by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact hZ.subsingleton_homotopyGroup n
  -- Pointed maps from the cellular classifying space realizing `ψ` and `φ ∘ ψ`.
  obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_cellularClassifyingSpace R (hπ hX) ψ.toMonoidHom
  obtain ⟨g, hg, hgψ⟩ :=
    exists_mapOfEq_cellularClassifyingSpace R (hπ hY) (ψ.trans φ).toMonoidHom
  have hfw : f.IsWeakHomotopyEquivalence :=
    (hC.isAspherical.isWeakHomotopyEquivalence_iff hX hf).2 (hfψ ▸ ψ.bijective)
  have hgw : g.IsWeakHomotopyEquivalence :=
    (hC.isAspherical.isWeakHomotopyEquivalence_iff hY hg).2 (hgψ ▸ (ψ.trans φ).bijective)
  -- A homotopy right inverse `s` of `f`; then `g ∘ s` is a weak homotopy equivalence.
  obtain ⟨s, ⟨H⟩⟩ := hfw.exists_comp_homotopic (ContinuousMap.id X)
  have hgs : (g.comp s).IsWeakHomotopyEquivalence :=
    hgw.comp (hfw.of_postcomp (ContinuousMap.IsWeakHomotopyEquivalence.id.of_homotopic ⟨H.symm⟩))
  refine ⟨hgs.homotopyEquiv, ?_⟩
  rw [hgs.homotopyEquiv_toFun]
  refine H.exists_path_fundamentalGroupMulEquivOfPath_map_comp hf hg φ.toMonoidHom ?_
  rw [hfψ, hgψ]
  exact (MulEquiv.toMonoidHom_trans ψ φ).symm

/-- **Two `K(G, 1)` spaces of CW type are homotopy equivalent.** See
`TauCeti.IsAspherical.exists_homotopyEquiv` for a homotopy equivalence realizing a prescribed
isomorphism of fundamental groups. -/
theorem IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv {G : Type v} [Group G]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y}
    (hX : IsEilenbergMacLaneSpaceOne G X x) (hY : IsEilenbergMacLaneSpaceOne G Y y) :
    Nonempty (X ≃ₕ Y) := by
  obtain ⟨eX⟩ := hX.nonempty_fundamentalGroupMulEquiv
  obtain ⟨eY⟩ := hY.nonempty_fundamentalGroupMulEquiv
  obtain ⟨e, -⟩ := IsAspherical.exists_homotopyEquiv hX.isAspherical hY.isAspherical
    (eX.trans eY.symm)
  exact ⟨e⟩

/-- **Milnor's classifying space is the unique `K(G, 1)` of CW type.** An aspherical space `X` of
CW type whose fundamental group is identified with `G` by `eX` is homotopy equivalent to
`classifyingSpace G`, by a homotopy equivalence `e` compatible with the identifications: for a
suitable path `γ` from `e x` to the base point, the map induced by `e`, followed by basepoint
change along `γ` and the identification `classifyingSpaceFundamentalGroupMulEquiv G`, is `eX`. -/
theorem IsAspherical.exists_homotopyEquiv_classifyingSpace {G : Type u} [Group G] {X : Type u}
    [TopologicalSpace X] [CWType X] {x : X} (hX : IsAspherical X x)
    (eX : FundamentalGroup X x ≃* G) :
    ∃ (e : X ≃ₕ classifyingSpace G) (γ : Path (e.toFun x) (classifyingSpaceBasepoint G)),
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv G
        (fundamentalGroupMulEquivOfPath γ (map e.toFun x a)) = eX a := by
  obtain ⟨e, γ, h⟩ := hX.exists_homotopyEquiv
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  exact ⟨e, γ, fun a ↦ by rw [h, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]⟩

end TauCeti
