/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
import TauCeti.AlgebraicTopology.Homotopy.WhiteheadTower
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Homotopy groups of acyclic spaces along the Whitehead tower

Serre's theorems that the homotopy groups of a simply connected space are uniquely two-divisible
when its mod-two homology vanishes, or torsion when its rational homology vanishes, share one
argument, which climbs the Whitehead tower one homotopy group at a time. This file proves it once,
for a ring of coefficients `k` and a property `P` of abelian groups invariant under isomorphism
(`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`), with the space, the ring and the
groups in one arbitrary universe. It needs two inputs:

* **the first homotopy group:** if `Z` is `(n + 1)`-connected and has the `k`-homology of a point,
  then `πₙ₊₂(Z)` has the property `P`; this comes from the Hurewicz isomorphism
  `πₙ₊₂(Z) ≅ Hₙ₊₂(Z; ℤ)` and a change of coefficients;
* **Eilenberg--Mac Lane spaces:** every `K(A, n)` space, `n ≥ 1`, of a group `A` with the property
  `P` has the `k`-homology of a point.

The step up the tower is `TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`: the
projection `Z⟨n + 2⟩ → Z` from the `(n + 2)`-connected cover is a fibration whose fibres are
`K(πₙ₊₂(Z), n + 1)` spaces (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). When
these are `k`-acyclic it is a `k`-homology isomorphism, so the cover is `k`-acyclic as well. The
cover is `(n + 2)`-connected and has the homotopy groups of `Z` above `n + 2`, so the first input
applies to it in the next degree. This is the shared induction along the Whitehead tower,
`TauCeti.whiteheadTower_induction`, which replaces each stage by its CW approximation.

The Eilenberg--Mac Lane fibre sits over the `(n + 1)`-connected stage `Z`, never over the original
space: only the fibrations `K(πₙ₊₂ Z, n + 1) → Z⟨n + 2⟩ → Z` between successive stages are used,
and no spectral sequence is needed.

## Main results

* `TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`: the `(n + 2)`-connected cover
  of an `(n + 1)`-connected Hausdorff `k`-acyclic space is `k`-acyclic when the
  `K(πₙ₊₂, n + 1)` spaces are.
* `TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`: given the two inputs, every
  homotopy group `πₙ₊₂` of a simply connected `k`-acyclic space has the property `P`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- **The `(n + 2)`-connected cover of a `k`-acyclic space.** Let `X` be a Hausdorff,
path-connected space whose homotopy groups `πⱼ` vanish for `1 ≤ j < m + 2`, and which has the
`k`-homology of a point. If every `K(πₘ₊₂(X), m + 1)` space has the `k`-homology of a point, then
so has the `(m + 2)`-connected cover `X⟨m + 2⟩`. -/
theorem subsingleton_singularHomology_nConnectedCover_of_fiber (X : TopCat.{u}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ j, j ≠ 0 → j < m + 2 → Subsingleton (π_ j X x))
    (hXk : ∀ i, Subsingleton (((singularChains k).obj X).homology (i + 1)))
    (hK : ∀ {Y : Type u} [TopologicalSpace Y] {y : Y},
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Y y →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (i : ℕ) :
    Subsingleton (((singularChains k).obj (nConnectedCover (m + 2) X x)).homology (i + 1)) := by
  -- Every fibre of the projection is a `K(πₘ₊₂(X), m + 1)` space, so it is `k`-acyclic and the
  -- projection is a `k`-homology isomorphism.
  have := isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber k
    (serreFibrations_nConnectedCoverProj (m + 2) X x)
    (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX) hK (i + 1)
  exact (subsingleton_singularChains_homology_iff_of_isIso _
    (nConnectedCoverProj (m + 2) X x) _).2 (hXk i)

variable (P : (G : Type u) → [AddCommGroup G] → Prop)
  (hP : ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H], (G ≃+ H) → P G → P H)
  (hπ : ∀ {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ),
    (∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z)) →
    (∀ i, Subsingleton (((singularChains k).obj (TopCat.of Z)).homology (i + 1))) →
      P (Additive (π_ (n + 2) Z z)))
  (hK : ∀ {A : Type u} [AddCommGroup A], P A → ∀ {n : ℕ} [NeZero n] {X : Type u}
    [TopologicalSpace X] {x : X}, IsEilenbergMacLaneSpace (Multiplicative A) n X x →
      ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)))

include hP hπ hK in
/-- **Homotopy groups of acyclic spaces.** Let `k` be a commutative ring and `P` a property of
abelian groups invariant under isomorphism. Suppose that

* for every `(n + 1)`-connected space `Z` with the `k`-homology of a point, `πₙ₊₂(Z)` has the
  property `P`, and
* every `K(A, n)` space, `n ≥ 1`, of an abelian group `A` with the property `P` has the
  `k`-homology of a point.

Then every homotopy group `πₙ₊₂(Y)` of a simply connected space `Y` with the `k`-homology of a
point has the property `P`. No CW structure is assumed on `Y`. -/
theorem prop_homotopyGroup_of_subsingleton_singularHomology {Y : Type u} [TopologicalSpace Y]
    [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : P (Additive (π_ (n + 2) Y y)) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (j : ℕ) (hj0 : j ≠ 0) (hj : j < 2) : Subsingleton (π_ j Y y) := by
    obtain rfl : j = 1 := by omega
    exact HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  -- Climb the Whitehead tower: the first homotopy group of each stage has `P`, so the fibres of its
  -- next cover are `k`-acyclic, and so is the cover.
  refine whiteheadTower_induction (N := n)
    (fun X ↦ ∀ i, Subsingleton (((singularChains k).obj X).homology (i + 1)))
    (fun G _ ↦ P (Additive G)) (fun _ _ f hf hXk i ↦ ?_) (fun _ _ _ _ e ↦ hP e.toAdditive)
    (fun z hZ hZk ↦ hπ z n hZ hZk)
    (fun m _ X _ _ x hX hXk ↦ subsingleton_singularHomology_nConnectedCover_of_fiber k X x m hX hXk
      fun hY ↦ hK (hπ x m hX hXk) (hY.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm))
    (Nat.zero_le n) y h₁ hY
  -- A weak homotopy equivalence is a homology isomorphism.
  have := hf.isIso_singularHomologyMap (ModuleCat.of k k) (i + 1)
  exact (subsingleton_singularChains_homology_iff_of_isIso _ f _).2 (hXk i)

end TauCeti
