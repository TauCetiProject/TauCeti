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

* **the first homotopy group:** if `Z` is `(n + 1)`-connected and has vanishing `k`-homology in
  degrees `n + 2` and `n + 3`, then `πₙ₊₂(Z)` has the property `P`; this comes from the Hurewicz
  isomorphism `πₙ₊₂(Z) ≅ Hₙ₊₂(Z; ℤ)` and a change of coefficients;
* **Eilenberg--Mac Lane spaces:** every `K(A, n)` space, `n ≥ 1`, of a group `A` with the property
  `P` has the `k`-homology of a point.

The step up the tower is `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_fiber` and
`TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`: the projection `Z⟨n + 2⟩ → Z`
from the `(n + 2)`-connected cover is a fibration whose fibres are `K(πₙ₊₂(Z), n + 1)` spaces
(`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). When these are `k`-acyclic it is a
`k`-homology isomorphism in every degree `q`, so vanishing of `H_q(Z; k)` passes to the cover. The
cover is `(n + 2)`-connected and has the homotopy groups of `Z` above `n + 2`, so the first input
applies to it in the next degree. This is the shared induction along the Whitehead tower,
`TauCeti.whiteheadTower_induction`, which replaces each stage by its CW approximation.

The Eilenberg--Mac Lane fibre sits over the `(n + 1)`-connected stage `Z`, never over the original
space: only the fibrations `K(πₙ₊₂ Z, n + 1) → Z⟨n + 2⟩ → Z` between successive stages are used,
and no spectral sequence is needed.

## Main results

* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_fiber`: the projection from the
  `(n + 2)`-connected cover of an `(n + 1)`-connected Hausdorff space induces an isomorphism on
  `k`-homology in every degree `q` when the `K(πₙ₊₂, n + 1)` spaces are `k`-acyclic.
* `TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`: vanishing of `H_q(X; k)` passes
  to the `(n + 2)`-connected cover under the same hypothesis.
* `TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`: given the two inputs, the
  homotopy group `πₙ₊₂` of a path-connected space with trivial fundamental group and vanishing
  `k`-homology in degrees `2, …, n + 3` has the property `P`.

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

/-- **The projection from the `(m + 2)`-connected cover is a homology isomorphism** when its
`K(πₘ₊₂(X), m + 1)` fibres are `k`-acyclic. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_of_fiber (X : TopCat.{u}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ j, j ≠ 0 → j < m + 2 → Subsingleton (π_ j X x))
    (hK : ∀ {Y : Type u} [TopologicalSpace Y] {y : Y},
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Y y →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (i : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).map
      (nConnectedCoverProj (m + 2) X x)) :=
  isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber k
    (serreFibrations_nConnectedCoverProj (m + 2) X x)
    (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX) hK i

/-- **Connected-cover homology vanishing in a single degree.** Let `X` be a Hausdorff,
path-connected space whose homotopy groups `πⱼ` vanish for `1 ≤ j < m + 2`, and whose `k`-homology
vanishes in degree `q`. If every `K(πₘ₊₂(X), m + 1)` space has the `k`-homology of a point, then
the `(m + 2)`-connected cover `X⟨m + 2⟩` also has vanishing `k`-homology in degree `q`. -/
theorem subsingleton_singularHomology_nConnectedCover_of_fiber (X : TopCat.{u}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ j, j ≠ 0 → j < m + 2 → Subsingleton (π_ j X x))
    (hK : ∀ {Y : Type u} [TopologicalSpace Y] {y : Y},
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Y y →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    {q : ℕ} (hq : Subsingleton (((singularChains k).obj X).homology q)) :
    Subsingleton (((singularChains k).obj (nConnectedCover (m + 2) X x)).homology q) := by
  -- Every fibre of the projection is a `K(πₘ₊₂(X), m + 1)` space, so it is `k`-acyclic and the
  -- projection is a `k`-homology isomorphism.
  have := isIso_singularHomologyMap_nConnectedCoverProj_of_fiber k X x m hX hK q
  exact (subsingleton_singularChains_homology_iff_of_isIso _
    (nConnectedCoverProj (m + 2) X x) _).2 hq

variable (P : (G : Type u) → [AddCommGroup G] → Prop)
  (hP : ∀ {G H : Type u} [AddCommGroup G] [AddCommGroup H], (G ≃+ H) → P G → P H)
  (hπ : ∀ {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ),
    (∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z)) →
    Subsingleton (((singularChains k).obj (TopCat.of Z)).homology (n + 2)) →
    Subsingleton (((singularChains k).obj (TopCat.of Z)).homology (n + 3)) →
      P (Additive (π_ (n + 2) Z z)))
  (hK : ∀ {A : Type u} [AddCommGroup A], P A → ∀ {n : ℕ} [NeZero n] {X : Type u}
    [TopologicalSpace X] {x : X}, IsEilenbergMacLaneSpace (Multiplicative A) n X x →
      ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)))

include hP hπ hK in
/-- **Homotopy groups of acyclic spaces.** Let `k` be a commutative ring and `P` a property of
abelian groups invariant under isomorphism. Suppose that

* for every `(n + 1)`-connected space `Z` with vanishing `k`-homology in degrees `n + 2` and
  `n + 3`, `πₙ₊₂(Z)` has the property `P`, and
* every `K(A, n)` space, `n ≥ 1`, of an abelian group `A` with the property `P` has the
  `k`-homology of a point.

Then the homotopy group `πₙ₊₂(Y, y)` of a path-connected space `Y` with trivial fundamental group
`π₁(Y, y)` and vanishing `k`-homology in degrees `2, …, n + 3` has the property `P`. No CW
structure is assumed on `Y`. -/
theorem prop_homotopyGroup_of_subsingleton_singularHomology {Y : Type u} [TopologicalSpace Y]
    [PathConnectedSpace Y] (y : Y) (hπ₁ : Subsingleton (π_ 1 Y y)) (n : ℕ)
    (hY : ∀ q ≤ n + 1, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (q + 2))) :
    P (Additive (π_ (n + 2) Y y)) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (j : ℕ) (hj0 : j ≠ 0) (hj : j < 2) : Subsingleton (π_ j Y y) := by
    obtain rfl : j = 1 := by omega
    exact hπ₁
  -- Climb the Whitehead tower: the first homotopy group of each stage has `P`, so the fibres of its
  -- next cover are `k`-acyclic, and so is the cover.
  refine whiteheadTower_induction (N := n)
    (fun X ↦ ∀ q ≤ n + 1, Subsingleton (((singularChains k).obj X).homology (q + 2)))
    (fun G _ ↦ P (Additive G)) (fun _ _ f hf hXk q hq ↦ ?_) (fun _ _ _ _ e ↦ hP e.toAdditive)
    (fun z hZ hZk ↦ hπ z n hZ (hZk n (by omega)) (hZk (n + 1) le_rfl))
    (fun m hm X _ _ x hX hXk q hq ↦ subsingleton_singularHomology_nConnectedCover_of_fiber k X x m
      hX (fun hY ↦ hK (hπ x m hX (hXk m (by omega)) (hXk (m + 1) (by omega)))
        (hY.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm))
      (hXk q hq))
    (Nat.zero_le n) y h₁ hY
  -- A weak homotopy equivalence is a homology isomorphism.
  have := hf.isIso_singularHomologyMap (ModuleCat.of k k) (q + 2)
  exact (subsingleton_singularChains_homology_iff_of_isIso _ f _).2 (hXk q hq)

end TauCeti
