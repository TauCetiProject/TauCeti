/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
import TauCeti.AlgebraicTopology.Homotopy.WhiteheadTower
import TauCeti.AlgebraicTopology.Singular.Homotopy.CWApproximation
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Homotopy groups of acyclic spaces along the Whitehead tower

Serre's theorems that the homotopy groups of a space with trivial fundamental group are uniquely
two-divisible or uniquely `m`-divisible when its mod-two or mod-`m` homology vanishes in a finite
range, or torsion when its rational homology vanishes, share one argument, which climbs the
Whitehead tower one homotopy group at a time. This file proves it once, for a ring of coefficients
`k`, a lookahead `r : ℕ`, and a property `P` of abelian groups invariant under isomorphism
(`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`). It needs two inputs:

* **the first homotopy group:** if `Z` is `(n + 1)`-connected and `H_q(Z; k)` vanishes in the
  range `n + 2 ≤ q ≤ n + 2 + r`, then `πₙ₊₂(Z)` has the property `P`; this comes from the Hurewicz
  isomorphism `πₙ₊₂(Z) ≅ Hₙ₊₂(Z; ℤ)` and a change of coefficients;
* **Eilenberg--Mac Lane spaces:** every `K(A, n)` space, `n ≥ 1`, of a group `A` with the property
  `P` has the `k`-homology of a point.

The step up the tower is `TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`: the
projection `Z⟨n + 2⟩ → Z` from the `(n + 2)`-connected cover is a fibration whose fibres are
`K(πₙ₊₂(Z), n + 1)` spaces (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). When
these are `k`-acyclic it is a `k`-homology isomorphism, so the cover inherits `k`-acyclicity in each
degree `i + 1` in the finite range. The cover is `(n + 2)`-connected and has the homotopy groups
of `Z` above `n + 2`, so the first input applies to it in the next degree. Initially the space is
replaced by the CW approximation of its base point's path component, which is path-connected and
preserves positive homotopy groups and homology vanishing; the shared induction along the Whitehead
tower, `TauCeti.whiteheadTower_induction`, then replaces each stage by its CW approximation.

The Eilenberg--Mac Lane fibre sits over the `(n + 1)`-connected stage `Z`, never over the original
space: only the fibrations `K(πₙ₊₂ Z, n + 1) → Z⟨n + 2⟩ → Z` between successive stages are used,
and no spectral sequence is needed.

## Main results

* `TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`: vanishing of `H_{i+1}(-; k)`
  transfers to the `(n + 2)`-connected cover of an `(n + 1)`-connected Hausdorff space when the
  `K(πₙ₊₂, n + 1)` spaces are `k`-acyclic.
* `TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`: given the two inputs, every
  homotopy group `πₙ₊₂(Y, y)` of a pointed space with trivial `π₁(Y, y)` and vanishing
  `k`-homology in `2 ≤ q ≤ n + 2 + r` has the property `P`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

variable (k : Type) [Ring k]

/-- **The `(n + 2)`-connected cover of a `k`-acyclic space.** Let `X` be a Hausdorff,
path-connected space whose homotopy groups `πⱼ` vanish for `1 ≤ j < m + 2`, and whose
`(i + 1)`-st `k`-homology vanishes. If every `K(πₘ₊₂(X), m + 1)` space has the `k`-homology of a
point, then the `(i + 1)`-st `k`-homology of the `(m + 2)`-connected cover `X⟨m + 2⟩` also
vanishes. -/
theorem subsingleton_singularHomology_nConnectedCover_of_fiber (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ j, j ≠ 0 → j < m + 2 → Subsingleton (π_ j X x))
    (hK : ∀ {Y : Type} [TopologicalSpace Y] {y : Y},
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Y y →
        ∀ j, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (j + 1)))
    (i : ℕ) (hXk : Subsingleton (((singularChains k).obj X).homology (i + 1))) :
    Subsingleton (((singularChains k).obj (nConnectedCover (m + 2) X x)).homology (i + 1)) := by
  -- Every fibre of the projection is a `K(πₘ₊₂(X), m + 1)` space, so it is `k`-acyclic and the
  -- projection is a `k`-homology isomorphism.
  have := isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber k
    (serreFibrations_nConnectedCoverProj (m + 2) X x)
    (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX) hK (i + 1)
  exact (subsingleton_singularChains_homology_iff_of_isIso _
    (nConnectedCoverProj (m + 2) X x) _).2 hXk

variable (P : (G : Type) → [AddCommGroup G] → Prop) (r : ℕ)
  (hP : ∀ {G H : Type} [AddCommGroup G] [AddCommGroup H], (G ≃+ H) → P G → P H)
  (hπ : ∀ {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ),
    (∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z)) →
    (∀ q, n + 2 ≤ q → q ≤ n + 2 + r →
      Subsingleton (((singularChains k).obj (TopCat.of Z)).homology q)) →
      P (Additive (π_ (n + 2) Z z)))
  (hK : ∀ {A : Type} [AddCommGroup A], P A → ∀ {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X}, IsEilenbergMacLaneSpace (Multiplicative A) n X x →
      ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)))

include hP hπ hK in
/-- **Homotopy groups of acyclic spaces.** Let `k` be a ring, `r : ℕ`, and `P` a property of
abelian groups invariant under isomorphism. Suppose that

* for every `(n + 1)`-connected space `Z` with vanishing `k`-homology in `n + 2 ≤ q ≤ n + 2 + r`,
  `πₙ₊₂(Z)` has the property `P`, and
* every `K(A, n)` space, `n ≥ 1`, of an abelian group `A` with the property `P` has the
  `k`-homology of a point.

Then every homotopy group `πₙ₊₂(Y, y)` of a pointed space `(Y, y)` with trivial `π₁(Y, y)` and
vanishing `k`-homology in the finite range `2 ≤ q ≤ n + 2 + r` has the property `P`. No Hausdorff,
path-connectedness, or CW structure is assumed on `Y`. -/
theorem prop_homotopyGroup_of_subsingleton_singularHomology {Y : Type} [TopologicalSpace Y]
    (y : Y) [Subsingleton (π_ 1 Y y)] (n : ℕ)
    (hY : ∀ q, 2 ≤ q → q ≤ n + 2 + r →
      Subsingleton (((singularChains k).obj (TopCat.of Y)).homology q)) :
    P (Additive (π_ (n + 2) Y y)) := by
  let X := cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))
  let x₀ := cwApproximationBasepoint (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y))
  have h₁ (j : ℕ) (hj0 : j ≠ 0) (hj : j < 2) : Subsingleton (π_ j X x₀) := by
    obtain rfl : j = 1 := by omega
    exact (cwApproximationPathComponentHomotopyGroupMulEquiv y 0).toEquiv.subsingleton
  have hXk (q : ℕ) (hq1 : 2 ≤ q) (hq2 : q ≤ n + 2 + r) :
      Subsingleton (((singularChains k).obj X).homology q) :=
    ModuleCat.isZero_iff_subsingleton.1 <|
      isZero_singularHomology_cwApproximation_of_isZero y k q <|
        ModuleCat.isZero_iff_subsingleton.2 (hY q hq1 hq2)
  -- Climb the Whitehead tower: the first homotopy group of each stage has `P`, so the fibres of its
  -- next cover are `k`-acyclic, and so is the cover.
  refine hP (cwApproximationPathComponentHomotopyGroupMulEquiv y (n + 1)).toAdditive <|
    whiteheadTower_induction (N := n)
      (fun W ↦ ∀ q, 2 ≤ q → q ≤ n + 2 + r →
        Subsingleton (((singularChains k).obj W).homology q))
      (fun G _ ↦ P (Additive G)) (fun _ _ f hf hWk q hq1 hq2 ↦ ?_)
      (fun _ _ _ _ e ↦ hP e.toAdditive)
      (fun z hZ hZk ↦ hπ z n hZ fun q hq1 hq2 ↦ hZk q (by omega) hq2)
      (fun m _ W _ _ w hW hWk q hq1 hq2 ↦ ?_)
      (Nat.zero_le n) x₀ h₁ hXk
  · -- A weak homotopy equivalence is a homology isomorphism.
    have := hf.isIso_singularHomologyMap (ModuleCat.of k k) q
    exact (subsingleton_singularChains_homology_iff_of_isIso _ f _).2 (hWk q hq1 hq2)
  · -- The fibres of the cover are `k`-acyclic, so `k`-homology vanishing transfers to the cover.
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact subsingleton_singularHomology_nConnectedCover_of_fiber k W w m hW
      (fun hY' ↦ hK (hπ w m hW fun j hj1 hj2 ↦ hWk j (by omega) (by omega))
        (hY'.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm))
      q' (hWk (q' + 1) hq1 hq2)

end TauCeti
