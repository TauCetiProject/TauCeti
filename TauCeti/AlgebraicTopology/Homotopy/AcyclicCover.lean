/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Homotopy groups of acyclic spaces along the Whitehead tower

Serre's theorems that the homotopy groups of a simply connected space are uniquely two-divisible
when its mod-two homology vanishes, or torsion when its rational homology vanishes, share one
argument, which climbs the Whitehead tower one homotopy group at a time. This file proves it once,
for a ring of coefficients `k` and a property `P` of abelian groups invariant under isomorphism
(`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`). It needs two inputs:

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
applies to it in the next degree. Each stage is replaced by its CW approximation, which is
Hausdorff and changes neither homotopy nor homology.

The Eilenberg--Mac Lane fibre sits over the `(n + 1)`-connected stage `Z`, never over the original
space: only the fibrations `K(πₙ₊₂ Z, n + 1) → Z⟨n + 2⟩ → Z` between successive stages are used,
and no spectral sequence is needed.

## Main results

* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_fiber`: the projection from the
  `(m + 2)`-connected cover induces a `k`-homology isomorphism when the `K(πₘ₊₂, m + 1)`
  fibres are `k`-acyclic.
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

namespace TauCeti

variable (k : Type) [CommRing k]

/-- **The projection from the `(m + 2)`-connected cover is a homology isomorphism** when its
`K(πₘ₊₂(X), m + 1)` fibres are `k`-acyclic. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_of_fiber (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ j, j ≠ 0 → j < m + 2 → Subsingleton (π_ j X x))
    (hK : ∀ {Y : Type} [TopologicalSpace Y] {y : Y},
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Y y →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (i : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} k) i).obj (ModuleCat.of k k)).map
      (nConnectedCoverProj (m + 2) X x)) :=
  isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber k
    (serreFibrations_nConnectedCoverProj (m + 2) X x)
    (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX) hK i

/-- **The `(n + 2)`-connected cover of a `k`-acyclic space.** Let `X` be a Hausdorff,
path-connected space whose homotopy groups `πⱼ` vanish for `1 ≤ j < m + 2`, and which has the
`k`-homology of a point. If every `K(πₘ₊₂(X), m + 1)` space has the `k`-homology of a point, then
so has the `(m + 2)`-connected cover `X⟨m + 2⟩`. -/
theorem subsingleton_singularHomology_nConnectedCover_of_fiber (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ j, j ≠ 0 → j < m + 2 → Subsingleton (π_ j X x))
    (hXk : ∀ i, Subsingleton (((singularChains k).obj X).homology (i + 1)))
    (hK : ∀ {Y : Type} [TopologicalSpace Y] {y : Y},
      IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) Y y →
        ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (i : ℕ) :
    Subsingleton (((singularChains k).obj (nConnectedCover (m + 2) X x)).homology (i + 1)) := by
  -- Every fibre of the projection is a `K(πₘ₊₂(X), m + 1)` space, so it is `k`-acyclic and the
  -- projection is a `k`-homology isomorphism.
  have := isIso_singularHomologyMap_nConnectedCoverProj_of_fiber k X x m hX hK (i + 1)
  exact (subsingleton_singularChains_homology_iff_of_isIso _
    (nConnectedCoverProj (m + 2) X x) _).2 (hXk i)

variable (P : (G : Type) → [AddCommGroup G] → Prop)
  (hP : ∀ {G H : Type} [AddCommGroup G] [AddCommGroup H], (G ≃+ H) → P G → P H)
  (hπ : ∀ {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ),
    (∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z)) →
    (∀ i, Subsingleton (((singularChains k).obj (TopCat.of Z)).homology (i + 1))) →
      P (Additive (π_ (n + 2) Z z)))
  (hK : ∀ {A : Type} [AddCommGroup A], P A → ∀ {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X}, IsEilenbergMacLaneSpace (Multiplicative A) n X x →
      ∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)))

include hP hπ hK in
/-- The induction along the Whitehead tower: for an `(n + 1)`-connected `k`-acyclic space, every
homotopy group `π_{N + 2}` with `N ≥ n` has the property `P`. The degree is `N = n + d`, by
induction on `d`. -/
private theorem prop_homotopyGroup_of_add (d : ℕ) :
    ∀ (n : ℕ) {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z),
      (∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z)) →
      (∀ i, Subsingleton (((singularChains k).obj (TopCat.of Z)).homology (i + 1))) →
        ∀ N, N = n + d → P (Additive (π_ (N + 2) Z z)) := by
  induction d with
  | zero =>
    intro n Z _ _ z hZ hZk N hN
    rw [hN]
    exact hπ z n hZ hZk
  | succ d ih =>
    intro n Z _ _ z hZ hZk N hN
    rw [hN]
    -- Replace `Z` by its CW approximation `X`, which is Hausdorff.
    let X := cwApproximation (TopCat.of Z) z
    let f := (cwApproximationMap (TopCat.of Z) z).hom
    let x₀ := cwApproximationBasepoint (TopCat.of Z) z
    have hf : f.IsWeakHomotopyEquivalence :=
      isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Z) z
    -- `f` identifies the homotopy groups of `X` at `x₀` with those of `Z` at `z`.
    let e (j : ℕ) [NeZero j] : π_ j X x₀ ≃* π_ j Z z :=
      cwApproximationHomotopyGroupMulEquiv (TopCat.of Z) z j
    have hX : ∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j X x₀) := fun j hj0 hj ↦ by
      have : NeZero j := ⟨hj0⟩
      have := hZ j hj0 hj
      exact (e j).toEquiv.subsingleton
    -- `f` is a homology isomorphism, so `X` is `k`-acyclic.
    have hXk (i : ℕ) : Subsingleton (((singularChains k).obj X).homology (i + 1)) := by
      have := hf.isIso_singularHomologyMap (ModuleCat.of k k) (i + 1)
      exact (subsingleton_singularChains_homology_iff_of_isIso _
        (cwApproximationMap (TopCat.of Z) z) _).2 (hZk i)
    -- The first homotopy group `πₙ₊₂(X)` has the property `P`, so the fibres of the
    -- `(n + 2)`-connected cover `C` of `X` are `k`-acyclic, and so is `C`.
    have hPX : P (Additive (π_ (n + 2) X x₀)) := hπ x₀ n hX hXk
    let C := nConnectedCover (n + 2) X x₀
    let c₀ := nConnectedCoverBasepoint (n + 2) X x₀
    have hC : ∀ j, j ≠ 0 → j < n + 1 + 2 → Subsingleton (π_ j C c₀) := fun j _ hj ↦
      subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2) X x₀ c₀
        (by omega)
    have hCk := subsingleton_singularHomology_nConnectedCover_of_fiber k X x₀ n hX hXk
      (fun hY ↦ hK hPX (hY.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm))
    -- The cover has the homotopy groups of `X`, hence of `Z`, above dimension `n + 2`.
    exact hP ((nConnectedCoverHomotopyGroupMulEquiv (n + 2) X x₀ _ (by omega)).trans
        (e _)).toAdditive (ih (n + 1) c₀ hC hCk _ (by omega))

include hP hπ hK in
/-- **Homotopy groups of acyclic spaces.** Let `k` be a commutative ring and `P` a property of
abelian groups invariant under isomorphism. Suppose that

* for every `(n + 1)`-connected space `Z` with the `k`-homology of a point, `πₙ₊₂(Z)` has the
  property `P`, and
* every `K(A, n)` space, `n ≥ 1`, of an abelian group `A` with the property `P` has the
  `k`-homology of a point.

Then every homotopy group `πₙ₊₂(Y)` of a simply connected space `Y` with the `k`-homology of a
point has the property `P`. No CW structure is assumed on `Y`. -/
theorem prop_homotopyGroup_of_subsingleton_singularHomology {Y : Type} [TopologicalSpace Y]
    [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : P (Additive (π_ (n + 2) Y y)) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (j : ℕ) (hj0 : j ≠ 0) (hj : j < 2) : Subsingleton (π_ j Y y) := by
    obtain rfl : j = 1 := by omega
    exact HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  exact prop_homotopyGroup_of_add k P hP hπ hK n 0 y h₁ hY n (Nat.zero_add n).symm

end TauCeti
