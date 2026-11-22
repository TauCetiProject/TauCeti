/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover

/-!
# Induction along the Whitehead tower

Many vanishing theorems for homotopy groups are proved one homotopy group at a time, by climbing
the Whitehead tower of a space. Let `H` be a property of spaces, typically a condition on their
homology, and `Q` a property of groups. Suppose that

* **(first homotopy group)** every `(N + 1)`-connected space `Z` with `H Z` has `Q (π_{N+2} Z)`,
  typically by the Hurewicz theorem;
* **(one step up the tower)** for `n < N`, the `(n + 2)`-connected cover `X⟨n + 2⟩` of an
  `(n + 1)`-connected Hausdorff space `X` with `H X` again satisfies `H`, typically by a
  comparison theorem for the fibration `X⟨n + 2⟩ → X`.

Then every `(n + 1)`-connected space `Y` with `H Y`, `n ≤ N`, has `Q (π_{N+2} Y)`
(`TauCeti.whiteheadTower_induction`). The cover `X⟨n + 2⟩` is `(n + 2)`-connected and has the
homotopy groups of `X` above `n + 2`, so the induction runs from `n` up to `N`. Each stage is first
replaced by its CW approximation, which is Hausdorff and weakly homotopy equivalent to it, so `H`
must be invariant under weak homotopy equivalences and `Q` under isomorphisms.

## Main results

* `TauCeti.whiteheadTower_induction`: the induction principle above.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
-/

public section

open CategoryTheory

open scoped Topology Topology.Homotopy

namespace TauCeti

universe u

/-- **Induction along the Whitehead tower.** Let `H` be a property of spaces that passes from the
target to the source of a weak homotopy equivalence, and `Q` an isomorphism-invariant property of
groups. Suppose that every `(N + 1)`-connected space with `H` has `Q (π_{N+2})` (`base`), and that
for `n < N` the `(n + 2)`-connected cover of an `(n + 1)`-connected Hausdorff space with `H` has
`H` (`step`). Then every `(n + 1)`-connected space `Y` with `H Y`, `n ≤ N`, has `Q (π_{N+2} Y)`. -/
theorem whiteheadTower_induction (H : TopCat.{u} → Prop) (Q : ∀ (G : Type u) [CommGroup G], Prop)
    (hH : ∀ ⦃X Y : TopCat.{u}⦄ (f : X ⟶ Y), f.hom.IsWeakHomotopyEquivalence → H Y → H X)
    (hQ : ∀ ⦃G G' : Type u⦄ [CommGroup G] [CommGroup G'], G ≃* G' → Q G → Q G') {N : ℕ}
    (base : ∀ {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z),
      (∀ q, q ≠ 0 → q < N + 2 → Subsingleton (π_ q Z z)) → H (TopCat.of Z) →
        Q (π_ (N + 2) Z z))
    (step : ∀ n < N, ∀ (X : TopCat.{u}) [T2Space X] [PathConnectedSpace X] (x : X),
      (∀ q, q ≠ 0 → q < n + 2 → Subsingleton (π_ q X x)) → H X →
        H (nConnectedCover (n + 2) X x))
    {n : ℕ} (hn : n ≤ N) {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y)
    (hY : ∀ q, q ≠ 0 → q < n + 2 → Subsingleton (π_ q Y y)) (hYH : H (TopCat.of Y)) :
    Q (π_ (N + 2) Y y) := by
  induction hn using Nat.decreasingInduction generalizing Y with
  | self => exact base y hY hYH
  | of_succ n hn ih =>
    -- Replace `Y` by its CW approximation `X`, which is Hausdorff.
    let X := cwApproximation (TopCat.of Y) y
    let f := cwApproximationMap (TopCat.of Y) y
    let x₀ := cwApproximationBasepoint (TopCat.of Y) y
    have hf : f.hom.IsWeakHomotopyEquivalence :=
      isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Y) y
    -- `f` identifies the homotopy groups of `X` at `x₀` with those of `Y` at `y`.
    let e (q : ℕ) [NeZero q] : π_ q X x₀ ≃* π_ q Y y :=
      cwApproximationHomotopyGroupMulEquiv (TopCat.of Y) y q
    have hX : ∀ q, q ≠ 0 → q < n + 2 → Subsingleton (π_ q X x₀) := fun q hq0 hq ↦ by
      have : NeZero q := ⟨hq0⟩
      have := hY q hq0 hq
      exact (e q).toEquiv.subsingleton
    -- The `(n + 2)`-connected cover `C` of `X` is `(n + 2)`-connected and satisfies `H`.
    let C := nConnectedCover (n + 2) X x₀
    let c₀ := nConnectedCoverBasepoint (n + 2) X x₀
    have hC : ∀ q, q ≠ 0 → q < n + 1 + 2 → Subsingleton (π_ q C c₀) := fun q _ hq ↦
      subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2) X x₀ c₀
        (by omega)
    -- The cover has the homotopy groups of `X`, hence of `Y`, above dimension `n + 2`.
    exact hQ ((nConnectedCoverHomotopyGroupMulEquiv (n + 2) X x₀ _ (by omega)).trans (e _))
      (ih c₀ hC (step n hn X x₀ hX (hH f hf hYH)))

end TauCeti
