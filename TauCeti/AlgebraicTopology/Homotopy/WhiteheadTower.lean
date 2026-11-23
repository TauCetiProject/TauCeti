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
* `TauCeti.exists_nConnectedCover_map`: finite Whitehead tower up to degree `n + 1`, constructing an
  `(n + 1)`-connected Hausdorff cover `q : Z → Y` in any morphism property `M` stable under weak
  homotopy equivalences, composition, and `nConnectedCoverProj`.

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

/-- **Finite Whitehead tower up to degree `n + 1`.** Given a morphism property `M` on `TopCat.{u}`
containing weak homotopy equivalences (`hW`), closed under composition (`hcomp`), and containing
each `(m + 2)`-connected cover projection (`hstep`) along an isomorphism-invariant property `Q`
satisfied by `π_{m + 2}(Y, y)` for `m < n`, any simply connected space `(Y, y)` admits a
Hausdorff `(n + 1)`-connected space `(Z, z)` and a based map `q : Z → Y` in `M` which is bijective
on `π_k` for `k ≥ n + 2`. -/
theorem exists_nConnectedCover_map
    (M : ∀ ⦃A B : TopCat.{u}⦄, (A ⟶ B) → Prop)
    (hW : ∀ ⦃A B : TopCat.{u}⦄ (f : A ⟶ B), f.hom.IsWeakHomotopyEquivalence → M f)
    (hcomp : ∀ ⦃A B C : TopCat.{u}⦄ {f : A ⟶ B} {g : B ⟶ C}, M f → M g → M (f ≫ g))
    (Q : ∀ (G : Type u) [CommGroup G], Prop)
    (hQ : ∀ ⦃G G' : Type u⦄ [CommGroup G] [CommGroup G'], G ≃* G' → Q G → Q G')
    (hstep : ∀ (Z : Type u) [TopologicalSpace Z] [T2Space Z] [PathConnectedSpace Z] (z : Z)
      (m : ℕ), (∀ k, k ≠ 0 → k < m + 2 → Subsingleton (π_ k Z z)) →
        Q (π_ (m + 2) Z z) → M (nConnectedCoverProj (m + 2) (TopCat.of Z) z))
    {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y) [Subsingleton (π_ 1 Y y)] :
    ∀ (n : ℕ), (∀ m < n, Q (π_ (m + 2) Y y)) →
      ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : T2Space Z) (_ : PathConnectedSpace Z)
        (z : Z) (q : C(Z, Y)) (hqz : q z = y),
        M (TopCat.ofHom q) ∧
        (∀ k < n + 2, Subsingleton (π_ k Z z)) ∧
        (∀ k, n + 2 ≤ k → Function.Bijective (HomotopyGroup.map (N := Fin k) q hqz))
  | 0, _ => by
    let q := (cwApproximationMap (TopCat.of Y) y).hom
    have hqz := cwApproximationMap_cwApproximationBasepoint (TopCat.of Y) y
    refine ⟨cwApproximation (TopCat.of Y) y, inferInstance, inferInstance, inferInstance,
      cwApproximationBasepoint (TopCat.of Y) y, q, hqz,
      hW _ (isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Y) y), fun k hk ↦ ?_,
      fun k hk ↦ ?_⟩
    · match k with
      | 0 => exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero _).1 inferInstance
      | 1 => exact ((HomotopyGroup.bijective_map_congr rfl rfl hqz).mp
          (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y 0 _)).1.subsingleton
      | k + 2 => omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (HomotopyGroup.bijective_map_congr rfl rfl hqz).mp
        (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y j _)
  | n + 1, hπ => by
    obtain ⟨Z, _, _, _, z, q, hqz, hMq, hZconn, hZbij⟩ :=
      exists_nConnectedCover_map M hW hcomp Q hQ hstep y n fun m hm ↦ hπ m (Nat.lt_succ_of_lt hm)
    let z' := nConnectedCoverBasepoint (n + 2) (TopCat.of Z) z
    let p := nConnectedCoverProj (n + 2) (TopCat.of Z) z
    have hpz' : p.hom z' = z := nConnectedCoverProj_nConnectedCoverBasepoint (n + 2) (TopCat.of Z) z
    have hq'z' : (q.comp p.hom) z' = y := (congrArg q hpz').trans hqz
    have hQZ : Q (π_ (n + 2) Z z) :=
      hQ (MulEquiv.ofBijective (HomotopyGroup.mapHom (N := Fin (n + 2)) q hqz)
        (hZbij (n + 2) le_rfl)).symm (hπ n (Nat.lt_succ_self n))
    refine ⟨nConnectedCover (n + 2) (TopCat.of Z) z, inferInstance, inferInstance,
      pathConnectedSpace_nConnectedCover (n + 2) (TopCat.of Z) z, z', q.comp p.hom, hq'z',
      hcomp (hstep Z z n (fun k _ hk ↦ hZconn k hk) hQZ) hMq,
      fun k hk ↦ subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2)
        (TopCat.of Z) z z' (Nat.lt_succ_iff.1 hk),
      fun k hk ↦ ?_⟩
    rw [(HomotopyGroup.map_comp_map q hqz p.hom hpz').symm]
    exact (hZbij k (Nat.le_of_succ_le hk)).comp
      (bijective_homotopyGroupMap_nConnectedCoverProj (n + 2) (TopCat.of Z) z z' hpz'
        (Nat.lt_of_succ_le hk))

end TauCeti
