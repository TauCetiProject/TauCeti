/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.MappingPath.Exact

/-!
# The `n`-connected cover of a space

Let `X` be a Hausdorff space with a base point `x` and let `n` be a natural number. Attaching
cells of dimension at least `n + 2` to `X` kills its homotopy groups above dimension `n` and keeps
the others (`TauCeti.killHomotopyGroups`); this is the `n`-th Postnikov section `j : X → Pₙ X`.
The **`n`-connected cover** `X⟨n⟩` of `X` (`TauCeti.nConnectedCover n X x`) is the homotopy fibre
of `j` over `j x`: the space of the points `z` of `X` together with a path from `j z` to `j x` in
`Pₙ X`. Its projection `X⟨n⟩ → X`, `(z, γ) ↦ z` (`TauCeti.nConnectedCoverProj`), is a Hurewicz
fibration whose fibre over `x` is the loop space of `Pₙ X`, and

* `X⟨n⟩` is `n`-connected: its homotopy groups `πₖ` vanish for `1 ≤ k ≤ n`
  (`TauCeti.subsingleton_homotopyGroup_nConnectedCover`), and it is path-connected when `X` is
  (`TauCeti.pathConnectedSpace_nConnectedCover`);
* the projection induces an isomorphism `πₖ(X⟨n⟩) ≅ πₖ(X)` for every `k > n`
  (`TauCeti.nConnectedCoverHomotopyGroupMulEquiv`).

No connectivity hypothesis on `X` is needed for these. When `X` is `(n - 1)`-connected, `Pₙ X` is
an Eilenberg--Mac Lane space `K(πₙ X, n)` (`TauCeti.isEilenbergMacLaneSpace_killHomotopyGroups`),
so the fibre of `X⟨n⟩ → X` is a `K(πₙ X, n - 1)`
(`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). Iterating the construction gives
the stages of the Whitehead tower of `X`, along which homotopy groups are studied one at a time
through the fibrations `K(πₙ X, n - 1) → X⟨n⟩ → X`.

The proof reads off the homotopy groups of `X⟨n⟩` from the exact homotopy sequence of the map `j`
(`TauCeti.TopCat.mem_range_map_homotopyFiberProj_iff`,
`TauCeti.TopCat.eq_const_of_map_homotopyFiberProj_eq_const`): `j` is bijective on `πₖ` for
`k ≤ n` and `πₖ(Pₙ X)` is trivial for `k > n`, so `j` is surjective on every homotopy group.

## Main declarations

* `TauCeti.nConnectedCover`: the `n`-connected cover `X⟨n⟩`, with its projection
  `TauCeti.nConnectedCoverProj` to `X` and base point `TauCeti.nConnectedCoverBasepoint`.
* `TauCeti.subsingleton_homotopyGroup_nConnectedCover`: `πₖ(X⟨n⟩)` is trivial for `1 ≤ k ≤ n`.
* `TauCeti.bijective_homotopyGroupMap_nConnectedCoverProj`,
  `TauCeti.nConnectedCoverHomotopyGroupMulEquiv`: `πₖ(X⟨n⟩) ≅ πₖ(X)` for `k > n`.
* `TauCeti.nConnectedCoverFiberHomeomorph`: the fibre of `X⟨n⟩ → X` over `x` is a loop space.
* `TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`: for `n ≥ 2` and `X`
  `(n - 1)`-connected, that fibre is a `K(πₙ X, n - 1)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.3, Postnikov towers and Whitehead towers.
-/

public section

noncomputable section

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

universe u

namespace TauCeti

variable (n : ℕ) (X : TopCat.{u}) (x : X)

/-- The **`n`-connected cover** `X⟨n⟩` of `X`: the homotopy fibre of the inclusion
`j : X → TauCeti.killHomotopyGroups (n + 1) X x` over `j x`, of the points `z` of `X` with a path
from `j z` to `j x`. -/
abbrev nConnectedCover : TopCat.{u} :=
  TopCat.of (MappingPathFiber (killHomotopyGroupsIncl (n + 1) X x).hom
    (killHomotopyGroupsIncl (n + 1) X x x))

/-- The projection `(z, γ) ↦ z` of the `n`-connected cover to `X`, a Hurewicz fibration
(`TauCeti.TopCat.isHurewiczFibration_homotopyFiberProj`). -/
abbrev nConnectedCoverProj : nConnectedCover n X x ⟶ X :=
  TopCat.homotopyFiberProj (killHomotopyGroupsIncl (n + 1) X x) x

/-- The base point of the `n`-connected cover: the point `x` with the constant path. -/
abbrev nConnectedCoverBasepoint : nConnectedCover n X x :=
  (TopCat.homotopyFiberBasepoint (killHomotopyGroupsIncl (n + 1) X x) x).1

/-- The base point of the `n`-connected cover lies over `x`. -/
theorem nConnectedCoverProj_nConnectedCoverBasepoint :
    nConnectedCoverProj n X x (nConnectedCoverBasepoint n X x) = x :=
  Set.mem_singleton_iff.1 (TopCat.homotopyFiberBasepoint _ x).2

/-- The projection of the `n`-connected cover is a Serre fibration. -/
theorem serreFibrations_nConnectedCoverProj :
    TopCat.serreFibrations (nConnectedCoverProj n X x) :=
  TopCat.serreFibrations_homotopyFiberProj _ x

/-- The fibre over `x` of the projection of the `n`-connected cover is the loop space of
`TauCeti.killHomotopyGroups (n + 1) X x` at the image of `x`. -/
def nConnectedCoverFiberHomeomorph :
    (nConnectedCoverProj n X x).fiber x ≃ₜ
      Ω (killHomotopyGroups (n + 1) X x) (killHomotopyGroupsIncl (n + 1) X x x) where
  toFun p := ⟨p.1.val.2, p.1.property.1.trans (congrArg _
    ((TopCat.homotopyFiberProj_apply _ x p.1).symm.trans (Set.mem_singleton_iff.1 p.2))),
    p.1.property.2⟩
  invFun γ := ⟨⟨(x, γ.toContinuousMap), γ.source, γ.target⟩,
    Set.mem_singleton_iff.2 (TopCat.homotopyFiberProj_apply _ x _)⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext
    ((TopCat.homotopyFiberProj_apply _ x p.1).symm.trans (Set.mem_singleton_iff.1 p.2)).symm rfl))
  right_inv _ := rfl
  continuous_toFun :=
    continuous_induced_rng.2 (continuous_subtype_val.comp continuous_subtype_val).snd
  continuous_invFun := ((continuous_const.prodMk continuous_induced_dom).subtype_mk _).subtype_mk _

@[simp]
theorem nConnectedCoverFiberHomeomorph_apply (p : (nConnectedCoverProj n X x).fiber x) (t : I) :
    nConnectedCoverFiberHomeomorph n X x p t = p.1.val.2 t :=
  (rfl)

variable [T2Space X]

/-- The inclusion `X → killHomotopyGroups (n + 1) X x` is surjective on every homotopy group: it is
bijective in dimensions at most `n`, and the homotopy groups of the target vanish above `n`. -/
private theorem surjective_map_killHomotopyGroupsIncl (k : ℕ) :
    Function.Surjective (HomotopyGroup.map (N := Option (Fin k)) (x := x)
      (killHomotopyGroupsIncl (n + 1) X x).hom rfl) := by
  rcases lt_or_ge k n with hk | hk
  · exact (bijective_homotopyGroupMap_killHomotopyGroupsIncl (n + 1) X x (by simpa using hk)).2
  · have := subsingleton_homotopyGroup_killHomotopyGroups (n + 1) X x (k := k + 1) (by omega)
    have := (HomotopyGroup.congrEquiv (X := killHomotopyGroups (n + 1) X x)
      (x := killHomotopyGroupsIncl (n + 1) X x x) (finSuccEquiv k)).symm.subsingleton
    exact fun _ ↦ ⟨⟦GenLoop.const⟧, Subsingleton.elim _ _⟩

/-- A class of `πₖ(X⟨n⟩)` which projects to the trivial class of `X` is trivial. -/
private theorem eq_const_of_map_nConnectedCoverProj_eq_const {k : ℕ}
    {c : π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)}
    (hc : HomotopyGroup.map (nConnectedCoverProj n X x).hom
      (nConnectedCoverProj_nConnectedCoverBasepoint n X x) c = ⟦GenLoop.const⟧) :
    c = ⟦GenLoop.const⟧ :=
  TopCat.eq_const_of_map_homotopyFiberProj_eq_const _ x
    (surjective_map_killHomotopyGroupsIncl n X x k) hc

/-- **The `n`-connected cover is `n`-connected**: its homotopy groups `πₖ` vanish for
`1 ≤ k ≤ n`. -/
theorem subsingleton_homotopyGroup_nConnectedCover {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ n) :
    Subsingleton (π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨fun c c' ↦ ?_⟩
  -- Every class projects to a class of `X` killed by the inclusion, which is injective on
  -- `π_{m + 1}`; so it projects to the trivial class, and is trivial.
  suffices h : ∀ c : π_ (m + 1) (nConnectedCover n X x) (nConnectedCoverBasepoint n X x),
      c = ⟦GenLoop.const⟧ from (h c).trans (h c').symm
  intro c
  refine eq_const_of_map_nConnectedCoverProj_eq_const n X x ?_
  have hinj := (bijective_homotopyGroupMap_killHomotopyGroupsIncl (n + 1) X x
    (N := Option (Fin m)) (by simp; omega)).1
  have hrange := (TopCat.mem_range_map_homotopyFiberProj_iff
    (killHomotopyGroupsIncl (n + 1) X x) x).1 ⟨HomotopyGroup.congrEquiv (finSuccEquiv m) c, rfl⟩
  rw [← GenLoop.map_const (killHomotopyGroupsIncl (n + 1) X x).hom rfl,
    ← HomotopyGroup.map_mk] at hrange
  apply (HomotopyGroup.congrEquiv (X := X) (x := x) (finSuccEquiv m)).injective
  rw [← HomotopyGroup.map_congrEquiv, hinj hrange,
    HomotopyGroup.congrEquiv_mk]
  exact congrArg _ (GenLoop.ext _ _ fun _ ↦ by simp)

/-- **The `n`-connected cover of a path-connected space is path-connected.** -/
instance pathConnectedSpace_nConnectedCover [PathConnectedSpace X] :
    PathConnectedSpace (nConnectedCover n X x) := by
  have : Subsingleton (π_ 0 X x) := HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
  have : Subsingleton (π_ 0 (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) :=
    ⟨fun c c' ↦ (eq_const_of_map_nConnectedCoverProj_eq_const n X x (Subsingleton.elim _ _)).trans
      (eq_const_of_map_nConnectedCoverProj_eq_const n X x (Subsingleton.elim _ _)).symm⟩
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨⟦nConnectedCoverBasepoint n X x⟧⟩,
      (HomotopyGroup.pi0EquivZerothHomotopy
        (x := nConnectedCoverBasepoint n X x)).symm.subsingleton⟩

/-- **The `n`-connected cover has the homotopy groups of `X` above dimension `n`**: the projection
`X⟨n⟩ → X` is bijective on `πₖ` for `k > n`. -/
theorem bijective_homotopyGroupMap_nConnectedCoverProj {k : ℕ} (hk : n < k) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (nConnectedCoverProj n X x).hom
      (nConnectedCoverProj_nConnectedCoverBasepoint n X x)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : k ≠ 0)
  refine ⟨fun c c' h ↦ ?_, fun a ↦ ?_⟩
  · -- The projection is a group homomorphism with trivial kernel.
    have hker := (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := Fin (m + 1))
      (nConnectedCoverProj n X x).hom (nConnectedCoverProj_nConnectedCoverBasepoint n X x))).2
      fun c hc ↦ by
        rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one] at hc
        rw [eq_const_of_map_nConnectedCoverProj_eq_const n X x hc, HomotopyGroup.mk_const_eq_one]
    exact hker h
  · -- Every class of `X` is killed by the inclusion, whose target has no `π_{m + 1}`.
    have := subsingleton_homotopyGroup_killHomotopyGroups (n + 1) X x (k := m + 1) (by omega)
    have := (HomotopyGroup.congrEquiv (X := killHomotopyGroups (n + 1) X x)
      (x := killHomotopyGroupsIncl (n + 1) X x x) (finSuccEquiv m)).symm.subsingleton
    obtain ⟨c, hc⟩ := (TopCat.mem_range_map_homotopyFiberProj_iff
      (killHomotopyGroupsIncl (n + 1) X x) x
      (a := HomotopyGroup.congrEquiv (finSuccEquiv m) a)).2 (Subsingleton.elim _ _)
    refine ⟨(HomotopyGroup.congrEquiv (finSuccEquiv m)).symm c,
      (HomotopyGroup.congrEquiv (X := X) (x := x) (finSuccEquiv m)).injective ?_⟩
    rw [← HomotopyGroup.map_congrEquiv, Equiv.apply_symm_apply]
    exact hc

/-- For `k > n`, the projection of the `n`-connected cover induces an isomorphism
`πₖ(X⟨n⟩) ≃* πₖ(X)`. -/
def nConnectedCoverHomotopyGroupMulEquiv (k : ℕ) [NeZero k] (hk : n < k) :
    π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x) ≃* π_ k X x :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom (nConnectedCoverProj n X x).hom
    (nConnectedCoverProj_nConnectedCoverBasepoint n X x))
    (bijective_homotopyGroupMap_nConnectedCoverProj n X x hk)

@[simp]
theorem nConnectedCoverHomotopyGroupMulEquiv_apply (k : ℕ) [NeZero k] (hk : n < k)
    (c : π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) :
    nConnectedCoverHomotopyGroupMulEquiv n X x k hk c =
      HomotopyGroup.map (nConnectedCoverProj n X x).hom
        (nConnectedCoverProj_nConnectedCoverBasepoint n X x) c :=
  HomotopyGroup.mapHom_apply _ _ c

/-- **The fibre of the `n`-connected cover of an `(n - 1)`-connected space is a `K(πₙ X, n - 1)`**,
for `n ≥ 2`: it is the loop space of the Eilenberg--Mac Lane space `K(πₙ X, n)` obtained from `X`
by killing its homotopy groups above `n`. -/
theorem isEilenbergMacLaneSpace_fiber_nConnectedCoverProj [PathConnectedSpace X] (m : ℕ)
    (hX : ∀ k, k ≠ 0 → k < m + 2 → Subsingleton (π_ k X x)) :
    IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) ((nConnectedCoverProj (m + 2) X x).fiber x)
      (TopCat.homotopyFiberBasepoint _ x) :=
  (isEilenbergMacLaneSpace_killHomotopyGroups (m + 2) X x hX).loopSpace.of_homotopyEquiv
    (nConnectedCoverFiberHomeomorph (m + 2) X x).symm.toHomotopyEquiv _

end TauCeti
