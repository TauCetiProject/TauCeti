/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Order.PartialSups
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Path-connected unions and intersections

If every member of a family of path-connected sets contains a path-connected set `C`, and two
distinct members meet inside `C`, then every pairwise intersection of the family is path
connected: it is a member of the family or `C` itself. This is the hypothesis on pairwise
intersections in the generation half of the Seifert--van Kampen theorem, and the form in which it
holds for the summands of a wedge sum.

Every space has a choice of base point in each path component, the representative of its class
in `ZerothHomotopy`.

Finite partial unions are path connected when each member is path connected and each new
member meets the preceding union. The partial unions use Mathlib's `partialSups`, indexed by any
locally finite linear order with a bottom element and a successor function, such as `ℕ` or
`Fin (n + 1)`.

If a set is covered by two path-connected subsets but is not itself path connected, then each of
the two subsets is a path component of it.

A function which, near each point of a path, agrees with its value at that point takes the same
value at the two ends of the path.

## Main declarations

* `TauCeti.isPathConnected_inter_of_pairwise`: pairwise intersections of such a family are path
  connected.
* `TauCeti.isPathConnected_partialSups`: path connectedness of successive finite unions.
* `IsPathConnected.pathComponentIn_eq_of_not_isPathConnected`: if a set that is not path connected
  is covered by two path-connected subsets, each of them is one of its path components.
* `TauCeti.exists_pathComponent_representative`: a choice of base point in each path component.
* `Path.eq_of_eventually_eq`: a function locally constant along a path takes the same value at its
  two ends.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X} {C : Set X}

/-- If every member of the family contains `C` and two distinct members meet inside `C`, then
every pairwise intersection is path connected as soon as `C` and the members are. -/
theorem isPathConnected_inter_of_pairwise (hUp : ∀ i, IsPathConnected (U i))
    (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i) (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C)
    (i j : ι) : IsPathConnected (U i ∩ U j) := by
  rcases eq_or_ne i j with rfl | hij
  · simpa using hUp i
  · rwa [(hUC hij).antisymm (subset_inter (hCU i) (hCU j))]

/-- Finite partial unions are path connected if each member is path connected and each
new member meets the preceding union. Only the members of index at most `n` are constrained. -/
theorem isPathConnected_partialSups {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [SuccOrder ι] (U : ι → Set X) (n : ι) (hU : ∀ i ≤ n, IsPathConnected (U i))
    (hOverlap : ∀ i < n, (partialSups U i ∩ U (Order.succ i)).Nonempty) :
    IsPathConnected (partialSups U n) := by
  induction n using Succ.rec_bot with
  | hbot =>
    rw [partialSups_bot]
    exact hU ⊥ le_rfl
  | hsucc n ih =>
    -- At a maximal index the successor is the index itself, so there is nothing to add.
    by_cases hn : IsMax n
    · rw [hn.succ_eq] at hU hOverlap ⊢
      exact ih hU hOverlap
    have hlt : n < Order.succ n := Order.lt_succ_of_not_isMax hn
    rw [partialSups_succ]
    exact (ih (fun i hi ↦ hU i (hi.trans hlt.le)) fun i hi ↦ hOverlap i (hi.trans hlt)).union
      (hU _ le_rfl) (hOverlap n hlt)

/-- If a set `A` is covered by two path-connected subsets `B` and `C` but is not itself path
connected, then `B` is a path component of `A`. -/
theorem _root_.IsPathConnected.pathComponentIn_eq_of_not_isPathConnected {A B : Set X} {x : X}
    (hB : IsPathConnected B) (hC : IsPathConnected C) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hABC : A ⊆ B ∪ C) (hx : x ∈ B) (hA : ¬IsPathConnected A) : pathComponentIn A x = B := by
  refine Subset.antisymm (fun q hq ↦ ?_) (hB.subset_pathComponentIn hx hBA)
  by_contra hqB
  have hqC : q ∈ C := (hABC (pathComponentIn_subset hq)).resolve_left hqB
  exact hA ⟨x, hBA hx, fun {z} hz ↦
    (hABC hz).elim (fun hzB ↦ hB.joinedIn _ hx _ hzB |>.mono hBA)
      (fun hzC ↦ (hq : JoinedIn A _ q).trans ((hC.joinedIn _ hqC _ hzC).mono hCA))⟩

/-- **Base points of path components.** There is a map sending each point to a point joined to
it, constant on path components. -/
theorem exists_pathComponent_representative :
    ∃ b : X → X, (∀ y, Joined (b y) y) ∧ ∀ {x y}, Joined x y → b x = b y :=
  ⟨fun y ↦ (Quotient.mk (pathSetoid X) y).out, fun y ↦ Quotient.mk_out (s := pathSetoid X) y,
    fun h ↦ congrArg Quotient.out (Quotient.sound (s := pathSetoid X) h)⟩

end TauCeti

/-- A function which, near each point of a path, agrees with its value at that point takes the
same value at the two ends of the path. -/
theorem Path.eq_of_eventually_eq {X α : Type*} [TopologicalSpace X] {f : X → α} {x y : X}
    (γ : Path x y) (h : ∀ t, ∀ᶠ s in 𝓝 t, f (γ s) = f (γ t)) : f x = f y := by
  simpa using ((IsLocallyConstant.iff_eventually_eq _).2 h).apply_eq_of_preconnectedSpace 0 1
