/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Connectivity of a CW pair from the dimensions of its cells

Let `C` be a relative CW complex with base `D` in a Hausdorff space, all of whose cells have
dimension at least `n`. Attaching cells of dimension at least `n` does not change homotopy groups
below degree `n - 1` (Hatcher, Corollary 4.12). This file states this for the pair `(C, D)`:

* the relative homotopy set `π_{k+1}(C, D, a)` is trivial for `k + 1 < n` and every `a ∈ D`
  (`TauCeti.subsingleton_relHomotopyGroup_of_isEmpty_cell`);
* the inclusion `D ↪ C` induces a surjection `π_k(D, a) → π_k(C, a)` for `k < n`
  (`TauCeti.surjective_homotopyGroupMap_of_isEmpty_cell`) and an injection for `k + 1 < n`
  (`TauCeti.injective_homotopyGroupMap_of_isEmpty_cell`).

In degree zero, at a base point `a ∈ D`, these say that every point of `C` is joined by a path to
a point of `D` (for `n ≥ 1`), and that two points of `D` joined by a path in `C` are joined by a
path in `D` (for `n ≥ 2`).

The same connectivity then holds for any map `j : B → Y` that is weakly equivalent to the
inclusion `D ↪ C`: given weak homotopy equivalences `f : D → B` and `g : C → Y` with
`g ∘ (D ↪ C) = j ∘ f`, every point of `Y` is joined by a path to a point of the image of `j`
(`TauCeti.exists_joined_of_isEmpty_cell_of_comp_eq`), and `j` induces a surjection
`π_k(B, b) → π_k(Y, j b)` for `k < n` and an injection for `k + 1 < n`, at every base point
`b ∈ B` (`TauCeti.surjective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq`,
`TauCeti.injective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq`). The typical case is the
inclusion of a subspace `B ⊆ Y` for which a homotopy equivalence of pairs `(C, D) ≃ (Y, B)`
is known, so that `(Y, B)` behaves like a CW pair with cells of dimension at least `n` without
being given such a structure. The transport is the square lemma
`ContinuousMap.IsWeakHomotopyEquivalence.forall_surjective_map_iff_of_comp_eq` (and its
injective counterpart); base points of `B` outside the image of `f` are reached by base-point
change.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12.
-/

public section

noncomputable section

universe u v

open Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D] {n : ℕ}

/-- **A CW pair with cells of dimension at least `n` is `(n - 1)`-connected** (Hatcher,
Corollary 4.12). If a relative CW complex `C` with base `D` has no cells of dimension less than
`n`, then the relative homotopy set `π_{k+1}(C, D, a)` is trivial for every `a ∈ D`, where
`k = Nat.card N` and `k + 1 < n`. -/
theorem subsingleton_relHomotopyGroup_of_isEmpty_cell {N : Type v} [Finite N]
    (hcell : ∀ m < n, IsEmpty (cell C m)) (hN : Nat.card N + 1 < n) (a : D) :
    Subsingleton (RelHomotopyGroup N
      ⟨TopPair.ofInclusion (X := TopCat.of X) (base_subset_complex (C := C)), a⟩) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hD : (skeletonLT C (n + 1) : Set X) = D := by
    exact_mod_cast skeletonLT_eq_base_of_isEmpty_cell C (n + 1) hcell
  exact subsingleton_relHomotopyGroup_skeletonLT (by omega) hD base_subset_complex a

/-- **Attaching cells of dimension at least `n` is surjective on `π_k` for `k < n`** (Hatcher,
Corollary 4.12). If a relative CW complex `C` with base `D` has no cells of dimension less than
`n`, then the inclusion `D ↪ C` induces a surjection `π_k(D, a) → π_k(C, a)`, where
`k = Nat.card N < n`. -/
theorem surjective_homotopyGroupMap_of_isEmpty_cell {N : Type v} [Finite N]
    (hcell : ∀ m < n, IsEmpty (cell C m)) (hN : Nat.card N < n) (a : D) :
    Function.Surjective (HomotopyGroup.map (N := N) (x := a)
      (ContinuousMap.inclusion (base_subset_complex (C := C))) rfl) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hD : (skeletonLT C (n + 1) : Set X) = D := by
    exact_mod_cast skeletonLT_eq_base_of_isEmpty_cell C (n + 1) hcell
  exact surjective_homotopyGroupMap_skeletonLT (by omega) hD base_subset_complex a

/-- **Attaching cells of dimension at least `n` is injective on `π_k` for `k + 1 < n`** (Hatcher,
Corollary 4.12). If a relative CW complex `C` with base `D` has no cells of dimension less than
`n`, then the inclusion `D ↪ C` induces an injection `π_k(D, a) → π_k(C, a)`, where
`k = Nat.card N` and `k + 1 < n`. -/
theorem injective_homotopyGroupMap_of_isEmpty_cell {N : Type v} [Finite N]
    (hcell : ∀ m < n, IsEmpty (cell C m)) (hN : Nat.card N + 1 < n) (a : D) :
    Function.Injective (HomotopyGroup.map (N := N) (x := a)
      (ContinuousMap.inclusion (base_subset_complex (C := C))) rfl) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hD : (skeletonLT C (n + 1) : Set X) = D := by
    exact_mod_cast skeletonLT_eq_base_of_isEmpty_cell C (n + 1) hcell
  exact injective_homotopyGroupMap_skeletonLT (by omega) hD base_subset_complex a

/-! ### Transport along weak homotopy equivalences -/

section Transport

variable {Y B : Type*} [TopologicalSpace Y] [TopologicalSpace B] {f : C(D, B)} {g : C(C, Y)}
  {j : C(B, Y)}

/-- If a relative CW complex `C` with base `D` has no cells of dimension less than `n`, where
`n ≥ 1`, and `j : B → Y` is weakly equivalent to the inclusion `D ↪ C`, through weak homotopy
equivalences `f : D → B` and `g : C → Y` with `g ∘ (D ↪ C) = j ∘ f`, then every point of `Y` is
joined by a path to a point of the image of `j`. -/
theorem exists_joined_of_isEmpty_cell_of_comp_eq (hcell : ∀ m < n, IsEmpty (cell C m))
    (hn : 0 < n) (hf : f.IsWeakHomotopyEquivalence) (hg : g.IsWeakHomotopyEquivalence)
    (hgf : g.comp (ContinuousMap.inclusion base_subset_complex) = j.comp f) (y : Y) :
    ∃ b, Joined (j b) y := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hD : (skeletonLT C (n + 1) : Set X) = D := by
    exact_mod_cast skeletonLT_eq_base_of_isEmpty_cell C (n + 1) hcell
  exact (hf.forall_exists_joined_iff_of_comp_eq hg hgf).2
    (exists_joined_skeletonLT hD base_subset_complex) y

/-- If a relative CW complex `C` with base `D` has no cells of dimension less than `n`, and
`j : B → Y` is weakly equivalent to the inclusion `D ↪ C`, through weak homotopy equivalences
`f : D → B` and `g : C → Y` with `g ∘ (D ↪ C) = j ∘ f`, then `j` induces a surjection
`π_k(B, b) → π_k(Y, j b)` at every `b ∈ B`, where `k = Nat.card N < n`. -/
theorem surjective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq {N : Type v} [Finite N]
    (hcell : ∀ m < n, IsEmpty (cell C m)) (hN : Nat.card N < n)
    (hf : f.IsWeakHomotopyEquivalence) (hg : g.IsWeakHomotopyEquivalence)
    (hgf : g.comp (ContinuousMap.inclusion base_subset_complex) = j.comp f) (b : B) :
    Function.Surjective (HomotopyGroup.map (N := N) j (rfl : j b = j b)) :=
  (hf.forall_surjective_map_iff_of_comp_eq hg hgf N).2
    (surjective_homotopyGroupMap_of_isEmpty_cell hcell hN) b

/-- If a relative CW complex `C` with base `D` has no cells of dimension less than `n`, and
`j : B → Y` is weakly equivalent to the inclusion `D ↪ C`, through weak homotopy equivalences
`f : D → B` and `g : C → Y` with `g ∘ (D ↪ C) = j ∘ f`, then `j` induces an injection
`π_k(B, b) → π_k(Y, j b)` at every `b ∈ B`, where `k = Nat.card N` and `k + 1 < n`. -/
theorem injective_homotopyGroupMap_of_isEmpty_cell_of_comp_eq {N : Type v} [Finite N]
    (hcell : ∀ m < n, IsEmpty (cell C m)) (hN : Nat.card N + 1 < n)
    (hf : f.IsWeakHomotopyEquivalence) (hg : g.IsWeakHomotopyEquivalence)
    (hgf : g.comp (ContinuousMap.inclusion base_subset_complex) = j.comp f) (b : B) :
    Function.Injective (HomotopyGroup.map (N := N) j (rfl : j b = j b)) :=
  (hf.forall_injective_map_iff_of_comp_eq hg hgf N).2
    (injective_homotopyGroupMap_of_isEmpty_cell hcell hN) b

end Transport

end TauCeti
