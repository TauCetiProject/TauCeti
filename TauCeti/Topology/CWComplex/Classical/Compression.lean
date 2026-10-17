/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Skeleton.Homotopy

/-!
# The compression lemma

Let `C` be a relative CW complex with base `D`, and let `B` be a subset of a space `Y`. Suppose
that, for every `n` such that `C` has `n`-cells, every map of pairs `(Dⁿ, Sⁿ⁻¹) → (Y, B)` is
homotopic relative to `Sⁿ⁻¹` to a map into `B`. The **compression lemma** says that every map
`f : C → Y` sending `D` into `B` is then homotopic relative to `D` to a map into `B`
(`TauCeti.exists_homotopicRel_range_subset`). In Hatcher's proof of Whitehead's theorem it is
applied to the identity of the mapping cylinder of a weak homotopy equivalence, relative to the
domain, to deform the cylinder into the domain.

The proof is Hatcher's. If `f` already sends `skeletonLT C n` into `B`, then through the
characteristic map of an `n`-cell it is a map of pairs `(Dⁿ, Sⁿ⁻¹) → (Y, B)`, which the hypothesis
homotopes relative to `Sⁿ⁻¹` into `B`. These homotopies are the restrictions of a homotopy of `f`
relative to `skeletonLT C n` (`TauCeti.exists_homotopicRel_cellMap`), after which `f` sends
`skeletonLT C (n + 1)` into `B`. Performing these homotopies one after the other
(`TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT`) gives a homotopy relative to `D` to a map
sending every skeleton, hence all of `C`, into `B`.

The balls and spheres are those of the characteristic maps, the closed unit ball and unit sphere
of `Fin n → ℝ` with the sup norm. For `n = 0` the sphere is empty and the ball is a point, so the
hypothesis for `0`-cells says that every point of `Y` is joined by a path to a point of `B`. By
Hatcher's compression criterion, the hypothesis in dimension `n ≥ 1` says that
`πₙ(Y, B, y₀) = 0` for every `y₀ ∈ B`; the version of the lemma with these hypotheses on the
cubical relative homotopy groups `TauCeti.RelHomotopyGroup` is
`TauCeti.exists_homotopicRel_range_subset_of_relHomotopyGroup`.

## Main results

* `TauCeti.exists_homotopicRel_range_subset`: **the compression lemma**.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.6 (the compression lemma) and the compression criterion for relative
  homotopy groups.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter II.
-/

public section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type*} [TopologicalSpace Y] {B : Set Y}

/-- **The compression lemma** (Hatcher, Lemma 4.6). Let `C` be a relative CW complex with base
`D` and let `B ⊆ Y`. Suppose that, for every `n` such that `C` has `n`-cells, every map from the
closed unit ball of `Fin n → ℝ` to `Y` sending the unit sphere into `B` is homotopic, relative to
the sphere, to a map into `B`. Then every map `f : C → Y` sending `D` into `B` is homotopic,
relative to `D`, to a map into `B`. -/
theorem exists_homotopicRel_range_subset
    (h : ∀ n, Nonempty (cell C n) → ∀ g : C(closedBall (0 : Fin n → ℝ) 1, Y),
      MapsTo g {y | (y : Fin n → ℝ) ∈ sphere 0 1} B →
        ∃ g' : C(closedBall (0 : Fin n → ℝ) 1, Y),
          g.HomotopicRel g' {y | (y : Fin n → ℝ) ∈ sphere 0 1} ∧ range g' ⊆ B)
    (f : C(C, Y)) (hf : MapsTo f {x : C | (x : X) ∈ D} B) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ D} ∧ range g ⊆ B := by
  -- A map sending `skeletonLT C n` into `B` is compressed on each closed `n`-cell.
  have step (n : ℕ) (g : C(C, Y)) (hg : MapsTo g {x : C | (x : X) ∈ skeletonLT C n} B) :
      ∃ g' : C(C, Y), g.HomotopicRel g' {x : C | (x : X) ∈ skeletonLT C n} ∧
        MapsTo g' {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)} B := by
    have hcomp (j : cell C n) := h n ⟨j⟩ (g.comp (cellMap j)) fun y hy ↦
      hg (by simpa using cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩)
    choose ψ hψ hψB using hcomp
    obtain ⟨g', hgg', hg'⟩ := exists_homotopicRel_cellMap n g ψ hψ
    exact ⟨g', hgg', mapsTo_skeletonLT_succ_iff.2
      ⟨fun x hx ↦ hgg'.fst_eq_snd hx ▸ hg hx, fun j y ↦ hg' j y ▸ hψB j ⟨y, rfl⟩⟩⟩
  obtain ⟨g, hg, hfg⟩ := exists_homotopicRel_forall_mapsTo_skeletonLT (fun _ ↦ B) step f hf
  refine ⟨g, hfg, range_subset_iff.2 fun x ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_skeletonLT_add 0 x.2
  exact hg (0 + n) hn

end TauCeti
