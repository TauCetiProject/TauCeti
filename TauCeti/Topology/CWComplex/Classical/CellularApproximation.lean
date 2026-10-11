/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Homotopy

/-!
# The cellular approximation theorem

Let `C` and `C'` be relative CW complexes with bases `D` and `E`. This file proves that every map
`f : C → C'` sending `D` into `E` is homotopic, relative to `D`, to a cellular map: one sending
the skeleton `skeletonLT C n` into `skeletonLT C' n` for every `n`
(`TauCeti.exists_isCellular_homotopicRel`). For CW complexes, with empty bases, every map is
homotopic to a cellular map (`TauCeti.exists_isCellular_homotopic`). Constructions defined only
for cellular maps, such as induced maps of cellular chain complexes, therefore apply to every map
of CW complexes up to homotopy.

The proof is Hatcher's. Suppose `f` already sends `skeletonLT C n` into `skeletonLT C' n`.
Through the characteristic map of an `n`-cell of `C`, `f` is a map of a closed `n`-ball sending
its boundary sphere into `skeletonLT C' n`. Since the ball has dimension `n`,
`TauCeti.exists_homotopicRel_skeletonLT_finrank` homotopes it, relative to its boundary,
into `skeletonLT C' (n + 1)`. These homotopies are the restrictions of a homotopy of `f` relative
to `skeletonLT C n` (`TauCeti.exists_homotopicRel_cellMap`), which gives the inductive step
`TauCeti.exists_homotopicRel_mapsTo_skeletonLT_succ`. Performing the successive homotopies one
after the other (`TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT`) gives a single homotopy
to a cellular map.

## Main results

* `TauCeti.exists_homotopicRel_mapsTo_skeletonLT_succ`: the inductive step, a map sending
  `skeletonLT C n` into `skeletonLT C' n` is homotopic relative to `skeletonLT C n` to one that
  also sends `skeletonLT C (n + 1)` into `skeletonLT C' (n + 1)`.
* `TauCeti.exists_isCellular_homotopicRel`: **the cellular approximation theorem** for relative
  CW complexes.
* `TauCeti.exists_isCellular_homotopic`: the cellular approximation theorem for CW complexes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Theorem 4.8.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter II, Section 4.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

universe u v w

section Step

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] {C' E : Set Y} [RelCWComplex C' E]

/-- **The inductive step of cellular approximation.** A map `f : C → C'` sending the skeleton
`skeletonLT C n` into `skeletonLT C' n` is homotopic, relative to `skeletonLT C n`, to a map that
also sends `skeletonLT C (n + 1)` into `skeletonLT C' (n + 1)`. -/
theorem exists_homotopicRel_mapsTo_skeletonLT_succ (n : ℕ) (f : C(C, C'))
    (hf : MapsTo f {x : C | (x : X) ∈ skeletonLT C n} {y : C' | (y : Y) ∈ skeletonLT C' n}) :
    ∃ g : C(C, C'), f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C n} ∧
      MapsTo g {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)}
        {y : C' | (y : Y) ∈ skeletonLT C' ((n + 1 : ℕ) : ℕ∞)} := by
  have hsucc : (skeletonLT C' n : Set Y) ⊆ skeletonLT C' ((n + 1 : ℕ) : ℕ∞) :=
    skeletonLT_mono (by exact_mod_cast n.le_succ)
  -- Compress `f` on each closed `n`-cell into `skeletonLT C' (n + 1)`, relative to the points
  -- already sent there, which include the boundary sphere.
  have hcomp (j : cell C n) := exists_homotopicRel_skeletonLT_finrank (C := C')
    (isCompact_closedBall (0 : Fin n → ℝ) 1) (n := n) (Module.finrank_fin_fun ℝ).le
    (f.comp (cellMap j))
  choose ψ hψ hψmem using hcomp
  obtain ⟨g, hfg, hg⟩ := exists_homotopicRel_cellMap n f ψ fun j ↦ (hψ j).mono fun y hy ↦
    hsucc (hf (by simpa using cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩))
  refine ⟨g, hfg, mapsTo_skeletonLT_succ_iff.2 ⟨fun x hx ↦ ?_, fun j y ↦ hg j y ▸ hψmem j y⟩⟩
  rw [mem_ofPred_eq, ← hfg.fst_eq_snd hx]
  exact hsucc (hf hx)

end Step

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {C D : Set X} [RelCWComplex C D] {C' E : Set Y} [RelCWComplex C' E]

/-- **The cellular approximation theorem** (Hatcher, Theorem 4.8). Every map `f : C → C'` of
relative CW complexes sending the base `D` into the base `E` is homotopic, relative to `D`, to a
cellular map. -/
theorem exists_isCellular_homotopicRel (f : TopCat.of C ⟶ TopCat.of C')
    (hf : MapsTo f {x : C | (x : X) ∈ D} {y : C' | (y : Y) ∈ E}) :
    ∃ g : TopCat.of C ⟶ TopCat.of C', IsCellular C C' g ∧
      f.hom.HomotopicRel g.hom {x : C | (x : X) ∈ D} := by
  obtain ⟨g, hg, hfg⟩ := exists_homotopicRel_forall_mapsTo_skeletonLT
    (fun n ↦ {y : C' | (y : Y) ∈ skeletonLT C' n})
    (fun n g hg ↦ exists_homotopicRel_mapsTo_skeletonLT_succ n g hg) f.hom
    (by simpa only [Nat.cast_zero, ← SetLike.mem_coe, skeletonLT_zero_eq_base] using hf)
  exact ⟨TopCat.ofHom g, fun n _ hx ↦ hg n hx, hfg⟩

/-- **The cellular approximation theorem for CW complexes** (Hatcher, Theorem 4.8). Every map of
CW complexes is homotopic to a cellular map. -/
theorem exists_isCellular_homotopic {C : Set X} [CWComplex C] {C' : Set Y} [CWComplex C']
    (f : TopCat.of C ⟶ TopCat.of C') :
    ∃ g : TopCat.of C ⟶ TopCat.of C', IsCellular C C' g ∧ f.hom.Homotopic g.hom := by
  obtain ⟨g, hg, hfg⟩ := exists_isCellular_homotopicRel f fun _ hx ↦ absurd hx (notMem_empty _)
  exact ⟨g, hg, hfg.homotopic⟩

end TauCeti
