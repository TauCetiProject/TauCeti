/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Stratification.Basic

/-!
# Common closed charts for semilinear partitions

Two finite semilinear partitions of the same set have a common partition by
relative interiors of closed rational-normal polyhedra. Each new interior lies
in one piece of each original partition, and its closure lies in both parent
closures. Thus closing charts commutes with refinement at the level needed to
compare continuous extensions from the original domains.

We apply `IsRationalSemilinear.exists_disjoint_intrinsicInteriors` to the
intersections of parent pieces. Lower-dimensional cells and arbitrary real
offsets are retained; no full-dimensionality or closedness is required.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Stratification/Refinement.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open Set

namespace TauCeti

variable {N V ι κ : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite ι] [Finite κ]
  {A : ι → Set V} {B : κ → Set V}

/-- Two finite semilinear partitions of the same set admit common closed
polyhedral charts. Every new interior belongs to exactly one parent in each
partition, and the whole closed chart lies in both parent closures. -/
theorem IsRationalSemilinear.exists_common_polyhedralRefinement
    (hA : ∀ a, IsRationalSemilinear h (A a))
    (hB : ∀ b, IsRationalSemilinear h (B b))
    (hAdisj : Pairwise fun a b => Disjoint (A a) (A b))
    (hBdisj : Pairwise fun a b => Disjoint (B a) (B b))
    (hcover : (⋃ a, A a) = ⋃ b, B b) :
    ∃ (μ : Type) (_ : Finite μ) (C : μ → Set V) (left : μ → ι) (right : μ → κ),
      (∀ s, (C s).Nonempty ∧ IsRationalNormalPolyhedron h (C s) ∧
        (intrinsicInterior ℝ (C s)).Nonempty ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (C s)) ∧
        intrinsicInterior ℝ (C s) ⊆ A (left s) ∩ B (right s) ∧
        C s ⊆ closure (A (left s)) ∩ closure (B (right s))) ∧
      (Pairwise fun s t => Disjoint (intrinsicInterior ℝ (C s))
        (intrinsicInterior ℝ (C t))) ∧
      (∀ a, ⋃ (s) (_ : left s = a), intrinsicInterior ℝ (C s) = A a) ∧
      (∀ b, ⋃ (s) (_ : right s = b), intrinsicInterior ℝ (C s) = B b) := by
  classical
  let := h.finiteDimensional
  -- Subdivide only the intersections, using the existing closed-chart construction.
  have hex (p : ι × κ) := ((hA p.1).inter (hB p.2)).exists_disjoint_intrinsicInteriors
  choose ν hν D hD hdisj hDcover using hex
  let (p : ι × κ) : Finite (ν p) := hν p
  have hsub (p : ι × κ) (j : ν p) :
      intrinsicInterior ℝ (D p j) ⊆ A p.1 ∩ B p.2 :=
    hDcover p ▸ subset_iUnion (fun j => intrinsicInterior ℝ (D p j)) j
  -- Compress the finite chart index, independently of the parent universes.
  let := Fintype.ofFinite (Σ p : ι × κ, ν p)
  let e := Fintype.equivFin (Σ p : ι × κ, ν p)
  have hmem (a : ι) (b : κ) (x : V) (ha : x ∈ A a) (hb : x ∈ B b) :
      ∃ s, (e.symm s).1.1 = a ∧ (e.symm s).1.2 = b ∧
        x ∈ intrinsicInterior ℝ (D (e.symm s).1 (e.symm s).2) := by
    have hxAB : x ∈ A a ∩ B b := ⟨ha, hb⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp ((hDcover (a, b)).symm ▸ hxAB)
    refine ⟨e ⟨(a, b), j⟩, by simp only [Equiv.symm_apply_apply],
      by simp only [Equiv.symm_apply_apply], ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hj
  refine ⟨Fin (Fintype.card (Σ p : ι × κ, ν p)), inferInstance,
    fun s => D (e.symm s).1 (e.symm s).2,
    fun s => (e.symm s).1.1, fun s => (e.symm s).1.2, ?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨hne, hpoly, hlc, hclosure⟩ := hD (e.symm s).1 (e.symm s).2
    exact ⟨hne, hpoly, hne.intrinsicInterior hpoly.convex, hlc,
      hsub (e.symm s).1 (e.symm s).2,
      subset_inter (hclosure.trans (closure_mono inter_subset_left))
        (hclosure.trans (closure_mono inter_subset_right))⟩
  -- Interiors with different parents are disjoint; within one parent the
  -- existing decomposition already gives disjointness.
  · intro s t hst
    have hne := e.symm.injective.ne hst
    dsimp only
    generalize e.symm s = z at hne ⊢
    generalize e.symm t = z' at hne ⊢
    obtain ⟨⟨a, b⟩, j⟩ := z
    obtain ⟨⟨a', b'⟩, l⟩ := z'
    by_cases ha : a = a'
    · subst a'
      by_cases hb : b = b'
      · subst b'
        exact hdisj (a, b) (fun hj : j = l => hne (by subst l; rfl))
      · exact (hBdisj hb).mono ((hsub (a, b) j).trans inter_subset_right)
          ((hsub (a, b') l).trans inter_subset_right)
    · exact (hAdisj ha).mono ((hsub (a, b) j).trans inter_subset_left)
        ((hsub (a', b') l).trans inter_subset_left)
  -- Recover each parent piece separately, including lower-dimensional pieces.
  · intro a
    apply Subset.antisymm
    · exact iUnion₂_subset fun s hs =>
        hs ▸ ((hsub (e.symm s).1 (e.symm s).2).trans inter_subset_left)
    · intro x hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp (hcover ▸ mem_iUnion.mpr ⟨a, hx⟩)
      obtain ⟨s, hs, -, hxs⟩ := hmem a b x hx hb
      exact mem_iUnion₂.mpr ⟨s, hs, hxs⟩
  · intro b
    apply Subset.antisymm
    · exact iUnion₂_subset fun s hs =>
        hs ▸ ((hsub (e.symm s).1 (e.symm s).2).trans inter_subset_right)
    · intro x hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover.symm ▸ mem_iUnion.mpr ⟨b, hx⟩)
      obtain ⟨s, -, hs, hxs⟩ := hmem a b x ha hx
      exact mem_iUnion₂.mpr ⟨s, hs, hxs⟩

end TauCeti
