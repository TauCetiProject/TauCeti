/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Finite smooth spanning families

A finite-rank smooth real vector bundle over a compact Hausdorff finite-dimensional manifold
has finitely many global smooth sections spanning every fiber. The base may have corners.
The construction cuts off local frames and takes a finite subcover. It does not require a
metric, orientability, connectedness, a nonempty base, or positive rank.

This is the finite-dimensional perturbation space for generic smooth sections.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 2, for smooth local frames and partitions
  of unity; Chapter 3, for finite-dimensional perturbations of sections.
-/

public section

open Bundle Filter Module Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {X H M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- A compact smooth real vector bundle admits a finite family of global smooth sections
spanning each fiber. This includes rank zero and the empty base. -/
theorem exists_fin_spanning_contMDiffSection :
    ∃ (n : ℕ) (s : Fin n → ContMDiffSection I F ∞ V),
      ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤ := by
  classical
  let b := Module.finBasis ℝ F
  let e (x : M) := trivializationAt F V x
  have hlocal (x : M) : ∃ s : Fin (finrank ℝ F) → ContMDiffSection I F ∞ V,
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, Submodule.span ℝ (range fun i ↦ s i y) = ⊤ := by
    obtain ⟨f, hf, heq⟩ := (e x).exists_contMDiff_eventuallyEq_localFrame (I := I) b
      (mem_baseSet_trivializationAt F V x)
    obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp (Filter.eventually_all.mpr heq)
    refine ⟨fun i ↦ ⟨f i, hf i⟩, U ∩ (e x).baseSet,
      hUopen.inter (e x).open_baseSet, ⟨hxU, mem_baseSet_trivializationAt F V x⟩, ?_⟩
    intro y hy
    have hfun : (fun i ↦ f i y) = (e x).basisAt b hy.2 := by
      funext i
      rw [hU y hy.1 i, (e x).localFrame_apply_of_mem_baseSet b hy.2]
    exact hfun ▸ ((e x).basisAt b hy.2).span_eq
  choose s U hU hxU hspan using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU fun x _ ↦
    mem_iUnion.mpr ⟨x, hxU x⟩
  let J := ↥t × Fin (finrank ℝ F)
  let f : J → ContMDiffSection I F ∞ V := fun i ↦ s i.1.1 i.2
  let q := Fintype.equivFin J
  refine ⟨Fintype.card J, f ∘ q.symm, fun x ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  apply top_unique
  rw [← hspan a x hx]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨q (⟨a, ha⟩, i), ?_⟩
  simp [f]

end TauCeti
