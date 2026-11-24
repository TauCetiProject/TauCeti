/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support

/-!
# Finite differentiable spanning families

For `n ≤ ∞`, a finite-rank `C^n` real vector bundle over a compact Hausdorff
finite-dimensional `C^n` manifold
has finitely many global `C^n` sections spanning every fiber. The base may have corners.
The construction cuts off local frames and takes a finite subcover. It does not require a
metric, orientability, connectedness, a nonempty base, or positive rank.

Without compactness, the cut-off local frames still give, near each point, finitely many
compactly supported `C^n` sections spanning every nearby fiber
(`TauCeti.exists_compactlySupported_spanning_nhds`).

This is the finite-dimensional perturbation space for generic differentiable sections.

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
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {n : ℕ∞ω} [IsManifold I n M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V I]

/-- For `n ≤ ∞`, near each point of a `C^n` real vector bundle of finite rank, finitely many
compactly supported `C^n` sections span every fiber. -/
theorem exists_compactlySupported_spanning_nhds [ENat.LEInfty n] (x : M) :
    ∃ s : Fin (finrank ℝ F) → ContMDiffSection I F n V,
      (∀ i, s i ∈ ContMDiffSection.compactlySupported I F n V) ∧
        ∀ᶠ y in 𝓝 x, Submodule.span ℝ (range fun i ↦ s i y) = ⊤ := by
  let b := Module.finBasis ℝ F
  let e := trivializationAt F V x
  have hx := mem_baseSet_trivializationAt F V x
  obtain ⟨f, hf, heq, hc⟩ :=
    e.exists_contMDiff_eventuallyEq_localFrame (I := I) (n := n) b ENat.LEInfty.out hx
  refine ⟨fun i ↦ ⟨f i, hf i⟩, fun i ↦ ?_, ?_⟩
  · rw [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def]
    exact hc i
  filter_upwards [Filter.eventually_all.mpr heq, e.open_baseSet.mem_nhds hx] with y hy hye
  have hfun : (fun i ↦ (⟨f i, hf i⟩ : ContMDiffSection I F n V) y) = e.basisAt b hye := by
    funext i
    simp [hy i, e.localFrame_apply_of_mem_baseSet b hye]
  exact hfun ▸ (e.basisAt b hye).span_eq

variable [CompactSpace M]

/-- For `n ≤ ∞`, a compact `C^n` real vector bundle admits a finite family of global `C^n` sections
spanning each fiber. This includes rank zero and the empty base. -/
theorem exists_fin_spanning_contMDiffSection [ENat.LEInfty n] :
    ∃ (m : ℕ) (s : Fin m → ContMDiffSection I F n V),
      ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤ := by
  have hlocal (x : M) : ∃ s : Fin (finrank ℝ F) → ContMDiffSection I F n V,
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, Submodule.span ℝ (range fun i ↦ s i y) = ⊤ := by
    obtain ⟨s, -, hs⟩ := exists_compactlySupported_spanning_nhds (I := I) (F := F) (V := V) x
    obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp hs
    exact ⟨s, U, hUopen, hxU, hU⟩
  choose s U hU hxU hspan using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU fun x _ ↦
    mem_iUnion.mpr ⟨x, hxU x⟩
  let J := ↥t × Fin (finrank ℝ F)
  let f : J → ContMDiffSection I F n V := fun i ↦ s i.1.val i.2
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
