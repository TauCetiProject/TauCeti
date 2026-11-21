/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Finite smooth spanning families

A finite-rank smooth real vector bundle over a compact Hausdorff finite-dimensional manifold
has finitely many global smooth sections spanning every fiber. The base may have corners.
The construction cuts off local frames and takes a finite subcover. It does not require a
metric, orientability, connectedness, a nonempty base, or positive rank.

Without compactness, the cut-off local frames still give, near each point, finitely many
compactly supported smooth sections spanning every nearby fiber
(`TauCeti.exists_compactlySupported_spanning_nhds`).

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
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- Near each point of a smooth real vector bundle of finite rank, finitely many compactly
supported smooth sections span every fiber. -/
theorem exists_compactlySupported_spanning_nhds (x : M) :
    ∃ s : Fin (finrank ℝ F) → ContMDiffSection I F ∞ V,
      (∀ i, s i ∈ ContMDiffSection.compactlySupported I F ∞ V) ∧
        ∀ᶠ y in 𝓝 x, Submodule.span ℝ (range fun i ↦ s i y) = ⊤ := by
  let b := Module.finBasis ℝ F
  let e := trivializationAt F V x
  have hx := mem_baseSet_trivializationAt F V x
  obtain ⟨f, hf, heq⟩ := e.exists_contMDiff_eventuallyEq_localFrame (I := I) b hx
  -- Cut the frame off a second time, now by a compactly supported bump equal to one near `x`.
  let ρ : SmoothBumpFunction I x := Classical.arbitrary _
  let ψ : C^∞⟮I, M; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  refine ⟨fun i ↦ ψ • ⟨f i, hf i⟩, fun i ↦
    ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport ψ
      ρ.hasCompactSupport _, ?_⟩
  filter_upwards [Filter.eventually_all.mpr heq, ρ.eventuallyEq_one,
    e.open_baseSet.mem_nhds hx] with y hy hρ hye
  have hfun : (fun i ↦ (ψ • ⟨f i, hf i⟩ : ContMDiffSection I F ∞ V) y) =
      e.basisAt b hye := by
    funext i
    rw [ContMDiffSection.smul_apply]
    simp [ψ, show (ρ : M → ℝ) y = 1 from hρ, hy i, e.localFrame_apply_of_mem_baseSet b hye]
  exact hfun ▸ (e.basisAt b hye).span_eq

variable [CompactSpace M]

/-- A compact smooth real vector bundle admits a finite family of global smooth sections
spanning each fiber. This includes rank zero and the empty base. -/
theorem exists_fin_spanning_contMDiffSection :
    ∃ (n : ℕ) (s : Fin n → ContMDiffSection I F ∞ V),
      ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤ := by
  have hlocal (x : M) : ∃ s : Fin (finrank ℝ F) → ContMDiffSection I F ∞ V,
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, Submodule.span ℝ (range fun i ↦ s i y) = ⊤ := by
    obtain ⟨s, -, hs⟩ := exists_compactlySupported_spanning_nhds (I := I) (F := F) (V := V) x
    obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp hs
    exact ⟨s, U, hUopen, hxU, hU⟩
  choose s U hU hxU hspan using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU fun x _ ↦
    mem_iUnion.mpr ⟨x, hxU x⟩
  let J := ↥t × Fin (finrank ℝ F)
  let f : J → ContMDiffSection I F ∞ V := fun i ↦ s i.1.val i.2
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
