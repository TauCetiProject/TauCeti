/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Leaving a compact set through its intrinsic frontier

Follow the ray from a point `p` of a compact set `C` through another point `x` of `C`. The last
point of `C` on this ray lies in the intrinsic frontier of `C`
(`IsCompact.exists_lineMap_mem_intrinsicFrontier`): beyond it the ray leaves `C`, so it cannot be
an intrinsic interior point. No convexity is needed.
-/

public section

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] {C : Set E} {p x : E}

/-- On the ray from a point `p` of a compact set `C` through another point `x` of `C`, some point
at parameter `T ≥ 1` lies in the intrinsic frontier of `C`. -/
theorem IsCompact.exists_lineMap_mem_intrinsicFrontier (hC : IsCompact C) (hp : p ∈ C)
    (hx : x ∈ C) (hxp : x ≠ p) :
    ∃ T : ℝ, 1 ≤ T ∧ AffineMap.lineMap p x T ∈ intrinsicFrontier ℝ C := by
  -- the last parameter `T` at which the ray `f` is still in `C`
  set f : ℝ → E := ⇑(AffineMap.lineMap (k := ℝ) p x)
  have hf : Topology.IsClosedEmbedding f := by
    have : f = (· + p) ∘ fun t : ℝ => t • (x - p) := by
      ext t
      simp [f, AffineMap.lineMap_apply]
    rw [this]
    exact (Homeomorph.addRight p).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (sub_ne_zero.2 hxp))
  have hf1 : (1 : ℝ) ∈ f ⁻¹' C ∩ Ici 0 := ⟨by simpa [f] using hx, zero_le_one⟩
  obtain ⟨T, ⟨hTC, hT0⟩, hTmax⟩ :=
    ((hf.isCompact_preimage hC).inter_right isClosed_Ici).exists_isGreatest ⟨1, hf1⟩
  refine ⟨T, hTmax hf1, ?_⟩
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  refine ⟨subset_intrinsicClosure hTC, fun hTi => ?_⟩
  -- an intrinsic interior point would let the ray stay in `C` slightly past `T`
  obtain ⟨z, hz, hzT⟩ := mem_intrinsicInterior.1 hTi
  let g : ℝ → affineSpan ℝ C := fun t => ⟨f t, AffineMap.lineMap_mem t
    (subset_affineSpan ℝ C hp) (subset_affineSpan ℝ C hx)⟩
  have hg : ∀ t, (g t : E) = f t := fun _ => rfl
  have hgT : g T = z := Subtype.ext ((hg T).trans hzT.symm)
  have hgTi : g T ∈ interior ((↑) ⁻¹' C) := hgT ▸ hz
  have hnhds : g ⁻¹' interior ((↑) ⁻¹' C) ∈ nhds T :=
    (isOpen_interior.preimage (hf.continuous.subtype_mk _)).mem_nhds hgTi
  obtain ⟨u, hTu, hsub⟩ := exists_Ico_subset_of_mem_nhds hnhds ⟨T + 1, by linarith⟩
  have hmid : (T + u) / 2 ∈ Ico T u := ⟨by linarith, by linarith⟩
  have hgmid : g ((T + u) / 2) ∈ ((↑) ⁻¹' C : Set (affineSpan ℝ C)) :=
    interior_subset (hsub hmid)
  have hmemC : f ((T + u) / 2) ∈ C := by
    rw [← hg]
    exact mem_preimage.1 hgmid
  linarith [hTmax ⟨hmemC, mem_Ici.2 (by linarith [mem_Ici.1 hT0])⟩]
