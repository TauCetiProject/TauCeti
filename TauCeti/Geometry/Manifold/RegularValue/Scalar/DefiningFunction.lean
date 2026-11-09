/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Globalizing a local defining function

A smooth function on an open subset of a manifold whose nonpositive locus is closed in the
whole manifold extends to a global smooth defining function for that locus. The extension
agrees with the original function near every point of the nonpositive locus and is strictly
positive elsewhere. Consequently regularity of its zero level is preserved.

This allows a defining function in tubular coordinates to describe an exterior in the ambient
manifold, including points outside the coordinate neighbourhood. The construction combines the
local function with the positive constant one using Mathlib's smooth Urysohn lemma
`exists_contMDiffMap_zero_one_nhds_of_isClosed`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 5.47
  (regular domains), and Chapter 2 (smooth cutoffs).
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Globalize a local smooth defining function without changing its germ on the closed
nonpositive locus. Its strict negative and zero loci are also preserved, and it is positive
outside the original domain. Closedness is required in the ambient manifold. -/
theorem exists_contMDiffMap_definingFunction {n : ℕ∞} {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ) n f U) (hs : IsClosed {x | x ∈ U ∧ f x ≤ 0}) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯,
      (∀ x ∈ U, f x ≤ 0 → (g : M → ℝ) =ᶠ[𝓝 x] f) ∧
      (∀ x, g x ≤ 0 ↔ x ∈ U ∧ f x ≤ 0) ∧
      (∀ x, g x < 0 ↔ x ∈ U ∧ f x < 0) ∧
      (∀ x, g x = 0 ↔ x ∈ U ∧ f x = 0) := by
  have := Manifold.locallyCompact_of_finiteDimensional I (M := M)
  obtain ⟨β, hβ0, hβ1, hβ⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I
    (n := n) hU.isClosed_compl hs (by
      exact disjoint_left.mpr fun x hx hx' => hx hx'.1)
  have hsupport : tsupport β ⊆ U := by
    intro x hx
    by_contra h
    have hz : ∀ᶠ y in 𝓝 x, β y = 0 :=
      hβ0.filter_mono (nhds_le_nhdsSet h)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  have hprod : ContMDiff I 𝓘(ℝ) n (fun x => β x * f x) := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU := hsupport (tsupport_mul_subset_left hx)
    exact β.contMDiff.contMDiffAt.mul (hf.contMDiffAt (hU.mem_nhds hxU))
  let g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x => β x * f x + (1 - β x), hprod.add (contMDiff_const.sub β.contMDiff)⟩
  have hgerm (x : M) (hx : x ∈ U ∧ f x ≤ 0) : (g : M → ℝ) =ᶠ[𝓝 x] f := by
    filter_upwards [hβ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [g, hy]
  have hpos (x : M) (hx : ¬ (x ∈ U ∧ f x ≤ 0)) : 0 < g x := by
    by_cases hb : β x = 0
    · simp [g, hb]
    · have hxU : x ∈ U := hsupport (subset_closure hb)
      have hfpos : 0 < f x := lt_of_not_ge fun h => hx ⟨hxU, h⟩
      have hbpos : 0 < β x := lt_of_le_of_ne (hβ x).1 (Ne.symm hb)
      exact add_pos_of_pos_of_nonneg (mul_pos hbpos hfpos) (sub_nonneg.mpr (hβ x).2)
  refine ⟨g, fun x hxU hx => hgerm x ⟨hxU, hx⟩, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U ∧ f x ≤ 0
    · simp [hx, (hgerm x hx).eq_of_nhds]
    · exact iff_of_false (not_le.mpr (hpos x hx)) hx
  · intro x
    by_cases hx : x ∈ U ∧ f x ≤ 0
    · rw [(hgerm x hx).eq_of_nhds]
      simp [hx.1]
    · exact iff_of_false (not_lt.mpr (hpos x hx).le) (fun h => hx ⟨h.1, h.2.le⟩)
  · intro x
    by_cases hx : x ∈ U ∧ f x ≤ 0
    · rw [(hgerm x hx).eq_of_nhds]
      simp [hx.1]
    · exact iff_of_false (hpos x hx).ne' (fun h => hx ⟨h.1, h.2.le⟩)

/-- If the local defining function has no critical point on its zero locus, its globalization
has zero as a regular value. In particular the construction preserves the regular hypersurface,
the closed domain, and its strict negative locus simultaneously. -/
theorem exists_contMDiffMap_regular_definingFunction {n : ℕ∞} {U : Set M}
    (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ) n f U) (hs : IsClosed {x | x ∈ U ∧ f x ≤ 0})
    (hreg : ∀ x ∈ U, f x = 0 → IsRegularPoint I 𝓘(ℝ) f x) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, IsRegularValue I 𝓘(ℝ) g 0 ∧
      (∀ x ∈ U, f x ≤ 0 → (g : M → ℝ) =ᶠ[𝓝 x] f) ∧
      (∀ x, g x ≤ 0 ↔ x ∈ U ∧ f x ≤ 0) ∧
      (∀ x, g x < 0 ↔ x ∈ U ∧ f x < 0) ∧
      (∀ x, g x = 0 ↔ x ∈ U ∧ f x = 0) := by
  obtain ⟨g, hgerm, hle, hlt, heq⟩ := exists_contMDiffMap_definingFunction hU hf hs
  refine ⟨g, ?_, hgerm, hle, hlt, heq⟩
  rw [isRegularValue_iff]
  intro x hx
  obtain ⟨hxU, hfx⟩ := (heq x).mp hx
  rw [isRegularPoint_iff, (hgerm x hxU hfx.le).mfderiv_eq]
  exact (tangentSpaceCast 𝓘(ℝ) (f x) (g x)).surjective.comp
    (isRegularPoint_iff.mp (hreg x hxU hfx))

end TauCeti

namespace PartialDiffeomorph

open TauCeti

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

/-- A regular domain carried into a manifold by smooth coordinates has a global regular
defining function, provided its closed domain lies in the coordinate source and has closed
image. The function retains the original defining germ throughout that image. -/
theorem exists_contMDiffMap_regular_definingFunction
    (Φ : PartialDiffeomorph I J M N ∞) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f Φ.source)
    (hsource : {x | f x ≤ 0} ⊆ Φ.source)
    (hclosed : IsClosed (Φ '' {x | f x ≤ 0}))
    (hreg : ∀ x, f x = 0 → IsRegularPoint I 𝓘(ℝ) f x) :
    ∃ g : C^∞⟮J, N; 𝓘(ℝ), ℝ⟯, IsRegularValue J 𝓘(ℝ) g 0 ∧
      (∀ x, f x ≤ 0 → (g : N → ℝ) =ᶠ[𝓝 (Φ x)] f ∘ Φ.symm) ∧
      {y | g y ≤ 0} = Φ '' {x | f x ≤ 0} ∧
      {y | g y < 0} = Φ '' {x | f x < 0} ∧
      {y | g y = 0} = Φ '' {x | f x = 0} := by
  have himage {s : Set M} (hs : s ⊆ Φ.source) :
      Φ '' s = {y | y ∈ Φ.target ∧ Φ.symm y ∈ s} :=
    Φ.toPartialEquiv.image_eq_target_inter_inv_preimage hs
  have hle := himage hsource
  have hlt := himage (s := {x | f x < 0}) (fun x (hx : f x < 0) => hsource hx.le)
  have heq := himage (s := {x | f x = 0}) (fun x (hx : f x = 0) => hsource hx.le)
  have hlocal : ContMDiffOn J 𝓘(ℝ) ∞ (f ∘ Φ.symm) Φ.target :=
    hf.comp Φ.contMDiffOn_invFun Φ.toPartialEquiv.symm.mapsTo
  obtain ⟨g, hg, hgerm, hgle, hglt, hgeq⟩ :=
    TauCeti.exists_contMDiffMap_regular_definingFunction Φ.open_target hlocal
      (hle ▸ hclosed) (fun y hy hfy => by
        have hinv :=
          (PartialDiffeomorph.isLocalDiffeomorphAt J I ∞ Φ.symm hy).isInvertible_mfderiv (by simp)
        exact (hreg _ hfy).comp (isRegularPoint_iff.mpr hinv.surjective))
  refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxsource := hsource hx
    apply hgerm _ (Φ.toPartialEquiv.map_source hxsource)
    simpa only [comp_apply, PartialDiffeomorph.symm_toPartialEquiv,
      Φ.toPartialEquiv.left_inv hxsource] using hx
  · exact (Set.ext hgle).trans hle.symm
  · exact (Set.ext hglt).trans hlt.symm
  · exact (Set.ext hgeq).trans heq.symm

end PartialDiffeomorph
