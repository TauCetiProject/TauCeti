/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Smooth and holomorphic dual cores

Dualizing a finite-rank bundle core preserves its regularity: dual transitions are the
transposes of reverse transitions, and transposition is continuous linear. Over a complex
manifold this constructs the holomorphic dual on the existing dual-core carrier.

`dualTotalSpaceDiffeomorph` identifies that construction with Mathlib's dual bundle, the
bundle of continuous linear maps to the trivial line. Its underlying homeomorphism is
`dualTotalSpaceHomeomorph`; in a frame it reads a dual coordinate vector as the functional
with those coefficients. It is `𝕜`-linear on fibres (complex-linear, not conjugate-linear,
when `𝕜 = ℂ`).
The naturality formula `dualFiberEquiv_fiberMap_dualMap` for the underlying identification
also describes this diffeomorphism.

No regularity of the base atlas or transitions is needed for the comparison itself: its
expression in the corresponding bundle charts is a fixed continuous linear equivalence.
The regularity instance supplies the smooth bundle structure when the original core is smooth.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The dual of a `C^n` finite-rank core is `C^n`. For complex scalars at regularity `∞`,
this is the holomorphic dual structure on the shared dual core. -/
instance isContMDiff_dual (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n] :
    A.dual.core.IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    -- The dual core keeps the same coordinate spaces and chart domains; unfold its
    -- projections before elaborating the operator-space topology and the composition.
    dsimp +instances only [dual]
    have ht := (ContinuousLinearMap.piTransposeL 𝕜 (Fin A.rank) (Fin A.rank)).contMDiff
      |>.comp_contMDiffOn ((A.core.contMDiffOn_coordChange (n := n) I j i).mono
        (fun _ (hx : _ ∈ A.core.baseSet i ∩ A.core.baseSet j) ↦ ⟨hx.2, hx.1⟩))
    simpa only [Function.comp_def, ContinuousLinearMap.piTransposeL_apply] using ht

/-- Reading the vectors of the dual core as functionals is `C^n` on total spaces, in the
induced dual-bundle charts. -/
theorem contMDiff_dualFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] 𝕜)) n
      (fun p : A.dual.core.TotalSpace ↦
        TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
          (E := fun x ↦ A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) p.proj
          (dualFiberEquiv A p.proj p.2)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hp : p ∈ (A.dual.core.localTriv p.proj).source :=
    (A.dual.core.mem_localTriv_source p.proj p).2 (A.dual.core.mem_baseSet_at p.proj)
  have hU := (A.dual.core.localTriv p.proj).open_source.mem_nhds hp
  have hc := Bundle.TotalSpace.contMDiffAt_trivializationAt_snd
    (IB := I) (n := n) p
  have htriv : trivializationAt (Fin A.dual.rank → 𝕜) A.dual.core.Fiber p.proj =
      A.dual.core.localTriv p.proj := by
    rw [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt, A.dual.indexAt_eq]
  rw [htriv] at hc
  refine ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin A.rank)).symm.contDiff.contMDiff
    |>.contMDiffAt.comp p hc).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  exact (A.dualFiberEquiv_inCoordinates p.proj q.proj
    ((A.dual.core.mem_localTriv_source p.proj q).1 hq) q.2)

/-- The dual core and Mathlib's dual bundle are `C^n` diffeomorphic by the canonical
`𝕜`-linear identification of each coordinate vector with a functional. -/
noncomputable def dualTotalSpaceDiffeomorph (A : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.dual.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.dual.rank → 𝕜),
      I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] 𝕜)⟯
        TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
          (fun x ↦ A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) :=
  bundleDiffeomorph (dualFiberEquiv A) (A.contMDiff_dualFiberEquiv (I := I) (n := n))

/-- The diffeomorphism retains the canonical dual-bundle homeomorphism. -/
@[simp]
theorem dualTotalSpaceDiffeomorph_toHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    (A.dualTotalSpaceDiffeomorph I n).toHomeomorph = A.dualTotalSpaceHomeomorph := by
  apply Homeomorph.ext
  intro p
  exact (bundleDiffeomorph_apply (IB := I) (n := n) (dualFiberEquiv A)
    A.contMDiff_dualFiberEquiv p).trans (A.dualTotalSpaceHomeomorph_apply p).symm

/-- The forward comparison reads a dual coordinate vector as a functional in the same fibre. -/
@[simp]
theorem dualTotalSpaceDiffeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.core.TotalSpace) :
    A.dualTotalSpaceDiffeomorph I n p = ⟨p.proj, dualFiberEquiv A p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- The inverse comparison records the coefficients of the functional in the same fibre. -/
@[simp]
theorem dualTotalSpaceDiffeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
      (fun x ↦ A.core.Fiber x →L[𝕜] Trivial B 𝕜 x)) :
    (A.dualTotalSpaceDiffeomorph I n).symm p =
      ⟨p.proj, (dualFiberEquiv A p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end TauCeti.FiniteRankBundleCore
