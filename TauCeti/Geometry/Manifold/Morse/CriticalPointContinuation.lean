/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Morse.ModelTransport
import TauCeti.Analysis.Calculus.Morse.CriticalPointContinuation

/-!
# Continuation of nondegenerate critical points on manifolds

A nondegenerate critical point of a jointly `C³` real family on a finite-dimensional
boundaryless manifold extends to a locally unique `C²` branch. Nondegeneracy and the Morse
index persist, and the critical value is `C²`. At the base parameter, its derivative agrees
with the parameter derivative of the family at the original critical point.

The uniqueness assertion concerns a neighbourhood in the product of parameter and manifold,
not all critical points of a nearby member. The branch is a total function, but no properties
away from the base parameter are asserted. No compactness or properness is required.

The construction uses
`TauCeti.IsNondegenerateCriticalPoint.exists_contDiffAt_criticalPoint_continuation` in fixed
coordinates and the boundaryless model transport to retain the original manifold structure.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

private theorem exists_criticalPoint_continuation_self
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 3 M]
    {F : P × M → ℝ} {p : P} {x : M}
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (fun y ↦ F (p, y)) x)
    (hF : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ) 3 F (p, x)) :
    ∃ ψ : P → M,
      ψ p = x ∧ ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, E) 2 ψ p ∧
      (∀ᶠ q in 𝓝 p, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E)
        (fun y ↦ F (q, y)) (ψ q)) ∧
      (∀ᶠ q in 𝓝 p, manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ F (q, y)) (ψ q) =
        manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ F (p, y)) x) ∧
      (∀ᶠ q in 𝓝 (p, x), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun y ↦ F (q.1, y)) q.2 = 0 ↔
        ψ q.1 = q.2) ∧
      ContDiffAt ℝ 2 (fun q ↦ F (q, ψ q)) p ∧
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
  let c := chartAt E x
  let φ := extChartAt 𝓘(ℝ, E) x
  let G : P × E → ℝ := fun q ↦ F (q.1, φ.symm q.2)
  -- Construct the coordinate branch, then compose with the inverse chart for its regularity.
  have hx : x ∈ φ.source := mem_extChartAt_source x
  have hcx : φ x ∈ φ.target := mem_extChartAt_target x
  have hinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 3 φ.symm (φ x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hcx)
  have hG : ContDiffAt ℝ 3 G (p, φ x) := by
    have hcomp := hF.comp_of_eq (contDiffAt_fst.contMDiffAt.prodMk
      (hinv.comp (p, φ x) contDiffAt_snd.contMDiffAt)) (by simp [φ])
    exact contMDiffAt_iff_contDiffAt.mp hcomp
  have hcoord : IsNondegenerateCriticalPoint (fun v ↦ G (p, v)) (φ x) :=
    (isManifoldNondegenerateCriticalPoint_iff _).mp h
  obtain ⟨η, hηp, hη, hnd, hindex, huniq, hval, hderiv⟩ :=
    hcoord.exists_contDiffAt_criticalPoint_continuation hG
  let ψ : P → M := fun q ↦ φ.symm (η q)
  have hψp : ψ p = x := by simp [ψ, hηp, φ]
  have hψ : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, E) 2 ψ p := by
    have hinv' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 φ.symm (η p) := by
      rw [hηp]
      exact hinv.of_le (by norm_num)
    exact hinv'.comp p hη.contMDiffAt
  have htarget : ∀ᶠ q in 𝓝 p, η q ∈ φ.target :=
    hη.continuousAt.preimage_mem_nhds (hηp ▸ (isOpen_extChartAt_target x).mem_nhds hcx)
  have he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M := IsManifold.chart_mem_maximalAtlas x
  have hsliceFun (q : P) : (fun v ↦ G (q, v)) = (fun y ↦ F (q, y)) ∘ φ.symm := rfl
  -- Nondegeneracy and inertia are read in this fixed chart, not the varying preferred charts.
  have hnd' : ∀ᶠ q in 𝓝 p,
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (fun y ↦ F (q, y)) (ψ q) := by
    filter_upwards [hnd, htarget] with q hq ht
    exact isManifoldNondegenerateCriticalPoint_symm_of_mem_maximalAtlas he ht hq
  have hindex' : ∀ᶠ q in 𝓝 p,
      manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ F (q, y)) (ψ q) =
        manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ F (p, y)) x := by
    filter_upwards [hnd, hindex, htarget] with q hq hi ht
    have hchart : manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ F (q, y)) (ψ q) =
        morseIndex (fun v ↦ G (q, v)) (η q) :=
      manifoldMorseIndex_symm_eq_morseIndex_of_mem_maximalAtlas he ht hq
    rw [hchart, manifoldMorseIndex_def]
    exact hi
  -- Pull the joint uniqueness neighbourhood back through the coordinate map.
  have hmap : ContinuousAt (fun q : P × M ↦ (q.1, φ q.2)) (p, x) :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt (I := 𝓘(ℝ, E)) x).comp continuousAt_snd)
  have hGnear := hmap.eventually (hG.eventually (by norm_num))
  have hsnear : ∀ᶠ q : P × M in 𝓝 (p, x), q.2 ∈ φ.source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds x)
  have huniq' : ∀ᶠ q in 𝓝 (p, x),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun y ↦ F (q.1, y)) q.2 = 0 ↔ ψ q.1 = q.2 := by
    filter_upwards [hmap.eventually huniq, hGnear, hsnear,
      continuousAt_fst.preimage_mem_nhds htarget] with q hu hg hs ht
    have hslice : DifferentiableAt ℝ (fun v ↦ G (q.1, v)) (φ q.2) :=
      (hg.comp (φ q.2) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
        (by norm_num)
    rw [hsliceFun] at hslice
    rw [mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hs hslice]
    exact hu.trans (φ.symm_apply_eq hs ht).symm
  refine ⟨ψ, hψp, hψ, hnd', hindex', huniq', hval, ?_⟩
  simpa only [G, hηp, φ.left_inv hx] using hderiv

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  {F : P × M → ℝ} {p : P} {x : M}

/-- **Continuation of a nondegenerate critical point on a manifold.**

For a jointly `C³` family, a nondegenerate critical point extends to a locally unique `C²`
branch with unchanged Morse index. Its critical value is `C²`; at the base parameter its
derivative agrees with the parameter derivative of the family at the original spatial point.
All assertions except the value at the base parameter are local. In particular uniqueness
holds only near `(p, x)` and makes no global claim about the critical set. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_contMDiffAt_criticalPoint_continuation
    (h : IsManifoldNondegenerateCriticalPoint I (fun y ↦ F (p, y)) x)
    (hF : ContMDiffAt (𝓘(ℝ, P).prod I) 𝓘(ℝ) 3 F (p, x)) :
    ∃ ψ : P → M,
      ψ p = x ∧ ContMDiffAt 𝓘(ℝ, P) I 2 ψ p ∧
      (∀ᶠ q in 𝓝 p, IsManifoldNondegenerateCriticalPoint I (fun y ↦ F (q, y)) (ψ q)) ∧
      (∀ᶠ q in 𝓝 p, manifoldMorseIndex I (fun y ↦ F (q, y)) (ψ q) =
        manifoldMorseIndex I (fun y ↦ F (p, y)) x) ∧
      (∀ᶠ q in 𝓝 (p, x), mfderiv I 𝓘(ℝ) (fun y ↦ F (q.1, y)) q.2 = 0 ↔ ψ q.1 = q.2) ∧
      ContDiffAt ℝ 2 (fun q ↦ F (q, ψ q)) p ∧
      fderiv ℝ (fun q ↦ F (q, ψ q)) p = fderiv ℝ (fun q ↦ F (q, x)) p := by
  let e := BoundarylessModel.diffeomorph I (M := M) 3
  let F' : P × BoundarylessModel I M → ℝ := fun q ↦ F (q.1, e.symm q.2)
  have hcoe : ⇑e.symm = (BoundarylessModel.homeomorph I M).symm :=
    BoundarylessModel.coe_diffeomorph_symm I 3
  have hslice (q : P) : (fun y ↦ F' (q, y)) =
      (fun y ↦ F (q, y)) ∘ (BoundarylessModel.homeomorph I M).symm := by
    funext y
    simp only [F', e, BoundarylessModel.coe_diffeomorph_symm, comp_apply]
  have h' : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E)
      (fun y ↦ F' (p, y)) (e x) := by
    rw [hslice, BoundarylessModel.isManifoldNondegenerateCriticalPoint_iff,
      ← hcoe, e.symm_apply_apply]
    exact h
  have hF' : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ) 3 F' (p, e x) :=
    hF.comp_of_eq (contMDiffAt_fst.prodMk
      (e.symm.contMDiff.contMDiffAt.comp (p, e x) contMDiffAt_snd)) (by simp)
  obtain ⟨η, hηp, hη, hnd, hindex, huniq, hval, hderiv⟩ :=
    exists_criticalPoint_continuation_self h' hF'
  let ψ : P → M := fun q ↦ e.symm (η q)
  have hψp : ψ p = x := by simp [ψ, hηp]
  refine ⟨ψ, hψp, (e.symm.contMDiff.contMDiffAt.of_le (by norm_num)).comp p hη,
    ?_, ?_, ?_, hval, ?_⟩
  · filter_upwards [hnd] with q hq
    rw [hslice, BoundarylessModel.isManifoldNondegenerateCriticalPoint_iff, ← hcoe] at hq
    exact hq
  · filter_upwards [hindex] with q hq
    rw [hslice, hslice, BoundarylessModel.manifoldMorseIndex_eq,
      BoundarylessModel.manifoldMorseIndex_eq] at hq
    simpa only [← hcoe, e.symm_apply_apply] using hq
  · have hmap : ContinuousAt (fun q : P × M ↦ (q.1, e q.2)) (p, x) :=
      continuousAt_fst.prodMk (e.continuous.continuousAt.comp continuousAt_snd)
    filter_upwards [hmap.eventually huniq] with q hq
    have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun y ↦ F' (q.1, y)) (e q.2) = 0 ↔
        mfderiv I 𝓘(ℝ) (fun y ↦ F (q.1, y)) q.2 = 0 := by
      have hz := BoundarylessModel.mfderiv_source_eq_zero_iff I 𝓘(ℝ)
        (fun y ↦ F (q.1, y)) (e q.2)
      rw [← hcoe] at hz
      have heval : e.symm (e q.2) = q.2 := e.symm_apply_apply q.2
      rw [heval] at hz
      simpa only [F', comp_def] using hz
    exact hz.symm.trans (hq.trans e.toEquiv.symm_apply_eq.symm)
  · simpa only [F', hηp, e.symm_apply_apply] using hderiv

end TauCeti
