/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Kernel
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth bundles of split kernels

Let `A x : E →L[𝕜] F` be a family of operators and let `q : E →L[𝕜] G` be a fixed
complementary coordinate such that `(A x).prod q` is invertible. The kernel bundle
with its subspace topology and the chart `kernelTrivialization` is a smooth vector
bundle. If `A` is `C^n`, its inclusion into `X × E` is `C^n` as well. A map into
this bundle is `C^n` exactly when its base and underlying domain vector are `C^n`.
In particular, this characterizes smooth sections without unfolding kernel charts.

No finite-dimensionality is needed. These bundles supply the smooth structure
for finite-rank stabilized Fredholm kernels, whose determinant lines are the
local models for the Fredholm determinant bundle.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second
  edition, Appendix A.2 (stabilized kernels and determinant bundles).
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 X E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace HX] {I : ModelWithCorners 𝕜 EX HX}
  [TopologicalSpace X] [ChartedSpace HX X]
  {n : ℕ∞ω} {A : X → E →L[𝕜] F} {q : E →L[𝕜] G}

/-- The split-kernel chart defines a `C^n` vector bundle. Its chart transitions
are identities; smoothness of the ambient inclusion additionally requires
smoothness of `A`, as in `contMDiff_kernel_inclusion`. -/
theorem kernelContMDiffVectorBundle (hA : Continuous A)
    (h : ∀ x, ((A x).prod q).IsInvertible) :
    letI := kernelFiberBundle hA h
    letI := kernelVectorBundle hA h
    ContMDiffVectorBundle n G (fun x ↦ (A x).ker) I := by
  let := kernelFiberBundle hA h
  let := kernelVectorBundle hA h
  constructor
  intro e e' he he'
  have heq : e = kernelTrivialization hA h := by
    simpa only [trivializationAtlas_kernelFiberBundle, mem_singleton_iff] using he.out
  have heq' : e' = kernelTrivialization hA h := by
    simpa only [trivializationAtlas_kernelFiberBundle, mem_singleton_iff] using he'.out
  subst e
  subst e'
  have hc (x : X) : (kernelTrivialization hA h).coordChangeL 𝕜
      (kernelTrivialization hA h) x = ContinuousLinearEquiv.refl 𝕜 G := by
    ext v
    rw [Trivialization.coordChangeL_apply']
    · simp
    · simp
  simp only [hc]
  exact contMDiffOn_const

variable (hA : ContMDiff I 𝓘(𝕜, E →L[𝕜] F) n A)
  (h : ∀ x, ((A x).prod q).IsInvertible)

include hA h in
/-- The bounded inverse kernel parametrization has the regularity of the
operator family, including for Banach-manifold parameter spaces. -/
theorem _root_.ContinuousLinearMap.contMDiff_kerSection :
    ContMDiff I 𝓘(𝕜, G →L[𝕜] E) n (fun x ↦ (A x).kerSection q) := by
  intro x
  exact (ContinuousLinearMap.contDiffAt_kerSection (n := n) (h x)).comp_contMDiffAt
    (f := fun x ↦ (A x, q)) ((hA x).prodMk_space contMDiffAt_const)

section Maps

variable {M EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

/-- A map into the split-kernel bundle is `C^n` within a set at a point
exactly when its base and its underlying domain vector are `C^n` there. -/
theorem contMDiffWithinAt_kernel_iff
    {f : M → TotalSpace G (fun x ↦ (A x).ker)} {s : Set M} {y : M} :
    letI := kernelFiberBundle hA.continuous h
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, G)) n f s y ↔
      ContMDiffWithinAt J I n (fun z ↦ (f z).proj) s y ∧
      ContMDiffWithinAt J 𝓘(𝕜, E) n (fun z ↦ ((f z).2 : E)) s y := by
  let := kernelFiberBundle hA.continuous h
  rw [Bundle.contMDiffWithinAt_totalSpace_iff]
  simp only [trivializationAt_kernelFiberBundle, kernelTrivialization_apply]
  constructor
  · rintro ⟨hb, hv⟩
    refine ⟨hb, ?_⟩
    have hs := (((ContinuousLinearMap.contMDiff_kerSection hA h) (f y).proj).comp_contMDiffWithinAt
      y hb).clm_apply hv
    exact hs.congr (fun z _ ↦
      (ContinuousLinearMap.kerSection_apply_of_mem_ker (h (f z).proj) (f z).2.property).symm)
      (ContinuousLinearMap.kerSection_apply_of_mem_ker (h (f y).proj) (f y).2.property).symm
  · rintro ⟨hb, hv⟩
    exact ⟨hb, q.contDiff.comp_contMDiffWithinAt hv⟩

/-- Smoothness of a map into a split-kernel bundle can be checked in the
ambient product, with no chosen kernel coordinates in the criterion. -/
theorem contMDiff_kernel_iff
    {f : M → TotalSpace G (fun x ↦ (A x).ker)} :
    letI := kernelFiberBundle hA.continuous h
    ContMDiff J (I.prod 𝓘(𝕜, G)) n f ↔
      ContMDiff J I n (fun z ↦ (f z).proj) ∧
      ContMDiff J 𝓘(𝕜, E) n (fun z ↦ ((f z).2 : E)) := by
  let := kernelFiberBundle hA.continuous h
  constructor
  · intro hf
    have hp y := (contMDiffWithinAt_kernel_iff hA h (s := univ)).mp
      (hf y).contMDiffWithinAt
    exact ⟨fun y ↦ (hp y).1.contMDiffAt Filter.univ_mem,
      fun y ↦ (hp y).2.contMDiffAt Filter.univ_mem⟩
  · rintro ⟨hb, hv⟩ y
    exact ((contMDiffWithinAt_kernel_iff hA h (s := univ)).mpr
      ⟨(hb y).contMDiffWithinAt, (hv y).contMDiffWithinAt⟩).contMDiffAt Filter.univ_mem

end Maps

/-- The natural inclusion of the split-kernel total space into the ambient
product is `C^n` when the operator family is `C^n`. -/
theorem contMDiff_kernel_inclusion :
    letI := kernelFiberBundle hA.continuous h
    ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, E)) n
      (fun p : TotalSpace G (fun x ↦ (A x).ker) ↦ (p.proj, (p.2 : E))) := by
  let := kernelFiberBundle hA.continuous h
  have hi := (contMDiff_kernel_iff hA h).mp
    (contMDiff_id (I := I.prod 𝓘(𝕜, G)) (n := n))
  exact hi.1.prodMk hi.2

/-- A section of the kernel bundle is `C^n` exactly when its underlying
`E`-valued section is `C^n`. -/
theorem contMDiff_kernel_section_iff {v : ∀ x, (A x).ker} :
    letI := kernelFiberBundle hA.continuous h
    ContMDiff I (I.prod 𝓘(𝕜, G)) n (fun x ↦ TotalSpace.mk' G x (v x)) ↔
      ContMDiff I 𝓘(𝕜, E) n (fun x ↦ (v x : E)) := by
  let := kernelFiberBundle hA.continuous h
  rw [contMDiff_kernel_iff hA h]
  exact and_iff_right contMDiff_id

end TauCeti
