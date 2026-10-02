/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import TauCeti.Analysis.Fredholm.Index

/-!
# Linearization of a section at a zero

At a zero of a differentiable section, differentiating its fiber coordinates and transporting
back to the fiber gives a linear map independent of the trivialization. Away from a zero,
the derivative of the transition function contributes an additional term, so no such
independence is asserted.

We work with a section along a map from a normed parameter space to a manifold. This includes
sections over Banach spaces and the local expressions of sections over Banach manifolds in
base charts. The coordinate-change formula shows that Fredholmness, the index, and regularity
(surjectivity) at zeros can be checked in any bundle trivialization.

The convention is that of McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
2nd ed., Appendix A.3. The calculation uses Mathlib's bundle coordinate changes and the
Fréchet derivative rule `HasFDerivAt.clm_apply`.
-/

public section

open Bundle Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 X B F EB HB : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ a, TopologicalSpace (E a)] [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E I]
  {b : X → B} {s : ∀ y, E (b y)} {x : X}

variable {e e' : Trivialization F (π F E)}
  [MemTrivializationAtlas e] [MemTrivializationAtlas e']

/-- Differentiate a section along `b` in the preferred trivialization at `b x`, then transport
the derivative back to that fiber. At a zero of a differentiable section this is independent
of the trivialization, as expressed by `sectionLinearization_eq_symmL_comp`.

As with `fderiv`, this expression is defined even where differentiability fails. -/
noncomputable def sectionLinearization (b : X → B) (s : ∀ y, E (b y)) (x : X) :
    X →L[𝕜] E (b x) :=
  ((trivializationAt F E (b x)).symmL 𝕜 (b x)).comp
    (fderiv 𝕜 (fun y ↦ (trivializationAt F E (b x) ⟨b y, s y⟩).2) x)

/-- The defining expression for the linearization in the preferred trivialization. -/
theorem sectionLinearization_def :
    sectionLinearization (𝕜 := 𝕜) (F := F) b s x =
      ((trivializationAt F E (b x)).symmL 𝕜 (b x)).comp
        (fderiv 𝕜 (fun y ↦ (trivializationAt F E (b x) ⟨b y, s y⟩).2) x) :=
  (rfl)

/-- The zero section along a continuous map has zero linearization. -/
@[simp]
theorem sectionLinearization_zero (hb : ContinuousAt b x) :
    sectionLinearization (𝕜 := 𝕜) (F := F) b (fun y ↦ (0 : E (b y))) x = 0 := by
  have hcoord : (fun y ↦ (trivializationAt F E (b x) ⟨b y, (0 : E (b y))⟩).2)
      =ᶠ[nhds x] fun _ ↦ (0 : F) := by
    filter_upwards [hb.preimage_mem_nhds
      ((trivializationAt F E (b x)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E (b x)))] with y hy
    exact congrArg Prod.snd ((trivializationAt F E (b x)).zeroSection 𝕜 hy)
  rw [sectionLinearization_def, hcoord.fderiv_eq]
  simp

/-- At a zero of a section along a differentiable map, its coordinate derivatives in two
bundle trivializations differ by postcomposition with the fiber coordinate change. -/
theorem fderiv_section_coordChange_of_eq_zero
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    fderiv 𝕜 (fun y ↦ (e' ⟨b y, s y⟩).2) x =
      (e.coordChangeL 𝕜 e' (b x) : F →L[𝕜] F).comp
        (fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  have hA : DifferentiableAt 𝕜
      (fun y ↦ (e.coordChangeL 𝕜 e' (b y) : F →L[𝕜] F)) x :=
    (hb.coordChangeL he he').differentiableAt
  have hz : (e ⟨b x, s x⟩).2 = 0 := by
    rw [hzero]
    exact congrArg Prod.snd (e.zeroSection 𝕜 he)
  have hderiv := hA.hasFDerivAt.clm_apply hs.hasFDerivAt
  simp only [hz, map_zero, add_zero] at hderiv
  have hcoord : (fun y ↦ (e.coordChangeL 𝕜 e' (b y)) ((e ⟨b y, s y⟩).2))
      =ᶠ[nhds x] (fun y ↦ (e' ⟨b y, s y⟩).2) := by
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      ((e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩)] with y hy
    rw [Trivialization.coordChangeL_apply e e' hy,
      e.symm_apply_apply_mk hy.1]
  exact (hderiv.congr_of_eventuallyEq hcoord.symm).fderiv

/-- At a zero, the linearization can be computed in any bundle trivialization whose fiber
coordinates are differentiable at the parameter. -/
theorem sectionLinearization_eq_symmL_comp
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x) (he : b x ∈ e.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    sectionLinearization (𝕜 := 𝕜) (F := F) b s x =
      (e.symmL 𝕜 (b x)).comp (fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [sectionLinearization_def, fderiv_section_coordChange_of_eq_zero hb he
    (mem_baseSet_trivializationAt F E (b x)) hs hzero]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply e (trivializationAt F E (b x))
    ⟨he, mem_baseSet_trivializationAt F E (b x)⟩,
    Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F E (b x)),
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F E (b x)),
    Trivialization.symmL_apply _ he]

/-- Reading the intrinsic linearization in a trivialization recovers the derivative of the
section's fiber coordinates. -/
theorem continuousLinearMapAt_comp_sectionLinearization
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x) (he : b x ∈ e.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    (e.continuousLinearMapAt 𝕜 (b x)).comp
        (sectionLinearization (𝕜 := 𝕜) (F := F) b s x) =
      fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero]
  ext v
  simp only [ContinuousLinearMap.comp_apply, e.continuousLinearMapAt_symmL he]

/-- A zero is regular for the intrinsic linearization exactly when its coordinate derivative
is surjective. -/
theorem surjective_sectionLinearization_iff
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x) (he : b x ∈ e.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    Function.Surjective (sectionLinearization (𝕜 := 𝕜) (F := F) b s x) ↔
      Function.Surjective (fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he]
  exact Function.Surjective.of_comp_iff' (e.continuousLinearEquivAt 𝕜 (b x) he).symm.bijective _

/-- The Fredholm index of a section's coordinate derivative at a zero is independent of
the bundle trivialization. No Fredholm hypothesis is needed for this equality of indices. -/
theorem index_fderiv_section_coordChange_of_eq_zero
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    ContinuousLinearMap.index (fderiv 𝕜 (fun y ↦ (e' ⟨b y, s y⟩).2) x) =
      ContinuousLinearMap.index (fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [fderiv_section_coordChange_of_eq_zero hb he he' hs hzero]
  exact ContinuousLinearMap.index_equiv_comp _

/-- Fredholmness of a section's coordinate derivative at a zero is independent of
the bundle trivialization. -/
theorem isFredholm_fderiv_section_coordChange_iff_of_eq_zero [CompleteSpace 𝕜]
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    ContinuousLinearMap.IsFredholm (fderiv 𝕜 (fun y ↦ (e' ⟨b y, s y⟩).2) x) ↔
      ContinuousLinearMap.IsFredholm (fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [fderiv_section_coordChange_of_eq_zero hb he he' hs hzero]
  exact ContinuousLinearMap.isFredholm_equiv_comp

/-- Surjectivity of a section's coordinate derivative at a zero is independent of
the bundle trivialization, so regular zeros can be tested in any fiber coordinates. -/
theorem surjective_fderiv_section_coordChange_iff_of_eq_zero
    (hb : MDifferentiableAt 𝓘(𝕜, X) I b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : DifferentiableAt 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    Function.Surjective (fderiv 𝕜 (fun y ↦ (e' ⟨b y, s y⟩).2) x) ↔
      Function.Surjective (fderiv 𝕜 (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [fderiv_section_coordChange_of_eq_zero hb he he' hs hzero]
  exact Function.Surjective.of_comp_iff'
    (e.coordChangeL 𝕜 e' (b x)).bijective _

/-- In a trivial bundle, the linearization of a section along any map is just the ordinary
Fréchet derivative of its fiber component. -/
@[simp]
theorem sectionLinearization_trivial (b : X → B) (f : X → F) (x : X) :
    sectionLinearization (𝕜 := 𝕜) (F := F) (E := Bundle.Trivial B F) b f x =
      fderiv 𝕜 f x := by
  rw [sectionLinearization_def]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply,
    Bundle.Trivial.symmL_trivialization, ContinuousLinearMap.id_comp]

end TauCeti
