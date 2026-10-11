/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# Linearization of a section at a zero

At a zero of a differentiable section, differentiating its fiber coordinates and transporting
back to the fiber gives a linear map from the tangent space of the source to the fiber,
independent of the trivialization. Away from a zero, the derivative of the transition function
contributes an additional term, so no such independence is asserted.

We work with a section along a map from a manifold `M` to the base of the bundle. This includes
sections over Banach manifolds, and sections over Banach spaces with their canonical manifold
structure `𝓘(𝕜, X)`, for which `mvfderiv_eq_fderiv` recovers the Fréchet derivative. The
coordinate-change formula shows that Fredholmness, the index, and regularity (surjectivity) at
zeros can be checked in any bundle trivialization, and the chain rule
`sectionLinearization_comp` passes between a manifold source and its source charts.

The convention is that of McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
2nd ed., Appendix A.3. The calculation uses Mathlib's bundle coordinate changes and the
zero-value derivative rule `TauCeti.mvfderiv_eq_comp_of_eventuallyEq_clm_apply`.
-/

public section

open Bundle Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 EM HM M B F : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace B]
  [∀ a, TopologicalSpace (E a)] [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : M → B} {s : ∀ y, E (b y)} {x : M}

variable {e e' : Trivialization F (π F E)}
  [MemTrivializationAtlas e] [MemTrivializationAtlas e']

variable (IM) in
/-- Differentiate a section along `b` in the preferred trivialization at `b x`, then transport
the derivative back to that fiber. At a zero of a differentiable section this is independent
of the trivialization, as expressed by `sectionLinearization_eq_symmL_comp`.

As with `mfderiv`, this expression is defined even where differentiability fails. -/
noncomputable def sectionLinearization (b : M → B) (s : ∀ y, E (b y)) (x : M) :
    TangentSpace IM x →L[𝕜] E (b x) :=
  ((trivializationAt F E (b x)).symmL 𝕜 (b x)).comp
    (mvfderiv IM (fun y ↦ (trivializationAt F E (b x) ⟨b y, s y⟩).2) x)

/-- The defining expression for the linearization in the preferred trivialization. -/
theorem sectionLinearization_def :
    sectionLinearization (F := F) IM b s x =
      ((trivializationAt F E (b x)).symmL 𝕜 (b x)).comp
        (mvfderiv IM (fun y ↦ (trivializationAt F E (b x) ⟨b y, s y⟩).2) x) :=
  (rfl)

/-- The zero section along a continuous map has zero linearization. -/
@[simp]
theorem sectionLinearization_zero (hb : ContinuousAt b x) :
    sectionLinearization (F := F) IM b (fun y ↦ (0 : E (b y))) x = 0 := by
  have hcoord : (fun y ↦ (trivializationAt F E (b x) ⟨b y, (0 : E (b y))⟩).2)
      =ᶠ[𝓝 x] fun _ ↦ (0 : F) := by
    filter_upwards [hb.preimage_mem_nhds
      ((trivializationAt F E (b x)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E (b x)))] with y hy
    exact congrArg Prod.snd ((trivializationAt F E (b x)).zeroSection 𝕜 hy)
  rw [sectionLinearization_def, mvfderiv, hcoord.mfderiv_eq, mfderiv_const]
  simp

/-- At a zero of a section along a continuous map, its coordinate derivatives in two
bundle trivializations differ by postcomposition with the fiber coordinate change. -/
theorem mvfderiv_section_coordChange_of_eq_zero
    (hb : ContinuousAt b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    mvfderiv IM (fun y ↦ (e' ⟨b y, s y⟩).2) x =
      (e.coordChangeL 𝕜 e' (b x) : F →L[𝕜] F).comp
        (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  have hc : ContinuousAt (fun y ↦ (e.coordChangeL 𝕜 e' (b y) : F →L[𝕜] F)) x :=
    ((continuousOn_coordChange 𝕜 e e').continuousAt
      ((e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩)).comp hb
  have hz : (e ⟨b x, s x⟩).2 = 0 := by
    rw [hzero]
    exact congrArg Prod.snd (e.zeroSection 𝕜 he)
  have hcoord : (fun y ↦ (e.coordChangeL 𝕜 e' (b y) : F →L[𝕜] F) ((e ⟨b y, s y⟩).2))
      =ᶠ[𝓝 x] (fun y ↦ (e' ⟨b y, s y⟩).2) := by
    filter_upwards [hb.preimage_mem_nhds
      ((e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩)] with y hy
    rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply e e' hy,
      e.symm_apply_apply_mk hy.1]
  exact mvfderiv_eq_comp_of_eventuallyEq_clm_apply hcoord hc hs hz

/-- At a zero, the linearization can be computed in any bundle trivialization whose fiber
coordinates are differentiable at the point. -/
theorem sectionLinearization_eq_symmL_comp
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    sectionLinearization (F := F) IM b s x =
      (e.symmL 𝕜 (b x)).comp (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [sectionLinearization_def, mvfderiv_section_coordChange_of_eq_zero hb he
    (mem_baseSet_trivializationAt F E (b x)) hs hzero]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply e (trivializationAt F E (b x))
    ⟨he, mem_baseSet_trivializationAt F E (b x)⟩,
    Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F E (b x)),
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F E (b x)),
    Trivialization.symmL_apply _ he]

/-- At a zero, the kernel inclusion composed with the inverse of a kernel-model equivalence
has range equal to the kernel of the intrinsic section linearization. -/
theorem range_subtypeL_comp_eq_ker_sectionLinearization {T : TangentSpace IM x →L[𝕜] F}
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasMFDerivAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x T) (hz : s x = 0)
    (K : T.ker ≃L[𝕜] G) :
    (T.ker.subtypeL.comp (K.symm : G →L[𝕜] T.ker)).range =
      (sectionLinearization (F := F) IM b s x).ker := by
  have hT : mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x = T := by
    rw [hf.mdifferentiableAt.mvfderiv]
    exact hf.2.fderivWithin IM.uniqueDiffWithinAt_image
  rw [sectionLinearization_eq_symmL_comp hb he hf.mdifferentiableAt hz,
    hT, ← e.symm_continuousLinearEquivAt_eq' he]
  simp only [ContinuousLinearMap.toLinearMap_comp, Submodule.toLinearMap_subtypeL,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.range_comp_of_range_eq_top T.ker.subtype
    (f := K.symm.toLinearEquiv.toLinearMap) K.symm.toLinearEquiv.range,
    LinearMap.ker_comp_of_ker_eq_bot T.toLinearMap
      (LinearMap.ker_eq_bot.2 (e.continuousLinearEquivAt 𝕜 (b x) he).symm.injective)]
  exact Submodule.range_subtype _

/-- Reading the intrinsic linearization in a trivialization recovers the derivative of the
section's fiber coordinates. -/
theorem continuousLinearMapAt_comp_sectionLinearization
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    (e.continuousLinearMapAt 𝕜 (b x)).comp (sectionLinearization (F := F) IM b s x) =
      mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero]
  ext v
  simp only [ContinuousLinearMap.comp_apply, e.continuousLinearMapAt_symmL he]

/-- A zero is regular for the intrinsic linearization exactly when its coordinate derivative
is surjective. -/
theorem surjective_sectionLinearization_iff
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    Function.Surjective (sectionLinearization (F := F) IM b s x) ↔
      Function.Surjective (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he]
  exact Function.Surjective.of_comp_iff' (e.continuousLinearEquivAt 𝕜 (b x) he).symm.bijective _

/-- At a zero, the intrinsic linearization has the same kernel as the derivative of any
differentiable fiber-coordinate expression. -/
theorem ker_sectionLinearization
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    (sectionLinearization (F := F) IM b s x).ker =
      (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x).ker := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he]
  ext v
  simp

/-- At a zero, the intrinsic linearization and any differentiable fiber-coordinate
expression have the same Fredholm index. -/
theorem index_sectionLinearization
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    LinearMap.index (sectionLinearization (F := F) IM b s x).toLinearMap =
      LinearMap.index (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x).toLinearMap := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.index_equiv_comp]

/-- A section's intrinsic linearization at a zero is Fredholm exactly when its derivative
in any differentiable fiber-coordinate expression is Fredholm. -/
theorem isFredholm_sectionLinearization_iff
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    ContinuousLinearMap.IsFredholm (sectionLinearization (F := F) IM b s x) ↔
      ContinuousLinearMap.IsFredholm (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [sectionLinearization_eq_symmL_comp hb he hs hzero,
    ← e.symm_continuousLinearEquivAt_eq' he]
  let A := e.continuousLinearEquivAt 𝕜 (b x) he
  -- Transport a norm to the fiber while retaining its given topology and module structure.
  let : NormedAddCommGroup (E (b x)) :=
    { (NormedAddCommGroup.induced (E (b x)) F A.toLinearEquiv A.injective).replaceTopology
        A.toHomeomorph.isInducing.eq_induced with
      toAddCommGroup := inferInstance
      norm := fun v ↦ ‖A v‖
      dist_eq := (NormedAddCommGroup.induced (E (b x)) F A.toLinearEquiv A.injective).dist_eq }
  let : NormedSpace 𝕜 (E (b x)) :=
    { norm_smul_le c v := by simpa only [← map_smul A c v] using! norm_smul_le c (A v) }
  -- Read the derivative as an operator on the model space, which carries the norm.
  suffices h : ∀ D : EM →L[𝕜] F, ContinuousLinearMap.IsFredholm
      ((A.symm : F →L[𝕜] E (b x)).comp D) ↔ ContinuousLinearMap.IsFredholm D from
    h (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x)
  intro D
  constructor
  · intro h
    simpa only [← ContinuousLinearMap.comp_assoc, ContinuousLinearEquiv.coe_comp_coe_symm,
      ContinuousLinearMap.id_comp] using h.equiv_comp (F := E (b x)) (G := F) A
  · intro h
    exact h.equiv_comp (G := E (b x)) A.symm

/-- The Fredholm index of a section's coordinate derivative at a zero is independent of
the bundle trivialization. No Fredholm hypothesis is needed for this equality of indices. -/
theorem index_mvfderiv_section_coordChange_of_eq_zero
    (hb : ContinuousAt b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    LinearMap.index (mvfderiv IM (fun y ↦ (e' ⟨b y, s y⟩).2) x).toLinearMap =
      LinearMap.index (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x).toLinearMap := by
  rw [mvfderiv_section_coordChange_of_eq_zero hb he he' hs hzero,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    LinearMap.index_equiv_comp]

/-- Fredholmness of a section's coordinate derivative at a zero is independent of
the bundle trivialization. -/
theorem isFredholm_mvfderiv_section_coordChange_iff_of_eq_zero
    (hb : ContinuousAt b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    ContinuousLinearMap.IsFredholm (mvfderiv IM (fun y ↦ (e' ⟨b y, s y⟩).2) x) ↔
      ContinuousLinearMap.IsFredholm (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [mvfderiv_section_coordChange_of_eq_zero hb he he' hs hzero]
  let A := e.coordChangeL 𝕜 e' (b x)
  -- Read the derivative as an operator on the model space, which carries the norm.
  suffices h : ∀ D : EM →L[𝕜] F, ContinuousLinearMap.IsFredholm ((A : F →L[𝕜] F).comp D) ↔
      ContinuousLinearMap.IsFredholm D from
    h (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x)
  intro D
  refine ⟨fun h ↦ ?_, fun h ↦ h.equiv_comp A⟩
  simpa only [← ContinuousLinearMap.comp_assoc, ContinuousLinearEquiv.coe_symm_comp_coe,
    ContinuousLinearMap.id_comp] using h.equiv_comp A.symm

/-- Surjectivity of a section's coordinate derivative at a zero is independent of
the bundle trivialization, so regular zeros can be tested in any fiber coordinates. -/
theorem surjective_mvfderiv_section_coordChange_iff_of_eq_zero
    (hb : ContinuousAt b x)
    (he : b x ∈ e.baseSet) (he' : b x ∈ e'.baseSet)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F) (fun y ↦ (e ⟨b y, s y⟩).2) x) (hzero : s x = 0) :
    Function.Surjective (mvfderiv IM (fun y ↦ (e' ⟨b y, s y⟩).2) x) ↔
      Function.Surjective (mvfderiv IM (fun y ↦ (e ⟨b y, s y⟩).2) x) := by
  rw [mvfderiv_section_coordChange_of_eq_zero hb he he' hs hzero]
  exact Function.Surjective.of_comp_iff'
    (e.coordChangeL 𝕜 e' (b x)).bijective _

/-- In a trivial bundle, the linearization of a section along any map is just the
vector-valued manifold derivative of its fiber component. -/
@[simp]
theorem sectionLinearization_trivial (b : M → B) (f : M → F) (x : M) :
    sectionLinearization (F := F) (E := Bundle.Trivial B F) IM b f x = mvfderiv IM f x := by
  rw [sectionLinearization_def]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply,
    Bundle.Trivial.symmL_trivialization, ContinuousLinearMap.id_comp]

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  [TopologicalSpace HN] {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace N] [ChartedSpace HN N]

/-- Pulling a section back along a differentiable map precomposes its intrinsic linearization
with the differential of that map. This is the chain rule used to pass between a manifold source
and a source chart. -/
theorem sectionLinearization_comp {g : N → M} {y : N}
    (hg : MDifferentiableAt IN IM g y)
    (hs : MDifferentiableAt IM 𝓘(𝕜, F)
      (fun z ↦ (trivializationAt F E (b (g y)) ⟨b z, s z⟩).2) (g y)) :
    sectionLinearization (F := F) IN (b ∘ g) (fun z ↦ s (g z)) y =
      (sectionLinearization (F := F) IM b s (g y)).comp (mfderiv IN IM g y) := by
  rw [sectionLinearization_def, sectionLinearization_def]
  -- The dependent pullback does not syntactically expose the coordinate expression as a
  -- composition, so make that composition explicit before applying the manifold chain rule.
  change ((trivializationAt F E (b (g y))).symmL 𝕜 (b (g y))).comp
      (mvfderiv IN ((fun z ↦
        (trivializationAt F E (b (g y)) ⟨b z, s z⟩).2) ∘ g) y) = _
  rw [mvfderiv_comp y hs hg, ContinuousLinearMap.comp_assoc]

end TauCeti
