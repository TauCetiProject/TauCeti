/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Complexification
public import TauCeti.Topology.VectorBundle.Complexification
public import Mathlib.Topology.VectorBundle.Hom

/-!
# Complexification of real Hom into a line bundle

For a real vector bundle `V` and a real line bundle `L`, complexification of the real Hom bundle
is complex-linearly equivalent, on each original fibre, to complex Hom between the complexified
bundles. `bundleHomComplexificationEquiv` sends `(z ⊗ T)(w ⊗ v)` to `(z*w) ⊗ T(v)`.
Its inverse reads real and imaginary parts on the real inclusion. The comparison commutes with
conjugation and real changes of fibres, and its native bundle frames satisfy the stated
commuting square. The coefficient model may be infinite-dimensional or incomplete.
-/

public section
noncomputable section
open Bundle FiberBundle Set TauCeti
open scoped TensorProduct TauCeti.Complexification
namespace TauCeti

variable {W D F : Type*}
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [TopologicalSpace (ℂ ⊗[ℝ] D)] [IsComplexificationTopology D]

/-- A real fibre frame extended to the existing complexification model. -/
private def frameComplex (e : W ≃L[ℝ] F) : (ℂ ⊗[ℝ] W) ≃L[ℂ] Complexification F :=
  e.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification F)

@[simp] private theorem frameComplex_tmul (e : W ≃L[ℝ] F) (z : ℂ) (v : W) :
    frameComplex e (z ⊗ₜ[ℝ] v) = ⟨z.re • e v, z.im • e v⟩ := by
  ext <;> simp [frameComplex]

variable [IsTopologicalAddGroup D] [ContinuousSMul ℝ D]
  [TopologicalSpace (ℂ ⊗[ℝ] (W →L[ℝ] D))]
  [IsComplexificationTopology (W →L[ℝ] D)]

/-- Complexifying real continuous Hom into a real line agrees with complex Hom between
the complexified original spaces. The equivalence is independent of the real frames `e`, `d`. -/
private def homComplexificationEquiv (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ) :
    (ℂ ⊗[ℝ] (W →L[ℝ] D)) ≃L[ℂ]
      ((ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) :=
  ((frameComplex (e.arrowCongr d)).trans (Complexification.strongDualLineEquiv F)).trans
    ((frameComplex e).symm.arrowCongr (frameComplex d).symm)

/-- Evaluation is independent of the chosen frames and preserves the actual tensor fibres. -/
private theorem homComplexificationEquiv_tmul (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (z w : ℂ) (T : W →L[ℝ] D) (v : W) :
    homComplexificationEquiv e d (z ⊗ₜ[ℝ] T) (w ⊗ₜ[ℝ] v) = (z*w) ⊗ₜ[ℝ] T v := by
  apply (frameComplex d).injective
  simp only [homComplexificationEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.apply_symm_apply, frameComplex_tmul]
  apply Complexification.ext <;>
    simp [Complex.mul_re, Complex.mul_im, ContinuousLinearEquiv.arrowCongr_apply,
      mul_assoc, add_mul, sub_mul] <;> ring

/-- Coordinate formula for the frame extension. -/
@[simp] private theorem frameComplex_re (e : W ≃L[ℝ] F) (u : ℂ ⊗[ℝ] W) :
    (frameComplex e u).re = e (realPart W u) := by simp [frameComplex]
/-- Imaginary coordinate formula for the frame extension. -/
@[simp] private theorem frameComplex_im (e : W ≃L[ℝ] F) (u : ℂ ⊗[ℝ] W) :
    (frameComplex e u).im = e (imaginaryPart W u) := by simp [frameComplex]

/-- The intrinsic coefficient comparison commutes with real frames and their scalar extensions. -/
private theorem homComplexificationEquiv_in_frames (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) :
    (e.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification F)).arrowCongr
      (d.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification ℝ))
        (homComplexificationEquiv e d u) =
      Complexification.strongDualLineEquiv F
        (((e.arrowCongr d).baseChangeComplex.trans
          (tensorContinuousLinearEquivComplexification (F →L[ℝ] ℝ))) u) := by
  ext v <;> simp [homComplexificationEquiv, frameComplex, sub_eq_add_neg]

/-- Pure real coefficients extend by the existing native scalar extension. -/
private theorem homComplexificationEquiv_tmul_map (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (z : ℂ) (T : W →L[ℝ] D) :
    homComplexificationEquiv e d (z ⊗ₜ[ℝ] T) = z • T.baseChangeComplex := by
  ext v
  induction v with
  | tmul w v => simp [homComplexificationEquiv_tmul, TensorProduct.smul_tmul']
  | add u v hu hv => simp [hu, hv]

/-- The comparison on arbitrary coefficients is the real extension plus i times the
imaginary extension. -/
private theorem homComplexificationEquiv_apply (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) :
    homComplexificationEquiv e d u = (realPart _ u).baseChangeComplex +
      Complex.I • (imaginaryPart _ u).baseChangeComplex := by
  conv_lhs => rw [← one_tmul_realPart_add_I_tmul_imaginaryPart _ u]
  simp only [map_add, homComplexificationEquiv_tmul_map, one_smul]

/-- Changing the real frames does not change the original-fibre map. -/
private theorem homComplexificationEquiv_independent (e e' : W ≃L[ℝ] F) (d d' : D ≃L[ℝ] ℝ) :
    homComplexificationEquiv e d = homComplexificationEquiv e' d' := by
  ext u
  rw [homComplexificationEquiv_apply, homComplexificationEquiv_apply]

/-- Real coordinate of the actual inverse: restriction followed by the native real projection. -/
private theorem homComplexificationEquiv_symm_re (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (A : (ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) :
    realPart _ ((homComplexificationEquiv e d).symm A) =
      (realPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) := by
  ext v
  have h := congrArg (fun B ↦ realPart D (B (1 ⊗ₜ[ℝ] v)))
    ((homComplexificationEquiv e d).apply_symm_apply A)
  change realPart D (homComplexificationEquiv e d ((homComplexificationEquiv e d).symm A) (1
    ⊗ₜ[ℝ] v)) = _ at h
  rw [homComplexificationEquiv_apply] at h
  simpa using h

/-- Imaginary coordinate of the actual inverse. -/
private theorem homComplexificationEquiv_symm_im (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (A : (ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) :
    imaginaryPart _ ((homComplexificationEquiv e d).symm A) =
      (imaginaryPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) := by
  ext v
  have h := congrArg (fun B ↦ imaginaryPart D (B (1 ⊗ₜ[ℝ] v)))
    ((homComplexificationEquiv e d).apply_symm_apply A)
  change imaginaryPart D (homComplexificationEquiv e d ((homComplexificationEquiv e d).symm A)
    (1 ⊗ₜ[ℝ] v)) = _ at h
  rw [homComplexificationEquiv_apply] at h
  simpa using h

/-- The intrinsic inverse on the original tensor fibre. -/
private theorem homComplexificationEquiv_symm_apply (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (A : (ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) :
    (homComplexificationEquiv e d).symm A =
      1 ⊗ₜ[ℝ] (realPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) +
      Complex.I ⊗ₜ[ℝ]
        (imaginaryPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) := by
  rw [← homComplexificationEquiv_symm_re e d A, ← homComplexificationEquiv_symm_im e d A]
  exact (one_tmul_realPart_add_I_tmul_imaginaryPart _ _).symm

/-- Complex conjugation intertwines the two intrinsic coefficient actions. -/
private theorem homComplexificationEquiv_conj (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] ℝ)
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) (v : ℂ ⊗[ℝ] W) :
    homComplexificationEquiv e d (tmulConj _ u) (tmulConj _ v) = tmulConj _
      (homComplexificationEquiv e d u v) := by
  induction u with
  | tmul z T =>
    induction v with
    | tmul w v => simp [homComplexificationEquiv_tmul]
    | add v w hv hw => simp only [map_add, hv, hw]
  | add u w hu hw => simp only [map_add, add_apply, hu, hw]

section Topological
variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V L : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℝ L)] [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]

local instance instIsTopologicalAddGroupLineBundleFiber (x : B) : IsTopologicalAddGroup (L x) :=
  VectorBundle.isTopologicalAddGroup ℝ ℝ L x
local instance instContinuousSMulLineBundleFiber (x : B) : ContinuousSMul ℝ (L x) :=
  VectorBundle.continuousSMul ℝ ℝ L x

variable [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]

variable (F) in
/-- The intrinsic complexification comparison on the original native Hom fibre. -/
def bundleHomComplexificationEquiv (x : B) : (ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ≃L[ℂ]
    ((ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  homComplexificationEquiv ((trivializationAt F V x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x))
    ((trivializationAt ℝ L x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt ℝ L x))

/-- Characteristic pure-tensor evaluation on original native fibres. -/
@[simp] theorem bundleHomComplexificationEquiv_tmul_apply_tmul (x : B) (z w : ℂ)
    (T : V x →L[ℝ] L x) (v : V x) :
    bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x (z ⊗ₜ[ℝ] T) (w ⊗ₜ[ℝ] v) =
      (z*w) ⊗ₜ[ℝ] T v := by
  exact homComplexificationEquiv_tmul _ _ z w T v

/-- Real or imaginary pure coefficients give the native complex extension. -/
theorem bundleHomComplexificationEquiv_tmul (x : B) (z : ℂ) (T : V x →L[ℝ] L x) :
    bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x (z ⊗ₜ[ℝ] T) =
      z • T.baseChangeComplex := by
  exact homComplexificationEquiv_tmul_map _ _ z T

/-- Actual inverse on the native original coefficient fibre. -/
theorem bundleHomComplexificationEquiv_symm_apply (x : B)
    (A : (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :
    (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x).symm A =
      1 ⊗ₜ[ℝ] (realPartCLM (L x)).comp
        ((A.restrictScalars ℝ).comp (oneTmulCLM (V x))) +
      Complex.I ⊗ₜ[ℝ] (imaginaryPartCLM (L x)).comp
        ((A.restrictScalars ℝ).comp (oneTmulCLM (V x))) := by
  exact homComplexificationEquiv_symm_apply _ _ A

/-- The coefficient comparison is the extension of its real part plus i times the extension
of its imaginary part. -/
theorem bundleHomComplexificationEquiv_apply (x : B)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    bundleHomComplexificationEquiv F (V := V) (L := L) x u =
      (realPart _ u).baseChangeComplex + Complex.I • (imaginaryPart _ u).baseChangeComplex := by
  exact homComplexificationEquiv_apply _ _ u

/-- Real restriction of the native inverse. -/
theorem bundleHomComplexificationEquiv_symm_realPart (x : B)
    (A : (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :
    realPart _ ((bundleHomComplexificationEquiv F (V := V) (L := L) x).symm A) =
      (realPartCLM (L x)).comp ((A.restrictScalars ℝ).comp (oneTmulCLM (V x))) := by
  exact homComplexificationEquiv_symm_re _ _ A

/-- Imaginary restriction of the native inverse. -/
theorem bundleHomComplexificationEquiv_symm_imaginaryPart (x : B)
    (A : (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :
    imaginaryPart _ ((bundleHomComplexificationEquiv F (V := V) (L := L) x).symm A) =
      (imaginaryPartCLM (L x)).comp ((A.restrictScalars ℝ).comp (oneTmulCLM (V x))) := by
  exact homComplexificationEquiv_symm_im _ _ A

/-- Native coefficient conjugation agrees with conjugating both tensor arguments. -/
theorem bundleHomComplexificationEquiv_conj (x : B) (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x))
    (v : ℂ ⊗[ℝ] V x) :
    bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x (tmulConj _ u) (tmulConj _ v) =
      tmulConj _ (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x u v) := by
  exact homComplexificationEquiv_conj _ _ u v

/-- Naturality under actual real-linear changes of original native fibres. -/
theorem bundleHomComplexificationEquiv_naturality (x y : B) (U : V x ≃L[ℝ] V y) (S : L x ≃L[ℝ] L y)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) (v : ℂ ⊗[ℝ] V x) :
    bundleHomComplexificationEquiv (F := F) (V := V) (L := L) y ((U.arrowCongr
      S).baseChangeComplex u)
      (U.baseChangeComplex v) =
      S.baseChangeComplex (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x u v) := by
  induction u with
  | tmul z T =>
    induction v with
    | tmul w v => simp
    | add v w hv hw => simp only [map_add, hv, hw]
  | add u w hu hw => simp only [map_add, add_apply, hu, hw]

/-- Any native real frames give the same original-fibre comparison. -/
private theorem bundleHomComplexificationEquiv_eq (x : B) (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (d : Trivialization ℝ (π ℝ L))
    [MemTrivializationAtlas d] (hx : x ∈ e.baseSet ∩ d.baseSet) :
    bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x = homComplexificationEquiv
      (e.continuousLinearEquivAt ℝ x hx.1) (d.continuousLinearEquivAt ℝ x hx.2) :=
  homComplexificationEquiv_independent _ _ _ _

/-- The intrinsic native comparison commutes with every pair of real fibre frames. -/
theorem bundleHomComplexificationEquiv_in_frames (x : B)
    (e : V x ≃L[ℝ] F) (d : L x ≃L[ℝ] ℝ)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    (e.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification F)).arrowCongr
      (d.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification ℝ))
        (bundleHomComplexificationEquiv F (V := V) (L := L) x u) =
      Complexification.strongDualLineEquiv F
        (((e.arrowCongr d).baseChangeComplex.trans
          (tensorContinuousLinearEquivComplexification (F →L[ℝ] ℝ))) u) := by
  rw [bundleHomComplexificationEquiv]
  rw [homComplexificationEquiv_independent _ e _ d]
  exact homComplexificationEquiv_in_frames e d u

omit [∀ x, IsComplexificationTopology (V x)]
  [∀ x, IsComplexificationTopology (L x)]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))] in
/-- The native real-Hom frame is the induced arrow equivalence on original fibres. -/
private theorem homFrame_native_real (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (d : Trivialization ℝ (π ℝ L))
    [MemTrivializationAtlas d] {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet) :
    (e.continuousLinearMap (RingHom.id ℝ) d).continuousLinearEquivAt ℝ x (by simpa using hx) =
      (e.continuousLinearEquivAt ℝ x hx.1).arrowCongr
        (d.continuousLinearEquivAt ℝ x hx.2) := by
  ext T v
  simp only [Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  rw [e.symmL_apply hx.1, Trivialization.continuousLinearEquivAt_symm_apply]
  simp [Trivialization.continuousLinearMapAt_apply_of_mem ℝ d hx.2]

omit [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))] in
/-- The complex-Hom frame of the original fibres agrees with complexified real frames. -/
private theorem homFrame_native_complex (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (d : Trivialization ℝ (π ℝ L))
    [MemTrivializationAtlas d] {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet) :
    (e.complexification.continuousLinearMap (RingHom.id ℂ)
      d.complexification).continuousLinearEquivAt ℂ x (by simpa using hx) =
      ((e.continuousLinearEquivAt ℝ x hx.1).baseChangeComplex.trans
        (tensorContinuousLinearEquivComplexification F)).arrowCongr
        ((d.continuousLinearEquivAt ℝ x hx.2).baseChangeComplex.trans
          (tensorContinuousLinearEquivComplexification ℝ)) := by
  rw [← e.continuousLinearEquivAt_complexification hx.1,
    ← d.continuousLinearEquivAt_complexification hx.2]
  apply DFunLike.ext
  intro T
  apply DFunLike.ext
  intro v
  simp only [Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  rw [e.complexification.symmL_apply (by simpa using hx.1),
    Trivialization.continuousLinearEquivAt_symm_apply]
  simp [Trivialization.continuousLinearMapAt_apply_of_mem ℂ d.complexification
    (by simpa using hx.2)]

/-- Exact commuting square for the native frames, with no compatibility hypothesis. -/
theorem bundleHomComplexificationEquiv_in_trivializations (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (d : Trivialization ℝ (π ℝ L))
    [MemTrivializationAtlas d] {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    (e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification
      ⟨x, bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x u⟩).2 =
      Complexification.strongDualLineEquiv F ((e.continuousLinearMap (RingHom.id ℝ)
        d).complexification
        ⟨x, u⟩).2 := by
  have h := bundleHomComplexificationEquiv_in_frames x
    (e.continuousLinearEquivAt ℝ x hx.1) (d.continuousLinearEquivAt ℝ x hx.2) u
  rw [← homFrame_native_complex e d hx] at h
  rw [← homFrame_native_real e d hx,
    ← (e.continuousLinearMap (RingHom.id ℝ) d).continuousLinearEquivAt_complexification
      (by simpa using hx)] at h
  simpa only [Trivialization.continuousLinearEquivAt_apply] using h

/-- The preferred native chart square. -/
theorem bundleHomComplexificationEquiv_in_trivializationAt (a x : B)
    (hx : x ∈ (trivializationAt F V a).baseSet ∩ (trivializationAt ℝ L a).baseSet)
    (u : ℂ ⊗[ℝ] (V x →L[ℝ] L x)) :
    (trivializationAt (Complexification F →L[ℂ] Complexification ℝ)
      (fun y ↦ (ℂ ⊗[ℝ] V y) →L[ℂ] (ℂ ⊗[ℝ] L y)) a
      ⟨x, bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x u⟩).2 =
    Complexification.strongDualLineEquiv F ((trivializationAt (Complexification (F →L[ℝ] ℝ))
      (fun y ↦ ℂ ⊗[ℝ] (V y →L[ℝ] L y)) a) ⟨x, u⟩).2 := by
  simpa only [hom_trivializationAt, trivializationAt_complexification] using
    bundleHomComplexificationEquiv_in_trivializations (trivializationAt F V a) (trivializationAt
      ℝ L a) hx u

/-- The inverse chart square follows from the actual inverse law. -/
theorem bundleHomComplexificationEquiv_symm_in_trivializationAt (a x : B)
    (hx : x ∈ (trivializationAt F V a).baseSet ∩ (trivializationAt ℝ L a).baseSet)
    (A : (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :
    ((trivializationAt (Complexification (F →L[ℝ] ℝ))
      (fun y ↦ ℂ ⊗[ℝ] (V y →L[ℝ] L y)) a)
        ⟨x, (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x).symm A⟩).2 =
    (Complexification.strongDualLineEquiv F).symm ((trivializationAt (Complexification F →L[ℂ]
      Complexification ℝ)
      (fun y ↦ (ℂ ⊗[ℝ] V y) →L[ℂ] (ℂ ⊗[ℝ] L y)) a) ⟨x, A⟩).2 := by
  have h := bundleHomComplexificationEquiv_in_trivializationAt a x hx
    ((bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x).symm A)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (Complexification.strongDualLineEquiv F).eq_symm_apply.mpr h.symm

/-- The same original atlas, restricted from complex to real scalars. -/
instance instVectorBundleRealComplexificationHom :
    VectorBundle ℝ (Complexification F →L[ℂ] Complexification ℝ)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) :=
  VectorBundle.restrictScalars ℝ ℂ _ _

omit [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))] in
/-- Atlas frames of complex Hom between complexifications come from real bundle frames. -/
theorem mem_trivializationAtlas_complexificationHom_iff
    {t : Trivialization (Complexification F →L[ℂ] Complexification ℝ)
      (π (Complexification F →L[ℂ] Complexification ℝ)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)))} :
    MemTrivializationAtlas t ↔
      ∃ (e : Trivialization F (π F V)) (d : Trivialization ℝ (π ℝ L))
        (he : MemTrivializationAtlas e) (hd : MemTrivializationAtlas d),
        t = e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification := by
  constructor
  · rintro ⟨⟨_, ⟨e, d, he, hd, rfl⟩, rfl⟩⟩
    obtain ⟨e0, he0, rfl⟩ := mem_trivializationAtlas_complexification_iff.mp he
    obtain ⟨d0, hd0, rfl⟩ := mem_trivializationAtlas_complexification_iff.mp hd
    exact ⟨e0, d0, he0, hd0, rfl⟩
  · rintro ⟨e, d, he, hd, rfl⟩
    infer_instance

/-- Transition functions in the existing complex-Hom atlas are conjugate to those of
complexified real Hom, by the fixed native model equivalence. -/
theorem complexificationHom_coordChange (e e' : Trivialization F (π F V))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (d d' : Trivialization ℝ (π ℝ L))
    [MemTrivializationAtlas d] [MemTrivializationAtlas d'] {x : B}
    (hx : x ∈ (e.baseSet ∩ d.baseSet) ∩ (e'.baseSet ∩ d'.baseSet)) :
    ((e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification).coordChangeL ℝ
      (e'.complexification.continuousLinearMap (RingHom.id ℂ) d'.complexification) x :
        (Complexification F →L[ℂ] Complexification ℝ) →L[ℝ]
          (Complexification F →L[ℂ] Complexification ℝ)) =
    ((Complexification.strongDualLineEquiv F).toContinuousLinearMap.restrictScalars ℝ).comp
      (((e.continuousLinearMap (RingHom.id ℝ) d).complexification.coordChangeL ℝ
        (e'.continuousLinearMap (RingHom.id ℝ) d').complexification x :
          Complexification (F →L[ℝ] ℝ) →L[ℝ] Complexification (F →L[ℝ] ℝ)).comp
        ((Complexification.strongDualLineEquiv F).symm.toContinuousLinearMap.restrictScalars ℝ))
          := by
  let t := e.complexification.continuousLinearMap (RingHom.id ℂ) d.complexification
  let t' := e'.complexification.continuousLinearMap (RingHom.id ℂ) d'.complexification
  let s := (e.continuousLinearMap (RingHom.id ℝ) d).complexification
  let s' := (e'.continuousLinearMap (RingHom.id ℝ) d').complexification
  have hxt : x ∈ t.baseSet ∩ t'.baseSet := by simpa [t, t'] using hx
  have hxs : x ∈ s.baseSet ∩ s'.baseSet := by simpa [s, s'] using hx
  apply DFunLike.ext
  intro f
  let u := (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x).symm (t.symm x f)
  have h0 := bundleHomComplexificationEquiv_in_trivializations e d hx.1 u
  have h1 := bundleHomComplexificationEquiv_in_trivializations e' d' hx.2 u
  have htu : bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x u = t.symm x f :=
    (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) x).apply_symm_apply _
  rw [htu] at h0 h1
  have hs : (s ⟨x, u⟩).2 = (Complexification.strongDualLineEquiv F).symm f := by
    apply (Complexification.strongDualLineEquiv F).injective
    rw [← h0]
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      congrArg Prod.snd (t.apply_mk_symm hxt.1 f)
  have hu : u = s.symm x ((Complexification.strongDualLineEquiv F).symm f) := by
    rw [← hs]
    exact (s.symm_apply_apply_mk hxs.1 u).symm
  change t.coordChangeL ℝ t' x f = _
  rw [t.coordChangeL_apply t' hxt]
  rw [h1, hu]
  change Complexification.strongDualLineEquiv F (s' ⟨x, s.symm x
    ((Complexification.strongDualLineEquiv
    F).symm f)⟩).2 = _
  rw [← s.coordChangeL_apply (R := ℝ) s' hxs]
  rfl

end Topological
end TauCeti
