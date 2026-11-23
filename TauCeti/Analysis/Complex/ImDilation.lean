/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.Sets.Opens

/-!
# Dilating the normal coordinate of the upper half-plane

`TauCeti.imDilation c` is the real-linear map `x + y i ↦ x + c y i`. It fixes the real axis
pointwise and, for `c < 0`, exchanges the open upper and lower half-planes. This file records its
algebra, its determinant `c`, the resulting change of variables for integrals, integrability and
`Lᵖ` membership on preimages, and the chain rule for undoing it. These are the coordinate changes
behind higher-order reflection across the real axis, `TauCeti.planarReflection`.

It also records the elementary bound `|χ z| ≤ M z.im` on the upper half-plane for a function
vanishing on the real axis with derivative bounded by `M`, which controls boundary layers when
integrating by parts up to the axis.

The reflection core `TopologicalSpace.Opens.reflectionCore V` of an open set `V ⊆ ℂ` is the open
set of points of `V` in the open upper half-plane together with the points whose vertical segment
to the conjugate point lies in `V`. It lies between `V ∩ {0 ≤ im}` and `V`, is the largest open
subset of `V` with this segment property (`TopologicalSpace.Opens.le_reflectionCore_iff`), and is
stable under the dilations by factors in `[-1, 1]` below the real axis
(`TopologicalSpace.Opens.imDilation_mem_reflectionCore`).
-/

public section

noncomputable section

open MeasureTheory Set Complex TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-- The real-linear map `x + y i ↦ x + c y i`, which dilates the normal coordinate of the upper
half-plane by `c` and fixes the real axis pointwise. -/
def imDilation (c : ℝ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ⟨z.re, c * z.im⟩
      map_add' := fun z w => Complex.ext (by simp) (by simp [mul_add])
      map_smul' := fun a z => Complex.ext (by simp) (by simp; ring) }

@[simp]
theorem imDilation_apply_re (c : ℝ) (z : ℂ) : (imDilation c z).re = z.re := by
  simp [imDilation]

@[simp]
theorem imDilation_apply_im (c : ℝ) (z : ℂ) : (imDilation c z).im = c * z.im := by
  simp [imDilation]

/-- The dilation in coordinates. -/
theorem imDilation_apply (c : ℝ) (z : ℂ) : imDilation c z = ⟨z.re, c * z.im⟩ :=
  Complex.ext (imDilation_apply_re c z) (imDilation_apply_im c z)

/-- Dilations of the normal coordinate compose by multiplying the factors. -/
theorem imDilation_imDilation (c c' : ℝ) (z : ℂ) :
    imDilation c (imDilation c' z) = imDilation (c * c') z :=
  Complex.ext rfl (by simp [mul_assoc])

/-- The normal dilation depends continuously on the factor, in the operator norm: it is
`x + y i ↦ x + c y i = re + c • (im • I)`. -/
@[continuity, fun_prop]
theorem continuous_imDilation : Continuous imDilation := by
  have h : imDilation =
      fun c : ℝ => Complex.reCLM.smulRight (1 : ℂ) + c • Complex.imCLM.smulRight I := by
    funext c
    refine ContinuousLinearMap.ext fun z => Complex.ext ?_ ?_ <;> simp
  rw [h]
  fun_prop

/-- The dilation by one is the identity. -/
@[simp]
theorem imDilation_one_apply (z : ℂ) : imDilation 1 z = z :=
  Complex.ext rfl (by simp)

/-- Points of the real axis are fixed. -/
theorem imDilation_of_im_eq_zero (c : ℝ) {z : ℂ} (hz : z.im = 0) : imDilation c z = z :=
  Complex.ext rfl (by simp [hz])

@[simp]
theorem imDilation_apply_one (c : ℝ) : imDilation c 1 = 1 :=
  imDilation_of_im_eq_zero c (by simp)

@[simp]
theorem imDilation_apply_I (c : ℝ) : imDilation c I = c • I :=
  Complex.ext (by simp) (by simp)

/-- The determinant of the dilation is the dilation factor. -/
theorem det_imDilation (c : ℝ) : LinearMap.det (imDilation c : ℂ →ₗ[ℝ] ℂ) = c := by
  rw [← LinearMap.det_toMatrix basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

/-- A nonzero dilation of the normal coordinate as a continuous linear equivalence. -/
def imDilationEquiv {c : ℝ} (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.ofContinuousLinearMap (imDilation c) (imDilation c⁻¹)
    (ContinuousLinearMap.ext fun z => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, imDilation_imDilation,
        mul_inv_cancel₀ hc, imDilation_one_apply])
    (ContinuousLinearMap.ext fun z => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, imDilation_imDilation,
        inv_mul_cancel₀ hc, imDilation_one_apply])

@[simp]
theorem coe_imDilationEquiv {c : ℝ} (hc : c ≠ 0) : ⇑(imDilationEquiv hc) = imDilation c := by
  rfl

/-- The determinant of a nonzero dilation, seen as an equivalence. -/
theorem det_imDilationEquiv {c : ℝ} (hc : c ≠ 0) :
    LinearMap.det ((imDilationEquiv hc : ℂ ≃L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = c :=
  det_imDilation c

/-- Precomposing with a nonzero dilation preserves compact support. -/
theorem _root_.HasCompactSupport.comp_imDilation {α : Type*} [Zero α] {f : ℂ → α}
    (hf : HasCompactSupport f) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport fun z => f (imDilation c z) :=
  hf.comp_homeomorph (imDilationEquiv hc).toHomeomorph

/-- A nonzero dilation is a measurable embedding. -/
theorem measurableEmbedding_imDilation {c : ℝ} (hc : c ≠ 0) :
    MeasurableEmbedding (imDilation c) :=
  (imDilationEquiv hc).toHomeomorph.measurableEmbedding

/-- Lebesgue measure scales by the inverse Jacobian under a dilation of the normal coordinate. -/
theorem map_imDilation_volume {c : ℝ} (hc : c ≠ 0) :
    Measure.map (imDilation c) volume = ENNReal.ofReal |c⁻¹| • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := (imDilation c : ℂ →ₗ[ℝ] ℂ)) (by rwa [det_imDilation])
  rwa [det_imDilation] at h

/-- Dilating the normal coordinate by a factor of modulus at most one does not increase the
norm. -/
theorem norm_imDilation_le {c : ℝ} (hc : |c| ≤ 1) (w : ℂ) : ‖imDilation c w‖ ≤ ‖w‖ := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c]
  rw [Complex.norm_def, Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.normSq_apply, imDilation_apply_re, imDilation_apply_im]
  nlinarith [mul_self_nonneg w.im]

/-- A function vanishing on the real axis with derivative bounded by `M` is at most `M z.im` on
the upper half-plane. -/
theorem abs_le_mul_im_of_eq_zero_on_real {M : ℝ} {χ : ℂ → ℝ} (hχ : Differentiable ℝ χ)
    (hM : ∀ y, ‖fderiv ℝ χ y‖ ≤ M) (hχ0 : ∀ x : ℝ, χ x = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    |χ z| ≤ M * z.im := by
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ)
    (fun y _ => (hχ y)) (fun y _ => hM y) convex_univ (mem_univ (z.re : ℂ)) (mem_univ z)
  have hz' : z - (z.re : ℂ) = z.im * I := by
    apply Complex.ext <;> simp
  rwa [hχ0, sub_zero, hz', norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hz, Real.norm_eq_abs] at hmv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Change of variables for a dilation of the normal coordinate** on a preimage. -/
theorem setIntegral_comp_imDilation {c : ℝ} (hc : c ≠ 0) (f : ℂ → F) (s : Set ℂ) :
    ∫ z in imDilation c ⁻¹' s, f (imDilation c z) = |c|⁻¹ • ∫ w in s, f w := by
  have he := measurableEmbedding_imDilation hc
  rw [← he.integral_map, ← he.restrict_map, map_imDilation_volume hc, Measure.restrict_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

omit [NormedSpace ℝ F] in
/-- Integrability transfers along a dilation of the normal coordinate. -/
theorem integrableOn_comp_imDilation_iff {c : ℝ} (hc : c ≠ 0) {f : ℂ → F} {s : Set ℂ} :
    IntegrableOn (fun z => f (imDilation c z)) (imDilation c ⁻¹' s) ↔ IntegrableOn f s := by
  have he := measurableEmbedding_imDilation hc
  rw [IntegrableOn, IntegrableOn, ← Function.comp_def, ← he.integrable_map_iff, ← he.restrict_map,
    map_imDilation_volume hc, Measure.restrict_smul,
    integrable_smul_measure (by simpa using hc) ENNReal.ofReal_ne_top]

omit [NormedSpace ℝ F] in
/-- `Lᵖ` membership transfers along a dilation of the normal coordinate. -/
theorem memLp_comp_imDilation_iff {c : ℝ} (hc : c ≠ 0) {f : ℂ → F} {s : Set ℂ} {p : ℝ≥0∞} :
    MemLp (fun z => f (imDilation c z)) p (volume.restrict (imDilation c ⁻¹' s)) ↔
      MemLp f p (volume.restrict s) := by
  have he := measurableEmbedding_imDilation hc
  rw [← Function.comp_def, ← he.memLp_map_measure_iff, ← he.restrict_map,
    map_imDilation_volume hc, Measure.restrict_smul]
  have h0 : ENNReal.ofReal |c⁻¹| ≠ 0 := by simpa using hc
  refine ⟨fun h => ?_, fun h => h.smul_measure ENNReal.ofReal_ne_top⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 h0)
  rwa [smul_smul, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_smul] at h'

/-- The chain rule for undoing a dilation. -/
theorem fderiv_comp_imDilation_apply {φ : ℂ → ℝ} (hφ : Differentiable ℝ φ) (c : ℝ)
    (w v : ℂ) :
    fderiv ℝ (fun w => φ (imDilation c w)) w v = fderiv ℝ φ (imDilation c w) (imDilation c v) := by
  have h := (hφ (imDilation c w)).hasFDerivAt.comp w (imDilation c).hasFDerivAt
  rw [Function.comp_def] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply]

/-! ### Reflection cores -/

/-- The reflection core of an open set `V ⊆ ℂ`: the points of `V` in the open upper half-plane,
together with the points `z` of `V` whose vertical segment `{imDilation c z | -1 ≤ c ≤ 1}`, from `z`
to its conjugate, lies in `V`. It is open, lies between `V ∩ {0 ≤ im}` and `V`, and is stable under
the dilations by factors in `[-1, 1]` below the real axis
(`TopologicalSpace.Opens.imDilation_mem_reflectionCore`), in particular under the node dilations,
so the higher reflections extend local Sobolev maps from its closed upper half to the whole core. -/
def _root_.TopologicalSpace.Opens.reflectionCore (V : Opens ℂ) : Opens ℂ where
  carrier := (V : Set ℂ) ∩ {z | 0 < z.im} ∪ {z | ∀ c ∈ Icc (-1 : ℝ) 1, imDilation c z ∈ V}
  is_open' := by
    refine (V.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)).union
      (isOpen_iff_mem_nhds.2 fun z hz => ?_)
    have hc : Continuous fun q : ℂ × ℝ => imDilation q.2 q.1 := by fun_prop
    exact isCompact_Icc.eventually_forall_of_forall_eventually fun c hcI =>
      hc.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds (hz c hcI))

/-- The reflection core as a set. -/
theorem _root_.TopologicalSpace.Opens.coe_reflectionCore (V : Opens ℂ) :
    (V.reflectionCore : Set ℂ) =
      (V : Set ℂ) ∩ {z | 0 < z.im} ∪ {z | ∀ c ∈ Icc (-1 : ℝ) 1, imDilation c z ∈ V} :=
  (rfl)

/-- Membership in the reflection core. -/
@[simp]
theorem _root_.TopologicalSpace.Opens.mem_reflectionCore {V : Opens ℂ} {z : ℂ} :
    z ∈ V.reflectionCore ↔ (z ∈ V ∧ 0 < z.im) ∨ ∀ c ∈ Icc (-1 : ℝ) 1, imDilation c z ∈ V :=
  Iff.rfl

/-- The reflection core of `V` lies in `V`. -/
theorem _root_.TopologicalSpace.Opens.reflectionCore_le (V : Opens ℂ) : V.reflectionCore ≤ V := by
  intro z hz
  rcases Opens.mem_reflectionCore.1 hz with hz | hz
  · exact hz.1
  · simpa using hz 1 ⟨by norm_num, le_rfl⟩

/-- The reflection core is monotone. -/
theorem _root_.TopologicalSpace.Opens.reflectionCore_mono {V W : Opens ℂ} (h : V ≤ W) :
    V.reflectionCore ≤ W.reflectionCore := fun _ hz =>
  Opens.mem_reflectionCore.2 <| (Opens.mem_reflectionCore.1 hz).imp
    (fun hz => ⟨h hz.1, hz.2⟩) fun hz c hc => h (hz c hc)

/-- The reflection core of `V` contains `V ∩ {0 ≤ im}`: points on the real axis are fixed by the
normal dilations. -/
theorem _root_.TopologicalSpace.Opens.inter_setOf_im_nonneg_subset_reflectionCore (V : Opens ℂ) :
    (V : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V.reflectionCore := by
  rintro z ⟨hzV, hz⟩
  rw [mem_ofPred_eq] at hz
  rw [SetLike.mem_coe, Opens.mem_reflectionCore]
  rcases hz.lt_or_eq with hpos | hzero
  · exact Or.inl ⟨hzV, hpos⟩
  · exact Or.inr fun c _ => by rwa [imDilation_of_im_eq_zero c hzero.symm]

/-- The vertical segment from a point of the reflection core on or below the real axis to its
conjugate lies in the original set. -/
theorem _root_.TopologicalSpace.Opens.imDilation_mem_of_mem_reflectionCore {V : Opens ℂ} {z : ℂ}
    (hz : z ∈ V.reflectionCore) (him : z.im ≤ 0) {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    imDilation c z ∈ V :=
  (Opens.mem_reflectionCore.1 hz).resolve_left (fun h => not_lt.2 him h.2) c hc

/-- **Characterisation of the reflection core.** An open set `W` lies in the reflection core of `V`
exactly when it lies in `V` and the vertical segment from each of its points on or below the real
axis to the conjugate point lies in `V`. So the reflection core is the largest open subset of `V`
with this property. -/
theorem _root_.TopologicalSpace.Opens.le_reflectionCore_iff {V W : Opens ℂ} :
    W ≤ V.reflectionCore ↔
      W ≤ V ∧ ∀ z ∈ W, z.im ≤ 0 → ∀ c ∈ Icc (-1 : ℝ) 1, imDilation c z ∈ V := by
  refine ⟨fun h => ⟨h.trans V.reflectionCore_le, fun _ hz him _ hc =>
    Opens.imDilation_mem_of_mem_reflectionCore (h hz) him hc⟩, fun ⟨hWV, h⟩ z hz => ?_⟩
  rcases lt_or_ge 0 z.im with him | him
  · exact Opens.mem_reflectionCore.2 (Or.inl ⟨hWV hz, him⟩)
  · exact Opens.mem_reflectionCore.2 (Or.inr (h z hz him))

/-- The reflection core is stable under the dilations by factors in `[-1, 1]` below the real
axis. -/
theorem _root_.TopologicalSpace.Opens.imDilation_mem_reflectionCore {V : Opens ℂ} {c : ℝ}
    (hc : c ∈ Icc (-1 : ℝ) 1) {z : ℂ} (hz : z ∈ V.reflectionCore) (him : z.im ≤ 0) :
    imDilation c z ∈ V.reflectionCore := by
  refine Opens.mem_reflectionCore.2 (Or.inr fun c' hc' => ?_)
  have hcc : |c' * c| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_le.2 hc') (abs_le.2 hc) (abs_nonneg _) zero_le_one).trans
      (one_mul 1).le
  rw [imDilation_imDilation]
  exact Opens.imDilation_mem_of_mem_reflectionCore hz him (abs_le.1 hcc)

/-- Taking the reflection core is idempotent. -/
@[simp]
theorem _root_.TopologicalSpace.Opens.reflectionCore_reflectionCore (V : Opens ℂ) :
    V.reflectionCore.reflectionCore = V.reflectionCore := by
  refine le_antisymm V.reflectionCore.reflectionCore_le fun z hz => ?_
  rcases lt_or_ge 0 z.im with h | h
  · exact Opens.mem_reflectionCore.2 (Or.inl ⟨hz, h⟩)
  · exact Opens.mem_reflectionCore.2
      (Or.inr fun c hc => Opens.imDilation_mem_reflectionCore hc hz h)

/-- The reflection core of `V` has the same upper half as `V`. -/
@[simp]
theorem _root_.TopologicalSpace.Opens.upperHalf_reflectionCore (V : Opens ℂ) :
    V.reflectionCore.upperHalf = V.upperHalf := by
  refine le_antisymm (Opens.upperHalf_mono V.reflectionCore_le) fun z hz => ?_
  obtain ⟨hzV, h⟩ := Opens.mem_upperHalf.1 hz
  exact Opens.mem_upperHalf.2 ⟨Opens.mem_reflectionCore.2 (Or.inl ⟨hzV, h⟩), h⟩

/-- The reflection core of `V` meets the closed upper half-plane in `V ∩ {0 ≤ im}`. -/
@[simp]
theorem _root_.TopologicalSpace.Opens.coe_reflectionCore_inter_setOf_im_nonneg (V : Opens ℂ) :
    (V.reflectionCore : Set ℂ) ∩ {z | 0 ≤ z.im} = (V : Set ℂ) ∩ {z | 0 ≤ z.im} :=
  (inter_subset_inter_left _ V.reflectionCore_le).antisymm
    (subset_inter V.inter_setOf_im_nonneg_subset_reflectionCore inter_subset_right)

/-- A compact subset `K` of the reflection core of `Ω` lies in the reflection core of an open
subset `V` of `Ω` whose closure is compact and contained in `Ω`. -/
theorem _root_.TopologicalSpace.Opens.exists_subset_reflectionCore_and_isCompact_closure
    {Ω : Opens ℂ} {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω.reflectionCore) :
    ∃ V : Opens ℂ, IsCompact (closure (V : Set ℂ)) ∧ closure (V : Set ℂ) ⊆ Ω ∧
      K ⊆ V.reflectionCore := by
  have hK' : IsCompact (K ∪ (fun q : ℝ × ℂ => imDilation q.1 q.2) ''
      (Icc (-1 : ℝ) 1 ×ˢ (K ∩ {z | z.im ≤ 0}))) :=
    hK.union ((isCompact_Icc.prod (hK.inter_right
      (isClosed_le Complex.continuous_im continuous_const))).image (by fun_prop))
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK' (by
    rintro _ (hz | ⟨⟨c, z⟩, ⟨hc, hzK, hz⟩, rfl⟩)
    · exact Ω.reflectionCore_le (hKΩ hz)
    · exact Opens.imDilation_mem_of_mem_reflectionCore (hKΩ hzK) hz hc)
  refine ⟨V, hVc, hVΩ, fun z hz => Opens.mem_reflectionCore.2 ?_⟩
  rcases lt_or_ge 0 z.im with h | h
  · exact Or.inl ⟨hKV (Or.inl hz), h⟩
  · exact Or.inr fun c hc => hKV (Or.inr ⟨(c, z), ⟨hc, hz, h⟩, rfl⟩)

/-- The closure of the upper half of an open set whose closure lies in `Ω` lies in the reflection
core of `Ω`. -/
theorem _root_.TopologicalSpace.Opens.closure_upperHalf_subset_reflectionCore {Ω W : Opens ℂ}
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) : closure (W.upperHalf : Set ℂ) ⊆ Ω.reflectionCore := by
  rw [Opens.coe_upperHalf]
  refine (closure_minimal (t := closure (W : Set ℂ) ∩ {z | 0 ≤ z.im})
    (inter_subset_inter subset_closure (ofPred_subset_ofPred.2 fun _ => le_of_lt))
    (isClosed_closure.inter (isClosed_le continuous_const Complex.continuous_im))).trans ?_
  exact (inter_subset_inter_left _ hWΩ).trans (Ω.inter_setOf_im_nonneg_subset_reflectionCore)

end TauCeti
