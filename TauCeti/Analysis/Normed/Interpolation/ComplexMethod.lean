/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple

/-!
# The complex interpolation method

For a compatible couple `(X₀, X₁)` of complex normed spaces, Calderón's complex method produces
the interpolation spaces `[X₀, X₁]_θ`, `0 ≤ θ ≤ 1`, as follows. Let `S` be the closed strip
`0 ≤ re z ≤ 1`. The *Calderón space* `𝓕(X₀, X₁)` consists of the bounded continuous functions
`F : S → X₀ + X₁`, holomorphic in the interior of `S`, whose boundary functions `t ↦ F (j + i t)`
are continuous functions `ℝ → X_j` tending to zero at infinity, for `j = 0, 1`. Its norm is
`‖F‖ = max_j sup_t ‖F (j + i t)‖_{X_j}`. The space `[X₀, X₁]_θ` is the quotient of `𝓕(X₀, X₁)` by
the kernel of evaluation at `θ`, with the quotient norm; evaluation at `θ` embeds it injectively
into the sum space.

We realise `𝓕(X₀, X₁)` as the submodule `CompatibleCouple.calderonSpace` of the product of the
bounded continuous functions on the strip with the two spaces `C₀(ℝ, X_j)` of boundary values.
The boundary values are determined by the function on the strip (`calderonSpace_ext`). By the
Hadamard three-lines theorem the sup norm of `F` on the strip is at most the norm of its boundary
values (`norm_apply_le_of_mem_calderonSpace`), so the product norm on this submodule is exactly
the norm `max_j sup_t ‖F (j + i t)‖_{X_j}` (`norm_calderonSpace`).

## Main declarations

* `TauCeti.projVerticalClosedStrip`: the retraction of `ℂ` onto the closed strip `0 ≤ re z ≤ 1`,
  clamping the real part. It extends a function on the strip continuously to `ℂ`.
* `CompatibleCouple.calderonSpace`: the Calderón space, and `CompatibleCouple.calderonMk`, its
  element given by a function on `ℂ` that is bounded on the strip, holomorphic inside and
  continuous up to the boundary, with prescribed boundary values.
* `CompatibleCouple.norm_calderonSpace`: the norm is the larger of the sup norms of the boundary
  values.
* `CompatibleCouple.isClosed_calderonSpace`: for Banach spaces `X₀`, `X₁` the Calderón space is
  closed, hence a Banach space.
* `CompatibleCouple.ComplexMethodSpace θ`: the complex interpolation space `[X₀, X₁]_θ`, a Banach
  space when `X₀` and `X₁` are, with the injective inclusion `ComplexMethodSpace.toSum` of norm at
  most `1` into the sum space.
* `ComplexMethodSpace.ofInter`: the inclusion of the intersection, of norm at most `1`.
* `ComplexMethodSpace.map`: a linear map `T` of sum spaces restricting to continuous linear maps
  `T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁` induces a continuous linear map of the complex
  interpolation spaces, and if `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖` with `M₀`, `M₁` positive,
  then for `0 ≤ θ ≤ 1` it multiplies norms by at most `M₀ ^ (1 - θ) * M₁ ^ θ`
  (`ComplexMethodSpace.norm_map_le`). It respects identities and composition. Thus the complex
  method is an exact interpolation functor of exponent `θ`.
* `ComplexMethodSpace.norm_refl`: for the couple `(X, X)`, the complex method gives back the norm
  of `X`.

Evaluation at a real `θ` uses `projVerticalClosedStrip θ`, so `[X₀, X₁]_θ` for `θ < 0` (resp.
`θ > 1`) is the space `[X₀, X₁]_0` (resp. `[X₀, X₁]_1`); the interesting range is `0 < θ < 1`.

## References

* A. P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.1 (Lemma 4.1.1 and Theorem 4.1.2).
-/

public noncomputable section

open Set Filter Topology Complex
open scoped BoundedContinuousFunction ZeroAtInfty
open Complex.HadamardThreeLines (verticalStrip verticalClosedStrip)

namespace TauCeti

/-! ### The retraction onto the strip -/

/-- The retraction of `ℂ` onto the closed strip `0 ≤ re z ≤ 1` that clamps the real part to
`[0, 1]` and keeps the imaginary part. -/
def projVerticalClosedStrip (z : ℂ) : verticalClosedStrip 0 1 :=
  ⟨⟨projIcc 0 1 zero_le_one z.re, z.im⟩, (projIcc 0 1 zero_le_one z.re).2⟩

theorem coe_projVerticalClosedStrip (z : ℂ) :
    (projVerticalClosedStrip z : ℂ) = ⟨projIcc 0 1 zero_le_one z.re, z.im⟩ :=
  (rfl)

@[simp]
theorem coe_projVerticalClosedStrip_of_mem {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    (projVerticalClosedStrip z : ℂ) = z := by
  rw [coe_projVerticalClosedStrip, projIcc_of_mem _ hz]

@[simp]
theorem projVerticalClosedStrip_coe (z : verticalClosedStrip 0 1) :
    projVerticalClosedStrip z = z :=
  Subtype.ext (coe_projVerticalClosedStrip_of_mem z.2)

theorem continuous_projVerticalClosedStrip : Continuous projVerticalClosedStrip :=
  ((Complex.equivRealProdCLM.symm.continuous.comp
    (((continuous_subtype_val.comp (continuous_projIcc (h := zero_le_one))).comp
      continuous_re).prodMk continuous_im))).subtype_mk _

/-- The point `θ` of the strip, with `θ` clamped to `[0, 1]`. -/
theorem coe_projVerticalClosedStrip_ofReal (θ : ℝ) :
    (projVerticalClosedStrip θ : ℂ) = ((projIcc 0 1 zero_le_one θ : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [coe_projVerticalClosedStrip]

namespace CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### The Calderón space -/

/-- The *Calderón space* `𝓕(X₀, X₁)` of a compatible couple of complex normed spaces: the triples
`(F, f₀, f₁)` of a bounded continuous function `F` on the closed strip `0 ≤ re z ≤ 1` with values in
the sum space `X₀ + X₁`, holomorphic in the open strip, and its boundary values
`f₀ t = F (i t) ∈ X₀`, `f₁ t = F (1 + i t) ∈ X₁`, which are continuous and tend to zero at
infinity. The boundary values are determined by `F` (`calderonSpace_ext`), and the norm is
`max ‖f₀‖ ‖f₁‖` (`norm_calderonSpace`). -/
def calderonSpace :
    Submodule ℂ ((verticalClosedStrip 0 1 →ᵇ C.SumSpace) × C₀(ℝ, X₀) × C₀(ℝ, X₁)) where
  carrier := {F | DifferentiableOn ℂ (F.1 ∘ projVerticalClosedStrip) (verticalStrip 0 1) ∧
    (∀ t : ℝ, F.1 (projVerticalClosedStrip (t * I)) = C.fstToSum (F.2.1 t)) ∧
    ∀ t : ℝ, F.1 (projVerticalClosedStrip (1 + t * I)) = C.sndToSum (F.2.2 t)}
  zero_mem' := ⟨differentiableOn_const (0 : C.SumSpace), by simp, by simp⟩
  add_mem' {F G} hF hG := ⟨hF.1.add hG.1, fun t => by simp [hF.2.1 t, hG.2.1 t],
    fun t => by simp [hF.2.2 t, hG.2.2 t]⟩
  smul_mem' c F hF := ⟨hF.1.const_smul c, fun t => by simp [hF.2.1 t],
    fun t => by simp [hF.2.2 t]⟩

variable {C}

theorem mem_calderonSpace_iff
    {F : (verticalClosedStrip 0 1 →ᵇ C.SumSpace) × C₀(ℝ, X₀) × C₀(ℝ, X₁)} :
    F ∈ C.calderonSpace ↔
      DifferentiableOn ℂ (F.1 ∘ projVerticalClosedStrip) (verticalStrip 0 1) ∧
      (∀ t : ℝ, F.1 (projVerticalClosedStrip (t * I)) = C.fstToSum (F.2.1 t)) ∧
      ∀ t : ℝ, F.1 (projVerticalClosedStrip (1 + t * I)) = C.sndToSum (F.2.2 t) :=
  Iff.rfl

/-- An element of the Calderón space is determined by its values on the strip. -/
theorem calderonSpace_ext {F G : C.calderonSpace} (h : ∀ z, F.1.1 z = G.1.1 z) : F = G := by
  obtain ⟨⟨F, f₀, f₁⟩, hF⟩ := F
  obtain ⟨⟨G, g₀, g₁⟩, hG⟩ := G
  obtain rfl : F = G := BoundedContinuousFunction.ext h
  obtain rfl : f₀ = g₀ := ZeroAtInftyContinuousMap.ext fun t =>
    C.fstToSum_injective ((hF.2.1 t).symm.trans (hG.2.1 t))
  obtain rfl : f₁ = g₁ := ZeroAtInftyContinuousMap.ext fun t =>
    C.sndToSum_injective ((hF.2.2 t).symm.trans (hG.2.2 t))
  rfl

/-- **Hadamard three-lines bound.** An element `(F, f₀, f₁)` of the Calderón space satisfies
`‖F z‖ ≤ ‖f₀‖ ^ (1 - re z) * ‖f₁‖ ^ re z` on the strip. -/
theorem norm_apply_le_of_mem_calderonSpace
    {F : (verticalClosedStrip 0 1 →ᵇ C.SumSpace) × C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : F ∈ C.calderonSpace) (z : verticalClosedStrip 0 1) :
    ‖F.1 z‖ ≤ ‖F.2.1‖ ^ (1 - (z : ℂ).re) * ‖F.2.2‖ ^ (z : ℂ).re := by
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (a := ‖F.2.1‖) (b := ‖F.2.2‖) (F.1 ∘ projVerticalClosedStrip) z.2
    ⟨hF.1, (F.1.continuous.comp continuous_projVerticalClosedStrip).continuousOn⟩
    ⟨‖F.1‖, by rintro _ ⟨w, -, rfl⟩; exact F.1.norm_coe_le_norm _⟩ ?_ ?_
  · simpa using key
  · intro w hw
    have hw : w = (w.im : ℂ) * I := Complex.ext (by simpa using hw) (by simp)
    rw [Function.comp_apply, hw, hF.2.1]
    exact (C.norm_fstToSum_le _).trans
      ((F.2.1.toBCF.norm_coe_le_norm _).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)
  · intro w hw
    have hw : w = 1 + (w.im : ℂ) * I := Complex.ext (by simpa using hw) (by simp)
    rw [Function.comp_apply, hw, hF.2.2]
    exact (C.norm_sndToSum_le _).trans
      ((F.2.2.toBCF.norm_coe_le_norm _).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)

/-- The values of an element `(F, f₀, f₁)` of the Calderón space are bounded by
`max ‖f₀‖ ‖f₁‖`. -/
theorem norm_apply_le_max_of_mem_calderonSpace
    {F : (verticalClosedStrip 0 1 →ᵇ C.SumSpace) × C₀(ℝ, X₀) × C₀(ℝ, X₁)}
    (hF : F ∈ C.calderonSpace) (z : verticalClosedStrip 0 1) :
    ‖F.1 z‖ ≤ max ‖F.2.1‖ ‖F.2.2‖ :=
  (norm_apply_le_of_mem_calderonSpace hF z).trans <|
    (Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 z.2.2) z.2.1 (norm_nonneg _)
      (norm_nonneg _) (by ring)).trans <| by
      nlinarith [le_max_left ‖F.2.1‖ ‖F.2.2‖, le_max_right ‖F.2.1‖ ‖F.2.2‖, z.2.1, z.2.2]

/-- The norm of an element `(F, f₀, f₁)` of the Calderón space is `max ‖f₀‖ ‖f₁‖`, the larger of
the sup norms of its boundary values. -/
theorem norm_calderonSpace (F : C.calderonSpace) : ‖F‖ = max ‖F.1.2.1‖ ‖F.1.2.2‖ := by
  refine (Submodule.norm_coe F).symm.trans ?_
  rw [Prod.norm_def, Prod.norm_def, max_eq_right]
  exact (BoundedContinuousFunction.norm_le (le_max_of_le_left (norm_nonneg _))).2
    (norm_apply_le_max_of_mem_calderonSpace F.2)

/-! ### Closedness and completeness -/

/-- For Banach spaces `X₀`, `X₁` the Calderón space is a closed submodule: uniform limits of
functions holomorphic in the open strip are holomorphic there, and the boundary conditions pass to
limits. -/
theorem isClosed_calderonSpace [CompleteSpace X₀] [CompleteSpace X₁] :
    IsClosed (C.calderonSpace : Set ((verticalClosedStrip 0 1 →ᵇ C.SumSpace) × C₀(ℝ, X₀) ×
      C₀(ℝ, X₁))) := by
  refine isClosed_of_closure_subset fun F hF => ?_
  obtain ⟨G, hG, hGF⟩ := mem_closure_iff_seq_limit.1 hF
  have h₁ : Tendsto (fun n => (G n).1) atTop (𝓝 F.1) := (continuous_fst.tendsto _).comp hGF
  have h₂ : Tendsto (fun n => (G n).2) atTop (𝓝 F.2) := (continuous_snd.tendsto _).comp hGF
  have hev (z : verticalClosedStrip 0 1) : Tendsto (fun n => (G n).1 z) atTop (𝓝 (F.1 z)) :=
    ((BoundedContinuousFunction.evalCLM ℂ z).continuous.tendsto _).comp h₁
  have hev₀ (t : ℝ) : Tendsto (fun n => (G n).2.1 t) atTop (𝓝 (F.2.1 t)) :=
    ((((BoundedContinuousFunction.evalCLM ℂ t).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous).tendsto _).comp
        ((continuous_fst.tendsto _).comp h₂))
  have hev₁ (t : ℝ) : Tendsto (fun n => (G n).2.2 t) atTop (𝓝 (F.2.2 t)) :=
    ((((BoundedContinuousFunction.evalCLM ℂ t).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous).tendsto _).comp
        ((continuous_snd.tendsto _).comp h₂))
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · have hu : TendstoUniformly (fun n => (G n).1 ∘ projVerticalClosedStrip)
        (F.1 ∘ projVerticalClosedStrip) atTop :=
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 h₁).comp _
    exact TendstoLocallyUniformlyOn.differentiableOn
      (hu.tendstoUniformlyOn (s := verticalStrip 0 1)).tendstoLocallyUniformlyOn
      (Eventually.of_forall fun n => (hG n).1) (isOpen_Ioo.preimage continuous_re)
  · exact tendsto_nhds_unique (hev _) <| ((C.fstToSum.continuous.tendsto _).comp (hev₀ t)).congr
      fun n => ((hG n).2.1 t).symm
  · exact tendsto_nhds_unique (hev _) <| ((C.sndToSum.continuous.tendsto _).comp (hev₁ t)).congr
      fun n => ((hG n).2.2 t).symm

instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.calderonSpace :=
  isClosed_calderonSpace.completeSpace_coe

/-! ### Elements of the Calderón space -/

section Mk

variable (f : ℂ → C.SumSpace) (hf : DiffContOnCl ℂ f (verticalStrip 0 1))
  (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (f₀ : C₀(ℝ, X₀)) (f₁ : C₀(ℝ, X₁))
  (h₀ : ∀ t : ℝ, f (t * I) = C.fstToSum (f₀ t)) (h₁ : ∀ t : ℝ, f (1 + t * I) = C.sndToSum (f₁ t))

/-- The restriction to the strip of a function on `ℂ` that is continuous on the strip and bounded
there. -/
private def stripRestrict : verticalClosedStrip 0 1 →ᵇ C.SumSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup ((verticalClosedStrip 0 1).domRestrict f)
    (continuousOn_iff_continuous_domRestrict.1 (hf.2.mono (by
      rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one, verticalClosedStrip])))
    hB.choose
    fun z => hB.choose_spec ⟨(z : ℂ), z.2, rfl⟩

include hf h₀ h₁ in
private theorem mem_calderonSpace_stripRestrict :
    (stripRestrict f hf hB, f₀, f₁) ∈ C.calderonSpace := by
  refine ⟨hf.1.congr fun z hz => ?_, fun t => ?_, fun t => ?_⟩
  · simp [stripRestrict, coe_projVerticalClosedStrip_of_mem
      (Ioo_subset_Icc_self hz : z ∈ verticalClosedStrip 0 1)]
  · simp [stripRestrict, coe_projVerticalClosedStrip_of_mem
      (by simp [verticalClosedStrip] : (t * I : ℂ) ∈ verticalClosedStrip 0 1), h₀]
  · simp [stripRestrict, coe_projVerticalClosedStrip_of_mem
      (by simp [verticalClosedStrip] : (1 + t * I : ℂ) ∈ verticalClosedStrip 0 1), h₁]

variable (C) in
/-- The element of the Calderón space given by a function `f : ℂ → X₀ + X₁` that is bounded on the
closed strip `0 ≤ re z ≤ 1`, holomorphic in the open strip and continuous on the closed one, with
boundary values `f (i t) = f₀ t ∈ X₀` and `f (1 + i t) = f₁ t ∈ X₁` given by continuous functions
tending to zero at infinity. -/
def calderonMk : C.calderonSpace :=
  ⟨(stripRestrict f hf hB, f₀, f₁), mem_calderonSpace_stripRestrict f hf hB f₀ f₁ h₀ h₁⟩

@[simp]
theorem calderonMk_fst_apply (z : verticalClosedStrip 0 1) :
    (C.calderonMk f hf hB f₀ f₁ h₀ h₁).1.1 z = f z :=
  (rfl)

@[simp]
theorem calderonMk_snd_fst :
    (C.calderonMk f hf hB f₀ f₁ h₀ h₁).1.2.1 = f₀ :=
  (rfl)

@[simp]
theorem calderonMk_snd_snd :
    (C.calderonMk f hf hB f₀ f₁ h₀ h₁).1.2.2 = f₁ :=
  (rfl)

theorem norm_calderonMk : ‖C.calderonMk f hf hB f₀ f₁ h₀ h₁‖ = max ‖f₀‖ ‖f₁‖ :=
  norm_calderonSpace _

end Mk

/-! ### Evaluation -/

variable (C) in
/-- Evaluation of the elements of the Calderón space at a point of the strip. -/
def calderonEval (z : verticalClosedStrip 0 1) : C.calderonSpace →L[ℂ] C.SumSpace :=
  (BoundedContinuousFunction.evalCLM ℂ z).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp C.calderonSpace.subtypeL)

@[simp]
theorem calderonEval_apply (z : verticalClosedStrip 0 1) (F : C.calderonSpace) :
    C.calderonEval z F = F.1.1 z :=
  (rfl)

theorem norm_calderonEval_apply_le (z : verticalClosedStrip 0 1) (F : C.calderonSpace) :
    ‖C.calderonEval z F‖ ≤ ‖F‖ := by
  rw [calderonEval_apply, norm_calderonSpace]
  exact norm_apply_le_max_of_mem_calderonSpace F.2 z

instance (z : verticalClosedStrip 0 1) :
    IsClosed ((C.calderonEval z).ker : Set C.calderonSpace) :=
  (C.calderonEval z).isClosed_ker

/-! ### The complex interpolation space -/

variable (C) in
/-- The complex interpolation space `[X₀, X₁]_θ` of Calderón's complex method: the quotient of the
Calderón space by the kernel of evaluation at `θ`, with the quotient norm
`‖u‖_θ = inf {‖F‖ | F (θ) = u}`. Here `θ` is clamped to `[0, 1]`. It embeds injectively into the
sum space by `ComplexMethodSpace.toSum`, and it is a Banach space when `X₀` and `X₁` are. -/
abbrev ComplexMethodSpace (θ : ℝ) : Type _ :=
  C.calderonSpace ⧸ (C.calderonEval (projVerticalClosedStrip θ)).ker

namespace ComplexMethodSpace

variable {θ : ℝ}

/- Shortcut instances: the quotient instances, found without searching through the Calderón
space. -/
instance : NormedAddCommGroup (C.ComplexMethodSpace θ) :=
  Submodule.Quotient.normedAddCommGroup _

instance : NormedSpace ℂ (C.ComplexMethodSpace θ) :=
  Submodule.Quotient.normedSpace _ ℂ

/-- The element of `[X₀, X₁]_θ` represented by an element of the Calderón space. -/
def mk : C.calderonSpace →L[ℂ] C.ComplexMethodSpace θ :=
  Submodule.mkQL _

theorem mk_surjective : Function.Surjective (mk : C.calderonSpace → C.ComplexMethodSpace θ) :=
  Submodule.mkQ_surjective _

/-- The inclusion `[X₀, X₁]_θ → X₀ + X₁`, induced by evaluation at `θ`. -/
def toSum : C.ComplexMethodSpace θ →L[ℂ] C.SumSpace :=
  Submodule.liftQL _ (C.calderonEval (projVerticalClosedStrip θ)) le_rfl

@[simp]
theorem toSum_mk (F : C.calderonSpace) :
    toSum (mk F : C.ComplexMethodSpace θ) = C.calderonEval (projVerticalClosedStrip θ) F :=
  (rfl)

theorem mk_eq_mk_iff {F G : C.calderonSpace} :
    (mk F : C.ComplexMethodSpace θ) = mk G ↔
      C.calderonEval (projVerticalClosedStrip θ) F =
        C.calderonEval (projVerticalClosedStrip θ) G := by
  rw [mk, Submodule.mkQL_apply, Submodule.mkQL_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero, ContinuousLinearMap.coe_coe]

theorem toSum_injective : Function.Injective (toSum : C.ComplexMethodSpace θ → C.SumSpace) := by
  intro u v h
  obtain ⟨F, rfl⟩ := mk_surjective u
  obtain ⟨G, rfl⟩ := mk_surjective v
  exact mk_eq_mk_iff.2 h

@[ext]
theorem ext {u v : C.ComplexMethodSpace θ} (h : toSum u = toSum v) : u = v :=
  toSum_injective h

/-- The quotient norm of `[X₀, X₁]_θ`: `‖u‖_θ < r` exactly when `u` is represented by an element of
the Calderón space of norm less than `r`. -/
theorem norm_lt_iff {u : C.ComplexMethodSpace θ} {r : ℝ} :
    ‖u‖ < r ↔ ∃ F : C.calderonSpace, mk F = u ∧ ‖F‖ < r :=
  QuotientAddGroup.norm_lt_iff

theorem norm_mk_le (F : C.calderonSpace) : ‖(mk F : C.ComplexMethodSpace θ)‖ ≤ ‖F‖ :=
  Submodule.Quotient.norm_mk_le _ F

/-- The inclusion into the sum space does not increase norms. -/
theorem norm_toSum_le (u : C.ComplexMethodSpace θ) : ‖toSum u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨F, rfl, hF⟩ := norm_lt_iff.1 hr
  exact (norm_calderonEval_apply_le _ F).trans_lt hF

theorem opNorm_toSum_le : ‖toSum (C := C) (θ := θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_toSum_le u

/-! ### The inclusion of the intersection -/

section Inter

variable (C θ) in
/-- The element `z ↦ exp (δ (z - c) ^ 2) x` of the Calderón space, for `x` in the intersection,
`δ > 0` and `c = θ` clamped to `[0, 1]`. Its value at `θ` is `x`. -/
private def gaussian (δ : ℝ) (hδ : 0 < δ) (x : C.inter) : C.calderonSpace :=
  let c : ℝ := projIcc 0 1 zero_le_one θ
  have hc := (projIcc 0 1 zero_le_one θ).2
  have hnorm (z : ℂ) : ‖exp (δ * (z - c) ^ 2)‖ = Real.exp (δ * ((z.re - c) ^ 2 - z.im ^ 2)) := by
    rw [Complex.norm_exp]
    simp [sq]
  have hdecay (a : ℝ) : Tendsto (fun t : ℝ => Real.exp (δ * (a - t ^ 2))) (cocompact ℝ) (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot hδ ?_)
    refine tendsto_atBot_add_const_left _ a (tendsto_neg_atTop_atBot.comp ?_)
    refine ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).congr fun t => ?_
    simp [Real.norm_eq_abs, sq_abs]
  C.calderonMk (fun z => exp (δ * (z - c) ^ 2) • C.fstToSum (C.interFst x))
    (Differentiable.diffContOnCl (by fun_prop))
    ⟨Real.exp δ * ‖C.fstToSum (C.interFst x)‖, by
      rintro _ ⟨z, hz, rfl⟩
      rw [Function.comp_apply, norm_smul, hnorm]
      gcongr
      have : (z.re - c) ^ 2 ≤ 1 := by
        rw [sq_le_one_iff_abs_le_one, abs_le]
        constructor <;> linarith [hz.1, hz.2, hc.1, hc.2]
      nlinarith [sq_nonneg z.im]⟩
    { toFun t := exp (δ * (t * I - c) ^ 2) • C.interFst x
      continuous_toFun := by fun_prop
      zero_at_infty' := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine ((hdecay (c ^ 2)).mul_const ‖C.interFst x‖).congr' ?_ |>.trans (by simp)
        filter_upwards with t
        simp [norm_smul, hnorm] }
    { toFun t := exp (δ * (1 + t * I - c) ^ 2) • C.interSnd x
      continuous_toFun := by fun_prop
      zero_at_infty' := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine ((hdecay ((1 - c) ^ 2)).mul_const ‖C.interSnd x‖).congr' ?_ |>.trans (by simp)
        filter_upwards with t
        simp [norm_smul, hnorm] }
    (fun t => by simp)
    (fun t => by rw [C.fstToSum_interFst]; simp)

private theorem toSum_mk_gaussian (δ : ℝ) (hδ : 0 < δ) (x : C.inter) :
    toSum (mk (gaussian C θ δ hδ x) : C.ComplexMethodSpace θ) = C.fstToSum (C.interFst x) := by
  simp [gaussian, coe_projVerticalClosedStrip_ofReal]

private theorem norm_gaussian_le (δ : ℝ) (hδ : 0 < δ) (x : C.inter) :
    ‖gaussian C θ δ hδ x‖ ≤ Real.exp δ * ‖x‖ := by
  have hc := (projIcc 0 1 zero_le_one θ).2
  have key (c t : ℝ) (hc : c ∈ Icc 0 1) : Real.exp (δ * (c * c - t * t)) ≤ Real.exp δ := by
    have h₁ : c * c ≤ 1 := by nlinarith [hc.1, hc.2]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hδ.le (sub_nonneg.2 h₁), mul_nonneg hδ.le (mul_self_nonneg t)]
  rw [norm_calderonSpace]
  refine max_le (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.symm.trans_le
      ((BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_))
    (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.symm.trans_le
      ((BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_))
  · simpa [gaussian, norm_smul, Complex.norm_exp, sq] using
      mul_le_mul (key _ t hc) (norm_fst_le _) (norm_nonneg _) (Real.exp_pos _).le
  · simpa [gaussian, norm_smul, Complex.norm_exp, sq] using
      mul_le_mul (key _ t ⟨by linarith [hc.2], by linarith [hc.1]⟩) (norm_snd_le _)
        (norm_nonneg _) (Real.exp_pos _).le

variable (θ) in
/-- The inclusion `X₀ ∩ X₁ → [X₀, X₁]_θ`, of norm at most `1` (`norm_ofInter_le`). -/
def ofInter : C.inter →L[ℂ] C.ComplexMethodSpace θ :=
  LinearMap.mkContinuous
    { toFun x := mk (gaussian C θ 1 one_pos x)
      map_add' x y := by ext; simp only [map_add, toSum_mk_gaussian]
      map_smul' c x := by ext; simp only [map_smul, toSum_mk_gaussian, RingHom.id_apply] }
    1 fun x => by
      -- the representatives `gaussian C θ δ` with `δ → 0` give the bound
      have h (δ : ℝ) (hδ : 0 < δ) :
          ‖(mk (gaussian C θ 1 one_pos x) : C.ComplexMethodSpace θ)‖ ≤ Real.exp δ * ‖x‖ := by
        have : (mk (gaussian C θ 1 one_pos x) : C.ComplexMethodSpace θ) =
            mk (gaussian C θ δ hδ x) := by
          ext
          rw [toSum_mk_gaussian, toSum_mk_gaussian]
        rw [this]
        exact (norm_mk_le _).trans (norm_gaussian_le δ hδ x)
      refine ge_of_tendsto (x := 𝓝[>] (0 : ℝ)) ?_ (eventually_nhdsWithin_of_forall h)
      simpa using ((Real.continuous_exp.tendsto 0).mul_const ‖x‖).mono_left nhdsWithin_le_nhds

@[simp]
theorem toSum_ofInter (x : C.inter) : toSum (ofInter θ x) = C.fstToSum (C.interFst x) :=
  toSum_mk_gaussian 1 one_pos x

theorem opNorm_ofInter_le : ‖(ofInter θ : C.inter →L[ℂ] C.ComplexMethodSpace θ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The norm of `x ∈ X₀ ∩ X₁` in `[X₀, X₁]_θ` is at most its norm `max ‖x₀‖ ‖x₁‖` in the
intersection. -/
theorem norm_ofInter_le (x : C.inter) : ‖ofInter θ x‖ ≤ ‖x‖ := by
  simpa using (ofInter θ : C.inter →L[ℂ] C.ComplexMethodSpace θ).le_of_opNorm_le opNorm_ofInter_le x

end Inter

/-! ### Functoriality -/

section Map

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁]
  [NormedSpace ℂ Y₁] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W]
  [T1Space W] {D : CompatibleCouple ℂ Y₀ Y₁ W}
  (T : C.SumSpace →ₗ[ℂ] D.SumSpace) {T₀ : X₀ →L[ℂ] Y₀} {T₁ : X₁ →L[ℂ] Y₁}
  (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
  (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))

variable (θ) in
/-- The element `z ↦ exp (a (z - c)) T (F z)` of the Calderón space of the target couple, for real
`a` and `c = θ` clamped to `[0, 1]`. Its value at `θ` is `T (F θ)`. -/
private def calderonMapAux (a : ℝ) (F : C.calderonSpace) : D.calderonSpace :=
  let c : ℝ := projIcc 0 1 zero_le_one θ
  have hc := (projIcc 0 1 zero_le_one θ).2
  let T' : C.SumSpace →L[ℂ] D.SumSpace := ⟨T, C.continuous_of_comp_fstToSum_sndToSum T hT₀ hT₁⟩
  have hgB (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖exp (a * (z - c))‖ ≤ Real.exp |a| := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    have : |z.re - c| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hz.2, hc.1], by linarith [hz.1, hc.2]⟩
    simpa [abs_mul] using mul_le_of_le_one_right (abs_nonneg a) this
  D.calderonMk (fun z => exp (a * (z - c)) • T' (F.1.1 (projVerticalClosedStrip z)))
    ⟨(by fun_prop : Differentiable ℂ fun z : ℂ => exp (a * (z - c))).differentiableOn.smul
      (T'.differentiable.comp_differentiableOn F.2.1),
      ((by fun_prop : Continuous fun z : ℂ => exp (a * (z - c))).smul
        (T'.continuous.comp (F.1.1.continuous.comp
          continuous_projVerticalClosedStrip))).continuousOn⟩
    ⟨Real.exp |a| * (‖T'‖ * ‖F.1.1‖), by
      rintro _ ⟨z, hz, rfl⟩
      rw [Function.comp_apply, norm_smul]
      exact mul_le_mul (hgB z hz) (T'.le_opNorm_of_le (F.1.1.norm_coe_le_norm _))
        (norm_nonneg _) (Real.exp_pos _).le⟩
    { toFun t := exp (a * (t * I - c)) • T₀ (F.1.2.1 t)
      continuous_toFun := (by fun_prop : Continuous fun t : ℝ => exp (a * (t * I - c))).smul
        (T₀.continuous.comp F.1.2.1.continuous)
      zero_at_infty' := by
        refine squeeze_zero_norm (fun t => (norm_smul _ _).trans_le (mul_le_mul
          (hgB _ (by simp [verticalClosedStrip])) (T₀.le_opNorm _) (norm_nonneg _)
          (Real.exp_pos _).le)) ?_
        simpa using ((ZeroAtInftyContinuousMapClass.zero_at_infty F.1.2.1).norm.const_mul
          ‖T₀‖).const_mul (Real.exp |a|) }
    { toFun t := exp (a * (1 + t * I - c)) • T₁ (F.1.2.2 t)
      continuous_toFun := (by fun_prop : Continuous fun t : ℝ => exp (a * (1 + t * I - c))).smul
        (T₁.continuous.comp F.1.2.2.continuous)
      zero_at_infty' := by
        refine squeeze_zero_norm (fun t => (norm_smul _ _).trans_le (mul_le_mul
          (hgB _ (by simp [verticalClosedStrip])) (T₁.le_opNorm _) (norm_nonneg _)
          (Real.exp_pos _).le)) ?_
        simpa using ((ZeroAtInftyContinuousMapClass.zero_at_infty F.1.2.2).norm.const_mul
          ‖T₁‖).const_mul (Real.exp |a|) }
    (fun t => by simp [T', F.2.2.1 t, hT₀])
    (fun t => by simp [T', F.2.2.2 t, hT₁])

private theorem calderonMapAux_apply (a : ℝ) (F : C.calderonSpace) (z : verticalClosedStrip 0 1) :
    (calderonMapAux θ T hT₀ hT₁ a F).1.1 z =
      exp (a * ((z : ℂ) - (projIcc 0 1 zero_le_one θ : ℝ))) • T (F.1.1 z) := by
  simp [calderonMapAux]

private theorem norm_calderonMapAux_fst_le (a : ℝ) {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (F : C.calderonSpace) :
    ‖(calderonMapAux θ T hT₀ hT₁ a F).1.2.1‖ ≤
      Real.exp (-(a * projIcc 0 1 zero_le_one θ)) * M₀ * ‖F.1.2.1‖ := by
  refine ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.symm.trans_le
    ((BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_)
  simpa [calderonMapAux, norm_smul, Complex.norm_exp, mul_assoc] using
    mul_le_mul_of_nonneg_left ((h₀ _).trans (mul_le_mul_of_nonneg_left
      ((F.1.2.1.toBCF.norm_coe_le_norm t).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)
      hM₀)) (Real.exp_pos _).le

private theorem norm_calderonMapAux_snd_le (a : ℝ) {M₁ : ℝ} (hM₁ : 0 ≤ M₁)
    (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (F : C.calderonSpace) :
    ‖(calderonMapAux θ T hT₀ hT₁ a F).1.2.2‖ ≤
      Real.exp (a * (1 - projIcc 0 1 zero_le_one θ)) * M₁ * ‖F.1.2.2‖ := by
  refine ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.symm.trans_le
    ((BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_)
  simpa [calderonMapAux, norm_smul, Complex.norm_exp, mul_assoc] using
    mul_le_mul_of_nonneg_left ((h₁ _).trans (mul_le_mul_of_nonneg_left
      ((F.1.2.2.toBCF.norm_coe_le_norm t).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)
      hM₁)) (Real.exp_pos _).le

variable (θ) in
/-- The map `F ↦ T ∘ F` of Calderón spaces. -/
private def calderonMap : C.calderonSpace →L[ℂ] D.calderonSpace :=
  LinearMap.mkContinuous
    { toFun := calderonMapAux θ T hT₀ hT₁ 0
      map_add' F G := calderonSpace_ext fun z => by simp [calderonMapAux_apply]
      map_smul' c F := calderonSpace_ext fun z => by simp [calderonMapAux_apply] }
    (max ‖T₀‖ ‖T₁‖) fun F => by
      have h₀ := norm_calderonMapAux_fst_le T hT₀ hT₁ (θ := θ) 0 (norm_nonneg _) T₀.le_opNorm F
      have h₁ := norm_calderonMapAux_snd_le T hT₀ hT₁ (θ := θ) 0 (norm_nonneg _) T₁.le_opNorm F
      simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at h₀ h₁
      refine (norm_calderonSpace _).trans_le ((max_le (h₀.trans (mul_le_mul (le_max_left _ _)
        (le_max_left _ _) (norm_nonneg _) (by positivity))) (h₁.trans (mul_le_mul
        (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) (by positivity)))).trans_eq ?_)
      exact congrArg (max ‖T₀‖ ‖T₁‖ * ·) (norm_calderonSpace F).symm

private theorem calderonMap_apply (F : C.calderonSpace) :
    calderonMap θ T hT₀ hT₁ F = calderonMapAux θ T hT₀ hT₁ 0 F :=
  (rfl)

/-- The continuous linear map `[X₀, X₁]_θ → [Y₀, Y₁]_θ` induced by a linear map `T` of sum spaces
that restricts to continuous linear maps `T₀ : X₀ →L[ℂ] Y₀` and `T₁ : X₁ →L[ℂ] Y₁`: it is
`F (θ) ↦ T (F (θ))` on representatives. If `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖` for positive
`M₀`, `M₁`, it multiplies norms by at most `M₀ ^ (1 - θ) * M₁ ^ θ` (`norm_map_le`). -/
def map : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ :=
  Submodule.liftQL _ ((mk : D.calderonSpace →L[ℂ] D.ComplexMethodSpace θ).comp
    (calderonMap θ T hT₀ hT₁)) fun F hF => by
    rw [LinearMap.mem_ker] at hF ⊢
    ext
    simp only [ContinuousLinearMap.coe_coe, calderonEval_apply] at hF
    simp [calderonMap_apply, calderonMapAux_apply, hF]

@[simp]
theorem toSum_map (u : C.ComplexMethodSpace θ) : toSum (map T hT₀ hT₁ u) = T (toSum u) := by
  obtain ⟨F, rfl⟩ := mk_surjective u
  have : map T hT₀ hT₁ (mk F : C.ComplexMethodSpace θ) = mk (calderonMap θ T hT₀ hT₁ F) := (rfl)
  rw [this, toSum_mk, toSum_mk]
  simp [calderonMap_apply, calderonMapAux_apply]

/-- **Exactness of the complex method.** For `0 ≤ θ ≤ 1`, if `‖T₀ x‖ ≤ M₀ ‖x‖` and
`‖T₁ x‖ ≤ M₁ ‖x‖` for positive `M₀`, `M₁`, the induced map multiplies the norm by at most
`M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem norm_map_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.ComplexMethodSpace θ) :
    ‖map T hT₀ hT₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  -- a representative `F` of `u` gives the representative `z ↦ exp (a (z - θ)) T (F z)` of the
  -- image, where `a = log M₀ - log M₁` balances the two boundary bounds
  set K := M₀ ^ (1 - θ) * M₁ ^ θ with hK
  set a := Real.log M₀ - Real.log M₁
  have hc : ((projIcc 0 1 zero_le_one θ : ℝ)) = θ := by rw [projIcc_of_mem _ hθ]
  have e₀ : Real.exp (-(a * θ)) * M₀ = K := by
    calc Real.exp (-(a * θ)) * M₀ = Real.exp (-(a * θ)) * Real.exp (Real.log M₀) := by
          rw [Real.exp_log hM₀]
      _ = K := by
          rw [← Real.exp_add, hK, Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁,
            ← Real.exp_add]
          congr 1
          ring
  have e₁ : Real.exp (a * (1 - θ)) * M₁ = K := by
    calc Real.exp (a * (1 - θ)) * M₁ = Real.exp (a * (1 - θ)) * Real.exp (Real.log M₁) := by
          rw [Real.exp_log hM₁]
      _ = K := by
          rw [← Real.exp_add, hK, Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁,
            ← Real.exp_add]
          congr 1
          ring
  have key (F : C.calderonSpace) (hF : mk F = u) : ‖map T hT₀ hT₁ u‖ ≤ K * ‖F‖ := by
    have : map T hT₀ hT₁ u = mk (calderonMapAux θ T hT₀ hT₁ a F) := by
      ext
      rw [toSum_map, ← hF, toSum_mk, toSum_mk]
      simp [calderonMapAux_apply, coe_projVerticalClosedStrip_ofReal]
    rw [this]
    refine (norm_mk_le _).trans ?_
    rw [norm_calderonSpace, norm_calderonSpace, mul_max_of_nonneg _ _ (by positivity)]
    refine max_le_max ?_ ?_
    · refine (norm_calderonMapAux_fst_le T hT₀ hT₁ a hM₀.le h₀ F).trans_eq ?_
      rw [hc, e₀]
    · refine (norm_calderonMapAux_snd_le T hT₀ hT₁ a hM₁.le h₁ F).trans_eq ?_
      rw [hc, e₁]
  refine ge_of_tendsto (x := 𝓝[>] ‖u‖)
    (tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const.mul continuous_id).tendsto ‖u‖))
    (eventually_nhdsWithin_of_forall fun r hr => ?_)
  obtain ⟨F, hF, hFr⟩ := norm_lt_iff.1 hr
  exact (key F hF).trans (mul_le_mul_of_nonneg_left hFr.le (by positivity))

/-- **Exactness of the complex method.** For `0 ≤ θ ≤ 1`, if `‖T₀ x‖ ≤ M₀ ‖x‖` and
`‖T₁ x‖ ≤ M₁ ‖x‖` for positive `M₀`, `M₁`, the induced map has norm at most
`M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem opNorm_map_le (hθ : θ ∈ Icc 0 1) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖(map T hT₀ hT₁ : C.ComplexMethodSpace θ →L[ℂ] D.ComplexMethodSpace θ)‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_map_le T hT₀ hT₁ hθ hM₀ hM₁ h₀ h₁)

end Map

/-- The identity of the couple induces the identity of the complex interpolation space. -/
theorem map_id :
    map (θ := θ) (LinearMap.id : C.SumSpace →ₗ[ℂ] C.SumSpace)
      (T₀ := ContinuousLinearMap.id ℂ X₀) (T₁ := ContinuousLinearMap.id ℂ X₁)
      (fun _ => rfl) (fun _ => rfl) = ContinuousLinearMap.id ℂ _ := by
  ext u
  exact toSum_map _ _ _ u

variable {Y₀ Y₁ W Z₀ Z₁ U : Type*} [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀]
  [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
  [ContinuousAdd W] [T1Space W] [NormedAddCommGroup Z₀] [NormedSpace ℂ Z₀] [NormedAddCommGroup Z₁]
  [NormedSpace ℂ Z₁] [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [ContinuousAdd U]
  [T1Space U] {D : CompatibleCouple ℂ Y₀ Y₁ W} {E : CompatibleCouple ℂ Z₀ Z₁ U} in
/-- The map induced by a composite of morphisms of couples is the composite of the induced
maps. -/
theorem map_comp (S : D.SumSpace →ₗ[ℂ] E.SumSpace) (T : C.SumSpace →ₗ[ℂ] D.SumSpace)
    {S₀ : Y₀ →L[ℂ] Z₀} {S₁ : Y₁ →L[ℂ] Z₁} {T₀ : X₀ →L[ℂ] Y₀} {T₁ : X₁ →L[ℂ] Y₁}
    (hS₀ : ∀ y, S (D.fstToSum y) = E.fstToSum (S₀ y))
    (hS₁ : ∀ y, S (D.sndToSum y) = E.sndToSum (S₁ y))
    (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) :
    map (θ := θ) (S ∘ₗ T) (T₀ := S₀.comp T₀) (T₁ := S₁.comp T₁)
        (fun x => by simp [hT₀, hS₀]) (fun x => by simp [hT₁, hS₁]) =
      (map S hS₀ hS₁).comp (map T hT₀ hT₁) := by
  ext u
  exact (toSum_map _ _ _ u).trans
    ((toSum_map S hS₀ hS₁ _).trans (congrArg S (toSum_map T hT₀ hT₁ u))).symm

/-! ### The diagonal couple -/

/-- For the couple `(X, X)`, the norm of `[X, X]_θ` is the norm of `X`: the inclusion into the sum
space, which is `X`, is an isometry. -/
theorem norm_refl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (u : (refl ℂ X).ComplexMethodSpace θ) : ‖u‖ = ‖toSum u‖ := by
  refine le_antisymm ?_ (norm_toSum_le u)
  set x := (refl ℂ X).sumSpaceEmbed (toSum u)
  have hx : (x, x) ∈ (refl ℂ X).inter := by simp
  have hu : ofInter θ ⟨(x, x), hx⟩ = u := by
    ext
    simp [x]
  calc ‖u‖ = ‖ofInter θ ⟨(x, x), hx⟩‖ := by rw [hu]
    _ ≤ ‖(⟨(x, x), hx⟩ : (refl ℂ X).inter)‖ := norm_ofInter_le _
    _ = ‖toSum u‖ := by simp [x, norm_refl_sumSpaceEmbed]

end ComplexMethodSpace

end CompatibleCouple

end TauCeti
