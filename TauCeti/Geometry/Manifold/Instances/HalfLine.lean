/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The closed and open half-lines

This file collects the elementary geometry of the one-dimensional closed half-line
`EuclideanHalfSpace 1` (`[0, ∞)`) and its open interior `(0, ∞)`
(`⟨Set.Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ`):

* `TauCeti.EuclideanHalfSpace.normalRay`: the inward normal ray `ℝ → EuclideanHalfSpace 1`,
  sending `r` to the point with zeroth coordinate `max r 0`, and its smoothness on `Ici 0`
  (`TauCeti.EuclideanHalfSpace.contMDiffOn_normalRay`) and along nonnegative `C^k` functions
  (`ContMDiff.normalRay`).
* `TauCeti.openHalfLineInclusion`, `TauCeti.contMDiff_openHalfLineInclusion`: the smooth inclusion
  of `(0, ∞)` into `EuclideanHalfSpace 1`.
* `EuclideanHalfSpace.halfLineInwardTranslation`,
  `EuclideanHalfSpace.contMDiff_halfLineInwardTranslation`: the smooth inward translation
  `x ↦ x + 1` from `EuclideanHalfSpace 1` into `(0, ∞)`.
* `TauCeti.halfLineInwardDeformation`, `TauCeti.contMDiff_halfLineInwardDeformation`,
  `TauCeti.halfLineInwardDeformation_zero`, `TauCeti.halfLineInwardDeformation_one`: the global
  smooth inward deformation `(t, x) ↦ x + (1 - t)²` on `ℝ × [0, ∞)` from `j ∘ r` to `id`.
* `TauCeti.starConvex_openHalfLine`: the open positive half-line `(0, ∞)` is star-convex about
  `1`.
-/

public section

noncomputable section

open Function Set Topology WithLp
open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

/-- The inward normal ray of the one-dimensional half-space model: the point of
`EuclideanHalfSpace 1` at normal distance `r` from the boundary, for `r ≤ 0` the origin.

Truncating at `0` is what makes the ray a globally defined continuous map on `ℝ`; it is used
only for `0 ≤ r`, where `normalRay_normalCoord` inverts it. -/
def normalRay (r : ℝ) : EuclideanHalfSpace 1 := ⟨toLp 2 fun _ ↦ max r 0, le_max_right r 0⟩

/-- The normal coordinate of a point of the normal ray. -/
@[simp]
theorem normalRay_coe_apply (r : ℝ) : (normalRay r).val 0 = max r 0 := (rfl)

/-- The origin of the one-dimensional half-space model has vanishing normal coordinate. -/
@[simp]
theorem val_zero_apply : (0 : EuclideanHalfSpace 1).val 0 = 0 := (rfl)

/-- The normal ray starts at the origin. -/
@[simp]
theorem normalRay_zero : normalRay 0 = 0 := by
  refine _root_.EuclideanHalfSpace.ext _ _ ?_
  ext i
  rw [Subsingleton.elim i 0]
  simp [normalRay]

/-- The normal ray parametrizes the one-dimensional half-space model by its normal coordinate. -/
@[simp]
theorem normalRay_normalCoord (t : EuclideanHalfSpace 1) : normalRay (t.val 0) = t := by
  refine _root_.EuclideanHalfSpace.ext _ _ ?_
  ext i
  rw [Subsingleton.elim i 0]
  simp [normalRay, max_eq_left t.property]

/-- The normal ray is the inverse of the model with corners of the half-line, applied to the
reals viewed as `ℝ¹`. -/
theorem normalRay_eq_symm (r : ℝ) :
    normalRay r = (𝓡∂ 1).symm ((PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm r) := by
  refine _root_.EuclideanHalfSpace.ext _ _ ?_
  ext i
  rw [Subsingleton.elim i 0]
  simp [modelWithCornersEuclideanHalfSpace_symm_apply]

/-- The normal ray is continuous. -/
theorem continuous_normalRay : Continuous normalRay := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

/-- The normal ray along a nonnegative `C^k` function is `C^k` into the one-dimensional
half-space model. -/
theorem _root_.ContMDiff.normalRay {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M]
    [ChartedSpace H' M] {k : WithTop ℕ∞} {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) k f)
    (hf0 : ∀ x, 0 ≤ f x) : ContMDiff I (𝓡∂ 1) k fun x ↦ normalRay (f x) := by
  have hcoord : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) k
      fun x ↦ (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm (f x) :=
    (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.contDiff.contMDiff.comp hf
  have hrange (x : M) : (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm (f x) ∈ range (𝓡∂ 1) := by
    rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
    simpa using hf0 x
  exact ((𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hcoord hrange).congr fun x ↦ normalRay_eq_symm _

/-- A point of the one-dimensional half-space model vanishes exactly when its normal coordinate
does. -/
@[simp]
theorem eq_zero_iff {t : EuclideanHalfSpace 1} : t = 0 ↔ t.val 0 = 0 := by
  refine ⟨fun h ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  rw [← normalRay_normalCoord t, h, normalRay_zero]

/-- The normal ray is `C^k` on the nonnegative reals, where it is the inverse of the model with
corners of the half-line. -/
theorem contMDiffOn_normalRay {k : WithTop ℕ∞} :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) k normalRay (Ici 0) := by
  refine ((𝓡∂ 1).contMDiffOn_symm.comp
    (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.contDiff.contMDiff.contMDiffOn
    fun r hr ↦ ?_).congr fun r _ ↦ normalRay_eq_symm r
  rw [mem_preimage, range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
  simpa using hr

end EuclideanHalfSpace

/-- Inclusion of the open half-line `(0, ∞)` into the closed half-line `EuclideanHalfSpace 1`. -/
def openHalfLineInclusion (y : (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ)) :
    EuclideanHalfSpace 1 :=
  EuclideanHalfSpace.normalRay y.val

/-- The `0`-th coordinate of `openHalfLineInclusion y` is `y`. -/
@[simp]
theorem coe_openHalfLineInclusion_apply
    (y : (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ)) :
    (openHalfLineInclusion y).val 0 = y.val := by
  rw [openHalfLineInclusion, EuclideanHalfSpace.normalRay_coe_apply,
    max_eq_left (Set.mem_Ioi.mp y.property).le]

/-- The inclusion `(0, ∞) → [0, ∞)` is smooth with respect to `𝓘(ℝ, ℝ)` and `𝓡∂ 1`. -/
theorem contMDiff_openHalfLineInclusion :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ openHalfLineInclusion :=
  contMDiff_subtypeVal.normalRay fun y ↦ (Set.mem_Ioi.mp y.property).le

end TauCeti

namespace EuclideanHalfSpace

open TauCeti

/-- Smooth inward translation `r(x) = x + 1` from the closed half-line `[0, ∞)` into its open
interior `(0, ∞)`. -/
def halfLineInwardTranslation (x : EuclideanHalfSpace 1) :
    (⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ) :=
  ⟨x.val 0 + 1, Set.mem_Ioi.mpr (add_pos_of_nonneg_of_pos x.property zero_lt_one)⟩

/-- The underlying real value of `halfLineInwardTranslation x` is `x.val 0 + 1`. -/
@[simp]
theorem coe_halfLineInwardTranslation (x : EuclideanHalfSpace 1) :
    (x.halfLineInwardTranslation : ℝ) = x.val 0 + 1 :=
  (rfl)

/-- The inward translation `r(x) = x + 1` is smooth from `EuclideanHalfSpace 1` to `(0, ∞)`. -/
theorem contMDiff_halfLineInwardTranslation :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ halfLineInwardTranslation := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (contDiff_id.add contDiff_const).contMDiff.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp (𝓡∂ 1).contMDiff)

end EuclideanHalfSpace

namespace TauCeti

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` on `ℝ × [0, ∞)`: because `(1 - t)² ≥ 0` for all
`t ∈ ℝ`, it stays in `[0, ∞)` globally in `t`, starts at `j(r(x)) = x + 1` at `t = 0`, and reaches
`x` at `t = 1`. -/
def halfLineInwardDeformation (p : ℝ × EuclideanHalfSpace 1) : EuclideanHalfSpace 1 :=
  EuclideanHalfSpace.normalRay (p.2.val 0 + (1 - p.1) ^ 2)

/-- The `0`-th coordinate of `halfLineInwardDeformation (t, x)` is `x + (1 - t)²`. -/
@[simp]
theorem coe_halfLineInwardDeformation_apply (p : ℝ × EuclideanHalfSpace 1) :
    (halfLineInwardDeformation p).val 0 = p.2.val 0 + (1 - p.1) ^ 2 := by
  rw [halfLineInwardDeformation, EuclideanHalfSpace.normalRay_coe_apply,
    max_eq_left (add_nonneg p.2.property (sq_nonneg (1 - p.1)))]

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` preserves the open interior `(0, ∞)` at every
time `t ∈ ℝ`. -/
theorem halfLineInwardDeformation_pos {t : ℝ} {x : EuclideanHalfSpace 1} (hx : 0 < x.val 0) :
    0 < (halfLineInwardDeformation (t, x)).val 0 := by
  rw [coe_halfLineInwardDeformation_apply]
  nlinarith [sq_nonneg (1 - t)]

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` is jointly smooth on `ℝ × [0, ∞)`. -/
theorem contMDiff_halfLineInwardDeformation :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡∂ 1) ∞ halfLineInwardDeformation := by
  have hx : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × EuclideanHalfSpace 1 ↦ p.2.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
      (𝓡∂ 1).contMDiff).comp contMDiff_snd
  have hg : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ q.2 + (1 - q.1) ^ 2) := by fun_prop
  exact (hg.contMDiff.comp (contMDiff_fst.prodMk_space hx)).normalRay
    fun p ↦ add_nonneg p.2.property (sq_nonneg (1 - p.1))

/-- At `t = 0`, `halfLineInwardDeformation` agrees with `j ∘ r`. -/
@[simp]
theorem halfLineInwardDeformation_zero (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (0, x) = openHalfLineInclusion x.halfLineInwardTranslation := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply, coe_openHalfLineInclusion_apply,
    EuclideanHalfSpace.coe_halfLineInwardTranslation]
  ring

/-- At `t = 1`, `halfLineInwardDeformation` is the identity on `[0, ∞)`. -/
@[simp]
theorem halfLineInwardDeformation_one (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (1, x) = x := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply]
  ring

/-- The open positive half-line `(0, ∞)` is star-convex about `1`. -/
theorem starConvex_openHalfLine :
    StarConvex ℝ (1 : ℝ)
      (𝓘(ℝ) '' ((⟨Ioi 0, isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ) : Set ℝ)) := by
  simpa using (convex_Ioi (0 : ℝ)).starConvex (zero_lt_one : (1 : ℝ) ∈ Ioi 0)

end TauCeti
