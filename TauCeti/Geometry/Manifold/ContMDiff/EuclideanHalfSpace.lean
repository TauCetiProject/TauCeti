/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth maps into Euclidean half-spaces

A nonnegative `C^n` real-valued function `f : M → ℝ` on a manifold lifts along the `0`-th
coordinate embedding `t ↦ (𝓡∂ k).symm (EuclideanSpace.single 0 t)` to a `C^n` map into
`EuclideanHalfSpace k` (`ContMDiff.modelWithCornersEuclideanHalfSpace_symm_single`). In
particular, for `k = 1`, any nonnegative `C^n` real function defines a `C^n` map into the closed
half-line `EuclideanHalfSpace 1`.

Specializing to dimension `1`, this file also sets up the inward domination of the closed half-line
`EuclideanHalfSpace 1` (`[0, ∞)`) by the open half-line `TauCeti.openHalfLine` (`(0, ∞)`): the
smooth inclusion `TauCeti.openHalfLineInclusion : openHalfLine → EuclideanHalfSpace 1`, the inward
translation `EuclideanHalfSpace.halfLineInwardTranslation : x ↦ x + 1`, and the global smooth
inward deformation `TauCeti.halfLineInwardDeformation : (t, x) ↦ x + (1 - t)²` from `j ∘ r` to
`id`, together with star-convexity of `openHalfLine` (`TauCeti.starConvex_openHalfLine`).

## Main definitions and results

* `ContMDiff.modelWithCornersEuclideanHalfSpace_symm_single`: lifting a nonnegative `C^n`
  real-valued function into `EuclideanHalfSpace k` along the `0`-th coordinate is `C^n`.
* `TauCeti.openHalfLine`, `TauCeti.openHalfLineInclusion`,
  `TauCeti.contMDiff_openHalfLineInclusion`: the open positive half-line `(0, ∞)` and its smooth
  inclusion into `EuclideanHalfSpace 1`.
* `EuclideanHalfSpace.halfLineInwardTranslation`, `TauCeti.contMDiff_halfLineInwardTranslation`:
  the smooth inward translation `x ↦ x + 1` from `EuclideanHalfSpace 1` into `openHalfLine`.
* `TauCeti.halfLineInwardDeformation`, `TauCeti.contMDiff_halfLineInwardDeformation`,
  `EuclideanHalfSpace.halfLineInwardDeformation_zero`,
  `EuclideanHalfSpace.halfLineInwardDeformation_one`: the global smooth inward deformation
  `(t, x) ↦ x + (1 - t)²` from `j ∘ r` to `id`.
* `TauCeti.starConvex_openHalfLine`: `(0, ∞)` is star-convex around `1`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ} [NeZero k] {n : ℕ∞ω} {f : M → ℝ}

/-- Lifting a nonnegative `C^n` real-valued function `f : M → ℝ` into `EuclideanHalfSpace k` via
the `0`-th coordinate embedding `t ↦ (𝓡∂ k).symm (EuclideanSpace.single 0 t)` gives a `C^n` map.
In particular, for `k = 1`, any nonnegative `C^n` real function lifts to a `C^n` map into the
closed half-line `EuclideanHalfSpace 1`. -/
theorem ContMDiff.modelWithCornersEuclideanHalfSpace_symm_single
    (hf : ContMDiff I 𝓘(ℝ) n f) (hf₀ : ∀ x, 0 ≤ f x) :
    ContMDiff I (𝓡∂ k) n fun x ↦ (𝓡∂ k).symm (EuclideanSpace.single (0 : Fin k) (f x)) :=
  (𝓡∂ k).contMDiffOn_symm.comp_contMDiff
    ((((EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp
      (contDiff_single (F' := fun _ : Fin k ↦ ℝ) n (0 : Fin k))).contMDiff).comp hf)
    fun x ↦ by
      rw [range_modelWithCornersEuclideanHalfSpace]
      simpa using hf₀ x

namespace TauCeti

/-- The open positive half-line `(0, ∞)` as an open submanifold of `ℝ`. -/
def openHalfLine : TopologicalSpace.Opens ℝ :=
  ⟨Ioi 0, isOpen_Ioi⟩

/-- A real number belongs to `openHalfLine` if and only if it is positive. -/
@[simp]
theorem mem_openHalfLine_iff {x : ℝ} : x ∈ openHalfLine ↔ 0 < x :=
  Iff.rfl

/-- Inclusion of the open half-line `(0, ∞)` into the closed half-line `EuclideanHalfSpace 1`. -/
def openHalfLineInclusion (y : openHalfLine) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (EuclideanSpace.single 0 y.val)

/-- The `0`-th coordinate of `openHalfLineInclusion y` is `y`. -/
@[simp]
theorem coe_openHalfLineInclusion_apply (y : openHalfLine) :
    (openHalfLineInclusion y).val 0 = y.val := by
  have hy : 0 ≤ (EuclideanSpace.single 0 y.val : EuclideanSpace ℝ (Fin 1)) 0 := by
    simpa using (mem_openHalfLine_iff.mp y.property).le
  rw [openHalfLineInclusion, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy]
  simp

/-- The inclusion `(0, ∞) → [0, ∞)` is smooth with respect to `𝓘(ℝ, ℝ)` and `𝓡∂ 1`. -/
theorem contMDiff_openHalfLineInclusion :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ openHalfLineInclusion :=
  contMDiff_subtypeVal.modelWithCornersEuclideanHalfSpace_symm_single fun y ↦
    (mem_openHalfLine_iff.mp y.property).le

end TauCeti

namespace EuclideanHalfSpace

open TauCeti

/-- Smooth inward translation `r(x) = x + 1` from the closed half-line `[0, ∞)` into its open
interior `(0, ∞)`. -/
def halfLineInwardTranslation (x : EuclideanHalfSpace 1) : openHalfLine :=
  ⟨x.val 0 + 1, mem_openHalfLine_iff.mpr (add_pos_of_nonneg_of_pos x.property zero_lt_one)⟩

/-- The underlying real value of `halfLineInwardTranslation x` is `x.val 0 + 1`. -/
@[simp]
theorem coe_halfLineInwardTranslation (x : EuclideanHalfSpace 1) :
    (x.halfLineInwardTranslation : ℝ) = x.val 0 + 1 :=
  (rfl)

end EuclideanHalfSpace

namespace TauCeti

/-- The inward translation `r(x) = x + 1` is smooth from `EuclideanHalfSpace 1` to `(0, ∞)`. -/
theorem contMDiff_halfLineInwardTranslation :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ EuclideanHalfSpace.halfLineInwardTranslation := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
    (𝓡∂ 1).contMDiff).add contMDiff_const

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` on `ℝ × [0, ∞)`: because `(1 - t)² ≥ 0` for all
`t ∈ ℝ`, it stays in `[0, ∞)` globally in `t`, starts at `j(r(x)) = x + 1` at `t = 0`, and reaches
`x` at `t = 1`. -/
def halfLineInwardDeformation (p : ℝ × EuclideanHalfSpace 1) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (EuclideanSpace.single 0 ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2))

/-- The `0`-th coordinate of `halfLineInwardDeformation (t, x)` is `x + (1 - t)²`. -/
@[simp]
theorem coe_halfLineInwardDeformation_apply (p : ℝ × EuclideanHalfSpace 1) :
    (halfLineInwardDeformation p).val 0 = p.2.val 0 + (1 - p.1) ^ 2 := by
  have hp : 0 ≤ (EuclideanSpace.single 0 ((𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2) :
      EuclideanSpace ℝ (Fin 1)) 0 := by
    have hx : 0 ≤ p.2.val 0 := p.2.property
    have hsq : 0 ≤ (1 - p.1) ^ 2 := sq_nonneg (1 - p.1)
    simpa using add_nonneg hx hsq
  rw [halfLineInwardDeformation, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hp]
  simp

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` preserves the open interior `(0, ∞)` at every
time `t ∈ ℝ`. -/
theorem halfLineInwardDeformation_pos {t : ℝ} {x : EuclideanHalfSpace 1} (hx : 0 < x.val 0) :
    0 < (halfLineInwardDeformation (t, x)).val 0 := by
  rw [coe_halfLineInwardDeformation_apply]
  nlinarith [sq_nonneg (1 - t)]

/-- The inward deformation `Φ(t, x) = x + (1 - t)²` is jointly smooth on `ℝ × [0, ∞)`. -/
theorem contMDiff_halfLineInwardDeformation :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓡∂ 1) ∞ halfLineInwardDeformation := by
  have hcoord : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × EuclideanHalfSpace 1 ↦ (𝓡∂ 1) p.2 0 + (1 - p.1) ^ 2) := by
    have hx : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (𝓡∂ 1) p.2 0) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
        (𝓡∂ 1).contMDiff).comp contMDiff_snd
    have ht : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × EuclideanHalfSpace 1 ↦ (1 - p.1) ^ 2) :=
      ((contDiff_const.sub contDiff_id).pow 2).contMDiff.comp contMDiff_fst
    exact hx.add ht
  exact hcoord.modelWithCornersEuclideanHalfSpace_symm_single fun p ↦
    add_nonneg p.2.property (sq_nonneg (1 - p.1))

end TauCeti

namespace EuclideanHalfSpace

open TauCeti

/-- At `t = 0`, `halfLineInwardDeformation` agrees with `j ∘ r`. -/
@[simp]
theorem halfLineInwardDeformation_zero (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (0, x) = openHalfLineInclusion x.halfLineInwardTranslation := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply, coe_openHalfLineInclusion_apply,
    coe_halfLineInwardTranslation]
  ring

/-- At `t = 1`, `halfLineInwardDeformation` is the identity on `[0, ∞)`. -/
@[simp]
theorem halfLineInwardDeformation_one (x : EuclideanHalfSpace 1) :
    halfLineInwardDeformation (1, x) = x := by
  ext i
  rw [Subsingleton.elim i 0, coe_halfLineInwardDeformation_apply]
  ring

end EuclideanHalfSpace

namespace TauCeti

/-- The open positive half-line `(0, ∞)` is star-convex around `1`. -/
theorem starConvex_openHalfLine : StarConvex ℝ 1 (openHalfLine : Set ℝ) :=
  (convex_Ioi (0 : ℝ)).starConvex (zero_lt_one : (1 : ℝ) ∈ Ioi 0)

end TauCeti
