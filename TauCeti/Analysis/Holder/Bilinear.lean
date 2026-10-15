/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Normed.Operator.Holder
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous bilinear operations on Hölder spaces

A continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G` acts pointwise on bounded Hölder functions.
The resulting bilinear map has norm at most `‖B‖`, and exactly `‖B‖` on a nonempty domain.
This supplies multiplication and scalar multiplication in Hölder spaces with the usual
supremum-plus-Hölder norm, without replacing the existing space or its norm.

The construction generalizes the scalar-multiplication operator `boundedHolderSpaceSmu` in
[DifferentialGeometry, Holder/Bilinear.lean](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/DifferentialGeometry/Analysis/Schauder/Holder/Bilinear.lean).
Keeping the supremum and Hölder terms separate improves its factor `3` to `1`.
-/

public section

noncomputable section

open scoped NNReal BoundedContinuousFunction
open TauCeti

namespace ContinuousLinearMap

variable {X E F G : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ≥0}

private def holderBilinear (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) : HolderSpace α X G :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ B (f x) (g x))
      ((B.continuous.comp f.continuous).clm_apply g.continuous)
      (‖B‖ * ‖f.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖)
      (fun x ↦ (B.le_opNorm₂ _ _).trans (by
        gcongr
        · simpa using f.toBoundedContinuousFunction.norm_coe_le_norm x
        · simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x)))
    (by
      simpa using (B.holderWith_comp₂
        (Mf := ‖f.toBoundedContinuousFunction‖₊) (Mg := ‖g.toBoundedContinuousFunction‖₊)
        f.memHolder.holderWith g.memHolder.holderWith
        f.toBoundedContinuousFunction.norm_coe_le_norm
        g.toBoundedContinuousFunction.norm_coe_le_norm).memHolder)

private theorem holderBilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) (x : X) :
    holderBilinear B f g x = B (f x) (g x) := by
  simp [holderBilinear]

private theorem norm_holderBilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) :
    ‖holderBilinear B f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  have hsup : ‖(holderBilinear B f g).toBoundedContinuousFunction‖ ≤
      ‖B‖ * ‖f.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    rw [HolderSpace.toBoundedContinuousFunction_apply, holderBilinear_apply]
    exact (B.le_opNorm₂ _ _).trans (by
      gcongr
      · simpa using f.toBoundedContinuousFunction.norm_coe_le_norm x
      · simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x)
  have hholder := B.holderWith_comp₂
    (Mf := ‖f.toBoundedContinuousFunction‖₊) (Mg := ‖g.toBoundedContinuousFunction‖₊)
    f.memHolder.holderWith g.memHolder.holderWith
    f.toBoundedContinuousFunction.norm_coe_le_norm
    g.toBoundedContinuousFunction.norm_coe_le_norm
  have hsemi : (nnHolderNorm α
      ((holderBilinear B f g).toBoundedContinuousFunction : X → G) : ℝ) ≤
      ‖B‖ * (‖f.toBoundedContinuousFunction‖ * nnHolderNorm α (g : X → F) +
        ‖g.toBoundedContinuousFunction‖ * nnHolderNorm α (f : X → E)) := by
    have heq : ((holderBilinear B f g).toBoundedContinuousFunction : X → G) =
        fun x ↦ B (f x) (g x) := by
      funext x
      rw [HolderSpace.toBoundedContinuousFunction_apply, holderBilinear_apply]
    rw [heq]
    exact_mod_cast (by simpa using hholder.nnholderNorm_le :
      nnHolderNorm α (fun x ↦ B (f x) (g x)) ≤
        ‖B‖₊ * (‖f.toBoundedContinuousFunction‖₊ * nnHolderNorm α (g : X → F) +
          ‖g.toBoundedContinuousFunction‖₊ * nnHolderNorm α (f : X → E)))
  have htotal := add_le_add hsup hsemi
  simp only [HolderSpace.coe_toBoundedContinuousFunction] at htotal
  simp only [HolderSpace.norm_def, HolderSpace.coe_toBoundedContinuousFunction]
  nlinarith [mul_nonneg (norm_nonneg B)
    (mul_nonneg (NNReal.coe_nonneg (nnHolderNorm α (f : X → E)))
      (NNReal.coe_nonneg (nnHolderNorm α (g : X → F))))]

private def holderBilinearLinear (B : E →L[ℝ] F →L[ℝ] G) :
    HolderSpace α X E →ₗ[ℝ] HolderSpace α X F →ₗ[ℝ] HolderSpace α X G :=
  LinearMap.mk₂ ℝ (holderBilinear B)
    (fun f₁ f₂ g ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])
    (fun c f g ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])
    (fun f g₁ g₂ ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])
    (fun c f g ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])

/-- Pointwise application of a continuous bilinear map as a continuous bilinear map of
bounded Hölder spaces. -/
def compHolder₂ (B : E →L[ℝ] F →L[ℝ] G) :
    HolderSpace α X E →L[ℝ] HolderSpace α X F →L[ℝ] HolderSpace α X G :=
  (holderBilinearLinear B).mkContinuous₂ ‖B‖ (norm_holderBilinear_le B)

@[simp]
theorem compHolder₂_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) (x : X) :
    B.compHolder₂ f g x = B (f x) (g x) := by
  simp [compHolder₂, holderBilinearLinear, holderBilinear_apply]

/-- Pointwise lifting to Hölder functions does not increase a bilinear map's operator norm. -/
theorem norm_compHolder₂_le (B : E →L[ℝ] F →L[ℝ] G) :
    ‖B.compHolder₂ (α := α) (X := X)‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

/-- On a nonempty domain, pointwise lifting preserves the bilinear operator norm. -/
@[simp]
theorem norm_compHolder₂ [Nonempty X] (B : E →L[ℝ] F →L[ℝ] G) :
    ‖B.compHolder₂ (α := α) (X := X)‖ = ‖B‖ := by
  refine le_antisymm B.norm_compHolder₂_le
    (B.opNorm_le_bound₂ (norm_nonneg (B.compHolder₂ (α := α) (X := X))) ?_)
  intro e f
  obtain ⟨x⟩ := ‹Nonempty X›
  calc
    ‖B e f‖ = ‖B.compHolder₂ (HolderSpace.const (α := α) (X := X) e)
        (HolderSpace.const f) x‖ := by
      simp
    _ ≤ ‖B.compHolder₂ (HolderSpace.const (α := α) e) (HolderSpace.const f)‖ := by
      let h := B.compHolder₂ (HolderSpace.const (α := α) (X := X) e) (HolderSpace.const f)
      simpa only [HolderSpace.toBoundedContinuousFunction_apply] using
        (h.toBoundedContinuousFunction.norm_coe_le_norm x).trans
          h.norm_toBoundedContinuousFunction_le
    _ ≤ _ := by
      simpa only [HolderSpace.norm_const] using (B.compHolder₂ (α := α) (X := X)).le_opNorm₂
        (HolderSpace.const e) (HolderSpace.const f)

@[simp]
theorem compHolder₂_flip (B : E →L[ℝ] F →L[ℝ] G) :
    B.flip.compHolder₂ (α := α) (X := X) = B.compHolder₂.flip := by
  ext f g x
  simp

@[simp]
theorem compHolder₂_const (B : E →L[ℝ] F →L[ℝ] G) (e : E) (f : F) :
    B.compHolder₂ (HolderSpace.const (α := α) (X := X) e) (HolderSpace.const f) =
      HolderSpace.const (B e f) := by
  ext x
  simp

end ContinuousLinearMap
