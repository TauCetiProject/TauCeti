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

/-- The values of a lifted bilinear map are bounded by the norms of the map and its inputs. -/
theorem norm_compHolder₂_apply_le (B : E →L[ℝ] F →L[ℝ] G) (f : HolderSpace α X E)
    (g : HolderSpace α X F) : ‖B.compHolder₂ f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  (B.compHolder₂.le_opNorm₂ f g).trans (by gcongr; exact B.norm_compHolder₂_le)

/-- Pointwise application of a Hölder field of continuous linear maps to a Hölder function is
bounded by the product of their norms. -/
theorem norm_id_compHolder₂_apply_le (f : HolderSpace α X (F →L[ℝ] G)) (g : HolderSpace α X F) :
    ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] G)).compHolder₂ f g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_compHolder₂_apply_le _ f g).trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg f) ContinuousLinearMap.norm_id_le) (norm_nonneg g))

/-- **The product bound with a small factor on the support.** If `f` is `α`-Hölder with constant
`K` and `‖f x‖ ≤ δ` wherever `g x ≠ 0`, then `‖B (f, g)‖ ≤ ‖B‖ (δ ‖g‖ + K ‖g‖_∞)`. The size of `f`
enters only on the support of `g`, and its Hölder constant only against the supremum of `g`.
This is the estimate for freezing a Hölder coefficient at a point near which `g` is supported. -/
theorem norm_compHolder₂_apply_le_of_norm_le (B : E →L[ℝ] F →L[ℝ] G) {f : HolderSpace α X E}
    {g : HolderSpace α X F} {K : ℝ≥0} {δ : ℝ} (hfK : HolderWith K α f)
    (hf : ∀ x, g x ≠ 0 → ‖f x‖ ≤ δ) :
    ‖B.compHolder₂ f g‖ ≤ ‖B‖ * (δ * ‖g‖ + K * ‖g.toBoundedContinuousFunction‖) := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨x₀, hx₀⟩ : ∃ x, g x ≠ 0 := by
    by_contra! h
    exact hg (HolderSpace.ext fun x ↦ by simpa using h x)
  lift δ to ℝ≥0 using (norm_nonneg _).trans (hf x₀ hx₀)
  have hgsup (x : X) : ‖g x‖ ≤ ‖g.toBoundedContinuousFunction‖ := by
    simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x
  have hsup : ‖(B.compHolder₂ f g).toBoundedContinuousFunction‖ ≤
      ‖B‖ * δ * ‖g.toBoundedContinuousFunction‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [HolderSpace.toBoundedContinuousFunction_apply, compHolder₂_apply]
    by_cases hx : g x = 0
    · simp only [hx, map_zero, norm_zero]
      positivity
    exact (B.le_opNorm₂ _ _).trans (by gcongr; exacts [hf x hx, hgsup x])
  -- Off the support of `g` the product vanishes, so only the bound of `f` on it enters.
  have hgH : HolderWith (nnHolderNorm α (g : X → F)) α g := by
    simpa using g.memHolder.holderWith
  have hholder := B.flip.holderWith_comp₂_of_eq_zero (s := {x | g x ≠ 0})
    (Mf := ‖g.toBoundedContinuousFunction‖₊) (Mg := δ) hgH (hfK.holderOnWith _)
    (fun x ↦ by simpa using hgsup x) (fun x hx ↦ hf x hx) (fun x hx ↦ by simpa using hx)
  have hsemi : (nnHolderNorm α ((B.compHolder₂ f g).toBoundedContinuousFunction : X → G) : ℝ) ≤
      ‖B‖ * (‖g.toBoundedContinuousFunction‖ * K + δ * nnHolderNorm α (g : X → F)) := by
    have heq : ((B.compHolder₂ f g).toBoundedContinuousFunction : X → G) =
        fun x ↦ B.flip (g x) (f x) := by
      funext x
      simp
    have h := hholder.nnholderNorm_le
    rw [opNNNorm_flip] at h
    rw [heq]
    calc _ ≤ ((‖B‖₊ * (‖g.toBoundedContinuousFunction‖₊ * K + δ * nnHolderNorm α (g : X → F)) :
          ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 h
      _ = _ := by push_cast; ring
  rw [HolderSpace.norm_def, HolderSpace.norm_def]
  simp only [HolderSpace.coe_toBoundedContinuousFunction] at hsemi ⊢
  nlinarith [norm_nonneg B]

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
