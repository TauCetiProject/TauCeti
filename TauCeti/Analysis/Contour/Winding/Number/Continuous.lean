/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Winding
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Contour.Winding.Number.Reparam

/-!
# Winding numbers of continuous functions along circles

For a function `f : ℂ → ℂ` that is continuous and nowhere zero on the circle of radius `r` about
`z₀`, the loop `θ ↦ f (circleMap z₀ r θ)` winds an integral number of times around the origin.
This file names that integer, `TauCeti.Contour.circleWindingNumber f z₀ r`, through the
topological winding number `ContinuousMap.windingNumber` of nowhere-zero functions on
`UnitAddCircle`. No differentiability is required, so the winding number is defined for the
boundary values of merely continuous maps of a disc. By convention it is `0` when `f` is
discontinuous or vanishes somewhere on the circle.

When the loop is `C¹`, it is the contour winding number of
`TauCeti.Analysis.Contour.Winding.Number.Basic`
(`TauCeti.Contour.coe_circleWindingNumber_eq_windingNumber`). It depends only on the values of
`f` on the circle and is stable under perturbations: it is unchanged by a perturbation smaller
than `|f|` (Rouché, `TauCeti.Contour.circleWindingNumber_eq_of_norm_sub_lt`), and therefore along
every continuous family of functions nowhere zero on the circle, indexed by a preconnected set
(`TauCeti.Contour.circleWindingNumber_eq_of_continuousOn_uncurry`), in particular along
straight-line homotopies
(`TauCeti.Contour.circleWindingNumber_comp_eq_of_forall_mem_segment`). For `f` continuous and
nowhere zero on a closed annulus `r₁ ≤ |z - z₀| ≤ r₂`, the two boundary circles have the same
winding number (`TauCeti.Contour.circleWindingNumber_eq_of_annulus`), and if `f` is continuous and
nowhere zero on a closed disc, its boundary circle has winding number zero
(`TauCeti.Contour.circleWindingNumber_eq_zero`).

## Main definitions

* `TauCeti.Contour.circleWindingNumber f z₀ r`: the winding number of `f` around `0` along the
  circle of radius `r` about `z₀`.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4.
-/

public section

noncomputable section

open Complex Metric Set Filter
open scoped Topology Real

namespace TauCeti.Contour

variable {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}

/-- The points `z₀ - r u`, `u` on the unit circle, lie on the circle of radius `|r|` about `z₀`. -/
private theorem sub_ofReal_mul_mem_sphere (z₀ : ℂ) (r : ℝ) (u : Circle) :
    z₀ - r * (u : ℂ) ∈ sphere z₀ |r| := by
  simp [mem_sphere_iff_norm]

/-- The loop `t ↦ f (z₀ - r e^{2πit})` on `UnitAddCircle`. It runs once counterclockwise around
the circle of radius `r` about `z₀`, starting at the angle `-π`. -/
private def circleLoop (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (hf : ContinuousOn f (sphere z₀ |r|)) :
    C(UnitAddCircle, ℂ) where
  toFun x := f (z₀ - r * (AddCircle.toCircle x : ℂ))
  continuous_toFun := hf.comp_continuous
    (continuous_const.sub (continuous_const.mul
      (continuous_subtype_val.comp AddCircle.continuous_toCircle)))
    fun _ ↦ sub_ofReal_mul_mem_sphere z₀ r _

private theorem circleLoop_apply (hf : ContinuousOn f (sphere z₀ |r|)) (x : UnitAddCircle) :
    circleLoop f z₀ r hf x = f (z₀ - r * (AddCircle.toCircle x : ℂ)) :=
  (rfl)

/-- On a real parameter `t`, the loop is `f ∘ circleMap z₀ r` at the angle `2πt - π`. -/
private theorem circleLoop_coe (hf : ContinuousOn f (sphere z₀ |r|)) (t : ℝ) :
    circleLoop f z₀ r hf t = f (circleMap z₀ r (2 * π * t + -π)) := by
  rw [circleLoop_apply, AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
  congr 1
  rw [show ((2 * π * t + -π : ℝ) : ℂ) * I = ((2 * π / 1 * t : ℝ) : ℂ) * I + -(π * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

/-- The **winding number** of `f : ℂ → ℂ` around `0` along the circle of radius `r` about `z₀`,
traversed once counterclockwise: the degree of the loop `θ ↦ f (circleMap z₀ r θ)`. It is defined
when `f` is continuous and nowhere zero on that circle, and is `0` by convention otherwise. -/
def circleWindingNumber (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) : ℤ :=
  haveI := Classical.propDecidable
  if h : ContinuousOn f (sphere z₀ |r|) ∧ ∀ z ∈ sphere z₀ |r|, f z ≠ 0 then
    (circleLoop f z₀ r h.1).windingNumber fun _ ↦ h.2 _ (sub_ofReal_mul_mem_sphere z₀ r _)
  else 0

private theorem circleWindingNumber_eq_windingNumber_circleLoop
    (hf : ContinuousOn f (sphere z₀ |r|)) (hne : ∀ z ∈ sphere z₀ |r|, f z ≠ 0) :
    circleWindingNumber f z₀ r = (circleLoop f z₀ r hf).windingNumber
      fun _ ↦ hne _ (sub_ofReal_mul_mem_sphere z₀ r _) :=
  dite_eq_left ⟨hf, hne⟩

/-- A function vanishing somewhere on the circle has winding number `0` by convention. -/
theorem circleWindingNumber_eq_zero_of_eq_zero {z : ℂ} (hz : z ∈ sphere z₀ |r|) (hfz : f z = 0) :
    circleWindingNumber f z₀ r = 0 :=
  dite_eq_right fun h ↦ h.2 z hz hfz

/-- The winding number only depends on the values on the circle. -/
theorem circleWindingNumber_congr (h : EqOn f g (sphere z₀ |r|)) :
    circleWindingNumber f z₀ r = circleWindingNumber g z₀ r := by
  by_cases hfg : ContinuousOn f (sphere z₀ |r|) ∧ ∀ z ∈ sphere z₀ |r|, f z ≠ 0
  · have hg : ContinuousOn g (sphere z₀ |r|) ∧ ∀ z ∈ sphere z₀ |r|, g z ≠ 0 :=
      ⟨hfg.1.congr h.symm, fun z hz ↦ h hz ▸ hfg.2 z hz⟩
    rw [circleWindingNumber_eq_windingNumber_circleLoop hfg.1 hfg.2,
      circleWindingNumber_eq_windingNumber_circleLoop hg.1 hg.2]
    exact ContinuousMap.windingNumber_congr _ _ fun x ↦ h (sub_ofReal_mul_mem_sphere z₀ r _)
  · have hg : ¬(ContinuousOn g (sphere z₀ |r|) ∧ ∀ z ∈ sphere z₀ |r|, g z ≠ 0) :=
      fun hg ↦ hfg ⟨hg.1.congr h, fun z hz ↦ (h hz).symm ▸ hg.2 z hz⟩
    rw [circleWindingNumber, circleWindingNumber, dite_eq_right hfg, dite_eq_right hg]

/-- A constant function has winding number `0`. -/
@[simp]
theorem circleWindingNumber_const (c : ℂ) : circleWindingNumber (fun _ ↦ c) z₀ r = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact circleWindingNumber_eq_zero_of_eq_zero
      (z := z₀ - r * ((1 : Circle) : ℂ)) (sub_ofReal_mul_mem_sphere z₀ r 1) rfl
  rw [circleWindingNumber_eq_windingNumber_circleLoop continuousOn_const fun _ _ ↦ hc]
  exact (ContinuousMap.windingNumber_congr (g := ContinuousMap.const _ c) _ (fun _ ↦ hc)
    fun _ ↦ rfl).trans (ContinuousMap.windingNumber_const hc)

/-- **Rouché's theorem for winding numbers.** If `f` and `g` are continuous on the circle of
radius `r` about `z₀`, `f` has no zero there and `|g - f| < |f|` on the circle, then `f` and `g`
have the same winding number. -/
theorem circleWindingNumber_eq_of_norm_sub_lt (hf : ContinuousOn f (sphere z₀ |r|))
    (hg : ContinuousOn g (sphere z₀ |r|)) (hne : ∀ z ∈ sphere z₀ |r|, f z ≠ 0)
    (hfg : ∀ z ∈ sphere z₀ |r|, ‖g z - f z‖ < ‖f z‖) :
    circleWindingNumber g z₀ r = circleWindingNumber f z₀ r := by
  have hgne (z : ℂ) (hz : z ∈ sphere z₀ |r|) : g z ≠ 0 := fun h ↦ by
    simpa [h] using hfg z hz
  rw [circleWindingNumber_eq_windingNumber_circleLoop hf hne,
    circleWindingNumber_eq_windingNumber_circleLoop hg hgne]
  exact ContinuousMap.windingNumber_eq_of_norm_sub_lt _
    fun x ↦ hfg _ (sub_ofReal_mul_mem_sphere z₀ r _)

/-- **Homotopy invariance of the winding number.** Let `F p`, for `p` in a preconnected set `S` of
parameters, be functions with no zero on the circle of radius `r` about `z₀`, such that `F p z`
depends jointly continuously on `p ∈ S` and on `z` in the circle. Then all the functions `F p`
have the same winding number along the circle. -/
theorem circleWindingNumber_eq_of_continuousOn_uncurry {P : Type*} [TopologicalSpace P]
    {S : Set P} (hS : IsPreconnected S) {F : P → ℂ → ℂ}
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ sphere z₀ |r|))
    (hne : ∀ p ∈ S, ∀ z ∈ sphere z₀ |r|, F p z ≠ 0) {p q : P} (hp : p ∈ S) (hq : q ∈ S) :
    circleWindingNumber (F p) z₀ r = circleWindingNumber (F q) z₀ r := by
  have hcont (p : P) (hp : p ∈ S) : ContinuousOn (F p) (sphere z₀ |r|) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn fun z hz ↦ ⟨hp, hz⟩
  -- Near `q`, the functions `F p` stay closer to `F q` than `|F q|`, so Rouché's theorem makes the
  -- winding number locally constant in the parameter.
  have hloc (q : P) (hq : q ∈ S) :
      ∀ᶠ p in 𝓝[S] q, circleWindingNumber (F p) z₀ r = circleWindingNumber (F q) z₀ r := by
    obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere z₀ |r|).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 (abs_nonneg r)) (continuous_norm.comp_continuousOn
        (hcont q hq))
    obtain ⟨v, hv, hclose⟩ := (isCompact_sphere z₀ |r|).mem_uniformity_of_prod hF hq
      (Metric.dist_mem_uniformity (norm_pos_iff.2 (hne q hq z₁ hz₁)))
    filter_upwards [hv, self_mem_nhdsWithin] with p hpv hpS
    refine circleWindingNumber_eq_of_norm_sub_lt (hcont q hq) (hcont p hpS) (hne q hq)
      fun z hz ↦ ?_
    rw [← dist_eq_norm]
    exact (hclose p hpv z hz).trans_le (hmin hz)
  -- A locally constant function on a preconnected space is constant.
  have := isPreconnected_iff_preconnectedSpace.1 hS
  have hconst : IsLocallyConstant fun x : S ↦ circleWindingNumber (F x) z₀ r :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦
      (eventually_nhds_subtype_iff S x _).2 (hloc x x.2)
  exact hconst.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- **Straight-line homotopy of the winding number.** Let `σ` and `τ` be continuous on the circle of
radius `r` about `z₀`, with values in a real normed space, and let `g` be continuous with no zero
on any segment from `σ z` to `τ z`, `z` on the circle. Then `g ∘ σ` and `g ∘ τ` have the same
winding number along the circle. -/
theorem circleWindingNumber_comp_eq_of_forall_mem_segment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → ℂ} {σ τ : ℂ → E} (hg : Continuous g)
    (hσ : ContinuousOn σ (sphere z₀ |r|)) (hτ : ContinuousOn τ (sphere z₀ |r|))
    (hne : ∀ z ∈ sphere z₀ |r|, ∀ y ∈ segment ℝ (σ z) (τ z), g y ≠ 0) :
    circleWindingNumber (g ∘ σ) z₀ r = circleWindingNumber (g ∘ τ) z₀ r := by
  have hsnd : MapsTo Prod.snd (Icc (0 : ℝ) 1 ×ˢ sphere z₀ |r|) (sphere z₀ |r|) :=
    fun _ hp ↦ hp.2
  have h := circleWindingNumber_eq_of_continuousOn_uncurry (z₀ := z₀) (r := r)
    (F := fun s z ↦ g (σ z + s • (τ z - σ z))) isPreconnected_Icc
    (hg.comp_continuousOn ((hσ.comp continuousOn_snd hsnd).add
      (continuousOn_fst.smul ((hτ.comp continuousOn_snd hsnd).sub
        (hσ.comp continuousOn_snd hsnd)))))
    (fun s hs z hz ↦ hne z hz _ (segment_eq_image' ℝ (σ z) (τ z) ▸ mem_image_of_mem _ hs))
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel, Function.comp_def] using h

/-- **Concentric circles through an annulus wind equally often.** If `f` is continuous and nowhere
zero on the closed annulus `r₁ ≤ |z - z₀| ≤ r₂`, with `0 ≤ r₁ ≤ r₂`, then the two boundary circles
have the same winding number. -/
theorem circleWindingNumber_eq_of_annulus {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂)
    (hf : ContinuousOn f (closedBall z₀ r₂ \ ball z₀ r₁))
    (hne : ∀ z ∈ closedBall z₀ r₂ \ ball z₀ r₁, f z ≠ 0) :
    circleWindingNumber f z₀ r₁ = circleWindingNumber f z₀ r₂ := by
  have hsub {s : ℝ} (hs : s ∈ Icc r₁ r₂) : sphere z₀ |s| ⊆ closedBall z₀ r₂ \ ball z₀ r₁ :=
    fun z hz ↦ by
      rw [abs_of_nonneg (hr₁.trans hs.1)] at hz
      simp only [Set.mem_sdiff, mem_closedBall, mem_ball, not_lt, mem_sphere.1 hz]
      exact ⟨hs.2, hs.1⟩
  have hmem₁ : r₁ ∈ Icc r₁ r₂ := left_mem_Icc.2 hr
  have hmem₂ : r₂ ∈ Icc r₁ r₂ := right_mem_Icc.2 hr
  rw [circleWindingNumber_eq_windingNumber_circleLoop (hf.mono (hsub hmem₁))
      fun z hz ↦ hne z (hsub hmem₁ hz),
    circleWindingNumber_eq_windingNumber_circleLoop (hf.mono (hsub hmem₂))
      fun z hz ↦ hne z (hsub hmem₂ hz)]
  -- Interpolate linearly between the two radii.
  have hrad (t : unitInterval) : r₁ + t * (r₂ - r₁) ∈ Icc r₁ r₂ :=
    ⟨le_add_of_nonneg_right (mul_nonneg t.2.1 (sub_nonneg.2 hr)), by
      nlinarith [t.2.2, sub_nonneg.2 hr]⟩
  have hmaps (p : unitInterval × UnitAddCircle) :
      z₀ - ((r₁ + p.1 * (r₂ - r₁) : ℝ) : ℂ) * (AddCircle.toCircle p.2 : ℂ) ∈
        closedBall z₀ r₂ \ ball z₀ r₁ :=
    hsub (hrad p.1) (sub_ofReal_mul_mem_sphere z₀ _ _)
  let H : C(unitInterval × UnitAddCircle, ℂ) :=
    { toFun p := f (z₀ - ((r₁ + p.1 * (r₂ - r₁) : ℝ) : ℂ) * (AddCircle.toCircle p.2 : ℂ))
      continuous_toFun := hf.comp_continuous (by
        refine continuous_const.sub (Continuous.mul ?_
          (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp continuous_snd)))
        exact continuous_ofReal.comp (continuous_const.add
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const))) hmaps }
  exact ContinuousMap.windingNumber_eq_of_homotopy _ _ H (fun p ↦ hne _ (hmaps p))
    (fun x ↦ by simp [H, circleLoop_apply]) (fun x ↦ by simp [H, circleLoop_apply])

/-- **The boundary of a disc on which `f` has no zero does not wind around `0`.** If `f` is
continuous and nowhere zero on the closed disc of radius `r ≥ 0` about `z₀`, its winding number
along the boundary circle is `0`. -/
theorem circleWindingNumber_eq_zero (hr : 0 ≤ r) (hf : ContinuousOn f (closedBall z₀ r))
    (hne : ∀ z ∈ closedBall z₀ r, f z ≠ 0) : circleWindingNumber f z₀ r = 0 := by
  rw [← sdiff_empty (s := closedBall z₀ r), ← ball_zero (x := z₀)] at hf hne
  rw [← circleWindingNumber_eq_of_annulus le_rfl hr hf hne,
    circleWindingNumber_congr (g := fun _ ↦ f z₀) fun z hz ↦ by
      rw [abs_zero, sphere_zero, mem_singleton_iff] at hz
      rw [hz]]
  exact circleWindingNumber_const _

/-- **Comparison with the contour winding number.** If `f` is continuous and nowhere zero on the
circle of radius `r` about `z₀` and the loop `f ∘ circleMap z₀ r` is `C¹`, then its winding number
is the contour winding number of that loop, traversed once from the angle `-π`. -/
theorem coe_circleWindingNumber_eq_windingNumber (hf : ContinuousOn f (sphere z₀ |r|))
    (hne : ∀ z ∈ sphere z₀ |r|, f z ≠ 0) (hγ : ContDiff ℝ 1 (f ∘ circleMap z₀ r)) :
    (circleWindingNumber f z₀ r : ℂ) = windingNumber (f ∘ circleMap z₀ r) (-π) π 0 := by
  have hloop : (fun t : ℝ ↦ circleLoop f z₀ r hf t) =
      (f ∘ circleMap z₀ r) ∘ fun t ↦ 2 * π * t + -π :=
    funext fun t ↦ circleLoop_coe hf t
  have hC1 : IsPiecewiseC1On (fun t : ℝ ↦ circleLoop f z₀ r hf t) 0 1 := by
    rw [hloop]
    exact IsPiecewiseC1On.of_contDiffOn
      (hγ.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).contDiffOn
  rw [circleWindingNumber_eq_windingNumber_circleLoop hf hne]
  refine (ContinuousMap.coe_windingNumber_eq_contour_windingNumber_unitAddCircle _ _ hC1).trans ?_
  rw [hloop, windingNumber_comp_mul_add (fun u _ ↦ (hγ.differentiable one_ne_zero).differentiableAt)
      (hγ.continuous_deriv le_rfl).continuousOn
      fun u _ ↦ hne _ (circleMap_mem_sphere' z₀ r u)]
  congr 1 <;> ring

end TauCeti.Contour
