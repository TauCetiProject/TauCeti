/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.ContMDiff.Curve
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Gluing, reparametrization and Green's formula for integrals over rectangles

This file develops the integral
`∫_u φ = ∫_{a.1}^{b.1} ∫_{a.2}^{b.2} φ_{u(s, t)}(∂_s u, ∂_t u) dt ds`
of a two-form `φ` over a map `u : ℝ × ℝ → M` (`TauCeti.rectangleIntegral`) along the first
coordinate `s`, the coordinate along which a cylinder `u` joins its boundary loops `u(a.1, ·)` and
`u(b.1, ·)`. For a continuous form and a `C¹` map:

* the integral is additive under subdivision of `[a.1, b.1]`
  (`TauCeti.rectangleIntegral_add_adjacent_fst`);
* it is invariant under a `C¹` change `σ` of the first coordinate, between the image endpoints
  (`TauCeti.rectangleIntegral_comp_prodMap`), and reversing the first coordinate changes its sign
  (`TauCeti.rectangleIntegral_comp_prodMap_one_sub`).

Two maps `u₁ u₂ : ℝ × ℝ → M` with `u₁(1, ·) = u₂(0, ·)` are glued into their concatenation
`TauCeti.rectangleTrans u₁ u₂`, the curve concatenation `TauCeti.curveConcat` in the first
coordinate of `u₁` and `u₂` reparametrized by a smooth transition function. It runs through `u₁`
for `s ∈ [0, 1/3]`, rests at the common edge for `s ∈ [1/3, 2/3]` and runs through `u₂` for
`s ∈ [2/3, 1]`, so it is as smooth as `u₁` and `u₂` (`TauCeti.contMDiff_rectangleTrans`). It
is periodic in `t` when `u₁` and `u₂` are, and its integral is the sum of the integrals of `u₁` and
`u₂` (`TauCeti.rectangleIntegral_rectangleTrans`). This is how a cap of a loop is glued to a
cylinder ending at the loop, and how two caps of the same loop are glued into a sphere.

Finally, **Green's formula** (`TauCeti.rectangleIntegral_mextDeriv`): the integral of an exact
two-form `dα` over a `C²` map `u` is the signed sum of the line integrals of `α` along the four
edges of the rectangle. In particular the integral of `dα` over a cylinder is the difference of the
line integrals of `α` along its two boundary loops.

## Main definitions

* `TauCeti.rectangleTrans u₁ u₂`: the concatenation of two maps of the plane along the first
  coordinate.

## Main results

* `TauCeti.rectangleIntegral_add_adjacent_fst`: additivity in the first coordinate.
* `TauCeti.rectangleIntegral_comp_prodMap`: reparametrization in the first coordinate.
* `TauCeti.rectangleIntegral_rectangleTrans`: the integral over a concatenation.
* `TauCeti.rectangleIntegral_mextDeriv`: Green's formula for an exact form.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §3
  (Stokes' theorem).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (gluing cylinders and caps of loops).
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Interval Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Additivity and reparametrization in the first coordinate -/

section Continuous

variable [IsManifold I 1 M]

/-- The inner integral of a rectangle integral of a continuous form over a `C¹` map is a
continuous function of the first coordinate. -/
theorem continuous_integral_mpullback {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a₂ b₂ : ℝ) :
    Continuous fun s ↦ ∫ t in a₂..b₂, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)] :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    ((hφ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]).congr fun _ ↦ rfl) a₂ b₂

/-- **Additivity in the first coordinate.** For a continuous form and a `C¹` map, the integral
over `[a.1, b.1] × [a.2, b.2]` is the sum of the integrals over `[a.1, c] × [a.2, b.2]` and
`[c, b.1] × [a.2, b.2]`. -/
theorem rectangleIntegral_add_adjacent_fst {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a b : ℝ × ℝ) (c : ℝ) :
    rectangleIntegral φ u a (c, b.2) + rectangleIntegral φ u (c, a.2) b =
      rectangleIntegral φ u a b := by
  have h := continuous_integral_mpullback hφ hu a.2 b.2
  simp only [rectangleIntegral_def]
  exact intervalIntegral.integral_add_adjacent_intervals (h.intervalIntegrable (μ := volume) _ _)
    (h.intervalIntegrable _ _)

/-- **Reparametrization in the first coordinate.** For a continuous form, a `C¹` map `u` and a
`C¹` change `σ` of the first coordinate, the integral over `u ∘ (σ × id)` is the integral over `u`
between the image endpoints. The change of coordinate need not be monotone. -/
theorem rectangleIntegral_comp_prodMap {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {σ σ' : ℝ → ℝ} {a b : ℝ × ℝ}
    (hσ : ∀ s ∈ [[a.1, b.1]], HasDerivAt σ (σ' s) s) (hσ' : ContinuousOn σ' [[a.1, b.1]]) :
    rectangleIntegral φ (u ∘ Prod.map σ id) a b =
      rectangleIntegral φ u (σ a.1, a.2) (σ b.1, b.2) := by
  -- Pointwise, the pulled-back integrand is the integrand at `(σ s, t)` scaled by `σ' s`.
  have key (s : ℝ) (hs : s ∈ [[a.1, b.1]]) (t : ℝ) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ Prod.map σ id) φ (s, t) ![(1, 0), (0, 1)] =
        σ' s • mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (σ s, t) ![(1, 0), (0, 1)] := by
    have hL : HasFDerivAt (Prod.map σ id)
        ((σ' s • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) (s, t) :=
      ((hσ s hs).comp_hasFDerivAt (s, t) hasFDerivAt_fst).prodMk hasFDerivAt_snd
    have h := (mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (σ s, t)).map_update_smul
      ![((1 : ℝ), (0 : ℝ)), (0, 1)] 0 (σ' s) (1, 0)
    -- The derivative of `σ × id` scales the first coordinate vector by `σ' s`.
    have hv : (((σ' s • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) :
        ℝ × ℝ →L[ℝ] ℝ × ℝ) ∘ ![(1, 0), (0, 1)]) =
        Function.update ![((1 : ℝ), (0 : ℝ)), (0, 1)] 0 (σ' s • ((1 : ℝ), (0 : ℝ))) := by
      funext i
      fin_cases i <;> simp
    rw [mpullback_comp_apply_of_hasFDerivAt hL ((hu _).mdifferentiableAt one_ne_zero)]
    -- Mathlib identifies the tangent spaces of the model space `ℝ × ℝ` definitionally with
    -- `ℝ × ℝ`, so the vector identity `hv` applies to tangent vectors.
    refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans
      (((congrArg (mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (σ s, t)) hv).trans h).trans ?_)
    congr 2
    funext i
    fin_cases i <;> rfl
  rw [rectangleIntegral_def, rectangleIntegral_def]
  calc (∫ s in a.1..b.1, ∫ t in a.2..b.2,
          mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ Prod.map σ id) φ (s, t) ![(1, 0), (0, 1)])
      = ∫ s in a.1..b.1, σ' s • (fun r ↦ ∫ t in a.2..b.2,
          mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (r, t) ![(1, 0), (0, 1)]) (σ s) := by
        refine intervalIntegral.integral_congr fun s hs ↦ ?_
        simp only [key s hs, intervalIntegral.integral_smul]
    _ = _ := intervalIntegral.integral_deriv_smul_comp hσ hσ'
        (continuous_integral_mpullback hφ hu a.2 b.2)

/-- Reversing the first coordinate changes the sign of the integral. -/
theorem rectangleIntegral_comp_prodMap_one_sub {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (a₂ b₂ : ℝ) :
    rectangleIntegral φ (u ∘ Prod.map (fun s ↦ 1 - s) id) (0, a₂) (1, b₂) =
      -rectangleIntegral φ u (0, a₂) (1, b₂) := by
  rw [rectangleIntegral_comp_prodMap hφ hu (σ' := fun _ ↦ -1)
    (fun s _ ↦ by simpa using (hasDerivAt_id s).const_sub 1) continuousOn_const]
  simpa using rectangleIntegral_symm_fst φ u 0 a₂ 1 b₂

end Continuous

/-! ### Concatenation along the first coordinate -/

/-- The concatenation of two maps `u₁ u₂ : ℝ × ℝ → M` along the first coordinate: for each `t`,
the concatenation `TauCeti.curveConcat` of the curves `s ↦ u₁ (β s, t)` and `s ↦ u₂ (β s, t)`,
where `β = Real.smoothTransition` rests at `0` before time `0` and at `1` after time `1`. On
`[0, 1]` it runs through `u₁` for `s ∈ [0, 1/3]` and through `u₂` for `s ∈ [2/3, 1]`. When
`u₁ (1, ·) = u₂ (0, ·)` it rests at this common edge for `s ∈ [1/3, 2/3]`, so it is as smooth as
`u₁` and `u₂`. It starts at `u₁ (0, ·)` and ends at `u₂ (1, ·)`. -/
def rectangleTrans (u₁ u₂ : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  curveConcat (fun s ↦ u₁ (Real.smoothTransition s, z.2))
    (fun s ↦ u₂ (Real.smoothTransition s, z.2)) z.1

omit [TopologicalSpace M] in
/-- The concatenation starts at the initial edge of the first map. -/
@[simp]
theorem rectangleTrans_apply_zero (u₁ u₂ : ℝ × ℝ → M) (t : ℝ) :
    rectangleTrans u₁ u₂ (0, t) = u₁ (0, t) := by
  simp [rectangleTrans]

omit [TopologicalSpace M] in
/-- The concatenation ends at the final edge of the second map. -/
@[simp]
theorem rectangleTrans_apply_one (u₁ u₂ : ℝ × ℝ → M) (t : ℝ) :
    rectangleTrans u₁ u₂ (1, t) = u₂ (1, t) := by
  rw [rectangleTrans, curveConcat_of_lt (by norm_num)]
  norm_num

omit [TopologicalSpace M] in
/-- The concatenation of two maps that are periodic in the second coordinate is periodic. -/
theorem rectangleTrans_apply_add_snd {u₁ u₂ : ℝ × ℝ → M} {T : ℝ}
    (h₁ : ∀ z : ℝ × ℝ, u₁ (z.1, z.2 + T) = u₁ z) (h₂ : ∀ z : ℝ × ℝ, u₂ (z.1, z.2 + T) = u₂ z)
    (z : ℝ × ℝ) : rectangleTrans u₁ u₂ (z.1, z.2 + T) = rectangleTrans u₁ u₂ z := by
  simp only [rectangleTrans, h₁ (_, z.2), h₂ (_, z.2)]

omit [TopologicalSpace M] in
/-- Below `s = 2/3` the concatenation is a reparametrization of the first map. -/
theorem rectangleTrans_eq_left {u₁ u₂ : ℝ × ℝ → M} (h : ∀ t, u₁ (1, t) = u₂ (0, t))
    {z : ℝ × ℝ} (hz : z.1 < 2 / 3) :
    rectangleTrans u₁ u₂ z =
      (u₁ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s)) id) z := by
  rw [rectangleTrans, eqOn_curveConcat_left (y := u₁ (1, z.2))
    (fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le hr])
    (fun r hr ↦ by rw [Real.smoothTransition.zero_of_nonpos hr, h]) hz]
  rfl

omit [TopologicalSpace M] in
/-- Above `s = 1/3` the concatenation is a reparametrization of the second map. -/
theorem rectangleTrans_eq_right {u₁ u₂ : ℝ × ℝ → M} (h : ∀ t, u₁ (1, t) = u₂ (0, t))
    {z : ℝ × ℝ} (hz : 1 / 3 < z.1) :
    rectangleTrans u₁ u₂ z =
      (u₂ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s - 2)) id) z := by
  rw [rectangleTrans, eqOn_curveConcat_right (y := u₁ (1, z.2))
    (fun r hr ↦ by rw [Real.smoothTransition.one_of_one_le hr])
    (fun r hr ↦ by rw [Real.smoothTransition.zero_of_nonpos hr, h]) hz]
  rfl

/-- The concatenation of two `C^n` maps sharing an edge is `C^n`. -/
theorem contMDiff_rectangleTrans {n : ℕ∞} {u₁ u₂ : ℝ × ℝ → M}
    (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₁) (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₂)
    (h : ∀ t, u₁ (1, t) = u₂ (0, t)) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (rectangleTrans u₁ u₂) := by
  have hL {f : ℝ → ℝ} (hf : ContDiff ℝ n f) : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) n
      (Prod.map (fun s ↦ Real.smoothTransition (f s)) (id : ℝ → ℝ)) :=
    ((Real.smoothTransition.contDiff.comp hf).prodMap contDiff_id).contMDiff
  intro z
  rcases lt_or_ge z.1 (2 / 3) with hz | hz
  · have hev : rectangleTrans u₁ u₂ =ᶠ[𝓝 z]
        u₁ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s)) id :=
      (isOpen_lt continuous_fst continuous_const).eventually_mem hz |>.mono
        fun w hw ↦ rectangleTrans_eq_left h hw
    exact ((hu₁.comp (hL (f := fun s ↦ 3 * s) (by fun_prop))) z).congr_of_eventuallyEq hev
  · have hev : rectangleTrans u₁ u₂ =ᶠ[𝓝 z]
        u₂ ∘ Prod.map (fun s ↦ Real.smoothTransition (3 * s - 2)) id :=
      (isOpen_lt continuous_const continuous_fst).eventually_mem (by linarith : (1 / 3 : ℝ) < z.1)
        |>.mono fun w hw ↦ rectangleTrans_eq_right h hw
    exact ((hu₂.comp (hL (f := fun s ↦ 3 * s - 2) (by fun_prop))) z).congr_of_eventuallyEq hev

/-- **The integral over a concatenation.** For a continuous form and two `C¹` maps `u₁` and `u₂`
with `u₁ (1, ·) = u₂ (0, ·)`, the integral over `[0, 1] × [a₂, b₂]` of their concatenation is the
sum of the integrals of `u₁` and `u₂`. -/
theorem rectangleIntegral_rectangleTrans [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {u₁ u₂ : ℝ × ℝ → M} (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u₁)
    (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u₂) (h : ∀ t, u₁ (1, t) = u₂ (0, t)) (a₂ b₂ : ℝ) :
    rectangleIntegral φ (rectangleTrans u₁ u₂) (0, a₂) (1, b₂) =
      rectangleIntegral φ u₁ (0, a₂) (1, b₂) + rectangleIntegral φ u₂ (0, a₂) (1, b₂) := by
  -- The two reparametrizations `s ↦ β (f s)`, for `f s = 3 s` and `f s = 3 s - 2`.
  have hβ {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
      (∀ s, HasDerivAt (fun s ↦ Real.smoothTransition (f s))
        (deriv (fun s ↦ Real.smoothTransition (f s)) s) s) ∧
      Continuous (deriv fun s ↦ Real.smoothTransition (f s)) :=
    have hc := Real.smoothTransition.contDiff.comp hf
    ⟨fun s ↦ (hc.differentiable one_ne_zero s).hasDerivAt, hc.continuous_deriv le_rfl⟩
  have h₁ := hβ (f := fun s ↦ 3 * s) (by fun_prop)
  have h₂ := hβ (f := fun s ↦ 3 * s - 2) (by fun_prop)
  rw [← rectangleIntegral_add_adjacent_fst hφ (contMDiff_rectangleTrans hu₁ hu₂ h) _ _ (1 / 2)]
  congr 1
  · -- On `[0, 1/2]` the concatenation is `u₁` reparametrized by `s ↦ β (3 s)`.
    rw [rectangleIntegral_congr fun z hz ↦ rectangleTrans_eq_left h (z := z) (by
        simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hz
        linarith [hz.1.2]),
      rectangleIntegral_comp_prodMap hφ hu₁ (fun s _ ↦ h₁.1 s) h₁.2.continuousOn]
    norm_num [Real.smoothTransition.one_of_one_le]
  · -- On `[1/2, 1]` it is `u₂` reparametrized by `s ↦ β (3 s - 2)`.
    rw [rectangleIntegral_congr fun z hz ↦ rectangleTrans_eq_right h (z := z) (by
        simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hz
        linarith [hz.1.1]),
      rectangleIntegral_comp_prodMap hφ hu₂ (fun s _ ↦ h₂.1 s) h₂.2.continuousOn]
    norm_num [Real.smoothTransition.zero_of_nonpos]

/-! ### Green's formula -/

variable [IsManifold I 2 M]

/-- **Green's formula.** The integral of the exterior derivative `dα` of a `C¹` one-form over a
`C²` map `u` on the rectangle with opposite corners `a` and `b` is the signed sum of the line
integrals of `α` along the four edges of the rectangle: the edges `s = b.1` and `s = a.1`, run in
the direction of `t`, minus the edges `t = b.2` and `t = a.2`, run in the direction of `s`. -/
theorem rectangleIntegral_mextDeriv {α : RoughForm I M F 1} (hα : IsSmoothForm I 1 α)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (a b : ℝ × ℝ) :
    rectangleIntegral (mextDeriv α) u a b =
      (pathIntegral α (fun t ↦ u (b.1, t)) a.2 b.2 -
        pathIntegral α (fun t ↦ u (a.1, t)) a.2 b.2) -
      (pathIntegral α (fun s ↦ u (s, b.2)) a.1 b.1 -
        pathIntegral α (fun s ↦ u (s, a.2)) a.1 b.1) := by
  have hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u := hu.of_le one_le_two
  -- The pullback `ψ = u^* α` is a `C¹` flat one-form on the plane with `dψ = u^* dα`.
  let ψ : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ) I u α
  have hψ : ContDiff ℝ 1 ψ :=
    isSmoothForm_modelSpace_iff.mp (hα.mpullback (by simpa [one_add_one_eq_two] using hu))
  have hdψ (z : ℝ × ℝ) : mpullback 𝓘(ℝ, ℝ × ℝ) I u (mextDeriv α) z = extDeriv ψ z := by
    rw [← mextDeriv_eq_extDeriv,
      mpullback_mextDeriv hu ((isSmoothBundleForm_def _ _).mpr hα.contMDiff)]
  rw [pathIntegral_apply_snd hu₁, pathIntegral_apply_snd hu₁, pathIntegral_apply_fst hu₁,
    pathIntegral_apply_fst hu₁, rectangleIntegral_def]
  simp only [hdψ]
  exact integral2_extDeriv fun z _ ↦ hψ.contDiffAt

end TauCeti
