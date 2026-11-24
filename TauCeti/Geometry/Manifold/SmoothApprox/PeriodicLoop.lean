/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothApprox.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Fract
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Topology.Homotopy.Path

/-!
# Smooth representatives of paths of smooth loops

Let `M` be a Hausdorff boundaryless manifold, and let `γ₀`, `γ₁` be loops at `x` that are the
restrictions to `[0, 1]` of `C^n` `1`-periodic maps `g₀ g₁ : ℝ → M`. A path of loops `P` from
`γ₀` to `γ₁` is a continuous cylinder whose seam stays at `x`. This file shows that `P` is
homotopic, relative to its endpoints, to the path of loops `s ↦ u (s, ·)` of a `C^n` map
`u : ℝ × ℝ → M` that is `1`-periodic in its second coordinate, with `u (0, ·) = g₀` and
`u (1, ·) = g₁`. The target need not be compact. For `n ≥ 2` such a `u` is a cylinder in the sense
of `TauCeti.IsLoopCylinder`; the consequences for cylinders and caps are drawn in
`Geometry/Symplectic/Hamiltonian/ContractibleAction/Smooth.lean`, and those for raw caps in
`Geometry/Symplectic/Floer/Cap/Smoothing.lean`.

The proof smooths a disc relative to its boundary, keeping the boundary values exactly. The path
`P` is first replaced by a continuous map of the plane which is already smooth off a rectangle
inside the unit square. Fix a smooth map `c` of `[0, 1]` onto itself which is `0` near `0` and `1`
near `1` (`TauCeti.collaredSmoothTransition`), and its linear interpolation `τ_r = (1 - r) id + r c`
with the identity (`TauCeti.collaredSmoothTransitionLineMap`). Then:

* near the edge `s = 0` the map is `g₀ ∘ τ_r`, with `r` rising smoothly from `0` to `1`;
* near the edge `s = 1` it is `g₁ ∘ τ_r`, with `r` falling smoothly from `1` to `0`;
* in between, it is `P` precomposed with `c` in the loop direction, so it is constant equal to `x`
  near the seam `t ∈ ℤ`.

Its class is that of `P`: it is the image of the diagonal of the square of loops
`(a, s) ↦ P (σ_a s) ∘ τ_{ρ_a s}`, whose edges `s = 0` and `s = 1` are `γ₀` and `γ₁`. The
relative Whitney approximation theorem
(`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`) then makes it smooth
without changing it off the rectangle. The result is periodized in `t`;
since the map is periodic near the seam, the periodization is still smooth
(`ContMDiff.comp_fract_snd`), and on the unit square it is the smoothed map.

## Main results

* `TauCeti.exists_contMDiff_periodic_homotopic`: every path of loops between `C^n` periodic loops
  is homotopic to the path of loops of a `C^n` periodic map of the plane.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.26
  (relative Whitney approximation).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace TauCeti

/-! ### Reparametrizations -/

section Reparam

/-- A smooth map of the line which is `0` up to `1/6` and `1` from `1/4` on. -/
private def loopRamp (s : ℝ) : ℝ :=
  Real.smoothTransition (12 * s - 2)

private theorem loopRamp_of_le {s : ℝ} (hs : s ≤ 1 / 6) : loopRamp s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem loopRamp_of_ge {s : ℝ} (hs : 1 / 4 ≤ s) : loopRamp s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem loopRamp_mem (s : ℝ) : loopRamp s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem contDiff_loopRamp {n : ℕ∞} : ContDiff ℝ n loopRamp :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The reparametrization `(s, t) ↦ τ_{r s} t` is `C^n` for a `C^n` weight `r`. -/
private theorem contDiff_lineMap_comp {n : ℕ∞} {r : ℝ → ℝ} (hr : ContDiff ℝ n r) :
    ContDiff ℝ n fun z : ℝ × ℝ ↦ collaredSmoothTransitionLineMap (r z.1) z.2 :=
  (contDiff_collaredSmoothTransitionLineMap (WithTop.coe_le_coe.2 le_top)).comp
    ((hr.comp contDiff_fst).prodMk contDiff_snd)

end Reparam

/-! ### A model of the path of loops which is smooth near the boundary of a rectangle -/

section Model

variable {M : Type*} [TopologicalSpace M] {x : M} {γ₀ γ₁ : Path x x}

/-- The model of the path of loops `P`, for periodic extensions `g₀`, `g₁` of its ends: `g₀`
precomposed with `collaredSmoothTransitionLineMap (loopRamp s)` for `s ≤ 1/3`, `g₁` precomposed
with `collaredSmoothTransitionLineMap (loopRamp (1 - s))` for `s > 2/3`, and in between `P`
precomposed with `collaredSmoothTransition` in the loop direction, run three times as fast. It is
smooth near the edges `s = 0` and `s = 1`, and equal to `x` near the seam in between. -/
private def loopModel (g₀ g₁ : ℝ → M) (P : Path γ₀ γ₁) (z : ℝ × ℝ) : M :=
  if z.1 ≤ 1 / 3 then g₀ (collaredSmoothTransitionLineMap (loopRamp z.1) z.2)
  else if z.1 ≤ 2 / 3 then P.extend (3 * z.1 - 1) (collaredSmoothTransitionUnit z.2)
  else g₁ (collaredSmoothTransitionLineMap (loopRamp (1 - z.1)) z.2)

variable {g₀ g₁ : ℝ → M} {P : Path γ₀ γ₁}

private theorem loopModel_of_le {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 3) :
    loopModel g₀ g₁ P z = g₀ (collaredSmoothTransitionLineMap (loopRamp z.1) z.2) := by
  simp only [loopModel, hz, ↓reduceIte]

private theorem loopModel_of_mem {z : ℝ × ℝ} (hz₁ : 1 / 3 < z.1) (hz₂ : z.1 ≤ 2 / 3) :
    loopModel g₀ g₁ P z = P.extend (3 * z.1 - 1) (collaredSmoothTransitionUnit z.2) := by
  simp only [loopModel, hz₁.not_ge, hz₂, ↓reduceIte]

private theorem loopModel_of_gt {z : ℝ × ℝ} (hz : 2 / 3 < z.1) :
    loopModel g₀ g₁ P z = g₁ (collaredSmoothTransitionLineMap (loopRamp (1 - z.1)) z.2) := by
  simp only [loopModel, (by linarith : ¬z.1 ≤ 1 / 3), hz.not_ge, ↓reduceIte]

private theorem loopModel_zero (t : ℝ) : loopModel g₀ g₁ P (0, t) = g₀ t := by
  rw [loopModel_of_le (by norm_num), loopRamp_of_le (by norm_num),
    collaredSmoothTransitionLineMap_zero_left]

private theorem loopModel_one (t : ℝ) : loopModel g₀ g₁ P (1, t) = g₁ t := by
  rw [loopModel_of_gt (by norm_num), sub_self, loopRamp_of_le (by norm_num),
    collaredSmoothTransitionLineMap_zero_left]

/-- The open set on which the model is constant equal to the base point: the parts near the seam
of the strip `1/4 < s < 3/4`. -/
private def loopBaseSet : Set (ℝ × ℝ) :=
  {z | 1 / 4 < z.1} ∩ {z | z.1 < 3 / 4} ∩ ({z | z.2 < 1 / 4} ∪ {z | 3 / 4 < z.2})

private theorem isOpen_loopBaseSet : IsOpen loopBaseSet :=
  ((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).inter
    ((isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd))

/-- The open set near which the model is smooth: the strips `s < 1/3` and `s > 2/3`, and the set on
which the model is the base point. -/
private def loopSmoothSet : Set (ℝ × ℝ) :=
  {z | z.1 < 1 / 3} ∪ {z | 2 / 3 < z.1} ∪ loopBaseSet

private theorem isOpen_loopSmoothSet : IsOpen loopSmoothSet :=
  ((isOpen_lt continuous_fst continuous_const).union
    (isOpen_lt continuous_const continuous_fst)).union isOpen_loopBaseSet

variable (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t) (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t)
include hγ₀ hγ₁

private theorem apply_zero_eq_base : g₀ 0 = x ∧ g₁ 0 = x :=
  ⟨by rw [← Icc.coe_zero, ← hγ₀, γ₀.source], by rw [← Icc.coe_zero, ← hγ₁, γ₁.source]⟩

private theorem apply_one_eq_base : g₀ 1 = x ∧ g₁ 1 = x :=
  ⟨by rw [← Icc.coe_one, ← hγ₀, γ₀.target], by rw [← Icc.coe_one, ← hγ₁, γ₁.target]⟩

private theorem loopModel_eq_of_mem (s t : unitInterval) :
    loopModel g₀ g₁ P (s, t) = P.extend (3 * s - 1)
      (collaredSmoothTransitionLineMapUnit
        (projIcc 0 1 zero_le_one (min (loopRamp s) (loopRamp (1 - s)))) t) := by
  rcases le_or_gt (s : ℝ) (1 / 3) with hs | hs
  · have h : loopRamp s ≤ loopRamp (1 - s) :=
      (loopRamp_mem _).2.trans (loopRamp_of_ge (by linarith)).ge
    simp [loopModel_of_le (z := ((s : ℝ), (t : ℝ))) hs, min_eq_left h,
      projIcc_of_mem _ (loopRamp_mem s), P.extend_of_le_zero (by linarith : 3 * (s : ℝ) - 1 ≤ 0),
      hγ₀, coe_collaredSmoothTransitionLineMapUnit]
  rcases le_or_gt (s : ℝ) (2 / 3) with hs' | hs'
  · rw [loopRamp_of_ge (by linarith), loopRamp_of_ge (by linarith), min_self,
      projIcc_eq_one.2 le_rfl, collaredSmoothTransitionLineMapUnit_one_left,
      loopModel_of_mem hs hs']
  · have h : loopRamp (1 - s) ≤ loopRamp s :=
      (loopRamp_mem _).2.trans (loopRamp_of_ge (by linarith)).ge
    simp [loopModel_of_gt (z := ((s : ℝ), (t : ℝ))) hs', min_eq_right h,
      projIcc_of_mem _ (loopRamp_mem (1 - s)),
      P.extend_of_one_le (by linarith : 1 ≤ 3 * (s : ℝ) - 1), hγ₁,
      coe_collaredSmoothTransitionLineMapUnit]

private theorem continuous_loopModel (hg₀ : Continuous g₀) (hg₁ : Continuous g₁) :
    Continuous (loopModel g₀ g₁ P) := by
  have hr₀ : Continuous fun z : ℝ × ℝ ↦ collaredSmoothTransitionLineMap (loopRamp z.1) z.2 :=
    (contDiff_lineMap_comp (n := 0) contDiff_loopRamp).continuous
  have hr₁ : Continuous fun z : ℝ × ℝ ↦ collaredSmoothTransitionLineMap (loopRamp (1 - z.1)) z.2 :=
    (contDiff_lineMap_comp (n := 0)
      (contDiff_loopRamp.comp (contDiff_const.sub contDiff_id))).continuous
  have hP : Continuous fun z : ℝ × ℝ ↦ P.extend (3 * z.1 - 1) (collaredSmoothTransitionUnit z.2) :=
    (Path.continuous_uncurry_iff.2 P.continuous_extend).comp
      (((continuous_const.mul continuous_fst).sub continuous_const).prodMk
        (continuous_collaredSmoothTransitionUnit.comp continuous_snd))
  refine Continuous.if_le (hg₀.comp hr₀)
    (Continuous.if_le hP (hg₁.comp hr₁) continuous_fst continuous_const fun z hz ↦ ?_)
    continuous_fst continuous_const fun z hz ↦ ?_
  · rw [hz, P.extend_of_one_le (by norm_num), hγ₁, loopRamp_of_ge (by norm_num),
      collaredSmoothTransitionLineMap_one_left, coe_collaredSmoothTransitionUnit_eq]
  · simp only [hz, (by norm_num : (1 : ℝ) / 3 ≤ 2 / 3), ↓reduceIte]
    rw [loopRamp_of_ge (by norm_num), P.extend_of_le_zero (by norm_num), hγ₀,
      collaredSmoothTransitionLineMap_one_left, coe_collaredSmoothTransitionUnit_eq]

/-- The model is `x` near the seam for `1/4 < s < 3/4`. -/
private theorem loopModel_eq_base {z : ℝ × ℝ} (hz₁ : 1 / 4 < z.1) (hz₂ : z.1 < 3 / 4)
    (ht : z.2 ≤ 1 / 4 ∨ 3 / 4 ≤ z.2) : loopModel g₀ g₁ P z = x := by
  obtain ⟨h₀, h₀'⟩ := apply_zero_eq_base hγ₀ hγ₁
  obtain ⟨h₁, h₁'⟩ := apply_one_eq_base hγ₀ hγ₁
  rcases le_or_gt z.1 (1 / 3) with hs | hs
  · rcases ht with ht | ht
    · simp [loopModel_of_le hs, loopRamp_of_ge hz₁.le, collaredSmoothTransition_eq_zero_of_le ht,
        h₀]
    · simp [loopModel_of_le hs, loopRamp_of_ge hz₁.le, collaredSmoothTransition_eq_one_of_ge ht,
        h₁]
  rcases le_or_gt z.1 (2 / 3) with hs' | hs'
  · rcases ht with ht | ht
    · simp [loopModel_of_mem hs hs', collaredSmoothTransitionUnit_eq_zero_of_le ht]
    · simp [loopModel_of_mem hs hs', collaredSmoothTransitionUnit_eq_one_of_ge ht]
  · have hr : loopRamp (1 - z.1) = 1 := loopRamp_of_ge (by linarith)
    rcases ht with ht | ht
    · simp [loopModel_of_gt hs', hr, collaredSmoothTransition_eq_zero_of_le ht, h₀']
    · simp [loopModel_of_gt hs', hr, collaredSmoothTransition_eq_one_of_ge ht, h₁']

private theorem loopModel_seam_zero (s : ℝ) : loopModel g₀ g₁ P (s, 0) = x := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [loopModel_of_le hs, collaredSmoothTransitionLineMap_zero_right,
      (apply_zero_eq_base hγ₀ hγ₁).1]
  rcases le_or_gt s (2 / 3) with hs' | hs'
  · rw [loopModel_of_mem hs hs', collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num),
      Path.source]
  · rw [loopModel_of_gt hs', collaredSmoothTransitionLineMap_zero_right,
      (apply_zero_eq_base hγ₀ hγ₁).2]

private theorem loopModel_seam_one (s : ℝ) : loopModel g₀ g₁ P (s, 1) = x := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [loopModel_of_le hs, collaredSmoothTransitionLineMap_one_right,
      (apply_one_eq_base hγ₀ hγ₁).1]
  rcases le_or_gt s (2 / 3) with hs' | hs'
  · rw [loopModel_of_mem hs hs', collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num),
      Path.target]
  · rw [loopModel_of_gt hs', collaredSmoothTransitionLineMap_one_right,
      (apply_one_eq_base hγ₀ hγ₁).2]

omit hγ₀ hγ₁ in
/-- The model is periodic in `t` near the seam. -/
private theorem loopModel_add_one (hgp₀ : Periodic g₀ 1) (hgp₁ : Periodic g₁ 1) (s : ℝ) {t : ℝ}
    (ht₀ : -1 / 4 ≤ t) (ht₁ : t ≤ 1 / 4) :
    loopModel g₀ g₁ P (s, t + 1) = loopModel g₀ g₁ P (s, t) := by
  rcases le_or_gt s (1 / 3) with hs | hs
  · rw [loopModel_of_le hs, loopModel_of_le hs, collaredSmoothTransitionLineMap_add_one _ ht₀ ht₁,
      hgp₀]
  rcases le_or_gt s (2 / 3) with hs' | hs'
  · rw [loopModel_of_mem hs hs', loopModel_of_mem hs hs',
      collaredSmoothTransitionUnit_eq_one_of_ge (by linarith),
      collaredSmoothTransitionUnit_eq_zero_of_le ht₁, Path.source, Path.target]
  · rw [loopModel_of_gt hs', loopModel_of_gt hs',
      collaredSmoothTransitionLineMap_add_one _ ht₀ ht₁, hgp₁]

private theorem contMDiffOn_loopModel {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H M] {n : ℕ∞}
    (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀) (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n (loopModel g₀ g₁ P) loopSmoothSet := by
  rintro z ((hz | hz) | hz)
  · have h : loopModel g₀ g₁ P =ᶠ[𝓝 z] fun w : ℝ × ℝ ↦
        g₀ (collaredSmoothTransitionLineMap (loopRamp w.1) w.2) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
      exact loopModel_of_le (le_of_lt hw)
    exact ((hg₀.comp (contDiff_lineMap_comp contDiff_loopRamp).contMDiff).contMDiffAt
      |>.congr_of_eventuallyEq h).contMDiffWithinAt
  · have h : loopModel g₀ g₁ P =ᶠ[𝓝 z] fun w : ℝ × ℝ ↦
        g₁ (collaredSmoothTransitionLineMap (loopRamp (1 - w.1)) w.2) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz] with w hw
      exact loopModel_of_gt hw
    exact ((hg₁.comp (contDiff_lineMap_comp
      (contDiff_loopRamp.comp (contDiff_const.sub contDiff_id))).contMDiff).contMDiffAt
      |>.congr_of_eventuallyEq h).contMDiffWithinAt
  · have h : loopModel g₀ g₁ P =ᶠ[𝓝 z] fun _ ↦ x := by
      filter_upwards [isOpen_loopBaseSet.mem_nhds hz] with w ⟨⟨hw₁, hw₂⟩, hw⟩
      exact loopModel_eq_base hγ₀ hγ₁ hw₁ hw₂ (hw.imp le_of_lt le_of_lt)
    exact (contMDiffAt_const.congr_of_eventuallyEq h).contMDiffWithinAt

/-- The path in the loop space traced by the model on the unit square. -/
private def loopModelPath (hg₀ : Continuous g₀) (hg₁ : Continuous g₁) : Path γ₀ γ₁ :=
  Path.ofContinuousFamily (fun s t : unitInterval ↦ loopModel g₀ g₁ P (s, t))
    ((continuous_loopModel hγ₀ hγ₁ hg₀ hg₁).comp
      (continuous_subtypeVal.prodMap continuous_subtypeVal))
    (fun s ↦ by rw [Icc.coe_zero, loopModel_seam_zero hγ₀ hγ₁])
    (fun s ↦ by rw [Icc.coe_one, loopModel_seam_one hγ₀ hγ₁])
    (fun t ↦ by rw [Icc.coe_zero, loopModel_zero, hγ₀])
    (fun t ↦ by rw [Icc.coe_one, loopModel_one, hγ₁])

private theorem loopModelPath_apply (hg₀ : Continuous g₀) (hg₁ : Continuous g₁)
    (s t : unitInterval) :
    loopModelPath (P := P) hγ₀ hγ₁ hg₀ hg₁ s t = loopModel g₀ g₁ P (s, t) :=
  Path.ofContinuousFamily_apply _ _ _ _ _ _ s t

/-- The model has the class of `P`: it is the image of the diagonal of the square of loops
`(a, s) ↦ P (σ_a s) ∘ τ_{ρ_a s}`, whose edges `s = 0` and `s = 1` are `γ₀` and `γ₁`. -/
private theorem homotopic_loopModelPath (hg₀ : Continuous g₀) (hg₁ : Continuous g₁) :
    P.Homotopic (loopModelPath (P := P) hγ₀ hγ₁ hg₀ hg₁) := by
  -- The square `(a, s) ↦ P (σ_a s) ∘ τ_{ρ_a s}`, with `(ρ_a, σ_a)` interpolating linearly between
  -- `(0, s)` and the parameters `(min (loopRamp s) (loopRamp (1 - s)), 3 s - 1)` of the model.
  set σ : unitInterval × unitInterval → ℝ := fun q ↦ (1 - q.1) * q.2 + q.1 * (3 * q.2 - 1)
  set ρ : unitInterval × unitInterval → unitInterval := fun q ↦
    projIcc 0 1 zero_le_one (q.1 * min (loopRamp q.2) (loopRamp (1 - q.2)))
  have hσ : Continuous σ := by fun_prop
  have hρ : Continuous ρ := continuous_projIcc.comp
    ((continuous_subtypeVal.comp continuous_fst).mul
      ((contDiff_loopRamp (n := 0)).continuous.comp (continuous_subtypeVal.comp continuous_snd)
        |>.min ((contDiff_loopRamp (n := 0)).continuous.comp
          (continuous_const.sub (continuous_subtypeVal.comp continuous_snd)))))
  let K := Path.continuousFamily (x₀ := x) (x₁ := x)
    (fun (q : unitInterval × unitInterval) (t : unitInterval) ↦
      P.extend (σ q) (collaredSmoothTransitionLineMapUnit (ρ q) t))
    ((Path.continuous_uncurry_iff.2 P.continuous_extend).comp ((hσ.comp continuous_fst).prodMk
      (continuous_collaredSmoothTransitionLineMapUnit.comp
        ((hρ.comp continuous_fst).prodMk continuous_snd))))
    (fun q ↦ by simp only [collaredSmoothTransitionLineMapUnit_zero_right, Path.source])
    (fun q ↦ by simp only [collaredSmoothTransitionLineMapUnit_one_right, Path.target])
  refine Path.homotopic_of_continuous_square K K.continuous (fun s ↦ ?_) (fun s ↦ ?_)
    (fun a ↦ ?_) (fun a ↦ ?_) <;> refine Path.ext (funext fun t ↦ ?_) <;>
    rw [Path.continuousFamily_apply]
  · have h₁ : σ (0, s) = s := by simp [σ]
    have h₂ : ρ (0, s) = 0 := by simp [ρ]
    rw [h₁, h₂, collaredSmoothTransitionLineMapUnit_zero_left, P.extend_extends']
  · have h₁ : σ (1, s) = 3 * (s : ℝ) - 1 := by simp [σ]
    have h₂ : ρ (1, s) =
        projIcc 0 1 zero_le_one (min (loopRamp s) (loopRamp (1 - s))) := by simp [ρ]
    rw [h₁, h₂, loopModelPath_apply, loopModel_eq_of_mem hγ₀ hγ₁]
  · have h₁ : σ (a, 0) ≤ 0 := by
      simp only [σ, Icc.coe_zero, mul_zero, zero_add, zero_sub]
      nlinarith [a.property.1]
    have h₂ : ρ (a, 0) = 0 := by
      simp [ρ, loopRamp_of_le (by norm_num : (0 : ℝ) ≤ 1 / 6),
        loopRamp_of_ge (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    rw [P.extend_of_le_zero h₁, h₂, collaredSmoothTransitionLineMapUnit_zero_left]
  · have h₁ : 1 ≤ σ (a, 1) := by
      simp only [σ, Icc.coe_one]
      nlinarith [a.property.1]
    have h₂ : ρ (a, 1) = 0 := by
      simp [ρ, loopRamp_of_le (by norm_num : (0 : ℝ) ≤ 1 / 6),
        loopRamp_of_ge (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    rw [P.extend_of_one_le h₁, h₂, collaredSmoothTransitionLineMapUnit_zero_left]

end Model

/-! ### Smooth representatives -/

section Smoothing

/-- The complement of a rectangle inside the unit square: the closed set on which the smoothing
of the model keeps its values. -/
private def loopFixedSet : Set (ℝ × ℝ) :=
  (Ioo (3 / 10 : ℝ) (7 / 10) ×ˢ Ioo (1 / 5 : ℝ) (4 / 5))ᶜ

private theorem isClosed_loopFixedSet : IsClosed loopFixedSet :=
  (isOpen_Ioo.prod isOpen_Ioo).isClosed_compl

private theorem mem_loopFixedSet_of_fst {z : ℝ × ℝ} (h : z.1 ≤ 3 / 10 ∨ 7 / 10 ≤ z.1) :
    z ∈ loopFixedSet := by
  rintro ⟨⟨h₁, h₂⟩, -⟩
  rcases h with h | h <;> linarith

private theorem mem_loopFixedSet_of_snd {z : ℝ × ℝ} (h : z.2 ≤ 1 / 5 ∨ 4 / 5 ≤ z.2) :
    z ∈ loopFixedSet := by
  rintro ⟨-, ⟨h₁, h₂⟩⟩
  rcases h with h | h <;> linarith

private theorem loopFixedSet_subset : loopFixedSet ⊆ loopSmoothSet := by
  intro z hz
  rcases lt_or_ge z.1 (1 / 3) with h₁ | h₁
  · exact Or.inl (Or.inl h₁)
  rcases lt_or_ge (2 / 3) z.1 with h₂ | h₂
  · exact Or.inl (Or.inr h₂)
  refine Or.inr ⟨⟨(by linarith : (1 / 4 : ℝ) < z.1), (by linarith : z.1 < 3 / 4)⟩, ?_⟩
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at h
  exact hz ⟨⟨by linarith, by linarith⟩, ⟨by linarith [h.1], by linarith [h.2]⟩⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {x : M} {γ₀ γ₁ : Path x x}
  {g₀ g₁ : ℝ → M} {n : ℕ∞}

/-- The periodization in `t` of a `C^n` map `G` which agrees with the model off a rectangle
inside the unit square is `C^n`: near the seam the model, hence `G`, is periodic. -/
private theorem contMDiff_periodize (hgp₀ : Periodic g₀ 1) (hgp₁ : Periodic g₁ 1)
    {P : Path γ₀ γ₁} {G : ℝ × ℝ → M} (hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n G)
    (hGf : ∀ z ∈ loopFixedSet, G z = loopModel g₀ g₁ P z) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n fun z : ℝ × ℝ ↦ G (z.1, Int.fract z.2) :=
  contMDiff_prod_modelWithCornersSelf_iff.1 <|
    (contMDiff_prod_modelWithCornersSelf_iff.2 hG).comp_fract_snd (ε := 1 / 5) (by norm_num)
      fun s t ht₀ ht₁ ↦ by
        rw [hGf _ (mem_loopFixedSet_of_snd (Or.inr (by linarith))),
          hGf _ (mem_loopFixedSet_of_snd (Or.inl (by linarith))),
          loopModel_add_one hgp₀ hgp₁ s (by linarith) (by linarith)]

/-- A homotopy, relative to the complement of a rectangle inside the unit square, from the model
to a map `G` gives a homotopy of paths in the loop space from the model path to every path of
loops given on the unit square by the periodization of `G`. -/
private theorem homotopic_loopModelPath_of_homotopyRel (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (hc₀ : Continuous g₀) (hc₁ : Continuous g₁)
    {P : Path γ₀ γ₁} {G : C(ℝ × ℝ, M)}
    (R : (⟨loopModel g₀ g₁ P, continuous_loopModel hγ₀ hγ₁ hc₀ hc₁⟩ : C(ℝ × ℝ, M)).HomotopyRel G
      loopFixedSet)
    {P' : Path γ₀ γ₁} (hP' : ∀ s t : unitInterval, P' s t = G (s, Int.fract (t : ℝ))) :
    (loopModelPath (P := P) hγ₀ hγ₁ hc₀ hc₁).Homotopic P' := by
  have hR : Continuous fun q : (unitInterval × unitInterval) × unitInterval ↦
      R (q.1.1, ((q.1.2 : ℝ), (q.2 : ℝ))) :=
    R.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_subtypeVal.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_subtypeVal.comp continuous_snd)))
  let K := Path.continuousFamily (x₀ := x) (x₁ := x)
    (fun (q : unitInterval × unitInterval) (t : unitInterval) ↦ R (q.1, ((q.2 : ℝ), (t : ℝ)))) hR
    (fun q ↦ by
      rw [Icc.coe_zero]
      exact (R.eq_fst _ (mem_loopFixedSet_of_snd (Or.inl (by norm_num)))).trans
        (loopModel_seam_zero hγ₀ hγ₁ _))
    (fun q ↦ by
      rw [Icc.coe_one]
      exact (R.eq_fst _ (mem_loopFixedSet_of_snd (Or.inr (by norm_num)))).trans
        (loopModel_seam_one hγ₀ hγ₁ _))
  refine Path.homotopic_of_continuous_square K K.continuous (fun s ↦ ?_) (fun s ↦ ?_)
    (fun a ↦ ?_) (fun a ↦ ?_) <;> refine Path.ext (funext fun t ↦ ?_) <;>
    rw [Path.continuousFamily_apply]
  · rw [loopModelPath_apply]
    exact R.apply_zero _
  · -- At `t = 1` the periodization reads `G` at `t = 0`, where both values are `x`.
    rw [R.apply_one, hP']
    rcases eq_or_lt_of_le t.property.2 with h | h
    · rw [h, Int.fract_one,
        ← R.fst_eq_snd (x := ((s : ℝ), 1)) (mem_loopFixedSet_of_snd (Or.inr (by norm_num))),
        ← R.fst_eq_snd (x := ((s : ℝ), 0)) (mem_loopFixedSet_of_snd (Or.inl (by norm_num)))]
      exact (loopModel_seam_one hγ₀ hγ₁ _).trans (loopModel_seam_zero hγ₀ hγ₁ _).symm
    · rw [Int.fract_eq_self.2 ⟨t.property.1, h⟩]
  · rw [Icc.coe_zero]
    exact (R.eq_fst _ (mem_loopFixedSet_of_fst (Or.inl (by norm_num)))).trans
      ((loopModel_zero t).trans (hγ₀ t).symm)
  · rw [Icc.coe_one]
    exact (R.eq_fst _ (mem_loopFixedSet_of_fst (Or.inr (by norm_num)))).trans
      ((loopModel_one t).trans (hγ₁ t).symm)

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth representatives of paths of loops.** Let `γ₀` and `γ₁` be loops at `x` in a
Hausdorff boundaryless manifold, the restrictions of `C^n` `1`-periodic maps `g₀ g₁ : ℝ → M`. Every
path of loops `P` from `γ₀` to `γ₁` is homotopic, relative to its endpoints, to the path of loops
`s ↦ u (s, ·)` of a `C^n` map `u : ℝ × ℝ → M` that is `1`-periodic in its second coordinate, with
`u (0, ·) = g₀` and `u (1, ·) = g₁`. -/
theorem exists_contMDiff_periodic_homotopic (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀)
    (hgp₀ : Periodic g₀ 1) (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t)
    (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁) (hgp₁ : Periodic g₁ 1)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (P : Path γ₀ γ₁) :
    ∃ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u ∧ (∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) ∧
      (∀ t, u (0, t) = g₀ t) ∧ (∀ t, u (1, t) = g₁ t) ∧
      ∃ P' : Path γ₀ γ₁, (∀ s t : unitInterval, P' s t = u (s, t)) ∧ P'.Homotopic P := by
  have hc₀ := hg₀.continuous
  have hc₁ := hg₁.continuous
  let f : C(ℝ × ℝ, M) := ⟨loopModel g₀ g₁ P, continuous_loopModel hγ₀ hγ₁ hc₀ hc₁⟩
  -- The model takes values in the images of `g₀`, `g₁` and `P`, so its image is relatively
  -- compact.
  have hK : IsCompact (closure (range f)) := by
    refine (((hgp₀.compact_of_continuous one_ne_zero hc₀).union
      (hgp₁.compact_of_continuous one_ne_zero hc₁)).union
      (isCompact_range (Path.continuous_uncurry_iff.2 P.continuous))).closure_of_subset ?_
    rintro _ ⟨z, rfl⟩
    rcases le_or_gt z.1 (1 / 3) with h | h
    · exact Or.inl (Or.inl ⟨_, (loopModel_of_le h).symm⟩)
    rcases le_or_gt z.1 (2 / 3) with h' | h'
    · exact Or.inr ⟨(projIcc 0 1 zero_le_one (3 * z.1 - 1), _), (loopModel_of_mem h h').symm⟩
    · exact Or.inl (Or.inr ⟨_, (loopModel_of_gt h').symm⟩)
  -- Smooth the model relative to the complement of a rectangle inside the unit square.
  obtain ⟨G, hG, ⟨R⟩⟩ := f.exists_contMDiff_homotopicRel_of_isCompact_closure_range
    (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) n hK isClosed_loopFixedSet
    (isOpen_loopSmoothSet.mem_nhdsSet.2 loopFixedSet_subset)
    (contMDiffOn_loopModel hγ₀ hγ₁ hg₀ hg₁)
  have hGf (z : ℝ × ℝ) (hz : z ∈ loopFixedSet) : G z = loopModel g₀ g₁ P z :=
    (R.fst_eq_snd hz).symm
  -- Periodize the smoothing in `t`.
  let u : ℝ × ℝ → M := fun z ↦ G (z.1, Int.fract z.2)
  have hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u := contMDiff_periodize hgp₀ hgp₁ hG hGf
  have hu₀ (t : ℝ) : u (0, t) = g₀ t := by
    simp only [u]
    rw [hGf _ (mem_loopFixedSet_of_fst (Or.inl (by norm_num))), loopModel_zero, hgp₀.apply_fract]
  have hu₁ (t : ℝ) : u (1, t) = g₁ t := by
    simp only [u]
    rw [hGf _ (mem_loopFixedSet_of_fst (Or.inr (by norm_num))), loopModel_one, hgp₁.apply_fract]
  have hseam₀ (s : ℝ) : u (s, 0) = x := by
    simp only [u, Int.fract_zero]
    rw [hGf _ (mem_loopFixedSet_of_snd (Or.inl (by norm_num))), loopModel_seam_zero hγ₀ hγ₁]
  have hseam₁ (s : ℝ) : u (s, 1) = x := by
    simp only [u, Int.fract_one]
    rw [hGf _ (mem_loopFixedSet_of_snd (Or.inl (by norm_num))), loopModel_seam_zero hγ₀ hγ₁]
  let Pu : Path γ₀ γ₁ := Path.ofContinuousFamily (fun s t ↦ u (s, t))
    (hu.continuous.comp (by fun_prop)) (fun s ↦ by rw [Icc.coe_zero, hseam₀])
    (fun s ↦ by rw [Icc.coe_one, hseam₁]) (fun t ↦ by rw [Icc.coe_zero, hu₀, hγ₀])
    (fun t ↦ by rw [Icc.coe_one, hu₁, hγ₁])
  have hPu (s t : unitInterval) : Pu s t = u (s, t) := Path.ofContinuousFamily_apply _ _ _ _ _ _ s t
  exact ⟨u, hu, fun z ↦ by simp only [u, Int.fract_add_one], hu₀, hu₁, Pu, hPu,
    ((homotopic_loopModelPath hγ₀ hγ₁ hc₀ hc₁).trans
      (homotopic_loopModelPath_of_homotopyRel hγ₀ hγ₁ hc₀ hc₁ R hPu)).symm⟩

end Smoothing

end TauCeti
