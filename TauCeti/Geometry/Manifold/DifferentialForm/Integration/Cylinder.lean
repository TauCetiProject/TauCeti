/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

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

open Set Real MeasureTheory
open scoped Manifold Interval ContDiff Topology

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


variable (I) in
/-- A smooth cylinder from the loop `γ` to the loop `γ₀`: a smooth map `u : ℝ × ℝ → M` running
along `γ` at `s = 0` and along `γ₀` at `s = 1`, each loop being traversed over `t ∈ [0, 1]`,
with `u (s, 1) = u (s, 0)` for `s ∈ [0, 1]`. The start is prescribed for all `t`, so that two
cylinders from the same loop can be glued smoothly along it; the other conditions only concern
the unit square. When `γ₀` is constant, `u` is a cap of `γ`. -/
structure IsSmoothCylinder (γ γ₀ : ℝ → M) (u : ℝ × ℝ → M) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u
  apply_zero (t : ℝ) : u (0, t) = γ t
  apply_one : ∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = γ₀ t
  periodic : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)

/-- A two-form `φ` **vanishes on spheres** when its integral over the unit square vanishes for
every smooth map `u : ℝ × ℝ → M` that is constant on each of the two vertical edges of the square
and agrees on its two horizontal edges. Such a map factors through the sphere obtained from the
square by collapsing the vertical edges and identifying the horizontal ones; composing a smooth
map of the round sphere with spherical coordinates gives such a map. For a symplectic form this
formulates the area condition of symplectic asphericity on maps of the square. -/
def VanishesOnSpheres (φ : RoughForm I M F 2) : Prop :=
  ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
    (∀ t ∈ Icc (0 : ℝ) 1, u (0, t) = u (0, 0)) → (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (1, 0)) →
    (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0

/-- A two-form `φ` **vanishes on tori** when its integral over the unit square vanishes for every
smooth map `u : ℝ × ℝ → M` that agrees on opposite edges of the square, so that it factors
through the torus. For a symplectic form this formulates the area condition of symplectic
atoroidality on maps of the square. -/
def VanishesOnTori (φ : RoughForm I M F 2) : Prop :=
  ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
    (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (0, t)) →
    (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0

/-- Unfolding `TauCeti.VanishesOnSpheres`. -/
theorem vanishesOnSpheres_iff (φ : RoughForm I M F 2) :
    VanishesOnSpheres φ ↔ ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
      (∀ t ∈ Icc (0 : ℝ) 1, u (0, t) = u (0, 0)) → (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (1, 0)) →
      (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-- Unfolding `TauCeti.VanishesOnTori`. -/
theorem vanishesOnTori_iff (φ : RoughForm I M F 2) :
    VanishesOnTori φ ↔ ∀ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u →
      (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (0, t)) →
      (∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)) → rectangleIntegral φ u (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-! ### Gluing two cylinders along their common start -/

section Glue

variable {X : Type*} {u v : ℝ × ℝ → X}

/-- The map gluing `u` and `v` along their common start: on `[0, 1/2]` it runs backwards
through `u`, and on `[1/2, 1]` forwards through `v`, each reparametrized by a smooth transition
so that the glued map rests on the common loop for `s ∈ [1/3, 2/3]`. -/
private def glue (u v : ℝ × ℝ → X) (z : ℝ × ℝ) : X :=
  if z.1 ≤ 1 / 2 then u (smoothTransition (-3 * z.1 + 1), z.2)
  else v (smoothTransition (3 * z.1 + -2), z.2)

private theorem glue_of_le {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 2) :
    glue u v z = u (smoothTransition (-3 * z.1 + 1), z.2) := by
  simp only [glue, hz, ↓reduceIte]

private theorem glue_of_gt {z : ℝ × ℝ} (hz : 1 / 2 < z.1) :
    glue u v z = v (smoothTransition (3 * z.1 + -2), z.2) := by
  simp only [glue, hz.not_ge, ↓reduceIte]

private theorem glue_eq_left (h : ∀ t, u (0, t) = v (0, t)) {z : ℝ × ℝ} (hz : z.1 < 2 / 3) :
    glue u v z = u (smoothTransition (-3 * z.1 + 1), z.2) := by
  rcases le_or_gt z.1 (1 / 2) with hz' | hz'
  · exact glue_of_le hz'
  · rw [glue_of_gt hz', smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), h]

private theorem glue_eq_right (h : ∀ t, u (0, t) = v (0, t)) {z : ℝ × ℝ} (hz : 1 / 3 < z.1) :
    glue u v z = v (smoothTransition (3 * z.1 + -2), z.2) := by
  rcases le_or_gt z.1 (1 / 2) with hz' | hz'
  · rw [glue_of_le hz', smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), h]
  · exact glue_of_gt hz'

private theorem glue_zero (t : ℝ) : glue u v (0, t) = u (1, t) := by
  rw [glue_of_le (by norm_num)]
  norm_num

private theorem glue_one (t : ℝ) : glue u v (1, t) = v (1, t) := by
  rw [glue_of_gt (by norm_num)]
  norm_num

private theorem glue_periodic (hu : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0))
    (hv : ∀ s ∈ Icc (0 : ℝ) 1, v (s, 1) = v (s, 0)) (s : ℝ) :
    glue u v (s, 1) = glue u v (s, 0) := by
  simp only [glue]
  split_ifs
  · exact hu _ ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · exact hv _ ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

/-- The reparametrizations used in the gluing are smooth. -/
private theorem contDiff_smoothTransition_affine {n : ℕ∞} (c d : ℝ) :
    ContDiff ℝ n fun s : ℝ ↦ smoothTransition (c * s + d) :=
  smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

variable {u v : ℝ × ℝ → M}

private theorem contMDiff_glue {n : ℕ∞} (h : ∀ t, u (0, t) = v (0, t))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n v) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (glue u v) := by
  -- Near a point with `s < 2/3` the glued map is a reparametrization of `u`, and near a point
  -- with `s > 1/3` it is a reparametrization of `v`.
  have hcomp {w : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n w) (c d : ℝ) :
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I n fun z : ℝ × ℝ ↦ w (smoothTransition (c * z.1 + d), z.2) :=
    hw.comp (((contDiff_smoothTransition_affine c d).comp contDiff_fst).prodMk
      contDiff_snd).contMDiff
  intro z
  rcases lt_or_ge z.1 (2 / 3) with hz | hz
  · refine (hcomp hu (-3) 1 z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with w hw
    exact glue_eq_left h hw
  · have hz' : (1 / 3 : ℝ) < z.1 := by linarith
    refine (hcomp hv 3 (-2) z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hz'] with w hw
    exact glue_eq_right h hw

/-- The integral over the glued map is the integral over `v` minus the integral over `u`. -/
private theorem rectangleIntegral_glue [IsManifold I 1 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ) (h : ∀ t, u (0, t) = v (0, t))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) :
    rectangleIntegral φ (glue u v) (0, 0) (1, 1) =
      rectangleIntegral φ v (0, 0) (1, 1) - rectangleIntegral φ u (0, 0) (1, 1) := by
  -- A reparametrization `s ↦ smoothTransition (c * s + d)` of the first coordinate.
  have hreparam {w : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w) (c d : ℝ) (a b : ℝ × ℝ) :
      rectangleIntegral φ (w ∘ Prod.map (fun s ↦ smoothTransition (c * s + d)) id) a b =
        rectangleIntegral φ w (smoothTransition (c * a.1 + d), a.2)
          (smoothTransition (c * b.1 + d), b.2) :=
    rectangleIntegral_comp_prodMap hφ hw
      (fun s _ ↦ ((contDiff_smoothTransition_affine (n := 1) c d).differentiable
        one_ne_zero s).hasDerivAt)
      ((contDiff_smoothTransition_affine (n := 1) c d).continuous_deriv le_rfl).continuousOn
  rw [← rectangleIntegral_add_adjacent hφ (contMDiff_glue h hu hv) (0, 0) (1 / 2) (1, 1)]
  -- On `[0, 1/2]` the glued map runs backwards through `u`, on `[1/2, 1]` forwards through `v`.
  have hl : rectangleIntegral φ (glue u v) (0, 0) (1 / 2, 1) =
      -rectangleIntegral φ u (0, 0) (1, 1) := by
    have heq : EqOn (glue u v) (u ∘ Prod.map (fun s ↦ smoothTransition (-3 * s + 1)) id)
        ([[(0 : ℝ), 1 / 2]] ×ˢ [[(0 : ℝ), 1]]) := by
      intro z hz
      rw [uIcc_of_le (by norm_num)] at hz
      exact glue_of_le hz.1.2
    rw [rectangleIntegral_congr heq, hreparam hu, ← rectangleIntegral_symm_fst]
    norm_num
    rw [smoothTransition.zero_of_nonpos (by norm_num)]
  have hr : rectangleIntegral φ (glue u v) (1 / 2, 0) (1, 1) =
      rectangleIntegral φ v (0, 0) (1, 1) := by
    have heq : EqOn (glue u v) (v ∘ Prod.map (fun s ↦ smoothTransition (3 * s + -2)) id)
        ([[(1 / 2 : ℝ), 1]] ×ˢ [[(0 : ℝ), 1]]) := by
      intro z hz
      rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)] at hz
      exact glue_eq_right h (by linarith [hz.1.1])
    rw [rectangleIntegral_congr heq, hreparam hv]
    norm_num
    rw [smoothTransition.zero_of_nonpos (by norm_num)]
  rw [hl, hr]
  abel

end Glue

/-! ### Independence of the cylinder -/

section Independence

variable [IsManifold I 1 M] {φ : RoughForm I M F 2} {γ γ₀ : ℝ → M}
  {u v : ℝ × ℝ → M}

/-- **Independence of the cap.** A continuous two-form that vanishes on spheres has the same
integral over any two caps of a loop, even if they end at different points. -/
theorem VanishesOnSpheres.rectangleIntegral_eq (hS : VanishesOnSpheres φ)
    (hφ : IsSmoothForm I 0 φ) {x y : M} (hu : IsSmoothCylinder I γ (fun _ ↦ x) u)
    (hv : IsSmoothCylinder I γ (fun _ ↦ y) v) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  have h t : u (0, t) = v (0, t) := (hu.apply_zero t).trans (hv.apply_zero t).symm
  have hglue := hS (glue u v) (contMDiff_glue h hu.contMDiff hv.contMDiff)
    (fun t ht ↦ by rw [glue_zero, glue_zero, hu.apply_one t ht, hu.apply_one 0 (by simp)])
    (fun t ht ↦ by rw [glue_one, glue_one, hv.apply_one t ht, hv.apply_one 0 (by simp)])
    (fun s _ ↦ glue_periodic hu.periodic hv.periodic s)
  rw [rectangleIntegral_glue hφ h (hu.contMDiff.of_le (by simp))
    (hv.contMDiff.of_le (by simp)), sub_eq_zero] at hglue
  exact hglue.symm

/-- **Independence of the cylinder.** A continuous two-form that vanishes on tori has the same
integral over any two cylinders from a loop `γ` to a loop `γ₀`. -/
theorem VanishesOnTori.rectangleIntegral_eq (hT : VanishesOnTori φ) (hφ : IsSmoothForm I 0 φ)
    (hu : IsSmoothCylinder I γ γ₀ u) (hv : IsSmoothCylinder I γ γ₀ v) :
    rectangleIntegral φ u (0, 0) (1, 1) = rectangleIntegral φ v (0, 0) (1, 1) := by
  have h t : u (0, t) = v (0, t) := (hu.apply_zero t).trans (hv.apply_zero t).symm
  have hglue := hT (glue u v) (contMDiff_glue h hu.contMDiff hv.contMDiff)
    (fun t ht ↦ by rw [glue_zero, glue_one, hu.apply_one t ht, hv.apply_one t ht])
    (fun s _ ↦ glue_periodic hu.periodic hv.periodic s)
  rw [rectangleIntegral_glue hφ h (hu.contMDiff.of_le (by simp))
    (hv.contMDiff.of_le (by simp)), sub_eq_zero] at hglue
  exact hglue.symm

end Independence

/-! ### Exact forms -/

section Exact

variable [IsManifold I 2 M] {α : RoughForm I M F 1}

/-- Exact two-forms vanish on spheres: by Stokes' formula the integral over a sphere is the sum
of the line integrals along its edges, which vanish on the collapsed vertical edges and cancel on
the identified horizontal ones. -/
theorem vanishesOnSpheres_mextDeriv (hα : IsSmoothForm I 1 α) :
    VanishesOnSpheres (mextDeriv α) := by
  intro u hu h₀ h₁ hp
  have hI : uIoo (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoo_of_le zero_le_one]
    exact Ioo_subset_Icc_self
  rw [rectangleIntegral_mextDeriv hα (hu.of_le (by simp))]
  dsimp only
  rw [pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (1, t)) (γ' := fun _ ↦ u (1, 0))
      fun t ht ↦ h₁ t (hI ht),
    pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (0, t)) (γ' := fun _ ↦ u (0, 0))
      fun t ht ↦ h₀ t (hI ht),
    pathIntegral_congr_of_eqOn_uIoo (γ := fun s ↦ u (s, 1)) (γ' := fun s ↦ u (s, 0))
      fun s hs ↦ hp s (hI hs)]
  simp

/-- Exact two-forms vanish on tori: by Stokes' formula the integral over a torus is the sum of the
line integrals along its edges, which cancel on opposite edges. -/
theorem vanishesOnTori_mextDeriv (hα : IsSmoothForm I 1 α) : VanishesOnTori (mextDeriv α) := by
  intro u hu h₁ hp
  have hI : uIoo (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoo_of_le zero_le_one]
    exact Ioo_subset_Icc_self
  rw [rectangleIntegral_mextDeriv hα (hu.of_le (by simp))]
  dsimp only
  rw [pathIntegral_congr_of_eqOn_uIoo (γ := fun t ↦ u (1, t)) (γ' := fun t ↦ u (0, t))
      fun t ht ↦ h₁ t (hI ht),
    pathIntegral_congr_of_eqOn_uIoo (γ := fun s ↦ u (s, 1)) (γ' := fun s ↦ u (s, 0))
      fun s hs ↦ hp s (hI hs)]
  simp

end Exact

end TauCeti
