/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Manifold.ContMDiff.RPow
public import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Conformal rescaling of Riemannian metrics

Multiplying a `C^n` Riemannian metric `g` on a vector bundle by a positive `C^n` function `f` on
the base gives another `C^n` Riemannian metric `f • g`, conformal to `g`. Many model metrics are
written this way: the upper half-space model of hyperbolic space is the Euclidean metric divided by
the square of the height, and the Poincaré ball model is the Euclidean metric multiplied by
`4 / (1 - ‖x‖²)²`.

Rescaling is an action of the multiplicative group of positive `C^n` functions: rescaling by `1`
does nothing, rescaling by `f` and then by `h` is rescaling by `h f`, and rescaling by `f⁻¹`
undoes rescaling by `f`. The *conformal class* `[g]` of `g` is the orbit of `g` under this action.
Conformality is therefore an equivalence relation, and two metrics have the same conformal class
exactly when they are conformal. On a bundle with nonzero fibres the conformal factor of a metric
in `[g]` is unique.

For every real `p ≠ 0`, the metrics in `[g]` are also exactly the metrics `u ^ p g` with `u` a
positive `C^n` function, and `u` is again unique on nonzero fibres; multiplying `u` by a constant
`c > 0` multiplies the metric by the constant `c ^ p`. On a manifold of dimension `N > 2` the
exponent `p = 4 / (N - 2)` gives the parametrization of a conformal class used in the Yamabe
problem, in which, classically, the scalar curvature of `u ^ p g` is expressed through the
conformal Laplacian of `g` applied to `u`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.rescale`: the rescaled metric `f • g`.
* `Bundle.ContMDiffRiemannianMetric.conformalClass`: the conformal class `[g]`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.rescale_one`,
  `Bundle.ContMDiffRiemannianMetric.rescale_rescale`,
  `Bundle.ContMDiffRiemannianMetric.rescale_inv_rescale`: the action laws of rescaling.
* `Bundle.ContMDiffRiemannianMetric.rescale_inj`: uniqueness of the conformal factor.
* `Bundle.ContMDiffRiemannianMetric.mem_conformalClass_comm`,
  `Bundle.ContMDiffRiemannianMetric.mem_conformalClass_trans`,
  `Bundle.ContMDiffRiemannianMetric.conformalClass_eq_conformalClass_iff`: conformality is an
  equivalence relation whose classes are the conformal classes.
* `Bundle.ContMDiffRiemannianMetric.mem_conformalClass_iff_exists_rpow`,
  `Bundle.ContMDiffRiemannianMetric.rescale_rpow_inj`,
  `Bundle.ContMDiffRiemannianMetric.rescale_const_mul_rpow`: the parametrization of `[g]` by real
  powers of positive functions, and its redundancy under constant factors.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (conformal metrics) and Chapter 3 (the models of hyperbolic space).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle Bornology
open scoped Manifold ContDiff

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The Riemannian metric `f • g` obtained by multiplying a `C^n` Riemannian metric `g` by a
positive `C^n` function `f` on the base. -/
def rescale (g : ContMDiffRiemannianMetric IB n F E) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf_pos : ∀ b, 0 < f b) :
    ContMDiffRiemannianMetric IB n F E where
  inner b := f b • g.inner b
  symm b v w := by
    simp only [smul_apply, g.symm b v w]
  pos b v hv := by
    simpa only [smul_apply, smul_eq_mul] using
      mul_pos (hf_pos b) (g.pos b v hv)
  isVonNBounded b := by
    -- The unit ball of `f b • g` is the unit ball of `g` scaled by `(√(f b))⁻¹`.
    set c := Real.sqrt (f b)
    have hc : 0 < c := Real.sqrt_pos.mpr (hf_pos b)
    refine ((g.isVonNBounded b).image (c⁻¹ • ContinuousLinearMap.id ℝ (E b))).subset ?_
    intro v hv
    refine ⟨c • v, ?_, by simp [smul_smul, mul_inv_cancel₀ hc.ne']⟩
    simp only [Set.mem_ofPred_eq, smul_apply, smul_eq_mul, map_smul] at hv ⊢
    calc c * (c * g.inner b v v) = f b * g.inner b v v := by
          rw [← mul_assoc, Real.mul_self_sqrt (hf_pos b).le]
      _ < 1 := hv
  contMDiff := hf.smul_section g.contMDiff

/-- The rescaled metric `f • g` is `f b` times `g` on the fibre over `b`. -/
@[simp]
theorem rescale_inner (g : ContMDiffRiemannianMetric IB n F E) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf_pos : ∀ b, 0 < f b) (b : B) (v w : E b) :
    (g.rescale f hf hf_pos).inner b v w = f b * g.inner b v w :=
  (rfl)

variable (g : ContMDiffRiemannianMetric IB n F E)
  {f : B → ℝ} {hf : ContMDiff IB 𝓘(ℝ) n f} {hf_pos : ∀ b, 0 < f b}

/-- Rescaling by the constant function `1` does not change the metric. -/
@[simp]
theorem rescale_one : g.rescale (fun _ ↦ 1) contMDiff_const (fun _ ↦ one_pos) = g := by
  ext b v w
  simp

/-- Rescaling `f g` by `h` is rescaling `g` by the product `h f`. -/
@[simp]
theorem rescale_rescale (h : B → ℝ) (hh : ContMDiff IB 𝓘(ℝ) n h) (hh_pos : ∀ b, 0 < h b) :
    (g.rescale f hf hf_pos).rescale h hh hh_pos =
      g.rescale (fun b ↦ h b * f b) (hh.mul hf) (fun b ↦ mul_pos (hh_pos b) (hf_pos b)) := by
  ext b v w
  simp [mul_assoc]

/-- Rescaling `f g` by `f⁻¹` gives back `g`. -/
theorem rescale_inv_rescale :
    (g.rescale f hf hf_pos).rescale (fun b ↦ (f b)⁻¹) (hf.inv₀ fun b ↦ (hf_pos b).ne')
      (fun b ↦ inv_pos.2 (hf_pos b)) = g := by
  ext b v w
  simp [inv_mul_cancel₀ (hf_pos b).ne']

/-- Rescaling `f⁻¹ g` by `f` gives back `g`. -/
theorem rescale_rescale_inv :
    (g.rescale (fun b ↦ (f b)⁻¹) (hf.inv₀ fun b ↦ (hf_pos b).ne')
      (fun b ↦ inv_pos.2 (hf_pos b))).rescale f hf hf_pos = g := by
  ext b v w
  simp [mul_inv_cancel₀ (hf_pos b).ne']

/-- On a bundle with nonzero fibres, the conformal factor of a rescaled metric is determined by
the metric: `f g = f' g` only if `f = f'`. -/
theorem rescale_inj [∀ b, Nontrivial (E b)] {f' : B → ℝ} {hf' : ContMDiff IB 𝓘(ℝ) n f'}
    {hf'_pos : ∀ b, 0 < f' b} :
    g.rescale f hf hf_pos = g.rescale f' hf' hf'_pos ↔ f = f' := by
  refine ⟨fun h ↦ funext fun b ↦ ?_, fun h ↦ by subst h; rfl⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : E b)
  have hb := congrArg (fun g' : ContMDiffRiemannianMetric IB n F E ↦ g'.inner b v v) h
  simp only [rescale_inner] at hb
  exact mul_right_cancel₀ (g.pos b v hv).ne' hb

/-- Rescalings by real powers `u ^ p`, `p ≠ 0`, of positive functions agree only for equal
functions, on a bundle with nonzero fibres. -/
theorem rescale_rpow_inj [∀ b, Nontrivial (E b)] {p : ℝ} (hp : p ≠ 0) {u u' : B → ℝ}
    {hu : ContMDiff IB 𝓘(ℝ) n fun b ↦ u b ^ p} {hu_pos : ∀ b, 0 < u b ^ p}
    {hu' : ContMDiff IB 𝓘(ℝ) n fun b ↦ u' b ^ p} {hu'_pos : ∀ b, 0 < u' b ^ p}
    (hu₀ : ∀ b, 0 ≤ u b) (hu'₀ : ∀ b, 0 ≤ u' b) :
    g.rescale (fun b ↦ u b ^ p) hu hu_pos = g.rescale (fun b ↦ u' b ^ p) hu' hu'_pos ↔
      u = u' := by
  refine (g.rescale_inj).trans ⟨fun h ↦ funext fun b ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← Real.rpow_rpow_inv (hu₀ b) hp, ← Real.rpow_rpow_inv (hu'₀ b) hp, congrFun h b]

/-- **Constant-factor redundancy.** Multiplying a positive function `u` by a constant `c > 0`
multiplies the rescaled metric `u ^ p g` by the constant `c ^ p`. -/
theorem rescale_const_mul_rpow {p c : ℝ} (hc : 0 < c) {u : B → ℝ} (hu₀ : ∀ b, 0 ≤ u b)
    {hcu : ContMDiff IB 𝓘(ℝ) n fun b ↦ (c * u b) ^ p} {hcu_pos : ∀ b, 0 < (c * u b) ^ p}
    {hu : ContMDiff IB 𝓘(ℝ) n fun b ↦ u b ^ p} {hu_pos : ∀ b, 0 < u b ^ p} :
    g.rescale (fun b ↦ (c * u b) ^ p) hcu hcu_pos =
      (g.rescale (fun b ↦ u b ^ p) hu hu_pos).rescale (fun _ ↦ c ^ p) contMDiff_const
        (fun _ ↦ Real.rpow_pos_of_pos hc p) := by
  ext b v w
  simp [Real.mul_rpow hc.le (hu₀ b), mul_assoc]

/-! ### The conformal class -/

/-- The conformal class `[g]` of a `C^n` Riemannian metric `g`: the set of metrics `f g`, for `f`
a positive `C^n` function on the base. -/
def conformalClass : Set (ContMDiffRiemannianMetric IB n F E) :=
  {g' | ∃ (f : B → ℝ) (hf : ContMDiff IB 𝓘(ℝ) n f) (hf_pos : ∀ b, 0 < f b),
    g' = g.rescale f hf hf_pos}

variable {g} {g' : ContMDiffRiemannianMetric IB n F E}

/-- Membership in the conformal class `[g]`: being `f g` for a positive `C^n` function `f`. -/
theorem mem_conformalClass_iff :
    g' ∈ g.conformalClass ↔ ∃ (f : B → ℝ) (hf : ContMDiff IB 𝓘(ℝ) n f) (hf_pos : ∀ b, 0 < f b),
      g' = g.rescale f hf hf_pos :=
  Iff.rfl

variable (g) in
/-- Every rescaling of `g` lies in the conformal class of `g`. -/
@[simp]
theorem rescale_mem_conformalClass : g.rescale f hf hf_pos ∈ g.conformalClass :=
  ⟨f, hf, hf_pos, rfl⟩

variable (g) in
/-- A metric lies in its own conformal class. -/
@[simp]
theorem self_mem_conformalClass : g ∈ g.conformalClass :=
  ⟨fun _ ↦ 1, contMDiff_const, fun _ ↦ one_pos, (g.rescale_one).symm⟩

/-- Conformality is symmetric. -/
theorem mem_conformalClass_comm : g' ∈ g.conformalClass ↔ g ∈ g'.conformalClass := by
  suffices ∀ g g' : ContMDiffRiemannianMetric IB n F E,
      g' ∈ g.conformalClass → g ∈ g'.conformalClass from ⟨this g g', this g' g⟩
  rintro g _ ⟨f, hf, hf_pos, rfl⟩
  exact ⟨_, _, _, (g.rescale_inv_rescale (hf := hf) (hf_pos := hf_pos)).symm⟩

/-- Conformality is transitive. -/
theorem mem_conformalClass_trans {g'' : ContMDiffRiemannianMetric IB n F E}
    (h : g' ∈ g.conformalClass) (h' : g'' ∈ g'.conformalClass) : g'' ∈ g.conformalClass := by
  obtain ⟨f, hf, hf_pos, rfl⟩ := h
  obtain ⟨f', hf', hf'_pos, rfl⟩ := h'
  rw [rescale_rescale]
  exact rescale_mem_conformalClass g

/-- Two metrics have the same conformal class exactly when they are conformal. -/
theorem conformalClass_eq_conformalClass_iff :
    g.conformalClass = g'.conformalClass ↔ g' ∈ g.conformalClass := by
  refine ⟨fun h ↦ h ▸ self_mem_conformalClass g', fun h ↦ Set.ext fun g'' ↦ ⟨fun h' ↦ ?_,
    fun h' ↦ mem_conformalClass_trans h h'⟩⟩
  exact mem_conformalClass_trans (mem_conformalClass_comm.1 h) h'

/-- A rescaled metric has the same conformal class as the original metric. -/
@[simp]
theorem conformalClass_rescale : (g.rescale f hf hf_pos).conformalClass = g.conformalClass :=
  (conformalClass_eq_conformalClass_iff.2 (rescale_mem_conformalClass g)).symm

/-- **Positive-function parametrization of the conformal class.** For every real `p ≠ 0`, the
metrics conformal to `g` are exactly the metrics `u ^ p g` with `u` a positive `C^n` function.
For a manifold of dimension `N > 2` and `p = 4 / (N - 2)` this is the parametrization of the
conformal class used in the Yamabe problem. -/
theorem mem_conformalClass_iff_exists_rpow {p : ℝ} (hp : p ≠ 0) :
    g' ∈ g.conformalClass ↔ ∃ (u : B → ℝ) (hu : ContMDiff IB 𝓘(ℝ) n u) (hu_pos : ∀ b, 0 < u b),
      g' = g.rescale (fun b ↦ u b ^ p) (hu.rpow_const_of_ne (fun b ↦ (hu_pos b).ne') p)
        (fun b ↦ Real.rpow_pos_of_pos (hu_pos b) p) := by
  refine ⟨?_, fun ⟨u, hu, hu_pos, h⟩ ↦ h ▸ rescale_mem_conformalClass g⟩
  rintro ⟨f, hf, hf_pos, rfl⟩
  refine ⟨fun b ↦ f b ^ p⁻¹, hf.rpow_const_of_ne (fun b ↦ (hf_pos b).ne') p⁻¹,
    fun b ↦ Real.rpow_pos_of_pos (hf_pos b) p⁻¹, ?_⟩
  ext b v w
  simp [Real.rpow_inv_rpow (hf_pos b).le hp]

end Bundle.ContMDiffRiemannianMetric
