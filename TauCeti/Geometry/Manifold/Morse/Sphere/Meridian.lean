/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import TauCeti.Geometry.Manifold.Morse.Sphere.Bott
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.Morse.Trajectory

/-!
# Gradient trajectories of functions of the height run along meridians

Let `h` be the height function on the unit sphere `Sⁿ` in the direction of a unit vector `v`
(`TauCeti.sphereHeight`), `φ : ℝ → ℝ` a `C²` function and `f = φ ∘ h`. The critical set of `f`
consists of the two poles and the latitudes `h = c` at the critical points `c` of `φ`
(`TauCeti.criticalPoints_comp_sphereHeight`); when `φ'' (c) ≠ 0` such a latitude is a Morse–Bott
critical submanifold (`TauCeti.Geometry.Manifold.Morse.Sphere.Bott`). This file follows the
negative gradient trajectories of `f` for a Riemannian metric on the sphere that is invariant under
the reflections in the hyperplanes containing `v`, such as the round metric, for which every
linear isometry acts by Riemannian isometries (`LinearIsometryEquiv.unitSphereRiemannianIsometry`).

* **Trajectories stay in a meridian plane.** For every vector `u ⊥ v`, the reflection `r_u` in
  the hyperplane `u^⊥` is an isometry fixing `f`, so it carries trajectories to trajectories.
  If `u` is also orthogonal to a point `x` of a trajectory, `r_u` fixes `x` and hence the whole
  trajectory (`TauCeti.IsLocalRiemannianIsometry.apply_eq_of_isMIntegralCurve_neg_mgradient`).
  Hence every point of the trajectory through `x` lies in the plane spanned by `v` and `x`
  (`IsMIntegralCurve.coe_mem_span_pair_of_neg_mgradient_comp_sphereHeight`).
* **Trajectories run along meridians.** If `x` is not critical, the trajectory never reaches a
  critical point, in particular not a pole, so it stays on the open half great circle from `v`
  to `-v` through `x`. On it a point is determined by its height `c`: it is
  `c v + √(1 - c²) w` for the unit vector `w` in the direction of `x - h(x) v`
  (`IsMIntegralCurve.coe_eq_of_neg_mgradient_comp_sphereHeight`).
* **Trajectories run between consecutive critical levels.** Suppose that `h(x)` lies in an
  interval `(c₁, c₂) ⊆ [-1, 1]` on which `φ' < 0`, and that `c₂` is a critical point of `φ` or
  `c₂ = 1`. Along the trajectory `f` decreases, so `h` increases, and the trajectory converges as
  `t → ∞` to the point `c₂ v + √(1 - c₂²) w` of the critical level `h = c₂` on its meridian
  (`IsMIntegralCurve.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg`). It is
  trapped in the compact arc of the meridian between the levels `c₁` and `c₂`, which contains only
  two critical points, so `TauCeti.IsMIntegralCurveOn.exists_tendsto_neg_mgradient` applies. The
  case `φ' > 0` follows by reversing `v`, and the limits as `t → -∞` by reversing time, which
  turns `f` into `-f`.

So the endpoints of the trajectory through a point `y` of a regular level `h = c`, with
`c₁ < c < c₂` between consecutive critical levels, are its images under the radial maps
`y ↦ cᵢ v + √(1 - cᵢ²) (y - c v) / √(1 - c²)` along the meridians. This is spelled out for the
two standard test functions of Morse–Bott complexes on the sphere, whose critical sets are
described in `TauCeti.Geometry.Manifold.Morse.Sphere.Bott`.

* **Two caps, `f = h²`.** The trajectory through a point of the open northern hemisphere comes
  from the north pole and converges to the point of the equator on its meridian, and
  symmetrically in the southern hemisphere.
* **Four critical levels, `f = b h - h³`.** With `a = √(b / 3)`, the trajectories run from the
  south pole to the latitude `h = -a`, from the latitude `h = a` to the latitude `h = -a`, and
  from the latitude `h = a` to the north pole, each along its meridian.

## Main results

* `IsMIntegralCurve.coe_mem_span_pair_of_neg_mgradient_comp_sphereHeight`: a trajectory stays in
  the plane spanned by `v` and any of its points.
* `IsMIntegralCurve.coe_eq_of_neg_mgradient_comp_sphereHeight`: a trajectory through a regular
  point stays on the open meridian arc through it.
* `IsMIntegralCurve.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg`,
  `IsMIntegralCurve.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_pos`,
  `IsMIntegralCurve.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_neg`,
  `IsMIntegralCurve.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_pos`: the limits of a
  trajectory between consecutive critical levels.
* `IsMIntegralCurve.tendsto_of_neg_mgradient_sq_comp_sphereHeight_of_pos`,
  `IsMIntegralCurve.tendsto_of_neg_mgradient_sq_comp_sphereHeight_of_neg`: the trajectories of
  `h²` run from a pole to the equator.
* `IsMIntegralCurve.tendsto_of_neg_mgradient_mul_sub_pow_three_comp_sphereHeight_of_lt_neg_sqrt`,
  `IsMIntegralCurve.tendsto_of_neg_mgradient_mul_sub_pow_three_comp_sphereHeight_of_mem_Ioo`,
  `IsMIntegralCurve.tendsto_of_neg_mgradient_mul_sub_pow_three_comp_sphereHeight_of_sqrt_lt`: the
  trajectories of `b h - h³` in its three regular bands.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (Morse–Bott trajectory spaces and their endpoint maps).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Bundle Filter Function Metric Module Set Submodule Topology TauCeti.Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### Points of the sphere in a meridian plane -/

section Plane

variable {v x y : sphere (0 : E) 1}

/-- A point `y` of the sphere in the plane spanned by `v` and `x` is `h y • v + b • w`, where
`w = x - h x • v` is orthogonal to `v` with `‖w‖² = 1 - h(x)²`; then `⟪y, w⟫ = b (1 - h(x)²)` and
`h(y)² + b² (1 - h(x)²) = 1`. -/
private theorem exists_eq_of_mem_span_pair (hy : (y : E) ∈ span ℝ {(v : E), (x : E)}) :
    ∃ b : ℝ, (y : E) = sphereHeight v y • (v : E) + b • ((x : E) - sphereHeight v x • (v : E)) ∧
      ⟪(y : E), (x : E) - sphereHeight v x • (v : E)⟫ = b * (1 - sphereHeight v x ^ 2) ∧
      sphereHeight v y ^ 2 + b ^ 2 * (1 - sphereHeight v x ^ 2) = 1 := by
  obtain ⟨a, b, hab⟩ := mem_span_pair.1 hy
  have hvv : ⟪(v : E), (v : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere _)
  have hxx : ⟪(x : E), (x : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere _)
  have hyy : ⟪(y : E), (y : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere _)
  have hxv : ⟪(x : E), (v : E)⟫ = sphereHeight v x := (sphereHeight_apply v x).symm
  have hvx : ⟪(v : E), (x : E)⟫ = sphereHeight v x := by rw [real_inner_comm, hxv]
  have hyv : sphereHeight v y = a + b * sphereHeight v x := by
    rw [sphereHeight_apply, ← hab, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hvv, hxv, mul_one]
  rw [← hab] at hyy
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hvv,
    hxx, hxv, hvx] at hyy
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hyv, ← hab]
    module
  · rw [← hab]
    simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hvv,
      hxx, hxv, hvx]
    ring
  · rw [hyv]
    linear_combination hyy

/-- A point `y` of the sphere in the plane spanned by `v` and a point `x` other than the poles, on
the side of `x` (`⟪y, x - h x • v⟫ ≥ 0`), is the point `c v + √(1 - c²) w` of height `c = h y` on
the meridian through `x`, where `w = (x - h x • v) / √(1 - h(x)²)` is a unit vector. -/
private theorem coe_eq_of_mem_span_pair (hx : sphereHeight v x ^ 2 < 1)
    (hy : (y : E) ∈ span ℝ {(v : E), (x : E)})
    (hyw : 0 ≤ ⟪(y : E), (x : E) - sphereHeight v x • (v : E)⟫) :
    (y : E) = sphereHeight v y • (v : E) + (√(1 - sphereHeight v y ^ 2) /
      √(1 - sphereHeight v x ^ 2)) • ((x : E) - sphereHeight v x • (v : E)) := by
  obtain ⟨b, hy', hyw', hnorm⟩ := exists_eq_of_mem_span_pair hy
  have hpos : 0 < 1 - sphereHeight v x ^ 2 := by linarith
  have hb : 0 ≤ b := by
    rw [hyw'] at hyw
    exact nonneg_of_mul_nonneg_left hyw hpos
  have hcoeff : √(1 - sphereHeight v y ^ 2) / √(1 - sphereHeight v x ^ 2) = b := by
    rw [show 1 - sphereHeight v y ^ 2 = b ^ 2 * (1 - sphereHeight v x ^ 2) by linarith,
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb, mul_div_assoc,
      div_self (Real.sqrt_pos.2 hpos).ne', mul_one]
  rw [hcoeff]
  exact hy'

/-- A point `y` of the sphere in the plane spanned by `v` and a point `x` other than the poles,
with `⟪y, x - h x • v⟫ = 0`, is a pole. -/
private theorem sphereHeight_sq_eq_one_of_mem_span_pair (hx : sphereHeight v x ^ 2 < 1)
    (hy : (y : E) ∈ span ℝ {(v : E), (x : E)})
    (hyw : ⟪(y : E), (x : E) - sphereHeight v x • (v : E)⟫ = 0) : sphereHeight v y ^ 2 = 1 := by
  obtain ⟨b, -, hyw', hnorm⟩ := exists_eq_of_mem_span_pair hy
  have hb : b = 0 := by
    rw [hyw] at hyw'
    rcases mul_eq_zero.1 hyw'.symm with h | h
    · exact h
    · linarith
  rw [hb] at hnorm
  linarith

end Plane

/-- A point which is not a critical point of `φ ∘ h` is not a pole. -/
private theorem sphereHeight_sq_lt_one_of_notMem_criticalPoints {φ : ℝ → ℝ} {v y : sphere (0 : E) 1}
    (hφ : Differentiable ℝ φ) (hy : y ∉ criticalPoints (𝓡 n) (φ ∘ sphereHeight v)) :
    sphereHeight v y ^ 2 < 1 := by
  rw [criticalPoints_comp_sphereHeight hφ] at hy
  have h₁ : sphereHeight v y ≠ 1 := fun h ↦ hy (Or.inr (by simp [sphereHeight_eq_one_iff.1 h]))
  have h₂ : sphereHeight v y ≠ -1 := fun h ↦
    hy (Or.inr (by simp [sphereHeight_eq_neg_one_iff.1 h]))
  have h₃ := lt_of_le_of_ne (sphereHeight_le_one v y) h₁
  have h₄ := lt_of_le_of_ne (neg_one_le_sphereHeight v y) h₂.symm
  nlinarith

/-- In a band `c₁ ≤ h ≤ c₂` inside `[-1, 1]` on whose interior `φ'` does not vanish, the critical
points of `φ ∘ h` lie on the two boundary levels. -/
private theorem sphereHeight_eq_or_eq_of_mem_criticalPoints {φ : ℝ → ℝ} {v y : sphere (0 : E) 1}
    {c₁ c₂ : ℝ} (hφ : Differentiable ℝ φ) (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c ≠ 0)
    (hy : y ∈ criticalPoints (𝓡 n) (φ ∘ sphereHeight v)) (hyI : sphereHeight v y ∈ Icc c₁ c₂) :
    sphereHeight v y = c₁ ∨ sphereHeight v y = c₂ := by
  by_contra! hne
  have hyI' : sphereHeight v y ∈ Ioo c₁ c₂ :=
    ⟨lt_of_le_of_ne hyI.1 hne.1.symm, lt_of_le_of_ne hyI.2 hne.2⟩
  rw [criticalPoints_comp_sphereHeight hφ] at hy
  rcases hy with hy | hy | hy
  · exact hderiv _ hyI' hy
  · rw [hy, sphereHeight_self] at hyI'
    linarith [hyI'.2]
  · rw [mem_singleton_iff.1 hy, sphereHeight_neg_self] at hyI'
    linarith [hyI'.1]

/-- A point strictly inside a band on whose interior `φ'` does not vanish is not a critical point
of `φ ∘ h`. -/
private theorem notMem_criticalPoints_of_sphereHeight_mem_Ioo {φ : ℝ → ℝ}
    {v y : sphere (0 : E) 1} {c₁ c₂ : ℝ} (hφ : Differentiable ℝ φ) (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c ≠ 0) (hy : sphereHeight v y ∈ Ioo c₁ c₂) :
    y ∉ criticalPoints (𝓡 n) (φ ∘ sphereHeight v) := fun hyc ↦ by
  rcases sphereHeight_eq_or_eq_of_mem_criticalPoints hφ hc₁ hc₂ hderiv hyc
    (Ioo_subset_Icc_self hy) with h | h
  · exact hy.1.ne' h
  · exact hy.2.ne h

/-- If `φ' < 0` on `(c₁, c₂)`, then `φ` is smaller at every point of `(c₁, c₂)` than at `c₁`. -/
private theorem apply_lt_apply_left_of_deriv_neg {φ : ℝ → ℝ} {c₁ c₂ y : ℝ} (hφ : Continuous φ)
    (hy : y ∈ Ioo c₁ c₂) (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c < 0) : φ y < φ c₁ :=
  strictAntiOn_of_deriv_neg (convex_Icc c₁ c₂) hφ.continuousOn
    (by simpa only [interior_Icc] using hderiv) ⟨le_rfl, (hy.1.trans hy.2).le⟩
    (Ioo_subset_Icc_self hy) hy.1

/-- The closed arc between the levels `c₁` and `c₂` of the meridian from `v` to `-v` through `x`. -/
private def meridianArc (v x : sphere (0 : E) 1) (c₁ c₂ : ℝ) : Set (sphere (0 : E) 1) :=
  {y | (y : E) ∈ span ℝ {(v : E), (x : E)} ∧
    0 ≤ ⟪(y : E), (x : E) - sphereHeight v x • (v : E)⟫ ∧ sphereHeight v y ∈ Icc c₁ c₂}

private theorem isCompact_meridianArc [FiniteDimensional ℝ E] (v x : sphere (0 : E) 1)
    (c₁ c₂ : ℝ) : IsCompact (meridianArc v x c₁ c₂) := by
  have h₁ : IsClosed {y : sphere (0 : E) 1 | (y : E) ∈ span ℝ {(v : E), (x : E)}} :=
    (span ℝ _).isClosed_of_finiteDimensional.preimage continuous_subtypeVal
  have h₂ : IsClosed {y : sphere (0 : E) 1 |
      0 ≤ ⟪(y : E), (x : E) - sphereHeight v x • (v : E)⟫} :=
    isClosed_le continuous_const (continuous_subtypeVal.inner continuous_const)
  have h₃ : IsClosed {y : sphere (0 : E) 1 | sphereHeight v y ∈ Icc c₁ c₂} :=
    isClosed_Icc.preimage (by
      rw [sphereHeight_eq_innerSL_comp]
      exact (innerSL ℝ (v : E)).continuous.comp continuous_subtypeVal)
  exact (h₁.inter (h₂.inter h₃)).isCompact

/-- In a band on whose interior `φ'` does not vanish, the meridian arc contains at most two
critical points of `φ ∘ h`, one on each boundary level. -/
private theorem finite_criticalPoints_inter_meridianArc {φ : ℝ → ℝ} {v x : sphere (0 : E) 1}
    {c₁ c₂ : ℝ} (hx : sphereHeight v x ^ 2 < 1) (hφ : Differentiable ℝ φ) (hc₁ : -1 ≤ c₁)
    (hc₂ : c₂ ≤ 1) (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c ≠ 0) :
    (criticalPoints (𝓡 n) (φ ∘ sphereHeight v) ∩ meridianArc v x c₁ c₂).Finite := by
  -- A point of the arc is determined by its height.
  have hsub (c : ℝ) : {y | y ∈ meridianArc v x c₁ c₂ ∧ sphereHeight v y = c}.Subsingleton := by
    intro y hy z hz
    apply Subtype.ext
    rw [coe_eq_of_mem_span_pair hx hy.1.1 hy.1.2.1, coe_eq_of_mem_span_pair hx hz.1.1 hz.1.2.1,
      hy.2, hz.2]
  refine ((hsub c₁).finite.union (hsub c₂).finite).subset ?_
  rintro y ⟨hyc, hyK⟩
  rcases sphereHeight_eq_or_eq_of_mem_criticalPoints hφ hc₁ hc₂ hderiv hyc hyK.2.2 with h | h
  · exact Or.inl ⟨hyK, h⟩
  · exact Or.inr ⟨hyK, h⟩

/-! ### Trajectories for a reflection-invariant metric -/

variable [RiemannianBundle (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)]
  [IsContMDiffRiemannianBundle (𝓡 n) 1 (EuclideanSpace ℝ (Fin n))
    (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)]
  {v : sphere (0 : E) 1} {φ : ℝ → ℝ} {γ : ℝ → sphere (0 : E) 1} {c₁ c₂ : ℝ}

/-- **Gradient trajectories of a function of the height stay in a meridian plane.** If the metric
is invariant under the reflections in the hyperplanes containing `v`, every point of a negative
gradient trajectory of `φ ∘ h` lies in the plane spanned by `v` and any other point of it. -/
theorem _root_.IsMIntegralCurve.coe_mem_span_pair_of_neg_mgradient_comp_sphereHeight
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (s t : ℝ) : (γ t : E) ∈ span ℝ {(v : E), (γ s : E)} := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [← (span ℝ {(v : E), (γ s : E)}).orthogonal_orthogonal, mem_orthogonal']
  intro u hu
  have hfix : ∀ y : E, ⟪u, y⟫ = 0 → (ℝ ∙ u)ᗮ.reflection y = y := fun y hy ↦
    (reflection_eq_self_iff y).2 (mem_orthogonal_singleton_iff_inner_right.2 hy)
  have huv : ⟪u, (v : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact (mem_orthogonal _ _).1 hu _ (subset_span (by simp))
  have hus : ⟪u, (γ s : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact (mem_orthogonal _ _).1 hu _ (subset_span (by simp))
  have hσf : ∀ y, (φ ∘ sphereHeight v) ((ℝ ∙ u)ᗮ.reflection.unitSphereEquiv y) =
      (φ ∘ sphereHeight v) y := fun y ↦ by
    simp only [comp_apply, sphereHeight_unitSphereEquiv (hfix _ huv)]
  have h := (hsymm u huv).apply_eq_of_isMIntegralCurve_neg_mgradient
    (hφ.comp_contMDiff (contMDiff_sphereHeight v)) hσf hγ (t₀ := s)
    (Subtype.ext (by rw [LinearIsometryEquiv.coe_unitSphereEquiv_apply]; exact hfix _ hus)) t
  rw [real_inner_comm]
  refine mem_orthogonal_singleton_iff_inner_right.1 ((reflection_eq_self_iff _).1 ?_)
  simpa only [LinearIsometryEquiv.coe_unitSphereEquiv_apply] using congrArg Subtype.val h

omit [IsContMDiffRiemannianBundle (𝓡 n) 1 (EuclideanSpace ℝ (Fin n))
  (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)] in
/-- The function `φ ∘ h` does not increase along its negative gradient trajectories. -/
private theorem antitone_comp_of_isMIntegralCurve
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v))) (hφ : ContDiff ℝ 2 φ) :
    Antitone ((φ ∘ sphereHeight v) ∘ γ) :=
  hγ.antitone_comp (fun _ ↦ (hφ.comp_contMDiff (contMDiff_sphereHeight v)).mdifferentiable
      two_ne_zero _) fun t ↦ by
    rw [Pi.neg_apply, mvfderiv_apply_neg_mgradient, neg_nonpos]
    positivity

/-- A gradient trajectory of `φ ∘ h` through a regular point never reaches a critical point. -/
private theorem notMem_criticalPoints_of_isMIntegralCurve
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v))) (hφ : ContDiff ℝ 2 φ)
    (h0 : γ 0 ∉ criticalPoints (𝓡 n) (φ ∘ sphereHeight v)) (t : ℝ) :
    γ t ∉ criticalPoints (𝓡 n) (φ ∘ sphereHeight v) := by
  intro ht
  have hz : (-mgradient (𝓡 n) (φ ∘ sphereHeight v)) (γ t) = 0 := by
    rw [Pi.neg_apply, neg_eq_zero, mgradient_eq_zero_iff]
    exact mem_criticalPoints.1 ht
  rw [hγ.apply_eq_of_eq_zero
    (contMDiff_neg_mgradient_one (hφ.comp_contMDiff (contMDiff_sphereHeight v))).contMDiffAt
    hz 0] at h0
  exact h0 ht

/-- A gradient trajectory of `φ ∘ h` through a regular point `x` stays on the side of `x` of the
line through the poles: `⟪γ t, x - h x • v⟫ > 0`. -/
private theorem inner_pos_of_isMIntegralCurve
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (h0 : γ 0 ∉ criticalPoints (𝓡 n) (φ ∘ sphereHeight v)) (t : ℝ) :
    0 < ⟪(γ t : E), (γ 0 : E) - sphereHeight v (γ 0) • (v : E)⟫ := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hx := sphereHeight_sq_lt_one_of_notMem_criticalPoints hφd h0
  -- The inner product is continuous in `t`, positive at `t = 0` and never zero, since it vanishes
  -- only at the poles.
  refine isPreconnected_univ.forall_lt_of_lt (continuousOn_const (c := (0 : ℝ)))
    (((continuous_subtypeVal.comp hγ.continuous).inner continuous_const).continuousOn)
    (Or.inr fun s _ hs ↦ ?_) (mem_univ 0) ?_ t (mem_univ t)
  · have h := sphereHeight_sq_eq_one_of_mem_span_pair hx
      (hγ.coe_mem_span_pair_of_neg_mgradient_comp_sphereHeight hsymm hφ 0 s) hs.symm
    exact (sphereHeight_sq_lt_one_of_notMem_criticalPoints hφd
      (notMem_criticalPoints_of_isMIntegralCurve hγ hφ h0 s)).ne h
  · have hxx : ⟪(γ 0 : E), (γ 0 : E)⟫ = 1 :=
      inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere _)
    simp only [comp_apply, inner_sub_right, real_inner_smul_right, hxx, ← sphereHeight_apply]
    linarith

/-- **Gradient trajectories of a function of the height run along meridians.** If the metric is
invariant under the reflections in the hyperplanes containing `v`, the negative gradient trajectory
of `φ ∘ h` through a regular point `x` stays on the open meridian arc through `x`: its point at
time `t` is `c v + √(1 - c²) w` with `c = h (γ t)`, where `w` is the unit vector in the direction
of `x - h(x) v`. -/
theorem _root_.IsMIntegralCurve.coe_eq_of_neg_mgradient_comp_sphereHeight
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (h0 : γ 0 ∉ criticalPoints (𝓡 n) (φ ∘ sphereHeight v)) (t : ℝ) :
    (γ t : E) = sphereHeight v (γ t) • (v : E) + (√(1 - sphereHeight v (γ t) ^ 2) /
      √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)) :=
  coe_eq_of_mem_span_pair
    (sphereHeight_sq_lt_one_of_notMem_criticalPoints (hφ.differentiable (by norm_num)) h0)
    (hγ.coe_mem_span_pair_of_neg_mgradient_comp_sphereHeight hsymm hφ 0 t)
    (inner_pos_of_isMIntegralCurve hγ hsymm hφ h0 t).le

/-- Forward in time, a gradient trajectory of `φ ∘ h` starting in a band `(c₁, c₂)` on which
`φ' < 0`, whose upper level `c₂` is critical, stays in that band: the height cannot drop to `c₁`,
where `φ ∘ h` is larger than at time `0`, and it cannot reach the critical level `c₂`. -/
private theorem sphereHeight_mem_Ioo_of_isMIntegralCurve
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v))) (hφ : ContDiff ℝ 2 φ)
    (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1) (h₀ : sphereHeight v (γ 0) ∈ Ioo c₁ c₂)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c < 0) (hcrit : c₂ = 1 ∨ deriv φ c₂ = 0) {t : ℝ}
    (ht : 0 ≤ t) : sphereHeight v (γ t) ∈ Ioo c₁ c₂ := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hx := notMem_criticalPoints_of_sphereHeight_mem_Ioo (n := n) hφd hc₁ hc₂
    (fun c hc ↦ (hderiv c hc).ne) h₀
  have hg : ContinuousOn (fun t ↦ sphereHeight v (γ t)) (Ici 0) :=
    ((contMDiff_sphereHeight (n := n) (m := 0) v).continuous.comp hγ.continuous).continuousOn
  refine ⟨isPreconnected_Ici.forall_lt_of_lt (continuousOn_const (c := c₁)) hg
    (Or.inr fun s hs hsc ↦ ?_) (mem_Ici.2 le_rfl) h₀.1 t ht, ?_⟩
  · -- `φ ∘ h` does not increase along `γ`, but `φ c₁ > φ (h (γ 0))`.
    have h₁ := apply_lt_apply_left_of_deriv_neg hφ.continuous h₀ hderiv
    have h₂ : (φ ∘ sphereHeight v) (γ s) ≤ (φ ∘ sphereHeight v) (γ 0) :=
      antitone_comp_of_isMIntegralCurve hγ hφ hs
    simp only [comp_apply, ← hsc] at h₂
    linarith
  · -- The level `c₂` consists of critical points, which `γ` never reaches.
    have hcrit₂ (y : sphere (0 : E) 1) (hy : sphereHeight v y = c₂) :
        y ∈ criticalPoints (𝓡 n) (φ ∘ sphereHeight v) := by
      rw [criticalPoints_comp_sphereHeight hφd]
      rcases hcrit with rfl | hc
      · exact Or.inr (Or.inl (sphereHeight_eq_one_iff.1 hy))
      · exact Or.inl (by simpa only [mem_preimage, mem_ofPred_eq, hy] using hc)
    exact isPreconnected_Ici.forall_lt_of_lt hg (continuousOn_const (c := c₂))
      (Or.inr fun s _ hs ↦ notMem_criticalPoints_of_isMIntegralCurve hγ hφ hx s (hcrit₂ _ hs))
      (mem_Ici.2 le_rfl) h₀.2 t ht

/-- **The forward limit of a gradient trajectory of a function of the height.** Let the metric be
invariant under the reflections in the hyperplanes containing `v`, let `-1 ≤ c₁ < c₂ ≤ 1` with
`φ' < 0` on `(c₁, c₂)`, and let `c₂` be a critical point of `φ` or `1`. The negative gradient
trajectory of `φ ∘ h` through a point `x` with `c₁ < h(x) < c₂` converges as `t → ∞` to the point
`c₂ v + √(1 - c₂²) w` of the critical level `h = c₂` on the meridian through `x`, where `w` is the
unit vector in the direction of `x - h(x) v`. -/
theorem _root_.IsMIntegralCurve.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1) (h₀ : sphereHeight v (γ 0) ∈ Ioo c₁ c₂)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c < 0) (hcrit : c₂ = 1 ∨ deriv φ c₂ = 0) :
    Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 (c₂ • (v : E) + (√(1 - c₂ ^ 2) /
      √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ) 2 (φ ∘ sphereHeight v) :=
    hφ.comp_contMDiff (contMDiff_sphereHeight v)
  have hderiv' (c : ℝ) (hc : c ∈ Ioo c₁ c₂) : deriv φ c ≠ 0 := (hderiv c hc).ne
  have hx := notMem_criticalPoints_of_sphereHeight_mem_Ioo (n := n) hφd hc₁ hc₂ hderiv' h₀
  have hx2 := sphereHeight_sq_lt_one_of_notMem_criticalPoints hφd hx
  -- Forward in time `γ` is trapped in the arc of its meridian between the levels `c₁` and `c₂`,
  -- which contains only finitely many critical points, so `γ` converges to one of them.
  have hmaps : MapsTo γ (Ici 0) (meridianArc v (γ 0) c₁ c₂) := fun t ht ↦
    ⟨hγ.coe_mem_span_pair_of_neg_mgradient_comp_sphereHeight hsymm hφ 0 t,
      (inner_pos_of_isMIntegralCurve hγ hsymm hφ hx t).le, Ioo_subset_Icc_self
        (sphereHeight_mem_Ioo_of_isMIntegralCurve hγ hφ hc₁ hc₂ h₀ hderiv hcrit ht)⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨p, ⟨hpc, hpK⟩, hlim⟩ := (hγ.isMIntegralCurveOn (Ici 0)).exists_tendsto_neg_mgradient hf
    (isCompact_meridianArc v (γ 0) c₁ c₂) hmaps
    (finite_criticalPoints_inter_meridianArc hx2 hφd hc₁ hc₂ hderiv')
  -- The limit is not on the level `c₁`, since `φ ∘ h` has not increased.
  have hp : sphereHeight v p = c₂ := by
    rcases sphereHeight_eq_or_eq_of_mem_criticalPoints hφd hc₁ hc₂ hderiv' hpc hpK.2.2 with h | h
    · have hFp : (φ ∘ sphereHeight v) p ≤ (φ ∘ sphereHeight v) (γ 0) :=
        le_of_tendsto ((hf.continuous.tendsto p).comp hlim)
          ((eventually_ge_atTop 0).mono fun t ht ↦ antitone_comp_of_isMIntegralCurve hγ hφ ht)
      have h₁ := apply_lt_apply_left_of_deriv_neg hφ.continuous h₀ hderiv
      simp only [comp_apply, h] at hFp
      linarith
    · exact h
  have hlim' := (continuous_subtypeVal.tendsto p).comp hlim
  rw [coe_eq_of_mem_span_pair hx2 hpK.1 hpK.2.1, hp] at hlim'
  exact hlim'

/-- **The forward limit of a gradient trajectory of a function of the height, increasing case.**
Let the metric be invariant under the reflections in the hyperplanes containing `v`, let
`-1 ≤ c₁ < c₂ ≤ 1` with `φ' > 0` on `(c₁, c₂)`, and let `c₁` be a critical point of `φ` or `-1`.
The negative gradient trajectory of `φ ∘ h` through a point `x` with `c₁ < h(x) < c₂` converges as
`t → ∞` to the point `c₁ v + √(1 - c₁²) w` of the critical level `h = c₁` on the meridian through
`x`, where `w` is the unit vector in the direction of `x - h(x) v`. -/
theorem _root_.IsMIntegralCurve.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_pos
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1) (h₀ : sphereHeight v (γ 0) ∈ Ioo c₁ c₂)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, 0 < deriv φ c) (hcrit : c₁ = -1 ∨ deriv φ c₁ = 0) :
    Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 (c₁ • (v : E) + (√(1 - c₁ ^ 2) /
      √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  -- Reverse the direction `v`: then `φ ∘ h = ψ ∘ h'` with `h' = -h` and `ψ c = φ (-c)`.
  have hfun : φ ∘ sphereHeight v = (fun c ↦ φ (-c)) ∘ sphereHeight (-v) := by
    funext y
    simp only [comp_apply, sphereHeight_neg, Pi.neg_apply, neg_neg]
  rw [hfun] at hγ
  have key := hγ.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg (c₁ := -c₂)
    (c₂ := -c₁) (fun u hu ↦ hsymm u (by simpa only [coe_neg_sphere, inner_neg_right,
      neg_eq_zero] using hu)) (hφ.comp contDiff_neg) (by linarith) (by linarith)
    (by simp only [sphereHeight_neg, Pi.neg_apply, mem_Ioo, neg_lt_neg_iff]; exact ⟨h₀.2, h₀.1⟩)
    (fun c hc ↦ by
      rw [deriv_comp_neg, neg_lt_zero]
      exact hderiv _ ⟨lt_neg_of_lt_neg hc.2, neg_lt.1 hc.1⟩)
    (by
      rcases hcrit with h | h
      · exact Or.inl (by rw [h, neg_neg])
      · exact Or.inr (by rw [deriv_comp_neg, neg_neg, h, neg_zero]))
  have hneg : ∀ y, sphereHeight (-v) y = -sphereHeight v y := fun y ↦ by
    rw [sphereHeight_neg, Pi.neg_apply]
  simpa only [hneg, coe_neg_sphere, neg_smul_neg, neg_sq] using key

omit [IsContMDiffRiemannianBundle (𝓡 n) 1 (EuclideanSpace ℝ (Fin n))
  (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)] in
/-- Reversing time turns a negative gradient trajectory of `φ ∘ h` into one of `(-φ) ∘ h`. -/
private theorem isMIntegralCurve_comp_neg
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v))) :
    IsMIntegralCurve (fun t ↦ γ (-t)) (-mgradient (𝓡 n) ((-φ) ∘ sphereHeight v)) := by
  rw [Pi.neg_comp]
  exact hγ.comp_neg_neg_mgradient

/-- **The backward limit of a gradient trajectory of a function of the height.** Under the
hypotheses of the decreasing case, but with `c₁` a critical point of `φ` or `-1`, the negative
gradient trajectory of `φ ∘ h` through `x` with `c₁ < h(x) < c₂` converges as `t → -∞` to the point
`c₁ v + √(1 - c₁²) w` of the level `h = c₁` on the meridian through `x`. -/
theorem _root_.IsMIntegralCurve.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_neg
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1) (h₀ : sphereHeight v (γ 0) ∈ Ioo c₁ c₂)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, deriv φ c < 0) (hcrit : c₁ = -1 ∨ deriv φ c₁ = 0) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (c₁ • (v : E) + (√(1 - c₁ ^ 2) /
      √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  -- Reversing time turns a trajectory of `-grad (φ ∘ h)` into one of `-grad ((-φ) ∘ h)`.
  have hγ' := isMIntegralCurve_comp_neg hγ
  have key := hγ'.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_pos hsymm hφ.neg hc₁
    hc₂ (by simpa only [neg_zero] using h₀)
    (fun c hc ↦ by rw [deriv.neg, neg_pos]; exact hderiv c hc)
    (by
      rcases hcrit with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [deriv.neg, h, neg_zero]))
  simp only [neg_zero] at key
  exact tendsto_comp_neg_atTop_iff.1 key

/-- **The backward limit of a gradient trajectory of a function of the height, increasing case.**
Under the hypotheses of the increasing case, but with `c₂` a critical point of `φ` or `1`, the
negative gradient trajectory of `φ ∘ h` through `x` with `c₁ < h(x) < c₂` converges as `t → -∞` to
the point `c₂ v + √(1 - c₂²) w` of the level `h = c₂` on the meridian through `x`. -/
theorem _root_.IsMIntegralCurve.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_pos
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) (φ ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hφ : ContDiff ℝ 2 φ) (hc₁ : -1 ≤ c₁) (hc₂ : c₂ ≤ 1) (h₀ : sphereHeight v (γ 0) ∈ Ioo c₁ c₂)
    (hderiv : ∀ c ∈ Ioo c₁ c₂, 0 < deriv φ c) (hcrit : c₂ = 1 ∨ deriv φ c₂ = 0) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (c₂ • (v : E) + (√(1 - c₂ ^ 2) /
      √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  have hγ' := isMIntegralCurve_comp_neg hγ
  have key := hγ'.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm hφ.neg hc₁
    hc₂ (by simpa only [neg_zero] using h₀)
    (fun c hc ↦ by rw [deriv.neg, neg_lt_zero]; exact hderiv c hc)
    (by
      rcases hcrit with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [deriv.neg, h, neg_zero]))
  simp only [neg_zero] at key
  exact tendsto_comp_neg_atTop_iff.1 key

/-! ### Two caps: the function `h²` -/

/-- **The trajectories of `h²` in the northern hemisphere run from the north pole to the
equator.** For a metric invariant under the reflections in the hyperplanes containing `v`, the
negative gradient trajectory of `h²` through a point `x` with `0 < h(x) < 1` converges to `v` as
`t → -∞`, and as `t → ∞` to the point `(x - h(x) v) / √(1 - h(x)²)` of the equator on the meridian
through `x`. -/
theorem _root_.IsMIntegralCurve.tendsto_of_neg_mgradient_sq_comp_sphereHeight_of_pos
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (h₀ : 0 < sphereHeight v (γ 0)) (h₁ : sphereHeight v (γ 0) < 1) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (v : E)) ∧
      Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 ((√(1 - sphereHeight v (γ 0) ^ 2))⁻¹ •
        ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  have hderiv (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) : 0 < deriv (fun t : ℝ ↦ t ^ 2) c := by
    simpa using mul_pos two_pos hc.1
  constructor
  · convert hγ.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_pos hsymm (by fun_prop)
      (by norm_num) le_rfl ⟨h₀, h₁⟩ hderiv (Or.inl rfl) using 2
    simp
  · convert hγ.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_pos hsymm (by fun_prop)
      (by norm_num) le_rfl ⟨h₀, h₁⟩ hderiv (Or.inr (by simp)) using 2
    simp

/-- **The trajectories of `h²` in the southern hemisphere run from the south pole to the
equator.** For a metric invariant under the reflections in the hyperplanes containing `v`, the
negative gradient trajectory of `h²` through a point `x` with `-1 < h(x) < 0` converges to `-v` as
`t → -∞`, and as `t → ∞` to the point `(x - h(x) v) / √(1 - h(x)²)` of the equator on the meridian
through `x`. -/
theorem _root_.IsMIntegralCurve.tendsto_of_neg_mgradient_sq_comp_sphereHeight_of_neg
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) ((fun t : ℝ ↦ t ^ 2) ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (h₀ : sphereHeight v (γ 0) < 0) (h₁ : -1 < sphereHeight v (γ 0)) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (-(v : E))) ∧
      Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 ((√(1 - sphereHeight v (γ 0) ^ 2))⁻¹ •
        ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  have hderiv (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 0) : deriv (fun t : ℝ ↦ t ^ 2) c < 0 := by
    simpa using mul_neg_of_pos_of_neg two_pos hc.2
  constructor
  · convert hγ.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm (by fun_prop)
      le_rfl (by norm_num) ⟨h₁, h₀⟩ hderiv (Or.inl rfl) using 2
    simp
  · convert hγ.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm (by fun_prop)
      le_rfl (by norm_num) ⟨h₁, h₀⟩ hderiv (Or.inr (by simp)) using 2
    simp

end TauCeti

/-! ### Four critical levels: the function `b h - h³` -/

namespace IsMIntegralCurve

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [RiemannianBundle (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)]
  [IsContMDiffRiemannianBundle (𝓡 n) 1 (EuclideanSpace ℝ (Fin n))
    (fun y : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) y)]
  {v : sphere (0 : E) 1} {γ : ℝ → sphere (0 : E) 1} {b : ℝ}

/-- **The trajectories of `b h - h³` below the lower critical latitude run from the south pole to
it.** For `0 ≤ b` put `a = √(b / 3)`. For a metric invariant under the reflections in the
hyperplanes containing `v`, the negative gradient trajectory of `b h - h³` through a point `x` with
`-1 < h(x) < -a` converges to `-v` as `t → -∞`, and as `t → ∞` to the point
`-a v + √(1 - a²) w` of the latitude `h = -a` on the meridian through `x`, where `w` is the unit
vector in the direction of `x - h(x) v`. -/
theorem tendsto_of_neg_mgradient_mul_sub_pow_three_comp_sphereHeight_of_lt_neg_sqrt
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hb : 0 ≤ b) (h₀ : -1 < sphereHeight v (γ 0)) (h₁ : sphereHeight v (γ 0) < -√(b / 3)) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (-(v : E))) ∧
      Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 (-√(b / 3) • (v : E) + (√(1 - b / 3) /
        √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  have ha := Real.sq_sqrt (div_nonneg hb (by norm_num : (0 : ℝ) ≤ 3))
  have ha₀ := Real.sqrt_nonneg (b / 3)
  have hderiv (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) (-√(b / 3))) :
      deriv (fun t : ℝ ↦ b * t - t ^ 3) c < 0 := by
    simp only [deriv_mul_sub_pow_three]
    nlinarith [hc.2]
  constructor
  · convert hγ.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm (by fun_prop)
      le_rfl (by linarith) ⟨h₀, h₁⟩ hderiv (Or.inl rfl) using 2
    simp
  · convert hγ.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm (by fun_prop)
      le_rfl (by linarith) ⟨h₀, h₁⟩ hderiv
      (Or.inr (deriv_mul_sub_pow_three_eq_zero_of_sq_eq (by rw [neg_sq, ha]))) using 4
    rw [neg_sq, ha]

/-- **The trajectories of `b h - h³` between the critical latitudes run from the upper to the
lower one.** For `b ≤ 3` put `a = √(b / 3)`. For a metric invariant under the reflections in the
hyperplanes containing `v`, the negative gradient trajectory of `b h - h³` through a point `x` with
`-a < h(x) < a` converges as `t → -∞` to the point `a v + √(1 - a²) w` of the latitude `h = a`,
and as `t → ∞` to the point `-a v + √(1 - a²) w` of the latitude `h = -a`, both on the meridian
through `x`, where `w` is the unit vector in the direction of `x - h(x) v`. -/
theorem tendsto_of_neg_mgradient_mul_sub_pow_three_comp_sphereHeight_of_mem_Ioo
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hb : b ≤ 3) (h₀ : sphereHeight v (γ 0) ∈ Ioo (-√(b / 3)) √(b / 3)) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (√(b / 3) • (v : E) + (√(1 - b / 3) /
        √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) ∧
      Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 (-√(b / 3) • (v : E) + (√(1 - b / 3) /
        √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) := by
  -- The interval `(-a, a)` is nonempty, so `b > 0`.
  have hb₀ : 0 ≤ b := by
    by_contra! h
    have : √(b / 3) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    linarith [h₀.1, h₀.2]
  have ha := Real.sq_sqrt (div_nonneg hb₀ (by norm_num : (0 : ℝ) ≤ 3))
  have ha₁ : √(b / 3) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hderiv (c : ℝ) (hc : c ∈ Ioo (-√(b / 3)) √(b / 3)) :
      0 < deriv (fun t : ℝ ↦ b * t - t ^ 3) c := by
    simp only [deriv_mul_sub_pow_three]
    nlinarith [hc.1, hc.2]
  constructor
  · convert hγ.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_pos hsymm (by fun_prop)
      (by linarith) ha₁ h₀ hderiv (Or.inr (deriv_mul_sub_pow_three_eq_zero_of_sq_eq ha)) using 4
    rw [ha]
  · convert hγ.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_pos hsymm (by fun_prop)
      (by linarith) ha₁ h₀ hderiv
      (Or.inr (deriv_mul_sub_pow_three_eq_zero_of_sq_eq (by rw [neg_sq, ha]))) using 4
    rw [neg_sq, ha]

/-- **The trajectories of `b h - h³` above the upper critical latitude run from it to the north
pole.** For `0 ≤ b` put `a = √(b / 3)`. For a metric invariant under the reflections in the
hyperplanes containing `v`, the negative gradient trajectory of `b h - h³` through a point `x` with
`a < h(x) < 1` converges as `t → -∞` to the point `a v + √(1 - a²) w` of the latitude `h = a` on
the meridian through `x`, where `w` is the unit vector in the direction of `x - h(x) v`, and to `v`
as `t → ∞`. -/
theorem tendsto_of_neg_mgradient_mul_sub_pow_three_comp_sphereHeight_of_sqrt_lt
    (hγ : IsMIntegralCurve γ (-mgradient (𝓡 n) ((fun t : ℝ ↦ b * t - t ^ 3) ∘ sphereHeight v)))
    (hsymm : ∀ u : E, ⟪u, (v : E)⟫ = 0 →
      IsLocalRiemannianIsometry (𝓡 n) (𝓡 n) (ℝ ∙ u)ᗮ.reflection.unitSphereEquiv)
    (hb : 0 ≤ b) (h₀ : √(b / 3) < sphereHeight v (γ 0)) (h₁ : sphereHeight v (γ 0) < 1) :
    Tendsto (fun t ↦ (γ t : E)) atBot (𝓝 (√(b / 3) • (v : E) + (√(1 - b / 3) /
        √(1 - sphereHeight v (γ 0) ^ 2)) • ((γ 0 : E) - sphereHeight v (γ 0) • (v : E)))) ∧
      Tendsto (fun t ↦ (γ t : E)) atTop (𝓝 (v : E)) := by
  have ha := Real.sq_sqrt (div_nonneg hb (by norm_num : (0 : ℝ) ≤ 3))
  have ha₀ := Real.sqrt_nonneg (b / 3)
  have hderiv (c : ℝ) (hc : c ∈ Ioo √(b / 3) 1) :
      deriv (fun t : ℝ ↦ b * t - t ^ 3) c < 0 := by
    simp only [deriv_mul_sub_pow_three]
    nlinarith [hc.1]
  constructor
  · convert hγ.tendsto_atBot_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm (by fun_prop)
      (by linarith) le_rfl ⟨h₀, h₁⟩ hderiv
      (Or.inr (deriv_mul_sub_pow_three_eq_zero_of_sq_eq ha)) using 4
    rw [ha]
  · convert hγ.tendsto_atTop_of_neg_mgradient_comp_sphereHeight_of_deriv_neg hsymm (by fun_prop)
      (by linarith) le_rfl ⟨h₀, h₁⟩ hderiv (Or.inl rfl) using 2
    simp

end IsMIntegralCurve
