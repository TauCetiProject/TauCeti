/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Basic
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm

/-!
# The second fundamental form of a surface of revolution

For the profile `(f(v), g(v))`, the normal `(-g' cos u, -g' sin u, f')` has squared
length `f'² + g'²`. Pairing the native second fundamental form with this normal gives
the angular coefficient `f g'` and the meridional coefficient `f' g'' - g' f''`.
The normal is deliberately not normalized, avoiding square roots in the coordinate formulas.
All smoothness assumptions are local; the height derivative is allowed to vanish.

## References

* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Chapter 3.
-/

public noncomputable section

open scoped ContDiff InnerProductSpace Topology

namespace TauCeti.SurfaceOfRevolution

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The profile normal `(-g' cos u, -g' sin u, f')`, whose length is the profile speed.
At differentiability points of nonzero radius, it is the cross product of the profile
and angular directions, in that order, divided by the radius. -/
def profileNormal (f g : ℝ → ℝ) (p : ℝ × ℝ) : E₃ :=
  (-deriv g p.2 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (-deriv g p.2 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    deriv f p.2 • EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The Euclidean coordinate expression for the profile normal. -/
theorem profileNormal_def (f g : ℝ → ℝ) (p : ℝ × ℝ) :
    profileNormal f g p =
      (-deriv g p.2 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (-deriv g p.2 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      deriv f p.2 • EuclideanSpace.basisFun (Fin 3) ℝ 2 := (rfl)

/-- The profile normal has squared length equal to the squared profile speed. -/
theorem inner_profileNormal_self (f g : ℝ → ℝ) (p : ℝ × ℝ) :
    inner ℝ (profileNormal f g p) (profileNormal f g p) = profileSpeedSq f g p.2 := by
  simp only [profileNormal, profileSpeedSq_def, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]
  norm_num
  linear_combination deriv g p.2 ^ 2 * Real.sin_sq_add_cos_sq p.1

/-- The profile normal is orthogonal to every tangent vector of the parametrization. -/
@[simp]
theorem inner_profileNormal_fderiv_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (w : ℝ × ℝ) : inner ℝ (profileNormal f g p) (fderiv ℝ (parametrization f g) p w) = 0 := by
  by_cases h : DifferentiableAt ℝ (parametrization f g) p
  swap
  · simp [fderiv_zero_of_not_differentiableAt h]
  obtain ⟨hf, hg⟩ := differentiableAt_parametrization_iff.mp h
  rw [fderiv_parametrization hf hg]
  simp only [profileNormal, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]
  norm_num
  linear_combination -deriv f p.2 * deriv g p.2 * w.2 * Real.sin_sq_add_cos_sq p.1

/-- The explicit profile normal lies in the native normal space of the parametrization. -/
@[simp]
theorem profileNormal_mem_orthogonal_range_fderiv_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    : profileNormal f g p ∈ (fderiv ℝ (parametrization f g) p).rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨w, rfl⟩
  rw [real_inner_comm]
  exact inner_profileNormal_fderiv_parametrization w

/-- The second derivative in arbitrary angular and profile directions. -/
theorem fderiv_fderiv_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p.2) (hg : ContDiffAt ℝ 2 g p.2) (w z : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (parametrization f g)) p w z =
      (deriv (deriv f) p.2 * w.2 * z.2 * Real.cos p.1 -
        deriv f p.2 * (w.1 * z.2 + w.2 * z.1) * Real.sin p.1 -
        f p.2 * w.1 * z.1 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (deriv (deriv f) p.2 * w.2 * z.2 * Real.sin p.1 +
        deriv f p.2 * (w.1 * z.2 + w.2 * z.1) * Real.cos p.1 -
        f p.2 * w.1 * z.1 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      (deriv (deriv g) p.2 * w.2 * z.2) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  let D : (ℝ × ℝ) → E₃ := fun q ↦
    (deriv f q.2 * z.2 * Real.cos q.1 - f q.2 * Real.sin q.1 * z.1) •
      EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (deriv f q.2 * z.2 * Real.sin q.1 + f q.2 * Real.cos q.1 * z.1) •
      EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    (deriv g q.2 * z.2) • EuclideanSpace.basisFun (Fin 3) ℝ 2
  have heq : (fun q ↦ fderiv ℝ (parametrization f g) q z) =ᶠ[𝓝 p] D := by
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually (hf.eventually (by simp)),
      continuous_snd.continuousAt.tendsto.eventually (hg.eventually (by simp))] with q hqf hqg
    exact fderiv_parametrization (hqf.differentiableAt (by norm_num))
      (hqg.differentiableAt (by norm_num)) z
  have hf' := hf.differentiableAt (by norm_num)
  have hff := (hf.derivWithin (by norm_num : 1 + 1 ≤ (2 : ℕ∞ω))).differentiableAt (by norm_num)
  have hgg := (hg.derivWithin (by norm_num : 1 + 1 ≤ (2 : ℕ∞ω))).differentiableAt (by norm_num)
  have ha := hf'.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have hb := hff.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have hc := hgg.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have hcos := (Real.hasDerivAt_cos p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hsin := (Real.hasDerivAt_sin p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hd : HasFDerivAt D _ p :=
    (((((hb.mul_const z.2).mul hcos).sub ((ha.mul hsin).mul_const z.1)).smul_const
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)).add
      ((((hb.mul_const z.2).mul hsin).add ((ha.mul hcos).mul_const z.1)).smul_const
        (EuclideanSpace.basisFun (Fin 3) ℝ 1))).add
      ((hc.mul_const z.2).smul_const (EuclideanSpace.basisFun (Fin 3) ℝ 2))
  have hactual := (contDiffAt_parametrization hf hg).hasFDerivAt_fderiv_apply
    (by norm_num) z
  have hid := congrArg (fun a ↦ a w) (hactual.fderiv.symm.trans (heq.fderiv_eq.trans hd.fderiv))
  simp only [ContinuousLinearMap.flip_apply, add_apply,
    sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_apply,
    Function.comp_apply, smul_eq_mul] at hid
  rw [hid]
  module

/-- Pairing the native second fundamental form with the profile normal gives its two
diagonal coefficients; the mixed angular-meridional coefficient vanishes. -/
theorem inner_profileNormal_secondFundamentalForm_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p.2) (hg : ContDiffAt ℝ 2 g p.2) (w z : ℝ × ℝ) :
    inner ℝ (profileNormal f g p) (TauCeti.secondFundamentalForm ℝ
      (parametrization f g) p w z) =
      f p.2 * deriv g p.2 * w.1 * z.1 +
        (deriv f p.2 * deriv (deriv g) p.2 - deriv g p.2 * deriv (deriv f) p.2) *
          w.2 * z.2 := by
  rw [TauCeti.inner_secondFundamentalForm_apply_of_mem_orthogonal
    profileNormal_mem_orthogonal_range_fderiv_parametrization, fderiv_fderiv_parametrization hf hg]
  simp only [profileNormal, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]
  norm_num
  linear_combination
    (f p.2 * deriv g p.2 * w.1 * z.1 -
      deriv g p.2 * deriv (deriv f) p.2 * w.2 * z.2) * Real.sin_sq_add_cos_sq p.1

/-- At a regular profile point of nonzero radius the profile normal spans the whole native
normal space. -/
theorem orthogonal_range_fderiv_parametrization_eq_span_profileNormal {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2)
    (hr : f p.2 ≠ 0) (hs : 0 < profileSpeedSq f g p.2) :
    (fderiv ℝ (parametrization f g) p).rangeᗮ =
      Submodule.span ℝ {profileNormal f g p} := by
  have hn : profileNormal f g p ≠ 0 := by
    intro h
    have hi := inner_profileNormal_self f g p
    rw [h, inner_zero_left] at hi
    linarith
  have hdim := (fderiv ℝ (parametrization f g) p).range.finrank_add_finrank_orthogonal
  have hrank := LinearMap.finrank_range_of_inj
    (injective_fderiv_parametrization hf hg hr hs)
  norm_num [Module.finrank_prod] at hdim hrank
  exact eq_span_singleton_of_mem_of_finrank_eq_one (by omega)
    profileNormal_mem_orthogonal_range_fderiv_parametrization hn

/-- The native second fundamental form in revolution coordinates. -/
theorem secondFundamentalForm_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f p.2) (hg : ContDiffAt ℝ 2 g p.2)
    (hr : f p.2 ≠ 0) (hs : 0 < profileSpeedSq f g p.2) (w z : ℝ × ℝ) :
    TauCeti.secondFundamentalForm ℝ (parametrization f g) p w z =
      ((f p.2 * deriv g p.2 * w.1 * z.1 +
        (deriv f p.2 * deriv (deriv g) p.2 - deriv g p.2 * deriv (deriv f) p.2) *
          w.2 * z.2) / profileSpeedSq f g p.2) • profileNormal f g p := by
  have hm := TauCeti.secondFundamentalForm_apply_mem_orthogonal (𝕜 := ℝ)
    (parametrization f g) p w z
  rw [orthogonal_range_fderiv_parametrization_eq_span_profileNormal
    (hf.differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num)) hr hs] at hm
  have hp := Submodule.starProjection_eq_self_iff.mpr hm
  rw [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq,
    inner_profileNormal_self, inner_profileNormal_secondFundamentalForm_parametrization hf hg] at hp
  exact hp.symm

end TauCeti.SurfaceOfRevolution
