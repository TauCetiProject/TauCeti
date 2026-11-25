/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Helicoid.Basic
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm

/-!
# The second fundamental form of a helicoid

The unnormalized normal `N=(-a sin u, a cos u, -v)` has squared length `a²+v²`.
The second fundamental form is `a/(a²+v²) (du⊗dv+dv⊗du) N`, so its diagonal
coefficients vanish. All formulas include the axis for nonzero pitch.
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Helicoid

local notation "P" => ℝ × ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The unnormalized helicoid normal in the ordered angular and radial coordinates. -/
def normal (a : ℝ) (p : P) : E₃ :=
  (-a * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (a * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 -
    p.2 • EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The normal has squared length `a²+v²`. -/
theorem inner_normal_self (a : ℝ) (p : P) :
    inner ℝ (normal a p) (normal a p) = a ^ 2 + p.2 ^ 2 := by
  simp only [normal, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]
  norm_num
  linear_combination a ^ 2 * Real.sin_sq_add_cos_sq p.1

/-- The explicit normal is orthogonal to every helicoid tangent vector. -/
theorem inner_normal_fderiv (a : ℝ) (p w : P) :
    inner ℝ (normal a p) (fderiv ℝ (parametrization a) p w) = 0 := by
  rw [fderiv_parametrization]
  simp only [normal, inner_sub_left, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]
  norm_num
  linear_combination a * p.2 * w.1 * Real.sin_sq_add_cos_sq p.1

/-- The explicit normal belongs to the differential's orthogonal complement. -/
theorem normal_mem_orthogonal (a : ℝ) (p : P) :
    normal a p ∈ (fderiv ℝ (parametrization a) p).rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨w, rfl⟩
  rw [real_inner_comm]
  exact inner_normal_fderiv a p w

/-- The affine height term has zero Hessian, leaving the Hessian of planar polar coordinates. -/
theorem fderiv_fderiv_parametrization (a : ℝ) (p w z : P) :
    fderiv ℝ (fderiv ℝ (parametrization a)) p w z =
      (-(w.1 * z.2 + w.2 * z.1) * Real.sin p.1 -
        p.2 * w.1 * z.1 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      ((w.1 * z.2 + w.2 * z.1) * Real.cos p.1 -
        p.2 * w.1 * z.1 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 := by
  have hcos := (Real.hasDerivAt_cos p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hsin := (Real.hasDerivAt_sin p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hrad := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  have hderiv :=
    ((hcos.mul_const z.2).sub ((hrad.mul hsin).mul_const z.1)).smul_const
      (EuclideanSpace.basisFun (Fin 3) ℝ 0) |>.add
    (((hsin.mul_const z.2).add ((hrad.mul hcos).mul_const z.1)).smul_const
      (EuclideanSpace.basisFun (Fin 3) ℝ 1)) |>.add_const
    ((a * z.1) • EuclideanSpace.basisFun (Fin 3) ℝ 2)
  have hD : HasFDerivAt (fun q ↦ fderiv ℝ (parametrization a) q z) _ p :=
    hderiv.congr_of_eventuallyEq (.of_forall fun q ↦ by
      simp [fderiv_parametrization, mul_comm z.2])
  have hcont : ContDiffAt ℝ 2 (parametrization a) p :=
    (contDiff_parametrization a).contDiffAt
  have hactual := hcont.hasFDerivAt_fderiv_apply (by norm_num) z
  have hh := congrArg (fun L ↦ L w) (hactual.fderiv.symm.trans hD.fderiv)
  rw [ContinuousLinearMap.flip_apply] at hh
  rw [hh]
  simp only [add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, Function.comp_apply, smul_eq_mul]
  module

/-- Pairing the second fundamental form with the normal leaves precisely the mixed coefficient. -/
theorem inner_normal_secondFundamentalForm (a : ℝ) (p w z : P) :
    inner ℝ (normal a p) (TauCeti.secondFundamentalForm ℝ (parametrization a) p w z) =
      a * (w.1 * z.2 + w.2 * z.1) := by
  rw [TauCeti.inner_secondFundamentalForm_apply_of_mem_orthogonal
    (normal_mem_orthogonal a p), fderiv_fderiv_parametrization]
  simp only [normal, inner_sub_left, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left]
  norm_num
  linear_combination a * (w.1 * z.2 + w.2 * z.1) * Real.sin_sq_add_cos_sq p.1

/-- At a regular parameter the normal spans the entire orthogonal normal space. -/
theorem orthogonal_range_fderiv_eq_span_normal {a : ℝ} (p : P) (hreg : a ≠ 0 ∨ p.2 ≠ 0) :
    (fderiv ℝ (parametrization a) p).rangeᗮ = Submodule.span ℝ {normal a p} := by
  have hn : normal a p ≠ 0 := by
    intro h
    have hi := inner_normal_self a p
    rw [h, inner_zero_left] at hi
    obtain ⟨ha, hp⟩ := sq_add_sq_eq_zero.mp hi.symm
    exact hreg.elim (· ha) (· hp)
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (by simpa using normal_mem_orthogonal a p))
  have hdim := (fderiv ℝ (parametrization a) p).range.finrank_add_finrank_orthogonal
  have hrank := LinearMap.finrank_range_of_inj ((injective_fderiv_parametrization_iff a p).2 hreg)
  rw [finrank_span_singleton hn]
  norm_num [Module.finrank_prod] at hdim hrank
  omega

/-- The Euclidean second fundamental form at every regular helicoid parameter. -/
theorem secondFundamentalForm_parametrization {a : ℝ} (p w z : P) (hreg : a ≠ 0 ∨ p.2 ≠ 0) :
    TauCeti.secondFundamentalForm ℝ (parametrization a) p w z =
      (a * (w.1 * z.2 + w.2 * z.1) / (a ^ 2 + p.2 ^ 2)) • normal a p := by
  have hm := TauCeti.secondFundamentalForm_apply_mem_orthogonal (𝕜 := ℝ)
    (parametrization a) p w z
  rw [orthogonal_range_fderiv_eq_span_normal p hreg] at hm
  have hp := Submodule.starProjection_eq_self_iff.mpr hm
  rw [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq,
    inner_normal_self, inner_normal_secondFundamentalForm] at hp
  exact hp.symm

end TauCeti.Helicoid
