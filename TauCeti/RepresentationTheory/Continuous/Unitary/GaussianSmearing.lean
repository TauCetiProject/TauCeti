/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration
public import TauCeti.RepresentationTheory.Continuous.Unitary.StronglyContinuous

/-!
# Complex-time Gaussian smearing for strongly continuous unitary representations

For a strongly continuous unitary representation `U` of `Multiplicative ℝ` on a complex inner
product space `H` and `R : H →L[ℂ] H`, `hU.gaussianSmear hcont R c z` is the bounded operator
`v ↦ ∫ t : ℝ, Complex.gaussianKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v))`. It defines
a locally norm-bounded strongly entire family (`differentiable_gaussianSmear_apply`,
`locallyBounded_gaussianSmear`) satisfying `(gaussianSmear R c (conj z))⋆ = gaussianSmear R⋆ c z`
(`star_gaussianSmear_conj`), conjugating by `U` at real times (`gaussianSmear_ofReal`), and
converging strongly to `R` at `z = 0` as `c → ∞` (`tendsto_gaussianSmear_apply`).

## Main definitions

* `ContRepresentation.IsUnitary.gaussianSmear`: complex-time Gaussian smearing of an operator.

## Main statements

* `ContRepresentation.IsUnitary.differentiable_gaussianSmear_apply`, `locallyBounded_gaussianSmear`,
  `star_gaussianSmear_conj`, `gaussianSmear_ofReal`, `tendsto_gaussianSmear_apply`.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter MeasureTheory Real Topology
open scoped ComplexConjugate InnerProductSpace

namespace ContRepresentation.IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {U : ContRepresentation ℂ (Multiplicative ℝ) H}

private theorem continuous_conj_apply (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) (v : H) :
    Continuous fun t : ℝ => U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
  have h1 : Continuous fun t : ℝ => U (.ofAdd (-t)) v := by
    convert (hU.continuous_inv_apply hcont v).comp continuous_ofAdd using 1; ext t; simp [ofAdd_neg]
  exact (hU.continuous_apply_prod hcont).comp (continuous_ofAdd.prodMk (R.continuous.comp h1))

private theorem norm_conj_apply_le (hU : U.IsUnitary) (R : H →L[ℂ] H) (v : H) (t : ℝ) :
    ‖U (.ofAdd t) (R (U (.ofAdd (-t)) v))‖ ≤ ‖R‖ * ‖v‖ := by
  rw [hU.norm_map]; simpa only [hU.norm_map] using R.le_opNorm (U (.ofAdd (-t)) v)

private theorem integrable_gaussianSmear (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) (c : ℝ) (z : ℂ) (v : H) :
    Integrable fun t : ℝ =>
      Complex.gaussianKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
  refine ((Complex.integrable_norm_gaussianKernel c z).mul_const (‖R‖ * ‖v‖)).mono'
    ((Complex.continuous_gaussianKernel c z).smul
      (continuous_conj_apply hU hcont R v)).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (norm_conj_apply_le hU R v t) (norm_nonneg _)

/-- Complex-time Gaussian smearing of an operator `R` under a strongly continuous unitary
representation `U` of `Multiplicative ℝ`. -/
def gaussianSmear (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H)
    (c : ℝ) (z : ℂ) : H →L[ℂ] H :=
  ({ toFun v := ∫ t : ℝ, Complex.gaussianKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v))
     map_add' u v := by
       simp only [map_add, smul_add]
       exact integral_add (integrable_gaussianSmear hU hcont R c z u)
         (integrable_gaussianSmear hU hcont R c z v)
     map_smul' a v := by
       simp only [map_smul, smul_comm _ a, RingHom.id_apply]; exact integral_smul a _ } :
    H →ₗ[ℂ] H).mkContinuous ((∫ t : ℝ, ‖Complex.gaussianKernel c t z‖) * ‖R‖) fun v => by
      refine (norm_integral_le_of_norm_le
        ((Complex.integrable_norm_gaussianKernel c z).mul_const (‖R‖ * ‖v‖))
        (ae_of_all _ fun t => ?_)).trans_eq (by rw [integral_mul_const, mul_assoc])
      rw [norm_smul]; exact mul_le_mul_of_nonneg_left (norm_conj_apply_le hU R v t) (norm_nonneg _)

/-- Pointwise evaluation of the complex-time Gaussian smearing operator. -/
theorem gaussianSmear_apply (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c : ℝ) (z : ℂ) (v : H) :
    hU.gaussianSmear hcont R c z v =
      ∫ t : ℝ, Complex.gaussianKernel c t z • U (.ofAdd t) (R (U (.ofAdd (-t)) v)) := by
  simp [gaussianSmear, LinearMap.mkContinuous_apply]

/-- Complex-time Gaussian smearing is strongly entire in `z`. -/
theorem differentiable_gaussianSmear_apply (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) (R : H →L[ℂ] H) (c : ℝ) (v : H) :
    Differentiable ℂ fun z => hU.gaussianSmear hcont R c z v := by
  simpa only [gaussianSmear_apply] using Complex.differentiable_integral_gaussianKernel_smul
    (continuous_conj_apply hU hcont R v) (norm_conj_apply_le hU R v) c

/-- Complex-time Gaussian smearing is locally norm-bounded in `z`. -/
theorem locallyBounded_gaussianSmear (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c : ℝ) (z₀ : ℂ) :
    ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖hU.gaussianSmear hcont R c z‖ ≤ M := by
  set D := ‖z₀‖ + 1
  refine ⟨1, one_pos, (∫ t : ℝ, ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) *
    rexp (-(c ^ 2 / 2) * t ^ 2)) * ‖R‖, fun z hz => ?_⟩
  rw [gaussianSmear]
  refine (LinearMap.mkContinuous_norm_le _
    (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg R)) _).trans ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact mul_le_mul_of_nonneg_right (integral_mono (Complex.integrable_norm_gaussianKernel c z)
      ((integrable_exp_neg_mul_sq (by positivity : 0 < c ^ 2 / 2)).const_mul _)
      fun t => Complex.norm_gaussianKernel_le c t (norm_lt_of_mem_ball hz).le) (norm_nonneg R)

variable [CompleteSpace H]

/-- An operator commuting with every real-time unitary conjugate `U_t R U_{-t}` commutes with the
complex-time Gaussian smearing of `R`. -/
theorem commute_gaussianSmear_of_commute (hU : U.IsUnitary)
    (hcont : ∀ v, Continuous fun g => U g v) {R X : H →L[ℂ] H}
    (hcomm : ∀ t : ℝ, X * (U (.ofAdd t) * R * U (.ofAdd (-t))) =
      (U (.ofAdd t) * R * U (.ofAdd (-t))) * X) (c : ℝ) (z : ℂ) :
    X * hU.gaussianSmear hcont R c z = hU.gaussianSmear hcont R c z * X := by
  ext v; simp only [mul_apply_eq_comp, gaussianSmear_apply]
  rw [← X.integral_comp_comm (integrable_gaussianSmear hU hcont R c z v)]
  congr 1 with t; rw [map_smul]; congr 1
  simpa only [mul_apply_eq_comp] using congrArg (fun Y => Y v) (hcomm t)

/-- Taking the adjoint of a Gaussian-smeared operator reflects the complex parameter and takes the
adjoint of the operator. -/
theorem star_gaussianSmear_conj (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c : ℝ) (z : ℂ) :
    star (hU.gaussianSmear hcont R c (conj z)) = hU.gaussianSmear hcont (star R) c z := by
  ext v; refine ext_inner_left ℂ fun u => ?_
  rw [star_eq_adjoint, adjoint_inner_right, ← inner_conj_symm]; simp only [gaussianSmear_apply]
  rw [← innerSL_apply_apply (𝕜 := ℂ) v, ← innerSL_apply_apply (𝕜 := ℂ) u,
    ← (innerSL ℂ v).integral_comp_comm (integrable_gaussianSmear hU hcont R c (conj z) u),
    ← (innerSL ℂ u).integral_comp_comm (integrable_gaussianSmear hU hcont (star R) c z v),
    ← integral_conj]
  congr 1 with t
  simp only [innerSL_apply_apply, inner_smul_right, map_mul, Complex.gaussianKernel_conj]
  have hstar_U (r : ℝ) : (U (.ofAdd r)).adjoint = U (.ofAdd (-r)) := by
    rw [hU.adjoint_eq_inv, ofAdd_neg]
  congr 1
  rw [inner_conj_symm, ← adjoint_inner_right, hstar_U, star_eq_adjoint, ← adjoint_inner_right,
    ← adjoint_inner_right, hstar_U, neg_neg]

/-- At real time `s`, Gaussian smearing conjugates the `z = 0` smearing by `U_s`. -/
theorem gaussianSmear_ofReal (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (c s : ℝ) :
    hU.gaussianSmear hcont R c s =
      U (.ofAdd s) * hU.gaussianSmear hcont R c 0 * U (.ofAdd (-s)) := by
  ext v; simp only [mul_apply_eq_comp, gaussianSmear_apply]
  rw [← (U (.ofAdd s)).integral_comp_comm
      (integrable_gaussianSmear hU hcont R c 0 (U (.ofAdd (-s)) v)),
    ← integral_add_right_eq_self _ s]
  congr 1 with u; rw [map_smul]; congr 1
  · simp only [Complex.gaussianKernel_def, sub_zero]; push_cast; ring_nf
  · have hm1 : U (.ofAdd s) * U (.ofAdd u) = U (.ofAdd (u + s)) := by
      rw [← map_mul, ← ofAdd_add, add_comm]
    have hm2 : U (.ofAdd (-u)) * U (.ofAdd (-s)) = U (.ofAdd (-(u + s))) := by
      rw [← map_mul, ← ofAdd_add, neg_add]
    simp only [mul_apply_eq_comp, ← hm1, ← hm2]

/-- As `c → ∞`, the Gaussian smearing at `z = 0` converges strongly to `R`. -/
theorem tendsto_gaussianSmear_apply (hU : U.IsUnitary) (hcont : ∀ v, Continuous fun g => U g v)
    (R : H →L[ℂ] H) (v : H) :
    Tendsto (fun c : ℝ => hU.gaussianSmear hcont R c 0 v) atTop (𝓝 (R v)) := by
  simpa [gaussianSmear_apply] using Complex.tendsto_integral_gaussianKernel_smul
    (continuous_conj_apply hU hcont R v) (norm_conj_apply_le hU R v)

end ContRepresentation.IsUnitary
