/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# The Kaplansky function

The **Kaplansky function** is `kaplanskyFun t = 2 * t / (1 + t ^ 2)`. It maps `ℝ` into `[-1, 1]`,
and `kaplanskyFunInv s = s / (1 + √(1 - s ^ 2))` is a continuous right inverse of it on `[-1, 1]`,
so the image is all of `[-1, 1]`.
Through the continuous functional calculus it therefore sends selfadjoint elements to selfadjoint
contractions, and every selfadjoint contraction `b` is `cfc kaplanskyFun a` for the selfadjoint
element `a = cfc kaplanskyFunInv b`, which lies in every closed star subalgebra containing `b`.

Writing `ρ t = (1 + t ^ 2)⁻¹` and `σ t = t / (1 + t ^ 2)`, so that `kaplanskyFun = 2 • σ`, the
differences of the functional calculus satisfy the identity
`cfc kaplanskyFun a - cfc kaplanskyFun b = 2 • (ρ(a) (a - b) ρ(b) + σ(a) (b - a) σ(b))`
for selfadjoint `a` and `b`, with `‖ρ(a)‖ ≤ 1` and `‖σ(a)‖ ≤ 1 / 2`. Since the factors `a - b`
appear linearly between uniformly bounded operators, this identity is what makes
`a ↦ cfc kaplanskyFun a` continuous for the strong operator topology on selfadjoint operators
without any norm bound on `a`. Together these are the functional-calculus inputs of the Kaplansky
density theorem.

## Main results

* `TauCeti.norm_cfc_kaplanskyFun_le`: `‖cfc kaplanskyFun a‖ ≤ 1`.
* `IsSelfAdjoint.cfc_kaplanskyFun_cfc_kaplanskyFunInv`: a selfadjoint contraction `b` satisfies
  `cfc kaplanskyFun (cfc kaplanskyFunInv b) = b`.
* `TauCeti.cfc_kaplanskyFun_sub_cfc_kaplanskyFun`: the difference identity above.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.3.5 (the
Kaplansky density theorem) and Lemma 5.3.4.
-/

public section

open Filter Topology

namespace TauCeti

/-! ### The real functions -/

/-- The **Kaplansky function** `t ↦ 2 * t / (1 + t ^ 2)`, a continuous map of `ℝ` onto
`[-1, 1]`. -/
noncomputable def kaplanskyFun (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

/-- The function `s ↦ s / (1 + √(1 - s ^ 2))`, a right inverse of the Kaplansky function on
`[-1, 1]` (`kaplanskyFun_kaplanskyFunInv`). -/
noncomputable def kaplanskyFunInv (s : ℝ) : ℝ := s / (1 + √(1 - s ^ 2))

theorem kaplanskyFun_def (t : ℝ) : kaplanskyFun t = 2 * t / (1 + t ^ 2) := (rfl)

theorem kaplanskyFunInv_def (s : ℝ) : kaplanskyFunInv s = s / (1 + √(1 - s ^ 2)) := (rfl)

private theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

/-- The function `ρ t = (1 + t ^ 2)⁻¹` of the Kaplansky difference identity is continuous. -/
theorem continuous_inv_one_add_sq : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ :=
  (continuous_const.add (continuous_pow 2)).inv₀ fun t => (one_add_sq_pos t).ne'

/-- The function `σ t = t / (1 + t ^ 2)` of the Kaplansky difference identity is continuous. -/
theorem continuous_div_one_add_sq : Continuous fun t : ℝ => t / (1 + t ^ 2) :=
  continuous_id.div (continuous_const.add (continuous_pow 2)) fun t => (one_add_sq_pos t).ne'

@[fun_prop]
theorem continuous_kaplanskyFun : Continuous kaplanskyFun :=
  (continuous_const.mul continuous_id).div (continuous_const.add (continuous_pow 2))
    fun t => (one_add_sq_pos t).ne'

@[fun_prop]
theorem continuous_kaplanskyFunInv : Continuous kaplanskyFunInv :=
  continuous_id.div (continuous_const.add (continuous_const.sub (continuous_pow 2)).sqrt)
    fun s => by positivity

/-- The Kaplansky function takes values in `[-1, 1]`. -/
theorem abs_kaplanskyFun_le_one (t : ℝ) : |kaplanskyFun t| ≤ 1 := by
  rw [kaplanskyFun_def, abs_div, abs_of_pos (one_add_sq_pos t), div_le_one (one_add_sq_pos t),
    abs_mul, abs_two]
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- `kaplanskyFunInv` is a right inverse of the Kaplansky function on `[-1, 1]`. -/
@[simp]
theorem kaplanskyFun_kaplanskyFunInv {s : ℝ} (hs : |s| ≤ 1) :
    kaplanskyFun (kaplanskyFunInv s) = s := by
  have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  have hr := Real.sq_sqrt h1
  have hr0 := Real.sqrt_nonneg (1 - s ^ 2)
  rw [kaplanskyFun_def, kaplanskyFunInv_def]
  field_simp
  linear_combination (-s) * hr

/-- `t / (1 + t ^ 2)` takes values in `[-1 / 2, 1 / 2]`. -/
theorem abs_div_one_add_sq_le (t : ℝ) : |t / (1 + t ^ 2)| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos (one_add_sq_pos t), div_le_iff₀ (one_add_sq_pos t)]
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-! ### The functional calculus -/

section Algebra

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The functional calculus sends `1 + t ^ 2` to `1 + a ^ 2`. -/
theorem cfc_one_add_sq {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => 1 + t ^ 2) a = 1 + a ^ 2 := by
  rw [cfc_const_add 1 (fun t : ℝ => t ^ 2) a, cfc_pow_id a 2, Algebra.algebraMap_eq_smul_one,
    one_smul]

/-- `cfc (t / (1 + t ^ 2)) a = cfc (1 + t ^ 2)⁻¹ a * a`. -/
theorem cfc_div_one_add_sq_eq_mul {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => t / (1 + t ^ 2)) a = cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a * a := calc
  _ = cfc (fun t : ℝ => (1 + t ^ 2)⁻¹ * t) a := cfc_congr fun t _ => div_eq_inv_mul t _
  _ = cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a * cfc (fun t : ℝ => t) a :=
    cfc_mul _ _ a continuous_inv_one_add_sq.continuousOn
  _ = _ := by rw [cfc_id' ℝ a]

/-- `cfc (t / (1 + t ^ 2)) a = a * cfc (1 + t ^ 2)⁻¹ a`. -/
theorem cfc_div_one_add_sq_eq_mul' {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun t : ℝ => t / (1 + t ^ 2)) a = a * cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a := calc
  _ = cfc (fun t : ℝ => t * (1 + t ^ 2)⁻¹) a := cfc_congr fun t _ => div_eq_mul_inv t _
  _ = cfc (fun t : ℝ => t) a * cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a :=
    cfc_mul _ _ a continuous_id.continuousOn continuous_inv_one_add_sq.continuousOn
  _ = _ := by rw [cfc_id' ℝ a]

/-- The Kaplansky function is twice `t ↦ t / (1 + t ^ 2)`. -/
theorem cfc_kaplanskyFun_eq_smul (a : A) :
    cfc kaplanskyFun a = (2 : ℝ) • cfc (fun t : ℝ => t / (1 + t ^ 2)) a := by
  rw [← cfc_smul (2 : ℝ) (fun t : ℝ => t / (1 + t ^ 2)) a continuous_div_one_add_sq.continuousOn]
  exact cfc_congr fun t _ => by rw [kaplanskyFun_def, smul_eq_mul, mul_div_assoc]

/-- **The Kaplansky difference identity.** For selfadjoint `a` and `b`, with
`ρ t = (1 + t ^ 2)⁻¹` and `σ t = t / (1 + t ^ 2)`,
`cfc kaplanskyFun a - cfc kaplanskyFun b = 2 • (ρ(a) (a - b) ρ(b) + σ(a) (b - a) σ(b))`. -/
theorem cfc_kaplanskyFun_sub_cfc_kaplanskyFun {a b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) :
    cfc kaplanskyFun a - cfc kaplanskyFun b = (2 : ℝ) •
      (cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a * (a - b) * cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) b +
        cfc (fun t : ℝ => t / (1 + t ^ 2)) a * (b - a) *
          cfc (fun t : ℝ => t / (1 + t ^ 2)) b) := by
  rw [cfc_kaplanskyFun_eq_smul, cfc_kaplanskyFun_eq_smul, ← smul_sub, cfc_div_one_add_sq_eq_mul ha,
    cfc_div_one_add_sq_eq_mul' hb]
  have h1 := (cfcUnits (fun t : ℝ => 1 + t ^ 2) a fun t _ => (one_add_sq_pos t).ne').inv_mul
  have h2 := (cfcUnits (fun t : ℝ => 1 + t ^ 2) b fun t _ => (one_add_sq_pos t).ne').mul_inv
  simp only [val_inv_cfcUnits, val_cfcUnits] at h1 h2
  rw [cfc_one_add_sq ha] at h1
  rw [cfc_one_add_sq hb] at h2
  generalize cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a = ρa at h1 ⊢
  generalize cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) b = ρb at h2 ⊢
  -- Insert `1 = (1 + b ^ 2) * ρb` on the right of `ρa * a` and `1 = ρa * (1 + a ^ 2)` on the
  -- left of `b * ρb`; the identity is then a polynomial identity.
  have h : ρa * a - b * ρb = ρa * a * ((1 + b ^ 2) * ρb) - ρa * (1 + a ^ 2) * b * ρb := by
    rw [h1, h2, mul_one, one_mul]
  rw [h]
  noncomm_ring

end Algebra

section Normed

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The Kaplansky function of any element is a contraction. -/
theorem norm_cfc_kaplanskyFun_le (a : A) : ‖cfc kaplanskyFun a‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun t _ => abs_kaplanskyFun_le_one t

/-- `‖cfc (1 + t ^ 2)⁻¹ a‖ ≤ 1`. -/
theorem norm_cfc_inv_one_add_sq_le (a : A) : ‖cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun t _ => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (one_add_sq_pos t)]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg t))

/-- `‖cfc (t / (1 + t ^ 2)) a‖ ≤ 1 / 2`. -/
theorem norm_cfc_div_one_add_sq_le (a : A) : ‖cfc (fun t : ℝ => t / (1 + t ^ 2)) a‖ ≤ 1 / 2 :=
  norm_cfc_le (by norm_num) fun t _ => abs_div_one_add_sq_le t

end Normed

/-- Every selfadjoint contraction `b` is the Kaplansky function of the selfadjoint element
`cfc kaplanskyFunInv b`, which lies in every closed star subalgebra containing `b` (`cfc_mem`). -/
@[simp]
theorem _root_.IsSelfAdjoint.cfc_kaplanskyFun_cfc_kaplanskyFunInv {A : Type*} [NormedRing A]
    [StarRing A] [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {b : A} (hb : IsSelfAdjoint b) (hb₁ : ‖b‖ ≤ 1) :
    cfc kaplanskyFun (cfc kaplanskyFunInv b) = b := by
  rw [← cfc_comp kaplanskyFun kaplanskyFunInv b]
  conv_rhs => rw [← cfc_id' ℝ b]
  refine cfc_congr fun s hs => kaplanskyFun_kaplanskyFunInv ?_
  have := norm_apply_le_norm_cfc (fun t : ℝ => t) b hs
  rw [cfc_id' ℝ b, Real.norm_eq_abs] at this
  exact this.trans hb₁

/-! ### Strong operator continuity -/

section StrongContinuity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} {x : ι → H →L[ℂ] H} {y : H →L[ℂ] H}

/-- **Strong continuity of the Kaplansky function.** If selfadjoint operators `x i` converge
strongly (pointwise on vectors) to a selfadjoint operator `y`, then `cfc kaplanskyFun (x i)`
converges strongly to `cfc kaplanskyFun y`. No norm bound on the `x i` is needed. -/
theorem tendsto_cfc_kaplanskyFun_apply (hx : ∀ᶠ i in l, IsSelfAdjoint (x i))
    (hy : IsSelfAdjoint y) (hxy : ∀ v, Tendsto (fun i => x i v) l (𝓝 (y v))) (v : H) :
    Tendsto (fun i => cfc kaplanskyFun (x i) v) l (𝓝 (cfc kaplanskyFun y v)) := by
  set w₁ := cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) y v
  set w₂ := cfc (fun t : ℝ => t / (1 + t ^ 2)) y v
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun i => 2 * (‖x i w₁ - y w₁‖ + 1 / 2 * ‖x i w₂ - y w₂‖)) l (𝓝 0) := by
    have h₁ := (tendsto_iff_norm_sub_tendsto_zero.mp (hxy w₁))
    have h₂ := (tendsto_iff_norm_sub_tendsto_zero.mp (hxy w₂))
    simpa only [mul_zero, add_zero] using (h₁.add (h₂.const_mul (1 / 2))).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hx] with i hi
  -- Apply the difference identity to `v` and bound the outer factors by `1` and `1 / 2`.
  have key : cfc kaplanskyFun (x i) v - cfc kaplanskyFun y v = (2 : ℝ) •
      (cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) (x i) (x i w₁ - y w₁) +
        cfc (fun t : ℝ => t / (1 + t ^ 2)) (x i) (y w₂ - x i w₂)) := by
    rw [← sub_apply, cfc_kaplanskyFun_sub_cfc_kaplanskyFun hi hy]
    simp [w₁, w₂]
  rw [key, norm_smul, Real.norm_two]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.le_of_opNorm_le _ (norm_cfc_inv_one_add_sq_le _) _).trans_eq
      (one_mul _)
  · rw [← norm_sub_rev (y w₂)]
    exact ContinuousLinearMap.le_of_opNorm_le _ (norm_cfc_div_one_add_sq_le _) _

/-- **Strong continuity of the Kaplansky function**, stated in Mathlib's strong operator topology
`H →Lₚₜ[ℂ] H`: along any filter, strong convergence of selfadjoint operators `x i → y` gives strong
convergence `cfc kaplanskyFun (x i) → cfc kaplanskyFun y`. -/
theorem tendsto_toPointwiseConvergenceCLM_cfc_kaplanskyFun (hx : ∀ᶠ i in l, IsSelfAdjoint (x i))
    (hy : IsSelfAdjoint y)
    (hxy : Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      (x i)) l (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H y))) :
    Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      (cfc kaplanskyFun (x i))) l
      (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        (cfc kaplanskyFun y))) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto] at hxy ⊢
  simp only [ContinuousLinearMap.toPointwiseConvergenceCLM_apply] at hxy ⊢
  exact tendsto_cfc_kaplanskyFun_apply hx hy hxy

end StrongContinuity

end TauCeti
