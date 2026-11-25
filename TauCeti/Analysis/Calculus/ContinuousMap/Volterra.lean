/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContinuousMap.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Volterra transforms of continuous paths

For a continuous real kernel `K` on a compact interval `[a, b]`, the Volterra transform sends
a continuous path `x : [a, b] → E` to
`T_K x (t) = x t + ∫ s in a..t, K s • x s`.
It is a continuous linear automorphism of `C([a, b], E)` with the explicit inverse
`T_K⁻¹ y (t) = y t - ∫ s in a..t, (K s * exp (-∫ u in s..t, K u)) • y s`,
obtained by solving the linear equation `z' = K (y - z)` with `z a = 0` by an integrating
factor.

Applied to the paths of a Brownian motion, `T_K` produces the Gaussian process
`B t + ∫ s in 0..t, K s * B s`; the facts proved here are the deterministic input: the
uniform bounds `‖T_K‖ ≤ 1 + (b - a) ‖K‖` and
`‖T_K⁻¹‖ ≤ 1 + (b - a) ‖K‖ exp ((b - a) ‖K‖)`, preservation of the initial value (so paths
based at zero stay based at zero), compatibility with restriction to shorter horizons, and
causality: the value at time `t` depends only on the path up to time `t`.

## Main definitions

* `ContinuousMap.volterraTransform`: the Volterra transform `T_K` as a continuous linear
  equivalence of `C(Set.Icc a b, E)`.

## Main results

* `ContinuousMap.volterraTransform_apply`, `ContinuousMap.volterraTransform_symm_apply`: the
  pointwise formulas for `T_K` and its inverse.
* `ContinuousMap.norm_volterraTransform_le`, `ContinuousMap.norm_volterraTransform_symm_le`:
  operator norm bounds.
* `ContinuousMap.volterraTransform_comp_inclusion`,
  `ContinuousMap.volterraTransform_symm_comp_inclusion`: restriction to `[a, c]` for `c ≤ b`.
* `ContinuousMap.volterraTransform_apply_eq_of_eqOn_Iic`,
  `ContinuousMap.volterraTransform_symm_apply_eq_of_eqOn_Iic`: causality.
* `intervalIntegral.integral_mul_exp_smul_add_primitive`: the integrating-factor identity on the
  real line behind the inverse formula.
-/

public section

open MeasureTheory Set

noncomputable section

section Auxiliary

/-! ### Integrating-factor identities on the real line -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℝ → ℝ} {u : ℝ → E} {a : ℝ}

/-- If `P = ∫ₐ k • u`, then `exp (∫ₐ k) • P` is the primitive of
`(k * exp (∫ₐ k)) • (u + P)`. This integrating-factor identity underlies `T_K⁻¹ (T_K x) = x`
(`ContinuousMap.volterraTransform`). -/
theorem intervalIntegral.integral_mul_exp_smul_add_primitive (hk : Continuous k)
    (hu : Continuous u) (t : ℝ) :
    ∫ s in a..t, (k s * Real.exp (∫ r in a..s, k r)) • (u s + ∫ r in a..s, k r • u r) =
      Real.exp (∫ r in a..t, k r) • ∫ r in a..t, k r • u r := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral_of_not_completeSpace hE]
  have hku : Continuous fun r ↦ k r • u r := hk.smul hu
  have hφ := intervalIntegral.continuous_primitive (μ := volume)
    (fun _ _ ↦ hk.intervalIntegrable _ _) a
  have hP := intervalIntegral.continuous_primitive (μ := volume)
    (fun _ _ ↦ hku.intervalIntegrable _ _) a
  have hderiv (s : ℝ) : HasDerivAt
      (fun s ↦ Real.exp (∫ r in a..s, k r) • ∫ r in a..s, k r • u r)
      ((k s * Real.exp (∫ r in a..s, k r)) • (u s + ∫ r in a..s, k r • u r)) s := by
    convert ((hk.integral_hasStrictDerivAt a s).hasDerivAt.exp).smul
      (hku.integral_hasStrictDerivAt a s).hasDerivAt using 1
    simp only [smul_add, smul_smul, mul_comm (k s)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
    (((hk.mul (Real.continuous_exp.comp hφ)).smul (hu.add hP)).intervalIntegrable _ _)]
  simp

end Auxiliary

namespace ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {a b : ℝ} (hab : a ≤ b)

/-! ### The transform and its inverse -/

/-- On `[a, t]`, the projection onto `[a, b]` is the identity. -/
private theorem coe_projIcc_of_mem_uIcc {t : ℝ} (ht : t ∈ Icc a b) {s : ℝ}
    (hs : s ∈ uIcc a t) : (projIcc a b hab s : ℝ) = s := by
  rw [uIcc_of_le ht.1] at hs
  exact congrArg Subtype.val (projIcc_of_mem hab ⟨hs.1, hs.2.trans ht.2⟩)

/-- The forward Volterra map `x ↦ x + ∫ₐ K • x`. -/
private def volterraForward (K : C(Icc a b, ℝ)) : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  ContinuousLinearMap.id ℝ _ + intervalIntegralOperator a b hab ∘L smulContinuousLinearMap K

private theorem volterraForward_apply (K : C(Icc a b, ℝ)) (x : C(Icc a b, E)) (t : Icc a b) :
    volterraForward hab K x t =
      x t + ∫ s in a..t, K (projIcc a b hab s) • x (projIcc a b hab s) := by
  simp [volterraForward]

/-- The integrating factor `exp (∫ₐ K)` and its reciprocal, as continuous functions. -/
private def expPrimitive (K : C(Icc a b, ℝ)) (c : ℝ) : C(Icc a b, ℝ) :=
  ⟨fun t ↦ Real.exp (c * intervalIntegralOperator a b hab K t), by fun_prop⟩

private theorem expPrimitive_apply (K : C(Icc a b, ℝ)) (c : ℝ) (t : Icc a b) :
    expPrimitive hab K c t = Real.exp (c * ∫ s in a..t, K (projIcc a b hab s)) := by
  simp [expPrimitive]

private theorem expPrimitive_neg (K : C(Icc a b, ℝ)) (c : ℝ) :
    expPrimitive hab (-K) c = expPrimitive hab K (-c) := by
  ext t
  simp [expPrimitive]

private theorem expPrimitive_neg_one_mul_one (K : C(Icc a b, ℝ)) (t : Icc a b) :
    expPrimitive hab K (-1) t * expPrimitive hab K 1 t = 1 := by
  rw [expPrimitive_apply, expPrimitive_apply, ← Real.exp_add]
  simp

private theorem smul_expPrimitive_neg_one_smul_expPrimitive_one (K : C(Icc a b, ℝ))
    (x : C(Icc a b, E)) :
    smulContinuousLinearMap (expPrimitive hab K (-1))
      (smulContinuousLinearMap (expPrimitive hab K 1) x) = x := by
  ext t
  simp [smul_smul, expPrimitive_neg_one_mul_one]

private theorem smul_expPrimitive_one_smul_expPrimitive_neg_one (K : C(Icc a b, ℝ))
    (x : C(Icc a b, E)) :
    smulContinuousLinearMap (expPrimitive hab K 1)
      (smulContinuousLinearMap (expPrimitive hab K (-1)) x) = x := by
  ext t
  simp [smul_smul, mul_comm (expPrimitive hab K 1 t), expPrimitive_neg_one_mul_one]

/-- The inverse Volterra map, written with the integrating factor. -/
private def volterraBackward (K : C(Icc a b, ℝ)) : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  ContinuousLinearMap.id ℝ _ - smulContinuousLinearMap (expPrimitive hab K (-1)) ∘L
    intervalIntegralOperator a b hab ∘L smulContinuousLinearMap (K * expPrimitive hab K 1)

private theorem volterraBackward_apply (K : C(Icc a b, ℝ)) (y : C(Icc a b, E)) (t : Icc a b) :
    volterraBackward hab K y t = y t - Real.exp (-∫ s in a..t, K (projIcc a b hab s)) •
      ∫ s in a..t, (K (projIcc a b hab s) * Real.exp (∫ r in a..s, K (projIcc a b hab r))) •
        y (projIcc a b hab s) := by
  simp only [volterraBackward, _root_.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, sub_apply, smulContinuousLinearMap_apply, expPrimitive_apply,
    intervalIntegralOperator_apply, mul_apply, neg_one_mul, one_mul]
  congr 2
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  simp only [coe_projIcc_of_mem_uIcc hab t.property hs]

private theorem volterraBackward_volterraForward (K : C(Icc a b, ℝ)) (x : C(Icc a b, E)) :
    volterraBackward hab K (volterraForward hab K x) = x := by
  ext t
  set k : ℝ → ℝ := fun s ↦ K (projIcc a b hab s)
  set u : ℝ → E := fun s ↦ x (projIcc a b hab s)
  have hk : Continuous k := by fun_prop
  have hu : Continuous u := by fun_prop
  rw [volterraBackward_apply, volterraForward_apply]
  -- On `[a, t]`, the transformed path is `u + ∫ₐ k • u`.
  have hcongr : ∫ s in a..t, (k s * Real.exp (∫ r in a..s, k r)) •
        volterraForward hab K x (projIcc a b hab s) =
      ∫ s in a..t, (k s * Real.exp (∫ r in a..s, k r)) • (u s + ∫ r in a..s, k r • u r) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    simp only [volterraForward_apply, coe_projIcc_of_mem_uIcc hab t.property hs, u, k]
  rw [hcongr, intervalIntegral.integral_mul_exp_smul_add_primitive hk hu, smul_smul, ← Real.exp_add]
  simp [k, u]

/-- Conjugating by the integrating factor turns `volterraForward (-K)` into the inverse map. -/
private theorem volterraBackward_eq_conj (K : C(Icc a b, ℝ)) (y : C(Icc a b, E)) :
    volterraBackward hab K y = smulContinuousLinearMap (expPrimitive hab K (-1))
      (volterraForward hab (-K) (smulContinuousLinearMap (expPrimitive hab K 1) y)) := by
  ext t
  simp [volterraBackward, volterraForward, smul_smul, sub_eq_add_neg,
    expPrimitive_neg_one_mul_one]

/-- Conjugating by the integrating factor turns `volterraBackward (-K)` into the forward map. -/
private theorem volterraForward_eq_conj (K : C(Icc a b, ℝ)) (x : C(Icc a b, E)) :
    volterraForward hab K x = smulContinuousLinearMap (expPrimitive hab K (-1))
      (volterraBackward hab (-K) (smulContinuousLinearMap (expPrimitive hab K 1) x)) := by
  ext t
  simp [volterraBackward, volterraForward, expPrimitive_neg, smul_smul, mul_assoc,
    expPrimitive_neg_one_mul_one]

/-- The right-inverse identity follows from the left-inverse identity for `-K` by conjugating with
the integrating factor. -/
private theorem volterraForward_volterraBackward (K : C(Icc a b, ℝ)) (y : C(Icc a b, E)) :
    volterraForward hab K (volterraBackward hab K y) = y := by
  rw [volterraForward_eq_conj hab K, volterraBackward_eq_conj hab K,
    smul_expPrimitive_one_smul_expPrimitive_neg_one, volterraBackward_volterraForward,
    smul_expPrimitive_neg_one_smul_expPrimitive_one]

/-- The **Volterra transform** `T_K x (t) = x t + ∫ s in a..t, K s • x s` of continuous paths on
`[a, b]` with a continuous real kernel `K`, as a continuous linear equivalence. Its inverse is
`T_K⁻¹ y (t) = y t - ∫ s in a..t, (K s * exp (-∫ u in s..t, K u)) • y s`
(`ContinuousMap.volterraTransform_symm_apply`). Inside the integrals, `K` and the path are
extended constantly outside `[a, b]`; only their values on `[a, t]` matter. -/
def volterraTransform (K : C(Icc a b, ℝ)) : C(Icc a b, E) ≃L[ℝ] C(Icc a b, E) :=
  .ofContinuousLinearMap (volterraForward hab K) (volterraBackward hab K)
    (ContinuousLinearMap.ext (volterraForward_volterraBackward hab K))
    (ContinuousLinearMap.ext (volterraBackward_volterraForward hab K))

variable (K : C(Icc a b, ℝ))

/-- The Volterra transform at time `t` adds `∫ s in a..t, K s • x s` to the path. -/
@[simp]
theorem volterraTransform_apply (x : C(Icc a b, E)) (t : Icc a b) :
    volterraTransform hab K x t =
      x t + ∫ s in a..t, K (projIcc a b hab s) • x (projIcc a b hab s) := by
  rw [volterraTransform, ContinuousLinearEquiv.coe_ofContinuousLinearMap, volterraForward_apply]

/-- The inverse Volterra transform at time `t` subtracts
`∫ s in a..t, (K s * exp (-∫ r in s..t, K r)) • y s` from the path. -/
@[simp]
theorem volterraTransform_symm_apply (y : C(Icc a b, E)) (t : Icc a b) :
    (volterraTransform hab K).symm y t =
      y t - ∫ s in a..t, (K (projIcc a b hab s) *
        Real.exp (-∫ r in s..t, K (projIcc a b hab r))) • y (projIcc a b hab s) := by
  set k : ℝ → ℝ := fun s ↦ K (projIcc a b hab s)
  have hk : Continuous k := by fun_prop
  rw [volterraTransform, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap, volterraBackward_apply,
    ← intervalIntegral.integral_smul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [smul_smul, ← intervalIntegral.integral_interval_sub_left (hk.intervalIntegrable a t)
    (hk.intervalIntegrable a s)]
  simp only [k, sub_eq_add_neg, neg_add, neg_neg, Real.exp_add]
  rw [mul_left_comm]

/-- The Volterra transform with zero kernel is the identity. -/
@[simp]
theorem volterraTransform_zero :
    volterraTransform (E := E) hab 0 = ContinuousLinearEquiv.refl ℝ _ := by
  ext x t
  simp

/-! ### Initial values, norms and causality -/

/-- The Volterra transform preserves the initial value of a path; in particular it maps paths
based at zero to paths based at zero. -/
theorem volterraTransform_apply_left (x : C(Icc a b, E)) :
    volterraTransform hab K x ⟨a, left_mem_Icc.2 hab⟩ = x ⟨a, left_mem_Icc.2 hab⟩ := by
  simp

/-- The inverse Volterra transform preserves the initial value of a path. -/
theorem volterraTransform_symm_apply_left (y : C(Icc a b, E)) :
    (volterraTransform hab K).symm y ⟨a, left_mem_Icc.2 hab⟩ = y ⟨a, left_mem_Icc.2 hab⟩ := by
  simp

/-- The Volterra transform has operator norm at most `1 + (b - a) ‖K‖`. -/
theorem norm_volterraTransform_le :
    ‖(volterraTransform (E := E) hab K : C(Icc a b, E) →L[ℝ] C(Icc a b, E))‖ ≤
      1 + (b - a) * ‖K‖ := by
  have hK : ‖smulContinuousLinearMap (E := E) K‖ ≤ ‖K‖ :=
    (ContinuousLinearMap.le_of_opNorm_le _ norm_smulContinuousLinearMap_le K).trans_eq (one_mul _)
  rw [volterraTransform, ContinuousLinearEquiv.toContinuousLinearMap_ofContinuousLinearMap]
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans <|
    add_le_add ContinuousLinearMap.norm_id_le <| (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
      mul_le_mul (norm_intervalIntegralOperator_le a b hab) hK (norm_nonneg _) (sub_nonneg.2 hab)

/-- The inverse Volterra transform has operator norm at most
`1 + (b - a) ‖K‖ exp ((b - a) ‖K‖)`. -/
theorem norm_volterraTransform_symm_le :
    ‖((volterraTransform (E := E) hab K).symm : C(Icc a b, E) →L[ℝ] C(Icc a b, E))‖ ≤
      1 + (b - a) * ‖K‖ * Real.exp ((b - a) * ‖K‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
  refine (norm_le _ (by positivity)).2 fun t ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, volterraTransform_symm_apply]
  have ht : |(t : ℝ) - a| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.2 t.property.1)]
    exact sub_le_sub_right t.property.2 a
  -- For `a ≤ s ≤ t`, the integrating factor is at most `exp ((b - a) ‖K‖)`.
  have hint : ‖∫ s in a..t, (K (projIcc a b hab s) *
        Real.exp (-∫ r in s..t, K (projIcc a b hab r))) • y (projIcc a b hab s)‖ ≤
      ‖K‖ * Real.exp ((b - a) * ‖K‖) * ‖y‖ * |(t : ℝ) - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
    rw [uIoc_of_le t.property.1] at hs
    have hexp : Real.exp (-∫ r in s..t, K (projIcc a b hab r)) ≤
        Real.exp ((b - a) * ‖K‖) := by
      refine Real.exp_le_exp.2 ((neg_le_abs _).trans ?_)
      rw [← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r _ ↦
        norm_coe_le_norm K _).trans ?_
      rw [abs_of_nonneg (sub_nonneg.2 hs.2), mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith [hs.1, t.property.2]) (norm_nonneg K)
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (mul_le_mul (norm_coe_le_norm K _) hexp (Real.exp_pos _).le
      (norm_nonneg K)) (norm_coe_le_norm y _) (norm_nonneg _) (by positivity)
  calc ‖y t - ∫ s in a..t, (K (projIcc a b hab s) *
          Real.exp (-∫ r in s..t, K (projIcc a b hab r))) • y (projIcc a b hab s)‖
      ≤ ‖y‖ + ‖K‖ * Real.exp ((b - a) * ‖K‖) * ‖y‖ * (b - a) :=
        (norm_sub_le _ _).trans (add_le_add (norm_coe_le_norm y t)
          (hint.trans (mul_le_mul_of_nonneg_left ht (by positivity))))
    _ = (1 + (b - a) * ‖K‖ * Real.exp ((b - a) * ‖K‖)) * ‖y‖ := by ring

omit [NormedSpace ℝ E] in
/-- Paths that agree on `[a, t]` agree at the projections of points of `[a, t]`. -/
private theorem apply_projIcc_eq_of_eqOn_Iic {x y : C(Icc a b, E)} {t : Icc a b}
    (h : EqOn x y (Iic t)) {s : ℝ} (hs : s ∈ uIcc a t) :
    x (projIcc a b hab s) = y (projIcc a b hab s) := by
  refine h ?_
  rw [mem_Iic, ← Subtype.coe_le_coe, coe_projIcc_of_mem_uIcc hab t.property hs]
  exact (uIcc_of_le t.property.1 ▸ hs).2

/-- **Causality** of the Volterra transform: its value at time `t` depends only on the path on
`[a, t]`. -/
theorem volterraTransform_apply_eq_of_eqOn_Iic {x y : C(Icc a b, E)} {t : Icc a b}
    (h : EqOn x y (Iic t)) :
    volterraTransform hab K x t = volterraTransform hab K y t := by
  simp only [volterraTransform_apply, h (mem_Iic.2 le_rfl)]
  congr 1
  exact intervalIntegral.integral_congr fun s hs ↦ by
    rw [apply_projIcc_eq_of_eqOn_Iic hab h hs]

/-- **Causality** of the inverse Volterra transform: its value at time `t` depends only on the
path on `[a, t]`. -/
theorem volterraTransform_symm_apply_eq_of_eqOn_Iic {x y : C(Icc a b, E)} {t : Icc a b}
    (h : EqOn x y (Iic t)) :
    (volterraTransform hab K).symm x t = (volterraTransform hab K).symm y t := by
  simp only [volterraTransform_symm_apply, h (mem_Iic.2 le_rfl)]
  congr 1
  exact intervalIntegral.integral_congr fun s hs ↦ by
    rw [apply_projIcc_eq_of_eqOn_Iic hab h hs]

/-! ### Restriction to shorter horizons -/

variable {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)

/-- On `[a, t]` with `t ≤ c ≤ b`, projecting onto `[a, c]` and including into `[a, b]` agrees
with projecting onto `[a, b]`. -/
private theorem inclusion_projIcc_of_mem_uIcc {t : ℝ} (ht : t ∈ Icc a c) {s : ℝ}
    (hs : s ∈ uIcc a t) :
    ContinuousMap.inclusion (Icc_subset_Icc_right hcb) (projIcc a c hac s) = projIcc a b hab s :=
  Subtype.ext <| (inclusion_apply_coe _ _).trans <| (coe_projIcc_of_mem_uIcc hac ht hs).trans
    (coe_projIcc_of_mem_uIcc hab ⟨ht.1, ht.2.trans hcb⟩ hs).symm

/-- The Volterra transform commutes with restriction to a shorter horizon `[a, c]`. -/
theorem volterraTransform_comp_inclusion (x : C(Icc a b, E)) :
    (volterraTransform hab K x).comp (.inclusion (Icc_subset_Icc_right hcb)) =
      volterraTransform hac (K.comp (.inclusion (Icc_subset_Icc_right hcb)))
        (x.comp (.inclusion (Icc_subset_Icc_right hcb))) := by
  ext t
  simp only [comp_apply, inclusion_apply_coe, volterraTransform_apply]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  simp only [inclusion_projIcc_of_mem_uIcc hab hac hcb t.property hs]

/-- The inverse Volterra transform commutes with restriction to a shorter horizon `[a, c]`. -/
theorem volterraTransform_symm_comp_inclusion (y : C(Icc a b, E)) :
    ((volterraTransform hab K).symm y).comp (.inclusion (Icc_subset_Icc_right hcb)) =
      (volterraTransform hac (K.comp (.inclusion (Icc_subset_Icc_right hcb)))).symm
        (y.comp (.inclusion (Icc_subset_Icc_right hcb))) := by
  rw [ContinuousLinearEquiv.eq_symm_apply, ← volterraTransform_comp_inclusion hab K hac hcb,
    ContinuousLinearEquiv.apply_symm_apply]

end ContinuousMap
