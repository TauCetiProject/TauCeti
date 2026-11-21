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
-/

public section

open MeasureTheory Set

noncomputable section

namespace ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Auxiliary

/-! ### Integrating-factor identities on the real line -/

variable {k : ℝ → ℝ} {u : ℝ → E} {a : ℝ}

/-- If `P = ∫ₐ k • u`, then `exp (∫ₐ k) • P` is the primitive of
`(k * exp (∫ₐ k)) • (u + P)`. This is the identity `T_K⁻¹ (T_K x) = x`. -/
private theorem integral_smul_add_primitive (hk : Continuous k) (hu : Continuous u) (t : ℝ) :
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

/-- If `W = ∫ₐ (k * exp (∫ₐ k)) • u`, then `exp (-∫ₐ k) • W` is the primitive of
`k • (u - exp (-∫ₐ k) • W)`. This is the identity `T_K (T_K⁻¹ y) = y`. -/
private theorem integral_smul_sub_primitive (hk : Continuous k) (hu : Continuous u) (t : ℝ) :
    ∫ s in a..t, k s • (u s - Real.exp (-∫ r in a..s, k r) •
        ∫ r in a..s, (k r * Real.exp (∫ q in a..r, k q)) • u r) =
      Real.exp (-∫ r in a..t, k r) •
        ∫ r in a..t, (k r * Real.exp (∫ q in a..r, k q)) • u r := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral_of_not_completeSpace hE]
  have hφ := intervalIntegral.continuous_primitive (μ := volume)
    (fun _ _ ↦ hk.intervalIntegrable _ _) a
  have hg : Continuous fun r ↦ (k r * Real.exp (∫ q in a..r, k q)) • u r :=
    (hk.mul (Real.continuous_exp.comp hφ)).smul hu
  have hW := intervalIntegral.continuous_primitive (μ := volume)
    (fun _ _ ↦ hg.intervalIntegrable _ _) a
  have hderiv (s : ℝ) : HasDerivAt
      (fun s ↦ Real.exp (-∫ r in a..s, k r) •
        ∫ r in a..s, (k r * Real.exp (∫ q in a..r, k q)) • u r)
      (k s • (u s - Real.exp (-∫ r in a..s, k r) •
        ∫ r in a..s, (k r * Real.exp (∫ q in a..r, k q)) • u r)) s := by
    convert ((hk.integral_hasStrictDerivAt a s).hasDerivAt.neg.exp).smul
      (hg.integral_hasStrictDerivAt a s).hasDerivAt using 1
    simp only [Pi.neg_apply]
    rw [smul_smul, mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
      smul_sub, smul_smul, mul_neg, neg_smul, mul_comm (k s), sub_eq_add_neg]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
    ((hk.smul (hu.sub ((Real.continuous_exp.comp hφ.neg).smul hW))).intervalIntegrable _ _)]
  simp

end Auxiliary

variable {a b : ℝ} (hab : a ≤ b)

/-! ### The transform and its inverse -/

/-- Pointwise multiplication by a continuous real function. -/
private def smulOperator (g : C(Icc a b, ℝ)) : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  applyContinuousLinearMap ⟨fun s ↦ g s • ContinuousLinearMap.id ℝ E, by fun_prop⟩

@[simp]
private theorem smulOperator_apply (g : C(Icc a b, ℝ)) (x : C(Icc a b, E)) (s : Icc a b) :
    smulOperator g x s = g s • x s := by
  simp [smulOperator]

/-- On `[a, t]`, the projection onto `[a, b]` is the identity. -/
private theorem coe_projIcc_of_mem_uIcc {t : ℝ} (ht : t ∈ Icc a b) {s : ℝ}
    (hs : s ∈ uIcc a t) : (projIcc a b hab s : ℝ) = s := by
  rw [uIcc_of_le ht.1] at hs
  exact congrArg Subtype.val (projIcc_of_mem hab ⟨hs.1, hs.2.trans ht.2⟩)

/-- The forward Volterra map `x ↦ x + ∫ₐ K • x`. -/
private def volterraForward (K : C(Icc a b, ℝ)) : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  ContinuousLinearMap.id ℝ _ + intervalIntegralOperator a b hab ∘L smulOperator K

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

/-- The inverse Volterra map, written with the integrating factor. -/
private def volterraBackward (K : C(Icc a b, ℝ)) : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  ContinuousLinearMap.id ℝ _ - smulOperator (expPrimitive hab K (-1)) ∘L
    intervalIntegralOperator a b hab ∘L smulOperator (K * expPrimitive hab K 1)

private theorem volterraBackward_apply (K : C(Icc a b, ℝ)) (y : C(Icc a b, E)) (t : Icc a b) :
    volterraBackward hab K y t = y t - Real.exp (-∫ s in a..t, K (projIcc a b hab s)) •
      ∫ s in a..t, (K (projIcc a b hab s) * Real.exp (∫ r in a..s, K (projIcc a b hab r))) •
        y (projIcc a b hab s) := by
  simp only [volterraBackward, _root_.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, sub_apply, smulOperator_apply, expPrimitive_apply,
    intervalIntegralOperator_apply, mul_apply, neg_one_mul, one_mul]
  congr 2
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  simp only [coe_projIcc_of_mem_uIcc hab t.2 hs]

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
    simp only [volterraForward_apply, coe_projIcc_of_mem_uIcc hab t.2 hs, u, k]
  rw [hcongr, integral_smul_add_primitive hk hu, smul_smul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_smul, add_sub_cancel_right]

private theorem volterraForward_volterraBackward (K : C(Icc a b, ℝ)) (y : C(Icc a b, E)) :
    volterraForward hab K (volterraBackward hab K y) = y := by
  ext t
  set k : ℝ → ℝ := fun s ↦ K (projIcc a b hab s)
  set u : ℝ → E := fun s ↦ y (projIcc a b hab s)
  have hk : Continuous k := by fun_prop
  have hu : Continuous u := by fun_prop
  rw [volterraForward_apply, volterraBackward_apply]
  -- On `[a, t]`, the inverse-transformed path is `u - exp (-∫ₐ k) • ∫ₐ (k * exp (∫ₐ k)) • u`.
  have hcongr : ∫ s in a..t, k s • volterraBackward hab K y (projIcc a b hab s) =
      ∫ s in a..t, k s • (u s - Real.exp (-∫ r in a..s, k r) •
        ∫ r in a..s, (k r * Real.exp (∫ q in a..r, k q)) • u r) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    simp only [volterraBackward_apply, coe_projIcc_of_mem_uIcc hab t.2 hs, u, k]
  rw [hcongr, integral_smul_sub_primitive hk hu, sub_add_cancel]

/-- The **Volterra transform** `T_K x (t) = x t + ∫ s in a..t, K s • x s` of continuous paths on
`[a, b]` with a continuous real kernel `K`, as a continuous linear equivalence. Its inverse is
`T_K⁻¹ y (t) = y t - ∫ s in a..t, (K s * exp (-∫ u in s..t, K u)) • y s`
(`ContinuousMap.volterraTransform_symm_apply`). Inside the integrals, `K` and the path are
extended constantly outside `[a, b]`; only their values on `[a, t]` matter. -/
def volterraTransform (K : C(Icc a b, ℝ)) : C(Icc a b, E) ≃L[ℝ] C(Icc a b, E) :=
  ContinuousLinearEquiv.equivOfInverse (volterraForward hab K) (volterraBackward hab K)
    (volterraBackward_volterraForward hab K) (volterraForward_volterraBackward hab K)

variable (K : C(Icc a b, ℝ))

/-- The Volterra transform at time `t` adds `∫ s in a..t, K s • x s` to the path. -/
@[simp]
theorem volterraTransform_apply (x : C(Icc a b, E)) (t : Icc a b) :
    volterraTransform hab K x t =
      x t + ∫ s in a..t, K (projIcc a b hab s) • x (projIcc a b hab s) := by
  rw [volterraTransform, ContinuousLinearEquiv.equivOfInverse_apply, volterraForward_apply]

/-- The inverse Volterra transform at time `t` subtracts
`∫ s in a..t, (K s * exp (-∫ r in s..t, K r)) • y s` from the path. -/
@[simp]
theorem volterraTransform_symm_apply (y : C(Icc a b, E)) (t : Icc a b) :
    (volterraTransform hab K).symm y t =
      y t - ∫ s in a..t, (K (projIcc a b hab s) *
        Real.exp (-∫ r in s..t, K (projIcc a b hab r))) • y (projIcc a b hab s) := by
  set k : ℝ → ℝ := fun s ↦ K (projIcc a b hab s)
  have hk : Continuous k := by fun_prop
  rw [volterraTransform, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply, volterraBackward_apply,
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
  refine ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg zero_le_one (mul_nonneg (sub_nonneg.2 hab) (norm_nonneg K))) fun x ↦ ?_
  refine (norm_le _ (by positivity)).2 fun t ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, volterraTransform_apply]
  have hint : ‖∫ s in a..t, K (projIcc a b hab s) • x (projIcc a b hab s)‖ ≤
      ‖K‖ * ‖x‖ * |(t : ℝ) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s _ ↦ by
      rw [norm_smul]
      exact mul_le_mul (norm_coe_le_norm K _) (norm_coe_le_norm x _) (norm_nonneg _)
        (norm_nonneg _)
  have ht : |(t : ℝ) - a| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.2 t.2.1)]
    exact sub_le_sub_right t.2.2 a
  calc ‖x t + ∫ s in a..t, K (projIcc a b hab s) • x (projIcc a b hab s)‖
      ≤ ‖x‖ + ‖K‖ * ‖x‖ * (b - a) :=
        (norm_add_le _ _).trans (add_le_add (norm_coe_le_norm x t)
          (hint.trans (mul_le_mul_of_nonneg_left ht (by positivity))))
    _ = (1 + (b - a) * ‖K‖) * ‖x‖ := by ring

/-- The inverse Volterra transform has operator norm at most
`1 + (b - a) ‖K‖ exp ((b - a) ‖K‖)`. -/
theorem norm_volterraTransform_symm_le :
    ‖((volterraTransform (E := E) hab K).symm : C(Icc a b, E) →L[ℝ] C(Icc a b, E))‖ ≤
      1 + (b - a) * ‖K‖ * Real.exp ((b - a) * ‖K‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
  refine (norm_le _ (by positivity)).2 fun t ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, volterraTransform_symm_apply]
  have ht : |(t : ℝ) - a| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.2 t.2.1)]
    exact sub_le_sub_right t.2.2 a
  -- For `a ≤ s ≤ t`, the integrating factor is at most `exp ((b - a) ‖K‖)`.
  have hint : ‖∫ s in a..t, (K (projIcc a b hab s) *
        Real.exp (-∫ r in s..t, K (projIcc a b hab r))) • y (projIcc a b hab s)‖ ≤
      ‖K‖ * Real.exp ((b - a) * ‖K‖) * ‖y‖ * |(t : ℝ) - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
    rw [uIoc_of_le t.2.1] at hs
    have hexp : Real.exp (-∫ r in s..t, K (projIcc a b hab r)) ≤
        Real.exp ((b - a) * ‖K‖) := by
      refine Real.exp_le_exp.2 ((neg_le_abs _).trans ?_)
      rw [← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r _ ↦
        norm_coe_le_norm K _).trans ?_
      rw [abs_of_nonneg (sub_nonneg.2 hs.2), mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith [hs.1, t.2.2]) (norm_nonneg K)
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (mul_le_mul (norm_coe_le_norm K _) hexp (Real.exp_pos _).le
      (norm_nonneg K)) (norm_coe_le_norm y _) (norm_nonneg _) (by positivity)
  calc ‖y t - ∫ s in a..t, (K (projIcc a b hab s) *
          Real.exp (-∫ r in s..t, K (projIcc a b hab r))) • y (projIcc a b hab s)‖
      ≤ ‖y‖ + ‖K‖ * Real.exp ((b - a) * ‖K‖) * ‖y‖ * (b - a) :=
        (norm_sub_le _ _).trans (add_le_add (norm_coe_le_norm y t)
          (hint.trans (mul_le_mul_of_nonneg_left ht (by positivity))))
    _ = (1 + (b - a) * ‖K‖ * Real.exp ((b - a) * ‖K‖)) * ‖y‖ := by ring

/-- **Causality** of the Volterra transform: its value at time `t` depends only on the path on
`[a, t]`. -/
theorem volterraTransform_apply_eq_of_eqOn_Iic {x y : C(Icc a b, E)} {t : Icc a b}
    (h : EqOn x y (Iic t)) :
    volterraTransform hab K x t = volterraTransform hab K y t := by
  simp only [volterraTransform_apply, h (mem_Iic.2 le_rfl)]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [h]
  rw [mem_Iic, ← Subtype.coe_le_coe, coe_projIcc_of_mem_uIcc hab t.2 hs]
  exact (uIcc_of_le t.2.1 ▸ hs).2

/-- **Causality** of the inverse Volterra transform: its value at time `t` depends only on the
path on `[a, t]`. -/
theorem volterraTransform_symm_apply_eq_of_eqOn_Iic {x y : C(Icc a b, E)} {t : Icc a b}
    (h : EqOn x y (Iic t)) :
    (volterraTransform hab K).symm x t = (volterraTransform hab K).symm y t := by
  simp only [volterraTransform_symm_apply, h (mem_Iic.2 le_rfl)]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [h]
  rw [mem_Iic, ← Subtype.coe_le_coe, coe_projIcc_of_mem_uIcc hab t.2 hs]
  exact (uIcc_of_le t.2.1 ▸ hs).2

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
  simp only [inclusion_projIcc_of_mem_uIcc hab hac hcb t.2 hs]

/-- The inverse Volterra transform commutes with restriction to a shorter horizon `[a, c]`. -/
theorem volterraTransform_symm_comp_inclusion (y : C(Icc a b, E)) :
    ((volterraTransform hab K).symm y).comp (.inclusion (Icc_subset_Icc_right hcb)) =
      (volterraTransform hac (K.comp (.inclusion (Icc_subset_Icc_right hcb)))).symm
        (y.comp (.inclusion (Icc_subset_Icc_right hcb))) := by
  ext t
  simp only [comp_apply, inclusion_apply_coe, volterraTransform_symm_apply]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  -- The inner integral runs over `[s, t] ⊆ [a, t]`.
  have hint : ∫ r in s..t, K (projIcc a b hab r) =
      ∫ r in s..t, K (ContinuousMap.inclusion (Icc_subset_Icc_right hcb) (projIcc a c hac r)) := by
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le t.2.1] at hs
    rw [uIcc_of_le hs.2] at hr
    rw [inclusion_projIcc_of_mem_uIcc hab hac hcb t.2
      (by rw [uIcc_of_le t.2.1]; exact ⟨hs.1.trans hr.1, hr.2⟩)]
  simp only [hint, inclusion_projIcc_of_mem_uIcc hab hac hcb t.2 hs]

end ContinuousMap
