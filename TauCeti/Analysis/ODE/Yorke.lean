/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.Analysis.Fourier.Wirtinger

/-!
# Yorke's lower bound for the periods of Lipschitz flows

Let `f` be a vector field on a finite-dimensional real inner product space `V` which is
`K`-Lipschitz along a solution `x` of `x' = f(x)`. **Yorke's theorem** says that if `x` returns to
its initial point after time `T > 0` without being constant, then `T ≥ 2π / K`
(`TauCeti.two_pi_le_mul_of_hasDerivAt_of_lipschitzOnWith`). Equivalently, a solution which
closes up after a time `T` with `K T < 2π` is constant
(`TauCeti.eqOn_const_of_hasDerivAt_of_lipschitzOnWith`). The constant `2π` is sharp: the linear
field `f(x) = K J x`, with `J` a rotation by a right angle in a plane, is `K`-Lipschitz and its
nonconstant orbits are circles of period exactly `2π / K`.

The proof applies Wirtinger's inequality to the velocity `y = f ∘ x`. It is Lipschitz, hence
absolutely continuous; it is periodic since `x` is; its mean vanishes, since its integral is the
displacement `x(b) - x(a) = 0`; and where it is differentiable its derivative satisfies
`‖y'‖ ≤ K ‖x'‖ = K ‖y‖`. Wirtinger's inequality
(`TauCeti.integral_norm_sub_average_sq_le`) then gives
`∫ ‖y‖² ≤ (T / 2π)² ∫ ‖y'‖² ≤ (K T / 2π)² ∫ ‖y‖²`, which forces `y = 0` when `K T < 2π`.

The Lipschitz condition is only needed on the orbit itself, which is what makes the theorem
usable in a chart of a manifold, where a vector field is Lipschitz only near a given point. A
Hamiltonian `εH` with `ε` small has a vector field with a small Lipschitz constant, so this is the
mechanism by which a `C²`-small autonomous Hamiltonian has no nonconstant `1`-periodic orbits.

## Main results

* `TauCeti.two_pi_le_mul_of_hasDerivAt_of_lipschitzOnWith`: a nonconstant solution on `[a, b]`
  with `x a = x b` has `2π ≤ K (b - a)`.
* `TauCeti.eqOn_const_of_hasDerivAt_of_lipschitzOnWith`: a solution on `[a, b]` with
  `x a = x b` and `K (b - a) < 2π` is constant on `[a, b]`.
* `Function.Periodic.eq_const_of_hasDerivAt_of_lipschitzOnWith`: a `T`-periodic solution on the
  whole line with `K T < 2π` is constant.
* `TauCeti.exists_pos_forall_periodic_eq_const_of_lipschitzOnWith`: in a finite-dimensional
  normed space, the same holds with `2π` replaced by a positive constant depending on the norm.

## References

* J. A. Yorke, *Periods of periodic solutions and the Lipschitz constant*, Proc. Amer. Math. Soc.
  22 (1969), 509–512.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped NNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {f : V → V} {x : ℝ → V} {K : ℝ≥0} {a b : ℝ}

omit [FiniteDimensional ℝ V] in
/-- The velocity `t ↦ f (x t)` of a solution of `x' = f(x)` on `[a, b]`, with `f` Lipschitz along
the solution, is Lipschitz on `[a, b]`. -/
private theorem exists_lipschitzOnWith_comp (hx : ∀ t ∈ Icc a b, HasDerivAt x (f (x t)) t)
    (hf : LipschitzOnWith K f (x '' Icc a b)) :
    ∃ M : ℝ≥0, (∀ t ∈ Icc a b, ‖f (x t)‖ ≤ M) ∧
      LipschitzOnWith (K * M) (fun t ↦ f (x t)) (Icc a b) := by
  have hxc : ContinuousOn x (Icc a b) := fun t ht ↦ (hx t ht).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn.comp hxc (mapsTo_image _ _))
  have hM' (t) (ht : t ∈ Icc a b) : ‖f (x t)‖ ≤ M.toNNReal :=
    (hM t ht).trans (Real.le_coe_toNNReal M)
  have hxlip : LipschitzOnWith M.toNNReal x (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ (hx t ht).hasDerivWithinAt) fun t ht ↦ by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact hM' t ht
  exact ⟨M.toNNReal, hM', hf.comp hxlip (mapsTo_image _ _)⟩

omit [FiniteDimensional ℝ V] in
/-- Where the velocity `t ↦ f (x t)` of a solution of `x' = f(x)` is differentiable, its
derivative is at most `K` times its size, `f` being `K`-Lipschitz along the solution. Elsewhere
`deriv` is `0`, so the bound holds on all of `(a, b)`. -/
private theorem norm_deriv_comp_le (hx : ∀ t ∈ Icc a b, HasDerivAt x (f (x t)) t)
    (hf : LipschitzOnWith K f (x '' Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b) :
    ‖deriv (fun t ↦ f (x t)) t‖ ≤ K * ‖f (x t)‖ := by
  by_cases hd : DifferentiableAt ℝ (fun t ↦ f (x t)) t
  · -- Compare the two components of `u ↦ (f (x u), x u)` near `t`.
    have hle : ∀ᶠ u in 𝓝 t, ‖f (x u) - f (x t)‖ ≤ K * ‖x u - x t‖ := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hf.dist_le_mul _ (mem_image_of_mem _ hu) _
        (mem_image_of_mem _ (Ioo_subset_Icc_self ht))
    simpa using (hd.hasDerivAt.prodMk (hx t (Ioo_subset_Icc_self ht))).hasFDerivAt
      |>.norm_apply_le_mul_norm_apply (L := ContinuousLinearMap.fst ℝ V V)
        (M := ContinuousLinearMap.snd ℝ V V) (by simpa using hle) 1
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    positivity

/-- **Wirtinger's inequality for the velocity.** The velocity `y = f ∘ x` of a closed solution of
`x' = f(x)` on `[a, b]`, with `f` `K`-Lipschitz along it, satisfies
`∫ ‖y‖² ≤ (K (b - a) / 2π)² ∫ ‖y‖²`. -/
private theorem integral_norm_sq_le (hab : a < b) (hx : ∀ t ∈ Icc a b, HasDerivAt x (f (x t)) t)
    (hf : LipschitzOnWith K f (x '' Icc a b)) (hxab : x a = x b) :
    ∫ t in a..b, ‖f (x t)‖ ^ 2 ≤
      (K * (b - a) / (2 * Real.pi)) ^ 2 * ∫ t in a..b, ‖f (x t)‖ ^ 2 := by
  set y : ℝ → V := fun t ↦ f (x t)
  obtain ⟨M, hM, hylip⟩ := exists_lipschitzOnWith_comp hx hf
  -- The hypotheses of Wirtinger's inequality for `y`: absolute continuity, an a.e. derivative,
  -- which is bounded, and equal values at the ends.
  have hyac : AbsolutelyContinuousOnInterval y a b :=
    (uIcc_of_le hab.le ▸ hylip).absolutelyContinuousOnInterval
  have hyd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt y (deriv y t) t := by
    have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
      rw [ae_iff]
      simp
    filter_upwards [hylip.ae_differentiableWithinAt_of_mem_real, hb] with t ht htb htI
    rw [uIoc_of_le hab.le] at htI
    exact ((ht (Ioc_subset_Icc_self htI)).differentiableAt
      (Icc_mem_nhds htI.1 (lt_of_le_of_ne htI.2 htb))).hasDerivAt
  have hy'L2 : MemLp (deriv y) 2 (volume.restrict (Ioc a b)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine MemLp.of_bound (stronglyMeasurable_deriv y).aestronglyMeasurable (K * M) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (norm_deriv_comp_le hx hf ht).trans (by gcongr; exact hM t (Ioo_subset_Icc_self ht))
  -- The velocity has mean zero, since its integral is the displacement `x b - x a = 0`.
  have hmean : ⨍ t in a..b, y t = 0 := by
    rw [interval_average_eq, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hx t (uIcc_of_le hab.le ▸ ht))
      (hylip.continuousOn.intervalIntegrable_of_Icc hab.le), hxab, sub_self, smul_zero]
  have hW := integral_norm_sub_average_sq_le hab hyac hyd (congrArg f hxab) hy'L2
  simp only [hmean, sub_zero] at hW
  -- Bound the derivative term by the velocity term.
  have hcomp : ∫ t in a..b, ‖deriv y t‖ ^ 2 ≤ K ^ 2 * ∫ t in a..b, ‖y t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on_of_le_Ioo hab.le
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
        (hy'L2.integrable_norm_pow two_ne_zero))
      (((continuous_pow 2).comp_continuousOn hylip.continuousOn.norm).intervalIntegrable_of_Icc
        hab.le |>.const_mul _) fun t ht ↦ ?_
    rw [← mul_pow]
    gcongr
    exact norm_deriv_comp_le hx hf ht
  calc ∫ t in a..b, ‖y t‖ ^ 2 ≤ ((b - a) / (2 * Real.pi)) ^ 2 * ∫ t in a..b, ‖deriv y t‖ ^ 2 := hW
    _ ≤ ((b - a) / (2 * Real.pi)) ^ 2 * (K ^ 2 * ∫ t in a..b, ‖y t‖ ^ 2) := by gcongr
    _ = (K * (b - a) / (2 * Real.pi)) ^ 2 * ∫ t in a..b, ‖y t‖ ^ 2 := by ring

/-- **Yorke's theorem.** Let `x` solve `x' = f(x)` on `[a, b]`, with `f` `K`-Lipschitz along the
solution, and return to its initial point, `x a = x b`. If `K (b - a) < 2π`, then `x` is constant
on `[a, b]`. -/
theorem eqOn_const_of_hasDerivAt_of_lipschitzOnWith
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (f (x t)) t) (hf : LipschitzOnWith K f (x '' Icc a b))
    (hxab : x a = x b) (hK : K * (b - a) < 2 * Real.pi) : EqOn x (fun _ ↦ x a) (Icc a b) := by
  rcases lt_or_ge a b with hab | hba
  swap
  · intro t ht
    simp [le_antisymm (ht.2.trans hba) ht.1]
  set y : ℝ → V := fun t ↦ f (x t)
  obtain ⟨_, -, hylip⟩ := exists_lipschitzOnWith_comp hx hf
  have hyc : ContinuousOn y (Icc a b) := hylip.continuousOn
  have hy2c : ContinuousOn (fun t ↦ ‖y t‖ ^ 2) (Icc a b) := (continuous_pow 2).comp_continuousOn
    hyc.norm
  -- `∫ ‖y‖² ≤ q ∫ ‖y‖²` with `q = (K (b - a) / 2π)² < 1`, so the integral vanishes.
  have hq : (K * (b - a) / (2 * Real.pi)) ^ 2 < 1 := by
    rw [sq_lt_one_iff₀ (by positivity), div_lt_one (by positivity)]
    exact hK
  have hI0 : 0 ≤ ∫ t in a..b, ‖y t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun _ _ ↦ by positivity
  have hI : ∫ t in a..b, ‖y t‖ ^ 2 = 0 :=
    le_antisymm (by nlinarith [integral_norm_sq_le hab hx hf hxab]) hI0
  -- A continuous function with vanishing square integral vanishes on `(a, b)`, hence on `[a, b]`.
  have hzero := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun _ ↦ by positivity) (hy2c.intervalIntegrable_of_Icc hab.le)).1 hI
  have hyzero : EqOn y 0 (Icc a b) := by
    refine EqOn.of_subset_closure (fun t ht ↦ ?_) hyc continuousOn_const Ioo_subset_Icc_self
      (closure_Ioo hab.ne).ge
    have h := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
      (fun t ht ↦ Or.inl (Ioo_subset_Ioc_self ht)) hzero) isOpen_Ioo
      (hy2c.mono Ioo_subset_Icc_self) continuousOn_const ht
    simpa using h
  -- So `x` has zero derivative, and is constant.
  exact constant_of_has_deriv_right_zero
    (fun t ht ↦ (hx t ht).continuousAt.continuousWithinAt) fun t ht ↦
      ((hx t (Ico_subset_Icc_self ht)).congr_deriv
        (hyzero (Ico_subset_Icc_self ht))).hasDerivWithinAt

/-- **Yorke's theorem**, lower bound form. A solution of `x' = f(x)` on `[a, b]`, with `f`
`K`-Lipschitz along the solution, which returns to its initial point, `x a = x b`, without being
constant on `[a, b]`, takes time at least `2π / K`: `2π ≤ K (b - a)`. -/
theorem two_pi_le_mul_of_hasDerivAt_of_lipschitzOnWith
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (f (x t)) t) (hf : LipschitzOnWith K f (x '' Icc a b))
    (hxab : x a = x b) {t : ℝ} (ht : t ∈ Icc a b) (hxt : x t ≠ x a) :
    2 * Real.pi ≤ K * (b - a) := by
  by_contra hK
  exact hxt (eqOn_const_of_hasDerivAt_of_lipschitzOnWith hx hf hxab (not_le.1 hK) ht)

end TauCeti

namespace Function.Periodic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {f : V → V} {x : ℝ → V} {K : ℝ≥0} {T : ℝ}

/-- **Yorke's theorem** for periodic solutions. A `T`-periodic solution of `x' = f(x)` on the whole
line, `T > 0`, with `f` `K`-Lipschitz along the solution and `K T < 2π`, is constant. -/
theorem eq_const_of_hasDerivAt_of_lipschitzOnWith (hper : Periodic x T) (hT : 0 < T)
    (hx : ∀ t, HasDerivAt x (f (x t)) t) (hf : LipschitzOnWith K f (range x))
    (hK : K * T < 2 * Real.pi) : x = fun _ ↦ x 0 := by
  have h := TauCeti.eqOn_const_of_hasDerivAt_of_lipschitzOnWith (a := 0) (b := 0 + T)
    (fun t _ ↦ hx t) (hf.mono (image_subset_range _ _)) (hper 0).symm (by simpa using hK)
  -- Every value of `x` is taken on `[0, T]`, where `x` is constant.
  funext t
  obtain ⟨s, hs, hst⟩ : x t ∈ x '' Icc 0 (0 + T) := hper.image_Icc hT 0 ▸ mem_range_self t
  rw [← hst]
  exact h hs

end Function.Periodic

namespace TauCeti

open Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Yorke's theorem in a finite-dimensional normed space.** There is a constant `c > 0`,
depending only on the norm, such that every `T`-periodic solution of `x' = f(x)` on the whole
line, `T > 0`, with `f` `K`-Lipschitz along the solution and `K T < c`, is constant. For an inner
product norm one can take `c = 2π` (`Function.Periodic.eq_const_of_hasDerivAt_of_lipschitzOnWith`);
in general the norm is compared with a Euclidean one. -/
theorem exists_pos_forall_periodic_eq_const_of_lipschitzOnWith :
    ∃ c > (0 : ℝ), ∀ (f : E → E) (x : ℝ → E) (K : ℝ≥0) (T : ℝ), Periodic x T → 0 < T →
      (∀ t, HasDerivAt x (f (x t)) t) → LipschitzOnWith K f (range x) → K * T < c →
        x = fun _ ↦ x 0 := by
  set A := toEuclidean (E := E)
  set L : ℝ≥0 := ‖A.toContinuousLinearMap‖₊ * ‖A.symm.toContinuousLinearMap‖₊
  refine ⟨2 * Real.pi / (L + 1), by positivity, fun f x K T hper hT hx hf hK ↦ ?_⟩
  -- In Euclidean coordinates `A ∘ x` solves `w' = A (f (A⁻¹ w))`, which is `K L`-Lipschitz along
  -- the solution.
  have hxA (t : ℝ) : HasDerivAt (fun t ↦ A (x t)) (A (f (A.symm (A (x t))))) t := by
    convert A.hasFDerivAt.comp_hasDerivAt t (hx t) using 1
    · rfl
    · rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.coe_coe]
  have hlip : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * (K * ‖A.symm.toContinuousLinearMap‖₊))
      (fun w ↦ A (f (A.symm w))) (range fun t ↦ A (x t)) := by
    refine A.toContinuousLinearMap.lipschitzWith.comp_lipschitzOnWith
      (hf.comp A.symm.toContinuousLinearMap.lipschitzWith.lipschitzOnWith ?_)
    rintro _ ⟨t, rfl⟩
    simp
  have hKL : ↑(‖A.toContinuousLinearMap‖₊ * (K * ‖A.symm.toContinuousLinearMap‖₊)) * T <
      2 * Real.pi := by
    have hKT : (K : ℝ) * T * (L + 1) < 2 * Real.pi := (lt_div_iff₀ (by positivity)).1 hK
    have hL : (‖A.toContinuousLinearMap‖₊ * (K * ‖A.symm.toContinuousLinearMap‖₊) : ℝ≥0) =
        K * L := by
      simp only [L]
      ring
    rw [hL, NNReal.coe_mul]
    nlinarith [mul_nonneg K.coe_nonneg hT.le]
  have h := Periodic.eq_const_of_hasDerivAt_of_lipschitzOnWith (fun t ↦ by simp [hper t]) hT
    hxA hlip hKL
  funext t
  exact A.injective (congrFun h t)

end TauCeti
