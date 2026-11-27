/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
public import TauCeti.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint
public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Commutant
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Calderón–Zygmund operators

A **Calderón–Zygmund operator** on a finite-dimensional real inner product space `V` of dimension
`n` is a bounded linear operator `T` on `L²(V)` which, away from the support of its argument, is
integration against a **standard kernel** `K`: `‖K x y‖ ≤ C / dist x y ^ n`, `K` is `δ`-Hölder in
each variable off the diagonal at the scale of `dist x y`, and `T f x = ∫ K x y f y dy` for almost
every `x` outside a compact set carrying `f` (`TauCeti.HasStandardKernel`). This file proves the
basic theorems about this class.

* **Adjoints.** The adjoint of an `L²` operator with an off-diagonal kernel `k` has the transposed
  kernel `(x, y) ↦ (k y x)†` (`ContinuousLinearMap.ae_adjoint_apply_eq_integral`, proved for any
  proper metric measure space and operator-valued kernels bounded away from the diagonal in
  `TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint`). Hence the adjoint of a
  Calderón–Zygmund operator with kernel `K` is a Calderón–Zygmund operator with the kernel
  `(x, y) ↦ conj (K y x)` and the same constants (`TauCeti.HasStandardKernel.adjoint`).
* **The Calderón–Zygmund theorem.** A Calderón–Zygmund operator is of weak type `(1, 1)`
  (`TauCeti.HasStandardKernel.exists_mul_volume_lt_enorm_le`) and bounded in the `Lᵖ` norm for
  every `1 < p < ∞` (`TauCeti.HasStandardKernel.exists_eLpNorm_le`), with constants depending
  only on `p`, `C`, `δ`, a bound for `‖T‖` and the dimension of `V`
  (`TauCeti.exists_mul_volume_lt_enorm_le_of_hasStandardKernel`,
  `TauCeti.exists_eLpNorm_le_of_hasStandardKernel`). A standard kernel satisfies Hörmander's
  condition with a bound depending only on `C`, `δ` and `V`
  (`TauCeti.HasStandardKernel.setLIntegral_enorm_sub_le`), so these are the real
  Calderón–Zygmund theorems under Hörmander's condition on `V`
  (`TauCeti.exists_mul_volume_lt_enorm_le_of_hormander`, `TauCeti.exists_eLpNorm_le_of_hormander`),
  whose hypotheses on the adjoint the adjoint theorem supplies.
* **The kernel and the operator.** The kernel is determined by the operator off the diagonal
  (`TauCeti.HasStandardKernel.unique`), but the operator is not determined by the kernel: adding a
  multiplication operator by an `L∞` function does not change the kernel
  (`TauCeti.HasStandardKernel.add_multiplicationOperator`), and on scalar functions two
  Calderón–Zygmund operators with the same kernel differ by such a multiplication operator
  (`TauCeti.HasStandardKernel.exists_sub_eq_multiplicationOperator`), since their difference does
  not enlarge compact supports (`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_isCompact`).
  So the operator, not the kernel, is the primitive datum, and the operators with the kernel of
  one Calderón–Zygmund operator `T` are the `T + M_a`
  (`TauCeti.HasStandardKernel.hasStandardKernel_iff_exists_eq_add`).
* **Examples.** The identity has the kernel `0` (`TauCeti.hasStandardKernel_id`), and the Riesz
  transforms are Calderón–Zygmund operators (`TauCeti.hasStandardKernel_rieszTransform`). A
  difference kernel `(x, y) ↦ k (x - y)` satisfies the smoothness estimate in both variables once
  `k` satisfies it in one (`TauCeti.norm_sub_add_norm_sub_le_of_norm_sub_le`).

The definition asks nothing of `K` on the diagonal, and no measurability: the smoothness estimate
makes `K` continuous off the diagonal (`TauCeti.HasStandardKernel.continuousOn_uncurry`), which is
all the measure theory needs. Boundedness on `L²` is part of the definition, since the kernel
estimates do not imply it: multiplication by `x` on `ℝ` has the kernel `0` off the diagonal and is
unbounded.

## References

* E. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory Integrals*,
  Chapter I, §6, and Chapter VII, §3.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3 (standard kernels and the
  Calderón–Zygmund theorem, Theorem 5.3.3).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate Topology

namespace TauCeti

/-- **The smoothness estimate for a difference kernel.** If `k` satisfies the one-variable estimate
`‖k a - k b‖ ≤ c ‖a - b‖ ^ δ / ‖b‖ ^ e` whenever `2 ‖a - b‖ < ‖b‖`, then the kernel
`(x, y) ↦ k (x - y)` satisfies the smoothness estimate in both variables with the constant `2 c`,
as in the field `TauCeti.HasStandardKernel.norm_sub_add_norm_sub_le`. -/
theorem norm_sub_add_norm_sub_le_of_norm_sub_le {X E : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup E] {k : X → E} {c δ e : ℝ}
    (hk : ∀ a b, 2 * ‖a - b‖ < ‖b‖ → ‖k a - k b‖ ≤ c * ‖a - b‖ ^ δ / ‖b‖ ^ e) {x y y' : X}
    (hy : 2 * dist y y' < dist x y) :
    ‖k (x - y) - k (x - y')‖ + ‖k (y - x) - k (y' - x)‖ ≤
      2 * c * dist y y' ^ δ / dist x y ^ e := by
  have b₁ := hk (x - y') (x - y) (by rwa [sub_sub_sub_cancel_left, ← dist_eq_norm, ← dist_eq_norm])
  have b₂ := hk (y' - x) (y - x) (by
    rwa [sub_sub_sub_cancel_right, ← dist_eq_norm, ← dist_eq_norm, dist_comm y' y, dist_comm y x])
  rw [sub_sub_sub_cancel_left, norm_sub_rev (k _), ← dist_eq_norm y, ← dist_eq_norm x] at b₁
  rw [sub_sub_sub_cancel_right, norm_sub_rev (k _), ← dist_eq_norm y', ← dist_eq_norm y,
    dist_comm y' y, dist_comm y x] at b₂
  exact (add_le_add b₁ b₂).trans_eq (by ring)

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Calderón–Zygmund operators.** A bounded operator `T` on `L²(V, F)` **has the standard kernel**
`K` with constant `C` and exponent `δ > 0` when, writing `n` for the dimension of `V`,

* `K` satisfies the size estimate `‖K x y‖ ≤ C / dist x y ^ n` for `x ≠ y`;
* `K` satisfies the smoothness estimate in both variables,
  `‖K x y - K x y'‖ + ‖K y x - K y' x‖ ≤ C dist y y' ^ δ / dist x y ^ (n + δ)` whenever
  `2 dist y y' < dist x y`;
* `T` is given by `K` away from the support of its argument: if `f` vanishes outside a compact
  set `s`, then `T f x = ∫ K x y • f y dy` for almost every `x ∉ s`.

Such a `T` is a **Calderón–Zygmund operator**. Boundedness on `L²` is part of the data, since the
kernel estimates alone do not imply it: multiplication by `x` on `ℝ` has the kernel `0` off the
diagonal but is unbounded on `L²`. The kernel acts on `F`-valued functions by scalar
multiplication, as the Riesz transforms do. -/
structure HasStandardKernel (T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (K : V → V → ℂ) (C : ℝ≥0) (δ : ℝ) : Prop where
  /-- The smoothness exponent is positive. -/
  exponent_pos : 0 < δ
  /-- The size estimate. -/
  norm_le : ∀ x y, x ≠ y → ‖K x y‖ ≤ C / dist x y ^ Module.finrank ℝ V
  /-- The smoothness estimate in both variables. -/
  norm_sub_add_norm_sub_le : ∀ x y y', 2 * dist y y' < dist x y →
    ‖K x y - K x y'‖ + ‖K y x - K y' x‖ ≤
      C * dist y y' ^ δ / dist x y ^ (Module.finrank ℝ V + δ)
  /-- `T` is integration against `K` away from the support of its argument. -/
  ae_apply_eq_integral : ∀ (f : Lp F 2 (volume : Measure V)) (s : Set V), IsCompact s →
    (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ y, K x y • f y

namespace HasStandardKernel

variable {T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)} {K : V → V → ℂ}
  {C : ℝ≥0} {δ : ℝ}

/-- The estimates of a standard kernel persist under a larger constant. -/
theorem mono (h : HasStandardKernel T K C δ) {C' : ℝ≥0} (hC : C ≤ C') :
    HasStandardKernel T K C' δ where
  exponent_pos := h.exponent_pos
  norm_le x y hxy := (h.norm_le x y hxy).trans (by gcongr)
  norm_sub_add_norm_sub_le x y y' hy := (h.norm_sub_add_norm_sub_le x y y' hy).trans (by gcongr)
  ae_apply_eq_integral := h.ae_apply_eq_integral

/-- A standard kernel is continuous off the diagonal. -/
theorem continuousOn_uncurry (h : HasStandardKernel T K C δ) :
    ContinuousOn (Function.uncurry K) {p : V × V | p.1 ≠ p.2} := by
  rintro ⟨x₀, y₀⟩ (hxy : x₀ ≠ y₀)
  refine ContinuousAt.continuousWithinAt ?_
  have hd : 0 < dist x₀ y₀ := dist_pos.2 hxy
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  -- The two smoothness estimates bound the oscillation of `K` near `(x₀, y₀)` by `b`.
  set b : V × V → ℝ := fun p ↦ C * dist p.2 y₀ ^ δ / dist p.1 p.2 ^ (n + δ) +
    C * dist p.1 x₀ ^ δ / dist y₀ p.1 ^ (n + δ)
  have hδ := h.exponent_pos
  have hb : ContinuousAt b (x₀, y₀) := by
    have hpow : ∀ {f : V × V → ℝ}, Continuous f → (∀ p, 0 ≤ f p) → ∀ {e : ℝ}, 0 ≤ e →
        Continuous fun p ↦ f p ^ e := fun hf _ _ he ↦ hf.rpow_const fun _ ↦ Or.inr he
    refine ContinuousAt.add (ContinuousAt.div ?_ ?_ ?_) (ContinuousAt.div ?_ ?_ ?_)
    · exact (continuous_const.mul (hpow (continuous_snd.dist continuous_const)
        (fun _ ↦ dist_nonneg) hδ.le)).continuousAt
    · exact (hpow (continuous_fst.dist continuous_snd) (fun _ ↦ dist_nonneg)
        (by positivity)).continuousAt
    · exact (Real.rpow_pos_of_pos hd _).ne'
    · exact (continuous_const.mul (hpow (continuous_fst.dist continuous_const)
        (fun _ ↦ dist_nonneg) hδ.le)).continuousAt
    · exact (hpow (continuous_const.dist continuous_fst) (fun _ ↦ dist_nonneg)
        (by positivity)).continuousAt
    · exact (Real.rpow_pos_of_pos (dist_comm x₀ y₀ ▸ hd) _).ne'
  have hb0 : b (x₀, y₀) = 0 := by simp [b, Real.zero_rpow hδ.ne']
  have h₁ : ∀ᶠ p : V × V in 𝓝 (x₀, y₀), 2 * dist p.2 y₀ < dist p.1 p.2 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hd)
  have h₂ : ∀ᶠ p : V × V in 𝓝 (x₀, y₀), 2 * dist p.1 x₀ < dist y₀ p.1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa [dist_comm] using hd)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ (hb0 ▸ hb.tendsto)
  filter_upwards [h₁, h₂] with ⟨x, y⟩ hp₁ hp₂
  calc ‖K x y - K x₀ y₀‖ ≤ ‖K x y - K x y₀‖ + ‖K x y₀ - K x₀ y₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ b (x, y) := add_le_add
        ((le_add_of_nonneg_right (norm_nonneg _)).trans (h.norm_sub_add_norm_sub_le x y y₀ hp₁))
        ((le_add_of_nonneg_left (norm_nonneg _)).trans (h.norm_sub_add_norm_sub_le y₀ x x₀ hp₂))

/-! ### The kernel modified on the diagonal

The estimates say nothing about `K` on the diagonal, where it need not even be measurable. The
real Calderón–Zygmund theorems and the kernel of the adjoint take a strongly measurable
operator-valued kernel, so they are applied to `K` set to `0` on the diagonal, which is continuous
off the diagonal. The change is invisible in the integrals `∫ K x y • f y dy` for `x` outside the
set carrying `f`. -/

open scoped Classical in
/-- The kernel `K` set to `0` on the diagonal. -/
private def offDiag (K : V → V → ℂ) (x y : V) : ℂ := if x = y then 0 else K x y

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
private theorem offDiag_of_ne {x y : V} (hxy : x ≠ y) : offDiag K x y = K x y := by
  simp [offDiag, hxy]

private theorem stronglyMeasurable_offDiag (h : HasStandardKernel T K C δ) :
    StronglyMeasurable (Function.uncurry (offDiag K)) := by
  classical
  have : Function.uncurry (offDiag K) =
      {p : V × V | p.1 ≠ p.2}.piecewise (Function.uncurry K) 0 := by
    ext ⟨x, y⟩
    by_cases hxy : x = y <;> simp [offDiag, hxy, Set.piecewise]
  rw [this]
  exact (h.continuousOn_uncurry.measurable_piecewise continuousOn_const
    (isOpen_ne_fun continuous_fst continuous_snd).measurableSet).stronglyMeasurable

/-- Changing a kernel on the diagonal does not change its integrals at points outside the set
carrying the integrand. -/
private theorem integral_offDiag_smul (K : V → V → ℂ) {f : V → F} {s : Set V}
    (hf : ∀ᵐ y, y ∉ s → f y = 0) {x : V} (hx : x ∉ s) :
    ∫ y, offDiag K x y • f y = ∫ y, K x y • f y := by
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  by_cases hxy : x = y
  · subst hxy
    simp [hy hx]
  · rw [offDiag_of_ne hxy]

private theorem norm_offDiag_le (h : HasStandardKernel T K C δ) {x y : V} (hxy : x ≠ y) :
    ‖offDiag K x y‖ ≤ C * dist x y ^ (-(Module.finrank ℝ V : ℝ)) := by
  rw [offDiag_of_ne hxy, Real.rpow_neg dist_nonneg, Real.rpow_natCast, ← div_eq_mul_inv]
  exact h.norm_le x y hxy

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Changing a kernel on the diagonal does not change its differences on the set where Hörmander's
condition integrates. -/
private theorem offDiag_sub_offDiag {x y y' : V} (hy : 2 * dist y y' < dist x y') :
    offDiag K x y - offDiag K x y' = K x y - K x y' := by
  have hxy' : x ≠ y' := dist_pos.1 ((mul_nonneg zero_le_two dist_nonneg).trans_lt hy)
  have hxy : x ≠ y := by
    rintro rfl
    linarith [dist_nonneg (x := x) (y := y')]
  rw [offDiag_of_ne hxy, offDiag_of_ne hxy']

/-- The smoothness estimate in the second variable, in the form taken by Hörmander's condition. -/
private theorem norm_sub_le_mul_rpow (h : HasStandardKernel T K C δ) {x y y' : V}
    (hy : 2 * dist y y' < dist x y') :
    ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))) := by
  rw [norm_sub_rev, Real.rpow_neg dist_nonneg, ← mul_assoc, ← div_eq_mul_inv, dist_comm y y']
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans
    (h.norm_sub_add_norm_sub_le x y' y (by rwa [dist_comm y' y]))

/-- **Hörmander's condition.** A standard kernel satisfies Hörmander's integral condition, with a
bound depending only on `C`, `δ` and `V`. -/
theorem setLIntegral_enorm_sub_le (h : HasStandardKernel T K C δ) (y y' : V) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤
      C * volume (ball (0 : V) 1) *
        ENNReal.ofReal (2 ^ (Module.finrank ℝ V : ℝ) / (2 ^ δ - 1)) :=
  setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow
    (fun r hr ↦ by rw [Measure.addHaar_closedBall _ _ hr.le, Real.rpow_natCast, mul_comm])
    h.exponent_pos fun _ hx ↦ h.norm_sub_le_mul_rpow hx

variable (V C δ) in
/-- The bound in Hörmander's condition (`TauCeti.HasStandardKernel.setLIntegral_enorm_sub_le`) is
finite. -/
private theorem coe_mul_volume_ball_mul_ofReal_ne_top :
    C * volume (ball (0 : V) 1) *
      ENNReal.ofReal (2 ^ (Module.finrank ℝ V : ℝ) / (2 ^ δ - 1)) ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top measure_ball_lt_top.ne)
    ENNReal.ofReal_ne_top

section OpKernel

variable {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 ℂ F]

variable (F 𝕜) in
/-- The kernel as a `𝕜`-linear operator-valued kernel `v ↦ K x y • v`, set to `0` on the
diagonal. For `𝕜 = ℝ` it is in the form taken by the real Calderón–Zygmund theorems, and for
`𝕜 = ℂ` in the form taken by `ContinuousLinearMap.ae_adjoint_apply_eq_integral`. -/
private def opKernel (K : V → V → ℂ) (x y : V) : F →L[𝕜] F :=
  ContinuousLinearMap.lsmul 𝕜 ℂ (offDiag K x y)

private theorem stronglyMeasurable_opKernel (h : HasStandardKernel T K C δ) :
    StronglyMeasurable (Function.uncurry (opKernel F 𝕜 K)) :=
  (ContinuousLinearMap.lsmul 𝕜 ℂ).continuous.comp_stronglyMeasurable
    h.stronglyMeasurable_offDiag

private theorem norm_opKernel_le (h : HasStandardKernel T K C δ) (x y : V) (hxy : x ≠ y) :
    ‖opKernel F 𝕜 K x y‖ ≤ C * dist x y ^ (-(Module.finrank ℝ V : ℝ)) :=
  (ContinuousLinearMap.opNorm_lsmul_apply_le _).trans (h.norm_offDiag_le hxy)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem norm_opKernel_sub_le {x y y' : V} (hy : 2 * dist y y' < dist x y') :
    ‖opKernel F 𝕜 K x y - opKernel F 𝕜 K x y'‖ ≤ ‖K x y - K x y'‖ := by
  rw [opKernel, opKernel, ← map_sub, offDiag_sub_offDiag hy]
  exact ContinuousLinearMap.opNorm_lsmul_apply_le _

/-- Hörmander's condition (`TauCeti.HasStandardKernel.setLIntegral_enorm_sub_le`) for the
operator-valued kernel. -/
private theorem setLIntegral_enorm_opKernel_sub_le (h : HasStandardKernel T K C δ) (y y' : V) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖opKernel F 𝕜 K x y - opKernel F 𝕜 K x y'‖ₑ ≤
      C * volume (ball (0 : V) 1) *
        ENNReal.ofReal (2 ^ (Module.finrank ℝ V : ℝ) / (2 ^ δ - 1)) :=
  (setLIntegral_mono' (measurableSet_lt measurable_const (by fun_prop))
    fun _ hx ↦ eNorm_le_iff_norm_le.2 (norm_opKernel_sub_le hx)).trans
    (h.setLIntegral_enorm_sub_le y y')

private theorem ae_apply_eq_integral_opKernel (h : HasStandardKernel T K C δ)
    (f : Lp F 2 (volume : Measure V)) (s : Set V) (hs : IsCompact s)
    (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → T f x = ∫ z, opKernel F 𝕜 K x z (f z) := by
  filter_upwards [h.ae_apply_eq_integral f s hs hf] with x hx hxs
  rw [hx hxs, ← integral_offDiag_smul K hf hxs]
  simp [opKernel]

/-- `ae_apply_eq_integral_opKernel` for the realification `T.restrictScalars ℝ`, the operator
taken by the real Calderón–Zygmund theorems. -/
private theorem ae_restrictScalars_apply_eq_integral_opKernel (h : HasStandardKernel T K C δ)
    (f : Lp F 2 (volume : Measure V)) (s : Set V) (hs : IsCompact s)
    (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → T.restrictScalars ℝ f x = ∫ z, opKernel F ℝ K x z (f z) := by
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using
    h.ae_apply_eq_integral_opKernel f s hs hf

end OpKernel

/-! ### Adjoints and the Calderón–Zygmund bounds -/

variable [CompleteSpace F]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The adjoint of the operator kernel is the operator kernel of the conjugate transposed kernel
`(x, y) ↦ conj (K y x)`. -/
private theorem adjoint_opKernel (x y : V) :
    ContinuousLinearMap.adjoint (opKernel F ℂ K x y) =
      opKernel F ℂ (fun x y ↦ conj (K y x)) y x := by
  ext v
  by_cases hxy : x = y
  · simp [opKernel, offDiag, hxy]
  · have hid : ContinuousLinearMap.lsmul ℂ ℂ (K x y) = K x y • ContinuousLinearMap.id ℂ F := by
      ext; simp
    simp [opKernel, offDiag_of_ne hxy, offDiag_of_ne (Ne.symm hxy), hid, map_smulₛₗ,
      ContinuousLinearMap.adjoint_id]

/-- **Calderón–Zygmund operators are closed under adjoints.** The adjoint of a Calderón–Zygmund
operator with kernel `K` is a Calderón–Zygmund operator with the conjugate transposed kernel
`(x, y) ↦ conj (K y x)`, with the same constants. -/
theorem adjoint (h : HasStandardKernel T K C δ) :
    HasStandardKernel (ContinuousLinearMap.adjoint T) (fun x y ↦ conj (K y x)) C δ where
  exponent_pos := h.exponent_pos
  norm_le x y hxy := by simpa [dist_comm] using h.norm_le y x hxy.symm
  norm_sub_add_norm_sub_le x y y' hy := by
    simpa only [← map_sub, RCLike.norm_conj, add_comm] using h.norm_sub_add_norm_sub_le x y y' hy
  ae_apply_eq_integral g s hs hg := by
    have hk : ∀ r > 0, ∃ M, ∀ x y, r ≤ dist x y → ‖opKernel F ℂ K x y‖ ≤ M := fun r hr ↦
      ⟨C * r ^ (-(Module.finrank ℝ V : ℝ)), fun x y hxy ↦
        (h.norm_opKernel_le x y (dist_pos.1 (hr.trans_le hxy))).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hr hxy (neg_nonpos.2 (Nat.cast_nonneg _))) C.property)⟩
    filter_upwards [ContinuousLinearMap.ae_adjoint_apply_eq_integral T
      h.stronglyMeasurable_opKernel hk h.ae_apply_eq_integral_opKernel g hs hg] with x hx hxs
    simp_rw [hx hxs, adjoint_opKernel]
    rw [← integral_offDiag_smul (fun x y ↦ conj (K y x)) hg hxs]
    simp [opKernel]

/-- **Calderón–Zygmund operators are of weak type `(1, 1)`, uniformly.** Given `C`, `δ` and `M`,
there is a constant `A` with `t · |{x | ‖T f x‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`,
whenever `T` is a Calderón–Zygmund operator with constant `C`, exponent `δ` and `‖T‖ ≤ M`. So `A`
depends only on `C`, `δ`, `M` and the dimension of `V`, and the bound holds uniformly over families
of operators. -/
theorem _root_.TauCeti.exists_mul_volume_lt_enorm_le_of_hasStandardKernel (C : ℝ≥0) (δ M : ℝ) :
    ∃ A : ℝ≥0, ∀ (T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
      (K : V → V → ℂ), ‖T‖ ≤ M → HasStandardKernel T K C δ →
      ∀ (f : Lp F 2 (volume : Measure V)) (t : ℝ≥0∞),
        t * volume {x | t < ‖T f x‖ₑ} ≤ A * eLpNorm f 1 volume := by
  have hB := coe_mul_volume_ball_mul_ofReal_ne_top V C δ
  obtain ⟨A, hA⟩ := exists_mul_volume_lt_enorm_le_of_hormander (V := V) (E := F) (F := F)
    (M := .ofReal M) ENNReal.ofReal_ne_top hB
  refine ⟨A, fun T K hT h f t ↦ ?_⟩
  rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f)]
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using
    hA (T.restrictScalars ℝ) (opKernel F ℝ K)
      (by
        rw [← ofReal_norm, ContinuousLinearMap.norm_restrictScalars]
        exact ENNReal.ofReal_le_ofReal hT)
      h.stronglyMeasurable_opKernel h.setLIntegral_enorm_opKernel_sub_le
      h.ae_restrictScalars_apply_eq_integral_opKernel f t

/-- **Calderón–Zygmund operators are of weak type `(1, 1)`**: there is a constant `A` with
`t · |{x | ‖T f x‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`. A Calderón–Zygmund operator
need not be bounded on `L¹`, and this is the substitute at the endpoint. The constant depends only
on `C`, `δ`, `‖T‖` and the dimension of `V`
(`TauCeti.exists_mul_volume_lt_enorm_le_of_hasStandardKernel`). -/
theorem exists_mul_volume_lt_enorm_le (h : HasStandardKernel T K C δ) :
    ∃ A : ℝ≥0, ∀ (f : Lp F 2 (volume : Measure V)) (t : ℝ≥0∞),
      t * volume {x | t < ‖T f x‖ₑ} ≤ A * eLpNorm f 1 volume :=
  let ⟨A, hA⟩ := exists_mul_volume_lt_enorm_le_of_hasStandardKernel (V := V) (F := F) C δ ‖T‖
  ⟨A, hA T K le_rfl h⟩

/-- **Calderón–Zygmund operators are bounded on `Lᵖ`, uniformly**, for `1 < p < ∞`. Given `C`, `δ`
and `M`, there is a constant `A` with `‖T f‖_p ≤ A ‖f‖_p` for every `f ∈ L²`, whenever `T` is a
Calderón–Zygmund operator with constant `C`, exponent `δ` and `‖T‖ ≤ M`. So `A` depends only on
`p`, `C`, `δ`, `M` and the dimension of `V`, and the bound holds uniformly over families of
operators. The adjoint of `T` is a Calderón–Zygmund operator with the same constants
(`TauCeti.HasStandardKernel.adjoint`), which gives the range `p > 2` by duality. -/
theorem _root_.TauCeti.exists_eLpNorm_le_of_hasStandardKernel (C : ℝ≥0) (δ M : ℝ) {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ A : ℝ≥0, ∀ (T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
      (K : V → V → ℂ), ‖T‖ ≤ M → HasStandardKernel T K C δ →
      ∀ f : Lp F 2 (volume : Measure V), eLpNorm (T f) p volume ≤ A * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hB := coe_mul_volume_ball_mul_ofReal_ne_top V C δ
  obtain ⟨A, hA⟩ := exists_eLpNorm_le_of_hormander (V := V) (H := F) (K := F)
    (M := .ofReal M) ENNReal.ofReal_ne_top hB hB hp hp_top
  refine ⟨A, fun T K hT h f ↦ ?_⟩
  have h' := h.adjoint
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using
    hA (T.restrictScalars ℝ) (opKernel F ℝ K) (opKernel F ℝ fun x y ↦ conj (K y x))
      (by
        rw [← ofReal_norm, ContinuousLinearMap.norm_restrictScalars]
        exact ENNReal.ofReal_le_ofReal hT)
      h.stronglyMeasurable_opKernel h'.stronglyMeasurable_opKernel
      h.setLIntegral_enorm_opKernel_sub_le h'.setLIntegral_enorm_opKernel_sub_le
      h.ae_restrictScalars_apply_eq_integral_opKernel
      (fun f s hs hf ↦ by
        rw [L2.adjoint_restrictScalars]
        exact h'.ae_restrictScalars_apply_eq_integral_opKernel f s hs hf) f

/-- **Calderón–Zygmund operators are bounded on `Lᵖ`** for `1 < p < ∞`: there is a constant `A`
with `‖T f‖_p ≤ A ‖f‖_p` for every `f ∈ L²`. The constant depends only on `p`, `C`, `δ`, `‖T‖` and
the dimension of `V` (`TauCeti.exists_eLpNorm_le_of_hasStandardKernel`). -/
theorem exists_eLpNorm_le (h : HasStandardKernel T K C δ) {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ A : ℝ≥0, ∀ f : Lp F 2 (volume : Measure V),
      eLpNorm (T f) p volume ≤ A * eLpNorm f p volume :=
  let ⟨A, hA⟩ := exists_eLpNorm_le_of_hasStandardKernel (V := V) (F := F) C δ ‖T‖ hp hp_top
  ⟨A, hA T K le_rfl h⟩

end HasStandardKernel

/-- The identity is a Calderón–Zygmund operator, with the kernel `0`. -/
theorem hasStandardKernel_id (C : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    HasStandardKernel (ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure V))) 0 C δ where
  exponent_pos := hδ
  norm_le x y _ := by
    simp only [Pi.zero_apply, norm_zero]
    positivity
  norm_sub_add_norm_sub_le x y y' _ := by
    simp only [Pi.zero_apply, sub_zero, norm_zero, add_zero]
    positivity
  ae_apply_eq_integral f s _ hf := by
    filter_upwards [hf] with x hx hxs
    simp [hx hxs]

/-! ### The kernel determines the operator up to a multiplication operator -/

namespace HasStandardKernel

variable {T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)} {K K' : V → V → ℂ}
  {C C' : ℝ≥0} {δ δ' : ℝ}

/-- Off a closed ball `B`, a Calderón–Zygmund operator maps `1_B v` to `(∫_B K x y dy) • v`. -/
private theorem ae_apply_indicatorConstLp_closedBall_eq [CompleteSpace F]
    (h : HasStandardKernel T K C δ) (y₀ : V) (ρ : ℝ) (v : F) :
    ∀ᵐ x, x ∉ closedBall y₀ ρ →
      T (indicatorConstLp 2 (measurableSet_closedBall (x := y₀) (ε := ρ))
        measure_closedBall_lt_top.ne v) x = (∫ y in closedBall y₀ ρ, K x y) • v := by
  have hf := indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure V))
    (hs := measurableSet_closedBall (x := y₀) (ε := ρ)) (hμs := measure_closedBall_lt_top.ne)
    (c := v)
  have hvan : ∀ᵐ x, x ∉ closedBall y₀ ρ →
      (indicatorConstLp 2 (measurableSet_closedBall (x := y₀) (ε := ρ))
        measure_closedBall_lt_top.ne v : Lp F 2 (volume : Measure V)) x = 0 := by
    filter_upwards [hf] with x hx hxt
    rw [hx, indicator_of_notMem hxt]
  filter_upwards [h.ae_apply_eq_integral _ _ (isCompact_closedBall y₀ ρ) hvan] with x hx hxt
  rw [hx hxt, ← integral_smul_const, ← integral_indicator measurableSet_closedBall]
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  rw [hy]
  by_cases hyt : y ∈ closedBall y₀ ρ <;> simp [hyt]

/-- **The kernel is determined by the operator off the diagonal.** If `T` has the standard kernels
`K` and `K'`, then `K x y = K' x y` for `x ≠ y`. On the diagonal the definition asks nothing of a
standard kernel, so nothing can be said there. -/
theorem unique [CompleteSpace F] [Nontrivial F] (h : HasStandardKernel T K C δ)
    (h' : HasStandardKernel T K' C' δ') {x₀ y₀ : V} (hxy : x₀ ≠ y₀) : K x₀ y₀ = K' x₀ y₀ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  set r := dist x₀ y₀ / 2 with hr_def
  have hr : 0 < r := half_pos (dist_pos.2 hxy)
  have hcont : ContinuousOn (fun q : V × V ↦ K q.1 q.2 - K' q.1 q.2) {q | q.1 ≠ q.2} :=
    h.continuousOn_uncurry.sub h'.continuousOn_uncurry
  have hsep : ∀ x ∈ ball x₀ r, ∀ y ∈ closedBall y₀ r, x ≠ y := by
    rintro x hx y hy rfl
    have := dist_triangle_left x₀ y₀ x
    rw [mem_ball] at hx
    rw [mem_closedBall] at hy
    linarith
  set ρ : ℕ → ℝ := fun k ↦ r / (k + 1)
  have hρ : ∀ k, 0 < ρ k := fun k ↦ div_pos hr (by positivity)
  have hρr : ∀ k, ρ k ≤ r := fun k ↦ div_le_self hr.le (le_add_of_nonneg_left k.cast_nonneg)
  have hρ₀ : Tendsto ρ atTop (𝓝 0) := by
    simpa [ρ, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 1)
  -- off each ball `closedBall y₀ ρₖ`, the integrals of `K x` and `K' x` over it agree
  have hint : ∀ᵐ x, ∀ k, x ∉ closedBall y₀ (ρ k) →
      ∫ y in closedBall y₀ (ρ k), K x y = ∫ y in closedBall y₀ (ρ k), K' x y := by
    refine ae_all_iff.2 fun k ↦ ?_
    filter_upwards [h.ae_apply_indicatorConstLp_closedBall_eq y₀ (ρ k) v,
      h'.ae_apply_indicatorConstLp_closedBall_eq y₀ (ρ k) v] with x h₁ h₂ hx
    exact smul_left_injective ℂ hv ((h₁ hx).symm.trans (h₂ hx))
  -- so `K x y₀ = K' x y₀` for almost every `x` near `x₀`
  have hae : (fun x ↦ K x y₀ - K' x y₀) =ᵐ[volume.restrict (ball x₀ r)] fun _ ↦ 0 := by
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hint] with x hx hxb
    have hK : ContinuousOn (fun y ↦ K x y) (closedBall y₀ r) :=
      h.continuousOn_uncurry.comp (Continuous.prodMk_right x).continuousOn
        fun y hy ↦ hsep x hxb y hy
    have hK' : ContinuousOn (fun y ↦ K' x y) (closedBall y₀ r) :=
      h'.continuousOn_uncurry.comp (Continuous.prodMk_right x).continuousOn
        fun y hy ↦ hsep x hxb y hy
    refine ContinuousOn.eq_zero_of_forall_setIntegral_closedBall_eq_zero (μ := volume)
      (g := fun y ↦ K x y - K' x y) (hK.sub hK') hρ hρr hρ₀ fun k ↦ ?_
    have hBr := closedBall_subset_closedBall (x := y₀) (hρr k)
    rw [integral_sub ((hK.mono hBr).integrableOn_compact (isCompact_closedBall _ _))
      ((hK'.mono hBr).integrableOn_compact (isCompact_closedBall _ _)),
      hx k fun hx' ↦ hsep x hxb x (hBr hx') rfl, sub_self]
  -- and by continuity at `x₀`
  have hg : ContinuousOn (fun x ↦ K x y₀ - K' x y₀) (ball x₀ r) :=
    hcont.comp (Continuous.prodMk_left y₀).continuousOn
      fun x hx ↦ hsep x hx y₀ (mem_closedBall_self hr.le)
  exact sub_eq_zero.1 (Measure.eqOn_open_of_ae_eq hae isOpen_ball hg continuousOn_const
    (mem_ball_self hr))

/-- **Adding a multiplication operator does not change the kernel.** If `T` has the standard kernel
`K`, then so has `T + M_a` for every `a ∈ L∞`, with the same constants: multiplication by `a` does
not move supports. The identity, with the kernel `0`, is the case `T = 0`, `a = 1`. -/
theorem add_multiplicationOperator (h : HasStandardKernel T K C δ)
    (a : Lp ℂ ∞ (volume : Measure V)) :
    HasStandardKernel (T + Lp.multiplicationOperator a) K C δ where
  exponent_pos := h.exponent_pos
  norm_le := h.norm_le
  norm_sub_add_norm_sub_le := h.norm_sub_add_norm_sub_le
  ae_apply_eq_integral f s hs hf := by
    filter_upwards [h.ae_apply_eq_integral f s hs hf, hf,
      Lp.coeFn_add (T f) (Lp.multiplicationOperator a f), Lp.multiplicationOperator_ae a f]
      with x hT hfx hadd hmul hxs
    rw [add_apply, hadd, Pi.add_apply, hmul, hfx hxs, smul_zero, add_zero,
      hT hxs]

/-- **Two Calderón–Zygmund operators with the same kernel differ by a multiplication operator** by
some `a ∈ L∞`, whose norm is then `‖T₁ - T₂‖` (`MeasureTheory.Lp.norm_multiplicationOperator`).
The kernel does not determine the operator, so the operator, not the kernel, is the primitive
datum. -/
theorem exists_sub_eq_multiplicationOperator
    {T₁ T₂ : Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V)}
    (h₁ : HasStandardKernel T₁ K C δ) (h₂ : HasStandardKernel T₂ K C' δ') :
    ∃ a : Lp ℂ ∞ (volume : Measure V), T₁ - T₂ = Lp.multiplicationOperator a :=
  Lp.exists_eq_multiplicationOperator_of_isCompact ENNReal.ofNat_ne_top fun f s hs hf ↦ by
    filter_upwards [h₁.ae_apply_eq_integral f s hs hf, h₂.ae_apply_eq_integral f s hs hf,
      Lp.coeFn_sub (T₁ f) (T₂ f)] with x h₁x h₂x hsub hxs
    rw [sub_apply, hsub, Pi.sub_apply, h₁x hxs, h₂x hxs, sub_self]

/-- **The Calderón–Zygmund operators with a given kernel.** If `T₁` is a Calderón–Zygmund operator
with the standard kernel `K`, then the bounded operators with the standard kernel `K`, for the same
constants, are exactly the operators `T₁ + M_a` with `a ∈ L∞`. -/
theorem hasStandardKernel_iff_exists_eq_add
    {T₁ T₂ : Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V)}
    (h₁ : HasStandardKernel T₁ K C δ) :
    HasStandardKernel T₂ K C δ ↔
      ∃ a : Lp ℂ ∞ (volume : Measure V), T₂ = T₁ + Lp.multiplicationOperator a := by
  refine ⟨fun h₂ ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ h₁.add_multiplicationOperator a⟩
  obtain ⟨a, ha⟩ := h₂.exists_sub_eq_multiplicationOperator h₁
  exact ⟨a, by rw [← ha, add_sub_cancel]⟩

end HasStandardKernel

end TauCeti
