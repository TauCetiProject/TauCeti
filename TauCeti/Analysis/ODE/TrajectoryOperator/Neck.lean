/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.ODE.TrajectoryOperator.Scalar
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Kernel and cokernel cancellation on a neck

This file computes the scalar model of linear gluing for trajectory operators on the line, as
maps `W^{1,2}(ℝ, ℝ) → L²(ℝ, ℝ)`.

The two pieces are `D₁ = d/ds + tanh s` and `D₂ = d/ds - tanh s`. The solutions of `D₁ v = 0`
are the multiples of the hyperbolic secant `sech s = (cosh s)⁻¹`, which is square integrable, and
those of the formal adjoint equation `v' = tanh s · v` are the multiples of `cosh s`, which is
not. So `D₁` has kernel `ℝ · sech` and is onto, while `D₂` is injective with cokernel
`ℝ · sech`: their (kernel, cokernel) dimensions are `(1, 0)` and `(0, 1)`, and their indices are
`1` and `-1`.

Gluing the positive end of `D₁` to the negative end of `D₂` along a neck of length `2R` gives
`D_R = d/ds - a_R(s)` with `a_R(s) = 1 - tanh (s + R) + tanh (s - R)`
(`TauCeti.neckCoefficient`). Translated back to the two centres `∓R`, the coefficient `-a_R`
converges to the coefficients `tanh s` of `D₁` and `-tanh s` of `D₂`, exponentially fast in `R`
on every half-line. Both exterior ends of `D_R` have coefficient `a_R = 1`. Its positive
fundamental solution is `F_R(s) = exp s · cosh (s - R) / cosh (s + R)`
(`TauCeti.neckSolution`), with `F_R(s) / exp s → exp (∓ 2R)` as `s → ±∞`. Neither `F_R` nor
the adjoint solution `1 / F_R` is square integrable, so `D_R` is bijective: the glued kernel and
cokernel both vanish, and the one-dimensional kernel of `D₁` has cancelled against the
one-dimensional cokernel of `D₂`. The indices add, `0 = 1 + (-1)`, while the kernels and cokernels
separately do not.

The inverses are not uniformly bounded. The secant `sech (s + R)` centred at `-R` lies in the
kernel of `D₁` translated there, and `D_R` maps it to `-(1 + tanh (s - R)) sech (s + R)`, whose
`L²` norm is at most `2 exp (-2R)` times that of `sech`. So every inverse of `D_R` has norm at
least `exp (2R) / 2`.

## Main declarations

* `Real.memLp_inv_cosh`: the hyperbolic secant is square integrable.
* `TauCeti.WeakDerivStep.map_prevL_ker_trajectoryOperator_tanh`,
  `TauCeti.WeakDerivStep.range_trajectoryOperator_tanh`,
  `TauCeti.WeakDerivStep.index_trajectoryOperator_tanh`: `d/ds + tanh s` has kernel spanned by
  `sech`, is onto, and has index `1`.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_neg_tanh`,
  `TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_neg_tanh`,
  `TauCeti.WeakDerivStep.index_trajectoryOperator_neg_tanh`: `d/ds - tanh s` is injective, its
  cokernel is spanned by `sech`, and its index is `-1`.
* `TauCeti.neckCoefficient`, `TauCeti.neckSolution`: the glued coefficient `a_R` and its
  fundamental solution `F_R`, with `TauCeti.hasDerivAt_neckSolution` and the asymptotics
  `TauCeti.tendsto_neckSolution_div_exp_atTop`, `TauCeti.tendsto_neckSolution_div_exp_atBot`.
* `TauCeti.abs_neckCoefficient_sub_add_tanh_le`, `TauCeti.abs_neckCoefficient_add_sub_tanh_le`:
  convergence of the translated coefficients to those of the two pieces.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_neck`,
  `TauCeti.WeakDerivStep.range_trajectoryOperator_neck`: `D_R` is bijective.
* `TauCeti.WeakDerivStep.exists_norm_trajectoryOperator_neck_le`,
  `TauCeti.WeakDerivStep.exp_le_two_mul_norm_symm_neck`: a unit vector with image of size
  `O(exp (-2R))`, hence the lower bound `exp (2R) / 2` on the norm of the inverse.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Chapter 10 (gluing, and the linear gluing of Fredholm operators on long necks).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (kernels and cokernels of
  linearized trajectory operators as spaces of decaying solutions).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

/-! ### The hyperbolic secant -/

/-- The hyperbolic secant `(cosh x)⁻¹` is square integrable on the line: its square is at most
`(1 + x ^ 2)⁻¹`, because `cosh x ^ 2 = 1 + sinh x ^ 2` and `|x| ≤ |sinh x|`. -/
theorem Real.memLp_inv_cosh : MemLp (fun x ↦ (Real.cosh x)⁻¹) 2 volume := by
  have hc : Continuous fun x ↦ (Real.cosh x)⁻¹ :=
    Real.continuous_cosh.inv₀ fun x ↦ (Real.cosh_pos x).ne'
  refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2 <|
    integrable_inv_one_add_sq.mono' (hc.pow 2).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hx : |x| ≤ |Real.sinh x| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.2 (abs_nonneg x)
  have hsq : x ^ 2 ≤ Real.sinh x ^ 2 := sq_le_sq.2 hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow, Real.cosh_sq']
  exact inv_anti₀ (by positivity) (by linarith)

namespace TauCeti

/-- The translated secant `s ↦ (cosh (s + c))⁻¹` solves `v' = -tanh (s + c) · v`. -/
private theorem hasDerivAt_inv_cosh_add (c s : ℝ) :
    HasDerivAt (fun s ↦ (Real.cosh (s + c))⁻¹)
      (-(Real.tanh (s + c) * (Real.cosh (s + c))⁻¹)) s := by
  convert (((Real.hasDerivAt_cosh (s + c)).comp_add_const s c).inv
    (Real.cosh_pos (s + c)).ne') using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- A function bounded below in absolute value by a positive constant near `+∞` is not square
integrable. -/
private theorem not_memLp_two_of_eventually_atTop {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ᶠ s in atTop, c ≤ |f s|) : ¬MemLp f 2 volume := by
  intro h
  obtain ⟨T, hT⟩ := eventually_atTop.1 hf
  have hconst : IntegrableOn (fun _ : ℝ ↦ c ^ 2) (Ici T) := by
    refine ((memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h).integrableOn.mono'
      aestronglyMeasurable_const
      ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun s hs ↦ ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← sq_abs (f s)]
    exact pow_le_pow_left₀ hc.le (hT s hs) 2
  rw [integrableOn_const_iff] at hconst
  simp [Real.volume_Ici, hc.ne'] at hconst

/-- A function bounded below in absolute value by a positive constant near `-∞` is not square
integrable. -/
private theorem not_memLp_two_of_eventually_atBot {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ᶠ s in atBot, c ≤ |f s|) : ¬MemLp f 2 volume := fun h ↦
  not_memLp_two_of_eventually_atTop (f := fun s ↦ f (-s)) hc (tendsto_neg_atTop_atBot.eventually hf)
    (h.comp_measurePreserving (Measure.measurePreserving_neg volume))

/-- `cosh` is not square integrable. -/
private theorem not_memLp_cosh : ¬MemLp Real.cosh 2 volume :=
  not_memLp_two_of_eventually_atTop one_pos <| Eventually.of_forall fun s ↦
    (Real.one_le_cosh s).trans (le_abs_self _)

/-- The derivative `sech²` of `tanh` tends to zero along any filter along which `sech` does, in
particular at both ends. -/
private theorem tendsto_deriv_tanh {l : Filter ℝ} (hl : Tendsto (fun x ↦ (Real.cosh x)⁻¹) l (𝓝 0)) :
    Tendsto (deriv Real.tanh) l (𝓝 0) := by
  have h : deriv Real.tanh = fun x ↦ (Real.cosh x)⁻¹ ^ 2 :=
    funext fun x ↦ by rw [(Real.hasDerivAt_tanh x).deriv, inv_pow]
  simpa [h] using hl.pow 2

/-! ### The neck coefficient and its fundamental solution -/

/-- The coefficient `a_R(s) = 1 - tanh (s + R) + tanh (s - R)` of the operator
`D_R = d/ds - a_R(s)` obtained by gluing the positive end of `d/ds + tanh s` to the negative end
of `d/ds - tanh s` along a neck of length `2R`. It tends to `1` at both ends. -/
def neckCoefficient (R s : ℝ) : ℝ := 1 - Real.tanh (s + R) + Real.tanh (s - R)

/-- The defining formula of the neck coefficient. -/
theorem neckCoefficient_def (R s : ℝ) :
    neckCoefficient R s = 1 - Real.tanh (s + R) + Real.tanh (s - R) := (rfl)

private theorem neckCoefficient_eq (R : ℝ) :
    neckCoefficient R = fun s ↦ 1 - Real.tanh (s + R) + Real.tanh (s - R) :=
  funext (neckCoefficient_def R)

/-- The neck coefficient is smooth. -/
theorem contDiff_neckCoefficient (R : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (neckCoefficient R) := by
  unfold neckCoefficient
  fun_prop

/-- The derivative of the neck coefficient is `sech² (s - R) - sech² (s + R)`. -/
theorem hasDerivAt_neckCoefficient (R s : ℝ) :
    HasDerivAt (neckCoefficient R) ((Real.cosh (s - R) ^ 2)⁻¹ - (Real.cosh (s + R) ^ 2)⁻¹) s := by
  rw [neckCoefficient_eq]
  convert ((hasDerivAt_const s (1 : ℝ)).fun_sub
    ((Real.hasDerivAt_tanh (s + R)).comp_add_const s R)).fun_add
    ((Real.hasDerivAt_tanh (s - R)).comp_sub_const s R) using 1
  ring

/-- The neck coefficient tends to `1` at `+∞`: the right exterior end of the glued operator is that
of `d/ds - tanh s`. -/
theorem tendsto_neckCoefficient_atTop (R : ℝ) :
    Tendsto (neckCoefficient R) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (Real.tendsto_tanh_atTop.comp (tendsto_atTop_add_const_right _ R tendsto_id)) |>.add
    (Real.tendsto_tanh_atTop.comp (tendsto_atTop_add_const_right _ (-R) tendsto_id))
  rw [neckCoefficient_eq]
  simpa [Function.comp_def, sub_eq_add_neg] using h

/-- The neck coefficient tends to `1` at `-∞`: the left exterior end of the glued operator is that
of `d/ds + tanh s`. -/
theorem tendsto_neckCoefficient_atBot (R : ℝ) :
    Tendsto (neckCoefficient R) atBot (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (Real.tendsto_tanh_atBot.comp (tendsto_atBot_add_const_right _ R tendsto_id)) |>.add
    (Real.tendsto_tanh_atBot.comp (tendsto_atBot_add_const_right _ (-R) tendsto_id))
  rw [neckCoefficient_eq]
  simpa [Function.comp_def, sub_eq_add_neg] using h

/-- The derivative of the neck coefficient tends to zero along any filter along which the secant
does and which is invariant under translations. -/
private theorem tendsto_deriv_neckCoefficient (R : ℝ) {l : Filter ℝ}
    (hl : Tendsto (fun x ↦ (Real.cosh x)⁻¹) l (𝓝 0)) (hshift : ∀ c : ℝ, Tendsto (· + c) l l) :
    Tendsto (deriv (neckCoefficient R)) l (𝓝 0) := by
  have h : deriv (neckCoefficient R) =
      fun s ↦ (Real.cosh (s - R))⁻¹ ^ 2 - (Real.cosh (s + R))⁻¹ ^ 2 :=
    funext fun s ↦ by rw [(hasDerivAt_neckCoefficient R s).deriv, inv_pow, inv_pow]
  rw [h]
  simpa [Function.comp_def, sub_eq_add_neg] using
    ((hl.comp (hshift (-R))).pow 2).sub ((hl.comp (hshift R)).pow 2)

/-- **The coefficient near the left centre.** Translated by `-R`, the neck coefficient `a_R`
approximates `-tanh`, so that `d/ds - a_R` approximates `d/ds + tanh s` near `s = -R`; the error
is at most `2 exp (2 (s - 2R))`. -/
theorem abs_neckCoefficient_sub_add_tanh_le (R s : ℝ) :
    |neckCoefficient R (s - R) + Real.tanh s| ≤ 2 * Real.exp (2 * (s - 2 * R)) := by
  have h : neckCoefficient R (s - R) + Real.tanh s = 1 + Real.tanh (s - 2 * R) := by
    rw [neckCoefficient_def]
    ring_nf
  rw [h, abs_of_nonneg (by linarith [Real.neg_one_lt_tanh (s - 2 * R)])]
  exact Real.one_add_tanh_le _

/-- **The coefficient near the right centre.** Translated by `R`, the neck coefficient `a_R`
approximates `tanh`, so that `d/ds - a_R` approximates `d/ds - tanh s` near `s = R`; the error is
at most `2 exp (-2 (s + 2R))`. -/
theorem abs_neckCoefficient_add_sub_tanh_le (R s : ℝ) :
    |neckCoefficient R (s + R) - Real.tanh s| ≤ 2 * Real.exp (-(2 * (s + 2 * R))) := by
  have h : neckCoefficient R (s + R) - Real.tanh s = 1 + Real.tanh (-(s + 2 * R)) := by
    rw [neckCoefficient_def, Real.tanh_neg]
    ring_nf
  rw [h, abs_of_nonneg (by linarith [Real.neg_one_lt_tanh (-(s + 2 * R))]), ← mul_neg]
  exact Real.one_add_tanh_le _

/-- The positive fundamental solution `F_R(s) = exp s · cosh (s - R) / cosh (s + R)` of
`F' = a_R F`. -/
def neckSolution (R s : ℝ) : ℝ := Real.exp s * Real.cosh (s - R) / Real.cosh (s + R)

/-- The defining formula of the fundamental solution. -/
theorem neckSolution_def (R s : ℝ) :
    neckSolution R s = Real.exp s * Real.cosh (s - R) / Real.cosh (s + R) := (rfl)

private theorem neckSolution_eq (R : ℝ) :
    neckSolution R = fun s ↦ Real.exp s * Real.cosh (s - R) / Real.cosh (s + R) :=
  funext (neckSolution_def R)

/-- The fundamental solution is positive. -/
theorem neckSolution_pos (R s : ℝ) : 0 < neckSolution R s := by
  rw [neckSolution_def]
  have := Real.cosh_pos (s - R)
  have := Real.cosh_pos (s + R)
  positivity

/-- The fundamental solution solves `F_R' = a_R F_R`. -/
theorem hasDerivAt_neckSolution (R s : ℝ) :
    HasDerivAt (neckSolution R) (neckCoefficient R s * neckSolution R s) s := by
  have hc₁ := (Real.cosh_pos (s - R)).ne'
  have hc₂ := (Real.cosh_pos (s + R)).ne'
  rw [neckSolution_eq]
  convert ((Real.hasDerivAt_exp s).fun_mul
    ((Real.hasDerivAt_cosh (s - R)).comp_sub_const s R)).fun_div
    ((Real.hasDerivAt_cosh (s + R)).comp_add_const s R) hc₂ using 1
  rw [neckCoefficient_def, Real.tanh_eq_sinh_div_cosh,
    Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

/-- `F_R(s) / exp s = cosh (s - R) / cosh (s + R)` in terms of `tanh s`. -/
private theorem neckSolution_div_exp (R s : ℝ) :
    neckSolution R s / Real.exp s =
      (Real.cosh R - Real.tanh s * Real.sinh R) / (Real.cosh R + Real.tanh s * Real.sinh R) := by
  have hc := (Real.cosh_pos s).ne'
  rw [neckSolution_def, mul_div_assoc, mul_div_cancel_left₀ _ (Real.exp_pos s).ne',
    Real.cosh_sub, Real.cosh_add, Real.tanh_eq_sinh_div_cosh]
  conv_rhs => rw [← mul_div_mul_right _ _ hc]
  congr 1 <;> field_simp

/-- `F_R(s) / exp s → exp (-2R)` as `s → ∞`. -/
theorem tendsto_neckSolution_div_exp_atTop (R : ℝ) :
    Tendsto (fun s ↦ neckSolution R s / Real.exp s) atTop (𝓝 (Real.exp (-(2 * R)))) := by
  have hne : Real.cosh R + 1 * Real.sinh R ≠ 0 := by
    rw [one_mul, Real.cosh_add_sinh]
    exact (Real.exp_pos R).ne'
  have h := ((tendsto_const_nhds (x := Real.cosh R)).sub
    (Real.tendsto_tanh_atTop.mul_const (Real.sinh R))).div
    ((tendsto_const_nhds (x := Real.cosh R)).add
      (Real.tendsto_tanh_atTop.mul_const (Real.sinh R))) hne
  simp only [one_mul, Real.cosh_sub_sinh, Real.cosh_add_sinh, ← Real.exp_sub] at h
  convert h using 2
  · exact neckSolution_div_exp R _
  · congr 1
    ring

/-- `F_R(s) / exp s → exp (2R)` as `s → -∞`. -/
theorem tendsto_neckSolution_div_exp_atBot (R : ℝ) :
    Tendsto (fun s ↦ neckSolution R s / Real.exp s) atBot (𝓝 (Real.exp (2 * R))) := by
  have hne : Real.cosh R + -1 * Real.sinh R ≠ 0 := by
    rw [neg_one_mul, ← sub_eq_add_neg, Real.cosh_sub_sinh]
    exact (Real.exp_pos _).ne'
  have h := ((tendsto_const_nhds (x := Real.cosh R)).sub
    (Real.tendsto_tanh_atBot.mul_const (Real.sinh R))).div
    ((tendsto_const_nhds (x := Real.cosh R)).add
      (Real.tendsto_tanh_atBot.mul_const (Real.sinh R))) hne
  simp only [neg_one_mul, sub_neg_eq_add, ← sub_eq_add_neg, Real.cosh_add_sinh,
    Real.cosh_sub_sinh, ← Real.exp_sub] at h
  convert h using 2
  · exact neckSolution_div_exp R _
  · congr 1
    ring

/-- The fundamental solution `F_R` grows like `exp s` at `+∞`, so it is not square integrable. -/
theorem not_memLp_neckSolution (R : ℝ) : ¬MemLp (neckSolution R) 2 volume := by
  have hc : 0 < Real.exp (-(2 * R)) / 2 := by positivity
  refine not_memLp_two_of_eventually_atTop hc ?_
  filter_upwards [(tendsto_neckSolution_div_exp_atTop R).eventually
    (eventually_ge_nhds (half_lt_self (Real.exp_pos _))), eventually_ge_atTop 0] with s hs hs0
  rw [abs_of_pos (neckSolution_pos R s)]
  rw [le_div_iff₀ (Real.exp_pos s)] at hs
  nlinarith [Real.one_le_exp hs0]

/-- The adjoint solution `1 / F_R` grows like `exp (-s)` at `-∞`, so it is not square
integrable. -/
theorem not_memLp_inv_neckSolution (R : ℝ) :
    ¬MemLp (fun s ↦ (neckSolution R s)⁻¹) 2 volume := by
  have hc : 0 < (2 * Real.exp (2 * R))⁻¹ := by positivity
  refine not_memLp_two_of_eventually_atBot hc ?_
  filter_upwards [(tendsto_neckSolution_div_exp_atBot R).eventually
    (eventually_le_nhds (lt_two_mul_self (Real.exp_pos _))), eventually_le_atBot 0] with s hs hs0
  have hF := neckSolution_pos R s
  rw [abs_of_pos (inv_pos.2 hF), div_le_iff₀ (Real.exp_pos s)] at *
  rw [inv_le_inv₀ (by positivity) hF]
  nlinarith [Real.exp_le_one_iff.2 hs0, Real.exp_pos s, Real.exp_pos (2 * R)]

end TauCeti

/-! ### The two pieces and the glued operator -/

namespace TauCeti

/-- The secant `(cosh (s + R))⁻¹` centred at `-R` is mapped by `d/ds - a_R` to
`-(1 + tanh (s - R)) (cosh (s + R))⁻¹`, which is at most `2 exp (-2R)` times the secant centred
at `R`. -/
private theorem one_add_tanh_mul_inv_cosh_le (R s : ℝ) :
    (1 + Real.tanh (s - R)) * (Real.cosh (s + R))⁻¹ ≤
      2 * Real.exp (-(2 * R)) * (Real.cosh (s - R))⁻¹ := by
  have h₁ := Real.cosh_pos (s - R)
  have h₂ := Real.cosh_pos (s + R)
  have key : Real.exp (s - R) ≤ 2 * Real.exp (-(2 * R)) * Real.cosh (s + R) := by
    have h : Real.exp (-(2 * R)) * Real.exp (s + R) = Real.exp (s - R) := by
      rw [← Real.exp_add]
      ring_nf
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(s + R)), Real.exp_pos (-(2 * R))]
  calc (1 + Real.tanh (s - R)) * (Real.cosh (s + R))⁻¹
      = Real.exp (s - R) / (Real.cosh (s - R) * Real.cosh (s + R)) := by
        rw [Real.one_add_tanh]
        field_simp
    _ ≤ 2 * Real.exp (-(2 * R)) * Real.cosh (s + R) / (Real.cosh (s - R) * Real.cosh (s + R)) := by
        gcongr
    _ = 2 * Real.exp (-(2 * R)) * (Real.cosh (s - R))⁻¹ := by
        field_simp

/-- `cosh` solves `v' = tanh s · v`. -/
private theorem hasDerivAt_cosh_eq_tanh_mul (s : ℝ) :
    HasDerivAt Real.cosh (Real.tanh s * Real.cosh s) s := by
  convert Real.hasDerivAt_cosh s using 1
  rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ (Real.cosh_pos s).ne']

/-- The adjoint solution `1 / F_R` solves `v' = -a_R v`. -/
private theorem hasDerivAt_inv_neckSolution (R s : ℝ) :
    HasDerivAt (fun s ↦ (neckSolution R s)⁻¹) (-neckCoefficient R s * (neckSolution R s)⁻¹) s := by
  convert (hasDerivAt_neckSolution R s).inv (neckSolution_pos R s).ne' using 1
  field_simp [(neckSolution_pos R s).ne']

/-- If `f'` tends to zero, so does `(-f)'`. -/
private theorem tendsto_deriv_neg {f : ℝ → ℝ} {l : Filter ℝ} (h : Tendsto (deriv f) l (𝓝 0)) :
    Tendsto (deriv fun s ↦ -f s) l (𝓝 0) := by
  simpa [deriv.fun_neg] using h.neg

end TauCeti

namespace TauCeti.WeakDerivStep

/-- The `L²` class of the hyperbolic secant is nonzero. -/
private theorem sechLp_ne_zero :
    (Real.memLp_inv_cosh.restrict ((⊤ : Opens ℝ) : Set ℝ)).toLp (fun s ↦ (Real.cosh s)⁻¹) ≠ 0 := by
  intro h
  have h0 := (MemLp.coeFn_toLp (Real.memLp_inv_cosh.restrict ((⊤ : Opens ℝ) : Set ℝ))).symm.trans
    ((Lp.ext_iff.1 h).trans (Lp.coeFn_zero ℝ 2 _))
  obtain ⟨s, hs⟩ := h0.exists
  exact (inv_pos.2 (Real.cosh_pos s)).ne' hs

variable (AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))

/-- **The kernel of `d/ds + tanh s` is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ ℝ) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 := by
  simpa using finrank_ker_trajectoryOperator_smul_id Real.continuous_tanh
    (φ := fun s ↦ (Real.cosh s)⁻¹) (fun s ↦ by simpa using hasDerivAt_inv_cosh_add 0 s) (by simp)
    Real.memLp_inv_cosh AL hAL

/-- **The kernel of `d/ds + tanh s` is spanned by the hyperbolic secant.** Its values in
`L²(ℝ, ℝ)` are the multiples of `sech s = (cosh s)⁻¹`. -/
theorem map_prevL_ker_trajectoryOperator_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).ker.map
        (prevL (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
          : _ →ₗ[ℝ] _) =
      ℝ ∙ (Real.memLp_inv_cosh.restrict ((⊤ : Opens ℝ) : Set ℝ)).toLp
        fun s ↦ (Real.cosh s)⁻¹ := by
  set v := (Real.memLp_inv_cosh.restrict ((⊤ : Opens ℝ) : Set ℝ)).toLp fun s ↦ (Real.cosh s)⁻¹
  have hinj : Function.Injective
      (prevL (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :=
    fun u w h ↦ ext (by simpa using h)
  -- The secant is the value of an element of the kernel.
  obtain ⟨u, hu, huv⟩ := exists_trajectoryOperator_eq_zero_of_hasDerivAt hAL
    (v := fun s ↦ (Real.cosh s)⁻¹) (fun s ↦ by simpa using hasDerivAt_inv_cosh_add 0 s)
    Real.memLp_inv_cosh
  have hmem : v ∈ (trajectoryOperator (p := 2) AL).ker.map
      (prevL (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
        : _ →ₗ[ℝ] _) :=
    ⟨u, hu, by
      simp only [ContinuousLinearMap.coe_coe, prevL_apply]
      exact Lp.ext (huv.trans (MemLp.coeFn_toLp _).symm)⟩
  have hfin : Module.finrank ℝ ((trajectoryOperator (p := 2) AL).ker.map
      (prevL (ContinuousLinearMap.id ℝ
        (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))).toLinearMap) = 1 := by
    rw [← (Submodule.equivMapOfInjective (prevL (ContinuousLinearMap.id ℝ
      (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))).toLinearMap hinj _).finrank_eq,
      finrank_ker_trajectoryOperator_tanh AL hAL]
  have := Module.finite_of_finrank_eq_succ hfin
  exact (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
    (by rw [finrank_span_singleton sechLp_ne_zero, hfin])).symm

/-- **`d/ds + tanh s` is onto.** Its cokernel is the kernel of `d/ds - tanh s`, whose solutions
are the multiples of `cosh s`, none of them square integrable except `0`. -/
theorem range_trajectoryOperator_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).range = ⊤ :=
  range_trajectoryOperator_smul_id_eq_top Real.contDiff_tanh (by norm_num : (-1 : ℝ) ≠ 0)
    one_ne_zero Real.tendsto_tanh_atBot Real.tendsto_tanh_atTop
    (tendsto_deriv_tanh Real.tendsto_inv_cosh_atBot)
    (tendsto_deriv_tanh Real.tendsto_inv_cosh_atTop) hasDerivAt_cosh_eq_tanh_mul
    (fun s ↦ (Real.cosh_pos s).ne') not_memLp_cosh AL hAL

/-- **`d/ds + tanh s` has index `1`.** -/
theorem index_trajectoryOperator_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [ContinuousLinearMap.index_of_surjective _
      (LinearMap.range_eq_top.1 (range_trajectoryOperator_tanh AL hAL)),
    finrank_ker_trajectoryOperator_tanh AL hAL, Nat.cast_one]

/-- **`d/ds - tanh s` is injective.** The solutions of `v' = tanh s · v` are the multiples of
`cosh s`, which is not square integrable. -/
theorem ker_trajectoryOperator_neg_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ :=
  ker_trajectoryOperator_smul_id_eq_bot Real.continuous_tanh.neg (φ := Real.cosh)
    (fun s ↦ by simpa using hasDerivAt_cosh_eq_tanh_mul s) (fun s ↦ (Real.cosh_pos s).ne')
    not_memLp_cosh AL hAL

/-- **The cokernel of `d/ds - tanh s` is spanned by the hyperbolic secant.** The orthogonal
complement of its range in `L²(ℝ, ℝ)` is the line through `sech s = (cosh s)⁻¹`. -/
theorem orthogonal_range_trajectoryOperator_neg_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).rangeᗮ =
      ℝ ∙ (Real.memLp_inv_cosh.restrict ((⊤ : Opens ℝ) : Set ℝ)).toLp
        fun s ↦ (Real.cosh s)⁻¹ := by
  rw [orthogonal_range_trajectoryOperator_eq_map_ker (ae_isSymmetric_of_ae_eq_smul_id hAL)]
  exact map_prevL_ker_trajectoryOperator_tanh (-AL) (by simpa using neg_ae_eq_smul_id hAL)

/-- **The cokernel of `d/ds - tanh s` is one-dimensional.** -/
theorem finrank_coker_trajectoryOperator_neg_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    Module.finrank ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ⧸
      (trajectoryOperator (p := 2) AL).range) = 1 := by
  have hclosed := (isFredholm_trajectoryOperator_smul_id (a := fun s ↦ -Real.tanh s)
    Real.contDiff_tanh.neg one_ne_zero (by norm_num : (-1 : ℝ) ≠ 0)
    (by simpa using Real.tendsto_tanh_atBot.neg) (Real.tendsto_tanh_atTop.neg)
    (tendsto_deriv_neg (tendsto_deriv_tanh Real.tendsto_inv_cosh_atBot))
    (tendsto_deriv_neg (tendsto_deriv_tanh Real.tendsto_inv_cosh_atTop)) AL hAL).isClosed_range
  have := hclosed.completeSpace_coe
  rw [(trajectoryOperator (p := 2) AL).range.quotientEquivOrthogonal.toLinearEquiv.finrank_eq,
    orthogonal_range_trajectoryOperator_neg_tanh AL hAL, finrank_span_singleton sechLp_ne_zero]

/-- **`d/ds - tanh s` has index `-1`.** -/
theorem index_trajectoryOperator_neg_tanh
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).index = -1 := by
  rw [ContinuousLinearMap.index_of_injective _
      (LinearMap.ker_eq_bot.1 (ker_trajectoryOperator_neg_tanh AL hAL)),
    finrank_coker_trajectoryOperator_neg_tanh AL hAL, Nat.cast_one]

variable (R : ℝ)

/-- **The glued operator is injective.** Every solution of `v' = a_R v` is a multiple of the
fundamental solution `F_R`, which is not square integrable. -/
theorem ker_trajectoryOperator_neck
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ :=
  ker_trajectoryOperator_smul_id_eq_bot (contDiff_neckCoefficient R (n := 1)).continuous.neg
    (φ := neckSolution R) (fun s ↦ by simpa using hasDerivAt_neckSolution R s)
    (fun s ↦ (neckSolution_pos R s).ne') (not_memLp_neckSolution R) AL hAL

/-- **The glued operator is onto.** Its cokernel is spanned by the square-integrable solutions of
the adjoint equation `v' = -a_R v`, which are the multiples of `1 / F_R`; only `0` is square
integrable. -/
theorem range_trajectoryOperator_neck
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ) :
    (trajectoryOperator (p := 2) AL).range = ⊤ := by
  have hshift : ∀ c : ℝ, Tendsto (· + c) atTop atTop :=
    fun c ↦ tendsto_atTop_add_const_right _ c tendsto_id
  have hshift' : ∀ c : ℝ, Tendsto (· + c) atBot atBot :=
    fun c ↦ tendsto_atBot_add_const_right _ c tendsto_id
  exact range_trajectoryOperator_smul_id_eq_top (contDiff_neckCoefficient R).neg
    (by norm_num : (-1 : ℝ) ≠ 0) (by norm_num : (-1 : ℝ) ≠ 0)
    (tendsto_neckCoefficient_atBot R).neg (tendsto_neckCoefficient_atTop R).neg
    (tendsto_deriv_neg (tendsto_deriv_neckCoefficient R Real.tendsto_inv_cosh_atBot hshift'))
    (tendsto_deriv_neg (tendsto_deriv_neckCoefficient R Real.tendsto_inv_cosh_atTop hshift))
    (hasDerivAt_inv_neckSolution R) (fun s ↦ (inv_pos.2 (neckSolution_pos R s)).ne')
    (not_memLp_inv_neckSolution R) AL hAL

/-- **An almost-kernel of the glued operator.** The secant centred at `-R` is a nonzero element `u`
of `W^{1,2}(ℝ, ℝ)` with `‖D_R u‖ ≤ 2 exp (-2R) ‖u‖`. -/
theorem exists_norm_trajectoryOperator_neck_le
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ) :
    ∃ u, u ≠ 0 ∧ ‖trajectoryOperator (p := 2) AL u‖ ≤ 2 * Real.exp (-(2 * R)) * ‖u‖ := by
  set v : ℝ → ℝ := fun s ↦ (Real.cosh (s + R))⁻¹ with hv_def
  have hv (s : ℝ) : HasDerivAt v (-(Real.tanh (s + R) * v s)) s := hasDerivAt_inv_cosh_add R s
  have hv2 : MemLp v 2 volume :=
    Real.memLp_inv_cosh.comp_measurePreserving (measurePreserving_add_right volume R)
  have hvc : ContDiff ℝ 1 v :=
    (Real.contDiff_cosh.comp (contDiff_id.add contDiff_const)).inv fun s ↦ (Real.cosh_pos _).ne'
  -- `v` lies in the kernel of the translated piece `d/ds + tanh (s + R)`.
  have hB : MemLp (fun s ↦ Real.tanh (s + R) • ContinuousLinearMap.id ℝ ℝ) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
    refine memLp_top_of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun s ↦ ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_)
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, norm_smul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_tanh_lt_one _).le
  obtain ⟨u, -, hu⟩ := exists_trajectoryOperator_eq_zero_of_hasDerivAt hB.coeFn_toLp (v := v)
    (fun s ↦ by simpa using hv s) hv2
  refine ⟨u, fun h ↦ ?_, ?_⟩
  · -- `u` is not zero, since its value `v` is positive.
    rw [h, prev_zero] at hu
    obtain ⟨s, hs⟩ := ((Lp.coeFn_zero ℝ 2 _).symm.trans hu).exists
    exact (inv_pos.2 (Real.cosh_pos (s + R))).ne' hs.symm
  -- Pointwise, `D_R v` is at most `2 exp (-2R)` times the secant centred at `R`.
  have hpt (s : ℝ) : ‖deriv v s + ((-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ) (v s)‖ ^ 2
      ≤ (2 * Real.exp (-(2 * R))) ^ 2 * (Real.cosh (s - R))⁻¹ ^ 2 := by
    have heq : deriv v s + ((-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ) (v s) =
        -((1 + Real.tanh (s - R)) * (Real.cosh (s + R))⁻¹) := by
      rw [(hv s).deriv, neckCoefficient_def]
      simp only [hv_def, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul]
      ring
    have hnn : 0 ≤ (1 + Real.tanh (s - R)) * (Real.cosh (s + R))⁻¹ :=
      mul_nonneg (by linarith [Real.neg_one_lt_tanh (s - R)]) (inv_pos.2 (Real.cosh_pos _)).le
    rw [heq, norm_neg, Real.norm_eq_abs, abs_of_nonneg hnn, ← mul_pow]
    exact pow_le_pow_left₀ hnn (one_add_tanh_mul_inv_cosh_le R s) 2
  have hsech : Integrable (fun s ↦ (Real.cosh s)⁻¹ ^ 2) volume :=
    (memLp_two_iff_integrable_sq Real.memLp_inv_cosh.aestronglyMeasurable).1 Real.memLp_inv_cosh
  have hint : ‖trajectoryOperator (p := 2) AL u‖ ^ 2 ≤
      (2 * Real.exp (-(2 * R))) ^ 2 * ‖prev _ u‖ ^ 2 := by
    rw [norm_trajectoryOperator_sq_eq_integral hvc hu AL hAL, norm_prev_sq_eq_integral hu]
    calc ∫ s, ‖deriv v s + ((-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ) (v s)‖ ^ 2
        ≤ ∫ s, (2 * Real.exp (-(2 * R))) ^ 2 * (Real.cosh (s - R))⁻¹ ^ 2 :=
          integral_mono_of_nonneg (ae_of_all _ fun s ↦ by positivity)
            ((hsech.comp_sub_right R).const_mul _) (ae_of_all _ hpt)
      _ = (2 * Real.exp (-(2 * R))) ^ 2 * ∫ s, ‖v s‖ ^ 2 := by
          rw [integral_const_mul, integral_sub_right_eq_self (fun s ↦ (Real.cosh s)⁻¹ ^ 2) R]
          simp only [hv_def, Real.norm_eq_abs, sq_abs]
          rw [integral_add_right_eq_self (fun s ↦ (Real.cosh s)⁻¹ ^ 2) R]
  have hle : ‖trajectoryOperator (p := 2) AL u‖ ^ 2 ≤ (2 * Real.exp (-(2 * R)) * ‖u‖) ^ 2 :=
    hint.trans (by rw [mul_pow (2 * Real.exp _)]; gcongr; exact norm_prev_le _ u)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-- **The inverses of the glued operators are not uniformly bounded.** The glued operator is
bijective (`TauCeti.WeakDerivStep.ker_trajectoryOperator_neck`,
`TauCeti.WeakDerivStep.range_trajectoryOperator_neck`), so it is a continuous linear equivalence,
for instance `ContinuousLinearEquiv.ofBijective`; the inverse of any such equivalence has norm at
least `exp (2R) / 2`. -/
theorem exp_le_two_mul_norm_symm_neck
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-neckCoefficient R s) • ContinuousLinearMap.id ℝ ℝ)
    (e : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ≃L[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (he : e.toContinuousLinearMap = trajectoryOperator (p := 2) AL) :
    Real.exp (2 * R) ≤ 2 * ‖e.symm.toContinuousLinearMap‖ := by
  obtain ⟨u, hu0, hu⟩ := exists_norm_trajectoryOperator_neck_le AL R hAL
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set N := ‖e.symm.toContinuousLinearMap‖
  have h1 : ‖u‖ ≤ N * (2 * Real.exp (-(2 * R)) * ‖u‖) :=
    calc ‖u‖ = ‖e.symm.toContinuousLinearMap (e u)‖ := by simp
      _ ≤ N * ‖e u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * (2 * Real.exp (-(2 * R)) * ‖u‖) := by
          gcongr
          rw [← ContinuousLinearEquiv.coe_apply, he]
          exact hu
  have hexp : Real.exp (2 * R) * Real.exp (-(2 * R)) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 ≤ N * (2 * Real.exp (-(2 * R))) :=
    le_of_mul_le_mul_right (by linarith [h1] : 1 * ‖u‖ ≤ N * (2 * Real.exp (-(2 * R))) * ‖u‖)
      hu'
  calc Real.exp (2 * R) = Real.exp (2 * R) * 1 := (mul_one _).symm
    _ ≤ Real.exp (2 * R) * (N * (2 * Real.exp (-(2 * R)))) := by gcongr
    _ = 2 * N := by linear_combination (2 * N) * hexp

end TauCeti.WeakDerivStep
