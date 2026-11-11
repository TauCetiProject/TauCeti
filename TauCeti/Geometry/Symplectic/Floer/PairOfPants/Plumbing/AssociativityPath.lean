/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.MovingEnds

/-!
# A path of moving-end configurations between the two associativity compositions

The associativity of the pair-of-pants product compares `(a ⋆ b) ⋆ c` with `a ⋆ (b ⋆ c)`. Each
composition is a plumbed four-punctured sphere, and with the Hamiltonian of its neck switched off
its datum is a datum on a sphere with three moving input ends
(`TauCeti.Floer.plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation`). Write
`f = exp (-2πL) / 4` for the plumbing factor of the neck length `L`. Labelling the inputs
`a`, `b`, `c` in this order, the two configurations of centers and scales are

* for `(a ⋆ b) ⋆ c`: `a` at `0` with scale `f`, `b` at `f` with scale `-f`, `c` at `1` with
  scale `-1`;
* for `a ⋆ (b ⋆ c)`: `a` at `0` with scale `1`, `b` at `1` with scale `-f`, `c` at `1 - f` with
  scale `f`.

In the first, `a` and `b` sit on the small affine copy `w ↦ f w` of the pair of pants; in the
second, `b` and `c` sit on the copy `w ↦ 1 - f w`. This file joins the two by an explicit smooth
path of configurations `τ ↦ (associativityCenter f τ, associativityScale f τ)`, constant for
`τ ≤ 0` and for `τ ≥ 1`. On the eight intervals `[k/8, (k+1)/8]` it moves one center or one scale
along a segment, reparametrized by the smooth transition `β(8τ - k)`:

1. the scale of `c` shrinks from `-1` to `-f`;
2. `c` moves up from `1` to `1 + i`;
3. `b` moves along the real axis from `f` to `1`, passing under `c`;
4. `c` moves left to `1 - f + i`;
5. and 6. the scale of `c` turns from `-f` through `i f` to `f`, avoiding `0`;
7. `c` moves down to `1 - f`;
8. the scale of `a` grows from `f` to `1`.

For `0 ≤ f` and `3 f ≤ 1`, which holds for every neck length `L ≥ 0`, along the whole path the
discs `‖w - c_i‖ < ‖a_i‖ / 2` of the three input ends are pairwise disjoint
(`TauCeti.Floer.pairwise_add_le_norm_associativityCenter_sub`) and lie in the disc
`‖w‖ ≤ 2 exp (2π)` on which the output datum vanishes
(`TauCeti.Floer.norm_associativityCenter_add_le`), and for `0 < f` the scales do not vanish
(`TauCeti.Floer.associativityScale_ne_zero`). Therefore the data
`K_τ = puncturedSpherePerturbation (associativityCenter f τ) (associativityScale f τ) H Hout`
form a smooth one-parameter family
(`TauCeti.Floer.contMDiffAt_puncturedSpherePerturbation_associativity`), which is `H_i(t) dt` far
out on each input end and `Hout(t) dt` far out on the output end at every `τ`
(`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift`,
`TauCeti.Floer.puncturedSpherePerturbation_cylindricalEndLift_inf`), and whose integrated curvature
along any map into a manifold is bounded uniformly in `τ`
(`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_associativity_le`).
At `τ ≤ 0` it is the plumbed datum of `(a ⋆ b) ⋆ c` with the neck switched off
(`TauCeti.Floer.puncturedSpherePerturbation_associativity_of_nonpos`), and at `τ ≥ 1` that of
`a ⋆ (b ⋆ c)` (`TauCeti.Floer.puncturedSpherePerturbation_associativity_of_one_le`).

Concatenated with the families `λ ↦ K_λ` that switch the neck Hamiltonian back on at either end
(`TauCeti.Floer.plumbedPerturbation_update_smul`), this path joins the plumbed data of the two
compositions through Floer data with the same end Hamiltonians.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through the family of
  four-punctured spheres between its two degenerations.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured surfaces with cylindrical ends and consistent perturbation data over them.
-/

public noncomputable section

open Set Real Manifold Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*}

/-! ### The path of configurations -/

section Path

variable {f τ : ℝ}

/-- **The centers along the associativity path.** The input `a` stays at `0`; `b` moves from `f`
to `1` during the third eighth of the path; `c` moves from `1` up to `1 + i`, left to
`1 - f + i`, and down to `1 - f`, during the second, fourth and seventh eighths. -/
def associativityCenter (f τ : ℝ) : Fin 3 → ℂ :=
  ![0, ((f + (1 - f) * smoothTransition (8 * τ - 2) : ℝ) : ℂ),
    ((1 - f * smoothTransition (8 * τ - 3) : ℝ) : ℂ) +
      ((smoothTransition (8 * τ - 1) - smoothTransition (8 * τ - 6) : ℝ) : ℂ) * Complex.I]

/-- **The scales along the associativity path.** The scale of `b` is `-f` throughout; the scale
of `c` shrinks from `-1` to `-f` during the first eighth of the path and turns through `i f` to
`f` during the fifth and sixth; the scale of `a` grows from `f` to `1` during the last eighth. -/
def associativityScale (f τ : ℝ) : Fin 3 → ℂ :=
  ![((f + (1 - f) * smoothTransition (8 * τ - 7) : ℝ) : ℂ), ((-f : ℝ) : ℂ),
    ((-1 + (1 - f) * smoothTransition (8 * τ) + f * smoothTransition (8 * τ - 4) +
        f * smoothTransition (8 * τ - 5) : ℝ) : ℂ) +
      ((f * smoothTransition (8 * τ - 4) - f * smoothTransition (8 * τ - 5) : ℝ) : ℂ) * Complex.I]

@[simp] theorem associativityCenter_zero (f τ : ℝ) : associativityCenter f τ 0 = 0 :=
  (rfl)

theorem associativityCenter_one (f τ : ℝ) :
    associativityCenter f τ 1 = ((f + (1 - f) * smoothTransition (8 * τ - 2) : ℝ) : ℂ) :=
  (rfl)

theorem associativityCenter_two (f τ : ℝ) :
    associativityCenter f τ 2 = ((1 - f * smoothTransition (8 * τ - 3) : ℝ) : ℂ) +
      ((smoothTransition (8 * τ - 1) - smoothTransition (8 * τ - 6) : ℝ) : ℂ) * Complex.I :=
  (rfl)

theorem associativityScale_zero (f τ : ℝ) :
    associativityScale f τ 0 = ((f + (1 - f) * smoothTransition (8 * τ - 7) : ℝ) : ℂ) :=
  (rfl)

@[simp] theorem associativityScale_one (f τ : ℝ) : associativityScale f τ 1 = ((-f : ℝ) : ℂ) :=
  (rfl)

theorem associativityScale_two (f τ : ℝ) :
    associativityScale f τ 2 = ((-1 + (1 - f) * smoothTransition (8 * τ) +
        f * smoothTransition (8 * τ - 4) + f * smoothTransition (8 * τ - 5) : ℝ) : ℂ) +
      ((f * smoothTransition (8 * τ - 4) - f * smoothTransition (8 * τ - 5) : ℝ) : ℂ) *
        Complex.I :=
  (rfl)

/-- The transition of the `k`-th eighth vanishes before it starts. -/
private theorem stage_eq_zero {k : ℝ} (h : 8 * τ ≤ k) : smoothTransition (8 * τ - k) = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

/-- The transition of the `k`-th eighth is `1` after it ends. -/
private theorem stage_eq_one {k : ℝ} (h : k + 1 ≤ 8 * τ) : smoothTransition (8 * τ - k) = 1 :=
  smoothTransition.one_of_one_le (by linarith)

/-- The transition of the first eighth vanishes before it starts. -/
private theorem stage_zero_eq_zero (h : 8 * τ ≤ 0) : smoothTransition (8 * τ) = 0 :=
  smoothTransition.zero_of_nonpos h

/-- The transition of the first eighth is `1` after it ends. -/
private theorem stage_zero_eq_one (h : 1 ≤ 8 * τ) : smoothTransition (8 * τ) = 1 :=
  smoothTransition.one_of_one_le h

/-- **The path starts at the configuration of `(a ⋆ b) ⋆ c`.** -/
theorem associativityCenter_of_nonpos (hτ : τ ≤ 0) :
    associativityCenter f τ = ![0, (f : ℂ), 1] := by
  funext i
  fin_cases i
  · simp
  · simp [associativityCenter_one, stage_eq_zero (show 8 * τ ≤ 2 by linarith)]
  · simp [associativityCenter_two, stage_eq_zero (show 8 * τ ≤ 1 by linarith),
      stage_eq_zero (show 8 * τ ≤ 3 by linarith), stage_eq_zero (show 8 * τ ≤ 6 by linarith)]

/-- **The path starts at the configuration of `(a ⋆ b) ⋆ c`.** -/
theorem associativityScale_of_nonpos (hτ : τ ≤ 0) :
    associativityScale f τ = ![(f : ℂ), -(f : ℂ), -1] := by
  funext i
  fin_cases i
  · simp [associativityScale_zero, stage_eq_zero (show 8 * τ ≤ 7 by linarith)]
  · simp
  · simp [associativityScale_two, stage_zero_eq_zero (show 8 * τ ≤ 0 by linarith),
      stage_eq_zero (show 8 * τ ≤ 4 by linarith), stage_eq_zero (show 8 * τ ≤ 5 by linarith)]

/-- **The path ends at the configuration of `a ⋆ (b ⋆ c)`.** -/
theorem associativityCenter_of_one_le (hτ : 1 ≤ τ) :
    associativityCenter f τ = ![0, 1, 1 - (f : ℂ)] := by
  funext i
  fin_cases i
  · simp
  · simp [associativityCenter_one, stage_eq_one (show 2 + 1 ≤ 8 * τ by linarith)]
  · simp [associativityCenter_two, stage_eq_one (show 1 + 1 ≤ 8 * τ by linarith),
      stage_eq_one (show 3 + 1 ≤ 8 * τ by linarith), stage_eq_one (show 6 + 1 ≤ 8 * τ by linarith)]

/-- **The path ends at the configuration of `a ⋆ (b ⋆ c)`.** -/
theorem associativityScale_of_one_le (hτ : 1 ≤ τ) :
    associativityScale f τ = ![1, -(f : ℂ), (f : ℂ)] := by
  funext i
  fin_cases i
  · simp [associativityScale_zero, stage_eq_one (show 7 + 1 ≤ 8 * τ by linarith)]
  · simp
  · simp only [Fin.reduceFinMk, associativityScale_two,
      stage_zero_eq_one (show 1 ≤ 8 * τ by linarith), stage_eq_one (show 4 + 1 ≤ 8 * τ by linarith),
      stage_eq_one (show 5 + 1 ≤ 8 * τ by linarith), Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    push_cast
    ring

/-- **The path of centers is smooth.** -/
theorem contDiff_associativityCenter {n : ℕ∞} (f : ℝ) : ContDiff ℝ n (associativityCenter f) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simpa using contDiff_const
  · simp only [Fin.mk_one, associativityCenter_one, ← Complex.ofRealCLM_apply]
    fun_prop
  · simp only [Fin.reduceFinMk, associativityCenter_two, ← Complex.ofRealCLM_apply]
    fun_prop

/-- **The path of scales is smooth.** -/
theorem contDiff_associativityScale {n : ℕ∞} (f : ℝ) : ContDiff ℝ n (associativityScale f) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, associativityScale_zero, ← Complex.ofRealCLM_apply]
    fun_prop
  · simpa using contDiff_const
  · simp only [Fin.reduceFinMk, associativityScale_two, ← Complex.ofRealCLM_apply]
    fun_prop

/-! #### Norm estimates along the path -/

/-- After the first eighth, the scale of `c` has norm at most `f`. -/
private theorem norm_associativityScale_two_le (hf : 0 ≤ f) (hτ : 1 ≤ 8 * τ) :
    ‖associativityScale f τ 2‖ ≤ f := by
  rw [associativityScale_two, stage_zero_eq_one hτ]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
    zero_add]
  have h₄ := smoothTransition.nonneg (8 * τ - 4)
  have h₄' := smoothTransition.le_one (8 * τ - 4)
  have h₅ := smoothTransition.nonneg (8 * τ - 5)
  have h₅' := smoothTransition.le_one (8 * τ - 5)
  rcases le_or_gt (8 * τ) 5 with h | h
  · rw [stage_eq_zero h, abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith)]
    linarith
  · rw [stage_eq_one (by linarith), abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
    linarith

/-- The scale of `c` has norm at most `1`. -/
private theorem norm_associativityScale_two_le_one (hf : 0 ≤ f) (hf₁ : f ≤ 1) :
    ‖associativityScale f τ 2‖ ≤ 1 := by
  rcases le_or_gt 1 (8 * τ) with h | h
  · exact (norm_associativityScale_two_le hf h).trans hf₁
  rw [associativityScale_two, stage_eq_zero (show 8 * τ ≤ 4 by linarith),
    stage_eq_zero (show 8 * τ ≤ 5 by linarith)]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
    add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
    sub_self, abs_zero]
  have h₀ := smoothTransition.nonneg (8 * τ)
  have h₀' := smoothTransition.le_one (8 * τ)
  rw [abs_of_nonpos (by nlinarith)]
  nlinarith

/-- The norm of the scale of `a`. -/
private theorem norm_associativityScale_zero (hf : 0 ≤ f) (hf₁ : f ≤ 1) :
    ‖associativityScale f τ 0‖ = f + (1 - f) * smoothTransition (8 * τ - 7) := by
  rw [associativityScale_zero, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (add_nonneg hf (mul_nonneg (by linarith) (smoothTransition.nonneg _)))

/-- **The scales along the associativity path do not vanish.** -/
theorem associativityScale_ne_zero (hf : 0 < f) (i : Fin 3) : associativityScale f τ i ≠ 0 := by
  have h₀ := smoothTransition.nonneg (8 * τ)
  have h₀' := smoothTransition.le_one (8 * τ)
  have h₄ := smoothTransition.nonneg (8 * τ - 4)
  have h₅ := smoothTransition.nonneg (8 * τ - 5)
  have h₇ := smoothTransition.nonneg (8 * τ - 7)
  have h₇' := smoothTransition.le_one (8 * τ - 7)
  fin_cases i
  · simp only [Fin.zero_eta, associativityScale_zero, ne_eq, Complex.ofReal_eq_zero]
    rcases h₇.eq_or_lt with h | h
    · rw [← h]
      linarith
    · nlinarith [mul_nonneg hf.le (sub_nonneg.2 h₇')]
  · simp [hf.ne']
  · simp only [Fin.reduceFinMk, associativityScale_two]
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add, Complex.zero_re, Complex.zero_im] at hre him
    rcases le_or_gt (8 * τ) 4 with h | h
    · rw [stage_eq_zero h, stage_eq_zero (by linarith)] at hre
      rcases h₀.eq_or_lt with h0' | h0'
      · rw [← h0'] at hre
        linarith
      · nlinarith [mul_pos hf h0']
    rcases le_or_gt (8 * τ) 5 with h' | h'
    · have hpos := smoothTransition.pos_of_pos (show 0 < 8 * τ - 4 by linarith)
      rw [stage_eq_zero h'] at him
      nlinarith
    · have hpos := smoothTransition.pos_of_pos (show 0 < 8 * τ - 5 by linarith)
      rw [stage_zero_eq_one (by linarith), stage_eq_one (by linarith)] at hre
      nlinarith

/-- The discs of the inputs `a` and `b` are disjoint: `b` has reached `1` before `a` starts to
grow. -/
private theorem associativity_add_le_norm_sub_zero_one (hf : 0 ≤ f) (hf₁ : f ≤ 1) :
    ‖associativityScale f τ 0‖ / 2 + ‖associativityScale f τ 1‖ / 2 ≤
      ‖associativityCenter f τ 0 - associativityCenter f τ 1‖ := by
  have h₂ := smoothTransition.nonneg (8 * τ - 2)
  have h₂' := smoothTransition.le_one (8 * τ - 2)
  have h₇ := smoothTransition.le_one (8 * τ - 7)
  rw [associativityCenter_zero, associativityCenter_one, zero_sub, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, norm_associativityScale_zero hf hf₁, associativityScale_one,
    Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hf, abs_of_nonneg (by nlinarith)]
  rcases le_or_gt (8 * τ) 7 with h | h
  · rw [stage_eq_zero h]
    nlinarith
  · rw [stage_eq_one (k := 2) (by linarith)]
    nlinarith

/-- The discs of the inputs `a` and `c` are disjoint: the real part of `c` stays at least
`1 - f`. -/
private theorem associativity_add_le_norm_sub_zero_two (hf : 0 ≤ f) (hf₃ : 3 * f ≤ 1) :
    ‖associativityScale f τ 0‖ / 2 + ‖associativityScale f τ 2‖ / 2 ≤
      ‖associativityCenter f τ 0 - associativityCenter f τ 2‖ := by
  have hf₁ : f ≤ 1 := by linarith
  have h₃ := smoothTransition.le_one (8 * τ - 3)
  have h₇ := smoothTransition.le_one (8 * τ - 7)
  have hre : 1 - f ≤ ‖associativityCenter f τ 0 - associativityCenter f τ 2‖ := by
    rw [associativityCenter_zero, zero_sub, norm_neg, associativityCenter_two]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  rw [norm_associativityScale_zero hf hf₁]
  rcases le_or_gt (8 * τ) 7 with h | h
  · have := norm_associativityScale_two_le_one hf hf₁ (τ := τ)
    rw [stage_eq_zero h]
    linarith
  · have := norm_associativityScale_two_le hf (τ := τ) (by linarith)
    nlinarith

/-- The discs of the inputs `b` and `c` are disjoint: `c` passes above `b` while `b` moves. -/
private theorem associativity_add_le_norm_sub_one_two (hf : 0 ≤ f) (hf₃ : 3 * f ≤ 1) :
    ‖associativityScale f τ 1‖ / 2 + ‖associativityScale f τ 2‖ / 2 ≤
      ‖associativityCenter f τ 1 - associativityCenter f τ 2‖ := by
  have hf₁ : f ≤ 1 := by linarith
  have hsub : ∀ x y z : ℝ, (x : ℂ) - ((y : ℂ) + (z : ℂ) * Complex.I) =
      ((x - y : ℝ) : ℂ) + ((-z : ℝ) : ℂ) * Complex.I := fun x y z => by
    push_cast
    ring
  rw [associativityScale_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hf,
    associativityCenter_one, associativityCenter_two, hsub]
  rcases le_or_gt (8 * τ) 1 with h | h
  · have := norm_associativityScale_two_le_one hf hf₁ (τ := τ)
    rw [stage_eq_zero (show 8 * τ ≤ 2 by linarith), stage_eq_zero (show 8 * τ ≤ 3 by linarith)]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hc : ‖associativityScale f τ 2‖ ≤ f := norm_associativityScale_two_le hf h.le
  rcases le_or_gt (8 * τ) 2 with h' | h'
  · rw [stage_eq_zero h', stage_eq_zero (show 8 * τ ≤ 3 by linarith)]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith
  rcases le_or_gt (8 * τ) 6 with h'' | h''
  · rw [stage_eq_one (k := 1) (by linarith), stage_eq_zero h'']
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add]
    norm_num
    linarith
  · rw [stage_eq_one (k := 2) (by linarith), stage_eq_one (k := 3) (by linarith)]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The input discs stay disjoint along the associativity path.** For `0 ≤ f` and `3 f ≤ 1`,
the discs `‖w - c_i‖ < ‖a_i‖ / 2` of the three input ends are pairwise disjoint at every point of
the path. -/
theorem pairwise_add_le_norm_associativityCenter_sub (hf : 0 ≤ f) (hf₃ : 3 * f ≤ 1) :
    Pairwise fun i j => ‖associativityScale f τ i‖ / 2 + ‖associativityScale f τ j‖ / 2 ≤
      ‖associativityCenter f τ i - associativityCenter f τ j‖ := by
  have hab := associativity_add_le_norm_sub_zero_one (τ := τ) hf (by linarith)
  have hac := associativity_add_le_norm_sub_zero_two (τ := τ) hf hf₃
  have hbc := associativity_add_le_norm_sub_one_two (τ := τ) hf hf₃
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  · exact absurd rfl hij
  · exact hab
  · exact hac
  · rw [add_comm, norm_sub_rev]
    exact hab
  · exact absurd rfl hij
  · exact hbc
  · rw [add_comm, norm_sub_rev]
    exact hac
  · rw [add_comm, norm_sub_rev]
    exact hbc
  · exact absurd rfl hij

/-- **The input discs stay inside the disc where the output datum vanishes.** For `0 ≤ f ≤ 1`,
every input disc `‖w - c_i‖ < ‖a_i‖ / 2` along the associativity path lies in the disc
`‖w‖ ≤ 2 exp (2π)`. -/
theorem norm_associativityCenter_add_le (hf : 0 ≤ f) (hf₁ : f ≤ 1) (i : Fin 3) :
    ‖associativityCenter f τ i‖ + ‖associativityScale f τ i‖ / 2 ≤ 2 * Real.exp (2 * π) := by
  have hexp : 2 ≤ Real.exp (2 * π) := by
    have := Real.add_one_le_exp (2 * π)
    linarith [Real.two_le_pi]
  have h₁ := smoothTransition.nonneg (8 * τ - 1)
  have h₁' := smoothTransition.le_one (8 * τ - 1)
  have h₂ := smoothTransition.nonneg (8 * τ - 2)
  have h₂' := smoothTransition.le_one (8 * τ - 2)
  have h₃ := smoothTransition.nonneg (8 * τ - 3)
  have h₃' := smoothTransition.le_one (8 * τ - 3)
  have h₆ := smoothTransition.nonneg (8 * τ - 6)
  have h₆' := smoothTransition.le_one (8 * τ - 6)
  have h₇' := smoothTransition.le_one (8 * τ - 7)
  have hc : ‖associativityCenter f τ i‖ ≤ 2 := by
    fin_cases i
    · simp
    · rw [Fin.mk_one, associativityCenter_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by nlinarith)]
      nlinarith
    · simp only [Fin.reduceFinMk]
      rw [associativityCenter_two]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re,
        mul_zero, add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul,
        Complex.I_im, mul_one, zero_add]
      rw [abs_of_nonneg (by nlinarith)]
      have : |smoothTransition (8 * τ - 1) - smoothTransition (8 * τ - 6)| ≤ 1 :=
        abs_le.2 ⟨by linarith, by linarith⟩
      nlinarith
  have ha : ‖associativityScale f τ i‖ ≤ 1 := by
    fin_cases i
    · rw [Fin.zero_eta, norm_associativityScale_zero hf hf₁]
      nlinarith
    · simp [abs_of_nonneg hf, hf₁]
    · exact norm_associativityScale_two_le_one hf hf₁
  linarith

end Path

/-! ### The two compositions at the ends of the path -/

section Ends

variable {τ L : ℝ}

/-- **At its start the family is the composition `(a ⋆ b) ⋆ c`.** For `τ ≤ 0` and the plumbing
factor `f = exp (-2πL) / 4` of a neck length `L ≥ 0`, the datum of the sphere with the input ends
of the associativity path is the plumbed datum of the output end of a pair of pants with
Hamiltonians `Ha` glued into the input end `0` of one with Hamiltonians `Hb`, with the neck
Hamiltonian switched off. -/
theorem puncturedSpherePerturbation_associativity_of_nonpos (hτ : τ ≤ 0) (hL : 0 ≤ L)
    (Ha Hb : Puncture → ℝ → M → ℝ) :
    puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) ![Ha zero, Ha one, Hb one]
        (Hb inf) =
      plumbedPerturbation (update Ha inf 0) (update Hb zero 0) zero L := by
  have hf : zero.plumbingFactor L = ((Real.exp (-(2 * π * L)) / 4 : ℝ) : ℂ) := by
    rw [plumbingFactor_eq_mul_ofReal, endScale_zero]
    push_cast
    ring
  rw [plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation (r := one) (by simp)
    (by simp) (by simp) hL, associativityCenter_of_nonpos hτ, associativityScale_of_nonpos hτ,
    plumbingMap_apply, hf]
  norm_num

/-- **At its end the family is the composition `a ⋆ (b ⋆ c)`.** For `τ ≥ 1` and the plumbing
factor `f = exp (-2πL) / 4` of a neck length `L ≥ 0`, the datum of the sphere with the input ends
of the associativity path is the plumbed datum of the output end of a pair of pants with
Hamiltonians `Ha` glued into the input end `1` of one with Hamiltonians `Hb`, with the neck
Hamiltonian switched off. The inputs `a`, `b`, `c` carry the Hamiltonians `Hb 0`, `Ha 0`,
`Ha 1`. -/
theorem puncturedSpherePerturbation_associativity_of_one_le (hτ : 1 ≤ τ) (hL : 0 ≤ L)
    (Ha Hb : Puncture → ℝ → M → ℝ) :
    puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) ![Hb zero, Ha zero, Ha one]
        (Hb inf) =
      plumbedPerturbation (update Ha inf 0) (update Hb one 0) one L := by
  have hf : one.plumbingFactor L = -((Real.exp (-(2 * π * L)) / 4 : ℝ) : ℂ) := by
    rw [plumbingFactor_eq_mul_ofReal, endScale_one]
    push_cast
    ring
  rw [plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation (r := zero) (by simp)
    (by simp) (by simp) hL, associativityCenter_of_one_le hτ, associativityScale_of_one_le hτ,
    plumbingMap_apply, hf]
  -- The two data list the same three input ends in the orders `a, b, c` and `b, c, a`.
  funext w x
  simp only [puncturedSpherePerturbation_def, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, endCenter_one,
    endCenter_zero, endScale_zero, neg_neg, mul_one]
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, ← sub_eq_add_neg]
  abel

end Ends

/-! ### The family of data along the path -/

section Family

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Fin 3 → ℝ → M → ℝ} {Hout : ℝ → M → ℝ} {f τ : ℝ}

/-- **The data along the associativity path form a smooth family.** For period-one Hamiltonians
of class `C^n` and `0 < f`, the datum of the sphere with the input ends of the associativity
path is `C^n` jointly in the parameter `τ`, the domain point and the target point, at every domain
point other than the three centers. -/
theorem contMDiffAt_puncturedSpherePerturbation_associativity {n : ℕ∞}
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry Hout))
    (hf : 0 < f) {w : ℂ} (hw : ∀ i, w ≠ associativityCenter f τ i) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => puncturedSpherePerturbation (associativityCenter f p.1)
        (associativityScale f p.1) H Hout p.2.1 p.2.2) (τ, (w, x)) := by
  have hcfg : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, (Fin 3 → ℂ) × (Fin 3 → ℂ)) n
      (fun τ => (associativityCenter f τ, associativityScale f τ)) τ :=
    ((contDiff_associativityCenter f).prodMk (contDiff_associativityScale f)).contMDiff.contMDiffAt
  exact (contMDiffAt_puncturedSpherePerturbation hH hHs hHout hHouts
    (associativityScale_ne_zero hf) hw x).comp (τ, (w, x))
    ((hcfg.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)

end Family

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Fin 3 → ℝ → M → ℝ} {Hout : ℝ → M → ℝ} {f τ : ℝ}

/-- **The curvature along the associativity path is bounded uniformly.** Let the inputs `a`, `b`,
`c` carry period-one `C¹` Hamiltonians `H i` on a manifold `M` with a two-form `ω`, with
`|H i| ≤ B i`, and let the output carry a period-one `C¹` Hamiltonian `Hout` with `|Hout| ≤ Bout`.
For `0 < f` and `3 f ≤ 1`, at every point `τ` of the associativity path and for every map `u` into
`M`, the integral over the plane of `|R_K(z, u(z))|` for the datum `K` of the sphere with the input
ends of the path is at most `∑ i, B i + Bout`. -/
theorem lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_associativity_le
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hf : 0 < f)
    (hf₃ : 3 * f ≤ 1) {B : Fin 3 → ℝ} {Bout : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation (associativityCenter f τ) (associativityScale f τ) H
          Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation (associativityCenter f τ) (associativityScale f τ) H
          Hout (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ ≤
      ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout := by
  have hf₁ : f ≤ 1 := by linarith
  -- The supports of the input end data lie in the input discs.
  have hexp : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [Real.pi_pos])
  have hr (i : Fin 3) : ‖associativityScale f τ i‖ * Real.exp (-(2 * π)) / 2 ≤
      ‖associativityScale f τ i‖ / 2 := by
    have := norm_nonneg (associativityScale f τ i)
    nlinarith
  refine lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le ω hH hHs hHout hHouts
    (associativityScale_ne_zero hf) (fun i j hij => ?_) (fun i => ?_) hB hBout u
  · exact (add_le_add (hr i) (hr j)).trans
      (pairwise_add_le_norm_associativityCenter_sub hf.le hf₃ hij)
  · linarith [hr i, norm_associativityCenter_add_le hf.le hf₁ (τ := τ) i]

end TauCeti.SmoothTwoForm
