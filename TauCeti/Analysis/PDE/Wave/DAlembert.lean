/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.InnerProductSpace.Parallelogram

/-!
# The one-dimensional wave equation and d'Alembert's formula

This file solves the Cauchy problem for the one-dimensional wave equation

`∂ₜ²u = ∂ₓ²u`, `u(0, x) = f(x)`, `∂ₜu(0, x) = g(x)`

by **d'Alembert's formula**

`u(t, x) = (f(x + t) + f(x - t)) / 2 + (1 / 2) ∫_{x - t}^{x + t} g`,

for functions with values in a real Banach space. As in the other classical PDE files, a function
`u : ℝ → ℝ → F` takes the time first, so `u t` is the spatial profile at time `t`; the time
derivative is `deriv (fun s ↦ u s x) t` and the spatial derivatives are `deriv (u t) x` and
`deriv (deriv (u t)) x`. Classical solutions are `C²` on the whole space-time plane, so negative
times are allowed and the formula is used with an oriented interval integral.

* **Existence.** For `f` of class `C²` and `g` of class `C¹`, `dAlembert f g` is `C²` and solves
  the Cauchy problem. It is the superposition of the left-moving wave `A(x + t)` and the
  right-moving wave `B(x - t)` with `A = (f + G) / 2`, `B = (f - G) / 2`, where `G` is a primitive
  of `g`; every such superposition of `C²` waves solves the equation.
* **Representation and uniqueness.** Every `C²` solution on the plane is given by d'Alembert's
  formula in terms of its own Cauchy data. No growth condition at infinity is needed: the
  operator factors as `(∂ₜ - ∂ₓ)(∂ₜ + ∂ₓ)`, so `∂ₜu + ∂ₓu` is constant along the lines
  `x + t = const`, and integrating along the lines `x - t = const` recovers `u`. In particular
  the value `u(t, x)` depends only on the data on `[x - |t|, x + |t|]` (finite speed of
  propagation, with speed one).
* **Bounds.** `‖u(t, x)‖ ≤ M + |t| N` when `‖f‖ ≤ M` and `‖g‖ ≤ N`, and the energy
  `∫ ‖∂ₜu(t, ·)‖² + ‖∂ₓu(t, ·)‖²` of a solution with values in a real Hilbert space is
  independent of `t`, finite or not.
* **No dispersion.** For initial data `(f, 0)` vanishing outside `(-R, R)`, from time `R` on the
  solution consists of two copies of `f / 2` travelling in opposite directions, so its supremum
  norm does not decay. This is the one-dimensional case of the wave equation, which has no
  positive dispersive decay exponent.

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `hasDerivAt_comp_add_add_comp_sub`: the time and space derivatives of `A(x + t) + B(x - t)`.
* `deriv_deriv_comp_add_add_comp_sub`: `A(x + t) + B(x - t)` solves the wave equation.
* `dAlembert`: d'Alembert's formula.
* `contDiff_dAlembert`, `deriv_deriv_dAlembert`, `dAlembert_time_zero`, `deriv_dAlembert_zero`:
  d'Alembert's formula gives a classical solution with the prescribed Cauchy data.
* `eq_dAlembert_of_deriv_deriv_eq`: every classical solution is given by d'Alembert's formula.
* `eq_of_deriv_deriv_eq_of_eqOn_initial`, `eq_of_deriv_deriv_eq_of_eq_initial`: the domain of
  dependence and uniqueness for the Cauchy problem.
* `norm_dAlembert_le`: the bound `‖u(t, x)‖ ≤ M + |t| N`.
* `lintegral_enorm_sub_sq_add_enorm_add_sq`: the energy of two travelling waves is independent of
  time.
* `lintegral_enorm_deriv_sq_add_enorm_deriv_sq_eq`: conservation of energy.
* `dAlembert_zero_right_apply_add_of_abs_lt`: the absence of dispersive decay.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.4.1 (d'Alembert's formula)
  and Section 2.4.3 (energy methods).
* F. John, *Partial Differential Equations*, 4th ed., Chapter 2, Section 1.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Set Function MeasureTheory intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Travelling waves -/

section TravellingWave

variable {A B A' B' : ℝ → F}

/-- The time and space derivatives of the superposition `A(x + t) + B(x - t)` of a left- and a
right-moving wave: `∂ₜu = A'(x + t) - B'(x - t)` and `∂ₓu = A'(x + t) + B'(x - t)`. -/
theorem hasDerivAt_comp_add_add_comp_sub (hA : ∀ z, HasDerivAt A (A' z) z)
    (hB : ∀ z, HasDerivAt B (B' z) z) (t x : ℝ) :
    HasDerivAt (fun s ↦ A (x + s) + B (x - s)) (A' (x + t) - B' (x - t)) t ∧
      HasDerivAt (fun y ↦ A (y + t) + B (y - t)) (A' (x + t) + B' (x - t)) x := by
  refine ⟨?_, ((hA (x + t)).comp_add_const x t).fun_add ((hB (x - t)).comp_sub_const x t)⟩
  have h := ((hA (x + t)).comp_const_add x t).fun_add ((hB (x - t)).comp_const_sub x t)
  rwa [← sub_eq_add_neg] at h

/-- **Travelling waves solve the wave equation.** If `A` and `B` are `C²`, then
`u(t, x) = A(x + t) + B(x - t)` satisfies `∂ₜ²u = ∂ₓ²u` everywhere. -/
theorem deriv_deriv_comp_add_add_comp_sub (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B)
    (t x : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ A (x + r) + B (x - r)) s) t =
      deriv (deriv fun y ↦ A (y + t) + B (y - t)) x := by
  have hA2 (z : ℝ) := (hA.differentiable_deriv_two z).hasDerivAt
  have hB2 (z : ℝ) := (hB.differentiable_deriv_two z).hasDerivAt
  have h1 := hasDerivAt_comp_add_add_comp_sub (fun z ↦ (hA.differentiable two_ne_zero z).hasDerivAt)
    (fun z ↦ (hB.differentiable two_ne_zero z).hasDerivAt)
  have h2 := hasDerivAt_comp_add_add_comp_sub hA2 fun z ↦ (hB2 z).neg
  have ht : deriv (fun r ↦ A (x + r) + B (x - r)) =
      fun s ↦ deriv A (x + s) + (-deriv B) (x - s) := by
    ext s
    simpa [sub_eq_add_neg] using (h1 s x).1.deriv
  have hx : deriv (fun y ↦ A (y + t) + B (y - t)) =
      fun y ↦ deriv A (y + t) + deriv B (y - t) :=
    funext fun y ↦ (h1 t y).2.deriv
  rw [ht, hx, (h2 t x).1.deriv, (hasDerivAt_comp_add_add_comp_sub hA2 hB2 t x).2.deriv]
  simp [sub_eq_add_neg]

end TravellingWave

/-! ### d'Alembert's formula -/

section DAlembert

variable {f g : ℝ → F} {t x : ℝ}

/-- **d'Alembert's formula** for the one-dimensional wave equation with initial displacement `f`
and initial velocity `g`:
`dAlembert f g t x = (f(x + t) + f(x - t)) / 2 + (1 / 2) ∫_{x - t}^{x + t} g`. -/
def dAlembert (f g : ℝ → F) (t x : ℝ) : F :=
  (2 : ℝ)⁻¹ • (f (x + t) + f (x - t)) + (2 : ℝ)⁻¹ • ∫ y in x - t..x + t, g y

theorem dAlembert_def (f g : ℝ → F) (t x : ℝ) :
    dAlembert f g t x =
      (2 : ℝ)⁻¹ • (f (x + t) + f (x - t)) + (2 : ℝ)⁻¹ • ∫ y in x - t..x + t, g y :=
  (rfl)

/-- At time zero, d'Alembert's formula returns the initial displacement. -/
@[simp]
theorem dAlembert_time_zero (f g : ℝ → F) (x : ℝ) : dAlembert f g 0 x = f x := by
  simp only [dAlembert_def, add_zero, sub_zero, integral_same, smul_zero]
  module

/-- With zero initial velocity, d'Alembert's formula is the average of the two translates of the
initial displacement. -/
@[simp]
theorem dAlembert_zero_right (f : ℝ → F) (t x : ℝ) :
    dAlembert f 0 t x = (2 : ℝ)⁻¹ • (f (x + t) + f (x - t)) := by
  simp [dAlembert_def]

/-- **The domain of dependence.** d'Alembert's formula at `(t, x)` only depends on the initial
data on the interval between `x - t` and `x + t`. -/
theorem dAlembert_congr {f' g' : ℝ → F} (hf : EqOn f f' (uIcc (x - t) (x + t)))
    (hg : EqOn g g' (uIcc (x - t) (x + t))) : dAlembert f g t x = dAlembert f' g' t x := by
  rw [dAlembert_def, dAlembert_def, hf right_mem_uIcc, hf left_mem_uIcc,
    integral_congr hg]

/-- d'Alembert's formula as the superposition of the left-moving wave `(f + G) / 2` and the
right-moving wave `(f - G) / 2`, where `G(z) = ∫_0^z g` is a primitive of the initial velocity. -/
theorem dAlembert_eq_add (hg : Continuous g) (t x : ℝ) :
    dAlembert f g t x = (2 : ℝ)⁻¹ • (f (x + t) + ∫ y in 0..x + t, g y) +
      (2 : ℝ)⁻¹ • (f (x - t) - ∫ y in 0..x - t, g y) := by
  rw [dAlembert_def, ← integral_interval_sub_left (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  module

/-- The time and space derivatives of d'Alembert's formula, from its travelling-wave form. -/
private theorem hasDerivAt_dAlembert [CompleteSpace F] (hf : Differentiable ℝ f)
    (hg : Continuous g) (t x : ℝ) :
    HasDerivAt (fun s ↦ dAlembert f g s x)
      ((2 : ℝ)⁻¹ • (deriv f (x + t) + g (x + t)) - (2 : ℝ)⁻¹ • (deriv f (x - t) - g (x - t)))
      t ∧
    HasDerivAt (dAlembert f g t)
      ((2 : ℝ)⁻¹ • (deriv f (x + t) + g (x + t)) + (2 : ℝ)⁻¹ • (deriv f (x - t) - g (x - t)))
      x := by
  simp only [funext₂ (dAlembert_eq_add (f := f) hg)]
  exact hasDerivAt_comp_add_add_comp_sub
    (fun z ↦ ((hf z).hasDerivAt.add (hg.integral_hasStrictDerivAt 0 z).hasDerivAt).const_smul _)
    (fun z ↦ ((hf z).hasDerivAt.sub (hg.integral_hasStrictDerivAt 0 z).hasDerivAt).const_smul _)
    t x

/-- The time derivative of d'Alembert's formula:
`∂ₜu(t, x) = (f'(x + t) + g(x + t)) / 2 - (f'(x - t) - g(x - t)) / 2`. -/
theorem hasDerivAt_dAlembert_time [CompleteSpace F] (hf : Differentiable ℝ f) (hg : Continuous g)
    (t x : ℝ) :
    HasDerivAt (fun s ↦ dAlembert f g s x)
      ((2 : ℝ)⁻¹ • (deriv f (x + t) + g (x + t)) - (2 : ℝ)⁻¹ • (deriv f (x - t) - g (x - t)))
      t :=
  (hasDerivAt_dAlembert hf hg t x).1

/-- The space derivative of d'Alembert's formula:
`∂ₓu(t, x) = (f'(x + t) + g(x + t)) / 2 + (f'(x - t) - g(x - t)) / 2`. -/
theorem hasDerivAt_dAlembert_space [CompleteSpace F] (hf : Differentiable ℝ f) (hg : Continuous g)
    (t x : ℝ) :
    HasDerivAt (dAlembert f g t)
      ((2 : ℝ)⁻¹ • (deriv f (x + t) + g (x + t)) + (2 : ℝ)⁻¹ • (deriv f (x - t) - g (x - t)))
      x :=
  (hasDerivAt_dAlembert hf hg t x).2

/-- At time zero, the time derivative of d'Alembert's formula is the initial velocity. -/
@[simp]
theorem deriv_dAlembert_zero [CompleteSpace F] (hf : Differentiable ℝ f) (hg : Continuous g)
    (x : ℝ) :
    deriv (fun t ↦ dAlembert f g t x) 0 = g x := by
  rw [(hasDerivAt_dAlembert_time hf hg 0 x).deriv, add_zero, sub_zero]
  module

/-- For `f` of class `C²` and `g` of class `C¹`, d'Alembert's formula is the superposition of two
travelling waves of class `C²`. -/
private theorem exists_contDiff_dAlembert_eq_add [CompleteSpace F] (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 1 g) :
    ∃ A B : ℝ → F, ContDiff ℝ 2 A ∧ ContDiff ℝ 2 B ∧
      ∀ t x, dAlembert f g t x = A (x + t) + B (x - t) := by
  have hG : ContDiff ℝ 2 fun z ↦ ∫ y in 0..z, g y := by
    refine (contDiff_succ_iff_deriv (n := 1)).2
      ⟨fun z ↦ (hg.continuous.integral_hasStrictDerivAt 0 z).hasDerivAt.differentiableAt,
        by simp, ?_⟩
    rwa [funext fun z ↦ (hg.continuous.integral_hasStrictDerivAt 0 z).hasDerivAt.deriv]
  exact ⟨_, _, (hf.add hG).const_smul _, (hf.sub hG).const_smul _,
    dAlembert_eq_add hg.continuous⟩

/-- For `f` of class `C²` and `g` of class `C¹`, d'Alembert's formula is `C²` on space-time. -/
theorem contDiff_dAlembert [CompleteSpace F] (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 2 (uncurry (dAlembert f g)) := by
  obtain ⟨A, B, hA, hB, h⟩ := exists_contDiff_dAlembert_eq_add hf hg
  have : uncurry (dAlembert f g) = fun p : ℝ × ℝ ↦ A (p.2 + p.1) + B (p.2 - p.1) :=
    funext fun p ↦ h p.1 p.2
  rw [this]
  exact (hA.comp (contDiff_snd.add contDiff_fst)).add (hB.comp (contDiff_snd.sub contDiff_fst))

/-- **d'Alembert's formula solves the wave equation.** For `f` of class `C²` and `g` of class
`C¹`, `u = dAlembert f g` satisfies `∂ₜ²u = ∂ₓ²u` everywhere. -/
theorem deriv_deriv_dAlembert [CompleteSpace F] (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (t x : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ dAlembert f g r x) s) t =
      deriv (deriv (dAlembert f g t)) x := by
  obtain ⟨A, B, hA, hB, h⟩ := exists_contDiff_dAlembert_eq_add hf hg
  have : dAlembert f g t = fun y ↦ A (y + t) + B (y - t) := funext (h t)
  simp only [h]
  rw [this]
  exact deriv_deriv_comp_add_add_comp_sub hA hB t x

/-- **A priori bound.** If `‖f‖ ≤ M` and `‖g‖ ≤ N` on the interval between `x - t` and `x + t`,
then `‖dAlembert f g t x‖ ≤ M + |t| N`. The linear growth in `t` is attained by `f = 0` and a
constant `g`. -/
theorem norm_dAlembert_le {M N : ℝ} (hf : ∀ y ∈ uIcc (x - t) (x + t), ‖f y‖ ≤ M)
    (hg : ∀ y ∈ uIcc (x - t) (x + t), ‖g y‖ ≤ N) : ‖dAlembert f g t x‖ ≤ M + |t| * N := by
  have hint : ‖∫ y in x - t..x + t, g y‖ ≤ N * |x + t - (x - t)| :=
    norm_integral_le_of_norm_le_const fun y hy ↦ hg y (uIoc_subset_uIcc hy)
  have habs : |x + t - (x - t)| = 2 * |t| := by
    rw [show x + t - (x - t) = 2 * t by ring, abs_mul, abs_two]
  rw [dAlembert_def]
  calc ‖(2 : ℝ)⁻¹ • (f (x + t) + f (x - t)) + (2 : ℝ)⁻¹ • ∫ y in x - t..x + t, g y‖
      ≤ (2 : ℝ)⁻¹ * (‖f (x + t)‖ + ‖f (x - t)‖) + (2 : ℝ)⁻¹ * ‖∫ y in x - t..x + t, g y‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (2 : ℝ)⁻¹ * (M + M) + (2 : ℝ)⁻¹ * (N * (2 * |t|)) := by
        gcongr
        · exact hf _ right_mem_uIcc
        · exact hf _ left_mem_uIcc
        · exact habs ▸ hint
    _ = M + |t| * N := by ring

/-- **No dispersion in one dimension.** If the initial displacement `f` vanishes outside
`(-R, R)` and the initial velocity is zero, then from time `|t| ≥ R` on the solution contains an
undamped copy of `f / 2` translated by `t`: `u(t, y + t) = f(y) / 2` for `|y| < R`. In
particular, for every `|t| ≥ R` the supremum norm of `u(t, ·)` is at least half that of `f`: it
does not decay as `|t| → ∞`. -/
theorem dAlembert_zero_right_apply_add_of_abs_lt {R y : ℝ} (hf : ∀ z, R ≤ |z| → f z = 0)
    (ht : R ≤ |t|) (hy : |y| < R) : dAlembert f 0 t (y + t) = (2 : ℝ)⁻¹ • f y := by
  have h2t : R ≤ |y + t + t| := by
    have := abs_sub_abs_le_abs_sub (2 * t) (-y)
    rw [abs_neg, abs_mul, abs_two] at this
    rw [show y + t + t = 2 * t - -y by ring]
    linarith
  rw [dAlembert_zero_right, hf _ h2t, add_sub_cancel_right, zero_add]

end DAlembert

/-! ### Representation of classical solutions and uniqueness -/

section Representation

variable {u : ℝ → ℝ → F}

/-- **The characteristic factorization.** For a `C²` solution of the wave equation,
`w = ∂ₜu + ∂ₓu`, the derivative of `u` in the direction `(1, 1)`, is constant along the lines
`x + t = const`: `w(t, x) = w(0, x + t)`. -/
private theorem fderiv_apply_one_one_eq (hu : ContDiff ℝ 2 (uncurry u))
    (hwave : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x)
    (t x : ℝ) :
    fderiv ℝ (uncurry u) (t, x) (1, 1) = fderiv ℝ (uncurry u) (0, x + t) (1, 1) := by
  set U := uncurry u
  have hU1 : Differentiable ℝ U := hu.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ U) :=
    (hu.fderiv_right (m := 1) one_add_one_eq_two.le).differentiable one_ne_zero
  -- The wave equation reads `D²U p e₁ e₁ = D²U p e₂ e₂`.
  have hpure : ∀ p : ℝ × ℝ, fderiv ℝ (fderiv ℝ U) p (1, 0) (1, 0) =
      fderiv ℝ (fderiv ℝ U) p (0, 1) (0, 1) := by
    rintro ⟨t, x⟩
    have ht : deriv (fun r ↦ u r x) = fun s ↦ fderiv ℝ U (s, x) (1, 0) :=
      funext fun s ↦ (hasDerivAt_parameterCurve_uncurry (hU1 (s, x))).deriv
    have hx : deriv (u t) = fun y ↦ fderiv ℝ U (t, y) (0, 1) :=
      funext fun y ↦ (hasDerivAt_timeSlice_uncurry (hU1 (t, y))).deriv
    have h := hwave t x
    rwa [ht, hx, (hasDerivAt_fderiv_apply_fst (hD _) _).deriv,
      (hasDerivAt_fderiv_apply_snd (hD _) _).deriv] at h
  have hsymm : ∀ p, IsSymmSndFDerivAt ℝ U p := fun p ↦
    hu.contDiffAt.isSymmSndFDerivAt (by simp)
  -- Along the characteristic `s ↦ (s, x + t - s)`, the derivative of `w` vanishes.
  have hzero : ∀ s : ℝ, fderiv ℝ (fderiv ℝ U) (((0, x + t) : ℝ × ℝ) + s • ((1, -1) : ℝ × ℝ))
      (1, -1) (1, 1) = 0 := by
    intro s
    set p : ℝ × ℝ := (0, x + t) + s • ((1, -1) : ℝ × ℝ)
    have e1 : ((1, -1) : ℝ × ℝ) = (1, 0) - (0, 1) := by simp
    have e2 : ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) := by simp
    rw [e1, e2, map_sub, map_add]
    simp only [sub_apply]
    rw [hpure p, hsymm p (1, 0) (0, 1)]
    abel
  have hline (s : ℝ) := hasDerivAt_fderiv_apply_line (p := ((0, x + t) : ℝ × ℝ))
    (q := ((1, -1) : ℝ × ℝ)) (hD _) ((1, 1) : ℝ × ℝ) (s := s)
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hline s).differentiableAt)
    (fun s ↦ (hline s).deriv.trans (hzero s)) t 0
  simpa [Prod.ext_iff] using hconst

variable [CompleteSpace F]

/-- **Representation of classical solutions.** Every `C²` solution `u` of the wave equation
`∂ₜ²u = ∂ₓ²u` on the space-time plane is given by d'Alembert's formula in terms of its initial
displacement `u(0, ·)` and initial velocity `∂ₜu(0, ·)`. No growth condition at infinity is
assumed. -/
theorem eq_dAlembert_of_deriv_deriv_eq (hu : ContDiff ℝ 2 (uncurry u))
    (hwave : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x)
    (t x : ℝ) : u t x = dAlembert (u 0) (fun y ↦ deriv (fun s ↦ u s y) 0) t x := by
  set U := uncurry u
  have hU1 : Differentiable ℝ U := hu.differentiable (by norm_num)
  set g : ℝ → F := fun y ↦ deriv (fun s ↦ u s y) 0
  -- `h z = w(0, z) = g z + (u 0)' z` is the value of `∂ₜu + ∂ₓu` on the initial line.
  set h : ℝ → F := fun z ↦ fderiv ℝ U (0, z) (1, 1)
  have hcont (v : ℝ × ℝ) : Continuous fun z ↦ fderiv ℝ U (0, z) v := by
    have := hu.continuous_fderiv (by norm_num)
    fun_prop
  have hg (z : ℝ) : g z = fderiv ℝ U (0, z) (1, 0) :=
    (hasDerivAt_parameterCurve_uncurry (hU1 (0, z))).deriv
  have hf' (z : ℝ) : HasDerivAt (u 0) (fderiv ℝ U (0, z) (0, 1)) z :=
    hasDerivAt_timeSlice_uncurry (hU1 (0, z))
  have hh : h = fun z ↦ g z + fderiv ℝ U (0, z) (0, 1) := by
    ext z
    rw [hg z, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  -- Along `s ↦ (s, x - t + s)`, the derivative of `u` is `h (2 s + (x - t))`.
  have hψ : ∀ s, HasDerivAt (fun r ↦ U (r, x - t + r)) (h (2 * s + (x - t))) s := by
    intro s
    have hline : HasDerivAt (fun r : ℝ ↦ (r, x - t + r)) ((1, 1) : ℝ × ℝ) s :=
      (hasDerivAt_id s).prodMk ((hasDerivAt_id s).const_add (x - t))
    have := (hU1 (s, x - t + s)).hasFDerivAt.comp_hasDerivAt s hline
    rwa [fderiv_apply_one_one_eq hu hwave, show x - t + s + s = 2 * s + (x - t) by ring] at this
  have hFTC := integral_eq_sub_of_hasDerivAt (fun s _ ↦ hψ s)
    (((hcont ((1, 1) : ℝ × ℝ)).comp ((continuous_const.mul continuous_id).add
      continuous_const)).intervalIntegrable 0 t)
  simp only [U, uncurry_apply_pair, sub_add_cancel, add_zero] at hFTC
  have hsub : ∫ y in x - t..x + t, fderiv ℝ U (0, y) (0, 1) = u 0 (x + t) - u 0 (x - t) :=
    integral_eq_sub_of_hasDerivAt (fun z _ ↦ hf' z) ((hcont _).intervalIntegrable _ _)
  have hcomp : ∫ s in (0 : ℝ)..t, h (2 * s + (x - t)) =
      (2 : ℝ)⁻¹ • ((∫ y in x - t..x + t, g y) + (u 0 (x + t) - u 0 (x - t))) := by
    rw [integral_comp_mul_add _ two_ne_zero, mul_zero, zero_add,
      show 2 * t + (x - t) = x + t by ring, hh, integral_add ?_ ((hcont _).intervalIntegrable _ _),
      hsub]
    simp only [g, funext hg]
    exact (hcont _).intervalIntegrable _ _
  rw [sub_eq_iff_eq_add.1 hFTC.symm, hcomp, dAlembert_def]
  module

/-- **The domain of dependence.** Two `C²` solutions of the wave equation whose initial
displacements and initial velocities agree on the interval between `x - t` and `x + t` agree at
`(t, x)`. In other words, waves propagate with speed at most one. -/
theorem eq_of_deriv_deriv_eq_of_eqOn_initial {v : ℝ → ℝ → F} (hu : ContDiff ℝ 2 (uncurry u))
    (hv : ContDiff ℝ 2 (uncurry v))
    (hwu : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x)
    (hwv : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ v r x) s) t = deriv (deriv (v t)) x)
    {t x : ℝ} (h0 : EqOn (u 0) (v 0) (uIcc (x - t) (x + t)))
    (h1 : EqOn (fun y ↦ deriv (fun s ↦ u s y) 0) (fun y ↦ deriv (fun s ↦ v s y) 0)
      (uIcc (x - t) (x + t))) : u t x = v t x := by
  rw [eq_dAlembert_of_deriv_deriv_eq hu hwu, eq_dAlembert_of_deriv_deriv_eq hv hwv,
    dAlembert_congr h0 h1]

/-- **Uniqueness for the Cauchy problem.** Two `C²` solutions of the wave equation on the
space-time plane with the same initial displacement and the same initial velocity are equal. -/
theorem eq_of_deriv_deriv_eq_of_eq_initial {v : ℝ → ℝ → F} (hu : ContDiff ℝ 2 (uncurry u))
    (hv : ContDiff ℝ 2 (uncurry v))
    (hwu : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x)
    (hwv : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ v r x) s) t = deriv (deriv (v t)) x)
    (h0 : u 0 = v 0) (h1 : ∀ y, deriv (fun s ↦ u s y) 0 = deriv (fun s ↦ v s y) 0) : u = v :=
  funext fun _ ↦ funext fun _ ↦ eq_of_deriv_deriv_eq_of_eqOn_initial hu hv hwu hwv
    (fun y _ ↦ congrFun h0 y) (fun y _ ↦ h1 y)

end Representation

/-! ### Conservation of energy -/

section Energy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The energy of the superposition `A(x + t) + B(x - t)` of two travelling waves, written in terms
of the a.e. strongly measurable profiles `A'`, `B'` of their derivatives: since
`∂ₜu = A'(x + t) - B'(x - t)` and `∂ₓu = A'(x + t) + B'(x - t)`, it equals
`2 ∫ ‖A'‖² + 2 ∫ ‖B'‖²` and does not depend on `t`. -/
theorem lintegral_enorm_sub_sq_add_enorm_add_sq {A' B' : ℝ → H} (hA : AEStronglyMeasurable A')
    (hB : AEStronglyMeasurable B') (t : ℝ) :
    ∫⁻ x, (‖A' (x + t) - B' (x - t)‖ₑ ^ 2 + ‖A' (x + t) + B' (x - t)‖ₑ ^ 2) =
      2 * (∫⁻ z, ‖A' z‖ₑ ^ 2) + 2 * ∫⁻ z, ‖B' z‖ₑ ^ 2 := by
  simp_rw [add_comm (‖_ - _‖ₑ ^ 2), parallelogram_law_with_enorm ℝ, mul_add]
  have hA' : AEMeasurable fun x ↦ ‖A' (x + t)‖ₑ ^ 2 :=
    (hA.comp_measurePreserving (measurePreserving_add_right volume t)).enorm.pow_const 2
  have hB' : AEMeasurable fun x ↦ ‖B' (x - t)‖ₑ ^ 2 :=
    (hB.comp_measurePreserving (measurePreserving_sub_right volume t)).enorm.pow_const 2
  rw [lintegral_add_left' (hA'.const_mul 2), lintegral_const_mul'' _ hA',
    lintegral_const_mul'' _ hB', lintegral_add_right_eq_self (fun z ↦ ‖A' z‖ₑ ^ 2),
    lintegral_sub_right_eq_self (fun z ↦ ‖B' z‖ₑ ^ 2)]

/-- **Conservation of energy.** For a `C²` solution `u` of the wave equation with values in a
real Hilbert space, the energy `∫ ‖∂ₜu(t, x)‖² + ‖∂ₓu(t, x)‖² dx` is independent of `t`. The
identity holds in `ℝ≥0∞`, so solutions of infinite energy are included. -/
theorem lintegral_enorm_deriv_sq_add_enorm_deriv_sq_eq [CompleteSpace H] {u : ℝ → ℝ → H}
    (hu : ContDiff ℝ 2 (uncurry u))
    (hwave : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x)
    (t : ℝ) :
    ∫⁻ x, (‖deriv (fun s ↦ u s x) t‖ₑ ^ 2 + ‖deriv (u t) x‖ₑ ^ 2) =
      ∫⁻ x, (‖deriv (fun s ↦ u s x) 0‖ₑ ^ 2 + ‖deriv (u 0) x‖ₑ ^ 2) := by
  set f := u 0
  set g : ℝ → H := fun y ↦ deriv (fun s ↦ u s y) 0
  have hrep : u = dAlembert f g :=
    funext fun t ↦ funext (eq_dAlembert_of_deriv_deriv_eq hu hwave t)
  have hf : ContDiff ℝ 1 f := (hu.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  have hg : Continuous g := by
    have : g = fun y ↦ fderiv ℝ (uncurry u) (0, y) (1, 0) :=
      funext fun y ↦
        (hasDerivAt_parameterCurve_uncurry (hu.differentiable (by norm_num) (0, y))).deriv
    have hD := hu.continuous_fderiv (by norm_num)
    rw [this]
    fun_prop
  have hf' : Continuous (deriv f) := hf.continuous_deriv_one
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have key : ∀ t, ∫⁻ x, (‖deriv (fun s ↦ u s x) t‖ₑ ^ 2 + ‖deriv (u t) x‖ₑ ^ 2) =
      2 * (∫⁻ z, ‖(2 : ℝ)⁻¹ • (deriv f z + g z)‖ₑ ^ 2) +
        2 * ∫⁻ z, ‖(2 : ℝ)⁻¹ • (deriv f z - g z)‖ₑ ^ 2 := fun t ↦ by
    rw [hrep]
    simp_rw [(hasDerivAt_dAlembert_time hfd hg t _).deriv,
      (hasDerivAt_dAlembert_space hfd hg t _).deriv]
    exact lintegral_enorm_sub_sq_add_enorm_add_sq ((hf'.add hg).const_smul _).aestronglyMeasurable
      ((hf'.sub hg).const_smul _).aestronglyMeasurable t
  rw [key, key]

end Energy

end PDE

end TauCeti
