/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Contour.Winding.Number.Homotopy
public import TauCeti.Topology.Circle.Degree

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.Normed.Module.Normalize

/-!
# Winding number, continuous logarithms, and homotopy of nowhere-zero circle functions

For a nowhere-zero continuous complex function `f : C(AddCircle T, ℂ)`, radial normalization gives
a continuous map `f.normalizeToCircle hf : C(AddCircle T, Circle)` sending `x` to `f x / ‖f x‖`,
and pulling back along `[0, 1] → AddCircle T`, `t ↦ t * T`, produces a closed loop
`f.normalizedLoop hf` in `Circle`. Its topological degree (`Circle.degree`) is the **winding
number** `f.windingNumber hf : ℤ` of `f` about the origin.

Lifting `f.normalizeToCircle hf` along the universal covering `Circle.exp : ℝ → Circle` yields a
continuous real angle function whose increment over each period `T` is `k * (2π)`, where
`k = f.windingNumber hf`. Subtracting the linear drift `k * (2π / T) * x` produces a continuous
`T`-periodic phase `ψ`, giving the canonical factorization
`f x = fourier k x * Complex.exp (g x)` for a continuous `g : C(AddCircle T, ℂ)`
(`ContinuousMap.exists_eq_fourier_mul_exp`). Three consequences follow immediately:

* **Continuous logarithm criterion** (`ContinuousMap.windingNumber_eq_zero_iff_exists_exp`): a
  nowhere-zero continuous circle function has winding number `0` if and only if it is the
  exponential of a continuous circle function.
* **Hopf homotopy classification** (`ContinuousMap.exists_homotopy_fourier`,
  `ContinuousMap.windingNumber_eq_iff_exists_homotopy_fourier`): `f` is homotopic through
  nowhere-zero continuous circle functions to the Fourier monomial `fourier k` precisely when
  `f.windingNumber hf = k`.
* **Agreement with the contour winding integral**
  (`ContinuousMap.coe_windingNumber_eq_contour_windingNumber_mul`,
  `ContinuousMap.coe_windingNumber_eq_contour_windingNumber`): when the unit-interval pullback of
  `f` is piecewise `C¹` on `[0, 1]`, `(f.windingNumber hf : ℂ)` coincides with
  `TauCeti.Contour.windingNumber` about `0`.

Finally, `ContinuousMap.exists_norm_sub_lt_windingNumber_ne` shows that any continuous circle
function that vanishes at a point can be uniformly approximated arbitrarily closely by pairs of
nowhere-zero continuous functions of different winding numbers. Approximating `f` uniformly by a
trigonometric polynomial shifted to vanish at the same point and factoring over `ℂ`, pushing a
unit-circle root slightly inside versus slightly outside the unit circle changes the winding number
by `1`. This is the topological input showing that a Fredholm Toeplitz operator with continuous
symbol must have nowhere-vanishing symbol.

## Main definitions

* `ContinuousMap.normalizeToCircle`: radial normalization `x ↦ f x / ‖f x‖` of a nowhere-zero
  continuous map `f : C(X, ℂ)` into `Circle`.
* `ContinuousMap.normalizedLoop`: the loop `t ↦ f.normalizeToCircle hf (t * T)` in `Circle`.
* `ContinuousMap.windingNumber`: the integer winding number `Circle.degree (f.normalizedLoop hf)`.

## Main results

* `TauCeti.fourier_ne_zero`, `TauCeti.norm_fourier_apply`: Fourier monomials on `AddCircle T` are
  nowhere zero and have pointwise norm `1`.
* `ContinuousMap.windingNumber_mul`, `ContinuousMap.windingNumber_fourier`,
  `ContinuousMap.windingNumber_eq_of_homotopy`, `ContinuousMap.windingNumber_eq_of_norm_sub_lt`:
  additivity, normalization on Fourier modes, homotopy invariance, and Rouché stability.
* `ContinuousMap.exists_eq_fourier_mul_exp`: factorization `f = fourier k * (Complex.exp ∘ g)`.
* `ContinuousMap.windingNumber_eq_zero_iff_exists_exp`: degree zero iff continuous logarithm.
* `ContinuousMap.exists_homotopy_fourier`: nowhere-zero homotopy from `f` to `fourier k`.
* `ContinuousMap.coe_windingNumber_eq_contour_windingNumber_mul`,
  `ContinuousMap.coe_windingNumber_eq_contour_windingNumber`: equality with
  `TauCeti.Contour.windingNumber` for piecewise-`C¹` pullbacks.
* `ContinuousMap.exists_norm_sub_lt_windingNumber_ne`: uniform approximation of a circle function
  with a zero by nowhere-zero functions of distinct winding numbers.

## References

* I. C. Gohberg and M. G. Krein, *Systems of integral equations on a half line with kernels
  depending on the difference of arguments*, Amer. Math. Soc. Transl. (2) 14 (1960), 217–287.
* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, second edition, Chapter 7.
* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, §2.
-/

public section

noncomputable section

open Metric NormedSpace Set
open scoped unitInterval

namespace TauCeti

/-- Every Fourier monomial on `AddCircle T` is nowhere zero. -/
theorem fourier_ne_zero {T : ℝ} (k : ℤ) (x : AddCircle T) : fourier k x ≠ 0 := by
  rw [fourier_apply]
  exact Circle.coe_ne_zero _

/-- Every Fourier monomial on `AddCircle T` has pointwise modulus `1`. -/
theorem norm_fourier_apply {T : ℝ} (k : ℤ) (x : AddCircle T) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

end TauCeti

namespace ContinuousMap

open TauCeti

section Normalize

variable {X : Type*} [TopologicalSpace X]

/-- Radial normalization of a nowhere-zero continuous complex function `f : C(X, ℂ)` as a
continuous map into `Circle`, sending `x` to `f x / ‖f x‖`. -/
def normalizeToCircle (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) : C(X, Circle) where
  toFun x := ⟨NormedSpace.normalize (f x),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hf x))⟩
  continuous_toFun :=
    (continuous_iff_continuousAt.2 fun x => (f.continuous.tendsto x).normalize (hf x)).subtype_mk _

private theorem coe_normalizeToCircle_eq_normalize (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    ((f.normalizeToCircle hf x : Circle) : ℂ) = NormedSpace.normalize (f x) :=
  (rfl)

/-- The complex value of `f.normalizeToCircle hf x` is `f x / ‖f x‖`. -/
@[simp]
theorem coe_normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖ := by
  rw [coe_normalizeToCircle_eq_normalize, NormedSpace.normalize, Complex.real_smul,
    Complex.ofReal_inv, inv_mul_eq_div]

/-- Multiplying the normalized phase `f.normalizeToCircle hf x` by `‖f x‖` recovers `f x`. -/
theorem norm_mul_normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x := by
  have hnorm : (‖f x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf x))
  rw [coe_normalizeToCircle_apply, mul_div_cancel₀ _ hnorm]

/-- Radial normalization into `Circle` respects pointwise multiplication. -/
@[simp]
theorem normalizeToCircle_mul (f g : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) (x : X) :
    (f * g).normalizeToCircle (fun y => mul_ne_zero (hf y) (hg y)) x =
      f.normalizeToCircle hf x * g.normalizeToCircle hg x := by
  apply Circle.ext
  simp [Complex.ofReal_mul, div_mul_div_comm]

/-- Radial normalization sends `1` to `1`. -/
@[simp]
theorem normalizeToCircle_one
    (hf : ∀ x : X, (1 : C(X, ℂ)) x ≠ 0 := fun _ => one_ne_zero) (x : X) :
    (1 : C(X, ℂ)).normalizeToCircle hf x = 1 := by
  apply Circle.ext
  rw [coe_normalizeToCircle_apply]
  simp

end Normalize

section Winding

variable {T : ℝ}

/-- Pulling `f.normalizeToCircle hf` back along `[0, 1] → AddCircle T`, `t ↦ t * T`, gives a
closed loop in `Circle` based at `f.normalizeToCircle hf 0`. -/
def normalizedLoop (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) :
    Path (f.normalizeToCircle hf 0) (f.normalizeToCircle hf 0) where
  toFun t := f.normalizeToCircle hf (((t : ℝ) * T : ℝ) : AddCircle T)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [AddCircle.coe_period]

/-- Evaluation of `f.normalizedLoop hf` at `t ∈ [0, 1]`. -/
@[simp]
theorem normalizedLoop_apply (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) (t : I) :
    f.normalizedLoop hf t = f.normalizeToCircle hf (((t : ℝ) * T : ℝ) : AddCircle T) :=
  (rfl)

/-- The **winding number** of a nowhere-zero continuous circle function `f : C(AddCircle T, ℂ)`
about `0`, defined as `Circle.degree (f.normalizedLoop hf)`. -/
def windingNumber (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) : ℤ :=
  Circle.degree (f.normalizedLoop hf)

/-- Defining formula for `ContinuousMap.windingNumber`. -/
theorem windingNumber_def (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) :
    f.windingNumber hf = Circle.degree (f.normalizedLoop hf) :=
  (rfl)

/-- Two nowhere-zero continuous circle functions with the same radial normalization have the same
winding number. -/
theorem windingNumber_eq_of_normalizeToCircle_eq {f g : C(AddCircle T, ℂ)}
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    (hfg : ∀ x, f.normalizeToCircle hf x = g.normalizeToCircle hg x) :
    f.windingNumber hf = g.windingNumber hg :=
  Circle.degree_congr _ _ fun t => hfg (((t : ℝ) * T : ℝ) : AddCircle T)

/-- Pointwise equal nowhere-zero continuous circle functions have the same winding number. -/
theorem windingNumber_congr {f g : C(AddCircle T, ℂ)} (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    (hfg : ∀ x, f x = g x) : f.windingNumber hf = g.windingNumber hg :=
  windingNumber_eq_of_normalizeToCircle_eq hf hg fun x => by
    apply Circle.ext
    simp [hfg x]

/-- A nonzero constant circle function has winding number `0`. -/
theorem windingNumber_const {c : ℂ} (hc : c ≠ 0)
    (hf : ∀ x : AddCircle T, ContinuousMap.const (AddCircle T) c x ≠ 0 := fun _ => hc) :
    (ContinuousMap.const (AddCircle T) c).windingNumber hf = 0 := by
  let x₀ := (ContinuousMap.const (AddCircle T) c).normalizeToCircle hf 0
  refine (Circle.degree_congr _ (Path.refl x₀) fun t => ?_).trans (Circle.degree_refl x₀)
  apply Circle.ext
  simp [x₀, coe_normalizeToCircle_apply]

/-- The constant function `1` has winding number `0`. -/
@[simp]
theorem windingNumber_one
    (hf : ∀ x : AddCircle T, (1 : C(AddCircle T, ℂ)) x ≠ 0 := fun _ => one_ne_zero) :
    (1 : C(AddCircle T, ℂ)).windingNumber hf = 0 :=
  windingNumber_const one_ne_zero hf

/-- The winding number of a pointwise product is the sum of the winding numbers. -/
theorem windingNumber_mul (f g : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    (hfg : ∀ x, (f * g) x ≠ 0 := fun x => mul_ne_zero (hf x) (hg x)) :
    (f * g).windingNumber hfg = f.windingNumber hf + g.windingNumber hg := by
  rw [windingNumber_def, windingNumber_def, windingNumber_def, ← Circle.degree_mul]
  refine Circle.degree_congr _ _ fun t => ?_
  simp only [normalizedLoop_apply, Path.mul_apply]
  exact normalizeToCircle_mul f g hf hg _

/-- A nonzero scalar multiple of a nowhere-zero circle function has the same winding number. -/
theorem windingNumber_smul {c : ℂ} (hc : c ≠ 0) (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0)
    (hcf : ∀ x, (c • f) x ≠ 0 := fun x => mul_ne_zero hc (hf x)) :
    (c • f).windingNumber hcf = f.windingNumber hf := by
  have hc' : ∀ x : AddCircle T, ContinuousMap.const (AddCircle T) c x ≠ 0 := fun _ => hc
  exact (windingNumber_congr hcf (fun x => mul_ne_zero (hc' x) (hf x)) fun _ => rfl).trans
    ((windingNumber_mul _ _ hc' hf).trans (by rw [windingNumber_const hc, zero_add]))

/-- The winding number of the `n`-th pointwise power is `n` times the winding number. -/
theorem windingNumber_pow (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) (n : ℕ)
    (hfn : ∀ x, (f ^ n) x ≠ 0 := fun x => pow_ne_zero n (hf x)) :
    (f ^ n).windingNumber hfn = n * f.windingNumber hf := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hfn' : ∀ x, (f ^ n) x ≠ 0 := fun x => pow_ne_zero n (hf x)
    have hpow : ∀ x, (f ^ (n + 1)) x = (f ^ n * f) x := fun x => by simp [pow_succ]
    rw [windingNumber_congr hfn (fun x => mul_ne_zero (hfn' x) (hf x)) hpow,
      windingNumber_mul _ _ hfn' hf, ih hfn']
    push_cast
    ring

/-- **Homotopy invariance of the winding number.** Two nowhere-zero continuous circle functions
joined by a continuous homotopy through nowhere-zero functions have the same winding number. -/
theorem windingNumber_eq_of_homotopy {f g : C(AddCircle T, ℂ)}
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) (H : C(I × AddCircle T, ℂ))
    (hH : ∀ p, H p ≠ 0) (h0 : ∀ x, H (0, x) = f x) (h1 : ∀ x, H (1, x) = g x) :
    f.windingNumber hf = g.windingNumber hg := by
  let F : C(I × I, Circle) :=
    (H.normalizeToCircle hH).comp
      ⟨fun p : I × I => (p.1, (((p.2 : ℝ) * T : ℝ) : AddCircle T)), by fun_prop⟩
  refine Circle.degree_eq_of_homotopy (f.normalizedLoop hf) (g.normalizedLoop hg) F
    (fun t => ?_) (fun t => ?_) (fun s => ?_)
  · apply Circle.ext
    simp [F, h0]
  · apply Circle.ext
    simp [F, h1]
  · simp [F, AddCircle.coe_period]

/-- **Rouché stability of the winding number.** If `‖g x - f x‖ < ‖f x‖` at every point of the
circle, then `g` is nowhere zero and has the same winding number as `f`. -/
theorem windingNumber_eq_of_norm_sub_lt {f g : C(AddCircle T, ℂ)}
    (hf : ∀ x, f x ≠ 0) (hfg : ∀ x, ‖g x - f x‖ < ‖f x‖)
    (hg : ∀ x, g x ≠ 0 := fun x hx => by simpa [hx] using (hfg x).ne) :
    g.windingNumber hg = f.windingNumber hf := by
  let H : C(I × AddCircle T, ℂ) :=
    ⟨fun p => f p.2 + (p.1 : ℝ) • (g p.2 - f p.2), by fun_prop⟩
  have hH (p : I × AddCircle T) : H p ≠ 0 := by
    intro hp
    have heq : (p.1 : ℝ) • (g p.2 - f p.2) = -f p.2 := eq_neg_of_add_eq_zero_right hp
    have hnorm : ‖f p.2‖ = (p.1 : ℝ) * ‖g p.2 - f p.2‖ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.2.1] using
        (congrArg norm heq).symm
    have hle : (p.1 : ℝ) * ‖g p.2 - f p.2‖ ≤ 1 * ‖g p.2 - f p.2‖ :=
      mul_le_mul_of_nonneg_right p.1.2.2 (norm_nonneg _)
    linarith [hfg p.2]
  exact (windingNumber_eq_of_homotopy hf hg H hH (fun x => by simp [H])
    (fun x => by simp [H])).symm

/-- The `k`-th Fourier monomial `x ↦ exp(2πikx / T)` has winding number `k`. -/
@[simp]
theorem windingNumber_fourier [hT : Fact (0 < T)] (k : ℤ)
    (hf : ∀ x : AddCircle T, fourier k x ≠ 0 := fourier_ne_zero k) :
    (fourier (T := T) k).windingNumber hf = k := by
  have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.out.ne'
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t : I => k * (2 * Real.pi) * (t : ℝ))
    (by fun_prop) (fun t => ?_) (by simp)
  apply Circle.ext
  rw [Circle.coe_exp, normalizedLoop_apply, coe_normalizeToCircle_apply, norm_fourier_apply,
    Complex.ofReal_one, div_one, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- **Canonical exponential factorization of a nowhere-zero circle function.** Every nowhere-zero
continuous `f : C(AddCircle T, ℂ)` factors as `f x = fourier (f.windingNumber hf) x * exp(g x)`
for some continuous `g : C(AddCircle T, ℂ)`. -/
theorem exists_eq_fourier_mul_exp [hT : Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (hf : ∀ x, f x ≠ 0) :
    ∃ g : C(AddCircle T, ℂ), ∀ x, f x = fourier (f.windingNumber hf) x * Complex.exp (g x) := by
  have hTne : T ≠ 0 := hT.out.ne'
  set k : ℤ := f.windingNumber hf
  -- Lift the normalized map along `Circle.exp : ℝ → Circle` over the universal cover `ℝ`.
  let u : C(ℝ, Circle) :=
    (f.normalizeToCircle hf).comp ⟨((↑) : ℝ → AddCircle T), continuous_quotient_mk'⟩
  obtain ⟨Θ, ⟨-, hΘ_lift⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts u 0 (Complex.arg (u 0))
      (Circle.exp_arg (u 0))
  have hΘ (r : ℝ) : Circle.exp (Θ r) = f.normalizeToCircle hf (r : AddCircle T) :=
    congr_fun hΘ_lift r
  -- Read the degree off the restriction of `Θ` to `[0, T]`.
  have hsubT : Θ T - Θ 0 = k * (2 * Real.pi) := by
    have hloop := Circle.sub_eq_degree_mul (f.normalizedLoop hf)
      (θ := fun t : I => Θ ((t : ℝ) * T)) (by fun_prop) (fun t => hΘ ((t : ℝ) * T))
    simpa [k, windingNumber_def] using hloop
  -- `Θ (r + T) - Θ r` is constant on `ℝ`, hence equal to `k * (2π)`.
  obtain ⟨c, hc⟩ := Circle.exists_forall_eq_add_of_exp_eq (G := fun r => Θ (r + T)) (G' := Θ)
    (by fun_prop) Θ.continuous fun r => by rw [hΘ, hΘ, AddCircle.coe_add_period]
  have hc_eq : c = k * (2 * Real.pi) := by
    have hc0 := hc 0
    rw [zero_add] at hc0
    linarith [hc0, hsubT]
  -- Subtracting the linear drift makes the angle lift `T`-periodic.
  let Ψ : ℝ → ℝ := fun r => Θ r - k * (2 * Real.pi / T) * r
  have hΨ_per : Function.Periodic Ψ T := fun r => by
    simp only [Ψ, hc r, hc_eq]
    field_simp
    ring
  have hΨ_cont : Continuous Ψ := by fun_prop
  let ψ : C(AddCircle T, ℝ) :=
    ⟨hΨ_per.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr <| by
      have hcomp : hΨ_per.lift ∘ ((↑) : ℝ → AddCircle T) = Ψ := funext hΨ_per.lift_coe
      rwa [hcomp]⟩
  let g : C(AddCircle T, ℂ) :=
    ⟨fun x => (Real.log ‖f x‖ : ℂ) + (ψ x : ℂ) * Complex.I,
      Continuous.add
        (Complex.continuous_ofReal.comp
          (f.continuous.norm.log fun x => norm_ne_zero_iff.mpr (hf x)))
        ((Complex.continuous_ofReal.comp ψ.continuous).mul continuous_const)⟩
  refine ⟨g, fun x => ?_⟩
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hψr : ψ (r : AddCircle T) = Ψ r := hΨ_per.lift_coe r
  have hexp_log : Complex.exp (Real.log ‖f (r : AddCircle T)‖) = ‖f (r : AddCircle T)‖ := by
    rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hf _))]
  have hexp_phase :
      fourier k (r : AddCircle T) * Complex.exp ((Ψ r : ℂ) * Complex.I) =
        (f.normalizeToCircle hf (r : AddCircle T) : ℂ) := by
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * k * r / T + (Ψ r : ℂ) * Complex.I =
          (Θ r : ℂ) * Complex.I := by
      have hTℂ : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTne
      simp only [Ψ, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_intCast, Complex.ofReal_ofNat]
      field_simp
      ring
    rw [fourier_coe_apply, ← Complex.exp_add, harg, ← Circle.coe_exp, hΘ]
  calc
    f (r : AddCircle T)
      = (‖f (r : AddCircle T)‖ : ℂ) * (f.normalizeToCircle hf (r : AddCircle T) : ℂ) :=
        (f.norm_mul_normalizeToCircle_apply hf _).symm
    _ = Complex.exp (Real.log ‖f (r : AddCircle T)‖) *
          (fourier k (r : AddCircle T) * Complex.exp ((Ψ r : ℂ) * Complex.I)) := by
        rw [hexp_log, hexp_phase]
    _ = fourier k (r : AddCircle T) * Complex.exp (g (r : AddCircle T)) := by
        simp only [g, ContinuousMap.coe_mk, hψr, Complex.exp_add]
        ring

/-- **Continuous logarithm criterion.** A nowhere-zero continuous circle function has winding
number `0` if and only if it is the exponential of a continuous complex function on the circle. -/
theorem windingNumber_eq_zero_iff_exists_exp [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (hf : ∀ x, f x ≠ 0) :
    f.windingNumber hf = 0 ↔ ∃ g : C(AddCircle T, ℂ), ∀ x, f x = Complex.exp (g x) := by
  constructor
  · intro h0
    obtain ⟨g, hg⟩ := f.exists_eq_fourier_mul_exp hf
    exact ⟨g, fun x => by simpa [h0] using hg x⟩
  · rintro ⟨g, hg⟩
    refine Circle.degree_eq_of_sub_eq _
      (θ := fun t : I => (g (((t : ℝ) * T : ℝ) : AddCircle T)).im) (by fun_prop)
      (fun t => ?_) (by simp [AddCircle.coe_period])
    apply Circle.ext
    have hx := hg (((t : ℝ) * T : ℝ) : AddCircle T)
    have hre_im : Complex.exp (g (((t : ℝ) * T : ℝ) : AddCircle T)) =
        (Real.exp (g (((t : ℝ) * T : ℝ) : AddCircle T)).re : ℂ) *
          Complex.exp (((g (((t : ℝ) * T : ℝ) : AddCircle T)).im : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im (g (((t : ℝ) * T : ℝ) : AddCircle T))]
      rw [Complex.exp_add, Complex.ofReal_exp]
    rw [Circle.coe_exp, normalizedLoop_apply, coe_normalizeToCircle_apply, hx, Complex.norm_exp,
      hre_im, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]

/-- Every nowhere-zero continuous circle function `f` is continuously homotopic through
nowhere-zero functions to the Fourier monomial `fourier (f.windingNumber hf)`. -/
theorem exists_homotopy_fourier [Fact (0 < T)] (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0) :
    ∃ H : C(I × AddCircle T, ℂ),
      (∀ p, H p ≠ 0) ∧ (∀ x, H (0, x) = f x) ∧
        ∀ x, H (1, x) = fourier (f.windingNumber hf) x := by
  obtain ⟨g, hg⟩ := f.exists_eq_fourier_mul_exp hf
  refine ⟨⟨fun p => fourier (f.windingNumber hf) p.2 *
      Complex.exp (((1 - (p.1 : ℝ)) : ℂ) * g p.2), by fun_prop⟩,
    fun p => mul_ne_zero (fourier_ne_zero _ _) (Complex.exp_ne_zero _),
    fun x => ?_, fun x => ?_⟩
  · simpa using (hg x).symm
  · simp

/-- **Hopf classification of nowhere-zero circle functions.** A nowhere-zero continuous circle
function has winding number `k` if and only if it is homotopic through nowhere-zero continuous
functions to `fourier k`. -/
theorem windingNumber_eq_iff_exists_homotopy_fourier [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (hf : ∀ x, f x ≠ 0) (k : ℤ) :
    f.windingNumber hf = k ↔
      ∃ H : C(I × AddCircle T, ℂ),
        (∀ p, H p ≠ 0) ∧ (∀ x, H (0, x) = f x) ∧ ∀ x, H (1, x) = fourier k x := by
  constructor
  · rintro rfl
    exact f.exists_homotopy_fourier hf
  · rintro ⟨H, hH, h0, h1⟩
    rw [windingNumber_eq_of_homotopy hf (fourier_ne_zero k) H hH h0 h1, windingNumber_fourier]

end Winding

section ContourComparison

/-- Piecewise `C¹` regularity on `[a, b]` transfers across functions agreeing on `uIcc a b`. -/
private theorem isPiecewiseC1On_congr {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ}
    (h : TauCeti.IsPiecewiseC1On γ₁ a b) (heq : EqOn γ₁ γ₂ (uIcc a b)) :
    TauCeti.IsPiecewiseC1On γ₂ a b := by
  rw [TauCeti.isPiecewiseC1On_iff] at h ⊢
  obtain ⟨hcont, p, hp, hpieces⟩ := h
  exact ⟨hcont.congr heq.symm, p, hp, fun c d hcd hdisj =>
    (hpieces c d hcd hdisj).congr (heq.symm.mono hcd)⟩

/-- Direct evaluation of the contour winding integral of `t ↦ c₀ * exp(2πikt)` on `[0, 1]`. -/
private theorem contour_windingNumber_const_mul_exp (c₀ : ℂ) (hc₀ : c₀ ≠ 0) (k : ℤ) :
    TauCeti.Contour.windingNumber
        (fun t : ℝ => c₀ * Complex.exp (2 * Real.pi * Complex.I * k * t)) 0 1 0 = k := by
  set α : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
  set δ : ℝ → ℂ := fun t => c₀ * Complex.exp (α * t)
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hδ_ne (t : ℝ) : δ t ≠ 0 := mul_ne_zero hc₀ (Complex.exp_ne_zero _)
  have hδ_deriv (t : ℝ) : HasDerivAt δ (δ t * α) t := by
    have hlin : HasDerivAt (fun s : ℝ => α * (s : ℂ)) α t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul α
    simpa [δ, mul_assoc] using (hlin.cexp).const_mul c₀
  have hint_eq (t : ℝ) : (δ t - 0)⁻¹ * deriv δ t = α := by
    rw [sub_zero, (hδ_deriv t).deriv, inv_mul_cancel_left₀ (hδ_ne t)]
  have hdiv_fun : (fun t => (δ t - 0)⁻¹ * deriv δ t) = fun _ => α := funext hint_eq
  have hcont : ContinuousOn δ (uIcc 0 1) := by
    refine Continuous.continuousOn ?_
    simp only [δ]
    fun_prop
  have hint : IntervalIntegrable (fun t => (δ t - 0)⁻¹ * deriv δ t)
      MeasureTheory.volume 0 1 := by
    simp only [hint_eq]
    exact intervalIntegrable_const
  rw [TauCeti.Contour.windingNumber_eq_integral_of_avoidance hcont
    (fun t _ => hδ_ne t) hint, hdiv_fun, intervalIntegral.integral_const]
  simp only [sub_zero, one_smul, α]
  field_simp

/-- **Equality of topological and contour winding numbers on `AddCircle T`.** For a nowhere-zero
continuous function `f : C(AddCircle T, ℂ)` whose unit-interval pullback
`t ↦ f (((t * T : ℝ) : AddCircle T))` is piecewise `C¹` on `[0, 1]`, the integer winding number
`f.windingNumber hf` equals the contour winding integral about `0`. -/
theorem coe_windingNumber_eq_contour_windingNumber_mul {T : ℝ} [hT : Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) (hf : ∀ x, f x ≠ 0)
    (hC1 : TauCeti.IsPiecewiseC1On (fun t : ℝ => f (((t * T : ℝ) : AddCircle T))) 0 1) :
    (f.windingNumber hf : ℂ) =
      TauCeti.Contour.windingNumber (fun t : ℝ => f (((t * T : ℝ) : AddCircle T))) 0 1 0 := by
  have hTℂ : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.out.ne'
  set k : ℤ := f.windingNumber hf
  obtain ⟨g, hg⟩ := f.exists_eq_fourier_mul_exp hf
  have hf0 : f 0 = Complex.exp (g 0) := by simpa using hg 0
  have hfg (x : AddCircle T) :
      f x = f 0 * fourier k x * Complex.exp (g x - g 0) := by
    rw [hf0, mul_comm (Complex.exp (g 0)), mul_assoc, ← Complex.exp_add, add_sub_cancel, hg x]
  let γ : ℝ → ℂ := fun t => f (((t * T : ℝ) : AddCircle T))
  let δ : ℝ → ℂ := fun t => f 0 * Complex.exp (2 * Real.pi * Complex.I * k * t)
  have hδ_fourier (t : ℝ) : f 0 * fourier k (((t * T : ℝ) : AddCircle T)) = δ t := by
    rw [fourier_coe_apply]
    simp only [δ, Complex.ofReal_mul]
    congr 2
    field_simp
  let p : Path (f 0) (f 0) :=
    { toFun t := f ((((t : ℝ) * T : ℝ) : AddCircle T))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [AddCircle.coe_period] }
  let q : Path (f 0) (f 0) :=
    { toFun t := f 0 * fourier k ((((t : ℝ) * T : ℝ) : AddCircle T))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [AddCircle.coe_period] }
  -- Fixed-endpoint homotopy in `ℂ \ {0}` damping the oscillatory factor `g x - g 0`.
  let φ : p.Homotopy q :=
    { toFun st := f 0 * fourier k ((((st.2 : ℝ) * T : ℝ) : AddCircle T)) *
        Complex.exp (((1 - (st.1 : ℝ)) : ℂ) * (g ((((st.2 : ℝ) * T : ℝ) : AddCircle T)) - g 0))
      continuous_toFun := by fun_prop
      map_zero_left t := by
        simpa [p] using (hfg ((((t : ℝ) * T : ℝ) : AddCircle T))).symm
      map_one_left t := by simp [q]
      prop' s t ht := by
        rcases ht with rfl | rfl
        · simp [p]
        · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, one_mul, AddCircle.coe_period T]
          simp [p, AddCircle.coe_period T] }
  have hp_eq : EqOn γ p.extend (uIcc 0 1) := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact (p.extend_extends' ⟨t, ht⟩).symm
  have hq_eq : EqOn δ q.extend (uIcc 0 1) := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact (hδ_fourier t).symm.trans (q.extend_extends' ⟨t, ht⟩).symm
  have hpC1 : TauCeti.IsPiecewiseC1On p.extend 0 1 := isPiecewiseC1On_congr hC1 hp_eq
  have hδ_contDiff : ContDiff ℝ 1 δ :=
    contDiff_const.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have hqC1 : TauCeti.IsPiecewiseC1On q.extend 0 1 :=
    isPiecewiseC1On_congr (TauCeti.IsPiecewiseC1On.of_contDiffOn hδ_contDiff.contDiffOn) hq_eq
  have havoid (st : I × I) : φ st ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hf 0) (fourier_ne_zero _ _)) (Complex.exp_ne_zero _)
  have hhom := TauCeti.Contour.windingNumber_eq_of_pathHomotopy φ hpC1 hqC1 havoid
  have hp_wind : TauCeti.Contour.windingNumber γ 0 1 0 =
      TauCeti.Contour.windingNumber p.extend 0 1 0 :=
    TauCeti.Contour.windingNumber_congr_curve (hp_eq.mono uIoo_subset_uIcc_self)
  have hq_wind : TauCeti.Contour.windingNumber δ 0 1 0 =
      TauCeti.Contour.windingNumber q.extend 0 1 0 :=
    TauCeti.Contour.windingNumber_congr_curve (hq_eq.mono uIoo_subset_uIcc_self)
  rw [hp_wind, hhom, ← hq_wind]
  exact (contour_windingNumber_const_mul_exp (f 0) (hf 0) k).symm

/-- **Equality of topological and contour winding numbers on `UnitAddCircle`.** For a nowhere-zero
continuous symbol `f : C(UnitAddCircle, ℂ)` whose pullback `t ↦ f (t : UnitAddCircle)` is piecewise
`C¹` on `[0, 1]`, `(f.windingNumber hf : ℂ)` equals the contour winding integral
`TauCeti.Contour.windingNumber (fun t : ℝ => f (t : UnitAddCircle)) 0 1 0`. -/
theorem coe_windingNumber_eq_contour_windingNumber (f : C(UnitAddCircle, ℂ))
    (hf : ∀ x, f x ≠ 0)
    (hC1 : TauCeti.IsPiecewiseC1On (fun t : ℝ => f (t : UnitAddCircle)) 0 1) :
    (f.windingNumber hf : ℂ) =
      TauCeti.Contour.windingNumber (fun t : ℝ => f (t : UnitAddCircle)) 0 1 0 := by
  simpa only [mul_one] using
    f.coe_windingNumber_eq_contour_windingNumber_mul hf (by simpa only [mul_one] using hC1)

end ContourComparison

section ZeroPerturbation

variable {T : ℝ}

/-- Every trigonometric polynomial on `AddCircle T` has the form
`x ↦ fourier (-N) x * P(fourier 1 x)` for some `N : ℕ` and `P : Polynomial ℂ`. -/
private theorem exists_polynomial_of_mem_span_fourier
    {q : C(AddCircle T, ℂ)} (hq : q ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    ∃ (N : ℕ) (P : Polynomial ℂ), ∀ x, q x = fourier (-N) x * P.eval (fourier 1 x) := by
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hq
  obtain ⟨c, rfl⟩ := hq
  let N : ℕ := c.support.sup fun k => (-k).toNat
  let P : Polynomial ℂ := ∑ k ∈ c.support, Polynomial.C (c k) * Polynomial.X ^ (k + N).toNat
  have heval (z : ℂ) : P.eval z = ∑ k ∈ c.support, c k * z ^ (k + N).toNat := by
    dsimp only [P]
    induction c.support using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  refine ⟨N, P, fun x => ?_⟩
  rw [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, heval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  have hkN : 0 ≤ k + (N : ℤ) := by
    have hle : (-k).toNat ≤ N := Finset.le_sup (f := fun k : ℤ => (-k).toNat) hk
    omega
  have hpow' (m : ℕ) : (fourier (T := T) 1 x) ^ m = fourier (m : ℤ) x := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]
  rw [hpow', Int.toNat_of_nonneg hkN, mul_left_comm (fourier (T := T) (-↑N) x), ← fourier_add]
  have hsub : -(N : ℤ) + (k + N) = k := by omega
  rw [hsub]

/-- On the unit circle, `z ↦ z - w` has winding number `1` when `‖w‖ < 1`. -/
private theorem windingNumber_fourier_one_sub_const_of_norm_lt_one [Fact (0 < T)]
    {w : ℂ} (hw : ‖w‖ < 1) :
    (fourier (T := T) 1 - ContinuousMap.const (AddCircle T) w).windingNumber
      (fun x hx => by
        have h : ‖fourier (T := T) 1 x‖ = ‖w‖ := congrArg norm (sub_eq_zero.mp hx)
        rw [norm_fourier_apply] at h
        exact hw.ne h.symm) = 1 := by
  have hlt (x : AddCircle T) :
      ‖(fourier (T := T) 1 - ContinuousMap.const (AddCircle T) w) x - fourier 1 x‖ <
        ‖fourier (T := T) 1 x‖ := by
    simpa [norm_fourier_apply] using hw
  rw [windingNumber_eq_of_norm_sub_lt (fourier_ne_zero 1) hlt, windingNumber_fourier]

/-- On the unit circle, `z ↦ z - w` has winding number `0` when `1 < ‖w‖`. -/
private theorem windingNumber_fourier_one_sub_const_of_one_lt_norm
    {w : ℂ} (hw : 1 < ‖w‖) :
    (fourier (T := T) 1 - ContinuousMap.const (AddCircle T) w).windingNumber
      (fun x hx => by
        have h : ‖fourier (T := T) 1 x‖ = ‖w‖ := congrArg norm (sub_eq_zero.mp hx)
        rw [norm_fourier_apply] at h
        exact hw.ne h) = 0 := by
  have hw0 : -w ≠ 0 := neg_ne_zero.mpr (norm_pos_iff.mp (zero_lt_one.trans hw))
  have hlt (x : AddCircle T) :
      ‖(fourier (T := T) 1 - ContinuousMap.const (AddCircle T) w) x -
          ContinuousMap.const (AddCircle T) (-w) x‖ <
        ‖ContinuousMap.const (AddCircle T) (-w) x‖ := by
    simpa [sub_neg_eq_add, add_sub_cancel_right, norm_fourier_apply] using hw
  rw [windingNumber_eq_of_norm_sub_lt (fun _ => hw0) hlt, windingNumber_const hw0]

/-- **Instability of winding at a zero.** Every continuous function `f : C(AddCircle T, ℂ)` that
vanishes at some point `x₀` can be uniformly approximated within any `ε > 0` by two nowhere-zero
continuous functions of distinct winding numbers. -/
theorem exists_norm_sub_lt_windingNumber_ne [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    {x₀ : AddCircle T} (hx₀ : f x₀ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g₁ g₂ : C(AddCircle T, ℂ)) (hg₁ : ∀ x, g₁ x ≠ 0) (hg₂ : ∀ x, g₂ x ≠ 0),
      ‖g₁ - f‖ < ε ∧ ‖g₂ - f‖ < ε ∧ g₁.windingNumber hg₁ ≠ g₂.windingNumber hg₂ := by
  -- Approximate `f` within `ε / 3` by a trigonometric polynomial `p`, then shift so `q x₀ = 0`.
  have hdense : Dense (Submodule.span ℂ (Set.range (fourier (T := T))) : Set C(AddCircle T, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  obtain ⟨p, hp_dist, hp_mem⟩ := Metric.dense_iff.mp hdense f (ε / 3) (by positivity)
  rw [Metric.mem_ball, dist_eq_norm] at hp_dist
  have hpx₀ : ‖p x₀‖ < ε / 3 := by
    calc
      ‖p x₀‖ = ‖(p - f) x₀‖ := by simp [hx₀]
      _ ≤ ‖p - f‖ := ContinuousMap.norm_coe_le_norm (p - f) x₀
      _ < ε / 3 := hp_dist
  let q : C(AddCircle T, ℂ) := p - p x₀ • fourier 0
  have hq_mem : q ∈ Submodule.span ℂ (Set.range (fourier (T := T))) :=
    Submodule.sub_mem _ hp_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  have hqx₀ : q x₀ = 0 := by simp [q]
  have hq_norm : ‖q - f‖ < 2 * ε / 3 := by
    have hconst_norm : ‖(p x₀ • fourier (T := T) 0 : C(AddCircle T, ℂ))‖ ≤ ‖p x₀‖ := by
      rw [ContinuousMap.norm_le _ (norm_nonneg _)]
      intro x
      simp
    calc
      ‖q - f‖ = ‖(p - f) - p x₀ • fourier 0‖ := by
        congr 1
        ext x
        simp [q]
        ring
      _ ≤ ‖p - f‖ + ‖(p x₀ • fourier (T := T) 0 : C(AddCircle T, ℂ))‖ := norm_sub_le _ _
      _ < ε / 3 + ε / 3 := add_lt_add hp_dist (hconst_norm.trans_lt hpx₀)
      _ = 2 * ε / 3 := by ring
  obtain ⟨N, P, hP⟩ := exists_polynomial_of_mem_span_fourier hq_mem
  by_cases hP0 : P = 0
  · -- Degenerate case `q = 0`: `‖f‖ < 2ε/3`, so small multiples of `e_1` and `e_0` suffice.
    have hf_norm : ‖f‖ < 2 * ε / 3 := by
      have hq0 : q = 0 := by ext x; simp [hP x, hP0]
      simpa [hq0] using hq_norm
    let c : ℂ := ((ε / 4 : ℝ) : ℂ)
    have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hc_norm : ‖c‖ = ε / 4 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    let g₁ : C(AddCircle T, ℂ) := c • fourier 1
    let g₂ : C(AddCircle T, ℂ) := c • fourier 0
    have hbound (k : ℤ) : ‖(c • fourier (T := T) k) - f‖ < ε := by
      have hck : ‖(c • fourier (T := T) k : C(AddCircle T, ℂ))‖ ≤ ε / 4 := by
        rw [ContinuousMap.norm_le _ (by positivity)]
        intro x
        simp [hc_norm]
      calc
        ‖(c • fourier (T := T) k) - f‖ ≤ ‖c • fourier (T := T) k‖ + ‖f‖ := norm_sub_le _ _
        _ < ε / 4 + 2 * ε / 3 := add_lt_add_of_le_of_lt hck hf_norm
        _ < ε := by linarith
    refine ⟨g₁, g₂, fun x => mul_ne_zero hc (fourier_ne_zero 1 x),
      fun x => mul_ne_zero hc (fourier_ne_zero 0 x), hbound 1, hbound 0, ?_⟩
    simp [g₁, g₂, windingNumber_smul hc]
  · -- Nonzero polynomial `P`: split off the unit-circle root `z₀ = fourier 1 x₀`.
    set z₀ : ℂ := fourier 1 x₀
    have hz₀_norm : ‖z₀‖ = 1 := norm_fourier_apply 1 x₀
    have hz₀_eval : P.eval z₀ = 0 := by
      have h0 := (hP x₀).symm.trans hqx₀
      exact (mul_eq_zero.mp h0).resolve_left (fourier_ne_zero (-N) x₀)
    have hz₀_mem : z₀ ∈ P.roots := (Polynomial.mem_roots hP0).mpr hz₀_eval
    set M : Multiset ℂ := P.roots.erase z₀
    have hroots : P.roots = z₀ ::ₘ M := (Multiset.cons_erase hz₀_mem).symm
    have hsplit (z : ℂ) :
        P.eval z = P.leadingCoeff * ((z - z₀) * (M.map fun r => z - r).prod) := by
      rw [(IsAlgClosed.splits P).eval_eq_prod_roots, hroots, Multiset.map_cons, Multiset.prod_cons]
    -- Push remaining unit-circle roots slightly inside the circle, and push `z₀` in vs out.
    let ρ : ℝ → ℂ → ℂ := fun δ r => if ‖r‖ = 1 then ((1 - δ : ℝ) : ℂ) * r else r
    let factor : ℝ → ℂ → C(AddCircle T, ℂ) :=
      fun δ r => fourier 1 - ContinuousMap.const (AddCircle T) (ρ δ r)
    let R : ℝ → C(AddCircle T, ℂ) := fun δ =>
      ContinuousMap.const (AddCircle T) P.leadingCoeff * fourier (-N) *
        (M.map (factor δ)).prod
    let G₁ : ℝ → C(AddCircle T, ℂ) := fun δ =>
      (fourier 1 - ContinuousMap.const (AddCircle T) (((1 - δ : ℝ) : ℂ) * z₀)) * R δ
    let G₂ : ℝ → C(AddCircle T, ℂ) := fun δ =>
      (fourier 1 - ContinuousMap.const (AddCircle T) (((1 + δ : ℝ) : ℂ) * z₀)) * R δ
    have hconst_cont : Continuous (ContinuousMap.const (AddCircle T) : ℂ → C(AddCircle T, ℂ)) :=
      Metric.continuous_iff.mpr fun z η hη => ⟨η, hη, fun w hw => by
        rw [dist_eq_norm] at hw ⊢
        exact lt_of_le_of_lt ((ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun _ => le_rfl) hw⟩
    have hfactor_cont (r : ℂ) : Continuous fun δ : ℝ => factor δ r := by
      have hρ_cont : Continuous fun δ : ℝ => ρ δ r := by
        simp only [ρ]
        split_ifs <;> fun_prop
      exact continuous_const.sub (hconst_cont.comp hρ_cont)
    have hM_cont (S : Multiset ℂ) : Continuous fun δ : ℝ => (S.map (factor δ)).prod := by
      induction S using Multiset.induction_on with
      | empty => simpa using continuous_const
      | cons r S ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        exact (hfactor_cont r).mul ih
    have hR_cont : Continuous R := continuous_const.mul (hM_cont M)
    have hG₁_cont : Continuous G₁ :=
      (continuous_const.sub (hconst_cont.comp (by fun_prop))).mul hR_cont
    have hG₂_cont : Continuous G₂ :=
      (continuous_const.sub (hconst_cont.comp (by fun_prop))).mul hR_cont
    have hq_eq_G0 : G₁ 0 = q ∧ G₂ 0 = q := by
      have hρ0 (r : ℂ) : ρ 0 r = r := by simp [ρ]
      have hprod (S : Multiset ℂ) (x : AddCircle T) :
          ((S.map (factor 0)).prod) x = (S.map fun r => fourier 1 x - r).prod := by
        induction S using Multiset.induction_on with
        | empty => simp
        | cons r S ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, ContinuousMap.mul_apply, ih]
          simp [factor, hρ0]
      have hval (x : AddCircle T) :
          (fourier 1 x - z₀) * (R 0 x) = q x := by
        simp only [R, ContinuousMap.mul_apply, ContinuousMap.const_apply, hprod M x]
        rw [hP x, hsplit (fourier 1 x)]
        ring
      exact ⟨by ext x; simpa [G₁] using hval x, by ext x; simpa [G₂] using hval x⟩
    -- Continuity at `δ = 0` yields `δ ∈ (0, 1)` with both `G₁ δ` and `G₂ δ` within `ε / 3` of `q`.
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
      Metric.continuousAt_iff.mp (hG₁_cont.continuousAt (x := 0)) (ε / 3) (by positivity)
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
      Metric.continuousAt_iff.mp (hG₂_cont.continuousAt (x := 0)) (ε / 3) (by positivity)
    let δ : ℝ := min (1 / 2) (min (δ₁ / 2) (δ₂ / 2))
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hδ_dist : dist δ 0 = δ := by simp [abs_of_pos hδ0]
    have hG₁_close : ‖G₁ δ - q‖ < ε / 3 := by
      have hlt : dist δ 0 < δ₁ := by
        rw [hδ_dist]
        exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hδ₁_pos)
      simpa [hq_eq_G0.1, dist_eq_norm] using hδ₁ hlt
    have hG₂_close : ‖G₂ δ - q‖ < ε / 3 := by
      have hlt : dist δ 0 < δ₂ := by
        rw [hδ_dist]
        exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hδ₂_pos)
      simpa [hq_eq_G0.2, dist_eq_norm] using hδ₂ hlt
    -- Verify nowhere-vanishing and distinct winding numbers at this `δ ∈ (0, 1)`.
    have hfactor_ne (r : ℂ) (x : AddCircle T) : factor δ r x ≠ 0 := by
      intro hzero
      have hnorm_eq : 1 = ‖ρ δ r‖ := by
        simpa [norm_fourier_apply] using congrArg norm (sub_eq_zero.mp hzero)
      simp only [ρ] at hnorm_eq
      split_ifs at hnorm_eq with hr
      · rw [norm_mul, hr, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (sub_pos.mpr hδ1)] at hnorm_eq
        linarith
      · exact hr hnorm_eq.symm
    have hM_ne (S : Multiset ℂ) (x : AddCircle T) : ((S.map (factor δ)).prod) x ≠ 0 := by
      induction S using Multiset.induction_on with
      | empty => simp
      | cons r S ih => simpa [Multiset.prod_cons] using mul_ne_zero (hfactor_ne r x) ih
    have hR_ne (x : AddCircle T) : R δ x ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP0)
        (fourier_ne_zero (-N) x)) (hM_ne M x)
    have hw₁ : ‖((1 - δ : ℝ) : ℂ) * z₀‖ < 1 := by
      rw [norm_mul, hz₀_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr hδ1)]
      linarith
    have hw₂ : 1 < ‖((1 + δ : ℝ) : ℂ) * z₀‖ := by
      rw [norm_mul, hz₀_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have hf₁_ne (x : AddCircle T) :
        (fourier (T := T) 1 - ContinuousMap.const (AddCircle T) (((1 - δ : ℝ) : ℂ) * z₀)) x ≠ 0 :=
      fun hx => hw₁.ne <| by
        simpa [norm_fourier_apply] using (congrArg norm (sub_eq_zero.mp hx)).symm
    have hf₂_ne (x : AddCircle T) :
        (fourier (T := T) 1 - ContinuousMap.const (AddCircle T) (((1 + δ : ℝ) : ℂ) * z₀)) x ≠ 0 :=
      fun hx => hw₂.ne <| by
        simpa [norm_fourier_apply] using congrArg norm (sub_eq_zero.mp hx)
    have hG₁_ne (x : AddCircle T) : G₁ δ x ≠ 0 := mul_ne_zero (hf₁_ne x) (hR_ne x)
    have hG₂_ne (x : AddCircle T) : G₂ δ x ≠ 0 := mul_ne_zero (hf₂_ne x) (hR_ne x)
    have hwind_ne : (G₁ δ).windingNumber hG₁_ne ≠ (G₂ δ).windingNumber hG₂_ne := by
      rw [windingNumber_mul _ _ hf₁_ne hR_ne, windingNumber_mul _ _ hf₂_ne hR_ne,
        windingNumber_fourier_one_sub_const_of_norm_lt_one hw₁,
        windingNumber_fourier_one_sub_const_of_one_lt_norm hw₂]
      omega
    have hG₁_f : ‖G₁ δ - f‖ < ε := by
      calc
        ‖G₁ δ - f‖ = ‖(G₁ δ - q) + (q - f)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖G₁ δ - q‖ + ‖q - f‖ := norm_add_le _ _
        _ < ε / 3 + 2 * ε / 3 := add_lt_add hG₁_close hq_norm
        _ = ε := by ring
    have hG₂_f : ‖G₂ δ - f‖ < ε := by
      calc
        ‖G₂ δ - f‖ = ‖(G₂ δ - q) + (q - f)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖G₂ δ - q‖ + ‖q - f‖ := norm_add_le _ _
        _ < ε / 3 + 2 * ε / 3 := add_lt_add hG₂_close hq_norm
        _ = ε := by ring
    exact ⟨G₁ δ, G₂ δ, hG₁_ne, hG₂_ne, hG₁_f, hG₂_f, hwind_ne⟩

end ZeroPerturbation

end ContinuousMap

end
