/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Derivatives of functions of temperate growth

A smooth function whose iterated derivatives are all bounded has temperate growth. Typical examples
are smooth functions which outside a ball agree with a homogeneous function of degree at most `0`.
So does a smooth function satisfying symbol estimates
`‖D^k f(x)‖ ≤ C_k (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)` of some real order `m`, and the rescaled
Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r`.

The derivative `Df` of a function `f` of temperate growth has temperate growth, since the iterated
derivatives of `Df` are those of `f` shifted by one order. So does each directional derivative
`x ↦ Df(x) v`. These are the coefficients that appear when the Leibniz rule is applied to the
product of a Schwartz function or a tempered distribution with `f`.

The determinant has temperate growth: on a finite-dimensional space it is a polynomial in the
matrix entries, and otherwise it is the constant `1`. So does the Jacobian determinant
`x ↦ det Df(x)`. The absolute value of a
real function of temperate growth without zeros has temperate growth: on the connected space `E`
the function has constant sign. These give the Jacobian factor `|det Dφ⁻¹|` of a change of
variables `φ` of Schwartz functions. If `g ∘ f = id` and `g` has temperate growth, then `‖x‖` is
bounded by a polynomial in `‖f x‖`, the growth condition of Mathlib's `SchwartzMap.compCLM`.

A measure of temperate growth is finite on compact sets.

## Main results

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: bounded derivatives give temperate
  growth.
* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow`: symbol estimates
  give temperate growth.
* `Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow`: the rescaled Bessel potential has
  temperate growth.
* `Function.hasTemperateGrowth_norm_sub_pow`: `y ↦ ‖x - y‖ ^ (2N)` has temperate growth.
* `Function.HasTemperateGrowth.fderiv`: `Df` has temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: `x ↦ Df(x) v` has temperate growth.
* `Function.HasTemperateGrowth.prod`: finite products of functions of temperate growth.
* `ContinuousLinearMap.hasTemperateGrowth_det`, `Function.HasTemperateGrowth.det_fderiv`: the
  determinant and the Jacobian determinant have temperate growth.
* `Function.HasTemperateGrowth.abs`: `|f|` has temperate growth if `f` has no zeros.
* `Function.HasTemperateGrowth.abs_det_fderiv_symm`: the Jacobian factor `|det Dφ⁻¹|` of a
  bijection `φ` such that `φ` and `φ⁻¹` have temperate growth.
* `Function.HasTemperateGrowth.exists_norm_le_of_leftInverse`: a polynomial lower bound for
  `‖f x‖` from a left inverse of temperate growth.
* `MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts`: a measure of temperate
  growth is finite on compact sets.
-/

public section

open scoped ContDiff

namespace Function.HasTemperateGrowth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F}

/-- A smooth function all of whose iterated derivatives are bounded has temperate growth. -/
theorem of_norm_iteratedFDeriv_le (hf : ContDiff ℝ ∞ f)
    (hbd : ∀ n : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) : f.HasTemperateGrowth :=
  ⟨hf, fun n ↦ ⟨0, (hbd n).imp fun C hC x ↦ by simpa using hC x⟩⟩

/-- **Symbol estimates give temperate growth.** A smooth function whose `k`-th derivative is
bounded by `C_k (1 + ‖x‖²) ^ ((m - k) / 2)` for every `k` has temperate growth. -/
theorem of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow {m : ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ k : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)) :
    f.HasTemperateGrowth := by
  refine ⟨hf, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hbound k
  refine ⟨⌈m⌉₊, max C 0, fun x ↦ (hC x).trans ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ ^ 2 := le_add_of_nonneg_right (by positivity)
  have hw : (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖) ^ ⌈m⌉₊ :=
    calc (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ (1 + ‖x‖ ^ 2) ^ ((⌈m⌉₊ : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by
            have := Nat.le_ceil m
            have : (0 : ℝ) ≤ k := k.cast_nonneg
            linarith)
      _ ≤ (1 + ‖x‖) ^ (⌈m⌉₊ : ℝ) :=
          TauCeti.one_add_norm_sq_rpow_half_le_one_add_norm_rpow x (Nat.cast_nonneg _)
      _ = (1 + ‖x‖) ^ ⌈m⌉₊ := Real.rpow_natCast _ _
  calc C * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) ≤ max C 0 * (1 + ‖x‖ ^ 2) ^ ((m - k) / 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + ‖x‖) ^ ⌈m⌉₊ := mul_le_mul_of_nonneg_left hw (le_max_right _ _)

/-- The derivative of a function of temperate growth has temperate growth. -/
theorem fderiv (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right le_rfl, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x ↦ by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩

/-- A directional derivative `x ↦ Df(x) v` of a function of temperate growth has temperate
growth. -/
theorem fderiv_apply (hf : f.HasTemperateGrowth) (v : E) :
    (fun x ↦ _root_.fderiv ℝ f x v).HasTemperateGrowth :=
  (ContinuousLinearMap.apply ℝ F v).hasTemperateGrowth.comp hf.fderiv

/-- A finite product of functions of temperate growth has temperate growth. -/
@[fun_prop]
theorem prod {ι R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] {f : ι → E → R}
    {s : Finset ι} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HasTemperateGrowth.const]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (by simp)).mul (ih fun i hi ↦ hf i (by simp [hi]))

/-- If `g ∘ f = id` with `g` of temperate growth, then `‖x‖` is bounded by a polynomial in
`‖f x‖`. -/
theorem exists_norm_le_of_leftInverse {g : F → E} (hg : g.HasTemperateGrowth)
    (h : LeftInverse g f) : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖f x‖) ^ k := by
  obtain ⟨k, C, hC⟩ := hg.2 0
  exact ⟨k, C, fun x ↦ by simpa [h x] using hC (f x)⟩

/-- The absolute value of a real function of temperate growth without zeros has temperate growth:
by the intermediate value theorem the function has constant sign. -/
theorem abs {f : E → ℝ} (hf : f.HasTemperateGrowth) (h0 : ∀ x, f x ≠ 0) :
    (fun x ↦ |f x|).HasTemperateGrowth := by
  rcases (h0 0).lt_or_gt with hneg | hpos
  · have : ∀ x, f x < 0 := fun x ↦ by
      by_contra! hx
      obtain ⟨y, hy⟩ := intermediate_value_univ 0 x hf.1.continuous ⟨hneg.le, hx⟩
      exact h0 y hy
    convert hf.neg using 1
    funext x
    simp [abs_of_neg (this x)]
  · have : ∀ x, 0 < f x := fun x ↦ by
      by_contra! hx
      obtain ⟨y, hy⟩ := intermediate_value_univ x 0 hf.1.continuous ⟨hx, hpos.le⟩
      exact h0 y hy
    simpa [abs_of_pos (this _)] using hf

end Function.HasTemperateGrowth

/-- The determinant has temperate growth: on a finite-dimensional space it is a polynomial in the
matrix entries, and otherwise it is the constant `1`. -/
theorem ContinuousLinearMap.hasTemperateGrowth_det {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : (fun A : E →L[ℝ] E ↦ A.det).HasTemperateGrowth := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · simp [ContinuousLinearMap.det, LinearMap.det_eq_one_of_not_module_finite hE]
  let b := Module.finBasis ℝ E
  have h : (fun A : E →L[ℝ] E ↦ A.det) = fun A ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, b.coord (σ i) (A (b i)) := by
    funext A
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [LinearMap.toMatrix_apply, Units.smul_def]
  have hprod (σ : Equiv.Perm (Fin (Module.finrank ℝ E))) :
      (fun A : E →L[ℝ] E ↦ ∏ i, b.coord (σ i) (A (b i))).HasTemperateGrowth :=
    Function.HasTemperateGrowth.prod fun i _ ↦ ((b.coord (σ i)).toContinuousLinearMap.comp
      (ContinuousLinearMap.apply ℝ E (b i) : (E →L[ℝ] E) →L[ℝ] E)).hasTemperateGrowth
  rw [h]
  exact Function.HasTemperateGrowth.sum fun σ _ ↦
    (Function.HasTemperateGrowth.const _).fun_mul (hprod σ)

/-- The Jacobian determinant `x ↦ det Df(x)` of a function of temperate growth has temperate
growth. -/
theorem Function.HasTemperateGrowth.det_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → E} (hf : f.HasTemperateGrowth) :
    (fun x ↦ (_root_.fderiv ℝ f x).det).HasTemperateGrowth :=
  ContinuousLinearMap.hasTemperateGrowth_det.comp hf.fderiv

/-- For a bijection `φ` such that `φ` and `φ⁻¹` have temperate growth, the Jacobian factor
`y ↦ |det Dφ⁻¹(y)|` of the change of variables has temperate growth: `det Dφ⁻¹(y)` has no zeros,
being the reciprocal of `det Dφ(φ⁻¹ y)`. -/
theorem Function.HasTemperateGrowth.abs_det_fderiv_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) :
    (fun y ↦ |(_root_.fderiv ℝ φ.symm y).det|).HasTemperateGrowth :=
  hψ.det_fderiv.abs fun y h ↦ by
    simpa [h] using φ.det_fderiv_symm_mul_det_fderiv (hφ.1.differentiable (by simp) _)
      (hψ.1.differentiable (by simp) y)

namespace Function

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The rescaled Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_one_add_norm_smul_sq_rpow (c r : ℝ) :
    (fun x : H ↦ (1 + ‖c • x‖ ^ 2) ^ r).HasTemperateGrowth :=
  (hasTemperateGrowth_one_add_norm_sq_rpow H r).comp (by fun_prop)

/-- An even power `y ↦ ‖x - y‖ ^ (2N)` of the distance to a point has temperate growth. -/
theorem hasTemperateGrowth_norm_sub_pow (x : H) (N : ℕ) :
    (fun y : H ↦ ‖x - y‖ ^ (2 * N)).HasTemperateGrowth := by
  have h : (fun y : H ↦ ‖x - y‖ ^ (2 * N)) = ((fun z : H ↦ ‖z‖ ^ 2) ∘ fun y ↦ x - y) ^ N := by
    funext y
    simp [pow_mul]
  rw [h]
  exact ((hasTemperateGrowth_norm_sq H).comp (by fun_prop)).pow N

end Function

open MeasureTheory

/-- A measure of temperate growth is finite on compact sets: `(1 + ‖x‖) ^ (-n)` is integrable and
bounded below by a positive constant on any bounded set. -/
theorem MeasureTheory.Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (μ : Measure E)
    [h : μ.HasTemperateGrowth] : IsFiniteMeasureOnCompacts μ := by
  obtain ⟨n, hn⟩ := h.exists_integrable
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hε : 0 < (1 + max R 0) ^ (-(n : ℝ)) := by positivity
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hn.measure_norm_ge_lt_top hε)
  have hx' : ‖x‖ ≤ max R 0 := by simpa using (hR hx).trans (le_max_left R 0)
  rw [Set.mem_ofPred_eq, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
