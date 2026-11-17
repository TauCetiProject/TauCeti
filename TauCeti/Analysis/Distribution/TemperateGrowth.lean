/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Determinant
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Topology.Order.IntermediateValue

/-!
# Derivatives of functions of temperate growth

A smooth function whose iterated derivatives are all bounded has temperate growth. Typical examples
are smooth functions which outside a ball agree with a homogeneous function of degree at most `0`.
So does a smooth function satisfying symbol estimates
`‖D^k f(x)‖ ≤ C_k (1 + ‖x‖ ^ 2) ^ ((m - k) / 2)` of some real order `m`, and the rescaled
Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r`. On a real inner product space, so does the
logarithm `x ↦ log (1 + ‖x‖ ^ 2)` of the squared Japanese bracket, which enters the complex powers
of the Japanese bracket.

The derivative `Df` of a function `f` of temperate growth has temperate growth, since the iterated
derivatives of `Df` are those of `f` shifted by one order. So does each directional derivative
`x ↦ Df(x) v`. These are the coefficients that appear when the Leibniz rule is applied to the
product of a Schwartz function or a tempered distribution with `f`.

On a finite-dimensional space the determinant is a polynomial in the matrix entries, so it has
temperate growth, and so does the Jacobian determinant `x ↦ det Df(x)`. The absolute value of a
real function of temperate growth without zeros has temperate growth: on the connected space `E`
the function has constant sign. These give the Jacobian factor `|det Dφ⁻¹|` of a change of
variables `φ` of Schwartz functions.

When the derivatives of positive order of a map `g : E → E` are bounded, so are all derivatives of
the coefficients `x ↦ ⟪w, Dg(x) v⟫` of the chain rule, and when those of `φ⁻¹` are bounded, so are
all derivatives of the Jacobian factor `|det Dφ⁻¹|`. These are the inputs of the Sobolev estimates
for changes of variables in `TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables`.

If `g ∘ f = id` and `g` has temperate growth, then `‖x‖` is
bounded by a polynomial in `‖f x‖`, the growth condition of Mathlib's `SchwartzMap.compCLM`.

A measure of temperate growth is finite on compact sets.

## Main results

* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le`: bounded derivatives give temperate
  growth.
* `Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow`: symbol estimates
  give temperate growth.
* `Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow`: the rescaled Bessel potential has
  temperate growth.
* `Function.hasTemperateGrowth_log_one_add_norm_sq`: `x ↦ log (1 + ‖x‖ ^ 2)` has temperate growth.
* `Function.hasTemperateGrowth_norm_sub_pow`: `y ↦ ‖x - y‖ ^ (2N)` has temperate growth.
* `Function.HasTemperateGrowth.fderiv`: `Df` has temperate growth.
* `Function.HasTemperateGrowth.fderiv_apply`: `x ↦ Df(x) v` has temperate growth.
* `Function.HasTemperateGrowth.prod`: finite products of functions of temperate growth.
* `ContinuousLinearMap.hasTemperateGrowth_det`, `Function.HasTemperateGrowth.det_fderiv`: the
  determinant and the Jacobian determinant have temperate growth.
* `Function.HasTemperateGrowth.abs`: `|f|` has temperate growth if `f` has no zeros.
* `Function.HasTemperateGrowth.abs_det_fderiv_symm`: the Jacobian factor `|det Dφ⁻¹|` of a
  bijection `φ` such that `φ` and `φ⁻¹` have temperate growth.
* `Function.HasTemperateGrowth.inner_fderiv_apply`,
  `Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_inner_fderiv_apply_le`: the chain-rule
  coefficient `x ↦ ⟪w, Dg(x) v⟫` has temperate growth, and a bounded derivative of order `n` when
  that of `g` of order `n + 1` is bounded.
* `Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le`: the Jacobian
  factor `|det Dφ⁻¹|` has a bounded derivative of order `n` when those of `φ⁻¹` of orders `1` to
  `n + 1` are bounded.
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
theorem prod {ι R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R] {f : ι → E → R}
    (s : Finset ι) (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
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
  obtain ⟨ε, hε⟩ := isPreconnected_univ.exists_abs_eq_mul hf.1.continuous.continuousOn
    fun x _ ↦ h0 x
  simpa only [hε _ (Set.mem_univ _)] using (HasTemperateGrowth.const ε).fun_mul hf

end Function.HasTemperateGrowth

/-- On a finite-dimensional space the determinant has temperate growth, being a polynomial in the
matrix entries. -/
theorem ContinuousLinearMap.hasTemperateGrowth_det {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (fun A : E →L[ℝ] E ↦ A.det).HasTemperateGrowth := by
  let b := Module.finBasis ℝ E
  have h : (fun A : E →L[ℝ] E ↦ A.det) = fun A ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      (Equiv.Perm.sign σ : ℝ) * ∏ i, b.coord (σ i) (A (b i)) := by
    funext A
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [LinearMap.toMatrix_apply, Units.smul_def]
  have hprod (σ : Equiv.Perm (Fin (Module.finrank ℝ E))) :
      (fun A : E →L[ℝ] E ↦ ∏ i, b.coord (σ i) (A (b i))).HasTemperateGrowth :=
    Function.HasTemperateGrowth.prod _ fun i _ ↦ ((b.coord (σ i)).toContinuousLinearMap.comp
      (ContinuousLinearMap.apply ℝ E (b i) : (E →L[ℝ] E) →L[ℝ] E)).hasTemperateGrowth
  rw [h]
  exact Function.HasTemperateGrowth.sum fun σ _ ↦
    (Function.HasTemperateGrowth.const _).fun_mul (hprod σ)

/-- The Jacobian determinant `x ↦ det Df(x)` of a function of temperate growth on a
finite-dimensional space has temperate growth. -/
theorem Function.HasTemperateGrowth.det_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} (hf : f.HasTemperateGrowth) :
    (fun x ↦ (_root_.fderiv ℝ f x).det).HasTemperateGrowth :=
  ContinuousLinearMap.hasTemperateGrowth_det.comp hf.fderiv

/-- For a bijection `φ` of a finite-dimensional space such that `φ` and `φ⁻¹` have temperate
growth, the Jacobian factor `y ↦ |det Dφ⁻¹(y)|` of the change of variables has temperate growth:
`det Dφ⁻¹(y)` has no zeros, being the reciprocal of `det Dφ(φ⁻¹ y)`. -/
theorem Function.HasTemperateGrowth.abs_det_fderiv_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) :
    (fun y ↦ |(_root_.fderiv ℝ φ.symm y).det|).HasTemperateGrowth :=
  hψ.det_fderiv.abs fun y ↦ φ.det_fderiv_symm_ne_zero (hφ.1.differentiable (by simp) _)
    (hψ.1.differentiable (by simp) y)

section InnerProduct

open scoped RealInnerProductSpace

namespace Function.HasTemperateGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : E → E}

/-- The coefficient `x ↦ ⟪w, Dg(x) v⟫` of the chain rule, as a complex function, is the
composition of `Dg` with a continuous linear functional. -/
private theorem ofReal_inner_fderiv_apply_eq (v w : E) :
    (fun x ↦ ((⟪w, _root_.fderiv ℝ g x v⟫ : ℝ) : ℂ)) =
      ((Complex.ofRealCLM.comp (innerSL ℝ w)).comp (ContinuousLinearMap.apply ℝ E v)) ∘
        _root_.fderiv ℝ g := by
  funext x
  simp

/-- The coefficient `x ↦ ⟪w, Dg(x) v⟫` of the chain rule has temperate growth. -/
theorem inner_fderiv_apply (hg : g.HasTemperateGrowth) (v w : E) :
    (fun x ↦ ((⟪w, _root_.fderiv ℝ g x v⟫ : ℝ) : ℂ)).HasTemperateGrowth := by
  rw [ofReal_inner_fderiv_apply_eq]
  exact (ContinuousLinearMap.hasTemperateGrowth _).comp hg.fderiv

/-- If the derivative of `g` of order `n + 1` is bounded, then so is the derivative of order `n` of
the chain-rule coefficient `x ↦ ⟪w, Dg(x) v⟫`. -/
theorem exists_norm_iteratedFDeriv_inner_fderiv_apply_le (hg : g.HasTemperateGrowth) (v w : E)
    {n : ℕ} (hb : ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ C) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ ((⟪w, _root_.fderiv ℝ g x v⟫ : ℝ) : ℂ)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  set L := (Complex.ofRealCLM.comp (innerSL ℝ w)).comp (ContinuousLinearMap.apply ℝ E v)
  refine ⟨‖L‖ * C, fun x ↦ ?_⟩
  rw [ofReal_inner_fderiv_apply_eq]
  refine (L.norm_iteratedFDeriv_comp_left hg.fderiv.1.contDiffAt (by simp)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

/-- If `φ` and `φ⁻¹` have temperate growth and the derivatives of `φ⁻¹` of orders `1` to `n + 1`
are bounded, then the derivative of order `n` of the Jacobian factor `|det Dφ⁻¹|` is bounded. -/
theorem exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le [FiniteDimensional ℝ E] {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth) (n : ℕ)
    (hb : ∀ m ≤ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (m + 1) φ.symm x‖ ≤ C) :
    ∃ C, ∀ y, ‖iteratedFDeriv ℝ n
      (fun y ↦ ((|(_root_.fderiv ℝ φ.symm y).det| : ℝ) : ℂ)) y‖ ≤ C := by
  -- The determinant of the bounded smooth map `Dφ⁻¹` has bounded derivatives.
  obtain ⟨C, hC⟩ := (ContinuousLinearMap.hasTemperateGrowth_det.1.of_le
    (by exact_mod_cast le_top)).exists_norm_iteratedFDeriv_comp_le
      (hψ.fderiv.1.of_le (by exact_mod_cast le_top))
      fun m hm ↦ (hb m hm).imp fun C hC x ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hC x
  -- `det Dφ⁻¹` has no zeros on the connected space `E`, hence a constant sign `ε`.
  have hcont : Continuous fun y ↦ (_root_.fderiv ℝ φ.symm y).det := hψ.det_fderiv.1.continuous
  obtain ⟨ε, hε⟩ := isPreconnected_univ.exists_abs_eq_mul hcont.continuousOn fun y _ ↦
    φ.det_fderiv_symm_ne_zero (hφ.1.differentiable (by simp) _) (hψ.1.differentiable (by simp) y)
  have hJ : (fun y ↦ ((|(_root_.fderiv ℝ φ.symm y).det| : ℝ) : ℂ)) =
      (ε • Complex.ofRealCLM) ∘ ((fun A : E →L[ℝ] E ↦ A.det) ∘ _root_.fderiv ℝ φ.symm) := by
    funext y
    simp only [Function.comp_apply, _root_.smul_apply, Complex.ofRealCLM_apply,
      Complex.real_smul, hε y (Set.mem_univ y), Complex.ofReal_mul]
  refine ⟨‖ε • Complex.ofRealCLM‖ * C, fun y ↦ ?_⟩
  rw [hJ]
  exact ((ε • Complex.ofRealCLM).norm_iteratedFDeriv_comp_left
    ((ContinuousLinearMap.hasTemperateGrowth_det.1.comp hψ.fderiv.1).contDiffAt) (by simp)).trans
    (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _))

end Function.HasTemperateGrowth

end InnerProduct

namespace Function

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The rescaled Bessel potential `x ↦ (1 + ‖c • x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_one_add_norm_smul_sq_rpow (c r : ℝ) :
    (fun x : H ↦ (1 + ‖c • x‖ ^ 2) ^ r).HasTemperateGrowth :=
  (hasTemperateGrowth_one_add_norm_sq_rpow H r).comp (by fun_prop)

/-- On a real inner product space `H`, the logarithm `x ↦ log (1 + ‖x‖ ^ 2)` of the squared
Japanese bracket has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_log_one_add_norm_sq :
    (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2)).HasTemperateGrowth := by
  -- The function is bounded by `‖x‖ ^ 2`, and its derivative `(1 + ‖x‖ ^ 2)⁻¹ D‖x‖ ^ 2` has
  -- temperate growth.
  have hderiv (x : H) : HasFDerivAt (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2))
      ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ) • fderiv ℝ (fun x : H ↦ ‖x‖ ^ 2) x) x := by
    have h := (((contDiff_norm_sq ℝ (E := H) (n := 1)).differentiable one_ne_zero).differentiableAt
      (x := x)).hasFDerivAt.const_add 1
    rw [Real.rpow_neg_one]
    exact h.log (ne_of_gt (by positivity))
  have hfd : fderiv ℝ (fun x : H ↦ Real.log (1 + ‖x‖ ^ 2)) =
      (fun x : H ↦ (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) • fderiv ℝ (fun x : H ↦ ‖x‖ ^ 2) :=
    funext fun x ↦ (hderiv x).fderiv
  refine HasTemperateGrowth.of_fderiv (k := 2) (C := 1) ?_
    (fun x ↦ (hderiv x).differentiableAt) fun x ↦ ?_
  · rw [hfd]
    exact (hasTemperateGrowth_one_add_norm_sq_rpow H (-1)).smul
      (hasTemperateGrowth_norm_sq H).fderiv
  · have hle : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    rw [Real.norm_of_nonneg (Real.log_nonneg hle), one_mul]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ‖x‖ ^ 2)
    nlinarith [norm_nonneg x]

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
