/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.ContinuousLinearMapInverse
import TauCeti.Analysis.Complex.Sector.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Strongly parameter-dependent symbols

The resolvent `(A - z)⁻¹` of an elliptic differential operator `A` of order `2` is approximated by
a pseudodifferential operator whose symbol depends on the spectral parameter `z`. Integrating such
a family along a contour around the spectrum gives the complex powers of `A`, so the symbol
estimates have to be uniform in `z`, with `z` counting as two frequency orders: for the Euclidean
Laplacian, the resolvent symbol `(‖ξ‖² - z)⁻¹` is homogeneous of degree `-2` under
`(ξ, z) ↦ (t ξ, t² z)`.

For an open set `Λ ⊆ ℂ` of spectral parameters, `TauCeti.ParameterSymbol n Λ V W m` is the class
of smooth maps `a((x, ξ), z)` on `ℝⁿ × ℝⁿ × Λ` with values in `V →L[ℂ] W` satisfying

`‖∂ₓ^α ∂_ξ^β ∂_z^γ a((x, ξ), z)‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - |β| - 2 |γ|)`

for `x` in a compact set, all `ξ` and all `z ∈ Λ`, the `z`-derivatives being real derivatives.
The estimates are stated as one bound for each `k` on the full `k`-th derivative, taken in the
directions dilated by `TauCeti.parameterDilation` (`TauCeti.parameterIteratedFDeriv`). A closed
sector of spectral parameters, as used for contour integrals, lies in a slightly larger open one.

## Main results

* `TauCeti.parameterWeight_rpow_le_one_add_norm_sq_rpow`,
  `TauCeti.parameterWeight_rpow_le_one_add_sqrt_rpow`,
  `TauCeti.parameterWeight_rpow_le_mul_one_add_norm_sq_rpow`: the weight dominates
  `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)` and `1 + ‖z‖ ^ (1 / 2)`, and at a fixed spectral parameter it is at
  most a multiple of `⟨ξ⟩`;
* `TauCeti.parameterWeight_add_le`, `TauCeti.parameterWeight_rpow_le_mul_parameterWeight_add_rpow`:
  shifting the spectral parameter by `u` changes the weight by at most the factor
  `1 + ‖u‖ ^ (1 / 2)`;
* `TauCeti.ParameterSymbol.inclusion`: the order inclusions, and the complex vector space
  structure of each class;
* `TauCeti.ParameterSymbol.comp`: the pointwise composition of symbols of orders `m'` and `m` has
  order `m' + m`;
* `TauCeti.ParameterSymbol.spatialDeriv`, `TauCeti.ParameterSymbol.frequencyDeriv`: a derivative
  in a position direction keeps the order `m`, and a derivative in a frequency direction lowers it
  to `m - 1`;
* `TauCeti.ParameterSymbol.inverse`: **uniform inverse estimates**. If `a` has order `m` and is
  elliptic with parameter (`TauCeti.ParameterSymbol.IsElliptic`: it is invertible, with
  `‖a⁻¹‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-m)`), its pointwise inverse has order `-m`;
* `TauCeti.ParameterSymbol.ofQuasiHomogeneous`: a smooth function on `ℝⁿ × ℝⁿ × ℂ` that is
  quasi-homogeneous of degree `m`, `f((x, t ξ), t² z) = t ^ m f((x, ξ), z)` for `t > 0`, is a
  symbol of order `m`; for instance the spectral parameter `z • id` has order `2`
  (`TauCeti.ParameterSymbol.spectralParameter`);
* `TauCeti.ParameterSymbol.isElliptic_add`: adding a perturbation bounded by a multiple of
  `(1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - 1)` to a symbol of order `m` with inverse bounded by a
  multiple of `(1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-m)`, both uniformly in the position, keeps it
  elliptic with parameter at spectral parameters of large modulus;
* `TauCeti.ParameterSymbol.shiftedLaplacian`, `TauCeti.ParameterSymbol.isElliptic_shiftedLaplacian`:
  for `s ≥ 0` the symbol `(s + ‖ξ‖²) - z` of `s - Δ - z` has order `2` and is elliptic with
  parameter on every sector `Re z ≤ c ‖z‖`, `c < 1`, on which `s + ‖z‖` is bounded below by a
  positive constant, and also on every half plane `Re z ≤ s - δ`, `δ > 0`, which for `δ < s`
  contains the closed negative real axis
  (`TauCeti.ParameterSymbol.isElliptic_shiftedLaplacian_of_re_le`).
  Hence the resolvent symbol `((s + ‖ξ‖²) - z)⁻¹` has order `-2`
  (`TauCeti.ParameterSymbol.coefficient_inverse_shiftedLaplacian`). For `s = 0` it is the principal
  resolvent symbol `(‖ξ‖² - z)⁻¹`, which keeps its low-frequency values: at `ξ = 0` it is `1` for
  `z = -1` and `1 / 2` for `z = -2`.

## Implementation notes

The estimates are proved at one point `p = ((x, ξ), z)` at a time. Pulling a function back along
`v ↦ p + parameterDilation n t v`, with `t` the weight at `p`, turns the dilated derivatives at
`p` into ordinary iterated derivatives at `0`
(`TauCeti.parameterIteratedFDeriv_eq_iteratedFDeriv_comp`), where the uniform Leibniz bound
`TauCeti.exists_norm_iteratedFDeriv_bilinear_le` applies
(`TauCeti.exists_norm_parameterIteratedFDeriv_bilinear_le`). The inverse estimates come from
`TauCeti.exists_norm_iteratedFDeriv_clm_inverse_le`, an induction on the order from
`∂ᵤ(a⁻¹) = -a⁻¹ (∂ᵤ a) a⁻¹`, as for the cut-off inverse `TauCeti.Symbol.cutoffInverse` of a
symbol.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ}

/-! ### The weight and the dilations -/

/-- The weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` of a frequency `ξ` and a spectral parameter `z`. A
spectral parameter counts as two frequency orders: `parameterWeight ξ z - 1` is positively
homogeneous of degree one under `(ξ, z) ↦ (t ξ, t² z)`. -/
def parameterWeight (ξ : CoordinateSpace n) (z : ℂ) : ℝ :=
  1 + ‖ξ‖ + Real.sqrt ‖z‖

theorem parameterWeight_def (ξ : CoordinateSpace n) (z : ℂ) :
    parameterWeight ξ z = 1 + ‖ξ‖ + Real.sqrt ‖z‖ :=
  (rfl)

theorem one_le_parameterWeight (ξ : CoordinateSpace n) (z : ℂ) : 1 ≤ parameterWeight ξ z := by
  have := Real.sqrt_nonneg ‖z‖
  have := norm_nonneg ξ
  unfold parameterWeight
  linarith

theorem parameterWeight_pos (ξ : CoordinateSpace n) (z : ℂ) : 0 < parameterWeight ξ z :=
  one_pos.trans_le (one_le_parameterWeight ξ z)

theorem norm_le_parameterWeight (ξ : CoordinateSpace n) (z : ℂ) : ‖ξ‖ ≤ parameterWeight ξ z := by
  have := Real.sqrt_nonneg ‖z‖
  unfold parameterWeight
  linarith

theorem norm_le_parameterWeight_sq (ξ : CoordinateSpace n) (z : ℂ) :
    ‖z‖ ≤ parameterWeight ξ z ^ 2 := by
  have h : Real.sqrt ‖z‖ ≤ parameterWeight ξ z := by
    have := norm_nonneg ξ
    unfold parameterWeight
    linarith
  calc ‖z‖ = Real.sqrt ‖z‖ ^ 2 := (Real.sq_sqrt (norm_nonneg z)).symm
    _ ≤ parameterWeight ξ z ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- `⟨ξ⟩² = 1 + ‖ξ‖²` is at most the square of the parameter weight. -/
theorem one_add_norm_sq_le_parameterWeight_sq (ξ : CoordinateSpace n) (z : ℂ) :
    1 + ‖ξ‖ ^ 2 ≤ parameterWeight ξ z ^ 2 := by
  have := Real.sqrt_nonneg ‖z‖
  have := norm_nonneg ξ
  rw [parameterWeight_def]
  nlinarith

/-- For a nonpositive exponent the parameter weight is dominated by the frequency weight:
`w ^ r ≤ ⟨ξ⟩ ^ r`. -/
theorem parameterWeight_rpow_le_one_add_norm_sq_rpow (ξ : CoordinateSpace n) (z : ℂ) {r : ℝ}
    (hr : r ≤ 0) : parameterWeight ξ z ^ r ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  calc parameterWeight ξ z ^ r = (parameterWeight ξ z ^ 2) ^ (r / 2) :=
        (Real.sq_rpow_div_two (parameterWeight_pos ξ z).le r).symm
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_norm_sq_le_parameterWeight_sq ξ z)
          (by linarith)

/-- For a nonpositive exponent the parameter weight is dominated by the weight of the spectral
parameter: `w ^ r ≤ (1 + ‖z‖ ^ (1 / 2)) ^ r`. -/
theorem parameterWeight_rpow_le_one_add_sqrt_rpow (ξ : CoordinateSpace n) (z : ℂ) {r : ℝ}
    (hr : r ≤ 0) : parameterWeight ξ z ^ r ≤ (1 + Real.sqrt ‖z‖) ^ r := by
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr
  rw [parameterWeight_def]
  linarith [norm_nonneg ξ]

/-- At a fixed spectral parameter `z` the parameter weight is comparable to the frequency weight:
`w ^ r ≤ (3 (1 + ‖z‖)) ^ (|r| / 2) ⟨ξ⟩ ^ r` for every real `r`. -/
theorem parameterWeight_rpow_le_mul_one_add_norm_sq_rpow (ξ : CoordinateSpace n) (z : ℂ)
    (r : ℝ) :
    parameterWeight ξ z ^ r ≤ (3 * (1 + ‖z‖)) ^ (|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  have hz : 1 ≤ 3 * (1 + ‖z‖) := by linarith [norm_nonneg z]
  rcases le_total r 0 with hr | hr
  · exact (parameterWeight_rpow_le_one_add_norm_sq_rpow ξ z hr).trans
      (le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hz (by positivity)))
  · have hsq : parameterWeight ξ z ^ 2 ≤ 3 * (1 + ‖z‖) * (1 + ‖ξ‖ ^ 2) := by
      have := Real.sq_sqrt (norm_nonneg z)
      have := Real.sqrt_nonneg ‖z‖
      rw [parameterWeight_def]
      nlinarith [sq_nonneg (1 - ‖ξ‖), sq_nonneg (1 - Real.sqrt ‖z‖),
        sq_nonneg (‖ξ‖ - Real.sqrt ‖z‖), norm_nonneg ξ, mul_nonneg (norm_nonneg z)
          (sq_nonneg ‖ξ‖)]
    calc parameterWeight ξ z ^ r = (parameterWeight ξ z ^ 2) ^ (r / 2) :=
          (Real.sq_rpow_div_two (parameterWeight_pos ξ z).le r).symm
      _ ≤ (3 * (1 + ‖z‖) * (1 + ‖ξ‖ ^ 2)) ^ (r / 2) :=
          Real.rpow_le_rpow (by positivity) hsq (by linarith)
      _ = _ := by rw [abs_of_nonneg hr, Real.mul_rpow (by positivity) (by positivity)]

/-- Shifting the spectral parameter by `u` enlarges the parameter weight by at most the factor
`1 + ‖u‖ ^ (1 / 2)`. -/
theorem parameterWeight_add_le (ξ : CoordinateSpace n) (z u : ℂ) :
    parameterWeight ξ (z + u) ≤ (1 + Real.sqrt ‖u‖) * parameterWeight ξ z := by
  have hsq : Real.sqrt ‖z + u‖ ≤ Real.sqrt ‖z‖ + Real.sqrt ‖u‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_add_le z u, Real.sq_sqrt (norm_nonneg z), Real.sq_sqrt (norm_nonneg u),
      mul_nonneg (Real.sqrt_nonneg ‖z‖) (Real.sqrt_nonneg ‖u‖)]
  have := Real.sqrt_nonneg ‖u‖
  have := Real.sqrt_nonneg ‖z‖
  rw [parameterWeight_def, parameterWeight_def]
  nlinarith [norm_nonneg ξ]

/-- For a nonpositive exponent `r`, shifting the spectral parameter by `u` changes the power
`w ^ r` of the parameter weight by at most the factor `(1 + ‖u‖ ^ (1 / 2)) ^ (-r)`. -/
theorem parameterWeight_rpow_le_mul_parameterWeight_add_rpow (ξ : CoordinateSpace n) (z u : ℂ)
    {r : ℝ} (hr : r ≤ 0) :
    parameterWeight ξ z ^ r ≤ (1 + Real.sqrt ‖u‖) ^ (-r) * parameterWeight ξ (z + u) ^ r := by
  have hk : 0 < 1 + Real.sqrt ‖u‖ := by positivity
  calc parameterWeight ξ z ^ r
      = (1 + Real.sqrt ‖u‖) ^ (-r) * ((1 + Real.sqrt ‖u‖) * parameterWeight ξ z) ^ r := by
        rw [Real.mul_rpow hk.le (parameterWeight_pos ξ z).le, ← mul_assoc, ← Real.rpow_add hk,
          neg_add_cancel, Real.rpow_zero, one_mul]
    _ ≤ (1 + Real.sqrt ‖u‖) ^ (-r) * parameterWeight ξ (z + u) ^ r :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (parameterWeight_pos ξ _)
          (parameterWeight_add_le ξ z u) hr) (by positivity)

variable (n) in
/-- The anisotropic dilation `((y, η), μ) ↦ ((y, t η), t² μ)` of the position, frequency and
spectral parameter directions. -/
def parameterDilation (t : ℝ) :
    (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] (CoordinateSpace n × CoordinateSpace n) × ℂ :=
  ((ContinuousLinearMap.id ℝ (CoordinateSpace n)).prodMap
    (t • ContinuousLinearMap.id ℝ (CoordinateSpace n))).prodMap
    ((t ^ 2) • ContinuousLinearMap.id ℝ ℂ)

@[simp]
theorem parameterDilation_apply (t : ℝ) (v : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterDilation n t v = ((v.1.1, t • v.1.2), (t ^ 2) • v.2) := (rfl)

/-- The `k`-th derivative of `f` at `p = ((x, ξ), z)`, taken in the directions dilated by
`parameterDilation n (parameterWeight ξ z)`: a frequency direction is scaled by the weight and the
spectral parameter direction by its square. A bound `C * parameterWeight ξ z ^ m` on its norm
amounts to the estimates `‖∂ₓ^α ∂_ξ^β ∂_z^γ f‖ ≤ C' * parameterWeight ξ z ^ (m - |β| - 2 |γ|)` for
`|α| + |β| + |γ| = k`, with real derivatives `∂_z` in the spectral parameter. -/
def parameterIteratedFDeriv {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ)
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => (CoordinateSpace n × CoordinateSpace n) × ℂ) A :=
  (iteratedFDeriv ℝ k f p).compContinuousLinearMap fun _ =>
    parameterDilation n (parameterWeight p.1.2 p.2)

/-- The dilated derivative evaluated on directions `v`: the ordinary derivative evaluated on the
dilated directions. -/
theorem parameterIteratedFDeriv_apply {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ)
    (v : Fin k → (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv k f p v =
      iteratedFDeriv ℝ k f p fun i => parameterDilation n (parameterWeight p.1.2 p.2) (v i) := by
  simp only [parameterIteratedFDeriv, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- The dilated derivative of order `0` is the value of the function. -/
@[simp]
theorem parameterIteratedFDeriv_zero_apply {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ)
    (v : Fin 0 → (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv 0 f p v = f p := by
  simp [parameterIteratedFDeriv_apply]

/-! ### Estimates

The estimates below are proved at one point `p` at a time, by pulling the function back along the
affine map `v ↦ p + parameterDilation n t v` with `t` the weight at `p`. This turns the dilated
derivatives at `p` into ordinary iterated derivatives at `0`, to which the Leibniz rule applies. -/

section Estimates

variable {A X Y Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

/-- For `t ≠ 0`, the dilation is a linear equivalence, with inverse the dilation by `t⁻¹`. -/
private def dilationEquiv (t : ℝ) (ht : t ≠ 0) :
    ((CoordinateSpace n × CoordinateSpace n) × ℂ) ≃L[ℝ]
      ((CoordinateSpace n × CoordinateSpace n) × ℂ) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (parameterDilation n t) (parameterDilation n t⁻¹)
    (ContinuousLinearMap.ext fun v => by simp [smul_smul, ht])
    (ContinuousLinearMap.ext fun v => by simp [smul_smul, ht])

private theorem iteratedFDeriv_comp_dilation (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) {t : ℝ} (ht : t ≠ 0) (k : ℕ) :
    iteratedFDeriv ℝ k (fun v => f (p + parameterDilation n t v)) 0 =
      (iteratedFDeriv ℝ k f p).compContinuousLinearMap fun _ => parameterDilation n t := by
  have h := (dilationEquiv t ht).iteratedFDeriv_comp_right (fun u => f (p + u)) 0 k
  rw [map_zero, iteratedFDeriv_comp_add_left, add_zero] at h
  exact h

/-- The dilated derivative at `p` is the ordinary derivative at `0` of the pullback along
`v ↦ p + parameterDilation n t v`, `t` the weight at `p`. -/
theorem parameterIteratedFDeriv_eq_iteratedFDeriv_comp
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) (k : ℕ) :
    parameterIteratedFDeriv k f p = iteratedFDeriv ℝ k
      (fun v => f (p + parameterDilation n (parameterWeight p.1.2 p.2) v)) 0 :=
  (iteratedFDeriv_comp_dilation f p (parameterWeight_pos _ _).ne' k).symm

/-- The dilated derivative of order `0` has the norm of the value of the function. -/
@[simp]
theorem norm_parameterIteratedFDeriv_zero (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    ‖parameterIteratedFDeriv 0 f p‖ = ‖f p‖ := by
  simp [parameterIteratedFDeriv_eq_iteratedFDeriv_comp, Prod.mk_zero_zero]

/-- The dilated derivatives at `p` only depend on the function near `p`. -/
theorem parameterIteratedFDeriv_congr {f g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (h : f =ᶠ[𝓝 p] g) (k : ℕ) :
    parameterIteratedFDeriv k f p = parameterIteratedFDeriv k g p := by
  unfold parameterIteratedFDeriv
  rw [(h.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]

/-- The dilated derivatives of a function vanishing near `p` vanish at `p`. -/
theorem parameterIteratedFDeriv_eq_zero_of_eventuallyEq_zero
    {f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (h : f =ᶠ[𝓝 p] 0) (k : ℕ) :
    parameterIteratedFDeriv k f p = 0 := by
  rw [parameterIteratedFDeriv_congr h, parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
  simp

/-- The dilated derivatives of a finite sum of functions smooth at `p` are the sums of their
dilated derivatives. -/
theorem parameterIteratedFDeriv_sum {ι : Type*} {s : Finset ι}
    {f : ι → (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} {k : ℕ}
    (hf : ∀ j ∈ s, ContDiffAt ℝ k (f j) p) :
    parameterIteratedFDeriv k (fun q => ∑ j ∈ s, f j q) p =
      ∑ j ∈ s, parameterIteratedFDeriv k (f j) p := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_fun_sum_apply hf]

/-- The dilated derivatives of a difference of functions smooth at `p` are the differences of their
dilated derivatives. -/
theorem parameterIteratedFDeriv_sub {f g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} {k : ℕ} (hf : ContDiffAt ℝ k f p)
    (hg : ContDiffAt ℝ k g p) :
    parameterIteratedFDeriv k (fun q => f q - g q) p =
      parameterIteratedFDeriv k f p - parameterIteratedFDeriv k g p := by
  ext v
  simp [parameterIteratedFDeriv_apply, fun_iteratedFDeriv_sub_apply hf hg]

/-- `TauCeti.parameterIteratedFDeriv_eq_iteratedFDeriv_comp` at a point given by its position,
frequency and spectral parameter. -/
theorem parameterIteratedFDeriv_mk_eq
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A) (x ξ : CoordinateSpace n) (z : ℂ)
    (k : ℕ) : parameterIteratedFDeriv k f ((x, ξ), z) = iteratedFDeriv ℝ k
      (fun v => f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v)) 0 :=
  parameterIteratedFDeriv_eq_iteratedFDeriv_comp f _ k

/-- The pullback of a function smooth on `univ ×ˢ Λ` is smooth on an open neighbourhood of `0`. -/
theorem contDiffOn_comp_parameterDilation {Λ : Set ℂ} (hΛ : IsOpen Λ)
    {f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A} (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ))
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) (t : ℝ) :
    IsOpen ((fun v => p + parameterDilation n t v) ⁻¹' (univ ×ˢ Λ)) ∧
      (0 : (CoordinateSpace n × CoordinateSpace n) × ℂ) ∈
        (fun v => p + parameterDilation n t v) ⁻¹' (univ ×ˢ Λ) ∧
      ContDiffOn ℝ ∞ (fun v => f (p + parameterDilation n t v))
        ((fun v => p + parameterDilation n t v) ⁻¹' (univ ×ˢ Λ)) := by
  refine ⟨(isOpen_univ.prod hΛ).preimage (by fun_prop), by simpa using hp, ?_⟩
  exact hf.comp (contDiff_const.add (parameterDilation n t).contDiff).contDiffOn
    (mapsTo_preimage _ _)

/-- **Leibniz rule** for dilated derivatives: at a point `p` with `p.2 ∈ Λ`, if the dilated
derivatives of order at most `k` of `f` and `g`, smooth on `univ ×ˢ Λ`, are bounded by `C` and `D`,
those of `B (f ·) (g ·)` are bounded by `E * (C * D)`, with `E` depending only on `B` and `k`. -/
theorem exists_norm_parameterIteratedFDeriv_bilinear_le (B : X →L[ℝ] Y →L[ℝ] Z) (k : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {Λ : Set ℂ}, IsOpen Λ →
      ∀ (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → X)
        (g : (CoordinateSpace n × CoordinateSpace n) × ℂ → Y),
      ContDiffOn ℝ ∞ f (univ ×ˢ Λ) → ContDiffOn ℝ ∞ g (univ ×ˢ Λ) →
      ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, p.2 ∈ Λ → ∀ C D : ℝ,
      (∀ i ≤ k, ‖parameterIteratedFDeriv i f p‖ ≤ C) →
      (∀ i ≤ k, ‖parameterIteratedFDeriv i g p‖ ≤ D) →
      ∀ j ≤ k, ‖parameterIteratedFDeriv j (fun q => B (f q) (g q)) p‖ ≤ E * (C * D) := by
  obtain ⟨E, hE, hB⟩ := exists_norm_iteratedFDeriv_bilinear_le
    ((CoordinateSpace n × CoordinateSpace n) × ℂ) B k
  refine ⟨E, hE, fun hΛ f g hf hg p hp C D hC hD j hj => ?_⟩
  obtain ⟨hU, h0, hfT⟩ := contDiffOn_comp_parameterDilation hΛ hf hp (parameterWeight p.1.2 p.2)
  obtain ⟨-, -, hgT⟩ := contDiffOn_comp_parameterDilation hΛ hg hp (parameterWeight p.1.2 p.2)
  have hk : ((k : ℕ∞ω)) ≤ ∞ := by exact_mod_cast le_top
  rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
  refine hB _ _ _ 0 hU h0 (hfT.of_le hk) (hgT.of_le hk) C D (fun i hi => ?_) (fun i hi => ?_) j hj
  · rw [← parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
    exact hC i hi
  · rw [← parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
    exact hD i hi

/-- The estimates of order `m` for a function of positions, frequencies and spectral parameters in
`Λ`: on every compact set of positions, `‖parameterIteratedFDeriv k f ((x, ξ), z)‖` is at most a
constant times `parameterWeight ξ z ^ m`. -/
private def Bounds (Λ : Set ℂ) (m : ℝ) (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A) :
    Prop :=
  ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
    ‖parameterIteratedFDeriv k f ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m

variable {Λ : Set ℂ} {m m' : ℝ} {f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}

private theorem rpow_parameterWeight_pos (ξ : CoordinateSpace n) (z : ℂ) (m : ℝ) :
    0 < parameterWeight ξ z ^ m :=
  Real.rpow_pos_of_pos (parameterWeight_pos ξ z) m

/-- One constant serves for all derivatives of order at most `k`. -/
private theorem Bounds.exists_forall_le (h : Bounds Λ m f) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i f ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m := by
  induction k with
  | zero =>
    obtain ⟨C, hC, h0⟩ := h K hK 0
    exact ⟨C, hC, fun i hi => by obtain rfl := Nat.le_zero.1 hi; exact h0⟩
  | succ k ih =>
    obtain ⟨C, hC, hk⟩ := ih
    obtain ⟨D, -, hk1⟩ := h K hK (k + 1)
    refine ⟨max C D, le_max_of_le_left hC, fun i hi x hx ξ z hz => ?_⟩
    have hw := (rpow_parameterWeight_pos ξ z m).le
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact (hk i (Nat.lt_succ_iff.1 hi) x hx ξ z hz).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)
    · exact (hk1 x hx ξ z hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)

private theorem Bounds.mono (h : Bounds Λ m f) (hm : m ≤ m') : Bounds Λ m' f := fun K hK k => by
  obtain ⟨C, hC, hf⟩ := h K hK k
  exact ⟨C, hC, fun x hx ξ z hz => (hf x hx ξ z hz).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_parameterWeight ξ z) hm) hC)⟩

private theorem Bounds.congr {g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    (h : Bounds Λ m g) (hfg : ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, p.2 ∈ Λ →
      f =ᶠ[𝓝 p] g) : Bounds Λ m f := fun K hK k => by
  obtain ⟨C, hC, hg⟩ := h K hK k
  refine ⟨C, hC, fun x hx ξ z hz => ?_⟩
  rw [parameterIteratedFDeriv_congr (hfg _ hz)]
  exact hg x hx ξ z hz

private theorem Bounds.add (hΛ : IsOpen Λ) {g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ)) (hg : ContDiffOn ℝ ∞ g (univ ×ˢ Λ)) (hbf : Bounds Λ m f)
    (hbg : Bounds Λ m g) : Bounds Λ m (fun p => f p + g p) := fun K hK k => by
  obtain ⟨C, hC, hf'⟩ := hbf K hK k
  obtain ⟨D, hD, hg'⟩ := hbg K hK k
  refine ⟨C + D, add_nonneg hC hD, fun x hx ξ z hz => ?_⟩
  obtain ⟨hU, h0, hfT⟩ := contDiffOn_comp_parameterDilation hΛ hf (p := ((x, ξ), z)) hz
    (parameterWeight ξ z)
  obtain ⟨-, -, hgT⟩ := contDiffOn_comp_parameterDilation hΛ hg (p := ((x, ξ), z)) hz
    (parameterWeight ξ z)
  have h₁ := hf' x hx ξ z hz
  have h₂ := hg' x hx ξ z hz
  rw [parameterIteratedFDeriv_mk_eq] at h₁ h₂ ⊢
  have key : iteratedFDeriv ℝ k
      (fun v => f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v) +
        g (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v)) 0 = _ + _ :=
    iteratedFDeriv_add_apply (((hfT 0 h0).contDiffAt (hU.mem_nhds h0)).of_le
      (by exact_mod_cast le_top)) (((hgT 0 h0).contDiffAt (hU.mem_nhds h0)).of_le
      (by exact_mod_cast le_top))
  rw [key]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- Composition with a fixed continuous linear map keeps the order. -/
private theorem Bounds.comp_left (hΛ : IsOpen Λ) {A' : Type*} [NormedAddCommGroup A']
    [NormedSpace ℝ A'] (L : A →L[ℝ] A') (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ)) (hb : Bounds Λ m f) :
    Bounds Λ m (fun p => L (f p)) := fun K hK k => by
  obtain ⟨C, hC, hf'⟩ := hb K hK k
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg L) hC, fun x hx ξ z hz => ?_⟩
  obtain ⟨hU, h0, hfT⟩ := contDiffOn_comp_parameterDilation hΛ hf (p := ((x, ξ), z)) hz
    (parameterWeight ξ z)
  have := hf' x hx ξ z hz
  rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp] at *
  refine (L.norm_iteratedFDeriv_comp_left ((hfT 0 h0).contDiffAt (hU.mem_nhds h0))
    (by exact_mod_cast le_top)).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this (norm_nonneg L)

/-- **Leibniz rule**: a bilinear expression in functions of orders `m` and `m'` has order
`m + m'`. -/
private theorem Bounds.bilinear (hΛ : IsOpen Λ) (B : X →L[ℝ] Y →L[ℝ] Z)
    {f : (CoordinateSpace n × CoordinateSpace n) × ℂ → X}
    {g : (CoordinateSpace n × CoordinateSpace n) × ℂ → Y}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ)) (hg : ContDiffOn ℝ ∞ g (univ ×ˢ Λ)) (hbf : Bounds Λ m f)
    (hbg : Bounds Λ m' g) : Bounds Λ (m + m') (fun p => B (f p) (g p)) := fun K hK k => by
  obtain ⟨C, hC, hf'⟩ := hbf.exists_forall_le hK k
  obtain ⟨D, hD, hg'⟩ := hbg.exists_forall_le hK k
  obtain ⟨E, hE, hB⟩ := exists_norm_parameterIteratedFDeriv_bilinear_le (n := n) B k
  refine ⟨E * (C * D), by positivity, fun x hx ξ z hz => ?_⟩
  refine (hB hΛ f g hf hg _ hz (C * parameterWeight ξ z ^ m) (D * parameterWeight ξ z ^ m')
    (fun i hi => hf' i hi x hx ξ z hz) (fun i hi => hg' i hi x hx ξ z hz) k le_rfl).trans_eq ?_
  rw [Real.rpow_add (parameterWeight_pos ξ z)]
  ring

/-- The pointwise inverse of a function of order `m` whose inverse has the bound of order `-m`
has order `-m`. -/
private theorem Bounds.inverse (hΛ : IsOpen Λ) {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {a : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W}
    (ha : ContDiffOn ℝ ∞ a (univ ×ˢ Λ)) (hb : Bounds Λ m a)
    (hinv : ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, p.2 ∈ Λ → (a p).IsInvertible)
    (hC : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖(a ((x, ξ), z)).inverse‖ ≤ C * parameterWeight ξ z ^ (-m)) :
    Bounds Λ (-m) (fun p => (a p).inverse) := fun K hK k => by
  obtain ⟨A, -, hA⟩ := hb.exists_forall_le hK k
  obtain ⟨B, hB⟩ := hC K hK
  obtain ⟨c, hc⟩ := exists_norm_iteratedFDeriv_clm_inverse_le
    (E := (CoordinateSpace n × CoordinateSpace n) × ℂ) (V := V) (W := W) k A B
  refine ⟨max c 0, le_max_right _ _, fun x hx ξ z hz => ?_⟩
  have hs := rpow_parameterWeight_pos ξ z m
  obtain ⟨hU, h0, haT⟩ := contDiffOn_comp_parameterDilation hΛ ha (p := ((x, ξ), z)) hz
    (parameterWeight ξ z)
  rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
  have h := hc _ _ 0 _ hs hU h0 haT (fun y hy => hinv _ hy.2) (fun j hj => ?_) ?_ k le_rfl
  · refine h.trans ?_
    rw [Real.rpow_neg (parameterWeight_pos ξ z).le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 hs.le)
  · rw [← parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
    exact hA j hj x hx ξ z hz
  · simpa [Real.rpow_neg (parameterWeight_pos ξ z).le, div_eq_mul_inv] using hB x hx ξ z hz

/-- A constant has order `0`. -/
private theorem bounds_const (c : A) :
    Bounds Λ 0 (fun _ : (CoordinateSpace n × CoordinateSpace n) × ℂ => c) := fun K _ k => by
  refine ⟨‖c‖, norm_nonneg c, fun x _ ξ z _ => ?_⟩
  rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp, Real.rpow_zero, mul_one]
  rcases k with _ | k
  · simp
  · simp [iteratedFDeriv_const_of_ne]

/-- A smooth function of the position alone has order `0`: the dilations do not scale the position
directions, so its dilated derivatives are its ordinary derivatives in the position. -/
private theorem bounds_comp_fst_fst {g : CoordinateSpace n → A} (hg : ContDiff ℝ ∞ g) :
    Bounds Λ 0 (fun p : (CoordinateSpace n × CoordinateSpace n) × ℂ => g p.1.1) :=
  fun K hK k => by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hg.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ z _ => ?_⟩
  set L : (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] CoordinateSpace n :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one fun v => by
    simpa [L] using (norm_fst_le v.1).trans (norm_fst_le v)
  have hfun : (fun v => g (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v).1.1) =
      (fun y => g (x + y)) ∘ L := by
    funext v
    simp [L]
  rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp, Real.rpow_zero, mul_one, hfun,
    L.iteratedFDeriv_comp_right (f := fun y => g (x + y))
      (hg.comp (contDiff_const.add contDiff_id)) 0 (by exact_mod_cast le_top), map_zero,
    iteratedFDeriv_comp_add_left, add_zero]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ k g x‖ * ∏ _ : Fin k, ‖L‖ ≤ ‖iteratedFDeriv ℝ k g x‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hL) (norm_nonneg _)
    _ ≤ max C 0 := by
        rw [mul_one]
        exact (hC x hx).trans (le_max_left _ _)

/-- A continuous linear map `L` has order `m` if both `L` and `L` composed with the dilations are
bounded by multiples of the weight to the power `m`. -/
private theorem bounds_continuousLinearMap
    (L : (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] A) {C : ℝ}
    (h₀ : ∀ x ξ, ∀ z ∈ Λ, ‖L ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m)
    (h₁ : ∀ ξ : CoordinateSpace n, ∀ z ∈ Λ, ‖L.comp (parameterDilation n (parameterWeight ξ z))‖ ≤
      C * parameterWeight ξ z ^ m) :
    Bounds Λ m L := fun K _ k => by
  refine ⟨max C 0, le_max_right _ _, fun x _ ξ z hz => ?_⟩
  have hw := (rpow_parameterWeight_pos ξ z m).le
  have hC : C * parameterWeight ξ z ^ m ≤ max C 0 * parameterWeight ξ z ^ m :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
  have hL : (fun v => L (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v)) =
      fun v => L ((x, ξ), z) + (L.comp (parameterDilation n (parameterWeight ξ z))) v := by
    ext1 v
    rw [map_add]
    rfl
  rw [hL]
  rcases k with _ | k
  · simpa [Prod.mk_zero_zero] using (h₀ x ξ z hz).trans hC
  · rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (fun v => L ((x, ξ), z) +
        (L.comp (parameterDilation n (parameterWeight ξ z))) v) =
          fun _ => L.comp (parameterDilation n (parameterWeight ξ z)) := by
      ext1 v
      rw [fderiv_const_add, ContinuousLinearMap.fderiv]
    rw [hd]
    rcases k with _ | k
    · simpa using (h₁ ξ z hz).trans hC
    · simpa [iteratedFDeriv_const_of_ne] using mul_nonneg (le_max_right C 0) hw

/-- The derivative in a direction `e` that the dilations scale by `t ^ d` lowers the order by `d`:
`d = 0` for a position direction, `d = 1` for a frequency direction. -/
private theorem Bounds.fderiv_apply (hΛ : IsOpen Λ) (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ))
    (hb : Bounds Λ m f) {e : (CoordinateSpace n × CoordinateSpace n) × ℂ} {d : ℕ}
    (he : ∀ t : ℝ, parameterDilation n t e = t ^ d • e) :
    Bounds Λ (m - d) (fun p => fderiv ℝ f p e) := fun K hK k => by
  obtain ⟨C, hC, hf'⟩ := hb K hK (k + 1)
  refine ⟨‖e‖ * C, mul_nonneg (norm_nonneg e) hC, fun x hx ξ z hz => ?_⟩
  have ht := parameterWeight_pos ξ z
  have htd : 0 < parameterWeight ξ z ^ d := pow_pos ht d
  obtain ⟨hU, h0, hgT⟩ := contDiffOn_comp_parameterDilation hΛ hf (p := ((x, ξ), z)) hz
    (parameterWeight ξ z)
  -- With `g` the pullback of `f` along the dilation, `fderiv f · e = t⁻ᵈ • fderiv g · e`.
  let L : ((((CoordinateSpace n × CoordinateSpace n) × ℂ) →L[ℝ] A) →L[ℝ] A) :=
    (parameterWeight ξ z ^ d)⁻¹ • ContinuousLinearMap.apply ℝ A e
  have hL : ‖L‖ ≤ (parameterWeight ξ z ^ d)⁻¹ * ‖e‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
    simp only [L, smul_apply, ContinuousLinearMap.apply_apply, norm_smul,
      norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos ht]
    rw [mul_assoc, mul_comm ‖e‖]
    exact mul_le_mul_of_nonneg_left (φ.le_opNorm e) (by positivity)
  have hev : (fun v => fderiv ℝ f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v) e)
      =ᶠ[𝓝 0] fun v => L (fderiv ℝ
        (fun w => f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) w)) v) := by
    filter_upwards [hU.mem_nhds h0] with v hv
    have hdf : DifferentiableAt ℝ f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v) :=
      (hf.contDiffAt ((isOpen_univ.prod hΛ).mem_nhds hv)).differentiableAt (by simp)
    have hg : HasFDerivAt (fun w => f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) w))
        ((fderiv ℝ f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) v)).comp
          (parameterDilation n (parameterWeight ξ z))) v :=
      hdf.hasFDerivAt.comp v ((parameterDilation n (parameterWeight ξ z)).hasFDerivAt.const_add _)
    rw [hg.fderiv]
    simp [L, he, smul_smul, inv_mul_cancel₀ htd.ne']
  have hd : ContDiffAt ℝ ∞
      (fderiv ℝ fun w => f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) w)) 0 :=
    (hgT.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds h0)
  have h₁ := hf' x hx ξ z hz
  rw [parameterIteratedFDeriv_mk_eq, ← norm_iteratedFDeriv_fderiv] at h₁
  rw [parameterIteratedFDeriv_mk_eq, (hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  refine (L.norm_iteratedFDeriv_comp_left hd (by exact_mod_cast le_top)).trans ?_
  rw [Real.rpow_sub ht, Real.rpow_natCast]
  calc ‖L‖ * ‖iteratedFDeriv ℝ k
          (fderiv ℝ fun w => f (((x, ξ), z) + parameterDilation n (parameterWeight ξ z) w)) 0‖
      ≤ (parameterWeight ξ z ^ d)⁻¹ * ‖e‖ * (C * parameterWeight ξ z ^ m) :=
        mul_le_mul hL h₁ (norm_nonneg _) (by positivity)
    _ = ‖e‖ * C * (parameterWeight ξ z ^ m / parameterWeight ξ z ^ d) := by ring

/-- A smooth function that is quasi-homogeneous of degree `m` has the estimates of order `m`: the
dilated derivative at `p = ((x, ξ), z)` is `w ^ m` times the ordinary derivative at the point
`parameterDilation n w⁻¹ p`, whose frequency and spectral parameter have norm at most `1`. -/
private theorem bounds_of_quasiHomogeneous (Λ : Set ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ t : ℝ, 0 < t → ∀ p, f (parameterDilation n t p) = t ^ m • f p) :
    Bounds Λ m f := fun K hK k => by
  obtain ⟨C, hC⟩ := ((hK.prod (isCompact_closedBall (0 : CoordinateSpace n) 1)).prod
    (isCompact_closedBall (0 : ℂ) 1)).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ z _ => ?_⟩
  set t := parameterWeight ξ z with ht_def
  have ht : 0 < t := parameterWeight_pos ξ z
  set q := parameterDilation n t⁻¹ ((x, ξ), z) with hqdef
  have hDq : parameterDilation n t q = ((x, ξ), z) := by
    simp [hqdef, smul_smul, ht.ne']
  -- The dilation by `t` takes `v + q` to `((x, ξ), z) + parameterDilation n t v`.
  have hq : (fun v => f (((x, ξ), z) + parameterDilation n t v)) = fun v => t ^ m • f (v + q) := by
    funext v
    rw [← hhom t ht, map_add, hDq, add_comm]
  have hmem : q ∈ (K ×ˢ Metric.closedBall (0 : CoordinateSpace n) 1) ×ˢ
      Metric.closedBall (0 : ℂ) 1 := by
    simp only [hqdef, parameterDilation_apply, mem_prod, mem_closedBall_zero_iff, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos ht, inv_pow]
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · rw [inv_mul_le_one₀ ht]
      exact norm_le_parameterWeight ξ z
    · rw [inv_mul_le_one₀ (by positivity)]
      exact norm_le_parameterWeight_sq ξ z
  have hfq : ContDiff ℝ ∞ fun v => f (v + q) := hf.comp (contDiff_id.add contDiff_const)
  have heq : parameterIteratedFDeriv k f ((x, ξ), z) = t ^ m • iteratedFDeriv ℝ k f q := by
    rw [parameterIteratedFDeriv_eq_iteratedFDeriv_comp]
    dsimp only
    rw [← ht_def, hq,
      iteratedFDeriv_const_smul_apply' (hfq.contDiffAt.of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_comp_add_right, zero_add]
  have htm := Real.rpow_pos_of_pos ht m
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos htm, mul_comm]
  gcongr
  exact (hC q hmem).trans (le_max_left _ _)

end Estimates

/-! ### Strongly parameter-dependent symbols -/

variable (n) in
/-- The class of strongly parameter-dependent symbols of order `m` on `ℝⁿ × ℝⁿ × Λ`, for an open
set `Λ ⊆ ℂ` of spectral parameters, with values in `V →L[ℂ] W`: maps `a((x, ξ), z)`, smooth in all
variables on `ℝⁿ × ℝⁿ × Λ`, such that on every compact set `K` of positions, for every `k`,

`‖parameterIteratedFDeriv k a ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m`

for some `C`, all `x ∈ K`, all frequencies `ξ` and all `z ∈ Λ`. Equivalently,
`‖∂ₓ^α ∂_ξ^β ∂_z^γ a((x, ξ), z)‖ ≤ C' (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (m - |β| - 2 |γ|)`: a frequency
derivative gains one order and a derivative in the spectral parameter gains two. By convention the
coefficient vanishes for spectral parameters outside `Λ`. -/
@[ext]
structure ParameterSymbol (Λ : TopologicalSpace.Opens ℂ) (V W : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The coefficient `a((x, ξ), z)` at the position `x`, the frequency `ξ` and the spectral
  parameter `z`, set to `0` for `z ∉ Λ`. -/
  coefficient : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient (univ ×ˢ (Λ : Set ℂ))
  coefficient_of_notMem : ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, p.2 ∉ Λ →
    coefficient p = 0
  exists_bound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv k coefficient ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m

namespace ParameterSymbol

variable {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

theorem coefficient_injective : Function.Injective
    (coefficient : ParameterSymbol n Λ V W m → (CoordinateSpace n × CoordinateSpace n) × ℂ → _) :=
  fun _ _ h => ParameterSymbol.ext h

/-- A parameter-dependent symbol is determined by its values at spectral parameters in `Λ`. -/
theorem ext_of_mem {a b : ParameterSymbol n Λ V W m}
    (h : ∀ x ξ, ∀ z ∈ Λ, a.coefficient ((x, ξ), z) = b.coefficient ((x, ξ), z)) : a = b := by
  ext1
  funext ⟨⟨x, ξ⟩, z⟩
  by_cases hz : z ∈ Λ
  · exact h x ξ z hz
  · rw [a.coefficient_of_notMem _ hz, b.coefficient_of_notMem _ hz]

section Module

instance : Zero (ParameterSymbol n Λ V W m) where
  zero :=
    { coefficient := 0
      contDiffOn_coefficient := contDiffOn_const
      coefficient_of_notMem := fun _ _ => rfl
      exists_bound := fun _ _ k => ⟨0, le_rfl, fun x _ ξ z _ => by
        rw [parameterIteratedFDeriv, zero_mul, norm_le_zero_iff]
        ext
        simp⟩ }

instance : Add (ParameterSymbol n Λ V W m) where
  add a b :=
    { coefficient := fun p => a.coefficient p + b.coefficient p
      contDiffOn_coefficient := a.contDiffOn_coefficient.add b.contDiffOn_coefficient
      coefficient_of_notMem := fun p hp => by
        rw [a.coefficient_of_notMem p hp, b.coefficient_of_notMem p hp, add_zero]
      exists_bound := by
        exact Bounds.add Λ.isOpen a.contDiffOn_coefficient b.contDiffOn_coefficient
          a.exists_bound b.exists_bound }

instance : SMul ℂ (ParameterSymbol n Λ V W m) where
  smul c a :=
    { coefficient := fun p => c • a.coefficient p
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul c
      coefficient_of_notMem := fun p hp => by rw [a.coefficient_of_notMem p hp, smul_zero]
      exists_bound := by
        exact Bounds.comp_left Λ.isOpen
          ((c • ContinuousLinearMap.id ℂ (V →L[ℂ] W)).restrictScalars ℝ) a.contDiffOn_coefficient
          a.exists_bound }

instance : Neg (ParameterSymbol n Λ V W m) where
  neg a := (-1 : ℂ) • a

instance : Sub (ParameterSymbol n Λ V W m) where
  sub a b := a + -b

instance : SMul ℕ (ParameterSymbol n Λ V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (ParameterSymbol n Λ V W m) where
  smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : ParameterSymbol n Λ V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : ParameterSymbol n Λ V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : ParameterSymbol n Λ V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : ParameterSymbol n Λ V W m) : (-a).coefficient = -a.coefficient :=
  neg_one_smul ℂ a.coefficient

@[simp]
theorem coefficient_sub (a b : ParameterSymbol n Λ V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient := by
  rw [sub_eq_add_neg a.coefficient]
  exact congrArg (a.coefficient + ·) (coefficient_neg b)

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : ParameterSymbol n Λ V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : ParameterSymbol n Λ V W m) :
    (k • a).coefficient = k • a.coefficient :=
  Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (ParameterSymbol n Λ V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (ParameterSymbol n Λ V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

@[simp]
theorem coefficient_sum {ι : Type*} (s : Finset ι) (a : ι → ParameterSymbol n Λ V W m) :
    (∑ i ∈ s, a i).coefficient = ∑ i ∈ s, (a i).coefficient :=
  map_sum (AddMonoidHom.mk' coefficient coefficient_add) a s

end Module

/-- A parameter-dependent symbol of order `m` has every order `m' ≥ m`, since the weight is at
least `1`. -/
def inclusion (h : m ≤ m') : ParameterSymbol n Λ V W m →ₗ[ℂ] ParameterSymbol n Λ V W m' where
  toFun a :=
    { coefficient := a.coefficient
      contDiffOn_coefficient := a.contDiffOn_coefficient
      coefficient_of_notMem := a.coefficient_of_notMem
      exists_bound := by exact Bounds.mono a.exists_bound h }
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_inclusion (h : m ≤ m') (a : ParameterSymbol n Λ V W m) :
    (inclusion h a).coefficient = a.coefficient := (rfl)

theorem inclusion_injective (h : m ≤ m') :
    Function.Injective (inclusion (n := n) (Λ := Λ) (V := V) (W := W) h) :=
  fun _ _ hab => ParameterSymbol.ext (by simpa using congrArg ParameterSymbol.coefficient hab)

/-- The pointwise composition `b((x, ξ), z) ∘ a((x, ξ), z)` of parameter-dependent symbols of
orders `m'` and `m` has order `m' + m`. For matrix-valued symbols this is the matrix product. -/
def comp (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) :
    ParameterSymbol n Λ V U (m' + m) where
  coefficient p := (b.coefficient p).comp (a.coefficient p)
  contDiffOn_coefficient := by
    exact (((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).isBoundedBilinearMap
      |>.contDiff (n := ∞)).comp_contDiffOn
      (b.contDiffOn_coefficient.prodMk a.contDiffOn_coefficient)
  coefficient_of_notMem p hp := by
    rw [b.coefficient_of_notMem p hp, ContinuousLinearMap.zero_comp]
  exists_bound := by
    exact Bounds.bilinear Λ.isOpen ((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ)
      b.contDiffOn_coefficient a.contDiffOn_coefficient b.exists_bound a.exists_bound

@[simp]
theorem coefficient_comp (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (b.comp a).coefficient p = (b.coefficient p).comp (a.coefficient p) := (rfl)

open scoped Classical in
/-- A smooth function `f` of the position alone, as a parameter-dependent symbol of order `0`: its
coefficient is `f(x)` at every frequency and every spectral parameter in `Λ`. Composing a symbol
with it multiplies the symbol by `f`; it is the counterpart of `TauCeti.Symbol.ofSpatial`. -/
def ofSpatial (f : CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f) :
    ParameterSymbol n Λ V W 0 where
  coefficient p := if p.2 ∈ Λ then f p.1.1 else 0
  contDiffOn_coefficient :=
    (hf.comp (contDiff_fst.comp contDiff_fst)).contDiffOn.congr fun p hp => by
      simp [SetLike.mem_coe.1 hp.2]
  coefficient_of_notMem p hp := by simp [hp]
  exists_bound := (bounds_comp_fst_fst hf).congr fun p hp => by
    filter_upwards [(Λ.isOpen.preimage continuous_snd).mem_nhds hp] with q hq
    have hq' : q.2 ∈ Λ := hq
    simp [hq']

@[simp]
theorem coefficient_ofSpatial (f : CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (ofSpatial f hf : ParameterSymbol n Λ V W 0).coefficient ((x, ξ), z) = f x := by
  simp [ofSpatial, hz]

/-! ### Derivatives in the position and frequency directions -/

/-- The coefficient of a parameter-dependent symbol is smooth at every point whose spectral
parameter lies in `Λ`. -/
theorem contDiffAt_coefficient (a : ParameterSymbol n Λ V W m)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    ContDiffAt ℝ ∞ a.coefficient p :=
  (a.contDiffOn_coefficient p ⟨mem_univ _, hp⟩).contDiffAt
    ((isOpen_univ.prod Λ.isOpen).mem_nhds ⟨mem_univ _, hp⟩)

/-- The coefficient is differentiable at every point with spectral parameter in `Λ`. -/
theorem differentiableAt_coefficient (a : ParameterSymbol n Λ V W m)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) :
    DifferentiableAt ℝ a.coefficient p :=
  (a.contDiffAt_coefficient hp).differentiableAt (by simp)

open scoped Classical in
/-- The derivative of the coefficient in a direction `e` that the dilations scale by `t ^ d`, a
parameter-dependent symbol of order `m - d`. -/
private def fderivApply (a : ParameterSymbol n Λ V W m)
    (e : (CoordinateSpace n × CoordinateSpace n) × ℂ) (d : ℕ)
    (he : ∀ t : ℝ, parameterDilation n t e = t ^ d • e) : ParameterSymbol n Λ V W (m - d) where
  coefficient p := if p.2 ∈ Λ then fderiv ℝ a.coefficient p e else 0
  contDiffOn_coefficient :=
    ((a.contDiffOn_coefficient.fderiv_of_isOpen (isOpen_univ.prod Λ.isOpen) (by simp)).clm_apply
      (contDiffOn_const (c := e))).congr fun p hp => by simp [SetLike.mem_coe.1 hp.2]
  coefficient_of_notMem p hp := by simp [hp]
  exists_bound := by
    refine (Bounds.fderiv_apply Λ.isOpen a.contDiffOn_coefficient a.exists_bound he).congr
      fun p hp => ?_
    filter_upwards [(Λ.isOpen.preimage continuous_snd).mem_nhds hp] with q hq
    have hq' : q.2 ∈ Λ := hq
    simp [hq']

/-- The derivative `∂_v a` of a parameter-dependent symbol in the position direction `v`. It has
the same order `m`: the dilations do not scale the position directions. -/
def spatialDeriv (a : ParameterSymbol n Λ V W m) (v : CoordinateSpace n) :
    ParameterSymbol n Λ V W m :=
  inclusion (by simp) (a.fderivApply ((v, 0), 0) 0 fun t => by simp)

/-- The derivative `∂_w a` of a parameter-dependent symbol in the frequency direction `w`. It has
order `m - 1`: each frequency derivative gains one order. -/
def frequencyDeriv (a : ParameterSymbol n Λ V W m) (w : CoordinateSpace n) :
    ParameterSymbol n Λ V W (m - 1) :=
  inclusion (by simp) (a.fderivApply ((0, w), 0) 1 fun t => by simp)

theorem coefficient_spatialDeriv_eq_fderiv (a : ParameterSymbol n Λ V W m) (v : CoordinateSpace n)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (a.spatialDeriv v).coefficient ((x, ξ), z) = fderiv ℝ a.coefficient ((x, ξ), z) ((v, 0), 0) :=
  by simp [spatialDeriv, fderivApply, hz]

theorem coefficient_frequencyDeriv_eq_fderiv (a : ParameterSymbol n Λ V W m)
    (w : CoordinateSpace n) (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (a.frequencyDeriv w).coefficient ((x, ξ), z) =
      fderiv ℝ a.coefficient ((x, ξ), z) ((0, w), 0) :=
  by simp [frequencyDeriv, fderivApply, hz]

/-- At a spectral parameter in `Λ`, the derivative of the coefficient along a map `g` into the
position-frequency space is the derivative of the coefficient in the direction `g'`. -/
private theorem fderiv_coefficient_comp (a : ParameterSymbol n Λ V W m) {z : ℂ} (hz : z ∈ Λ)
    {g : CoordinateSpace n → CoordinateSpace n × CoordinateSpace n}
    {g' : CoordinateSpace n →L[ℝ] CoordinateSpace n × CoordinateSpace n} {y : CoordinateSpace n}
    (hg : HasFDerivAt g g' y) (v : CoordinateSpace n) :
    fderiv ℝ (fun u => a.coefficient (g u, z)) y v = fderiv ℝ a.coefficient (g y, z) (g' v, 0) := by
  have h : HasFDerivAt (fun u => a.coefficient (g u, z))
      ((fderiv ℝ a.coefficient (g y, z)).comp ((ContinuousLinearMap.inl ℝ _ ℂ).comp g')) y :=
    (a.differentiableAt_coefficient (p := (g y, z)) hz).hasFDerivAt.comp y
      ((hasFDerivAt_prodMk_left (𝕜 := ℝ) (g y) z).comp y hg)
  rw [h.fderiv]
  simp

/-- The spatial derivative is the partial derivative in the position. -/
@[simp]
theorem coefficient_spatialDeriv (a : ParameterSymbol n Λ V W m) (v : CoordinateSpace n)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (a.spatialDeriv v).coefficient ((x, ξ), z) =
      fderiv ℝ (fun y => a.coefficient ((y, ξ), z)) x v := by
  rw [coefficient_spatialDeriv_eq_fderiv a v x ξ hz,
    a.fderiv_coefficient_comp hz (hasFDerivAt_prodMk_left (𝕜 := ℝ) x ξ)]
  simp

/-- The frequency derivative is the partial derivative in the frequency. -/
@[simp]
theorem coefficient_frequencyDeriv (a : ParameterSymbol n Λ V W m) (w : CoordinateSpace n)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (a.frequencyDeriv w).coefficient ((x, ξ), z) =
      fderiv ℝ (fun η => a.coefficient ((x, η), z)) ξ w := by
  rw [coefficient_frequencyDeriv_eq_fderiv a w x ξ hz,
    a.fderiv_coefficient_comp hz (hasFDerivAt_prodMk_right (𝕜 := ℝ) x ξ)]
  simp

/-! The spatial and frequency derivatives are linear in the symbol and commute with the
inclusions between orders. -/

@[simp]
theorem zero_spatialDeriv (v : CoordinateSpace n) :
    (0 : ParameterSymbol n Λ V W m).spatialDeriv v = 0 :=
  ext_of_mem fun x ξ z hz => by simp [coefficient_spatialDeriv_eq_fderiv _ _ _ _ hz]

@[simp]
theorem add_spatialDeriv (a b : ParameterSymbol n Λ V W m) (v : CoordinateSpace n) :
    (a + b).spatialDeriv v = a.spatialDeriv v + b.spatialDeriv v :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ _ _ hz,
      fderiv_add (a.differentiableAt_coefficient (p := ((x, ξ), z)) hz)
        (b.differentiableAt_coefficient (p := ((x, ξ), z)) hz)]

@[simp]
theorem smul_spatialDeriv (c : ℂ) (a : ParameterSymbol n Λ V W m) (v : CoordinateSpace n) :
    (c • a).spatialDeriv v = c • a.spatialDeriv v :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ _ _ hz,
      fderiv_const_smul (a.differentiableAt_coefficient (p := ((x, ξ), z)) hz)]

@[simp]
theorem neg_spatialDeriv (a : ParameterSymbol n Λ V W m) (v : CoordinateSpace n) :
    (-a).spatialDeriv v = -a.spatialDeriv v :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ _ _ hz, coefficient_neg, fderiv_neg]

@[simp]
theorem sub_spatialDeriv (a b : ParameterSymbol n Λ V W m) (v : CoordinateSpace n) :
    (a - b).spatialDeriv v = a.spatialDeriv v - b.spatialDeriv v := by
  simp [sub_eq_add_neg]

@[simp]
theorem spatialDeriv_inclusion (h : m ≤ m') (a : ParameterSymbol n Λ V W m)
    (v : CoordinateSpace n) : (inclusion h a).spatialDeriv v = inclusion h (a.spatialDeriv v) :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_spatialDeriv_eq_fderiv _ _ _ _ hz, coefficient_inclusion]

@[simp]
theorem zero_frequencyDeriv (w : CoordinateSpace n) :
    (0 : ParameterSymbol n Λ V W m).frequencyDeriv w = 0 :=
  ext_of_mem fun x ξ z hz => by simp [coefficient_frequencyDeriv_eq_fderiv _ _ _ _ hz]

@[simp]
theorem add_frequencyDeriv (a b : ParameterSymbol n Λ V W m) (w : CoordinateSpace n) :
    (a + b).frequencyDeriv w = a.frequencyDeriv w + b.frequencyDeriv w :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ _ _ hz,
      fderiv_add (a.differentiableAt_coefficient (p := ((x, ξ), z)) hz)
        (b.differentiableAt_coefficient (p := ((x, ξ), z)) hz)]

@[simp]
theorem smul_frequencyDeriv (c : ℂ) (a : ParameterSymbol n Λ V W m) (w : CoordinateSpace n) :
    (c • a).frequencyDeriv w = c • a.frequencyDeriv w :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ _ _ hz,
      fderiv_const_smul (a.differentiableAt_coefficient (p := ((x, ξ), z)) hz)]

@[simp]
theorem neg_frequencyDeriv (a : ParameterSymbol n Λ V W m) (w : CoordinateSpace n) :
    (-a).frequencyDeriv w = -a.frequencyDeriv w :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ _ _ hz, coefficient_neg, fderiv_neg]

@[simp]
theorem sub_frequencyDeriv (a b : ParameterSymbol n Λ V W m) (w : CoordinateSpace n) :
    (a - b).frequencyDeriv w = a.frequencyDeriv w - b.frequencyDeriv w := by
  simp [sub_eq_add_neg]

@[simp]
theorem frequencyDeriv_inclusion (h : m ≤ m') (a : ParameterSymbol n Λ V W m)
    (w : CoordinateSpace n) :
    (inclusion h a).frequencyDeriv w = inclusion (sub_le_sub_right h 1) (a.frequencyDeriv w) :=
  ext_of_mem fun x ξ z hz => by
    simp [coefficient_frequencyDeriv_eq_fderiv _ _ _ _ hz, coefficient_inclusion]

/-! ### Smoothing symbols -/

/-- A parameter-dependent symbol is *smoothing*, or of order `-∞`, if its coefficient is a
parameter-dependent symbol of every real order: the estimates
`‖∂ₓ^α ∂_ξ^β ∂_z^γ a((x, ξ), z)‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-N)` hold for every `N`, so the
symbol decays rapidly in the frequency and the spectral parameter jointly. -/
def IsSmoothing (a : ParameterSymbol n Λ V W m) : Prop :=
  ∀ m' : ℝ, ∃ b : ParameterSymbol n Λ V W m', b.coefficient = a.coefficient

theorem isSmoothing_iff {a : ParameterSymbol n Λ V W m} :
    a.IsSmoothing ↔ ∀ m' : ℝ, ∃ b : ParameterSymbol n Λ V W m', b.coefficient = a.coefficient :=
  Iff.rfl

/-- The estimates characterizing parameter-dependent smoothing symbols: a symbol is smoothing
exactly when, for every real order `m'`, every compact set `K` of positions and every derivative
order `k`, the dilated derivatives of order `k` are bounded by `C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ m'`
for all `x ∈ K`, all frequencies `ξ` and all `z ∈ Λ`. -/
theorem isSmoothing_iff_forall_exists_bound {a : ParameterSymbol n Λ V W m} :
    a.IsSmoothing ↔ ∀ m' : ℝ, ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
        ‖parameterIteratedFDeriv k a.coefficient ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m' := by
  refine ⟨fun h m' K hK k => ?_, fun h m' =>
    ⟨⟨a.coefficient, a.contDiffOn_coefficient, a.coefficient_of_notMem, h m'⟩, rfl⟩⟩
  obtain ⟨b, hb⟩ := h m'
  exact hb ▸ b.exists_bound K hK k

/-- A parameter-dependent symbol is smoothing iff for every `N` its coefficient is that of a
parameter-dependent symbol of order `m - N`. -/
theorem isSmoothing_iff_forall_nat {a : ParameterSymbol n Λ V W m} :
    a.IsSmoothing ↔
      ∀ N : ℕ, ∃ b : ParameterSymbol n Λ V W (m - N), b.coefficient = a.coefficient := by
  refine ⟨fun h N => h _, fun h m' => (h ⌈m - m'⌉₊).elim fun b hb => ?_⟩
  exact ⟨inclusion (by linarith [Nat.le_ceil (m - m')]) b, by rw [coefficient_inclusion, hb]⟩

@[simp]
theorem isSmoothing_zero : (0 : ParameterSymbol n Λ V W m).IsSmoothing :=
  fun _ => ⟨0, rfl⟩

theorem IsSmoothing.add {a b : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (hb : b.IsSmoothing) : (a + b).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  obtain ⟨b', hb'⟩ := hb m'
  exact ⟨a' + b', by simp [ha', hb']⟩

theorem IsSmoothing.smul {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing) (c : ℂ) :
    (c • a).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  exact ⟨c • a', by simp [ha']⟩

theorem IsSmoothing.neg {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing) :
    (-a).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  exact ⟨-a', by simp [ha']⟩

@[simp]
theorem isSmoothing_neg_iff {a : ParameterSymbol n Λ V W m} : (-a).IsSmoothing ↔ a.IsSmoothing :=
  ⟨fun ha => neg_neg a ▸ ha.neg, IsSmoothing.neg⟩

theorem IsSmoothing.sub {a b : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (hb : b.IsSmoothing) : (a - b).IsSmoothing := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem IsSmoothing.inclusion {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing) (h : m ≤ m') :
    (inclusion h a).IsSmoothing :=
  fun m'' => (ha m'').imp fun _ hb => by rw [hb, coefficient_inclusion]

/-- Including a parameter-dependent symbol into a higher order does not change whether it is
smoothing. -/
@[simp]
theorem isSmoothing_inclusion_iff {a : ParameterSymbol n Λ V W m} {h : m ≤ m'} :
    (inclusion h a).IsSmoothing ↔ a.IsSmoothing :=
  ⟨fun ha m'' => (ha m'').imp fun _ hb => by rw [hb, coefficient_inclusion], (·.inclusion h)⟩

theorem IsSmoothing.spatialDeriv {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (v : CoordinateSpace n) : (a.spatialDeriv v).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha m'
  refine ⟨a'.spatialDeriv v, funext fun ⟨⟨x, ξ⟩, z⟩ => ?_⟩
  by_cases hz : z ∈ Λ
  · simp [coefficient_spatialDeriv_eq_fderiv _ _ _ _ hz, ha']
  · rw [coefficient_of_notMem _ _ hz, coefficient_of_notMem _ _ hz]

theorem IsSmoothing.frequencyDeriv {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (w : CoordinateSpace n) : (a.frequencyDeriv w).IsSmoothing := fun m' => by
  obtain ⟨a', ha'⟩ := ha (m' + 1)
  refine ⟨ParameterSymbol.inclusion (by linarith) (a'.frequencyDeriv w),
    funext fun ⟨⟨x, ξ⟩, z⟩ => ?_⟩
  rw [coefficient_inclusion]
  by_cases hz : z ∈ Λ
  · simp [coefficient_frequencyDeriv_eq_fderiv _ _ _ _ hz, ha']
  · rw [coefficient_of_notMem _ _ hz, coefficient_of_notMem _ _ hz]

/-- Smoothing symbols form a right ideal under composition. -/
theorem IsSmoothing.comp_right {b : ParameterSymbol n Λ W U m'} (hb : b.IsSmoothing)
    (a : ParameterSymbol n Λ V W m) : (b.comp a).IsSmoothing := fun m'' => by
  obtain ⟨b', hb'⟩ := hb (m'' - m)
  exact ⟨ParameterSymbol.inclusion (by linarith) (b'.comp a), funext fun p => by simp [hb']⟩

/-- Smoothing symbols form a left ideal under composition. -/
theorem IsSmoothing.comp_left {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (b : ParameterSymbol n Λ W U m') : (b.comp a).IsSmoothing := fun m'' => by
  obtain ⟨a', ha'⟩ := ha (m'' - m')
  exact ⟨ParameterSymbol.inclusion (by linarith) (b.comp a'), funext fun p => by simp [ha']⟩

/-! ### Parameter-ellipticity and the inverse -/

/-- A parameter-dependent symbol of order `m` is *elliptic with parameter* if its values are
invertible at every point with spectral parameter in `Λ`, and the inverse satisfies the bound of
order `-m`, locally uniformly in the position:
`‖a((x, ξ), z)⁻¹‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-m)`. -/
structure IsElliptic (a : ParameterSymbol n Λ V W m) : Prop where
  isInvertible : ∀ x ξ, ∀ z ∈ Λ, (a.coefficient ((x, ξ), z)).IsInvertible
  exists_bound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
    ‖(a.coefficient ((x, ξ), z)).inverse‖ ≤ C * parameterWeight ξ z ^ (-m)

/-- **The inverse of a parameter-elliptic symbol.** The pointwise inverse
`((x, ξ), z) ↦ a((x, ξ), z)⁻¹` of a symbol of order `m` that is elliptic with parameter is a
parameter-dependent symbol of order `-m`. -/
def inverse [CompleteSpace V] (a : ParameterSymbol n Λ V W m) (ha : a.IsElliptic) :
    ParameterSymbol n Λ W V (-m) where
  coefficient p := (a.coefficient p).inverse
  contDiffOn_coefficient :=
    a.contDiffOn_coefficient.clm_inverse fun p hp => ha.isInvertible _ _ _ hp.2
  coefficient_of_notMem p hp := by
    rw [a.coefficient_of_notMem p hp, ContinuousLinearMap.inverse_zero]
  exists_bound := by
    exact Bounds.inverse Λ.isOpen a.contDiffOn_coefficient a.exists_bound
      (fun p hp => ha.isInvertible _ _ _ hp) ha.exists_bound

@[simp]
theorem coefficient_inverse [CompleteSpace V] (a : ParameterSymbol n Λ V W m) (ha : a.IsElliptic)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.inverse ha).coefficient p = (a.coefficient p).inverse := (rfl)

theorem coefficient_comp_coefficient_inverse [CompleteSpace V] {a : ParameterSymbol n Λ V W m}
    (ha : a.IsElliptic) (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (a.coefficient ((x, ξ), z)).comp ((a.inverse ha).coefficient ((x, ξ), z)) =
      ContinuousLinearMap.id ℂ W :=
  (ha.isInvertible x ξ z hz).self_comp_inverse

theorem coefficient_inverse_comp_coefficient [CompleteSpace V] {a : ParameterSymbol n Λ V W m}
    (ha : a.IsElliptic) (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ((a.inverse ha).coefficient ((x, ξ), z)).comp (a.coefficient ((x, ξ), z)) =
      ContinuousLinearMap.id ℂ V :=
  (ha.isInvertible x ξ z hz).inverse_comp_self

/-! ### The shifted Laplacian and its resolvent -/

/-- The scalar symbol `(s + ‖ξ‖²) - z` of `s - Δ - z`, as a function on all of `ℝⁿ × ℝⁿ × ℂ`. -/
private def laplacianSymbol (s : ℝ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) : ℂ :=
  ((s + ‖p.1.2‖ ^ 2 : ℝ) : ℂ) - p.2

private theorem contDiff_laplacianSymbol (s : ℝ) :
    ContDiff ℝ ∞ (laplacianSymbol (n := n) s) := by
  unfold laplacianSymbol
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.add
    ((contDiff_norm_sq ℝ).comp (contDiff_snd.comp contDiff_fst)))).sub contDiff_snd

/-- The scalar symbol `(s + ‖ξ‖²) - z` has order `2`: it is the constant `s` plus the function
`‖ξ‖² - z`, which is quasi-homogeneous of degree `2`. -/
private theorem bounds_laplacianSymbol (Λ : Set ℂ) (hΛ : IsOpen Λ) (s : ℝ) :
    Bounds Λ 2 (laplacianSymbol (n := n) s) := by
  have hg : ContDiff ℝ ∞ fun p : (CoordinateSpace n × CoordinateSpace n) × ℂ =>
      ((‖p.1.2‖ ^ 2 : ℝ) : ℂ) - p.2 :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).comp
      (contDiff_snd.comp contDiff_fst))).sub contDiff_snd
  have hhom (t : ℝ) (ht : 0 < t) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
      ((‖(parameterDilation n t p).1.2‖ ^ 2 : ℝ) : ℂ) - (parameterDilation n t p).2 =
        t ^ (2 : ℝ) • (((‖p.1.2‖ ^ 2 : ℝ) : ℂ) - p.2) := by
    simp [parameterDilation_apply, norm_smul, abs_of_pos ht, smul_sub, Complex.real_smul,
      mul_pow]
  refine (Bounds.add hΛ contDiffOn_const hg.contDiffOn
    ((bounds_const (Λ := Λ) (s : ℂ)).mono zero_le_two)
    (bounds_of_quasiHomogeneous Λ hg hhom)).congr fun p _ => Filter.Eventually.of_forall
      fun q => ?_
  simp only [laplacianSymbol, Complex.ofReal_add]
  ring

/-- The sector estimate for a real `q ≥ μ ‖ξ‖²`, `μ > 0`: for a spectral parameter `z` in the
sector `Re z ≤ c ‖z‖`, `c < 1`, with `δ ≤ q + ‖z‖`, `δ > 0`, the modulus of `q - z` is at least a
fixed multiple of the squared weight. -/
private theorem mul_parameterWeight_sq_le_norm_ofReal_sub {q μ c δ : ℝ} (hμ : 0 < μ) (hc : c < 1)
    (hδ : 0 < δ) {ξ : CoordinateSpace n} {z : ℂ} (hq : μ * ‖ξ‖ ^ 2 ≤ q) (hz : z.re ≤ c * ‖z‖)
    (hzδ : δ ≤ q + ‖z‖) :
    (1 - max c (-1)) / 2 / (3 * (1 + μ⁻¹ + δ⁻¹)) * parameterWeight ξ z ^ 2 ≤ ‖(q : ℂ) - z‖ := by
  set c₀ := max c (-1)
  have hc₀' : c₀ < 1 := max_lt hc (by norm_num)
  have hq₀ : 0 ≤ q := (mul_nonneg hμ.le (sq_nonneg _)).trans hq
  -- Sector estimate: `‖q - z‖ ≥ (1 - c₀) / 2 * (‖z‖ + q)`.
  have hsector : (1 - c₀) / 2 * (‖z‖ + q) ≤ ‖(q : ℂ) - z‖ := by
    simpa only [add_comm q] using Complex.mul_add_norm_le_norm_ofReal_sub hq₀ hz
  -- Weight estimate: `w² ≤ 3 (1 + ‖ξ‖² + ‖z‖) ≤ 3 (1 + μ⁻¹ + δ⁻¹) (‖z‖ + q)`.
  have hw : parameterWeight ξ z ^ 2 ≤ 3 * (1 + μ⁻¹ + δ⁻¹) * (‖z‖ + q) := by
    have hsqrt := Real.sq_sqrt (norm_nonneg z)
    have h3 : parameterWeight ξ z ^ 2 ≤ 3 * (1 + ‖ξ‖ ^ 2 + ‖z‖) := by
      rw [parameterWeight_def]
      nlinarith [sq_nonneg (1 - ‖ξ‖), sq_nonneg (1 - Real.sqrt ‖z‖),
        sq_nonneg (‖ξ‖ - Real.sqrt ‖z‖)]
    have h1 : 1 ≤ δ⁻¹ * (‖z‖ + q) := by
      rw [inv_mul_eq_div, one_le_div hδ]
      linarith
    have hξ : ‖ξ‖ ^ 2 ≤ μ⁻¹ * (‖z‖ + q) := by
      rw [inv_mul_eq_div, le_div_iff₀ hμ]
      nlinarith [norm_nonneg z]
    nlinarith [norm_nonneg z, inv_pos.2 hμ, inv_pos.2 hδ]
  have hκ : 0 < 3 * (1 + μ⁻¹ + δ⁻¹) := by positivity
  calc (1 - c₀) / 2 / (3 * (1 + μ⁻¹ + δ⁻¹)) * parameterWeight ξ z ^ 2
      ≤ (1 - c₀) / 2 / (3 * (1 + μ⁻¹ + δ⁻¹)) * (3 * (1 + μ⁻¹ + δ⁻¹) * (‖z‖ + q)) :=
        mul_le_mul_of_nonneg_left hw (div_nonneg (by linarith) hκ.le)
    _ = (1 - c₀) / 2 * (‖z‖ + q) := by field_simp
    _ ≤ _ := hsector

variable (V) in
/-- **Inverse estimate in a sector.** Let `q ≥ μ ‖ξ‖²` be real, `μ > 0`, and let the spectral
parameter `z` lie in the sector `Re z ≤ c ‖z‖`, `c < 1`, with `δ ≤ q + ‖z‖`, `δ > 0`. Then
`(q - z) • id` is invertible, with inverse bounded by `κ⁻¹ w ^ (-2)` for
`κ = (1 - max c (-1)) / 2 / (3 (1 + μ⁻¹ + δ⁻¹))` and `w = 1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)`. This is the
pointwise ellipticity estimate for symbols `q • id - z` with real scalar principal part, such as
`TauCeti.ParameterSymbol.shiftedLaplacian`. -/
theorem isInvertible_ofReal_sub_smul_id_and_norm_inverse_le {q μ c δ : ℝ} (hμ : 0 < μ)
    (hc : c < 1) (hδ : 0 < δ) {ξ : CoordinateSpace n} {z : ℂ} (hq : μ * ‖ξ‖ ^ 2 ≤ q)
    (hz : z.re ≤ c * ‖z‖) (hzδ : δ ≤ q + ‖z‖) :
    (((q : ℂ) - z) • ContinuousLinearMap.id ℂ V).IsInvertible ∧
      ‖(((q : ℂ) - z) • ContinuousLinearMap.id ℂ V).inverse‖ ≤
        ((1 - max c (-1)) / 2 / (3 * (1 + μ⁻¹ + δ⁻¹)))⁻¹ * parameterWeight ξ z ^ (-2 : ℝ) := by
  set κ := (1 - max c (-1)) / 2 / (3 * (1 + μ⁻¹ + δ⁻¹))
  have hκ : 0 < κ := div_pos (by linarith [max_lt hc (by norm_num : (-1 : ℝ) < 1)])
    (by positivity)
  have hw := pow_pos (parameterWeight_pos ξ z) 2
  have hle := mul_parameterWeight_sq_le_norm_ofReal_sub hμ hc hδ hq hz hzδ
  have hne : (q : ℂ) - z ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hle
    exact (mul_pos hκ hw).not_ge hle
  refine ⟨(ContinuousLinearMap.isInvertible_smul_iff hne).2
    (ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)), ?_⟩
  rw [ContinuousLinearMap.inverse_smul, ContinuousLinearMap.inverse_id,
    Real.rpow_neg (parameterWeight_pos ξ z).le, Real.rpow_two]
  calc ‖((q : ℂ) - z)⁻¹ • ContinuousLinearMap.id ℂ V‖
      ≤ ‖((q : ℂ) - z)⁻¹‖ := (ContinuousLinearMap.opNorm_smul_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le)
    _ = ‖(q : ℂ) - z‖⁻¹ := norm_inv _
    _ ≤ (κ * parameterWeight ξ z ^ 2)⁻¹ := inv_anti₀ (mul_pos hκ hw) hle
    _ = κ⁻¹ * (parameterWeight ξ z ^ 2)⁻¹ := mul_inv _ _

open scoped Classical in
variable (V) in
/-- The parameter-dependent symbol `((s + ‖ξ‖²) - z) • id` of order `2` of the family `s - Δ - z`
acting on `V`-valued functions, where `Δ` is the Euclidean Laplacian. -/
def shiftedLaplacian (s : ℝ) : ParameterSymbol n Λ V V 2 where
  coefficient p := if p.2 ∈ Λ then
    (((s + ‖p.1.2‖ ^ 2 : ℝ) : ℂ) - p.2) • ContinuousLinearMap.id ℂ V else 0
  contDiffOn_coefficient := by
    refine (((contDiff_laplacianSymbol s).smul
      (contDiff_const (c := ContinuousLinearMap.id ℂ V))).contDiffOn
      (s := univ ×ˢ (Λ : Set ℂ))).congr fun p hp => ?_
    simp [laplacianSymbol, SetLike.mem_coe.1 hp.2]
  coefficient_of_notMem p hp := by simp [hp]
  exists_bound := by
    refine (Bounds.comp_left Λ.isOpen
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
        (ContinuousLinearMap.id ℂ V)).restrictScalars ℝ) (contDiff_laplacianSymbol s).contDiffOn
      (bounds_laplacianSymbol Λ Λ.isOpen s)).congr fun p hp => ?_
    filter_upwards [(Λ.isOpen.preimage continuous_snd).mem_nhds hp] with q hq
    have hq' : q.2 ∈ Λ := hq
    simp [laplacianSymbol, hq']

@[simp]
theorem coefficient_shiftedLaplacian (s : ℝ) (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).coefficient ((x, ξ), z) =
      (((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z) • ContinuousLinearMap.id ℂ V :=
  by simp [shiftedLaplacian, hz]

/-- **Parameter-ellipticity of the shifted Laplacian.** For `0 ≤ s`, the symbol of `s - Δ - z`
is elliptic with parameter on every open set `Λ` of spectral parameters in a sector
`Re z ≤ c ‖z‖`, `c < 1`, around the negative real axis, on which moreover `δ ≤ s + ‖z‖` for some
`δ > 0`. The last condition holds for every such sector when `s > 0` and for its part outside
the ball of radius `δ` about `0` when `s = 0`. -/
theorem isElliptic_shiftedLaplacian {s c δ : ℝ} (hs : 0 ≤ s) (hc : c < 1) (hδ : 0 < δ)
    (hΛ : ∀ z ∈ Λ, z.re ≤ c * ‖z‖ ∧ δ ≤ s + ‖z‖) :
    (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).IsElliptic := by
  have h (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :=
    isInvertible_ofReal_sub_smul_id_and_norm_inverse_le V one_pos hc hδ
      (q := s + ‖ξ‖ ^ 2) (by linarith) (hΛ z hz).1 (by linarith [(hΛ z hz).2, sq_nonneg ‖ξ‖])
  refine ⟨fun x ξ z hz => ?_, fun K _ =>
    ⟨((1 - max c (-1)) / 2 / (3 * (1 + 1⁻¹ + δ⁻¹)))⁻¹, fun x _ ξ z hz => ?_⟩⟩
  · rw [coefficient_shiftedLaplacian s x ξ hz]
    exact (h x ξ hz).1
  · rw [coefficient_shiftedLaplacian s x ξ hz]
    exact (h x ξ hz).2

/-- **Parameter-ellipticity of the shifted Laplacian near the negative real axis.** For `δ > 0`,
the symbol of `s - Δ - z` is elliptic with parameter on every open set `Λ` of spectral parameters
in the half plane `Re z ≤ s - δ`. Unlike the sectors of
`TauCeti.ParameterSymbol.isElliptic_shiftedLaplacian`, such a set may contain `0` when `δ < s`,
and so a neighbourhood of the closed negative real axis. -/
theorem isElliptic_shiftedLaplacian_of_re_le {s δ : ℝ} (hδ : 0 < δ)
    (hΛ : ∀ z ∈ Λ, z.re ≤ s - δ) :
    (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).IsElliptic := by
  -- Write `(s + ‖ξ‖²) - z = (δ + ‖ξ‖²) - (z - (s - δ))`, with `z - (s - δ)` in the left half plane.
  have heq (ξ : CoordinateSpace n) (z : ℂ) :
      (((δ + ‖ξ‖ ^ 2 : ℝ) : ℂ) - (z - (s - δ : ℝ))) = ((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z := by
    push_cast
    ring
  have h (ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :=
    isInvertible_ofReal_sub_smul_id_and_norm_inverse_le V one_pos zero_lt_one hδ
      (q := δ + ‖ξ‖ ^ 2) (z := z - (s - δ : ℝ)) (by linarith)
      (by simp only [Complex.sub_re, Complex.ofReal_re, zero_mul]; linarith [hΛ z hz])
      (by linarith [norm_nonneg (z - (s - δ : ℝ)), sq_nonneg ‖ξ‖])
  refine ⟨fun x ξ z hz ↦ ?_, fun K _ ↦
    ⟨((1 - max 0 (-1)) / 2 / (3 * (1 + 1⁻¹ + δ⁻¹)))⁻¹ * (1 + Real.sqrt ‖((s - δ : ℝ) : ℂ)‖) ^ 2,
      fun x _ ξ z hz ↦ ?_⟩⟩
  · rw [coefficient_shiftedLaplacian s x ξ hz, ← heq]
    exact (h ξ hz).1
  · rw [coefficient_shiftedLaplacian s x ξ hz, ← heq, mul_assoc]
    refine (h ξ hz).2.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num; positivity))
    simpa using parameterWeight_rpow_le_mul_parameterWeight_add_rpow ξ (z - (s - δ : ℝ))
      ((s - δ : ℝ) : ℂ) (by norm_num : (-2 : ℝ) ≤ 0)

/-- The coefficient of the resolvent symbol: the inverse of the symbol of `s - Δ - z` is
`((s + ‖ξ‖²) - z)⁻¹ • id`, a parameter-dependent symbol of order `-2`. -/
theorem coefficient_inverse_shiftedLaplacian [CompleteSpace V] {s : ℝ}
    (h : (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).IsElliptic) (x ξ : CoordinateSpace n)
    {z : ℂ} (hz : z ∈ Λ) :
    ((shiftedLaplacian V s).inverse h).coefficient ((x, ξ), z) =
      (((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z)⁻¹ • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_inverse, coefficient_shiftedLaplacian s x ξ hz,
    ContinuousLinearMap.inverse_smul, ContinuousLinearMap.inverse_id]

/-- The symbol of `s - Δ - z` does not depend on the position. -/
@[simp]
theorem spatialDeriv_shiftedLaplacian (s : ℝ) (v : CoordinateSpace n) :
    (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).spatialDeriv v = 0 :=
  ext_of_mem fun x ξ z hz => by simp [coefficient_spatialDeriv _ _ _ _ hz, hz]

/-! ### Quasi-homogeneous symbols -/

open scoped Classical in
/-- A smooth function `f((x, ξ), z)` that is quasi-homogeneous of degree `m`,
`f((x, t ξ), t² z) = t ^ m f((x, ξ), z)` for `t > 0`, as a parameter-dependent symbol of order `m`
on `Λ`. Examples are the spectral parameter `z` itself, of order `2`
(`TauCeti.ParameterSymbol.spectralParameter`), and homogeneous polynomials of degree `m` in `ξ`
with coefficients depending on the position, the single summands of the symbol of a differential
operator; the symbol of a general differential operator is assembled from these in
`TauCeti.ParameterSymbol.ofDifferentialSymbol`. -/
def ofQuasiHomogeneous (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ t : ℝ, 0 < t → ∀ p, f (parameterDilation n t p) = t ^ m • f p) :
    ParameterSymbol n Λ V W m where
  coefficient p := if p.2 ∈ Λ then f p else 0
  contDiffOn_coefficient := hf.contDiffOn.congr fun p hp => by simp [SetLike.mem_coe.1 hp.2]
  coefficient_of_notMem p hp := by simp [hp]
  exists_bound := by
    refine (bounds_of_quasiHomogeneous Λ hf hhom).congr fun p hp => ?_
    filter_upwards [(Λ.isOpen.preimage continuous_snd).mem_nhds hp] with q hq
    have hq' : q.2 ∈ Λ := hq
    simp [hq']

@[simp]
theorem coefficient_ofQuasiHomogeneous
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ t : ℝ, 0 < t → ∀ p, f (parameterDilation n t p) = t ^ m • f p)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (ofQuasiHomogeneous f hf hhom : ParameterSymbol n Λ V W m).coefficient ((x, ξ), z) =
      f ((x, ξ), z) := by
  simp [ofQuasiHomogeneous, hz]

/-! ### The spectral parameter -/

variable (V) in
/-- The spectral parameter `z • id` as a parameter-dependent symbol of order `2`: a spectral
parameter counts as two frequency orders. -/
def spectralParameter : ParameterSymbol n Λ V V 2 :=
  ofQuasiHomogeneous (fun p => p.2 • ContinuousLinearMap.id ℂ V)
    (contDiff_snd.smul contDiff_const) fun t _ p => by
      rw [parameterDilation_apply, Real.rpow_two, smul_assoc]

@[simp]
theorem coefficient_spectralParameter (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (spectralParameter V : ParameterSymbol n Λ V V 2).coefficient ((x, ξ), z) =
      z • ContinuousLinearMap.id ℂ V :=
  coefficient_ofQuasiHomogeneous _ _ _ x ξ hz

/-- The spectral parameter does not depend on the position. -/
@[simp]
theorem spatialDeriv_spectralParameter (v : CoordinateSpace n) :
    (spectralParameter V : ParameterSymbol n Λ V V 2).spatialDeriv v = 0 :=
  ext_of_mem fun x ξ z hz => by simp [coefficient_spatialDeriv _ _ _ _ hz, hz]

/-! ### Lower-order perturbations -/

/-- **Lower-order perturbations of parameter-elliptic symbols.** Let `a` be a symbol of order `m`
that is invertible with `‖a((x, ξ), z)⁻¹‖ ≤ C w ^ (-m)`, and `r` a symbol with
`‖r((x, ξ), z)‖ ≤ D w ^ (m - 1)`, both uniformly in the position, where
`w = 1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)`. If `2 C D ≤ 1 + ‖z‖ ^ (1 / 2)` for every `z ∈ Λ`, then `a + r` is
elliptic with parameter: the relative size `‖a⁻¹ r‖` of the perturbation is at most `C D / w`,
at most `1 / 2` at spectral parameters of large modulus. -/
theorem isElliptic_add [CompleteSpace V] {a r : ParameterSymbol n Λ V W m} {C D : ℝ}
    (ha : ∀ x ξ, ∀ z ∈ Λ, (a.coefficient ((x, ξ), z)).IsInvertible)
    (hC : ∀ x ξ, ∀ z ∈ Λ,
      ‖(a.coefficient ((x, ξ), z)).inverse‖ ≤ C * parameterWeight ξ z ^ (-m))
    (hD : ∀ x ξ, ∀ z ∈ Λ, ‖r.coefficient ((x, ξ), z)‖ ≤ D * parameterWeight ξ z ^ (m - 1))
    (hΛ : ∀ z ∈ Λ, 2 * C * D ≤ 1 + Real.sqrt ‖z‖) : (a + r).IsElliptic := by
  have key (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
      C * parameterWeight ξ z ^ (-m) *
        ‖(a + r).coefficient ((x, ξ), z) - a.coefficient ((x, ξ), z)‖ ≤ 1 / 2 := by
    have ht := parameterWeight_pos ξ z
    have hp (s : ℝ) := Real.rpow_pos_of_pos ht s
    have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC x ξ z hz)) (hp _)
    have hw : 1 + Real.sqrt ‖z‖ ≤ parameterWeight ξ z := by
      rw [parameterWeight_def]
      linarith [norm_nonneg ξ]
    rw [coefficient_add, Pi.add_apply, add_sub_cancel_left]
    calc C * parameterWeight ξ z ^ (-m) * ‖r.coefficient ((x, ξ), z)‖
        ≤ C * parameterWeight ξ z ^ (-m) * (D * parameterWeight ξ z ^ (m - 1)) := by
          gcongr
          exact hD x ξ z hz
      _ = C * D * parameterWeight ξ z ^ (-m + (m - 1)) := by
          rw [Real.rpow_add ht]
          ring
      _ = C * D / parameterWeight ξ z := by
          rw [show -m + (m - 1) = -1 by ring, Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ ht]
          linarith [hΛ z hz]
  refine ⟨fun x ξ z hz => (ha x ξ z hz).of_mul_norm_sub_lt (hC x ξ z hz)
    ((key x ξ hz).trans_lt (by norm_num)), fun K _ => ⟨2 * C, fun x _ ξ z hz => ?_⟩⟩
  refine ((ha x ξ z hz).norm_inverse_le_of_mul_norm_sub_lt (hC x ξ z hz)
    ((key x ξ hz).trans_lt (by norm_num))).trans ?_
  have hM : 0 ≤ C * parameterWeight ξ z ^ (-m) := (norm_nonneg _).trans (hC x ξ z hz)
  rw [div_le_iff₀ (by linarith [key x ξ hz])]
  nlinarith [key x ξ hz]

end ParameterSymbol


end TauCeti
