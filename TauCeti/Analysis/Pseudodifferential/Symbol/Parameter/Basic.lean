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

* `TauCeti.ParameterSymbol.inclusion`: the order inclusions, and the complex vector space
  structure of each class;
* `TauCeti.exists_norm_parameterIteratedFDeriv_bilinear_le`: the **Leibniz rule** at one point
  for the dilated derivatives, with a constant independent of the functions, the point and the
  bounds;
* `TauCeti.ParameterSymbol.comp`: the pointwise composition of symbols of orders `m'` and `m` has
  order `m' + m`;
* `TauCeti.ParameterSymbol.IsSmoothing`: the predicate of having every order, closed under
  addition, scalar multiplication and composition with arbitrary symbols;
* `TauCeti.ParameterSymbol.inverse`: **uniform inverse estimates**. If `a` has order `m` and is
  elliptic with parameter (`TauCeti.ParameterSymbol.IsElliptic`: it is invertible, with
  `‖a⁻¹‖ ≤ C (1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-m)`), its pointwise inverse has order `-m`;
* `TauCeti.ParameterSymbol.shiftedLaplacian`, `TauCeti.ParameterSymbol.isElliptic_shiftedLaplacian`:
  for `s ≥ 0` the symbol `(s + ‖ξ‖²) - z` of `s - Δ - z` has order `2` and is elliptic with
  parameter on every sector `Re z ≤ c ‖z‖`, `c < 1`, on which `s + ‖z‖` is bounded below by a
  positive constant. Hence the resolvent symbol `((s + ‖ξ‖²) - z)⁻¹` has order `-2`
  (`TauCeti.ParameterSymbol.coefficient_inverse_shiftedLaplacian`). For `s = 0` it is the principal
  resolvent symbol `(‖ξ‖² - z)⁻¹`, which keeps its low-frequency values: at `ξ = 0` it is `1` for
  `z = -1` and `1 / 2` for `z = -2`.

## Implementation notes

The estimates are proved at one point `p = ((x, ξ), z)` at a time. Pulling a function back along
`v ↦ p + parameterDilation n t v`, with `t` the weight at `p`, turns the dilated derivatives at
`p` into ordinary iterated derivatives at `0`
(`TauCeti.parameterIteratedFDeriv_eq_iteratedFDeriv_comp`), where the uniform Leibniz bound
`TauCeti.exists_norm_iteratedFDeriv_bilinear_le` applies. The inverse estimates come from
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

/-- Where the quasi-norm `‖ξ‖⁴ + ‖z‖²` is at least `t⁴`, the weight is at least `t`. -/
theorem le_parameterWeight_of_pow_four_le {t : ℝ} {ξ : CoordinateSpace n} {z : ℂ}
    (h : t ^ 4 ≤ ‖ξ‖ ^ 4 + ‖z‖ ^ 2) : t ≤ parameterWeight ξ z := by
  have ha := norm_nonneg ξ
  have hb := Real.sqrt_nonneg ‖z‖
  have hz : ‖z‖ ^ 2 = Real.sqrt ‖z‖ ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (norm_nonneg z)]
  refine le_of_pow_le_pow_left₀ four_ne_zero (parameterWeight_pos ξ z).le (h.trans ?_)
  rw [hz, parameterWeight_def]
  calc ‖ξ‖ ^ 4 + Real.sqrt ‖z‖ ^ 4 ≤ (‖ξ‖ + Real.sqrt ‖z‖) ^ 4 :=
        pow_add_pow_le ha hb four_ne_zero
    _ ≤ (1 + ‖ξ‖ + Real.sqrt ‖z‖) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4

/-- Where the quasi-norm `‖ξ‖⁴ + ‖z‖²` is at most `s⁴`, the weight is at most `1 + 2 s`. -/
theorem parameterWeight_le_of_le_pow_four {s : ℝ} (hs : 0 ≤ s) {ξ : CoordinateSpace n} {z : ℂ}
    (h : ‖ξ‖ ^ 4 + ‖z‖ ^ 2 ≤ s ^ 4) : parameterWeight ξ z ≤ 1 + 2 * s := by
  have hξ : ‖ξ‖ ≤ s :=
    le_of_pow_le_pow_left₀ four_ne_zero hs ((le_add_of_nonneg_right (sq_nonneg _)).trans h)
  have hz : Real.sqrt ‖z‖ ≤ s := by
    refine (Real.sqrt_le_left hs).2 (le_of_pow_le_pow_left₀ two_ne_zero (sq_nonneg s) ?_)
    rw [← pow_mul]
    exact (le_add_of_nonneg_left (by positivity)).trans h
  rw [parameterWeight_def]
  linarith

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

/-- Dilations compose multiplicatively. -/
@[simp]
theorem parameterDilation_comp_parameterDilation (s t : ℝ) :
    (parameterDilation n s).comp (parameterDilation n t) = parameterDilation n (s * t) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp [smul_smul, mul_pow, mul_assoc]

/-- A dilation by a factor in `[0, 1]` has norm at most one. -/
theorem norm_parameterDilation_le_one {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    ‖parameterDilation n r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have hr : r ^ 2 ≤ 1 := pow_le_one₀ h₀ h₁
  simp only [parameterDilation_apply, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg h₀, one_mul]
  exact max_le_max (max_le_max le_rfl (mul_le_of_le_one_left (norm_nonneg _) h₁))
    (mul_le_of_le_one_left (norm_nonneg _) hr)

/-- A dilation by a factor `r ≥ 1` has norm at most `r²`. -/
theorem norm_parameterDilation_le_sq {r : ℝ} (h₁ : 1 ≤ r) :
    ‖parameterDilation n r‖ ≤ r ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hr : r ≤ r ^ 2 := by nlinarith
  have hr' : 1 ≤ r ^ 2 := h₁.trans hr
  simp only [parameterDilation_apply, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (zero_le_one.trans h₁)]
  refine max_le (max_le ?_ ?_) ?_
  · exact (le_mul_of_one_le_left (norm_nonneg _) hr').trans
      (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_left _ _)) (by positivity))
  · exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_left _ _)) (by positivity))
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

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

theorem parameterIteratedFDeriv_def {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ)
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv k f p = (iteratedFDeriv ℝ k f p).compContinuousLinearMap fun _ =>
      parameterDilation n (parameterWeight p.1.2 p.2) :=
  (rfl)

/-- The dilated derivatives at `p` only depend on the germ of the function at `p`. -/
theorem _root_.Filter.EventuallyEq.parameterIteratedFDeriv_eq {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (h : f =ᶠ[𝓝 p] g) (k : ℕ) :
    parameterIteratedFDeriv k f p = parameterIteratedFDeriv k g p := by
  rw [parameterIteratedFDeriv_def, parameterIteratedFDeriv_def,
    (h.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]

@[simp]
theorem parameterIteratedFDeriv_zero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv k (0 : (CoordinateSpace n × CoordinateSpace n) × ℂ → A) p = 0 := by
  ext v
  simp [parameterIteratedFDeriv_apply]

theorem parameterIteratedFDeriv_add {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ)
    {f g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hf : ContDiffAt ℝ k f p)
    (hg : ContDiffAt ℝ k g p) :
    parameterIteratedFDeriv k (f + g) p =
      parameterIteratedFDeriv k f p + parameterIteratedFDeriv k g p := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_add_apply hf hg]

theorem parameterIteratedFDeriv_sub {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ)
    {f g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hf : ContDiffAt ℝ k f p)
    (hg : ContDiffAt ℝ k g p) :
    parameterIteratedFDeriv k (f - g) p =
      parameterIteratedFDeriv k f p - parameterIteratedFDeriv k g p := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_sub_apply hf hg]

theorem parameterIteratedFDeriv_sum {A ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (s : Finset ι) {f : ι → (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hf : ∀ j ∈ s, ContDiffAt ℝ k (f j) p) :
    parameterIteratedFDeriv k (∑ j ∈ s, f j) p = ∑ j ∈ s, parameterIteratedFDeriv k (f j) p := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_sum_apply hf]

@[simp]
theorem parameterIteratedFDeriv_fun_zero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv k (fun _ : (CoordinateSpace n × CoordinateSpace n) × ℂ => (0 : A)) p =
      0 :=
  parameterIteratedFDeriv_zero k p

@[simp]
theorem parameterIteratedFDeriv_neg {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ)
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv k (-f) p = -parameterIteratedFDeriv k f p := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_neg_apply]

theorem parameterIteratedFDeriv_const_smul {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (c : ℝ) {f : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hf : ContDiffAt ℝ k f p) :
    parameterIteratedFDeriv k (c • f) p = c • parameterIteratedFDeriv k f p := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_const_smul_apply hf]

/-- The dilated derivatives of positive order of a constant vanish. -/
theorem parameterIteratedFDeriv_const_of_ne {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {k : ℕ} (hk : k ≠ 0) (c : A) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    parameterIteratedFDeriv k (fun _ => c) p = 0 := by
  ext v
  simp [parameterIteratedFDeriv_apply, iteratedFDeriv_const_of_ne hk]

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
  ContinuousLinearEquiv.equivOfInverse (parameterDilation n t) (parameterDilation n t⁻¹)
    (fun v => by simp [smul_smul, ht]) (fun v => by simp [smul_smul, ht])

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

/-- The pullback of a function smooth on `univ ×ˢ Λ` is smooth on an open neighbourhood of `0`. -/
private theorem contDiffOn_comp_dilation {Λ : Set ℂ} (hΛ : IsOpen Λ)
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

variable (n) in
/-- **Leibniz rule** at one point for the dilated derivatives. For functions `C^k` at `p` whose
dilated derivatives of order at most `k` at `p` are bounded by `M₁` and `M₂`, the dilated
derivatives of order at most `k` at `p` of a bilinear expression in them are at most
`E * (M₁ * M₂)`, where `E` is independent of the functions, of `p` and of `M₁` and `M₂`. -/
theorem exists_norm_parameterIteratedFDeriv_bilinear_le (B : X →L[ℝ] Y →L[ℝ] Z) (k : ℕ) :
    ∃ E, 0 ≤ E ∧ ∀ (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → X)
      (g : (CoordinateSpace n × CoordinateSpace n) × ℂ → Y)
      (p : (CoordinateSpace n × CoordinateSpace n) × ℂ), ContDiffAt ℝ k f p →
      ContDiffAt ℝ k g p → ∀ M₁ M₂ : ℝ, (∀ i ≤ k, ‖parameterIteratedFDeriv i f p‖ ≤ M₁) →
      (∀ i ≤ k, ‖parameterIteratedFDeriv i g p‖ ≤ M₂) →
      ∀ j ≤ k, ‖parameterIteratedFDeriv j (fun q => B (f q) (g q)) p‖ ≤ E * (M₁ * M₂) := by
  obtain ⟨E, hE, hB⟩ := exists_norm_iteratedFDeriv_bilinear_le
    ((CoordinateSpace n × CoordinateSpace n) × ℂ) B k
  refine ⟨E, hE, fun f g p hf hg M₁ M₂ h₁ h₂ j hj => ?_⟩
  set T := fun v => p + parameterDilation n (parameterWeight p.1.2 p.2) v
  have hT : ContDiffAt ℝ k T 0 := (contDiff_const.add (parameterDilation n _).contDiff).contDiffAt
  have hT0 : T 0 = p := by simp [T]
  have hfT : ContDiffAt ℝ k (f ∘ T) 0 := (hT0 ▸ hf).comp 0 hT
  have hgT : ContDiffAt ℝ k (g ∘ T) 0 := (hT0 ▸ hg).comp 0 hT
  obtain ⟨u, hu, hfu⟩ := hfT.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hgv⟩ := hgT.contDiffOn le_rfl (by simp)
  simp only [parameterIteratedFDeriv_eq_iteratedFDeriv_comp] at h₁ h₂ ⊢
  exact hB _ _ (interior (u ∩ v)) 0 isOpen_interior
    (mem_interior_iff_mem_nhds.2 (inter_mem hu hv))
    (hfu.mono (interior_subset.trans inter_subset_left))
    (hgv.mono (interior_subset.trans inter_subset_right)) M₁ M₂ h₁ h₂ j hj

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
  rw [(hfg _ hz).parameterIteratedFDeriv_eq k]
  exact hg x hx ξ z hz

private theorem Bounds.add (hΛ : IsOpen Λ) {g : (CoordinateSpace n × CoordinateSpace n) × ℂ → A}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ)) (hg : ContDiffOn ℝ ∞ g (univ ×ˢ Λ)) (hbf : Bounds Λ m f)
    (hbg : Bounds Λ m g) : Bounds Λ m (fun p => f p + g p) := fun K hK k => by
  obtain ⟨C, hC, hf'⟩ := hbf K hK k
  obtain ⟨D, hD, hg'⟩ := hbg K hK k
  refine ⟨C + D, add_nonneg hC hD, fun x hx ξ z hz => ?_⟩
  have hU := (isOpen_univ.prod hΛ).mem_nhds (⟨mem_univ _, hz⟩ : ((x, ξ), z) ∈ univ ×ˢ Λ)
  have hk : ((k : ℕ∞ω)) ≤ ∞ := by exact_mod_cast le_top
  rw [← Pi.add_def,
    parameterIteratedFDeriv_add k ((hf.contDiffAt hU).of_le hk) ((hg.contDiffAt hU).of_le hk)]
  exact (norm_add_le _ _).trans (by linarith [hf' x hx ξ z hz, hg' x hx ξ z hz])

/-- Composition with a fixed continuous linear map keeps the order. -/
private theorem Bounds.comp_left (hΛ : IsOpen Λ) {A' : Type*} [NormedAddCommGroup A']
    [NormedSpace ℝ A'] (L : A →L[ℝ] A') (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Λ)) (hb : Bounds Λ m f) :
    Bounds Λ m (fun p => L (f p)) := fun K hK k => by
  obtain ⟨C, hC, hf'⟩ := hb K hK k
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg L) hC, fun x hx ξ z hz => ?_⟩
  obtain ⟨hU, h0, hfT⟩ := contDiffOn_comp_dilation hΛ hf (p := ((x, ξ), z)) hz
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
  obtain ⟨E, hE, hB⟩ := exists_norm_parameterIteratedFDeriv_bilinear_le n B k
  refine ⟨E * (C * D), by positivity, fun x hx ξ z hz => ?_⟩
  have hU := (isOpen_univ.prod hΛ).mem_nhds (⟨mem_univ _, hz⟩ : ((x, ξ), z) ∈ univ ×ˢ Λ)
  have hk : ((k : ℕ∞ω)) ≤ ∞ := by exact_mod_cast le_top
  refine (hB f g _ ((hf.contDiffAt hU).of_le hk) ((hg.contDiffAt hU).of_le hk) _ _
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
  obtain ⟨hU, h0, haT⟩ := contDiffOn_comp_dilation hΛ ha (p := ((x, ξ), z)) hz
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

/-- The coefficient is smooth at every point with spectral parameter in `Λ`. -/
theorem contDiffAt_coefficient (a : ParameterSymbol n Λ V W m)
    {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ) {k : ℕ∞} :
    ContDiffAt ℝ k a.coefficient p :=
  (a.contDiffOn_coefficient.contDiffAt
    ((isOpen_univ.prod Λ.isOpen).mem_nhds ⟨mem_univ _, hp⟩)).of_le (by exact_mod_cast le_top)

/-- One constant serves for the estimates of all dilated derivatives of order at most `k`. -/
theorem exists_forall_le_bound (a : ParameterSymbol n Λ V W m) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
      ‖parameterIteratedFDeriv i a.coefficient ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m :=
  Bounds.exists_forall_le a.exists_bound hK k

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

/-! ### Smoothing symbols -/

/-- A parameter-dependent symbol is *smoothing*, or of order `-∞`, if its coefficient is a
parameter-dependent symbol of every real order: it decays faster than every power of
`1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)`, jointly in the frequency and the spectral parameter, together with
all its dilated derivatives. -/
def IsSmoothing (a : ParameterSymbol n Λ V W m) : Prop :=
  ∀ m' : ℝ, ∃ b : ParameterSymbol n Λ V W m', b.coefficient = a.coefficient

theorem isSmoothing_iff {a : ParameterSymbol n Λ V W m} :
    a.IsSmoothing ↔ ∀ m' : ℝ, ∃ b : ParameterSymbol n Λ V W m', b.coefficient = a.coefficient :=
  Iff.rfl

/-- The estimates characterizing smoothing symbols: a parameter-dependent symbol is smoothing
exactly when, for every real order `m'`, every compact set `K` of positions and every `k`, the
dilated derivative `parameterIteratedFDeriv k a ((x, ξ), z)` is bounded by
`C * parameterWeight ξ z ^ m'` for all `x ∈ K`, all frequencies `ξ` and all `z ∈ Λ`. -/
theorem isSmoothing_iff_forall_exists_bound {a : ParameterSymbol n Λ V W m} :
    a.IsSmoothing ↔ ∀ m' : ℝ, ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ k : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ∀ z ∈ Λ,
        ‖parameterIteratedFDeriv k a.coefficient ((x, ξ), z)‖ ≤ C * parameterWeight ξ z ^ m' := by
  refine ⟨fun h m' K hK k => ?_, fun h m' =>
    ⟨⟨a.coefficient, a.contDiffOn_coefficient, a.coefficient_of_notMem, h m'⟩, rfl⟩⟩
  obtain ⟨b, hb⟩ := h m'
  exact hb ▸ b.exists_bound K hK k

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
theorem isSmoothing_neg {a : ParameterSymbol n Λ V W m} : (-a).IsSmoothing ↔ a.IsSmoothing :=
  ⟨fun h => neg_neg a ▸ h.neg, IsSmoothing.neg⟩

theorem IsSmoothing.sub {a b : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (hb : b.IsSmoothing) : (a - b).IsSmoothing := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

@[simp]
theorem isSmoothing_inclusion {a : ParameterSymbol n Λ V W m} (h : m ≤ m') :
    (inclusion h a).IsSmoothing ↔ a.IsSmoothing := by
  simp only [isSmoothing_iff, coefficient_inclusion]

/-- Composing a smoothing symbol on the left with any symbol gives a smoothing symbol. -/
theorem IsSmoothing.comp_left {a : ParameterSymbol n Λ V W m} (ha : a.IsSmoothing)
    (b : ParameterSymbol n Λ W U m') : (b.comp a).IsSmoothing := fun m'' => by
  obtain ⟨a', ha'⟩ := ha (m'' - m')
  exact ⟨inclusion (by linarith) (b.comp a'), by funext p; simp [ha']⟩

/-- Composing a smoothing symbol on the right with any symbol gives a smoothing symbol. -/
theorem IsSmoothing.comp_right {b : ParameterSymbol n Λ W U m'} (hb : b.IsSmoothing)
    (a : ParameterSymbol n Λ V W m) : (b.comp a).IsSmoothing := fun m'' => by
  obtain ⟨b', hb'⟩ := hb (m'' - m)
  exact ⟨inclusion (by linarith) (b'.comp a), by funext p; simp [hb']⟩

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

/-- The scalar symbol `(s + ‖ξ‖²) - z` has order `2`: `‖ξ‖²` is a product of two functions of
order `1`, and `z` has order `2`. -/
private theorem bounds_laplacianSymbol (Λ : Set ℂ) (hΛ : IsOpen Λ) (s : ℝ) :
    Bounds Λ 2 (laplacianSymbol (n := n) s) := by
  let π : (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] CoordinateSpace n :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
  let ζ : (CoordinateSpace n × CoordinateSpace n) × ℂ →L[ℝ] ℂ := ContinuousLinearMap.snd ℝ _ _
  let B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℂ :=
    (ContinuousLinearMap.compL ℝ (CoordinateSpace n) ℝ ℂ Complex.ofRealCLM).comp (innerSL ℝ)
  have hπ : Bounds Λ 1 π := bounds_continuousLinearMap π (C := 1)
    (fun x ξ z _ => by simpa [π] using norm_le_parameterWeight ξ z) (fun ξ z _ => by
      rw [Real.rpow_one, one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (parameterWeight_pos ξ z).le fun v => ?_
      simp only [π, ContinuousLinearMap.comp_apply, parameterDilation_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', norm_smul,
        Real.norm_eq_abs, abs_of_pos (parameterWeight_pos ξ z)]
      exact mul_le_mul_of_nonneg_left ((norm_snd_le v.1).trans (norm_fst_le v))
        (parameterWeight_pos ξ z).le)
  have hζ : Bounds Λ 2 (-ζ) := bounds_continuousLinearMap (-ζ) (C := 1)
    (fun x ξ z _ => by simpa [ζ, Real.rpow_two] using norm_le_parameterWeight_sq ξ z)
    (fun ξ z _ => by
      rw [Real.rpow_two, one_mul, ContinuousLinearMap.neg_comp, norm_neg]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      simp only [ζ, ContinuousLinearMap.comp_apply, parameterDilation_apply,
        ContinuousLinearMap.coe_snd', norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (parameterWeight ξ z))]
      exact mul_le_mul_of_nonneg_left (norm_snd_le v) (sq_nonneg _))
  have hππ : Bounds Λ 2 (fun p => B (π p) (π p)) :=
    (Bounds.bilinear hΛ B π.contDiff.contDiffOn π.contDiff.contDiffOn hπ hπ).mono
      (by norm_num)
  have hBs : ContDiffOn ℝ ∞ (fun p => B (π p) (π p)) (univ ×ˢ Λ) :=
    ((B.isBoundedBilinearMap.contDiff (n := ∞)).comp (π.contDiff.prodMk π.contDiff)).contDiffOn
  have h₁ : Bounds Λ 2 (fun p => (s : ℂ) + B (π p) (π p)) :=
    Bounds.add hΛ contDiffOn_const hBs ((bounds_const (Λ := Λ) (s : ℂ)).mono zero_le_two) hππ
  have h₂ : Bounds Λ 2 (fun p => ((s : ℂ) + B (π p) (π p)) + (-ζ) p) :=
    Bounds.add hΛ (contDiffOn_const.add hBs) (-ζ).contDiff.contDiffOn h₁ hζ
  refine h₂.congr fun p _ => Filter.Eventually.of_forall fun q => ?_
  simp [laplacianSymbol, B, π, ζ, sub_eq_add_neg]

/-- For `0 ≤ s` and a spectral parameter `z` in the sector `Re z ≤ c ‖z‖`, `c < 1`, with
`δ ≤ s + ‖z‖`, the symbol `(s + ‖ξ‖²) - z` is bounded below by a multiple of the squared weight. -/
private theorem mul_parameterWeight_sq_le_norm_laplacianSymbol {s c δ : ℝ} (hs : 0 ≤ s)
    (hc : c < 1) (hδ : 0 < δ) {z : ℂ} (hz : z.re ≤ c * ‖z‖) (hzδ : δ ≤ s + ‖z‖)
    (x ξ : CoordinateSpace n) :
    (1 - max c (-1)) / 2 / (3 * (1 + δ⁻¹)) * parameterWeight ξ z ^ 2 ≤
      ‖laplacianSymbol s ((x, ξ), z)‖ := by
  set c₀ := max c (-1)
  set r := s + ‖ξ‖ ^ 2
  set a := ‖z‖
  have hc₀ : -1 ≤ c₀ := le_max_right _ _
  have hc₀' : c₀ < 1 := max_lt hc (by norm_num)
  have _ : 0 ≤ r := by positivity
  have ha : 0 ≤ a := norm_nonneg z
  have hre : z.re ≤ c₀ * a := hz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
  -- `‖r - z‖² = r² - 2 r Re z + ‖z‖²`.
  have hsq : ‖laplacianSymbol s ((x, ξ), z)‖ ^ 2 = r ^ 2 - 2 * r * z.re + a ^ 2 := by
    simp only [laplacianSymbol, a, r, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- Sector estimate: `‖r - z‖ ≥ (1 - c₀) / 2 * (r + ‖z‖)`.
  have hsector : (1 - c₀) / 2 * (r + a) ≤ ‖laplacianSymbol s ((x, ξ), z)‖ := by
    have h1 : ((1 - c₀) / 2 * (r + a)) ^ 2 ≤ ‖laplacianSymbol s ((x, ξ), z)‖ ^ 2 := by
      rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * r),
        mul_nonneg (by linarith : 0 ≤ 1 + c₀) (sq_nonneg (r - a)),
        mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - c₀) (by linarith : 0 ≤ 1 + c₀))
          (sq_nonneg (r + a))]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h1
  -- Weight estimate: `w² ≤ 3 (1 + δ⁻¹) (r + ‖z‖)`.
  have hw : parameterWeight ξ z ^ 2 ≤ 3 * (1 + δ⁻¹) * (r + a) := by
    have hsqrt := Real.sq_sqrt ha
    have h3 : parameterWeight ξ z ^ 2 ≤ 3 * (1 + ‖ξ‖ ^ 2 + a) := by
      unfold parameterWeight
      nlinarith [sq_nonneg (1 - ‖ξ‖), sq_nonneg (1 - Real.sqrt a), sq_nonneg (‖ξ‖ - Real.sqrt a)]
    have h1 : 1 ≤ δ⁻¹ * (r + a) := by
      rw [inv_mul_eq_div, one_le_div hδ]
      nlinarith [sq_nonneg ‖ξ‖]
    nlinarith [sq_nonneg ‖ξ‖]
  have hκ : 0 < 3 * (1 + δ⁻¹) := by positivity
  calc (1 - c₀) / 2 / (3 * (1 + δ⁻¹)) * parameterWeight ξ z ^ 2
      ≤ (1 - c₀) / 2 / (3 * (1 + δ⁻¹)) * (3 * (1 + δ⁻¹) * (r + a)) :=
        mul_le_mul_of_nonneg_left hw (div_nonneg (by linarith) hκ.le)
    _ = (1 - c₀) / 2 * (r + a) := by field_simp
    _ ≤ _ := hsector

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
  have hlow (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :=
    mul_parameterWeight_sq_le_norm_laplacianSymbol hs hc hδ (hΛ z hz).1 (hΛ z hz).2 x ξ
  have hκ : 0 < (1 - max c (-1)) / 2 / (3 * (1 + δ⁻¹)) :=
    div_pos (by linarith [max_lt hc (by norm_num : (-1 : ℝ) < 1)]) (by positivity)
  have hne (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
      ((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z ≠ 0 := by
    intro h
    have := (mul_pos hκ (pow_pos (parameterWeight_pos ξ z) 2)).trans_le (hlow x ξ hz)
    simp only [laplacianSymbol, h, norm_zero] at this
    exact lt_irrefl 0 this
  refine ⟨fun x ξ z hz => ?_, fun K _ => ⟨((1 - max c (-1)) / 2 / (3 * (1 + δ⁻¹)))⁻¹,
    fun x _ ξ z hz => ?_⟩⟩
  · rw [coefficient_shiftedLaplacian s x ξ hz,
      ContinuousLinearMap.isInvertible_smul_iff (hne x ξ hz)]
    exact ⟨ContinuousLinearEquiv.refl ℂ V, rfl⟩
  · rw [coefficient_shiftedLaplacian s x ξ hz, ContinuousLinearMap.inverse_smul,
      ContinuousLinearMap.inverse_id, Real.rpow_neg (parameterWeight_pos ξ z).le, Real.rpow_two]
    calc ‖(((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z)⁻¹ • ContinuousLinearMap.id ℂ V‖
        ≤ ‖(((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z)⁻¹‖ * ‖ContinuousLinearMap.id ℂ V‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖(((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z)⁻¹‖ :=
          mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
      _ = ‖laplacianSymbol s ((x, ξ), z)‖⁻¹ := norm_inv _
      _ ≤ ((1 - max c (-1)) / 2 / (3 * (1 + δ⁻¹)) * parameterWeight ξ z ^ 2)⁻¹ :=
          inv_anti₀ (mul_pos hκ (pow_pos (parameterWeight_pos ξ z) 2)) (hlow x ξ hz)
      _ = _ := mul_inv _ _

/-- The coefficient of the resolvent symbol: the inverse of the symbol of `s - Δ - z` is
`((s + ‖ξ‖²) - z)⁻¹ • id`, a parameter-dependent symbol of order `-2`. -/
theorem coefficient_inverse_shiftedLaplacian [CompleteSpace V] {s : ℝ}
    (h : (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).IsElliptic) (x ξ : CoordinateSpace n)
    {z : ℂ} (hz : z ∈ Λ) :
    ((shiftedLaplacian V s).inverse h).coefficient ((x, ξ), z) =
      (((s + ‖ξ‖ ^ 2 : ℝ) : ℂ) - z)⁻¹ • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_inverse, coefficient_shiftedLaplacian s x ξ hz,
    ContinuousLinearMap.inverse_smul, ContinuousLinearMap.inverse_id]

end ParameterSymbol


end TauCeti
