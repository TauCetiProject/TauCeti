/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic
public import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
public import TauCeti.Analysis.Calculus.Morse.Index
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Prod

/-!
# Nondegenerate critical points of separated sums of functions of one variable

For a finite family of functions `φ i : ℝ → ℝ`, the *separated sum* `y ↦ ∑ i, φ i (y i)` on
`ι → ℝ` has diagonal second derivative: its Hessian quadratic form at `y` is the diagonal form
`∑ i, φ i'' (y i) • (v i)²`, Mathlib's `QuadraticMap.weightedSumSquares` with weights the second
derivatives of the summands. Consequently `y` is a critical point of the sum exactly when each
`y i` is a critical point of `φ i`; it is a nondegenerate critical point exactly when, moreover,
each second derivative `φ i'' (y i)` is nonzero; and its Morse index is the number of `i` with
`φ i'' (y i) < 0`, by Sylvester's count `QuadraticForm.sigNeg_weightedSumSquares`. For the
diagonal quadratic function `TauCeti.diagonalQuadratic a = ∑ i, aᵢ xᵢ² / 2`, the normal form of the
Morse lemma, the origin is a nondegenerate critical point exactly when every `aᵢ` is nonzero, and
the Morse index is the number of negative `aᵢ`.

Conversely, at a `C²` critical point `p` of an arbitrary function `f` whose Hessian is the
diagonal form `∑ᵢ aᵢ vᵢ wᵢ`, the translated model `y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` is the second-order
Taylor approximation of `f`: the partial derivatives of `f` are `aᵢ (xᵢ - pᵢ)` up to
`o(|x - p|)`, and its second partial derivatives are close to `aᵢ δᵢⱼ` near `p`. Away from a
finite set `P` containing every critical point near it, compactness extends lower bounds for the
gradient and upper bounds for the Hessian of a `C²` function from far away to any positive
distance from `P`.

This is the calculus behind the standard Morse function `∑ i, cos (2π xᵢ / pᵢ)` on a torus
`∀ i, AddCircle (p i)`, whose charts have the real coordinates of the factors as coordinates. The
binary analogue for two arbitrary summands is `TauCeti.Analysis.Calculus.Morse.Prod`.

The first-derivative calculus of separated sums, including their critical points
`TauCeti.fderiv_sum_comp_eval_eq_zero_iff`, is in `TauCeti.Analysis.Calculus.FDeriv.Pi`; the
diagonal second derivative `TauCeti.fderiv_fderiv_sum_comp_eval_apply` is in
`TauCeti.Analysis.Calculus.SecondDerivative`.

## Main declarations

* `TauCeti.hessianQuadraticForm_sum_comp_eval`: its Hessian quadratic form is a weighted sum of
  squares.
* `TauCeti.isNondegenerateCriticalPoint_sum_comp_eval_iff`: its nondegenerate critical points.
* `TauCeti.morseIndex_sum_comp_eval`: its Morse index counts the negative second derivatives.
* `TauCeti.isNondegenerateCriticalPoint_diagonalQuadratic_zero_iff`,
  `TauCeti.morseIndex_diagonalQuadratic`: the origin is a nondegenerate critical point of
  `∑ i, aᵢ xᵢ² / 2` exactly when every `aᵢ` is nonzero, of Morse index the number of negative
  `aᵢ`.
* `TauCeti.eventually_sum_sq_fderiv_apply_single_sub_le`: at a twice differentiable critical point
  with Hessian `∑ᵢ aᵢ vᵢ wᵢ`, the gradient is `(aᵢ (xᵢ - pᵢ))ᵢ` up to `o(|x - p|)`.
* `TauCeti.eventually_sum_mul_sq_le_sum_fderiv_apply_single_sq` and
  `TauCeti.eventually_sum_mul_sq_le_and_sum_sum_abs_sub_le`: if moreover every `|aᵢ| ≥ c > 0`, then
  near `p` the gradient is at least that of the weakened model `θ a` for `θ² < 1`, and the Hessian
  is close to `diag(θ a)`.
* `TauCeti.exists_pos_forall_le_sum_fderiv_apply_single_sq_and_le`: if the critical points of a
  `C²` function near a finite set `P` lie in `P`, then a lower bound for the gradient and an upper
  bound for the Hessian far from `P` extend, with other constants, to any positive distance
  from `P`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι] {φ : ι → ℝ → ℝ} {y : ι → ℝ}

/-- **The Hessian of a separated sum is a weighted sum of squares**, with weights the second
derivatives of the summands. -/
@[simp]
theorem hessianQuadraticForm_sum_comp_eval (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    hessianQuadraticForm (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y =
      QuadraticMap.weightedSumSquares ℝ fun i ↦ deriv (deriv (φ i)) (y i) := by
  ext v
  simp [fderiv_fderiv_sum_comp_eval_apply hφ, mul_assoc]

/-- **Nondegenerate critical points of a separated sum.** For summands twice continuously
differentiable at the coordinates of `y`, the separated sum `z ↦ ∑ i, φ i (z i)` has a
nondegenerate critical point at `y` exactly when every `y i` is a critical point of `φ i` at which
the second derivative of `φ i` does not vanish. -/
@[simp]
theorem isNondegenerateCriticalPoint_sum_comp_eval_iff
    (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    IsNondegenerateCriticalPoint (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y ↔
      ∀ i, deriv (φ i) (y i) = 0 ∧ deriv (deriv (φ i)) (y i) ≠ 0 := by
  have hcont : ContDiffAt ℝ 2 (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y :=
    ContDiffAt.sum fun i _ ↦ (hφ i).comp y (contDiffAt_apply ℝ (fun _ ↦ ℝ) i y)
  -- The Hessian quadratic form is a weighted sum of squares, which is nondegenerate exactly when
  -- its weights are nonzero.
  rw [isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate,
    fderiv_sum_comp_eval_eq_zero_iff fun i ↦ (hφ i).differentiableAt (by simp),
    hessianQuadraticForm_sum_comp_eval hφ, QuadraticMap.nondegenerate_weightedSumSquares_iff]
  simp only [hcont, true_and, forall_and, isRegular_iff_ne_zero]

/-- **The Morse index of a separated sum** at a point at which every summand is twice continuously
differentiable is the number of summands whose second derivative is negative there. -/
@[simp]
theorem morseIndex_sum_comp_eval (hφ : ∀ i, ContDiffAt ℝ 2 (φ i) (y i)) :
    morseIndex (fun z : ι → ℝ ↦ ∑ i, φ i (z i)) y =
      {i | deriv (deriv (φ i)) (y i) < 0}.ncard := by
  rw [morseIndex_def, hessianQuadraticForm_sum_comp_eval hφ,
    QuadraticForm.sigNeg_weightedSumSquares]

/-- The origin is a nondegenerate critical point of `∑ᵢ aᵢ xᵢ² / 2` exactly when every `aᵢ` is
nonzero. -/
theorem isNondegenerateCriticalPoint_diagonalQuadratic_zero_iff (a : ι → ℝ) :
    IsNondegenerateCriticalPoint (diagonalQuadratic a) 0 ↔ ∀ i, a i ≠ 0 := by
  rw [funext (diagonalQuadratic_apply a),
    isNondegenerateCriticalPoint_sum_comp_eval_iff (φ := fun i y ↦ a i * y ^ 2 / 2)
      fun i ↦ by fun_prop]
  simp only [funext (deriv_mul_sq_div_two _)]
  simp

/-- The Morse index of `∑ᵢ aᵢ xᵢ² / 2` is the number of negative `aᵢ`. -/
@[simp]
theorem morseIndex_diagonalQuadratic (a x : ι → ℝ) :
    morseIndex (diagonalQuadratic a) x = (Finset.univ.filter fun i ↦ a i < 0).card := by
  have h : hessianQuadraticForm (diagonalQuadratic a) x = QuadraticMap.weightedSumSquares ℝ a := by
    ext v
    simp [mul_assoc]
  rw [morseIndex_def, h, QuadraticForm.sigNeg_weightedSumSquares, ← Set.ncard_coe_finset]
  simp

/-! ### Taylor estimates at a critical point with diagonal Hessian -/

section Taylor

open Filter Topology

variable [DecidableEq ι] {f : (ι → ℝ) → ℝ} {a p : ι → ℝ}

/-- At a critical point `p` at which `fderiv ℝ f` is differentiable, with Hessian `∑ᵢ aᵢ vᵢ wᵢ`,
the gradient of `f` is `(aᵢ (xᵢ - pᵢ))ᵢ` up to `o(|x - p|)`: for every `ε > 0`, near `p`,
`∑ᵢ (∂ᵢf(x) - aᵢ (xᵢ - pᵢ))² ≤ ε ∑ᵢ (xᵢ - pᵢ)²`. -/
theorem eventually_sum_sq_fderiv_apply_single_sub_le (hf : DifferentiableAt ℝ (fderiv ℝ f) p)
    (hp : fderiv ℝ f p = 0) (ha : ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a i * v i * w i)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 p, ∑ i, (fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i)) ^ 2 ≤
      ε * ∑ i, (x i - p i) ^ 2 := by
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) p := hf.hasFDerivAt
  set n : ℝ := (Fintype.card ι : ℝ)
  set δ := min 1 (ε / (n + 1))
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hδ : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  have hnδ : n * δ ^ 2 ≤ ε := by
    have h₁ : δ ^ 2 ≤ δ := by nlinarith [min_le_left 1 (ε / (n + 1))]
    have h₂ : (n + 1) * δ ≤ ε := (le_div_iff₀' (by positivity)).1 (min_le_right _ _)
    nlinarith
  filter_upwards [hd.isLittleO.def hδ] with x hx
  rw [hp, sub_zero] at hx
  -- Each coordinate of the remainder is bounded by its norm.
  have hi : ∀ i, (fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i)) ^ 2 ≤
      δ ^ 2 * ‖x - p‖ ^ 2 := by
    intro i
    have hcomp : fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i) =
        (fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) p (x - p)) (Pi.single i 1) := by
      rw [sub_apply, ha]
      simp [Pi.single_apply]
    have h₁ := ((fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) p (x - p)).le_opNorm (Pi.single i 1)).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    rw [Pi.norm_single, norm_one, mul_one, ← hcomp, Real.norm_eq_abs] at h₁
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  calc ∑ i, (fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i)) ^ 2
      ≤ ∑ _i : ι, δ ^ 2 * ‖x - p‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = n * δ ^ 2 * ‖x - p‖ ^ 2 := by simp [n, mul_assoc]
    _ ≤ ε * ∑ i, (x i - p i) ^ 2 := by
      -- The sup norm is at most the Euclidean norm.
      have hs : 0 ≤ ∑ i, (x i - p i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have h : ‖x - p‖ ≤ √(∑ i, (x i - p i) ^ 2) :=
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i ↦ by
          rw [Real.norm_eq_abs, Pi.sub_apply]
          exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j ↦ (x j - p j) ^ 2)
            (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i))
      have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [Real.sq_sqrt hs] at h'
      exact mul_le_mul hnδ h' (sq_nonneg _) hε.le

/-- At a critical point `p` at which `fderiv ℝ f` is differentiable, with Hessian `∑ᵢ aᵢ vᵢ wᵢ`,
where every `|aᵢ| ≥ c > 0`, the gradient of `f` is at least `θ` times that of the quadratic model
near `p` for every `θ² < 1`: `∑ᵢ (θ aᵢ (xᵢ - pᵢ))² ≤ |df(x)|²`. -/
theorem eventually_sum_mul_sq_le_sum_fderiv_apply_single_sq
    (hf : DifferentiableAt ℝ (fderiv ℝ f) p)
    (hp : fderiv ℝ f p = 0) (ha : ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ i, c ≤ |a i|) {θ : ℝ} (hθ : θ ^ 2 < 1) :
    ∀ᶠ x in 𝓝 p, ∑ i, (θ * a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 := by
  set η := (1 - θ ^ 2) / 2
  have hη : 0 < η := by simp only [η]; linarith
  filter_upwards [eventually_sum_sq_fderiv_apply_single_sub_le hf hp ha
    (ε := c ^ 2 * η ^ 2) (by positivity)] with x hx
  -- Write `∂ᵢf(x) = Aᵢ + Eᵢ` with `Aᵢ = aᵢ (xᵢ - pᵢ)` the gradient of the model.
  set A : ι → ℝ := fun i ↦ a i * (x i - p i)
  set E : ι → ℝ := fun i ↦ fderiv ℝ f x (Pi.single i 1) - A i
  have hpt : ∀ i, η * (1 - η) * A i ^ 2 - E i ^ 2 ≤ η * fderiv ℝ f x (Pi.single i 1) ^ 2 := by
    intro i
    have h : fderiv ℝ f x (Pi.single i 1) = A i + E i := by simp only [E]; ring
    rw [h]
    nlinarith [sq_nonneg (η * A i + E i), sq_nonneg (E i)]
  -- The remainder is small compared with the gradient of the model.
  have hE : ∑ i, E i ^ 2 ≤ η ^ 2 * ∑ i, A i ^ 2 := by
    refine hx.trans ?_
    rw [mul_comm (c ^ 2), mul_assoc, Finset.mul_sum (s := Finset.univ) (a := c ^ 2)]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ ?_) (sq_nonneg η)
    simp only [A, mul_pow]
    have : c ^ 2 ≤ a i ^ 2 := by
      rw [← sq_abs (a i)]
      exact pow_le_pow_left₀ hc.le (hca i) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hpt i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hθA : ∑ i, (θ * a i * (x i - p i)) ^ 2 = θ ^ 2 * ∑ i, A i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [A]; ring
  rw [hθA]
  have hθη : θ ^ 2 = 1 - 2 * η := by simp only [η]; ring
  rw [hθη]
  nlinarith

/-- Near a `C²` critical point `p` with Hessian `∑ᵢ aᵢ vᵢ wᵢ`, where every `|aᵢ| ≥ c > 0`, the
function `f` satisfies the hypotheses of the gap near the weakened quadratic model with
coefficients `θ aᵢ`, `0 ≤ θ < 1`: its gradient is at least that of the model, and its Hessian is
within `η + (1 - θ) ∑ᵢ |aᵢ|` of `diag(θ a)`, for any `η > 0`. -/
theorem eventually_sum_mul_sq_le_and_sum_sum_abs_sub_le (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0) (ha : ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ i, c ≤ |a i|) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ x in 𝓝 p, ∑ i, (θ * a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 ∧
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        if i = j then θ * a i else 0| ≤ η + (1 - θ) * ∑ i, |a i| := by
  -- The Hessian is continuous at `p`.
  have hcont : ContinuousAt (fun x ↦ ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1)|) p := by
    have hf₂ := hf.continuousAt_fderiv_fderiv le_rfl
    exact tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
      (((hf₂.clm_apply continuousAt_const).clm_apply continuousAt_const).sub
        continuousAt_const).abs
  filter_upwards [eventually_sum_mul_sq_le_sum_fderiv_apply_single_sq
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) hp ha hc hca
    (θ := θ) (by nlinarith), hcont.eventually_lt continuousAt_const (by simpa using hη)]
    with x h₁ h₂
  refine ⟨h₁, ?_⟩
  have hp' : ∀ i j, fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1) =
      if i = j then a i else 0 := fun i j ↦ by
    rw [ha, ← fderiv_fderiv_diagonalQuadratic_apply a 0,
      fderiv_fderiv_diagonalQuadratic_apply_single_single]
  -- The Hessian at `p` is `diag(a)`, at distance `(1 - θ) ∑ᵢ |aᵢ|` from `diag(θ a)`.
  have h₃ : ∀ i, ∑ j, |fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1) -
      if i = j then θ * a i else 0| = (1 - θ) * |a i| := fun i ↦ by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hp', Ne.symm hj]) (by simp), hp']
    simp only [ite_true]
    rw [← one_sub_mul, abs_mul, abs_of_nonneg (by linarith)]
  calc ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          if i = j then θ * a i else 0|
      ≤ ∑ i, ∑ j, (|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1)| +
          |fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1) -
            if i = j then θ * a i else 0|) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ abs_sub_le _ _ _
    _ = (∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1)|) +
          (1 - θ) * ∑ i, |a i| := by
        simp only [Finset.sum_add_distrib, h₃, Finset.mul_sum]
    _ ≤ η + (1 - θ) * ∑ i, |a i| := by linarith [h₂]

end Taylor

/-! ### Bounds away from isolated critical points -/

section Isolated

open Metric Set

variable [DecidableEq ι]

/-- If the critical points of a `C²` function `f` within distance `ρ` of a finite set `P` all lie
in `P`, then lower bounds for the gradient and upper bounds for the Hessian of `f` at distance more
than `ρ` from `P` extend to distance more than any `ρ' > 0`: in between, the gradient does not
vanish on a compact set. -/
theorem exists_pos_forall_le_sum_fderiv_apply_single_sq_and_le {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} {ρ : ℝ}
    (hcrit : ∀ x, fderiv ℝ f x = 0 → (∃ p ∈ P, dist x p ≤ ρ) → x ∈ P) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdf : ∀ x, (∀ p ∈ P, ρ < dist x p) → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {h : ℝ} (hh : ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    {ρ' : ℝ} (hρ' : 0 < ρ') :
    ∃ c₁ > 0, ∃ h₁, ∀ x, (∀ p ∈ P, ρ' < dist x p) →
      c₁ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 ∧
        ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h₁ := by
  -- The compact region at distance at most `ρ` from some point of `P` and at least `ρ'` from all.
  set S := (⋃ p ∈ P, closedBall p ρ) ∩ {x | ∀ p ∈ P, ρ' ≤ dist x p}
  have hS : IsCompact S := by
    refine (P.isCompact_biUnion fun p _ ↦ isCompact_closedBall p ρ).inter_right ?_
    simp only [Set.ofPred_forall]
    exact isClosed_biInter fun p _ ↦
      isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hg : Continuous fun x ↦ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 :=
    continuous_finsetSum _ fun i _ ↦
      ((hf.continuous_fderiv two_ne_zero).clm_apply continuous_const).pow 2
  have hH : Continuous fun x ↦
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| :=
    continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
      (hf.continuous_fderiv_fderiv_apply le_rfl _ _).abs
  -- On `S` the gradient does not vanish, so `|df|²` has a positive minimum there.
  obtain ⟨c₂, hc₂, hc₂S⟩ := hS.exists_forall_le' hg.continuousOn (a := 0) fun x hx ↦ by
    have hxP : ∃ p ∈ P, dist x p ≤ ρ := by simpa only [mem_iUnion, mem_closedBall, exists_prop]
      using hx.1
    have hx₀ : fderiv ℝ f x ≠ 0 := fun h₀ ↦
      absurd ((hx.2 x (hcrit x h₀ hxP)).trans_eq (dist_self x)) (not_le.2 hρ')
    refine (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _).lt_of_ne fun h₀ ↦ hx₀ ?_
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).1 h₀.symm
    exact ContinuousLinearMap.pi_ext_one fun i ↦ by simpa using hi i (Finset.mem_univ i)
  obtain ⟨H, hHS⟩ := hS.bddAbove_image hH.continuousOn
  refine ⟨min c₀ c₂, lt_min hc₀ hc₂, max h H, fun x hx ↦ ?_⟩
  by_cases hxρ : ∀ p ∈ P, ρ < dist x p
  · exact ⟨(min_le_left _ _).trans (hdf x hxρ), (hh x hxρ).trans (le_max_left _ _)⟩
  push Not at hxρ
  obtain ⟨p, hp, hxp⟩ := hxρ
  have hxS : x ∈ S := ⟨mem_biUnion hp (mem_closedBall.2 hxp), fun q hq ↦ (hx q hq).le⟩
  exact ⟨(min_le_right _ _).trans (hc₂S x hxS), (hHS ⟨x, hxS, rfl⟩).trans (le_max_right _ _)⟩

end Isolated

end TauCeti

end
