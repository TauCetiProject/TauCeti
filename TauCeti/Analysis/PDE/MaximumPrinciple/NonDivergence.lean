/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple
public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Positive
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The weak maximum principle for elliptic operators in non-divergence form

Let `K` be a compact subset of `ℝⁿ = EuclideanSpace ℝ ι`. This file proves the classical weak
maximum principle for the second-order operator in non-divergence form

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu`

with a variable coefficient matrix `a`, elliptic with constant `λ > 0` in the sense that
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ`, and a drift `b` bounded by `β`, both on the interior of `K`. In Lean,
`∂ᵢ∂ⱼu` at `x` is `fderiv ℝ (fderiv ℝ u) x eᵢ eⱼ` for the standard basis vectors
`eᵢ = EuclideanSpace.single i 1`, and `bⁱ ∂ᵢu` is `fderiv ℝ u x (b x)`.

If `c ≥ 0` and a function `u`, continuous on `K` and `C²` in its interior, satisfies
`c u ≤ L u` there, then every nonnegative upper bound for `u` on `frontier K` bounds `u` on all of
`K`. The coefficients need no regularity, not even measurability, since the argument is pointwise;
`a` need not be symmetric; and nothing beyond `c ≥ 0` is asked of the zeroth-order coefficient.
The minimum principle, the two-sided bound for solutions, the comparison principle and uniqueness
for the Dirichlet problem follow, and so does the quantitative form: if instead
`c u - F ≤ L u` for a constant `F ≥ 0`, then `u ≤ m + (exp ((β / λ + 1) diam K) - 1) F / λ`, with
a constant depending only on `β / λ`, `λ` and the diameter of `K`. Applied to `-u` it gives the
matching lower bound, and together the two give the bound on `sup |u|` in terms of
`sup_{frontier K} |u|` and `sup |L u - c u|` that the Schauder theory of the Dirichlet problem uses.

Only the lower ellipticity bound is used, so a coefficient field with
`TauCeti.PDE.UniformlyEllipticOn (interior K) a λ Λ` supplies the hypotheses through
`UniformlyEllipticOn.pos` and `UniformlyEllipticOn.lower_bound`.

The Laplacian is the case `a = 1`, treated in
`TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple`. The weak maximum
principle for weak solutions of equations in divergence form is
`TauCeti.Analysis.PDE.MaximumPrinciple.Weak`; neither form of the principle implies the other.

## The argument

At an interior local maximum of a `C²` function the gradient vanishes and the Hessian is negative
semidefinite. The negated Hessian is then a sum of rank-one matrices `vₖ vₖᵀ`
(`Matrix.posSemidef_iff_eq_sum_vecMulVec`), so `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = -∑ₖ vₖᵀ a vₖ ≤ 0`, and a strict
subsolution `L u > 0` has no interior local maximum. For the weak principle one perturbs `u` by
`ε w`, where `w = exp (α ⟪e, ·⟫)` for a unit vector `e` and `α = β / λ + 1`, so that
`L w = (α² eᵀ a e + α ⟪e, b⟫) w ≥ α λ w > 0`, and lets `ε → 0`. For the a priori bound one
compares `u` with `m + (F / λ) (exp (α d) - exp (α (⟪e, ·⟫ - s)))`, where `K` lies in the slab
`s ≤ ⟪e, ·⟫ ≤ s + d` and `d` is the diameter of `K`.

## Main declarations

* `TauCeti.PDE.sum_mul_fderiv_fderiv_nonpos_of_isLocalMax`: at a local maximum of a `C²` function,
  the principal part of an elliptic operator is nonpositive.
* `TauCeti.PDE.not_isLocalMax_of_sum_mul_fderiv_fderiv_add_fderiv_pos`: a strict subsolution of
  `L` has no local maximum.
* `TauCeti.PDE.mul_exp_le_sum_mul_fderiv_fderiv_add_fderiv_exp_inner`: the exponential barrier is
  a strict subsolution of `L`, with an explicit lower bound for `L w`.
* `TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_add_smul`,
  `TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_neg`: linearity of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v`.
* `TauCeti.PDE.sum_mul_fderiv_fderiv_add_fderiv_norm_sq`: the operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v`
  applied to `‖x‖²` is `2 tr A + 2 ⟪x, v⟫`.
* `TauCeti.PDE.le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`: **the weak maximum
  principle** for `-L + c`, `c ≥ 0`.
* `TauCeti.PDE.ge_of_sum_mul_fderiv_fderiv_add_fderiv_le_mul_ge_frontier`: the weak minimum
  principle.
* `TauCeti.PDE.abs_le_of_sum_mul_fderiv_fderiv_add_fderiv_eq_mul_abs_le_frontier`: the two-sided
  bound for solutions.
* `TauCeti.PDE.le_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_frontier`: the comparison
  principle.
* `TauCeti.PDE.eqOn_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_eq_of_eqOn_frontier`: uniqueness
  for the Dirichlet problem.
* `TauCeti.PDE.le_add_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`: the a priori
  bound.
* `TauCeti.PDE.sub_le_of_sum_mul_fderiv_fderiv_add_fderiv_le_mul_add_ge_frontier`: the a priori
  lower bound.
* `TauCeti.PDE.abs_le_add_of_abs_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_abs_le_frontier`: the
  a priori bound on `sup |u|`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 3.1 (Theorem 3.1 and Corollaries 3.2 and 3.3) and Section 3.3 (Theorem 3.7).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Matrix RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The principal part at a local maximum.** If the matrix `A` has nonnegative quadratic form
and `f` is `C²` at a local maximum `x`, then `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼf(x) ≤ 0`. The matrix need not be
symmetric. -/
theorem sum_mul_fderiv_fderiv_nonpos_of_isLocalMax {A : Matrix ι ι ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ A.toQuadraticForm' ξ) {f : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) ≤ 0 := by
  let H := fderiv ℝ (fderiv ℝ f) x
  -- The Hessian in coordinates.
  have hH (v w : EuclideanSpace ℝ ι) :
      H v w = ∑ i, ∑ j, v i * w j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v,
      ← (EuclideanSpace.basisFun ι ℝ).sum_repr w]
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, map_sum, map_smul,
      _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      by ring)
  -- The negated Hessian matrix is positive semidefinite, hence a sum of rank-one matrices.
  let M : Matrix ι ι ℝ :=
    Matrix.of fun i j ↦ -H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hM : M.PosSemidef := by
    refine .of_dotProduct_mulVec_nonneg ?_ fun v ↦ ?_
    · ext i j
      simpa [M] using hf.isSymmSndFDerivAt (by simp) (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1)
    · have h := fderiv_fderiv_self_nonpos_of_isLocalMax hf hmax (WithLp.toLp 2 v)
      rw [hH] at h
      have : star v ⬝ᵥ (M *ᵥ v) = -∑ i, ∑ j, v i * v j *
          H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        simp only [M, dotProduct, mulVec, star_trivial, of_apply, Finset.mul_sum,
          ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      linarith
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  have hMv (i j : ι) : H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      -∑ k, v k i * v k j := by
    have h := congrFun (congrFun hv i) j
    simp only [M, of_apply, Matrix.sum_apply, vecMulVec_apply, star_trivial] at h
    linarith
  -- Pairing `A` with `-∑ₖ vₖ vₖᵀ` gives `-∑ₖ vₖᵀ A vₖ`.
  have key : ∑ i, ∑ j, A i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      -∑ k, A.toQuadraticForm' (v k) := by
    simp only [hMv, toQuadraticForm'_apply, dotProduct, mulVec, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    calc _ = ∑ i, ∑ k, ∑ j, A i j * -(v k i * v k j) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
            Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [key, neg_nonpos]
  exact Finset.sum_nonneg fun k _ ↦ by simpa using hA (WithLp.toLp 2 (v k))

/-- **Strict interior obstruction.** If `A` has nonnegative quadratic form, `f` is `C²` at `x`
and `0 < ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼf(x) + ∂_v f(x)`, then `f` has no local maximum at `x`. The direction `v` is
arbitrary: at a local maximum the derivative of `f` vanishes. -/
theorem not_isLocalMax_of_sum_mul_fderiv_fderiv_add_fderiv_pos {A : Matrix ι ι ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ A.toQuadraticForm' ξ) {f : EuclideanSpace ℝ ι → ℝ}
    {x v : EuclideanSpace ℝ ι} (hf : ContDiffAt ℝ 2 f x)
    (hpos : 0 < ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ f x v) :
    ¬IsLocalMax f x := by
  intro hmax
  rw [hmax.fderiv_eq_zero, _root_.zero_apply, add_zero] at hpos
  exact (sum_mul_fderiv_fderiv_nonpos_of_isLocalMax hA hf hmax).not_gt hpos

/-- **The exponential barrier.** Let `A` satisfy `λ ‖ξ‖² ≤ ξᵀ A ξ` with `0 < λ`, let `e` be a unit
vector and let `‖b‖ ≤ β`. Then `w = exp (α ⟪e, ·⟫)` with `α = β / λ + 1` satisfies
`α λ w ≤ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw + ∂_b w` at every point; in particular it is a strict subsolution. -/
theorem mul_exp_le_sum_mul_fderiv_fderiv_add_fderiv_exp_inner {A : Matrix ι ι ℝ} {lam β : ℝ}
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    {e b : EuclideanSpace ℝ ι} (he : ‖e‖ = 1) (hb : ‖b‖ ≤ β) (x : EuclideanSpace ℝ ι) :
    (β / lam + 1) * lam * Real.exp ((β / lam + 1) * ⟪e, x⟫) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y ↦ Real.exp ((β / lam + 1) * ⟪e, y⟫)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun y ↦ Real.exp ((β / lam + 1) * ⟪e, y⟫)) x b := by
  set α := β / lam + 1
  have hβ : 0 ≤ β := (norm_nonneg b).trans hb
  have hα : 0 < α := by positivity
  have hαlam : α * lam - β = lam := by
    simp only [α]
    field_simp
    ring
  have hinner : -β ≤ ⟪e, b⟫ := by
    have h := (abs_le.mp (abs_real_inner_le_norm e b)).1
    rw [he, one_mul] at h
    linarith
  have hQ : lam ≤ A.toQuadraticForm' e := by simpa [he] using hA e
  -- The principal part of the barrier is `α² (eᵀ A e) w`.
  have hprin : ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y ↦ Real.exp (α * ⟪e, y⟫)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      α ^ 2 * A.toQuadraticForm' e * Real.exp (α * ⟪e, x⟫) := by
    simp only [fderiv_fderiv_exp_inner_apply, EuclideanSpace.inner_single_right, one_mul,
      conj_trivial, toQuadraticForm'_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hprin, fderiv_exp_inner_apply]
  have hw := Real.exp_pos (α * ⟪e, x⟫)
  nlinarith [mul_le_mul_of_nonneg_right hQ (mul_nonneg (sq_nonneg α) hw.le),
    mul_le_mul_of_nonneg_right hinner (mul_nonneg hα.le hw.le),
    congrArg (· * (α * Real.exp (α * ⟪e, x⟫))) hαlam]

/-- The operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v` is linear on functions that are `C²` at the point. -/
theorem sum_mul_fderiv_fderiv_add_fderiv_add_smul {A : Matrix ι ι ℝ}
    {f g : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (r : ℝ) (v : EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (f + r • g)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ (f + r • g) x v =
    (∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ f x v) +
    r * (∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ g x v) := by
  have hg' : ContDiffAt ℝ 2 (r • g) x := hg.const_smul r
  have h2 : fderiv ℝ (fderiv ℝ (f + r • g)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ (r • g)) x := by
    ext v w
    simpa [iteratedFDeriv_two_apply] using
      congrArg (· ![v, w]) (iteratedFDeriv_add_apply hf hg')
  rw [h2, fderiv_fderiv_const_smul, fderiv_add (hf.differentiableAt two_ne_zero)
    (hg'.differentiableAt two_ne_zero), fderiv_const_smul_field]
  simp only [_root_.add_apply, Pi.smul_apply, _root_.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  have h : ∑ i, ∑ j, A i j * (r * fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)) = ∑ i, ∑ j, r * (A i j * fderiv ℝ (fderiv ℝ g) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :=
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h]
  ring

/-- The operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v` commutes with negation. -/
theorem sum_mul_fderiv_fderiv_add_fderiv_neg (A : Matrix ι ι ℝ)
    (f : EuclideanSpace ℝ ι → ℝ) (x v : EuclideanSpace ℝ ι) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (-f)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ (-f) x v =
    -(∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) + fderiv ℝ f x v) := by
  have h : fderiv ℝ (-f) = -fderiv ℝ f := funext fun _ ↦ fderiv_neg
  simp only [h, fderiv_neg, _root_.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_add]

/-- The operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ + ∂_v` applied to the squared norm `‖x‖²` is `2 tr A + 2 ⟪x, v⟫`. -/
theorem sum_mul_fderiv_fderiv_add_fderiv_norm_sq {A : Matrix ι ι ℝ}
    {x v : EuclideanSpace ℝ ι} :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y : EuclideanSpace ℝ ι ↦ ‖y‖ ^ 2) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦ ‖y‖ ^ 2) x v = 2 * A.trace + 2 * ⟪x, v⟫ := by
  simp only [fderiv_fderiv_norm_sq_apply]
  simp [EuclideanSpace.inner_single_left, Matrix.trace, Finset.mul_sum, mul_comm]

variable [Nonempty ι]

/-- **The weak maximum principle for elliptic operators in non-divergence form.** Let `K` be
compact, and on its interior let `a` satisfy `λ ‖ξ‖² ≤ ξᵀ a(x) ξ` with `0 < λ`, let `‖b‖ ≤ β`
and `c ≥ 0`. If `f` is continuous on `K`, `C²` on its interior, and satisfies
`c f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼf + bⁱ ∂ᵢf` there, then every nonnegative bound `m` for `f` on `frontier K`
bounds `f` on `K`.

The index type `ι` is nonempty: in dimension zero every compact set is open, its frontier is
empty, and the statement fails. -/
theorem le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ} {lam β m : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hm : 0 ≤ m) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m := by
  intro x hxK
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ ι)
  set e : EuclideanSpace ℝ ι := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm hv
  set w : EuclideanSpace ℝ ι → ℝ := fun y ↦ Real.exp ((β / lam + 1) * ⟪e, y⟫)
  have hwpos (y : EuclideanSpace ℝ ι) : 0 < w y := Real.exp_pos _
  have hwcd : ContDiff ℝ 2 w := (contDiff_exp_inner _ e).of_le (by norm_cast)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hwcd.continuous.continuousOn
  have hC0 : 0 ≤ C := (hwpos x).le.trans (hC (Set.mem_image_of_mem w hxK))
  -- It suffices to show `f x ≤ m + ε C` for every `ε > 0`.
  apply le_of_forall_pos_mul_le hC0
  intro ε hε
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩
    (hcont.add (hwcd.continuous.continuousOn.const_smul ε))
  -- A maximizer `z` of `f + ε w` over `K` satisfies `f z ≤ m`.
  have hfz : f z ≤ m := by
    by_cases hzint : z ∈ interior K
    · by_contra hlt
      have hfzpos : 0 ≤ f z := hm.trans (not_le.mp hlt).le
      have hβ : 0 ≤ β := (norm_nonneg _).trans (hb hzint)
      have hLw := (mul_pos (mul_pos (by positivity) hlam) (hwpos z)).trans_le
        (mul_exp_le_sum_mul_fderiv_fderiv_add_fderiv_exp_inner hlam (ha hzint) he (hb hzint) z)
      have hgcd : ContDiffAt ℝ 2 (f + ε • w) z :=
        (hcd hzint).add (hwcd.contDiffAt.const_smul ε)
      refine not_isLocalMax_of_sum_mul_fderiv_fderiv_add_fderiv_pos (v := b z)
        (fun ξ ↦ (mul_nonneg hlam.le (sq_nonneg _)).trans (ha hzint ξ)) hgcd ?_
        (hzmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzint))
      rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul (hcd hzint) hwcd.contDiffAt]
      nlinarith [mul_nonneg (hc hzint) hfzpos, hsub hzint, mul_pos hε hLw]
    · exact hbdry ⟨subset_closure hzK, hzint⟩
  have hxle : f x + ε * w x ≤ f z + ε * w z := by
    simpa [smul_eq_mul] using hzmax hxK
  have hwzC : ε * w z ≤ ε * C :=
    mul_le_mul_of_nonneg_left (hC (Set.mem_image_of_mem w hzK)) hε.le
  nlinarith [mul_nonneg hε.le (hwpos x).le]

/-- **The weak minimum principle for elliptic operators in non-divergence form.** Under the
hypotheses of `le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`, a supersolution
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼf + bⁱ ∂ᵢf ≤ c f` is bounded below on `K` by every nonpositive lower bound `m` of
its values on `frontier K`. -/
theorem ge_of_sum_mul_fderiv_fderiv_add_fderiv_le_mul_ge_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ} {lam β m : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hm : m ≤ 0) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K →
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x) ≤ c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m ≤ f x := by
  intro x hx
  have h := le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier (f := -f) (m := -m) hK
    hlam ha hb hc (neg_nonneg.mpr hm) hcont.neg (fun y hy ↦ (hcd hy).neg)
    (fun y hy ↦ by
      rw [sum_mul_fderiv_fderiv_add_fderiv_neg, Pi.neg_apply, mul_neg]
      exact neg_le_neg (hsuper hy))
    (fun y hy ↦ by simpa using hbdry hy) hx
  simpa using h

/-- **The maximum principle for solutions.** Under the hypotheses of
`le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`, a solution of
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼf + bⁱ ∂ᵢf = c f` is bounded in absolute value on `K` by every bound for its absolute
value on `frontier K`. -/
theorem abs_le_of_sum_mul_fderiv_fderiv_add_fderiv_eq_mul_abs_le_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ} {lam β M : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hM : 0 ≤ M) (hcont : ContinuousOn f K) (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hsol : ∀ ⦃x⦄, x ∈ interior K →
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x) = c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) :
    ∀ ⦃x⦄, x ∈ K → |f x| ≤ M := fun _ hx ↦ abs_le.mpr
  ⟨ge_of_sum_mul_fderiv_fderiv_add_fderiv_le_mul_ge_frontier hK hlam ha hb hc
      (neg_nonpos.mpr hM) hcont hcd (fun _ hy ↦ (hsol hy).le) (fun _ hy ↦ (abs_le.mp (hbdry hy)).1)
      hx,
    le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hK hlam ha hb hc hM hcont hcd
      (fun _ hy ↦ (hsol hy).ge) (fun _ hy ↦ (abs_le.mp (hbdry hy)).2) hx⟩

/-- **The comparison principle for elliptic operators in non-divergence form.** Write
`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu - c u` with `a`, `b`, `c` as in
`le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`. If `f` and `g` are continuous on `K`
and `C²` on its interior, `L g ≤ L f` there and `f ≤ g` on `frontier K`, then `f ≤ g` on `K`. -/
theorem le_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f g : EuclideanSpace ℝ ι → ℝ} {lam β : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ g x (b x) - c x * g x ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x) - c x * f x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ g x) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ g x := by
  intro x hx
  have hfg : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  have h := le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier (f := f - g) (m := 0) hK
    hlam ha hb hc le_rfl (hfcont.sub hgcont) (fun y hy ↦ (hfcd hy).sub (hgcd hy))
    (fun y hy ↦ by
      rw [hfg, sum_mul_fderiv_fderiv_add_fderiv_add_smul (hfcd hy) (hgcd hy), ← hfg,
        Pi.sub_apply]
      linarith [hL hy])
    (fun y hy ↦ sub_nonpos.mpr (hbdry hy)) hx
  exact sub_nonpos.mp h

/-- **Uniqueness for the Dirichlet problem.** With `L` as in
`le_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_frontier`, two functions that are
continuous on `K`, `C²` on its interior, have the same values of `L` there and agree on
`frontier K` agree on `K`. -/
theorem eqOn_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_eq_of_eqOn_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f g : EuclideanSpace ℝ ι → ℝ} {lam β : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hfcont : ContinuousOn f K) (hgcont : ContinuousOn g K)
    (hfcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hgcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 g x)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x) - c x * f x =
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ g x (b x) - c x * g x)
    (hbdry : Set.EqOn f g (frontier K)) : Set.EqOn f g K := fun _ hx ↦ le_antisymm
  (le_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_frontier hK hlam ha hb hc hfcont
    hgcont hfcd hgcd (fun _ hy ↦ (hL hy).ge) (fun _ hy ↦ (hbdry hy).le) hx)
  (le_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_frontier hK hlam ha hb hc hgcont
    hfcont hgcd hfcd (fun _ hy ↦ (hL hy).le) (fun _ hy ↦ (hbdry hy).ge) hx)

/-- **The a priori bound for elliptic operators in non-divergence form.** Let `a`, `b`, `c` be as
in `le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`, and let `f`, continuous on `K` and
`C²` on its interior, satisfy `c f - F ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼf + bⁱ ∂ᵢf` there for a constant `F ≥ 0`.
Then every nonnegative bound `m` for `f` on `frontier K` gives

`f ≤ m + (exp ((β / λ + 1) diam K) - 1) F / λ` on `K`.

The constant depends only on `β / λ`, `λ` and the diameter of `K`. The hypothesis `0 ≤ β`, automatic
when `K` has interior points, keeps the bound valid when it has none. -/
theorem le_add_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ} {lam β m F : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hβ : 0 ≤ β) (hm : 0 ≤ m) (hF : 0 ≤ F) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hsub : ∀ ⦃x⦄, x ∈ interior K → c x * f x - F ≤
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x))
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) :
    ∀ ⦃x⦄, x ∈ K → f x ≤ m + (Real.exp ((β / lam + 1) * Metric.diam K) - 1) * F / lam := by
  intro x hxK
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ ι)
  set e : EuclideanSpace ℝ ι := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm hv
  set α := β / lam + 1
  set d := Metric.diam K
  -- Place `K` in the slab `s ≤ ⟪e, ·⟫ ≤ s + d`.
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn ⟨x, hxK⟩
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ ι ↦ ⟪e, y⟫).continuousOn
  have hslab (y : EuclideanSpace ℝ ι) (hy : y ∈ K) :
      0 ≤ ⟪e, y⟫ - ⟪e, x₀⟫ ∧ ⟪e, y⟫ - ⟪e, x₀⟫ ≤ d := by
    refine ⟨sub_nonneg.mpr (hx₀ hy), ?_⟩
    rw [← inner_sub_right]
    calc ⟪e, y - x₀⟫ ≤ ‖e‖ * ‖y - x₀‖ := real_inner_le_norm _ _
      _ = dist y x₀ := by rw [he, one_mul, dist_eq_norm]
      _ ≤ d := Metric.dist_le_diam_of_mem hK.isBounded hy hx₀K
  -- The comparison function `g = m + (F / λ) (exp (α d) - exp (α (⟪e, ·⟫ - s)))`.
  set w : EuclideanSpace ℝ ι → ℝ := fun y ↦ Real.exp (α * ⟪e, y⟫)
  have hwcd : ContDiff ℝ 2 w := (contDiff_exp_inner _ e).of_le (by norm_cast)
  set r := F / lam * Real.exp (-(α * ⟪e, x₀⟫))
  set g : EuclideanSpace ℝ ι → ℝ := (fun _ ↦ m + F / lam * Real.exp (α * d)) + (-r) • w
  have hrw (y : EuclideanSpace ℝ ι) : r * w y = F / lam * Real.exp (α * (⟪e, y⟫ - ⟪e, x₀⟫)) := by
    simp only [r, w, mul_assoc, ← Real.exp_add]
    ring_nf
  have hg (y : EuclideanSpace ℝ ι) : g y = m + F / lam * Real.exp (α * d) - r * w y := by
    simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hα : 1 ≤ α := le_add_of_nonneg_left (div_nonneg hβ hlam.le)
  have hFl : 0 ≤ F / lam := div_nonneg hF hlam.le
  -- On `K`, `F / λ ≤ r w ≤ (F / λ) exp (α d)`, so `m ≤ g ≤ m + (exp (α d) - 1) F / λ`.
  have hrwK (y : EuclideanSpace ℝ ι) (hy : y ∈ K) :
      F / lam ≤ r * w y ∧ r * w y ≤ F / lam * Real.exp (α * d) := by
    rw [hrw]
    obtain ⟨h0, hd⟩ := hslab y hy
    exact ⟨le_mul_of_one_le_right hFl (Real.one_le_exp (by positivity)),
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hd (by positivity))) hFl⟩
  have hgcd : ContDiff ℝ 2 g := contDiff_const.add (hwcd.const_smul (-r))
  -- `g` is a supersolution: `L g - c g ≤ -F`.
  have hLg (y : EuclideanSpace ℝ ι) (hy : y ∈ interior K) :
      ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ g y (b y) - c y * g y ≤ -F := by
    have hyK := interior_subset hy
    have hLw : α * lam * w y ≤ ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ w) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ w y (b y) :=
      mul_exp_le_sum_mul_fderiv_fderiv_add_fderiv_exp_inner hlam (ha hy) he (hb hy) y
    have hr : 0 ≤ r := by positivity
    have hcg : 0 ≤ c y * g y := mul_nonneg (hc hy) (by linarith [hg y, (hrwK y hyK).2])
    rw [sum_mul_fderiv_fderiv_add_fderiv_add_smul contDiffAt_const hwcd.contDiffAt]
    simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, _root_.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, neg_mul]
    -- `r L w ≥ α λ (r w) ≥ α λ (F / λ) = α F ≥ F`.
    have h1 : r * (α * lam * w y) = α * lam * (r * w y) := by ring
    have h2 : α * lam * (F / lam) = α * F := by field_simp
    have h3 := mul_le_mul_of_nonneg_left (hrwK y hyK).1 (by positivity : 0 ≤ α * lam)
    have h4 : F ≤ α * F := le_mul_of_one_le_left hF hα
    linarith [mul_le_mul_of_nonneg_left hLw hr]
  have hfg : f x ≤ g x := le_of_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_of_le_frontier hK hlam
    ha hb hc hcont hgcd.continuous.continuousOn hcd (fun _ _ ↦ hgcd.contDiffAt)
    (fun y hy ↦ (hLg y hy).trans (by linarith [hsub hy]))
    (fun y hy ↦ (hbdry hy).trans (by
      linarith [hg y, (hrwK y (hK.isClosed.frontier_subset hy)).2]))
    hxK
  have hbound : (Real.exp (α * d) - 1) * F / lam = F / lam * Real.exp (α * d) - F / lam := by
    ring
  linarith [hg x, (hrwK x hxK).1]

/-- **The a priori lower bound for elliptic operators in non-divergence form.** Under the
hypotheses of `le_add_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`, but with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼf + bⁱ ∂ᵢf ≤ c f + F` on the interior of `K`, every nonpositive lower bound `m` for
`f` on `frontier K` gives

`m - (exp ((β / λ + 1) diam K) - 1) F / λ ≤ f` on `K`. -/
theorem sub_le_of_sum_mul_fderiv_fderiv_add_fderiv_le_mul_add_ge_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ} {lam β m F : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hβ : 0 ≤ β) (hm : m ≤ 0) (hF : 0 ≤ F) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hsuper : ∀ ⦃x⦄, x ∈ interior K →
      ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x) ≤ c x * f x + F)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ f x) :
    ∀ ⦃x⦄, x ∈ K → m - (Real.exp ((β / lam + 1) * Metric.diam K) - 1) * F / lam ≤ f x := by
  intro x hx
  have h := le_add_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier (f := -f) (m := -m)
    hK hlam ha hb hc hβ (neg_nonneg.mpr hm) hF hcont.neg (fun y hy ↦ (hcd hy).neg)
    (fun y hy ↦ by
      rw [sum_mul_fderiv_fderiv_add_fderiv_neg, Pi.neg_apply, mul_neg]
      linarith [hsuper hy])
    (fun y hy ↦ by simpa using hbdry hy) hx
  rw [Pi.neg_apply] at h
  linarith

/-- **The a priori bound on `sup |u|` for elliptic operators in non-divergence form.** Let `a`,
`b`, `c` be as in `le_of_mul_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier`, and let `f`,
continuous on `K` and `C²` on its interior, satisfy `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼf + bⁱ ∂ᵢf - c f| ≤ F` there.
Then every bound `M` for `|f|` on `frontier K` gives

`|f| ≤ M + (exp ((β / λ + 1) diam K) - 1) F / λ` on `K`. -/
theorem abs_le_add_of_abs_sum_mul_fderiv_fderiv_add_fderiv_sub_mul_le_abs_le_frontier
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c f : EuclideanSpace ℝ ι → ℝ} {lam β M F : ℝ}
    (hlam : 0 < lam)
    (ha : ∀ ⦃x⦄, x ∈ interior K → ∀ ξ : EuclideanSpace ℝ ι,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ interior K → ‖b x‖ ≤ β) (hc : ∀ ⦃x⦄, x ∈ interior K → 0 ≤ c x)
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (hF : 0 ≤ F) (hcont : ContinuousOn f K)
    (hcd : ∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x)
    (hL : ∀ ⦃x⦄, x ∈ interior K →
      |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ f x (b x) - c x * f x| ≤ F)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → |f x| ≤ M) :
    ∀ ⦃x⦄, x ∈ K → |f x| ≤ M + (Real.exp ((β / lam + 1) * Metric.diam K) - 1) * F / lam := by
  intro x hx
  have hle := le_add_of_mul_sub_le_sum_mul_fderiv_fderiv_add_fderiv_le_frontier hK hlam ha hb hc
    hβ hM hF hcont hcd (fun _ hy ↦ by linarith [(abs_le.mp (hL hy)).1])
    (fun _ hy ↦ (abs_le.mp (hbdry hy)).2) hx
  have hge := sub_le_of_sum_mul_fderiv_fderiv_add_fderiv_le_mul_add_ge_frontier hK hlam ha hb hc
    hβ (neg_nonpos.mpr hM) hF hcont hcd (fun _ hy ↦ by linarith [(abs_le.mp (hL hy)).2])
    (fun _ hy ↦ (abs_le.mp (hbdry hy)).1) hx
  exact abs_le.mpr ⟨by linarith, hle⟩

end PDE

end TauCeti
