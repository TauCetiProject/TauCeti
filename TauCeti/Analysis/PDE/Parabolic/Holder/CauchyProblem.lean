/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Backward
public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
public import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The parabolic Cauchy problem with Hölder coefficients

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}`, with
`0 < α < 1`, and let `a` be uniformly elliptic, `λ ‖ξ‖² ≤ ξᵀ a(p) ξ` with `0 < λ`. This file
proves that the Cauchy problem

`P u = f`,  `u(·, 0) = g`

is well posed in the bounded order-two parabolic Hölder space: for every forcing
`f ∈ C_b^{α,α/2}` and initial datum `g ∈ C_b^{2,α}` it has exactly one solution
`u ∈ C_b^{2+α,1+α/2}`, and the data map `u ↦ (P u, u(·, 0))` is an isomorphism of Banach spaces
`C_b^{2+α,1+α/2} → C_b^{α,α/2} × C_b^{2,α}`
(`isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL`).
The norm of its inverse is bounded uniformly over the coefficients with given ellipticity
constants and Hölder norms, and over the horizons `T ≤ T₀`
(`exists_isInvertible_euclideanParabolicOperatorL_prod_and_norm_inverse_le`).
No symmetry of `a` and no sign condition on `c` is needed.

By time reversal `(x, s) ↦ (x, T - s)`, the same holds for the terminal-value problem of the
backward operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u`: the map `u ↦ (P_back u, u(·, T))`
is an isomorphism (`isInvertible_euclideanBackwardParabolicOperatorL_prod_spatialTraceL`).

## The argument

This is the method of continuity (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`),
started from the heat operator. Along the segment of coefficients

`a_θ = (1 - θ) I + θ a`, `b_θ = θ b`, `c_θ = θ c`, `0 ≤ θ ≤ 1`,

the operators `P_θ` are the affine interpolation of the heat operator and `P`
(`euclideanParabolicOperatorL_lineMap`). The coefficients `a_θ` are elliptic with the lower
constant `min 1 λ`, and all coefficients on the segment have Hölder norms at most `max 1 K`, which
also bounds `ξᵀ a_θ ξ / ‖ξ‖²` from above. So the global Schauder estimate
(`exists_norm_le_euclideanParabolicOperatorL`) holds along the whole segment with one constant.
Since the heat operator's data map is onto
(`bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL`), so is that of `P`, and the
estimate makes it invertible with a bounded inverse.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `exists_isInvertible_euclideanParabolicOperatorL_prod_and_norm_inverse_le`: the data map
  `u ↦ (P u, u(·, 0))` is invertible, with an inverse bound uniform over the coefficient class and
  over bounded horizons.
* `isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL`: the Cauchy problem is well posed
  for each elliptic Hölder coefficient triple.
* `isInvertible_euclideanBackwardParabolicOperatorL_prod_spatialTraceL`: the terminal-value
  problem for the backward operator is well posed.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity) and Theorem 6.8 (its elliptic application).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι]

section CauchyProblem

variable {T : ℝ≥0} {hT : (0 : ℝ) < T}

/-- A local shortcut for the norm on covectors, needed to state the type of the first-order
coefficient field outside `parabolicOperatorL`, as in `Operator.lean`. -/
local instance euclideanCovectorNormedAddCommGroup :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on covectors. -/
local instance euclideanCovectorNormedSpace : NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for the norm on Euclidean Hessians, needed for the same reason for the
second-order coefficient field. -/
local instance euclideanHessianNormedAddCommGroup :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for scalar operations on Euclidean Hessians. -/
local instance euclideanHessianNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance

/-- A bound on the entries of a coefficient matrix field is an upper ellipticity bound. -/
private theorem toQuadraticForm'_le_of_norm_le
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ} {K : ℝ}
    (hak : ∀ i j, ‖a i j‖ ≤ K) (p : slab (E := EuclideanSpace ℝ ι) 0 T)
    (ξ : EuclideanSpace ℝ ι) :
    (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Fintype.card ι ^ 2 * K * ‖ξ‖ ^ 2 := by
  refine (Matrix.toQuadraticForm'_le_sum_abs_mul_sq _ ξ).trans
    (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  calc ∑ i, ∑ j, |Matrix.of (fun i j ↦ a i j p) i j| ≤ ∑ _i : ι, ∑ _j : ι, K :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
          simpa only [Matrix.of_apply, Real.norm_eq_abs] using
            (HolderSpace.norm_apply_le (a i j) p).trans (hak i j)
    _ = Fintype.card ι ^ 2 * K := by simp [sq, mul_assoc]

/-- The quadratic form of the coefficients `(1 - θ) I + θ a` on the segment from the identity. -/
private theorem toQuadraticForm'_lineMap
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) (θ : ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) (ξ : EuclideanSpace ℝ ι) :
    (Matrix.of fun i j ↦ AffineMap.lineMap
        (fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)) a θ i j p).toQuadraticForm' ξ =
      (1 - θ) * ‖ξ‖ ^ 2 + θ * (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ := by
  have h : (Matrix.of fun i j ↦ AffineMap.lineMap
      (fun i j ↦ HolderSpace.const (α := α) ((1 : Matrix ι ι ℝ) i j)) a θ i j p) =
      (1 - θ) • (1 : Matrix ι ι ℝ) + θ • Matrix.of fun i j ↦ a i j p := by
    ext i j
    simp [AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module, HolderSpace.const_apply]
  rw [h, Matrix.toQuadraticForm'_add, _root_.add_apply, PDE.toQuadraticForm'_smul_one,
    Matrix.toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul]

/-- **The parabolic Cauchy problem with Hölder coefficients is well posed, uniformly.** For
`0 < α < 1`, a lower ellipticity constant `λ > 0`, a bound `K` on the Hölder norms of the
coefficients and a bound `T₀` on the horizon, there is a constant `C` such that on
`ℝⁿ × [0, T]`, `T ≤ T₀`, the data map `u ↦ (P u, u(·, 0))` of
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`, from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2} × C_b^{2,α}`, is
invertible with inverse of norm at most `C`, whenever `λ ‖ξ‖² ≤ ξᵀ a(p) ξ`. So for every forcing
`f` and initial datum `g` the Cauchy problem `P u = f`, `u(·, 0) = g` has exactly one solution `u`,
and `‖u‖_{2+α,par} ≤ C max (‖f‖_{α,par}, ‖g‖_{2,α})`. -/
theorem exists_isInvertible_euclideanParabolicOperatorL_prod_and_norm_inverse_le (hα₀ : 0 < α)
    (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ((euclideanParabolicOperatorL hα₁.le a b c).prod
            (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).IsInvertible ∧
          ‖((euclideanParabolicOperatorL hα₁.le a b c).prod
            (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).inverse‖ ≤ C := by
  -- The Schauder estimate for the whole segment from the heat operator to `P`: along it the
  -- ellipticity constant is `min 1 λ` and the coefficient norms are at most `max 1 K`.
  set m := min 1 lam
  set K' := max 1 K
  obtain ⟨C₀, hC₀, hest⟩ := exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁
    (Lam := Fintype.card ι ^ 2 * K') (lt_min one_pos hlam) K' T₀
  refine ⟨2 * C₀, by positivity, fun T hT hTT₀ a b c ha hak hbk hck ↦ ?_⟩
  set t₀ : Icc (0 : ℝ) T := ⟨0, left_mem_Icc.2 hT.le⟩
  set a₀ : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ :=
    fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)
  set L₀ := (euclideanParabolicOperatorL hα₁.le a₀ 0 0).prod
    (spatialTraceL (F := ℝ) (hab := hT) t₀)
  set L₁ := (euclideanParabolicOperatorL hα₁.le a b c).prod
    (spatialTraceL (F := ℝ) (hab := hT) t₀)
  have hK' : (1 : ℝ) ≤ K' := le_max_left _ _
  have hKK' : (K : ℝ) ≤ K' := le_max_right _ _
  have hpath : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ u, ‖u‖ ≤ 2 * C₀ * ‖AffineMap.lineMap L₀ L₁ θ u‖ := by
    intro θ hθ u
    set aθ := AffineMap.lineMap a₀ a θ
    set bθ := AffineMap.lineMap (0 : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      b θ
    set cθ := AffineMap.lineMap (0 : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) c θ
    have hL : AffineMap.lineMap L₀ L₁ θ u =
        (euclideanParabolicOperatorL hα₁.le aθ bθ cθ u, u.spatialTrace t₀) := by
      rw [← euclideanParabolicOperatorL_lineMap]
      simp only [L₀, L₁, AffineMap.lineMap_apply_module, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.prod_apply, Prod.smul_mk, Prod.mk_add_mk, spatialTraceL_apply,
        ← add_smul, sub_add_cancel, one_smul]
    -- The coefficients on the segment satisfy the hypotheses of the Schauder estimate.
    have hseg : ∀ x y : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ,
        ‖x‖ ≤ K' → ‖y‖ ≤ K' → ‖AffineMap.lineMap x y θ‖ ≤ K' := fun x y hx hy ↦ by
      simpa using (convex_closedBall (0 : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        K').lineMap_mem (by simpa using hx) (by simpa using hy) hθ
    have haθ : ∀ i j, ‖aθ i j‖ ≤ K' := fun i j ↦ by
      simp only [aθ, AffineMap.pi_lineMap_apply]
      refine hseg _ _ ((HolderSpace.norm_const_le _).trans ?_) ((hak i j).trans hKK')
      rw [Matrix.one_apply]
      split_ifs <;> simp [hK', zero_le_one.trans hK']
    have hbθ : ∀ i, ‖bθ i‖ ≤ K' := fun i ↦ by
      simp only [bθ, AffineMap.pi_lineMap_apply]
      exact hseg _ _ (by simp) ((hbk i).trans hKK')
    have hcθ : ‖cθ‖ ≤ K' :=
      hseg _ _ (by simp) (hck.trans hKK')
    have hlow : ∀ p (ξ : EuclideanSpace ℝ ι),
        m * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ aθ i j p).toQuadraticForm' ξ := fun p ξ ↦ by
      rw [toQuadraticForm'_lineMap]
      have h₁ : m * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (min_le_left _ _)
      have h₂ : m * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ :=
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (ha p ξ)
      nlinarith [mul_le_mul_of_nonneg_left h₁ (sub_nonneg.2 hθ.2),
        mul_le_mul_of_nonneg_left h₂ hθ.1]
    have h := hest T hT hTT₀ aθ bθ cθ hlow (toQuadraticForm'_le_of_norm_le haθ) haθ hbθ hcθ u
    rw [hL, Prod.norm_mk]
    calc ‖u‖ ≤ C₀ * (‖euclideanParabolicOperatorL hα₁.le aθ bθ cθ u‖ + ‖u.spatialTrace t₀‖) := h
      _ ≤ C₀ * (max ‖euclideanParabolicOperatorL hα₁.le aθ bθ cθ u‖ ‖u.spatialTrace t₀‖ +
          max ‖euclideanParabolicOperatorL hα₁.le aθ bθ cθ u‖ ‖u.spatialTrace t₀‖) := by
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]
      _ = _ := by ring
  -- The heat operator's data map is onto, hence so is that of `P`.
  have h₀ : Function.Surjective L₀ :=
    (bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL hα₀ hα₁ (A := 1) one_pos
      (fun ξ ↦ by rw [PDE.toQuadraticForm'_one, one_mul]) hT).2
  have h₁ : Function.Surjective L₁ :=
    (ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap hpath).1 h₀
  have hest₁ : ∀ u, ‖u‖ ≤ 2 * C₀ * ‖L₁ u‖ := fun u ↦ by
    simpa using hpath 1 (right_mem_Icc.2 zero_le_one) u
  refine ⟨ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le h₁ hest₁,
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_⟩
  -- `exact` fails to unify the two norm instances on the solution space, whose definition is not
  -- exposed to unfolding here; `convert` matches them structurally.
  convert ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le h₁ hest₁ y using 1

/-- **The parabolic Cauchy problem with Hölder coefficients is well posed.** For `0 < α < 1`,
coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}` on `ℝⁿ × [0, T]` with `λ ‖ξ‖² ≤ ξᵀ a(p) ξ` for
some `λ > 0`, the data map `u ↦ (P u, u(·, 0))` of `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` is an
isomorphism from `C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`: the Cauchy problem
`P u = f`, `u(·, 0) = g` has exactly one solution, depending continuously on `(f, g)`. -/
theorem isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α) (hα₁ : α < 1)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ((euclideanParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).IsInvertible := by
  -- Any common bound on the coefficient norms will do.
  set K : ℝ≥0 := ∑ i, ∑ j, ‖a i j‖₊ + ∑ i, ‖b i‖₊ + ‖c‖₊
  have hak : ∀ i j, ‖a i j‖ ≤ K := fun i j ↦ by
    have h : ‖a i j‖₊ ≤ K :=
      ((Finset.single_le_sum (fun j _ ↦ zero_le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖₊) (fun i _ ↦ zero_le)
          (Finset.mem_univ i))).trans (le_add_right (le_add_right le_rfl))
    exact_mod_cast h
  have hbk : ∀ i, ‖b i‖ ≤ K := fun i ↦ by
    have h : ‖b i‖₊ ≤ K :=
      (Finset.single_le_sum (f := fun i ↦ ‖b i‖₊) (fun i _ ↦ zero_le) (Finset.mem_univ i)).trans
        (le_add_right (le_add_left le_rfl))
    exact_mod_cast h
  have hck : ‖c‖ ≤ K := by
    have h : ‖c‖₊ ≤ K := le_add_left le_rfl
    exact_mod_cast h
  obtain ⟨C, -, hC⟩ := exists_isInvertible_euclideanParabolicOperatorL_prod_and_norm_inverse_le
    (ι := ι) hα₀ hα₁ hlam K T
  exact (hC T hT le_rfl a b c ha hak hbk hck).1

/-- **The terminal-value problem for the backward operator is well posed.** For `0 < α < 1`,
coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}` on `ℝⁿ × [0, T]` with `λ ‖ξ‖² ≤ ξᵀ a(p) ξ` for
some `λ > 0`, the data map `u ↦ (P_back u, u(·, T))` of
`P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` is an isomorphism from `C_b^{2+α,1+α/2}` onto
`C_b^{α,α/2} × C_b^{2,α}`. By time reversal `(x, s) ↦ (x, T - s)` this is the well-posedness of
the forward Cauchy problem with the reversed coefficients. -/
theorem isInvertible_euclideanBackwardParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α)
    (hα₁ : α < 1) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ((euclideanBackwardParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨T, right_mem_Icc.2 hT.le⟩)).IsInvertible := by
  -- Reverse time about `T`, which maps the slab `[0, T]` onto itself.
  set R := slabTimeReverse (E := EuclideanSpace ℝ ι) (T : ℝ) (sub_self (T : ℝ)).symm
    (sub_zero (T : ℝ)).symm
  have hA : HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (euclideanSecondOrderCoeff a) =
      euclideanSecondOrderCoeff fun i j ↦
        HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (a i j) := by
    ext p H
    simp [HolderSpace.compLipschitzL_apply]
  have hB : HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (euclideanFirstOrderCoeff b) =
      euclideanFirstOrderCoeff fun i ↦
        HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (b i) := by
    ext p v
    simp [HolderSpace.compLipschitzL_apply]
  have hC : HolderSpace.compLipschitzL _ R.isometry.lipschitzWith (euclideanZerothOrderCoeff c) =
      euclideanZerothOrderCoeff (HolderSpace.compLipschitzL _ R.isometry.lipschitzWith c) := by
    ext p
    simp [HolderSpace.compLipschitzL_apply]
  rw [ContinuousLinearMap.isInvertible_iff_bijective, euclideanBackwardParabolicOperatorL_def,
    bijective_backwardParabolicOperatorL_prod_spatialTraceL_iff (T := T)
      (ha := (sub_self (T : ℝ)).symm) (hb := (sub_zero (T : ℝ)).symm), hA, hB, hC,
    ← euclideanParabolicOperatorL_def]
  exact (isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hlam
    fun p ξ ↦ by simpa [HolderSpace.compLipschitzL_apply] using ha (R p) ξ).bijective

end CauchyProblem

end TauCeti.ParabolicC2HolderSpace
