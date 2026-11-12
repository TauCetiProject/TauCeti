/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Backward
public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# The parabolic Cauchy problem with variable coefficients

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, `T > 0`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded parabolic Hölder space `C_b^{α,α/2}`, with
`0 < α < 1`, and let `a` be uniformly elliptic: `lam ‖ξ‖² ≤ ξᵀ a(p) ξ` at every point `p`, with
`0 < lam`. This file proves that the Cauchy problem

`P u = f`,  `u(·, 0) = g`

is well posed in the bounded order-two parabolic Hölder space: the initial-data map
`u ↦ (P u, u(·, 0))` is an isomorphism of Banach spaces from `C_b^{2+α,1+α/2}` onto
`C_b^{α,α/2} × C_b^{2,α}`
(`TauCeti.ParabolicC2HolderSpace.isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL`).
Its inverse, the solution operator `(f, g) ↦ u`, is bounded uniformly over coefficients with fixed
ellipticity and norm bounds and over horizons `T ≤ T₀`, and it depends continuously on the
coefficients in operator norm. No symmetry of `a` and no sign condition on `c` is needed. By time
reversal, the terminal-value problem `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f`, `u(·, T) = g` is well
posed as well.

## The argument

This is the method of continuity (`IsPreconnected.isInvertible_of_forall_norm_le`) along the
segment of initial-data maps `L_s = (1 - s) L_heat + s L_P`, `s ∈ [0, 1]`, starting from the heat
operator. Since `P` is affine in its coefficients (`euclideanParabolicOperatorL_lineMap`), `L_s` is
the initial-data map of the operator with coefficients `(1 - s) 1 + s a`, `s b` and `s c`. These
satisfy the ellipticity bounds `min 1 lam` and `max 1 Lam` and the norm bound `1 + K` uniformly in
`s`, so the global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`) gives the a priori
estimate `‖u‖ ≤ C ‖L_s u‖` with `C` independent of `s`. The heat operator is invertible by the
constant-coefficient theory
(`TauCeti.ParabolicC2HolderSpace.bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL`),
hence so is `L_1`, the initial-data map of `P`.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL` and
  `bijective_euclideanParabolicOperatorL_prod_spatialTraceL`: the initial-data map is an
  isomorphism.
* `exists_norm_inverse_euclideanParabolicOperatorL_prod_spatialTraceL_le`: the uniform bound on
  the solution operator.
* `continuousAt_inverse_euclideanParabolicOperatorL_prod_spatialTraceL`: continuity of the
  solution operator in the coefficients.
* `bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL`: the terminal-value problem.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (Theorem 8.9.2).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2 (the method of continuity) and its use in Theorem 6.8.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A local shortcut for the norm on Euclidean Hessians, needed to state the reversed second-order
coefficient field: the norm instance on the domain of the coefficient space only arises as a nested
instance problem during unification. -/
private local instance instHessianNorm :
    NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance
/-- A local shortcut for scalar operations on Euclidean Hessians. -/
private local instance instHessianSpace :
    NormedSpace ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance

/-! ### The path from the heat operator -/

section Path

variable {T : ℝ≥0} {hT : (0 : ℝ) < T}

/-- The coefficients of the heat operator: the identity matrix. -/
private abbrev heatCoeff : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ :=
  fun i j ↦ HolderSpace.const ((1 : Matrix ι ι ℝ) i j)

/-- Along the segment from the identity to `a`, the matrix of coefficients at `p` is
`(1 - s) 1 + s a(p)`. -/
private theorem of_lineMap_heatCoeff_apply
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) (s : ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    (Matrix.of fun i j ↦ AffineMap.lineMap heatCoeff a s i j p) =
      (1 - s) • (1 : Matrix ι ι ℝ) + s • Matrix.of fun i j ↦ a i j p := by
  ext i j
  simp [AffineMap.lineMap_apply_module]

/-- Ellipticity along the segment from the identity: if `lam ‖ξ‖² ≤ ξᵀ a ξ ≤ Lam ‖ξ‖²`, then every
convex combination of `1` and `a` satisfies the bounds with `min 1 lam` and `max 1 Lam`. -/
private theorem lineMap_heatCoeff_ellipticity
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ} {lam Lam : ℝ}
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
      (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (p : slab (E := EuclideanSpace ℝ ι) 0 T)
    (ξ : EuclideanSpace ℝ ι) :
    min 1 lam * ‖ξ‖ ^ 2 ≤
        (Matrix.of fun i j ↦ AffineMap.lineMap heatCoeff a s i j p).toQuadraticForm' ξ ∧
      (Matrix.of fun i j ↦ AffineMap.lineMap heatCoeff a s i j p).toQuadraticForm' ξ ≤
        max 1 Lam * ‖ξ‖ ^ 2 := by
  rw [of_lineMap_heatCoeff_apply, Matrix.toQuadraticForm'_add, Matrix.toQuadraticForm'_smul,
    Matrix.toQuadraticForm'_smul, _root_.add_apply, _root_.smul_apply,
    _root_.smul_apply, PDE.toQuadraticForm'_one, smul_eq_mul, smul_eq_mul]
  have h₁ := ha p ξ
  have h₂ := ha' p ξ
  have hξ := sq_nonneg ‖ξ‖
  have hs₀ : 0 ≤ 1 - s := sub_nonneg.2 hs.2
  constructor
  · have hm₁ : min 1 lam * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 :=
      mul_le_of_le_one_left hξ (min_le_left _ _)
    have hm₂ : min 1 lam * ‖ξ‖ ^ 2 ≤ lam * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hξ
    nlinarith [mul_le_mul_of_nonneg_left hm₁ hs₀, mul_le_mul_of_nonneg_left (hm₂.trans h₁) hs.1]
  · have hM₁ : ‖ξ‖ ^ 2 ≤ max 1 Lam * ‖ξ‖ ^ 2 :=
      le_mul_of_one_le_left hξ (le_max_left _ _)
    have hM₂ : Lam * ‖ξ‖ ^ 2 ≤ max 1 Lam * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hξ
    nlinarith [mul_le_mul_of_nonneg_left hM₁ hs₀, mul_le_mul_of_nonneg_left (h₂.trans hM₂) hs.1]

/-- A convex combination of two elements of norm at most `K₀` and `K` has norm at most
`K₀ + K`. -/
private theorem norm_lineMap_le {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {x y : V} {K₀ K : ℝ} (hx : ‖x‖ ≤ K₀) (hy : ‖y‖ ≤ K)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖AffineMap.lineMap x y s‖ ≤ K₀ + K := by
  rw [AffineMap.lineMap_apply_module]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hs.2), Real.norm_of_nonneg hs.1]
  have h₁ : (1 - s) * ‖x‖ ≤ K₀ :=
    (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hs.1])).trans hx
  have h₂ : s * ‖y‖ ≤ K := (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans hy
  linarith

/-- The segment of initial-data operators from the heat operator to `P` is the initial-data
operator of the segment of coefficients. -/
private theorem lineMap_prod_spatialTraceL (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) (s : ℝ) :
    AffineMap.lineMap
        ((euclideanParabolicOperatorL hα heatCoeff 0 0).prod
          (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩))
        ((euclideanParabolicOperatorL hα a b c).prod
          (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) s =
      (euclideanParabolicOperatorL hα (AffineMap.lineMap heatCoeff a s)
          (AffineMap.lineMap 0 b s) (AffineMap.lineMap 0 c s)).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩) := by
  rw [euclideanParabolicOperatorL_lineMap]
  ext1 u
  simp only [AffineMap.lineMap_apply_module, _root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.prod_apply, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel,
    one_smul]

/-- **The a priori estimate along the method-of-continuity path.** For `0 < α < 1`, `0 < lam` and
bounds `K` and `T₀`, there is `C` such that for every horizon `T ≤ T₀`, all coefficients with
`lam ‖ξ‖² ≤ ξᵀ a ξ` and Hölder norms at most `K`, and every `s ∈ [0, 1]`, the initial-data operator
`L_s = (1 - s) L_heat + s L_P` satisfies `‖u‖ ≤ C ‖L_s u‖`. -/
private theorem exists_norm_le_lineMap (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam)
    (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
          ‖u‖ ≤ C * ‖AffineMap.lineMap
            ((euclideanParabolicOperatorL hα₁.le heatCoeff 0 0).prod
              (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩))
            ((euclideanParabolicOperatorL hα₁.le a b c).prod
              (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) s u‖ := by
  -- An entry bound `K` is the upper ellipticity bound `∑ᵢⱼ K`.
  set Lam : ℝ := ∑ _i : ι, ∑ _j : ι, (K : ℝ)
  obtain ⟨C, hC₀, hC⟩ := exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁
    (lt_min one_pos hlam) (Lam := max 1 Lam) (1 + K) T₀
  refine ⟨2 * C, by positivity, fun T hT hTT₀ a b c ha hak hbk hck s hs u ↦ ?_⟩
  have ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
      (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 := fun p ξ ↦
    (Matrix.toQuadraticForm'_le_sum_abs_mul_sq _ ξ).trans (mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        (HolderSpace.norm_apply_le (a i j) p).trans (hak i j)) (sq_nonneg _))
  have h := hC T hT hTT₀ (AffineMap.lineMap heatCoeff a s) (AffineMap.lineMap 0 b s)
    (AffineMap.lineMap 0 c s) (fun p ξ ↦ (lineMap_heatCoeff_ellipticity ha ha' hs p ξ).1)
    (fun p ξ ↦ (lineMap_heatCoeff_ellipticity ha ha' hs p ξ).2)
    (fun i j ↦ by
      push_cast
      exact norm_lineMap_le ((HolderSpace.norm_const_le _).trans (by
        rw [Matrix.one_apply]; split_ifs <;> simp)) (hak i j) hs)
    (fun i ↦ by
      push_cast
      exact norm_lineMap_le (by simp) (hbk i) hs)
    (by
      push_cast
      exact norm_lineMap_le (by simp) hck hs) u
  rw [lineMap_prod_spatialTraceL, ContinuousLinearMap.prod_apply, Prod.norm_mk,
    spatialTraceL_apply]
  refine h.trans ?_
  rw [mul_assoc, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (by
    linarith [le_max_left ‖euclideanParabolicOperatorL hα₁.le (AffineMap.lineMap heatCoeff a s)
        (AffineMap.lineMap 0 b s) (AffineMap.lineMap 0 c s) u‖
        ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖,
      le_max_right ‖euclideanParabolicOperatorL hα₁.le (AffineMap.lineMap heatCoeff a s)
        (AffineMap.lineMap 0 b s) (AffineMap.lineMap 0 c s) u‖
        ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖]) hC₀

end Path

/-! ### Solvability of the forward problem -/

section Forward

variable {T : ℝ≥0}

/-- **The Cauchy problem with variable coefficients is well posed.** For `0 < α < 1`, a horizon
`T > 0` and coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}(ℝⁿ × [0, T])` with
`lam ‖ξ‖² ≤ ξᵀ a ξ` and `0 < lam`, the initial-data map
`u ↦ (∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u, u(·, 0))` is an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`. No symmetry of `a` and no sign condition on `c`
is needed. -/
theorem isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ((euclideanParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).IsInvertible := by
  -- One bound `K` for all the coefficient norms.
  set K : ℝ≥0 := ∑ i, ∑ j, ‖a i j‖₊ + ∑ i, ‖b i‖₊ + ‖c‖₊
  have hak (i j : ι) : ‖a i j‖ ≤ K := by
    have h : ‖a i j‖₊ ≤ ∑ i, ∑ j, ‖a i j‖₊ :=
      (Finset.single_le_sum (f := fun j ↦ ‖a i j‖₊) (fun _ _ ↦ zero_le)
        (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖₊)
          (fun _ _ ↦ zero_le) (Finset.mem_univ i))
    exact_mod_cast h.trans (le_add_right (le_add_right le_rfl))
  have hbk (i : ι) : ‖b i‖ ≤ K := by
    have h : ‖b i‖₊ ≤ ∑ i, ‖b i‖₊ :=
      Finset.single_le_sum (f := fun i ↦ ‖b i‖₊) (fun _ _ ↦ zero_le) (Finset.mem_univ i)
    exact_mod_cast h.trans (le_add_right (le_add_left le_rfl))
  have hck : ‖c‖ ≤ K := by
    exact_mod_cast (le_add_left le_rfl : ‖c‖₊ ≤ K)
  obtain ⟨C, -, hC⟩ := exists_norm_le_lineMap (ι := ι) hα₀ hα₁ hlam K T
  -- The heat operator is surjective, by the constant-coefficient theory.
  have h₀ := (bijective_euclideanParabolicOperatorL_const_prod_spatialTraceL hα₀ hα₁ one_pos
    (A := (1 : Matrix ι ι ℝ)) (fun ξ ↦ by rw [one_mul, PDE.toQuadraticForm'_one]) hT).2
  have h := isPreconnected_Icc.isInvertible_of_forall_norm_le
    AffineMap.lineMap_continuous.continuousOn (hC T hT le_rfl a b c ha hak hbk hck)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    (by rwa [AffineMap.lineMap_apply_zero])
  rwa [AffineMap.lineMap_apply_one] at h

/-- **Existence and uniqueness for the Cauchy problem with variable coefficients.** Under the
hypotheses of `isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL`, for every forcing
`f ∈ C_b^{α,α/2}` and initial datum `g ∈ C_b^{2,α}` there is exactly one `u ∈ C_b^{2+α,1+α/2}` with
`∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u = f` and `u(·, 0) = g`. -/
theorem bijective_euclideanParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective ((euclideanParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) :=
  (isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT b c hlam ha).bijective

/-- **The solution operator of the Cauchy problem is uniformly bounded.** For `0 < α < 1`,
`0 < lam` and bounds `K` and `T₀`, there is `C` such that for every horizon `0 < T ≤ T₀` and all
coefficients with `lam ‖ξ‖² ≤ ξᵀ a ξ` and Hölder norms at most `K`, the solution operator
`(f, g) ↦ u` of `∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u = f`, `u(·, 0) = g` has norm at most `C`. -/
theorem exists_norm_inverse_euclideanParabolicOperatorL_prod_spatialTraceL_le (hα₀ : 0 < α)
    (hα₁ : α < 1) {lam : ℝ} (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ‖((euclideanParabolicOperatorL hα₁.le a b c).prod
          (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).inverse‖ ≤ C := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_le_lineMap (ι := ι) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC₀, fun T hT hTT₀ a b c ha hak hbk hck ↦
    ContinuousLinearMap.opNorm_le_bound _ hC₀ fun d ↦ ?_⟩
  have h := hC T hT hTT₀ a b c ha hak hbk hck 1 (right_mem_Icc.2 zero_le_one)
    (((euclideanParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).inverse d)
  have hinv := (isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁
    hT b c hlam ha).self_apply_inverse d
  rw [AffineMap.lineMap_apply_one, hinv] at h
  convert h using 2

/-- **The solution operator depends continuously on the coefficients.** Under the hypotheses of
`isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL`, the solution operator
`(f, g) ↦ u` of `∂ₜu - a'ⁱʲ ∂ᵢ∂ⱼu - b'ⁱ ∂ᵢu - c' u = f`, `u(·, 0) = g` is continuous in operator
norm as a function of the coefficients `(a', b', c')` at `(a, b, c)`. -/
theorem continuousAt_inverse_euclideanParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α)
    (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ContinuousAt (fun abc : (ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) ×
        (ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) ×
        HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ↦
      ((euclideanParabolicOperatorL hα₁.le abc.1 abc.2.1 abc.2.2).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).inverse) (a, b, c) := by
  have hL : Continuous fun abc : (ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) ×
      (ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) ×
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ ↦
      (euclideanParabolicOperatorL hα₁.le abc.1 abc.2.1 abc.2.2).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
      ((continuous_euclideanParabolicOperatorL hα₁.le).prodMk continuous_const)
  exact ContinuousAt.comp (g := ContinuousLinearMap.inverse)
    ((isInvertible_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT b c hlam
      ha).contDiffAt_map_inverse (n := 0)).continuousAt hL.continuousAt

end Forward

/-! ### The terminal-value problem -/

section Backward

variable {T : ℝ≥0}

/-- Reading the coefficients backward in time commutes with assembling the Euclidean operator. -/
private theorem parabolicOperatorL_compLipschitzL_euclidean (hα : α ≤ 1) (hT : (0 : ℝ) < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : (0 : ℝ) = T - T) (hb : (T : ℝ) = T - 0) :
    parabolicOperatorL (ht := hT) hα
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (euclideanSecondOrderCoeff a))
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (euclideanFirstOrderCoeff b))
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (euclideanZerothOrderCoeff c)) =
      euclideanParabolicOperatorL hα
        (fun i j ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (a i j))
        (fun i ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (b i))
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith c) := by
  ext u p
  simp [parabolicOperatorL_apply, HolderSpace.compLipschitzL_apply]

/-- **The terminal-value problem with variable coefficients is well posed.** For `0 < α < 1`, a
horizon `T > 0` and coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}(ℝⁿ × [0, T])` with
`lam ‖ξ‖² ≤ ξᵀ a ξ` and `0 < lam`, for every forcing `f ∈ C_b^{α,α/2}` and terminal datum
`g ∈ C_b^{2,α}` there is exactly one `u ∈ C_b^{2+α,1+α/2}` with
`∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u = f` and `u(·, T) = g`. The proof reverses time and solves a
forward Cauchy problem. -/
theorem bijective_euclideanBackwardParabolicOperatorL_prod_spatialTraceL (hα₀ : 0 < α)
    (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ) {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    Function.Bijective ((euclideanBackwardParabolicOperatorL hα₁.le a b c).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨T, right_mem_Icc.2 hT.le⟩)) := by
  have h₀ : (0 : ℝ) = T - T := (sub_self _).symm
  have h₁ : (T : ℝ) = T - 0 := (sub_zero _).symm
  rw [euclideanBackwardParabolicOperatorL_def,
    bijective_backwardParabolicOperatorL_prod_spatialTraceL_iff (T := T) (ha := h₀) (hb := h₁),
    parabolicOperatorL_compLipschitzL_euclidean hα₁.le hT a b c h₀ h₁]
  exact bijective_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT _ _ hlam
    fun p ξ ↦ by simpa only [HolderSpace.compLipschitzL_apply] using ha _ ξ

end Backward

end TauCeti.ParabolicC2HolderSpace
