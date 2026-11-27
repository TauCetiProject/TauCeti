/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# An extra coordinate for equations with a mixed term in the flux

The equation `-div(A ∇u + b u) + ⟪b, ∇u⟫ + c u = f` can be lifted to a
principal divergence equation with potential `c + 1` by adding a real coordinate
`t` and multiplying the solution by `exp t`. The mixed terms occupy the two
off-diagonal blocks of the lifted principal matrix. They cancel in its quadratic
form. Its lower bound is independent of `b`, and its upper bound uses only the size of `b`.
-/

public noncomputable section

open Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace Real

namespace TauCeti.PDE.MixedDivergence

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "E'" => EuclideanSpace ℝ (ι ⊕ Unit)

/-- Projection to the original coordinates. -/
def horizontal : E' →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ Unit)).comp
    (EuclideanSpace.sumEquivProd : E' ≃L[ℝ] E × EuclideanSpace ℝ Unit).toContinuousLinearMap

/-- Projection to the extra real coordinate. -/
def vertical : E' →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι ⊕ Unit ↦ ℝ) (Sum.inr ())

@[simp]
theorem horizontal_apply (x : E') (i : ι) : horizontal x i = x (Sum.inl i) :=
  EuclideanSpace.sumEquivProd_apply_fst x i

omit [Fintype ι] in
theorem vertical_apply (x : E') : vertical x = x (Sum.inr ()) := by
  simp [vertical]

@[simp]
theorem horizontal_basis_inl (i : ι) :
    horizontal (EuclideanSpace.basisFun (ι ⊕ Unit) ℝ (Sum.inl i)) =
      EuclideanSpace.basisFun ι ℝ i := by
  classical
  ext j
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single_apply]

@[simp]
theorem horizontal_basis_inr :
    horizontal (EuclideanSpace.basisFun (ι ⊕ Unit) ℝ (Sum.inr ())) = 0 := by
  classical
  ext j
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single]

@[simp]
theorem vertical_basis_inl (i : ι) :
    vertical (EuclideanSpace.basisFun (ι ⊕ Unit) ℝ (Sum.inl i)) = 0 := by
  classical
  simp [vertical_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.single]

@[simp]
theorem vertical_basis_inr :
    vertical (EuclideanSpace.basisFun (ι ⊕ Unit) ℝ (Sum.inr ())) = 1 := by
  classical
  simp [vertical_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.single]

/-- The point with prescribed horizontal and vertical coordinates. -/
def liftPoint (x : E) (t : ℝ) : E' := WithLp.toLp 2 (Sum.elim x fun _ ↦ t)

omit [Fintype ι] in
@[simp]
theorem liftPoint_apply_inl (x : E) (t : ℝ) (i : ι) : liftPoint x t (Sum.inl i) = x i := (rfl)

omit [Fintype ι] in
@[simp]
theorem liftPoint_apply_inr (x : E) (t : ℝ) : liftPoint x t (Sum.inr ()) = t := (rfl)

@[simp]
theorem liftPoint_horizontal_vertical (z : E') : liftPoint (horizontal z) (vertical z) = z := by
  apply PiLp.ext
  intro i
  rcases i with i | t
  · simp
  · cases t
    simp [vertical_apply]

@[simp]
theorem horizontal_liftPoint (x : E) (t : ℝ) : horizontal (liftPoint x t) = x := by
  ext i
  simp [liftPoint]

omit [Fintype ι] in
@[simp]
theorem vertical_liftPoint (x : E) (t : ℝ) : vertical (liftPoint x t) = t := by
  simp [vertical_apply, liftPoint]

omit [Fintype ι] in
theorem continuous_liftPoint : Continuous (fun z : E × ℝ ↦ liftPoint z.1 z.2) := by
  refine (PiLp.continuous_toLp 2 (fun _ : ι ⊕ Unit ↦ ℝ)).comp (continuous_pi fun i ↦ ?_)
  rcases i with i | _
  · exact (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i).comp continuous_fst
  · exact continuous_snd

theorem norm_sq_eq (x : E') : ‖x‖ ^ 2 = ‖horizontal x‖ ^ 2 + (vertical x) ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Real.norm_eq_abs, vertical_apply]

theorem norm_horizontal_le (x : E') : ‖horizontal x‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_liftPoint_zero (x : E) : ‖liftPoint x 0‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq]
  simp

theorem abs_vertical_le (x : E') : |vertical x| ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, norm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem dist_horizontal_le (x y : E') : dist (horizontal x) (horizontal y) ≤ dist x y := by
  simpa only [dist_eq_norm, map_sub] using norm_horizontal_le (x - y)

@[simp]
theorem dist_liftPoint_same (x y : E) (t : ℝ) :
    dist (liftPoint x t) (liftPoint y t) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq]
  simp

theorem inner_liftPoint_right (v : E') (x : E) (t : ℝ) :
    ⟪v, liftPoint x t⟫_ℝ = ⟪horizontal v, x⟫_ℝ + vertical v * t := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, liftPoint, vertical_apply, mul_comm]

/-- The principal matrix `[[a, b], [-bᵀ, 1]]` of the lifted equation, with `b` as the
top-right column and its negative transpose as the bottom-left row. -/
def skewBlock (a : Matrix ι ι ℝ) (b : E) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks a (fun i _ ↦ b i) (fun _ j ↦ -b j) (fun _ _ ↦ 1)

omit [Fintype ι] in
@[simp]
theorem skewBlock_apply_inl_inl (a : Matrix ι ι ℝ) (b : E) (i j : ι) :
    skewBlock a b (Sum.inl i) (Sum.inl j) = a i j := (rfl)

omit [Fintype ι] in
@[simp]
theorem skewBlock_apply_inl_inr (a : Matrix ι ι ℝ) (b : E) (i : ι) (t : Unit) :
    skewBlock a b (Sum.inl i) (Sum.inr t) = b i := (rfl)

omit [Fintype ι] in
@[simp]
theorem skewBlock_apply_inr_inl (a : Matrix ι ι ℝ) (b : E) (t : Unit) (j : ι) :
    skewBlock a b (Sum.inr t) (Sum.inl j) = -b j := (rfl)

omit [Fintype ι] in
@[simp]
theorem skewBlock_apply_inr_inr (a : Matrix ι ι ℝ) (b : E) (t s : Unit) :
    skewBlock a b (Sum.inr t) (Sum.inr s) = 1 := (rfl)

/-- The lifted bilinear form is the horizontal `a` form plus
`⟪x_h, b⟫ y_t - x_t ⟪b, y_h⟫ + x_t y_t`. -/
theorem matrixBilinearForm_skewBlock (a : Matrix ι ι ℝ) (b : E) (x y : E') :
    matrixBilinearForm (skewBlock a b) x y =
      matrixBilinearForm a (horizontal x) (horizontal y) +
        ⟪horizontal x, b⟫_ℝ * vertical y - vertical x * ⟪b, horizontal y⟫_ℝ +
        vertical x * vertical y := by
  simp [matrixBilinearForm_apply, skewBlock, Matrix.fromBlocks, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    PiLp.inner_apply, vertical_apply, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
  ring

/-- The two off-diagonal terms cancel in the quadratic form of the lifted matrix. -/
theorem matrixBilinearForm_skewBlock_self (a : Matrix ι ι ℝ) (b : E) (v : E') :
    matrixBilinearForm (skewBlock a b) v v =
      matrixBilinearForm a (horizontal v) (horizontal v) + (vertical v) ^ 2 := by
  rw [matrixBilinearForm_skewBlock, real_inner_comm (horizontal v) b]
  ring

private theorem abs_inner_mul_vertical_le (b : E) (v w : E') :
    |⟪horizontal v, b⟫_ℝ * vertical w| ≤ ‖b‖ * ‖v‖ * ‖w‖ := by
  rw [abs_mul]
  calc
    _ ≤ ‖horizontal v‖ * ‖b‖ * |vertical w| :=
      mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ ≤ ‖v‖ * ‖b‖ * ‖w‖ := by
      gcongr
      exacts [norm_horizontal_le v, abs_vertical_le w]
    _ = _ := by rw [mul_comm ‖v‖]

private theorem abs_matrixBilinearForm_skewBlock_le {a : Matrix ι ι ℝ} {Lam : ℝ}
    (hLam : 0 ≤ Lam) (ha : ∀ v w : E, |matrixBilinearForm a v w| ≤ Lam * ‖v‖ * ‖w‖)
    (b : E) (v w : E') :
    |matrixBilinearForm (skewBlock a b) v w| ≤ (Lam + 2 * ‖b‖ + 1) * ‖v‖ * ‖w‖ := by
  rw [matrixBilinearForm_skewBlock]
  have h₁ : |matrixBilinearForm a (horizontal v) (horizontal w)| ≤ Lam * ‖v‖ * ‖w‖ := by
    refine (ha _ _).trans ?_
    gcongr
    exacts [norm_horizontal_le v, norm_horizontal_le w]
  have h₂ := abs_inner_mul_vertical_le b v w
  have h₃ : |vertical v * ⟪b, horizontal w⟫_ℝ| ≤ ‖b‖ * ‖v‖ * ‖w‖ := by
    rw [mul_comm (vertical v), real_inner_comm (horizontal w) b]
    simpa only [mul_assoc, mul_comm ‖w‖ ‖v‖] using abs_inner_mul_vertical_le b w v
  have h₄ : |vertical v * vertical w| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (abs_vertical_le _) (abs_vertical_le _) (abs_nonneg _) (norm_nonneg _)
  calc
    _ ≤ |matrixBilinearForm a (horizontal v) (horizontal w) +
          ⟪horizontal v, b⟫_ℝ * vertical w - vertical v * ⟪b, horizontal w⟫_ℝ| +
        |vertical v * vertical w| := abs_add_le _ _
    _ ≤ |matrixBilinearForm a (horizontal v) (horizontal w)| + |⟪horizontal v, b⟫_ℝ * vertical w| +
        |vertical v * ⟪b, horizontal w⟫_ℝ| + |vertical v * vertical w| := by
      gcongr
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith only [h₁, h₂, h₃, h₄]

/-- The skew block construction preserves uniform ellipticity, with a bound for the mixed
coefficient appearing only in the upper constant. The coefficient family may be indexed
by any set, including an empty one. -/
theorem uniformlyEllipticOn_skewBlock [DecidableEq ι] {X : Type*} {s : Set X}
    {a : X → Matrix ι ι ℝ} {b : X → E} {lam Lam M : ℝ}
    (ha : UniformlyEllipticOn s a lam Lam) (hb : ∀ x ∈ s, ‖b x‖ ≤ M) :
    UniformlyEllipticOn s (fun x ↦ skewBlock (a x) (b x))
      (min lam 1) (Lam + 2 * max M 0 + 1) := by
  refine UniformlyEllipticOn.of_bounds (lt_min ha.pos zero_lt_one) ?_ ?_ ?_
  · linarith [min_le_left lam (1 : ℝ), ha.le, le_max_right M (0 : ℝ)]
  · intro x hx v
    rw [← matrixBilinearForm_self, matrixBilinearForm_skewBlock_self, norm_sq_eq, mul_add,
      matrixBilinearForm_self]
    exact add_le_add
      ((mul_le_mul_of_nonneg_right (min_le_left lam 1) (sq_nonneg _)).trans (ha.lower_bound hx _))
      (by simpa using mul_le_mul_of_nonneg_right (min_le_right lam 1) (sq_nonneg (vertical v)))
  · intro x hx v w
    rw [← matrixBilinearForm_apply]
    refine (abs_matrixBilinearForm_skewBlock_le ha.upper_nonneg
      (fun η ξ ↦ by simpa only [matrixBilinearForm_apply] using ha.upper_bound hx η ξ)
      (b x) v w).trans ?_
    gcongr
    exact (hb x hx).trans (le_max_left M 0)

/-- The exponential extension `(x, t) ↦ exp t * u x`, whose trace at `t = 0` is `u`. -/
def lift (u : E → ℝ) (x : E') : ℝ := rexp (vertical x) * u (horizontal x)

theorem lift_apply (u : E → ℝ) (x : E') :
    lift u x = rexp (vertical x) * u (horizontal x) := (rfl)

@[simp]
theorem lift_liftPoint_zero (u : E → ℝ) (x : E) : lift u (liftPoint x 0) = u x := by
  simp [lift_apply]

theorem contDiffOn_lift {k : WithTop ℕ∞} {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ k u s) : ContDiffOn ℝ k (lift u) (horizontal ⁻¹' s) :=
  (Real.contDiff_exp.comp vertical.contDiff).contDiffOn.mul
    (hu.comp horizontal.contDiff.contDiffOn (mapsTo_preimage horizontal s))

theorem continuousOn_lift {u : E → ℝ} {s : Set E} (hu : ContinuousOn u s) :
    ContinuousOn (lift u) (horizontal ⁻¹' s) :=
  (Real.continuous_exp.comp vertical.continuous).continuousOn.mul
    (hu.comp horizontal.continuous.continuousOn (mapsTo_preimage horizontal s))

/-- The full open cylinder over a base domain. -/
def liftDomain (U : Opens E) : Opens E' :=
  Opens.comap ⟨horizontal, horizontal.continuous⟩ U

@[simp]
theorem mem_liftDomain_iff (U : Opens E) (x : E') :
    x ∈ liftDomain U ↔ horizontal x ∈ U := (Iff.rfl)

theorem coe_liftDomain (U : Opens E) : (liftDomain U : Set E') = horizontal ⁻¹' U := (rfl)

end TauCeti.PDE.MixedDivergence
