/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.ExteriorSquare
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bound
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Pinching

/-!
# Hilbert–Schmidt norm of the curvature tensor and curvature-operator lower bounds

The pointwise Hilbert–Schmidt norm `|Rm|` of the curvature tensor of a smooth connection on a
Riemannian vector bundle (and in particular of the Levi-Civita connection of a Riemannian manifold)
is defined by summing the squared orthonormal components
`⟪R(b_i, b_j) c_k, c_l⟫^2` over any orthonormal bases `(b_i)` of `T_x M` and `(c_k)` of the
fibre `V_x`. By Parseval's identity in each linear slot, this sum is independent of the choice of
orthonormal bases.

We also develop its basic estimates and transformation laws for the Levi-Civita connection:

* **Basis independence & Parseval formulas**:
  `CovariantDerivative.curvatureTensorNormSq_eq_sum_orthonormalBasis` and
  `CovariantDerivative.curvatureTensorNormSq_eq_sum_norm_sq`.
* **Tensor and curvature-operator estimates**:
  `CovariantDerivative.norm_curvatureTensor_apply_le_curvatureTensorNorm_mul`,
  `CovariantDerivative.norm_curvatureEndomorphism_apply_le`, and
  `CovariantDerivative.neg_curvatureTensorNorm_mul_norm_sq_le_inner_curvatureEndomorphism`.
* **Compactness bound**:
  `CovariantDerivative.exists_curvatureTensorNorm_le_of_isCompact`.
* **Spectral equivalence for `curvatureEndomorphism`**:
  `CovariantDerivative.forall_le_inner_curvatureEndomorphism_iff_forall_hasEigenvalue`.
* **Isometry and scaling laws**:
  `TauCeti.IsLocalRiemannianIsometry.curvatureTensorNorm_map`,
  `Bundle.ContMDiffRiemannianMetric.curvatureTensorNorm_rescale_const`, and
  `Bundle.ContMDiffRiemannianMetric.forall_le_inner_curvatureEndomorphism_rescale_const_iff`.
* **Constant sectional curvature formula**:
  `CovariantDerivative.curvatureTensorNormSq_eq_of_eq_smul_inner_sub`.
-/

public section

open Bundle Manifold
open scoped Bundle ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

section ParsevalHelpers

/-- For a linear functional `f` on a finite-dimensional real inner product space, the sum of
`(f (b i)) ^ 2` over an orthonormal basis `b` is independent of `b`. -/
private theorem sum_sq_orthonormalBasis_eq {U ι ι' : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [Fintype ι] [Fintype ι']
    (b : OrthonormalBasis ι ℝ U) (b' : OrthonormalBasis ι' ℝ U) (f : U →ₗ[ℝ] ℝ) :
    ∑ i, (f (b i)) ^ 2 = ∑ j, (f (b' j)) ^ 2 := by
  let fC : U →L[ℝ] ℝ := f.toContinuousLinearMap
  let v : U := (InnerProductSpace.toDual ℝ U).symm fC
  have hv (u : U) : f u = ⟪v, u⟫ := by
    change fC u = ⟪(InnerProductSpace.toDual ℝ U).symm fC, u⟫
    rw [InnerProductSpace.toDual_symm_apply]
  have hsum : ∑ i, ⟪v, b i⟫ ^ 2 = ‖v‖ ^ 2 := by
    have h := b.sum_inner_mul_inner v v
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [sq, real_inner_comm v] using h
  have hsum' : ∑ j, ⟪v, b' j⟫ ^ 2 = ‖v‖ ^ 2 := by
    have h := b'.sum_inner_mul_inner v v
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [sq, real_inner_comm v] using h
  simp_rw [hv, hsum, hsum']

end ParsevalHelpers

section Definition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [RiemannianBundle V]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The squared Hilbert–Schmidt norm `|Rm|²` of the curvature tensor of `cov` at `x`. -/
def curvatureTensorNormSq (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (V x) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.symm.finiteDimensional
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let c := stdOrthonormalBasis ℝ (V x)
  ∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2

/-- The pointwise Hilbert–Schmidt norm `|Rm|` of the curvature tensor of `cov` at `x`. -/
def curvatureTensorNorm (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M) : ℝ :=
  Real.sqrt (cov.curvatureTensorNormSq x)

/-- The squared curvature tensor norm is nonnegative. -/
theorem curvatureTensorNormSq_nonneg (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M) :
    0 ≤ cov.curvatureTensorNormSq x := by
  unfold curvatureTensorNormSq
  positivity

/-- The curvature tensor norm is nonnegative. -/
theorem curvatureTensorNorm_nonneg (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M) :
    0 ≤ cov.curvatureTensorNorm x :=
  Real.sqrt_nonneg _

/-- Squaring the curvature tensor norm recovers `curvatureTensorNormSq`. -/
@[simp]
theorem curvatureTensorNorm_sq (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M) :
    cov.curvatureTensorNorm x ^ 2 = cov.curvatureTensorNormSq x :=
  Real.sq_sqrt (cov.curvatureTensorNormSq_nonneg x)

/-- **Basis independence of `curvatureTensorNormSq`**: for any orthonormal bases `b` of
`T_x M` and `c` of `V_x`, `|Rm|² = ∑ i j k l, ⟪R(b i, b j)(c k), c l⟫²`. -/
theorem curvatureTensorNormSq_eq_sum_orthonormalBasis (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (c : OrthonormalBasis κ ℝ (V x)) :
    cov.curvatureTensorNormSq x =
      ∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 := by
  let _ : FiniteDimensional ℝ (V x) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.symm.finiteDimensional
  let b₀ := stdOrthonormalBasis ℝ (TangentSpace I x)
  let c₀ := stdOrthonormalBasis ℝ (V x)
  change (∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b₀ i) (b₀ j) (c₀ k), c₀ l⟫ ^ 2) =
    ∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2
  -- First swap `c₀` to `c` in the `l` slot, using Parseval (`‖v‖² = ∑ l, ⟪v, c l⟫²`).
  have hnorm_c (v : V x) : ∑ l, ⟪v, c₀ l⟫ ^ 2 = ∑ l, ⟪v, c l⟫ ^ 2 := by
    have h₁ : ∑ l, ⟪v, c₀ l⟫ ^ 2 = ‖v‖ ^ 2 := by
      have h := c₀.sum_inner_mul_inner v v
      rw [real_inner_self_eq_norm_sq] at h
      simpa only [sq, real_inner_comm _ v] using h
    have h₂ : ∑ l, ⟪v, c l⟫ ^ 2 = ‖v‖ ^ 2 := by
      have h := c.sum_inner_mul_inner v v
      rw [real_inner_self_eq_norm_sq] at h
      simpa only [sq, real_inner_comm _ v] using h
    exact h₁.trans h₂.symm
  simp_rw [hnorm_c]
  -- Swap `c₀` to `c` in the `k` slot.
  have hswap_k (i j) :
      ∑ k, ∑ l, ⟪cov.curvatureTensor x (b₀ i) (b₀ j) (c₀ k), c l⟫ ^ 2 =
        ∑ k, ∑ l, ⟪cov.curvatureTensor x (b₀ i) (b₀ j) (c k), c l⟫ ^ 2 := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    let L : V x →ₗ[ℝ] ℝ :=
      { toFun := fun w ↦ ⟪cov.curvatureTensor x (b₀ i) (b₀ j) w, c l⟫
        map_add' := fun w₁ w₂ ↦ by simp [inner_add_left]
        map_smul' := fun r w ↦ by simp [real_inner_smul_left] }
    exact sum_sq_orthonormalBasis_eq c₀ c L
  simp_rw [hswap_k]
  -- Swap `b₀` to `b` in the `j` slot.
  have hswap_j (i) :
      ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b₀ i) (b₀ j) (c k), c l⟫ ^ 2 =
        ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b₀ i) (b j) (c k), c l⟫ ^ 2 := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    let L : TangentSpace I x →ₗ[ℝ] ℝ :=
      { toFun := fun v ↦ ⟪cov.curvatureTensor x (b₀ i) v (c k), c l⟫
        map_add' := fun v₁ v₂ ↦ by simp [inner_add_left]
        map_smul' := fun r v ↦ by simp [real_inner_smul_left] }
    exact sum_sq_orthonormalBasis_eq b₀ b L
  simp_rw [hswap_j]
  -- Swap `b₀` to `b` in the `i` slot.
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  let L : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u ↦ ⟪cov.curvatureTensor x u (b j) (c k), c l⟫
      map_add' := fun u₁ u₂ ↦ by simp [inner_add_left]
      map_smul' := fun r u ↦ by simp [real_inner_smul_left] }
  exact sum_sq_orthonormalBasis_eq b₀ b L

/-- `|Rm|² = ∑ i j k, ‖R(b i, b j)(c k)‖²` for any orthonormal bases `b` and `c`. -/
theorem curvatureTensorNormSq_eq_sum_norm_sq (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (x : M)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (c : OrthonormalBasis κ ℝ (V x)) :
    cov.curvatureTensorNormSq x =
      ∑ i, ∑ j, ∑ k, ‖cov.curvatureTensor x (b i) (b j) (c k)‖ ^ 2 := by
  rw [cov.curvatureTensorNormSq_eq_sum_orthonormalBasis x b c]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  have h := c.sum_inner_mul_inner (cov.curvatureTensor x (b i) (b j) (c k))
    (cov.curvatureTensor x (b i) (b j) (c k))
  rw [real_inner_self_eq_norm_sq] at h
  symm
  calc
    ‖cov.curvatureTensor x (b i) (b j) (c k)‖ ^ 2
        = ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ *
            ⟪c l, cov.curvatureTensor x (b i) (b j) (c k)⟫ := h.symm
    _ = ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 := by
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [real_inner_comm (c l), sq]

/-- **Multilinear norm bound from `|Rm|`**: `‖R(u, v) w‖ ≤ |Rm| ‖u‖ ‖v‖ ‖w‖`. -/
theorem norm_curvatureTensor_apply_le_curvatureTensorNorm_mul
    (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞] (x : M)
    (u v : TangentSpace I x) (w : V x) :
    ‖cov.curvatureTensor x u v w‖ ≤
      cov.curvatureTensorNorm x * ‖u‖ * ‖v‖ * ‖w‖ := by
  let _ : FiniteDimensional ℝ (V x) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.symm.finiteDimensional
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let c := stdOrthonormalBasis ℝ (V x)
  refine (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (cov.curvatureTensorNorm_nonneg x)
      (norm_nonneg u)) (norm_nonneg v)) (norm_nonneg w))).mp ?_
  have hu : u = ∑ i, ⟪b i, u⟫ • b i := (b.sum_repr' u).symm
  have hv : v = ∑ j, ⟪b j, v⟫ • b j := (b.sum_repr' v).symm
  have hw : w = ∑ k, ⟪c k, w⟫ • c k := (c.sum_repr' w).symm
  have hu_sq : ∑ i, ⟪b i, u⟫ ^ 2 = ‖u‖ ^ 2 := by
    have h := b.sum_inner_mul_inner u u
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [sq, real_inner_comm u] using h
  have hv_sq : ∑ j, ⟪b j, v⟫ ^ 2 = ‖v‖ ^ 2 := by
    have h := b.sum_inner_mul_inner v v
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [sq, real_inner_comm v] using h
  have hw_sq : ∑ k, ⟪c k, w⟫ ^ 2 = ‖w‖ ^ 2 := by
    have h := c.sum_inner_mul_inner w w
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [sq, real_inner_comm w] using h
  have hnorm_sq : ‖cov.curvatureTensor x u v w‖ ^ 2 =
      ∑ l, ⟪cov.curvatureTensor x u v w, c l⟫ ^ 2 := by
    have h := c.sum_inner_mul_inner (cov.curvatureTensor x u v w) (cov.curvatureTensor x u v w)
    rw [real_inner_self_eq_norm_sq] at h
    calc
      ‖cov.curvatureTensor x u v w‖ ^ 2
          = ∑ l, ⟪cov.curvatureTensor x u v w, c l⟫ * ⟪c l, cov.curvatureTensor x u v w⟫ := h.symm
      _ = ∑ l, ⟪cov.curvatureTensor x u v w, c l⟫ ^ 2 := by
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          rw [real_inner_comm (c l), sq]
  have hcomp (l) : ⟪cov.curvatureTensor x u v w, c l⟫ ^ 2 ≤
      (‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2) *
        ∑ i, ∑ j, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 := by
    have hexpand : ⟪cov.curvatureTensor x u v w, c l⟫ =
        ∑ p : _ × _ × _, (⟪b p.1, u⟫ * ⟪b p.2.1, v⟫ * ⟪c p.2.2, w⟫) *
          ⟪cov.curvatureTensor x (b p.1) (b p.2.1) (c p.2.2), c l⟫ := by
      have hlin : ⟪cov.curvatureTensor x u v w, c l⟫ =
          ∑ i, ∑ j, ∑ k, (⟪b i, u⟫ * ⟪b j, v⟫ * ⟪c k, w⟫) *
            ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ := by
        calc
          ⟪cov.curvatureTensor x u v w, c l⟫
              = ∑ i, ⟪b i, u⟫ * ⟪cov.curvatureTensor x (b i) v w, c l⟫ := by
                  conv_lhs => rw [hu]
                  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
                    sum_inner, real_inner_smul_left]
          _ = ∑ i, ∑ j, ⟪b i, u⟫ * (⟪b j, v⟫ * ⟪cov.curvatureTensor x (b i) (b j) w, c l⟫) := by
                  refine Finset.sum_congr rfl fun i _ ↦ ?_
                  conv_lhs =>
                    rw [hv]
                    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
                      sum_inner, real_inner_smul_left]
                  rw [Finset.mul_sum]
          _ = ∑ i, ∑ j, ∑ k, (⟪b i, u⟫ * ⟪b j, v⟫ * ⟪c k, w⟫) *
                ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ := by
                  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
                  conv_lhs =>
                    rw [hw]
                    simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
                  rw [Finset.mul_sum, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _ ↦ by ring
      rw [hlin, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (Fintype.sum_prod_type (fun q : Fin (Module.finrank ℝ (TangentSpace I x)) ×
          Fin (Module.finrank ℝ (V x)) ↦
        (⟪b i, u⟫ * ⟪b q.1, v⟫ * ⟪c q.2, w⟫) *
          ⟪cov.curvatureTensor x (b i) (b q.1) (c q.2), c l⟫)).symm
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (_ × _ × _))
      (fun p ↦ ⟪b p.1, u⟫ * ⟪b p.2.1, v⟫ * ⟪c p.2.2, w⟫)
      (fun p ↦ ⟪cov.curvatureTensor x (b p.1) (b p.2.1) (c p.2.2), c l⟫)
    rw [← hexpand] at hcs
    have hleft : (∑ p : _ × _ × _, (⟪b p.1, u⟫ * ⟪b p.2.1, v⟫ * ⟪c p.2.2, w⟫) ^ 2) =
        ‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      have hinner_prod (a) :
          (∑ q : _ × _, (⟪b a, u⟫ * ⟪b q.1, v⟫ * ⟪c q.2, w⟫) ^ 2) =
            ⟪b a, u⟫ ^ 2 * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
        rw [Fintype.sum_prod_type]
        calc
          ∑ j, ∑ k, (⟪b a, u⟫ * ⟪b j, v⟫ * ⟪c k, w⟫) ^ 2
              = ∑ j, ∑ k, (⟪b a, u⟫ ^ 2 * ⟪b j, v⟫ ^ 2) * ⟪c k, w⟫ ^ 2 := by
                  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
                  ring
          _ = ∑ j, (⟪b a, u⟫ ^ 2 * ⟪b j, v⟫ ^ 2) * ∑ k, ⟪c k, w⟫ ^ 2 := by
                  refine Finset.sum_congr rfl fun j _ ↦ (Finset.mul_sum _ _ _).symm
          _ = ⟪b a, u⟫ ^ 2 * (∑ j, ⟪b j, v⟫ ^ 2) * ‖w‖ ^ 2 := by
                  rw [hw_sq, ← Finset.sum_mul, ← Finset.mul_sum]
          _ = ⟪b a, u⟫ ^ 2 * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
                  rw [hv_sq, mul_assoc]
      simp_rw [hinner_prod, ← Finset.sum_mul, hu_sq, mul_assoc]
    have hright : (∑ p : _ × _ × _,
          ⟪cov.curvatureTensor x (b p.1) (b p.2.1) (c p.2.2), c l⟫ ^ 2) =
        ∑ i, ∑ j, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ ↦ Fintype.sum_prod_type _
    rwa [hleft, hright] at hcs
  calc
    ‖cov.curvatureTensor x u v w‖ ^ 2
        = ∑ l, ⟪cov.curvatureTensor x u v w, c l⟫ ^ 2 := hnorm_sq
    _ ≤ ∑ l, (‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2) *
          ∑ i, ∑ j, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 :=
        Finset.sum_le_sum fun l _ ↦ hcomp l
    _ = (‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2) * cov.curvatureTensorNormSq x := by
        rw [← Finset.mul_sum, cov.curvatureTensorNormSq_eq_sum_orthonormalBasis x b c]
        congr 1
        calc
          ∑ l, ∑ i, ∑ j, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2
              = ∑ i, ∑ l, ∑ j, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 :=
                  Finset.sum_comm
          _ = ∑ i, ∑ j, ∑ l, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 :=
                  Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
          _ = ∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (c k), c l⟫ ^ 2 :=
                  Finset.sum_congr rfl fun i _ ↦
                    Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
    _ = (cov.curvatureTensorNorm x * ‖u‖ * ‖v‖ * ‖w‖) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, cov.curvatureTensorNorm_sq]
        ring

end Definition

section CompactBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [RiemannianBundle V] [IsContinuousRiemannianBundle F V]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- On a compact subset `K` of a smooth manifold with continuous fibre metrics, the Hilbert–Schmidt
curvature tensor norm `|Rm|` of a smooth connection is uniformly bounded. -/
theorem exists_curvatureTensorNorm_le_of_isCompact (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] {K : Set M} (hK : IsCompact K) :
    ∃ C ≥ 0, ∀ x ∈ K, cov.curvatureTensorNorm x ≤ C := by
  obtain ⟨C₀, hC₀⟩ := cov.exists_norm_curvatureTensor_le_of_isCompact (F := F) (V := V) hK
  let C := (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ F : ℝ) * |C₀|
  refine ⟨C, by positivity, fun x hx ↦ ?_⟩
  let _ : FiniteDimensional ℝ (V x) :=
    ((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.symm.finiteDimensional
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let c := stdOrthonormalBasis ℝ (V x)
  have hb_norm (i) : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have hc_norm (k) : ‖c k‖ = 1 := c.orthonormal.norm_eq_one k
  have hsq : cov.curvatureTensorNormSq x ≤ C ^ 2 := by
    rw [cov.curvatureTensorNormSq_eq_sum_norm_sq x b c]
    have hterm (i j k) : ‖cov.curvatureTensor x (b i) (b j) (c k)‖ ^ 2 ≤ |C₀| ^ 2 := by
      have hle := hC₀ x hx (b i) (b j) (c k)
      rw [hb_norm, hb_norm, hc_norm, mul_one, mul_one, mul_one] at hle
      exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg C₀)).2 (hle.trans (le_abs_self C₀))
    have hfinE : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    have hfinV : Module.finrank ℝ (V x) = Module.finrank ℝ F :=
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq
    have hF_le : (Module.finrank ℝ F : ℝ) ≤ (Module.finrank ℝ F : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero (Module.finrank ℝ F)
    calc
      ∑ i, ∑ j, ∑ k, ‖cov.curvatureTensor x (b i) (b j) (c k)‖ ^ 2
          ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
              ∑ _j : Fin (Module.finrank ℝ (TangentSpace I x)),
                ∑ _k : Fin (Module.finrank ℝ (V x)), |C₀| ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
            Finset.sum_le_sum fun k _ ↦ hterm i j k
      _ = (Module.finrank ℝ E : ℝ) ^ 2 * (Module.finrank ℝ F : ℝ) * |C₀| ^ 2 := by
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, hfinE, hfinV]
          ring
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Module.finrank ℝ F : ℝ) ^ 2 * |C₀| ^ 2 := by
          gcongr
      _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ F : ℝ) * |C₀|) ^ 2 := by ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

end CompactBound

section ExteriorSquareAndSpectrum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
  [ContMDiffCovariantDerivative cov ∞]

/-- **Curvature operator norm bound**: `‖Rop z‖ ≤ (1 / 2) * |Rm| * ‖z‖`. -/
theorem norm_curvatureEndomorphism_apply_le (x : M)
    (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    ‖cov.curvatureEndomorphism hcov x z‖ ≤
      (1 / 2 : ℝ) * cov.curvatureTensorNorm x * ‖z‖ := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hnorm_sq (w : ⋀[ℝ]^2 (TangentSpace I x)) :
      ∑ i, ∑ j, ⟪exteriorPower.ιMulti ℝ 2 ![b i, b j], w⟫ ^ 2 = 2 * ‖w‖ ^ 2 := by
    have h := congrArg (fun S : Module.End ℝ (⋀[ℝ]^2 (TangentSpace I x)) ↦ ⟪S w, w⟫)
      (OrthonormalBasis.sum_rankOne_ιMulti_two b)
    simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, sum_inner, inner_smul_left, RCLike.conj_to_real,
      LinearMap.smul_apply, LinearMap.id_apply, real_inner_self_eq_norm_sq] at h
    simpa only [sq] using h
  have h2z : (2 : ℝ) • z = ∑ i, ∑ j,
      ⟪exteriorPower.ιMulti ℝ 2 ![b i, b j], z⟫ • exteriorPower.ιMulti ℝ 2 ![b i, b j] := by
    have h := congrArg (fun S : Module.End ℝ (⋀[ℝ]^2 (TangentSpace I x)) ↦ S z)
      (OrthonormalBasis.sum_rankOne_ιMulti_two b)
    simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using h.symm
  have hpair (k l) :
      4 * ⟪exteriorPower.ιMulti ℝ 2 ![b k, b l], cov.curvatureEndomorphism hcov x z⟫ ^ 2 ≤
        (2 * ‖z‖ ^ 2) *
          ∑ i, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 := by
    have hcoeff : 2 * ⟪exteriorPower.ιMulti ℝ 2 ![b k, b l], cov.curvatureEndomorphism hcov x z⟫ =
        ∑ p : Fin (Module.finrank ℝ (TangentSpace I x)) ×
            Fin (Module.finrank ℝ (TangentSpace I x)),
          ⟪exteriorPower.ιMulti ℝ 2 ![b p.1, b p.2], z⟫ *
            ⟪cov.curvatureTensor x (b p.1) (b p.2) (b l), b k⟫ := by
      have h1 : 2 * ⟪exteriorPower.ιMulti ℝ 2 ![b k, b l], cov.curvatureEndomorphism hcov x z⟫ =
          ⟪cov.curvatureEndomorphism hcov x ((2 : ℝ) • z),
            exteriorPower.ιMulti ℝ 2 ![b k, b l]⟫ := by
        rw [map_smul, two_smul ℝ, inner_add_left, real_inner_comm]
        ring
      rw [h1, h2z, map_sum, sum_inner]
      have hsum_ij : ∀ i,
          (∑ j, ⟪cov.curvatureEndomorphism hcov x
              (⟪exteriorPower.ιMulti ℝ 2 ![b i, b j], z⟫ • exteriorPower.ιMulti ℝ 2 ![b i, b j]),
            exteriorPower.ιMulti ℝ 2 ![b k, b l]⟫) =
            ∑ j, ⟪exteriorPower.ιMulti ℝ 2 ![b i, b j], z⟫ *
              ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ := fun i ↦ by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_smul]
        change (innerₗ (⋀[ℝ]^2 (TangentSpace I x)))
          (⟪exteriorPower.ιMulti ℝ 2 ![b i, b j], z⟫ •
            cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 ![b i, b j]))
          (exteriorPower.ιMulti ℝ 2 ![b k, b l]) = _
        rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact congrArg (⟪exteriorPower.ιMulti ℝ 2 ![b i, b j], z⟫ * ·)
          (cov.inner_curvatureEndomorphism_ιMulti hcov x ![b i, b j] ![b k, b l])
      simp_rw [map_sum, sum_inner, hsum_ij]
      symm
      exact Fintype.sum_prod_type (fun p : Fin (Module.finrank ℝ (TangentSpace I x)) ×
          Fin (Module.finrank ℝ (TangentSpace I x)) ↦
        ⟪exteriorPower.ιMulti ℝ 2 ![b p.1, b p.2], z⟫ *
          ⟪cov.curvatureTensor x (b p.1) (b p.2) (b l), b k⟫)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : Fin (Module.finrank ℝ (TangentSpace I x)) × _ ↦
        ⟪exteriorPower.ιMulti ℝ 2 ![b p.1, b p.2], z⟫)
      (fun p ↦ ⟪cov.curvatureTensor x (b p.1) (b p.2) (b l), b k⟫)
    rw [← hcoeff] at hcs
    have hz_sum : (∑ p : Fin (Module.finrank ℝ (TangentSpace I x)) × _,
        ⟪exteriorPower.ιMulti ℝ 2 ![b p.1, b p.2], z⟫ ^ 2) = 2 * ‖z‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      exact hnorm_sq z
    have hR_sum : (∑ p : Fin (Module.finrank ℝ (TangentSpace I x)) × _,
        ⟪cov.curvatureTensor x (b p.1) (b p.2) (b l), b k⟫ ^ 2) =
        ∑ i, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
      Fintype.sum_prod_type _
    calc
      4 * ⟪exteriorPower.ιMulti ℝ 2 ![b k, b l], cov.curvatureEndomorphism hcov x z⟫ ^ 2
          = (2 * ⟪exteriorPower.ιMulti ℝ 2 ![b k, b l],
              cov.curvatureEndomorphism hcov x z⟫) ^ 2 := by ring
      _ ≤ (2 * ‖z‖ ^ 2) *
            ∑ i, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 := by
          rwa [hz_sum, hR_sum] at hcs
  have hsum : 8 * ‖cov.curvatureEndomorphism hcov x z‖ ^ 2 ≤
      2 * (cov.curvatureTensorNormSq x * ‖z‖ ^ 2) := by
    have hswap : (∑ k, ∑ l, ∑ i, ∑ j,
          ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2) =
        cov.curvatureTensorNormSq x := by
      rw [cov.curvatureTensorNormSq_eq_sum_orthonormalBasis x b b]
      calc
        ∑ k, ∑ l, ∑ i, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2
            = ∑ k, ∑ i, ∑ l, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
                Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
        _ = ∑ i, ∑ k, ∑ l, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
                Finset.sum_comm
        _ = ∑ i, ∑ k, ∑ j, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
                Finset.sum_congr rfl fun i _ ↦
                  Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
        _ = ∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
                Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
        _ = ∑ i, ∑ j, ∑ l, ∑ k, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
                Finset.sum_congr rfl fun i _ ↦
                  Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
    calc
      8 * ‖cov.curvatureEndomorphism hcov x z‖ ^ 2
          = ∑ k, ∑ l, 4 *
              ⟪exteriorPower.ιMulti ℝ 2 ![b k, b l], cov.curvatureEndomorphism hcov x z⟫ ^ 2 := by
          simp_rw [← Finset.mul_sum, hnorm_sq]
          ring
      _ ≤ ∑ k, ∑ l, (2 * ‖z‖ ^ 2) *
            ∑ i, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 :=
          Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun l _ ↦ hpair k l
      _ = (2 * ‖z‖ ^ 2) *
            ∑ k, ∑ l, ∑ i, ∑ j, ⟪cov.curvatureTensor x (b i) (b j) (b l), b k⟫ ^ 2 := by
          simp_rw [← Finset.mul_sum]
      _ = 2 * (cov.curvatureTensorNormSq x * ‖z‖ ^ 2) := by
          rw [hswap]
          ring
  refine (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (cov.curvatureTensorNorm_nonneg x))
      (norm_nonneg z))).mp ?_
  rw [mul_pow, mul_pow, cov.curvatureTensorNorm_sq]
  linarith

/-- The Rayleigh quotient of `curvatureEndomorphism` is bounded below by `-(1 / 2) * |Rm|`:
`-(1 / 2) * |Rm| * ‖z‖² ≤ ⟪Rop z, z⟫`. -/
theorem neg_half_curvatureTensorNorm_mul_norm_sq_le_inner_curvatureEndomorphism
    (x : M) (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    -((1 / 2 : ℝ) * cov.curvatureTensorNorm x) * ‖z‖ ^ 2 ≤
      ⟪cov.curvatureEndomorphism hcov x z, z⟫ := by
  have h1 : |⟪cov.curvatureEndomorphism hcov x z, z⟫| ≤
      ‖cov.curvatureEndomorphism hcov x z‖ * ‖z‖ :=
    abs_real_inner_le_norm _ _
  have h2 : ‖cov.curvatureEndomorphism hcov x z‖ * ‖z‖ ≤
      ((1 / 2 : ℝ) * cov.curvatureTensorNorm x) * ‖z‖ ^ 2 := by
    calc
      ‖cov.curvatureEndomorphism hcov x z‖ * ‖z‖
          ≤ ((1 / 2 : ℝ) * cov.curvatureTensorNorm x * ‖z‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (cov.norm_curvatureEndomorphism_apply_le hcov x z)
            (norm_nonneg z)
      _ = ((1 / 2 : ℝ) * cov.curvatureTensorNorm x) * ‖z‖ ^ 2 := by ring
  linarith [neg_le_of_abs_le (h1.trans h2)]

/-- Weaker Rayleigh lower bound `-|Rm| * ‖z‖² ≤ ⟪Rop z, z⟫`, directly matching `ν ≥ -|Rm|`. -/
theorem neg_curvatureTensorNorm_mul_norm_sq_le_inner_curvatureEndomorphism
    (x : M) (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    -(cov.curvatureTensorNorm x) * ‖z‖ ^ 2 ≤
      ⟪cov.curvatureEndomorphism hcov x z, z⟫ := by
  have h := cov.neg_half_curvatureTensorNorm_mul_norm_sq_le_inner_curvatureEndomorphism hcov x z
  have hnn : 0 ≤ cov.curvatureTensorNorm x * ‖z‖ ^ 2 :=
    mul_nonneg (cov.curvatureTensorNorm_nonneg x) (sq_nonneg _)
  linarith

/-- **Rayleigh quotient vs eigenvalues for `curvatureEndomorphism`**: for a torsion-free metric
connection, `α ‖z‖² ≤ ⟪Rop z, z⟫` for all bivectors `z` if and only if every eigenvalue of `Rop`
is at least `α`. -/
theorem forall_le_inner_curvatureEndomorphism_iff_forall_hasEigenvalue
    (ht : cov.torsion = 0) (x : M) (α : ℝ) :
    (∀ z : ⋀[ℝ]^2 (TangentSpace I x), α * ‖z‖ ^ 2 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫) ↔
      ∀ μ : ℝ, (cov.curvatureEndomorphism hcov x).HasEigenvalue μ → α ≤ μ := by
  constructor
  · intro h μ hμ
    obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
    have hRay := h z
    have hzw : cov.curvatureEndomorphism hcov x z = μ • z := hz.apply_eq_smul
    rw [hzw] at hRay
    have hsmul : ⟪μ • z, z⟫ = μ * ‖z‖ ^ 2 := by
      change (innerₗ (⋀[ℝ]^2 (TangentSpace I x))) (μ • z) z = μ * ‖z‖ ^ 2
      rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, innerₗ_apply_apply,
        real_inner_self_eq_norm_sq]
    rw [hsmul] at hRay
    exact le_of_mul_le_mul_right hRay (sq_pos_of_pos (norm_pos_iff.mpr hz.right))
  · intro h z
    have hA := cov.isSymmetric_curvatureEndomorphism hcov ht x
    simpa only [RCLike.re_to_real] using
      LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices hA rfl
        (s := Set.univ) (fun i _ ↦ h _ (hA.hasEigenvalue_eigenvalues rfl i))
        (x := z) (by simp)

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Exact curvature norm on a space of constant curvature tensor**: if `R(u, v) w =
κ • (⟪v, w⟫ u - ⟪u, w⟫ v)`, then `|Rm|² = 2 * d * (d - 1) * κ²` where `d = dim T_x M`. -/
theorem curvatureTensorNormSq_eq_of_eq_smul_inner_sub (x : M) (κ : ℝ)
    (hκ : ∀ u v w : TangentSpace I x,
      cov.curvatureTensor x u v w = κ • (⟪v, w⟫ • u - ⟪u, w⟫ • v)) :
    cov.curvatureTensorNormSq x =
      2 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * κ ^ 2 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hb_inner := orthonormal_iff_ite.mp b.orthonormal
  rw [cov.curvatureTensorNormSq_eq_sum_norm_sq x b b]
  have hterm (i j k : Fin (Module.finrank ℝ (TangentSpace I x))) :
      ‖cov.curvatureTensor x (b i) (b j) (b k)‖ ^ 2 =
        if i = j then 0
        else if j = k then κ ^ 2
        else if i = k then κ ^ 2
        else 0 := by
    rw [hκ (b i) (b j) (b k), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      hb_inner, hb_inner]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rcases eq_or_ne j k with rfl | hjk
      · simp [hij, b.orthonormal.norm_eq_one]
      · rcases eq_or_ne i k with rfl | hik
        · simp [hij, hjk, b.orthonormal.norm_eq_one]
        · simp [hjk, hik]
  simp_rw [hterm]
  have hinner (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      (∑ k, if i = j then (0 : ℝ) else if j = k then κ ^ 2 else if i = k then κ ^ 2 else 0) =
        if i = j then 0 else 2 * κ ^ 2 := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp only [hij, ite_false]
      have hs : ∀ k, (if j = k then κ ^ 2 else if i = k then κ ^ 2 else 0) =
          (if k = j then κ ^ 2 else 0) + (if k = i then κ ^ 2 else 0) := fun k ↦ by
        by_cases hjk : j = k
        · subst hjk
          simp [Ne.symm hij]
        · by_cases hik : i = k
          · subst hik
            simp [hjk, Ne.symm hjk]
          · simp [hjk, Ne.symm hjk, hik, Ne.symm hik]
      simp_rw [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
  simp_rw [hinner]
  have hsum_ij : (∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
      ∑ j : Fin (Module.finrank ℝ (TangentSpace I x)),
        if i = j then (0 : ℝ) else 2 * κ ^ 2) =
      ((Module.finrank ℝ (TangentSpace I x) : ℝ) *
        (Module.finrank ℝ (TangentSpace I x) : ℝ) -
          (Module.finrank ℝ (TangentSpace I x) : ℝ)) * (2 * κ ^ 2) := by
    have hsplit (i) : (∑ j : Fin (Module.finrank ℝ (TangentSpace I x)),
        if i = j then (0 : ℝ) else 2 * κ ^ 2) =
        ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1) * (2 * κ ^ 2) := by
      have : ∀ j, (if i = j then (0 : ℝ) else 2 * κ ^ 2) =
          2 * κ ^ 2 - if j = i then 2 * κ ^ 2 else 0 := fun j ↦ by
        rcases eq_or_ne j i with rfl | hji <;> [simp; simp [hji, hji.symm]]
      simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    simp_rw [hsplit, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  rw [hsum_ij]
  change ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) - (Module.finrank ℝ E : ℝ)) *
      (2 * κ ^ 2) = _
  ring

end ExteriorSquareAndSpectrum

end CovariantDerivative

section IsometryInvariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- A local Riemannian isometry preserves the squared Hilbert–Schmidt curvature tensor norm. -/
theorem TauCeti.IsLocalRiemannianIsometry.curvatureTensorNormSq_map
    (hf : TauCeti.IsLocalRiemannianIsometry I J f) (x : M) :
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNormSq (f x) =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq x := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [(CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_eq_sum_orthonormalBasis
      x b b,
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNormSq_eq_sum_orthonormalBasis
      (f x) (b.map e) (b.map e)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [OrthonormalBasis.map_apply, he, hf.inner_curvatureTensor_mfderiv]

/-- A local Riemannian isometry preserves the Hilbert–Schmidt curvature tensor norm `|Rm|`. -/
theorem TauCeti.IsLocalRiemannianIsometry.curvatureTensorNorm_map
    (hf : TauCeti.IsLocalRiemannianIsometry I J f) (x : M) :
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNorm (f x) =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x := by
  simp only [CovariantDerivative.curvatureTensorNorm, hf.curvatureTensorNormSq_map]

end IsometryInvariance

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Helper packaging the exterior-square inner product of a Riemannian bundle as a pure bilinear
map on `⋀[ℝ]^2 (TangentSpace I x)`, independent of typeclass diamonds. -/
private def extInnerBilin (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) : ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  innerₗ (⋀[ℝ]^2 (TangentSpace I x))

omit [T2Space M] in
private theorem extInnerBilin_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (z w : ⋀[ℝ]^2 (TangentSpace I x)) :
    extInnerBilin g x z w =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ⟪z, w⟫) :=
  rfl

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  {c : ℝ} (hc : 0 < c)

/-- **Rescaling of `|Rm|²`**: multiplying a smooth metric by a positive constant `c` multiplies
`curvatureTensorNormSq` by `c⁻²`. -/
theorem curvatureTensorNormSq_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq x) =
    c⁻¹ ^ 2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq x) := by
  let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  let b₀ := letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    stdOrthonormalBasis ℝ (TangentSpace I x)
  have hb₀_inner (i j) : g.inner x (b₀ i) (b₀ j) = if i = j then 1 else 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact orthonormal_iff_ite.mp b₀.orthonormal i j
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩
  let bcVec : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x :=
    fun i ↦ (Real.sqrt c)⁻¹ • b₀ i
  have hbc_ortho : Orthonormal ℝ bcVec := by
    rw [orthonormal_iff_ite]
    intro i j
    have hinner : ∀ u v : TangentSpace I x, ⟪u, v⟫ = c * g.inner x u v := fun u v ↦
      g.rescale_inner (fun _ ↦ c) contMDiff_const (fun _ ↦ hc) x u v
    rw [hinner]
    change c * g.inner x ((Real.sqrt c)⁻¹ • b₀ i) ((Real.sqrt c)⁻¹ • b₀ j) = if i = j then 1 else 0
    simp only [map_smul, smul_apply, smul_eq_mul, hb₀_inner]
    rcases eq_or_ne i j with rfl | hij
    · simp only [ite_true]
      have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
      calc
        c * ((Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * 1))
            = c * (Real.sqrt c * Real.sqrt c)⁻¹ := by ring
        _ = c * c⁻¹ := by rw [hsq]
        _ = 1 := mul_inv_cancel₀ hc.ne'
    · simp [hij]
  have hbc_span : ⊤ ≤ Submodule.span ℝ (Set.range bcVec) := by
    intro v _
    have hv : v = ∑ i, (Real.sqrt c * g.inner x (b₀ i) v) • bcVec i := by
      have hrepr : v = ∑ i, g.inner x (b₀ i) v • b₀ i := by
        let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
        exact (b₀.sum_repr' v).symm
      conv_lhs => rw [hrepr]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [bcVec, smul_smul]
      rw [mul_comm (Real.sqrt c) (g.inner x (b₀ i) v), mul_assoc,
        mul_inv_cancel₀ (Real.sqrt_pos.mpr hc).ne', mul_one]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  let bc : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    OrthonormalBasis.mk hbc_ortho hbc_span
  have hbc_apply (i) : bc i = (Real.sqrt c)⁻¹ • b₀ i :=
    OrthonormalBasis.coe_mk hbc_ortho hbc_span ▸ rfl
  rw [(CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_eq_sum_orthonormalBasis
    x bc bc]
  have hR_eq :
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) :=
    g.curvatureTensor_leviCivitaConnection_rescale_const hc x
  have hterm (i j k l) :
      ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureTensor x
          (bc i) (bc j) (bc k), bc l⟫ ^ 2 =
        c⁻¹ ^ 2 *
          g.inner x ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨g.toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x)
            (b₀ i) (b₀ j) (b₀ k)) (b₀ l) ^ 2 := by
    have hinner : ∀ u v : TangentSpace I x, ⟪u, v⟫ = c * g.inner x u v := fun u v ↦
      g.rescale_inner (fun _ ↦ c) contMDiff_const (fun _ ↦ hc) x u v
    rw [hbc_apply, hbc_apply, hbc_apply, hbc_apply, hR_eq, hinner]
    change (c * g.inner x
        ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x)
          ((Real.sqrt c)⁻¹ • b₀ i) ((Real.sqrt c)⁻¹ • b₀ j) ((Real.sqrt c)⁻¹ • b₀ k))
        ((Real.sqrt c)⁻¹ • b₀ l)) ^ 2 = _
    simp only [map_smul, LinearMap.smul_apply, smul_apply, smul_eq_mul]
    have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
    calc
      (c * ((Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ *
          g.inner x ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
              ⟨g.toRiemannianMetric⟩;
            (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x)
            (b₀ i) (b₀ j) (b₀ k)) (b₀ l)))))) ^ 2
          = (c * ((Real.sqrt c * Real.sqrt c)⁻¹ * (Real.sqrt c * Real.sqrt c)⁻¹)) ^ 2 *
              g.inner x ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
                  ⟨g.toRiemannianMetric⟩;
                (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x)
                (b₀ i) (b₀ j) (b₀ k)) (b₀ l) ^ 2 := by
            ring
      _ = c⁻¹ ^ 2 * g.inner x
            ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
              (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x)
              (b₀ i) (b₀ j) (b₀ k)) (b₀ l) ^ 2 := by
            rw [hsq, mul_inv_cancel_left₀ hc.ne']
  simp_rw [hterm, ← Finset.mul_sum]
  refine congrArg (c⁻¹ ^ 2 * ·) ?_
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.curvatureTensorNormSq_eq_sum_orthonormalBasis
    (CovariantDerivative.leviCivitaConnection I M) x b₀ b₀).symm

/-- **Rescaling of `|Rm|`**: multiplying a smooth metric by `c > 0` multiplies `|Rm|` by `c⁻¹`. -/
@[simp]
theorem curvatureTensorNorm_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x) =
    c⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x) := by
  simp only [CovariantDerivative.curvatureTensorNorm,
    g.curvatureTensorNormSq_rescale_const hc x,
    Real.sqrt_mul (sq_nonneg c⁻¹), Real.sqrt_sq (inv_pos.mpr hc).le]

/-- Helper packaging the curvature-endomorphism bilinear form `⟪Rop ·, ·⟫` as a pure bilinear map
on `⋀[ℝ]^2 (TangentSpace I x)`. -/
private def extCurvBilin (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) : ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  ((innerₗ (⋀[ℝ]^2 (TangentSpace I x))).compl₁₂
    ((CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x) LinearMap.id)

private theorem extCurvBilin_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (z w : ⋀[ℝ]^2 (TangentSpace I x)) :
    extCurvBilin g x z w =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, w⟫) :=
  rfl

omit [T2Space M] in
private theorem extInnerBilin_rescale_const (x : M) :
    extInnerBilin (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x =
      c ^ 2 • extInnerBilin g x := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro u
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have h1 : extInnerBilin (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x
      (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
      c ^ 2 * (extInnerBilin g x
        (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v)) := by
    let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
    have hlhs : extInnerBilin gc x
        (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
        (Matrix.of fun i j : Fin 2 ↦ gc.inner x (u j) (v i)).det := by
      rw [extInnerBilin_apply]
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩
      rw [exteriorPower.inner_ιMulti_ιMulti]
      rfl
    have hrhs : extInnerBilin g x
        (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
        (Matrix.of fun i j : Fin 2 ↦ g.inner x (u j) (v i)).det := by
      rw [extInnerBilin_apply]
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      rw [exteriorPower.inner_ιMulti_ιMulti]
      rfl
    rw [hlhs, hrhs]
    have hmat : (Matrix.of fun i j : Fin 2 ↦ gc.inner x (u j) (v i)) =
        c • (Matrix.of fun i j : Fin 2 ↦ g.inner x (u j) (v i)) := by
      ext i j
      simp [gc, g.rescale_inner]
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
  simpa only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, smul_eq_mul] using h1

private theorem extCurvBilin_rescale_const (x : M) :
    extCurvBilin (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) x =
      c • extCurvBilin g x := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro u
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have hR_eq := g.curvatureTensor_leviCivitaConnection_rescale_const hc x
  have hlhs : extCurvBilin gc x (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
      gc.inner x ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) (u 0) (u 1) (v 1))
        (v 0) := by
    rw [extCurvBilin_apply]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩
    rw [CovariantDerivative.inner_curvatureEndomorphism_ιMulti, hR_eq]
    rfl
  have hrhs : extCurvBilin g x (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
      g.inner x ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) (u 0) (u 1) (v 1))
        (v 0) := by
    rw [extCurvBilin_apply]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    rw [CovariantDerivative.inner_curvatureEndomorphism_ιMulti]
    rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, smul_eq_mul,
    hlhs, hrhs, gc, g.rescale_inner]

/-- **Rescaling of curvature-operator lower bounds**: for `c > 0`, `Rop_{cg} ≥ α id` at `x`
if and only if `Rop_g ≥ (c * α) id` at `x`. -/
theorem forall_le_inner_curvatureEndomorphism_rescale_const_iff (x : M) (α : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ∀ z : ⋀[ℝ]^2 (TangentSpace I x), α * ‖z‖ ^ 2 ≤
        ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      ∀ z : ⋀[ℝ]^2 (TangentSpace I x), (c * α) * ‖z‖ ^ 2 ≤
        ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) := by
  let gc := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc
  have hinner_z (z : ⋀[ℝ]^2 (TangentSpace I x)) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩;
        ‖z‖ ^ 2) =
      c ^ 2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ‖z‖ ^ 2) := by
    have h := LinearMap.congr_fun₂ (g.extInnerBilin_rescale_const hc x) z z
    simp only [LinearMap.smul_apply, smul_eq_mul, extInnerBilin_apply] at h
    calc
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩;
          ‖z‖ ^ 2)
          = (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩;
              ⟪z, z⟫) := by
            let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩
            exact (real_inner_self_eq_norm_sq z).symm
      _ = c ^ 2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
            ⟪z, z⟫) := h
      _ = c ^ 2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
            ‖z‖ ^ 2) := by
            congr 1
            let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
            exact real_inner_self_eq_norm_sq z
  have hcurv_z (z : ⋀[ℝ]^2 (TangentSpace I x)) :
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gc.toRiemannianMetric⟩;
        ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) =
      c * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) := by
    have h := LinearMap.congr_fun₂ (g.extCurvBilin_rescale_const hc x) z z
    simp only [LinearMap.smul_apply, smul_eq_mul, extCurvBilin_apply] at h
    exact h
  refine forall_congr' fun z ↦ ?_
  rw [hinner_z z, hcurv_z z]
  constructor <;> intro h
  · refine le_of_mul_le_mul_left ?_ hc
    linarith
  · have h' := mul_le_mul_of_nonneg_left h hc.le
    linarith

end Bundle.ContMDiffRiemannianMetric
