/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Fibrewise sums of Euclidean coordinates

A map `f : ι → κ` of finite index types coarsens a Euclidean coordinate system: the coordinates
of a vector indexed by `ι` are merged into the groups cut out by the fibres of `f`, one group
summed into each coordinate of a vector indexed by `κ`.  This is Mathlib's `FunOnFinite.map`,
here read through `EuclideanSpace.equiv` so that it acts on Euclidean space, where it is again
continuous and measurable. The coordinates may be real or complex; measurability uses the
Borel measurable structure on the scalar field.

## Main definitions

* `TauCeti.euclideanFiberSum` sums the coordinates of a Euclidean vector over each fibre of a map
  of index types.

## Additional results

* `EuclideanSpace.measurableSet_setOf_forall_pos`: the real positive orthant is measurable.
* `EuclideanSpace.sqrt_card_pos`: the square root of the dimension is positive.
* `EuclideanSpace.sum_mul_dist_basisFun_le_sqrt`: a point of the standard simplex is, on average
  over the vertices weighted by its coordinates, at distance at most `√(1 - ‖x‖ ^ 2)` from them.
* `EuclideanSpace.abs_sub_sum_mul_basisFun_le_sqrt`: consequently a `K`-Lipschitz function at a
  point of the standard simplex is within `K * √(1 - ‖x‖ ^ 2)` of the coordinate-weighted average
  of its values at the vertices.
* `EuclideanSpace.consEquivL`: splitting off the first coordinate identifies `𝕜ⁿ⁺¹` with
  `𝕜 × 𝕜ⁿ`.
* `EuclideanSpace.finTwoEquivProd`: the two coordinates identify `𝕜²` isometrically with the `L²`
  product `WithLp 2 (𝕜 × 𝕜)`.
-/

public section

noncomputable section

open scoped BigOperators

namespace EuclideanSpace

/-- The positive orthant in finite real Euclidean space is measurable. -/
theorem measurableSet_setOf_forall_pos {ι : Type*} [Finite ι] :
    MeasurableSet {x : EuclideanSpace ℝ ι | ∀ i, 0 < x i} := by
  let : Fintype ι := Fintype.ofFinite ι
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_lt (measurable_const (a := (0 : ℝ))) (by fun_prop)

variable {𝕜 : Type*} {ι : Type*} [Fintype ι]

/-- The square root of the dimension of a nonzero Euclidean space is positive. -/
theorem sqrt_card_pos [Nonempty ι] : 0 < Real.sqrt (Fintype.card ι) :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)

/-- For a vector `x` whose coordinates sum to one, the `x`-weighted mean squared distance from
`x` to the standard basis vectors is `1 - ‖x‖ ^ 2`. -/
theorem sum_mul_dist_basisFun_sq {x : EuclideanSpace ℝ ι} (hx1 : ∑ i, x i = 1) :
    ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 = 1 - ‖x‖ ^ 2 := by
  classical
  have hdist (i : ι) :
      dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 = ‖x‖ ^ 2 - 2 * x i + 1 := by
    rw [EuclideanSpace.basisFun_apply, dist_eq_norm, norm_sub_sq_real,
      EuclideanSpace.inner_single_right]
    simp
  calc
    ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 =
        ∑ i, (‖x‖ ^ 2 * x i - 2 * x i ^ 2 + x i) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hdist]; ring
    _ = ‖x‖ ^ 2 * ∑ i, x i - 2 * ∑ i, x i ^ 2 + ∑ i, x i := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 1 - ‖x‖ ^ 2 := by
      rw [hx1, ← EuclideanSpace.real_norm_sq_eq]
      ring

/-- A point `x` of the standard simplex is, on average over the vertices weighted by its own
coordinates, at distance at most `√(1 - ‖x‖ ^ 2)` from them. -/
theorem sum_mul_dist_basisFun_le_sqrt {x : EuclideanSpace ℝ ι} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∑ i, x i = 1) :
    ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ≤ √(1 - ‖x‖ ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  calc
    (∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i)) ^ 2 ≤
        (∑ i, x i) * ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · exact fun i _ ↦ hx0 i
      · exact fun i _ ↦ mul_nonneg (hx0 i) (sq_nonneg _)
      · exact fun i _ ↦ le_of_eq (by ring)
    _ = 1 - ‖x‖ ^ 2 := by rw [hx1, one_mul, sum_mul_dist_basisFun_sq hx1]

/-- A `K`-Lipschitz function on the standard simplex differs at `x` from the `x`-weighted average
of its values at the vertices by at most `K * √(1 - ‖x‖ ^ 2)`. -/
theorem abs_sub_sum_mul_basisFun_le_sqrt {x : EuclideanSpace ℝ ι} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∑ i, x i = 1) {f : EuclideanSpace ℝ ι → ℝ} {K : NNReal} (hK : LipschitzWith K f) :
    |f x - ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i)| ≤ K * √(1 - ‖x‖ ^ 2) :=
  calc
    |f x - ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i)| =
        |∑ i, x i * (f x - f (EuclideanSpace.basisFun ι ℝ i))| := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hx1, one_mul]
    _ ≤ ∑ i, x i * |f x - f (EuclideanSpace.basisFun ι ℝ i)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
      rw [abs_mul, abs_of_nonneg (hx0 i)]
    _ ≤ ∑ i, x i * (K * dist x (EuclideanSpace.basisFun ι ℝ i)) := by
      refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hx0 i)
      simpa [Real.dist_eq] using hK.dist_le_mul x (EuclideanSpace.basisFun ι ℝ i)
    _ = K * ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ K * √(1 - ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_mul_dist_basisFun_le_sqrt hx0 hx1) K.coe_nonneg

variable [RCLike 𝕜]

variable (𝕜) in
/-- Splitting off the first coordinate identifies `𝕜ⁿ⁺¹` with `𝕜 × 𝕜ⁿ`: the continuous linear
equivalence `(t, x) ↦ (t, x₀, …, xₙ₋₁)`. This is `Fin.consEquivL` read in Euclidean
coordinates. -/
def consEquivL (n : ℕ) : (𝕜 × EuclideanSpace 𝕜 (Fin n)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  ((ContinuousLinearEquiv.refl 𝕜 𝕜).prodCongr (EuclideanSpace.equiv (Fin n) 𝕜)).trans
    ((Fin.consEquivL 𝕜 fun _ => 𝕜).trans (EuclideanSpace.equiv (Fin (n + 1)) 𝕜).symm)

theorem consEquivL_apply {n : ℕ} (z : 𝕜 × EuclideanSpace 𝕜 (Fin n)) :
    consEquivL 𝕜 n z = WithLp.toLp 2 (Fin.cons z.1 (WithLp.ofLp z.2)) := by
  ext i
  simp [consEquivL, Fin.consEquivL_apply, PiLp.coe_continuousLinearEquiv]

@[simp]
theorem consEquivL_apply_zero {n : ℕ} (z : 𝕜 × EuclideanSpace 𝕜 (Fin n)) :
    consEquivL 𝕜 n z 0 = z.1 := by
  simp [consEquivL_apply]

@[simp]
theorem consEquivL_apply_succ {n : ℕ} (z : 𝕜 × EuclideanSpace 𝕜 (Fin n)) (i : Fin n) :
    consEquivL 𝕜 n z i.succ = z.2 i := by
  simp [consEquivL_apply]

theorem consEquivL_symm_apply {n : ℕ} (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    (consEquivL 𝕜 n).symm x = (x 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp x))) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

@[simp]
theorem consEquivL_symm_apply_fst {n : ℕ} (x : EuclideanSpace 𝕜 (Fin (n + 1))) :
    ((consEquivL 𝕜 n).symm x).1 = x 0 := by
  simp [consEquivL_symm_apply]

@[simp]
theorem consEquivL_symm_apply_snd {n : ℕ} (x : EuclideanSpace 𝕜 (Fin (n + 1))) (i : Fin n) :
    ((consEquivL 𝕜 n).symm x).2 i = x i.succ := by
  simp [consEquivL_symm_apply, Fin.tail]

variable (𝕜) in
/-- The two coordinates identify `𝕜²` with the `L²` product `WithLp 2 (𝕜 × 𝕜)`, as a linear
isometry equivalence `x ↦ (x 0, x 1)`. -/
def finTwoEquivProd : EuclideanSpace 𝕜 (Fin 2) ≃ₗᵢ[𝕜] WithLp 2 (𝕜 × 𝕜) where
  toFun x := WithLp.toLp 2 (x 0, x 1)
  invFun p := WithLp.toLp 2 ![p.fst, p.snd]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    ext k
    fin_cases k <;> rfl
  right_inv _ := rfl
  norm_map' x := by
    -- `simp` does not unfold the coercion of the linear equivalence under construction, so state
    -- its value `WithLp.toLp 2 (x 0, x 1)` first.
    change ‖WithLp.toLp 2 (x 0, x 1)‖ = ‖x‖
    simp [WithLp.prod_norm_eq_of_L2, EuclideanSpace.norm_eq, Fin.sum_univ_two]

@[simp]
theorem finTwoEquivProd_apply_fst (x : EuclideanSpace 𝕜 (Fin 2)) :
    (finTwoEquivProd 𝕜 x).fst = x 0 :=
  (rfl)

@[simp]
theorem finTwoEquivProd_apply_snd (x : EuclideanSpace 𝕜 (Fin 2)) :
    (finTwoEquivProd 𝕜 x).snd = x 1 :=
  (rfl)

@[simp]
theorem finTwoEquivProd_symm_apply (p : WithLp 2 (𝕜 × 𝕜)) :
    (finTwoEquivProd 𝕜).symm p = WithLp.toLp 2 ![p.fst, p.snd] :=
  (rfl)

end EuclideanSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum the coordinates of a Euclidean vector over each fibre of `f`.

This is Mathlib's `FunOnFinite.map` read in Euclidean coordinates. -/
def euclideanFiberSum (f : ι → κ) (x : EuclideanSpace 𝕜 ι) : EuclideanSpace 𝕜 κ :=
  (EuclideanSpace.equiv κ 𝕜).symm (FunOnFinite.map f (EuclideanSpace.equiv ι 𝕜 x))

@[simp]
theorem euclideanFiberSum_apply [DecidableEq κ] (f : ι → κ) (x : EuclideanSpace 𝕜 ι) (j : κ) :
    euclideanFiberSum f x j = ∑ i with f i = j, x i := by
  simp [euclideanFiberSum, FunOnFinite.map_apply_apply]

/-- Fibrewise summation is continuous. -/
@[fun_prop]
theorem continuous_euclideanFiberSum (f : ι → κ) :
    Continuous (euclideanFiberSum (𝕜 := 𝕜) (ι := ι) f) :=
  (EuclideanSpace.equiv κ 𝕜).symm.continuous.comp <|
    (FunOnFinite.continuous_map 𝕜 f).comp (EuclideanSpace.equiv ι 𝕜).continuous

/-- Fibrewise summation is measurable. -/
@[fun_prop]
theorem measurable_euclideanFiberSum [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : ι → κ) :
    Measurable (euclideanFiberSum (𝕜 := 𝕜) (ι := ι) f) :=
  (continuous_euclideanFiberSum (𝕜 := 𝕜) f).measurable

end TauCeti
