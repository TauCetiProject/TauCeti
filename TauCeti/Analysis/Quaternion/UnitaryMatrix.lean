/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix

/-!
# The compact symplectic group `Sp(n)` of quaternionic unitary matrices

The compact symplectic group `Sp(n)` is the group `unitary (Matrix ι ι ℍ)` of quaternionic
matrices `A` with `Aᴴ A = A Aᴴ = 1`. This file shows that it is a compact group, and that it acts
by real linear isometries on the quaternionic coordinate space `ℍⁿ = PiLp 2 (fun _ : ι ↦ ℍ)`,
transitively on its unit sphere `S⁴ⁿ⁻¹`.

Quaternionic matrices act on column vectors on the left, `x ↦ A x`, and so commute with
quaternionic scalars acting on the right, `A (x q) = (A x) q`
(`TauCeti.quaternionUnitaryIsometry_op_smul`). The norm of `ℍⁿ` is recovered from the
quaternionic Hermitian product `xᴴ x = Σₖ star xₖ * xₖ`, a real number
(`TauCeti.star_dotProduct_self_ofLp`), so a unitary matrix, which preserves this product,
preserves the norm.

A unitary matrix has unit columns, so all its entries have norm at most one
(`TauCeti.norm_apply_le_one_of_mem_unitary_quaternion`); being closed, the unitary group is
compact.

Transitivity on the sphere uses quaternionic Householder reflections. If a unit vector `y` has
real `i`-th coordinate and `v = eᵢ - y ≠ 0`, then `H = 1 - (2 / |v|²) v vᴴ` is a Hermitian
involution, hence unitary, and `H eᵢ = y`. A general unit vector `x` is brought to this form by
a unit quaternion `u` on the right, and the diagonal unitary matrix with `ū` in position `i`
then corrects the phase.

## Main declarations

* `TauCeti.isCompact_unitary_quaternion`: `Sp(n)` is compact.
* `TauCeti.quaternionUnitaryIsometry`: the action of `Sp(n)` on `ℍⁿ` by real linear isometries,
  `A ↦ (x ↦ A x)`.
* `TauCeti.quaternionUnitaryIsometry_op_smul`: the action commutes with right multiplication by
  quaternions.
* `TauCeti.exists_quaternionUnitaryIsometry_apply_single_eq`: `Sp(n)` acts transitively on the
  unit sphere: every unit vector is the image of the basis vector `eᵢ`.

## References

* C. Chevalley, *Theory of Lie Groups I*, Princeton University Press, 1946, Chapter I, §§VII–IX
  (the symplectic group `Sp(n)` and its compactness).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

noncomputable section

open Metric MulOpposite Quaternion
open scoped Matrix RightActions

namespace TauCeti

variable {ι : Type*} [Fintype ι]

section Norm

/-- The quaternionic Hermitian square `vᴴ v = Σₖ star vₖ * vₖ` of a quaternionic vector is the real
number `Σₖ |vₖ|²`. -/
theorem star_dotProduct_self_quaternion (v : ι → ℍ) :
    star v ⬝ᵥ v = ((∑ k, normSq (v k) : ℝ) : ℍ) := by
  simp only [dotProduct, Pi.star_apply, star_mul_self, ← algebraMap_def, map_sum]

/-- The quaternionic Hermitian square of a vector of `ℍⁿ = PiLp 2 (fun _ : ι ↦ ℍ)` is its squared
norm. -/
theorem star_dotProduct_self_ofLp (x : PiLp 2 fun _ : ι ↦ ℍ) :
    star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x = ((‖x‖ ^ 2 : ℝ) : ℍ) := by
  rw [star_dotProduct_self_quaternion, PiLp.norm_sq_eq_of_L2]
  simp only [normSq_eq_norm_mul_self, sq]

end Norm

section Compact

/-- Every entry of a quaternionic unitary matrix has norm at most one: the columns of a unitary
matrix are unit vectors. -/
theorem norm_apply_le_one_of_mem_unitary_quaternion [DecidableEq ι] {U : Matrix ι ι ℍ}
    (hU : U ∈ unitary (Matrix ι ι ℍ)) (i j : ι) : ‖U i j‖ ≤ 1 := by
  -- The diagonal entry `(Uᴴ U)ⱼⱼ = Σₖ |Uₖⱼ|²` is `1`.
  have hcol : (star (U.col j) ⬝ᵥ U.col j : ℍ) = ((1 : ℝ) : ℍ) := by
    have h := congrFun (congrFun hU.1 j) j
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply] at h
    simpa [dotProduct, Matrix.conjTranspose_apply] using h
  rw [star_dotProduct_self_quaternion, Quaternion.coe_inj] at hcol
  have hle : normSq (U i j) ≤ 1 :=
    calc normSq (U i j) ≤ ∑ k, normSq (U.col j k) :=
          Finset.single_le_sum (f := fun k ↦ normSq (U.col j k)) (fun k _ ↦ normSq_nonneg)
            (Finset.mem_univ i)
      _ = 1 := hcol
  rw [normSq_eq_norm_mul_self] at hle
  nlinarith [norm_nonneg (U i j)]

/-- **The compact symplectic group is compact**: the quaternionic unitary matrices form a compact
subset of `Matrix ι ι ℍ`. -/
theorem isCompact_unitary_quaternion [DecidableEq ι] :
    IsCompact (unitary (Matrix ι ι ℍ) : Set (Matrix ι ι ℍ)) :=
  ((isCompact_closedBall (0 : ℍ) 1).matrix).of_isClosed_subset isClosed_unitary
    fun _ hU _ _ ↦ mem_closedBall_zero_iff.2 (norm_apply_le_one_of_mem_unitary_quaternion hU _ _)

/-- The compact symplectic group is a compact space. -/
instance [DecidableEq ι] : CompactSpace (unitary (Matrix ι ι ℍ)) :=
  isCompact_iff_compactSpace.1 isCompact_unitary_quaternion

end Compact

section Isometry

variable [DecidableEq ι]

/-- The real linear map `x ↦ A x` of `ℍⁿ` given by a quaternionic matrix. -/
private def mulVecLinearMap (A : Matrix ι ι ℍ) :
    (PiLp 2 fun _ : ι ↦ ℍ) →ₗ[ℝ] PiLp 2 fun _ : ι ↦ ℍ where
  toFun x := WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)
  map_add' x y := by simp [Matrix.mulVec_add]
  map_smul' c x := by simp [Matrix.mulVec_smul]

variable (ι) in
/-- **The compact symplectic group acts on `ℍⁿ` by real linear isometries**: a quaternionic
unitary matrix `A` acts on `ℍⁿ = PiLp 2 (fun _ : ι ↦ ℍ)` by `x ↦ A x`. -/
def quaternionUnitaryIsometry :
    unitary (Matrix ι ι ℍ) →* (PiLp 2 fun _ : ι ↦ ℍ) ≃ₗᵢ[ℝ] PiLp 2 fun _ : ι ↦ ℍ where
  toFun A :=
    { mulVecLinearMap A.1 with
      invFun := mulVecLinearMap (star A).1
      left_inv x := by
        simp [mulVecLinearMap, Matrix.mulVec_mulVec, A.2.1]
      right_inv x := by
        simp [mulVecLinearMap, Matrix.mulVec_mulVec, A.2.2]
      norm_map' x := by
        -- `A` preserves the quaternionic Hermitian square, which is the squared norm.
        have h : star (A.1 *ᵥ WithLp.ofLp x) ⬝ᵥ (A.1 *ᵥ WithLp.ofLp x) =
            star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x := by
          rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
            ← Matrix.star_eq_conjTranspose, A.2.1, Matrix.vecMul_one]
        rw [← WithLp.ofLp_toLp 2 (A.1 *ᵥ WithLp.ofLp x),
          star_dotProduct_self_ofLp, star_dotProduct_self_ofLp, Quaternion.coe_inj] at h
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h }
  map_one' := by
    ext x : 1
    simp [mulVecLinearMap]
  map_mul' A B := by
    ext x : 1
    simp [mulVecLinearMap, Matrix.mulVec_mulVec]

/-- A quaternionic unitary matrix acts on `ℍⁿ` by multiplying column vectors. -/
@[simp]
theorem quaternionUnitaryIsometry_apply (A : unitary (Matrix ι ι ℍ))
    (x : PiLp 2 fun _ : ι ↦ ℍ) :
    quaternionUnitaryIsometry ι A x = WithLp.toLp 2 (A.1 *ᵥ WithLp.ofLp x) :=
  (rfl)

/-- The action of a quaternionic unitary matrix on `ℍⁿ` commutes with quaternionic scalars acting
on the right: `A (x q) = (A x) q`. -/
theorem quaternionUnitaryIsometry_op_smul (A : unitary (Matrix ι ι ℍ))
    (x : PiLp 2 fun _ : ι ↦ ℍ) (q : ℍ) :
    quaternionUnitaryIsometry ι A (x <• q) = quaternionUnitaryIsometry ι A x <• q := by
  simp [Matrix.mulVec_smul]

/-- The action `(A, x) ↦ A x` of the compact symplectic group on `ℍⁿ` is jointly continuous. -/
theorem continuous_quaternionUnitaryIsometry_apply :
    Continuous fun p : unitary (Matrix ι ι ℍ) × PiLp 2 (fun _ : ι ↦ ℍ) ↦
      quaternionUnitaryIsometry ι p.1 p.2 := by
  simp only [quaternionUnitaryIsometry_apply]
  exact (PiLp.continuous_toLp 2 _).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

end Isometry

section Transitive

variable [DecidableEq ι]

/-- **A quaternionic Householder reflection.** If a unit vector `y` has a real `i`-th coordinate,
the reflection `H = 1 - (2 / |v|²) v vᴴ` in `v = eᵢ - y` is a unitary matrix with `H eᵢ = y`. -/
private theorem exists_mem_unitary_mulVec_single_eq {y : ι → ℍ}
    (hy : star y ⬝ᵥ y = 1) {i : ι} {r : ℝ} (hyi : y i = r) :
    ∃ H ∈ unitary (Matrix ι ι ℍ), H *ᵥ Pi.single i 1 = y := by
  set v : ι → ℍ := Pi.single i 1 - y with hv
  by_cases hv0 : v = 0
  · exact ⟨1, one_mem _, by rw [Matrix.one_mulVec]; exact sub_eq_zero.1 hv0⟩
  set s : ℝ := ∑ k, normSq (v k) with hs
  have hvv : star v ⬝ᵥ v = (s : ℍ) := star_dotProduct_self_quaternion v
  have hs0 : s ≠ 0 := by
    intro h
    refine hv0 (funext fun k ↦ normSq_eq_zero.1 ?_)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ normSq_nonneg).1 h k (Finset.mem_univ k)
  -- The Hermitian square of `v = eᵢ - y` is `2 (1 - yᵢ)`, and `vᴴ eᵢ = 1 - yᵢ`.
  have hvi : star v ⬝ᵥ Pi.single i 1 = ((1 - r : ℝ) : ℍ) := by
    simp [hv, dotProduct_single, hyi]
  have hs2 : s = 2 * (1 - r) := by
    have h : (s : ℍ) = 1 - (r : ℍ) - ((r : ℍ) - 1) := by
      rw [← hvv, hv, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hy]
      simp only [← Pi.single_star, star_one, single_dotProduct, one_mul, Pi.single_eq_same,
        dotProduct_single, mul_one, Pi.star_apply, hyi, star_coe]
    have h' := congrArg QuaternionAlgebra.re h
    simp only [re_coe, re_sub, re_one] at h'
    linarith
  set P : Matrix ι ι ℍ := Matrix.vecMulVec v (star v) with hP
  set c : ℝ := 2 / s with hc
  have hPP : P * P = s • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec, hvv, ← Matrix.vecMulVec_smul]
    congr 1
    funext k
    exact coe_mul_eq_smul _ _
  have hcs : c * c * s = 2 * c := by
    rw [hc]
    field_simp
  have hPstar : star P = P := by
    rw [hP, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec, star_star]
  set H : Matrix ι ι ℍ := 1 - c • P with hH
  have hHstar : star H = H := by
    rw [hH, star_sub, star_one]
    congr 1
    refine Matrix.ext fun k l ↦ ?_
    rw [Matrix.star_apply, Matrix.smul_apply, Quaternion.star_smul, ← Matrix.star_apply, hPstar,
      Matrix.smul_apply]
  have hHH : H * H = 1 := by
    calc H * H = 1 - (2 * c - c * c * s) • P := by
          rw [hH, sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one, smul_mul_smul_comm, hPP,
            smul_smul]
          module
      _ = 1 := by rw [hcs, sub_self, zero_smul, sub_zero]
  refine ⟨H, ⟨by rw [hHstar, hHH], by rw [hHstar, hHH]⟩, ?_⟩
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP,
    Matrix.vecMulVec_mulVec, hvi]
  have hv' : op ((1 - r : ℝ) : ℍ) • v = (1 - r) • v := by
    funext k
    exact mul_coe_eq_smul _ _
  rw [hv', smul_smul, hc, hs2, show 2 / (2 * (1 - r)) * (1 - r) = 1 by
    have : 1 - r ≠ 0 := fun h ↦ hs0 (by rw [hs2, h, mul_zero])
    field_simp, one_smul, hv, sub_sub_cancel]

/-- **The compact symplectic group acts transitively on the unit sphere of `ℍⁿ`**: every unit
vector `x` is the image `A eᵢ` of the basis vector `eᵢ` under a quaternionic unitary matrix
`A`. -/
theorem exists_quaternionUnitaryIsometry_apply_single_eq (i : ι)
    {x : PiLp 2 fun _ : ι ↦ ℍ} (hx : ‖x‖ = 1) :
    ∃ A, quaternionUnitaryIsometry ι A (WithLp.toLp 2 (Pi.single i 1)) = x := by
  -- A unit quaternion `u` making the `i`-th coordinate of `x u` real.
  obtain ⟨u, hu, r, hr⟩ : ∃ u : ℍ, normSq u = 1 ∧ ∃ r : ℝ, x i * u = r := by
    by_cases h : x i = 0
    · exact ⟨1, by simp, 0, by simp [h]⟩
    have hn : ‖x i‖ ≠ 0 := norm_ne_zero_iff.2 h
    refine ⟨(‖x i‖⁻¹ : ℝ) • star (x i), ?_, ‖x i‖⁻¹ * normSq (x i), ?_⟩
    · rw [normSq_smul, normSq_star, normSq_eq_norm_mul_self]
      field_simp
    · rw [mul_smul_comm, self_mul_star, ← coe_mul_eq_smul, coe_mul]
  have hnu : ‖u‖ = 1 := by
    rw [normSq_eq_norm_mul_self] at hu
    nlinarith [norm_nonneg u]
  have hy : star (WithLp.ofLp (x <• u)) ⬝ᵥ WithLp.ofLp (x <• u) = 1 := by
    rw [star_dotProduct_self_ofLp, norm_smul, norm_op, hnu, hx]
    simp
  obtain ⟨H, hH, hHy⟩ := exists_mem_unitary_mulVec_single_eq hy (i := i) hr
  -- The diagonal unitary matrix with `ū` in position `i` corrects the phase.
  set d : ι → ℍ := Function.update 1 i (star u) with hd
  have hdd (k : ι) : star (d k) * d k = 1 ∧ d k * star (d k) = 1 := by
    rcases eq_or_ne k i with rfl | hk
    · simp [hd, self_mul_star, star_mul_self, hu]
    · simp [hd, Function.update_of_ne hk]
  have hDu : Matrix.diagonal d ∈ unitary (Matrix ι ι ℍ) := by
    refine ⟨?_, ?_⟩ <;>
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] <;>
      congr 1 <;> funext k
    · exact (hdd k).1
    · exact (hdd k).2
  refine ⟨⟨H * Matrix.diagonal d, mul_mem hH hDu⟩, ?_⟩
  rw [quaternionUnitaryIsometry_apply, ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single,
    Matrix.mulVec_single, ← Matrix.mulVec_single_one, hHy]
  rw [hd, Function.update_self, mul_one, WithLp.ofLp_smul, smul_smul, ← op_mul, self_mul_star, hu]
  simp

end Transitive

end TauCeti
