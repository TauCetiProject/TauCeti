/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Geometry.Sphere.LinearIsometry
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Quaternion.Basic
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Householder

/-!
# The compact symplectic group `Sp(n)` of quaternionic unitary matrices

The compact symplectic group `Sp(n)` is the group `unitary (Matrix ι ι ℍ)` of quaternionic
matrices `A` with `Aᴴ A = A Aᴴ = 1`. This file shows that it is a compact group, and that it acts
by real linear isometries on the quaternionic coordinate space `ℍⁿ = PiLp 2 (fun _ : ι ↦ ℍ)`,
continuously and transitively by isometries on its unit sphere `S⁴ⁿ⁻¹`, commuting with right
multiplication by unit quaternions.

Quaternionic matrices act on column vectors on the left, `x ↦ A x`, and so commute with
quaternionic scalars acting on the right, `A (x q) = (A x) q`
(`TauCeti.quaternionUnitaryIsometry_op_smul`). The norm of `ℍⁿ` is recovered from the
quaternionic Hermitian product `xᴴ x = Σₖ star xₖ * xₖ`, a real number
(`TauCeti.star_dotProduct_self_ofLp`), so a unitary matrix, which preserves this product,
preserves the norm.

A unitary matrix has unit columns, so all its entries have norm at most one
(`TauCeti.norm_apply_le_one_of_mem_unitary_quaternion`); being closed, the unitary group is
compact.

Transitivity on the sphere uses quaternionic Householder reflections
(`TauCeti.quaternionHouseholder`). If a unit vector `y` has real `i`-th coordinate `r`, then
`v = eᵢ - y` has Hermitian square `|v|² = 2 (1 - r)` and
`H = 1 - (1 - r)⁻¹ v vᴴ` is a Hermitian involution (degenerating to `1` when `y = eᵢ`), hence
unitary (`TauCeti.quaternionHouseholder_mem_unitary`), and satisfies `H eᵢ = y`
(`TauCeti.quaternionHouseholder_mulVec_single_one`). A general unit vector `x` is brought to this
form by a unit quaternion `u` on the right, and the diagonal unitary matrix with `ū` in position
`i` then corrects the phase.

## Main declarations

* `TauCeti.isCompact_unitary_quaternion`: `Sp(n)` is compact.
* `TauCeti.quaternionUnitaryIsometry`: the action of `Sp(n)` on `ℍⁿ` by real linear isometries,
  `A ↦ (x ↦ A x)`.
* `TauCeti.quaternionUnitaryIsometry_op_smul`: the action commutes with right multiplication by
  quaternions.
* `TauCeti.quaternionHouseholder`: the quaternionic Householder reflection matrix sending `eᵢ` to a
  unit vector `y` with real `i`-th coordinate, together with unitarity
  (`TauCeti.quaternionHouseholder_mem_unitary`), action on `eᵢ`
  (`TauCeti.quaternionHouseholder_mulVec_single_one`), and continuity
  (`TauCeti.continuousOn_quaternionHouseholder`).
* `TauCeti.exists_quaternionUnitaryIsometry_apply_single_eq`: `Sp(n)` acts transitively on the
  unit sphere: every unit vector is the image of the basis vector `eᵢ`.
* `TauCeti.instMulActionUnitaryMatrixQuaternionSphere`,
  `TauCeti.instSMulCommClassUnitaryMatrixQuaternionSphere`,
  `TauCeti.instIsIsometricSMulUnitaryMatrixQuaternionSphere`,
  `TauCeti.instContinuousSMulUnitaryMatrixQuaternionSphere`,
  `TauCeti.instIsPretransitiveUnitaryMatrixQuaternionSphere`: the continuous, isometric, transitive
  left action of `Sp(ι)` on the unit sphere of `ℍⁿ`, commuting with right multiplication by unit
  quaternions.

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
    { mulVecLinearMap A.val with
      invFun := mulVecLinearMap (star A).val
      left_inv x := by
        simp [mulVecLinearMap, Matrix.mulVec_mulVec, A.property.1]
      right_inv x := by
        simp [mulVecLinearMap, Matrix.mulVec_mulVec, A.property.2]
      norm_map' x := by
        -- `A` preserves the quaternionic Hermitian square, which is the squared norm.
        have h : star (A.val *ᵥ WithLp.ofLp x) ⬝ᵥ (A.val *ᵥ WithLp.ofLp x) =
            star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x := by
          rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
            ← Matrix.star_eq_conjTranspose, A.property.1, Matrix.vecMul_one]
        rw [← WithLp.ofLp_toLp 2 (A.val *ᵥ WithLp.ofLp x),
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
    quaternionUnitaryIsometry ι A x = WithLp.toLp 2 (A.val *ᵥ WithLp.ofLp x) :=
  (rfl)

/-- The inverse of the action of a quaternionic unitary matrix `A` on `ℍⁿ` multiplies column
vectors by the conjugate transpose `star A`. -/
@[simp]
theorem quaternionUnitaryIsometry_symm_apply (A : unitary (Matrix ι ι ℍ))
    (x : PiLp 2 fun _ : ι ↦ ℍ) :
    (quaternionUnitaryIsometry ι A).symm x = WithLp.toLp 2 ((star A).val *ᵥ WithLp.ofLp x) :=
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
    ((continuous_subtypeVal.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

end Isometry

section Householder

variable [DecidableEq ι]

omit [Fintype ι] in
/-- The **quaternionic Householder matrix** `1 - (1 - (y i).re)⁻¹ • (eᵢ - y) (eᵢ - y)ᴴ` associated
with a vector `y : ι → ℍ` and index `i`. When `y` is a unit vector whose `i`-th coordinate is real,
this is a unitary matrix sending `eᵢ` to `y` (degenerating to `1` when `y = eᵢ`). -/
def quaternionHouseholder (i : ι) (y : ι → ℍ) : Matrix ι ι ℍ :=
  1 - (1 - (y i).re)⁻¹ • Matrix.vecMulVec (Pi.single i 1 - y) (star (Pi.single i 1 - y))

omit [Fintype ι] in
/-- Explicit formula for `TauCeti.quaternionHouseholder`. -/
theorem quaternionHouseholder_def (i : ι) (y : ι → ℍ) :
    quaternionHouseholder i y =
      1 - (1 - (y i).re)⁻¹ • Matrix.vecMulVec (Pi.single i 1 - y) (star (Pi.single i 1 - y)) :=
  (rfl)

omit [Fintype ι] in
/-- The quaternionic Householder matrix for `eᵢ` itself is the identity matrix. -/
@[simp]
theorem quaternionHouseholder_single_one (i : ι) :
    quaternionHouseholder i (Pi.single i 1) = 1 := by
  simp [quaternionHouseholder_def]

omit [Fintype ι] in
/-- The quaternionic Householder matrix for `-eᵢ` is the diagonal reflection negating coordinate
`i`. -/
theorem quaternionHouseholder_neg_single_one (i : ι) :
    quaternionHouseholder i (-Pi.single i 1) = Matrix.diagonal (Function.update 1 i (-1)) := by
  have hsub : (Pi.single i 1 - (-Pi.single i 1) : ι → ℍ) = Pi.single i ((2 : ℝ) : ℍ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      ext <;> simp
      norm_num
    · simp [hj]
  rw [quaternionHouseholder_def, Pi.neg_apply, Pi.single_eq_same, re_neg, re_one, sub_neg_eq_add,
    one_add_one_eq_two, hsub]
  refine Matrix.ext fun j k ↦ ?_
  by_cases hj : j = i
  · subst hj
    by_cases hk : k = j
    · subst hk
      ext <;> simp [Matrix.vecMulVec_apply]
      norm_num
    · simp [Matrix.vecMulVec_apply, hk, Ne.symm hk]
  · simp [Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.diagonal_apply, hj]

omit [Fintype ι] in
/-- The quaternionic Householder matrix `quaternionHouseholder i (y x)` depends continuously on `x`
on any set `s` where `y` is continuous and `(y x i).re ≠ 1`. -/
theorem continuousOn_quaternionHouseholder {X : Type*} [TopologicalSpace X] {s : Set X}
    {i : ι} {y : X → ι → ℍ} (hy : ContinuousOn y s) (hre : ∀ x ∈ s, (y x i).re ≠ 1) :
    ContinuousOn (fun x ↦ quaternionHouseholder i (y x)) s := by
  have hre_cont : ContinuousOn (fun x ↦ (y x i).re) s :=
    Quaternion.continuous_re.comp_continuousOn ((continuous_apply i).comp_continuousOn hy)
  have hc : ContinuousOn (fun x ↦ (1 - (y x i).re)⁻¹) s :=
    (continuousOn_const.sub hre_cont).inv₀ fun x hx ↦ sub_ne_zero.2 (hre x hx).symm
  have hv (j : ι) : ContinuousOn (fun x ↦ ((Pi.single i 1 : ι → ℍ) - y x) j) s :=
    (continuousOn_const.sub ((continuous_apply j).comp_continuousOn hy)).congr fun x _ ↦
      (Pi.sub_apply (Pi.single i 1 : ι → ℍ) (y x) j).symm
  refine continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ ?_
  simp only [quaternionHouseholder_def, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply]
  exact continuousOn_const.sub (hc.smul ((hv j).mul (hv k).star))

/-- For a unit vector `y` with real `i`-th coordinate `r`, the vector `eᵢ - y` has Hermitian
square `2 (1 - r)`. -/
private theorem star_dotProduct_single_sub {i : ι} {y : ι → ℍ}
    (hy : star y ⬝ᵥ y = 1) {r : ℝ} (hyi : y i = r) :
    star (Pi.single i 1 - y) ⬝ᵥ (Pi.single i 1 - y) = ((2 * (1 - r) : ℝ) : ℍ) := by
  have h : star (Pi.single i 1 - y) ⬝ᵥ (Pi.single i 1 - y) =
      (1 : ℍ) - (r : ℍ) - ((r : ℍ) - 1) := by
    simp [sub_dotProduct, dotProduct_sub, hy, hyi]
  rw [h]
  ext <;> simp
  ring

/-- **The quaternionic Householder matrix is unitary.** If `y` is a unit vector whose `i`-th
coordinate is real, then `quaternionHouseholder i y` belongs to `unitary (Matrix ι ι ℍ)`. -/
theorem quaternionHouseholder_mem_unitary {i : ι} {y : ι → ℍ}
    (hy : star y ⬝ᵥ y = 1) {r : ℝ} (hyi : y i = r) :
    quaternionHouseholder i y ∈ unitary (Matrix ι ι ℍ) := by
  have hre : (y i).re = r := by rw [hyi, re_coe]
  have hcs : (1 - r)⁻¹ * (1 - r)⁻¹ * (2 * (1 - r)) = 2 * (1 - r)⁻¹ := by
    by_cases hr : 1 - r = 0
    · simp [hr]
    · field_simp
  rw [quaternionHouseholder_def, hre]
  exact Matrix.one_sub_smul_vecMulVec_mem_unitary
    (by rw [star_dotProduct_single_sub hy hyi, Quaternion.algebraMap_def]) hcs

/-- **Action of the quaternionic Householder matrix on `eᵢ`.** If `y` is a unit vector whose `i`-th
coordinate is real, then `quaternionHouseholder i y *ᵥ Pi.single i 1 = y`. -/
theorem quaternionHouseholder_mulVec_single_one {i : ι} {y : ι → ℍ}
    (hy : star y ⬝ᵥ y = 1) {r : ℝ} (hyi : y i = r) :
    quaternionHouseholder i y *ᵥ Pi.single i 1 = y := by
  have hre : (y i).re = r := by rw [hyi, re_coe]
  by_cases hr : 1 - r = 0
  · have hvv : star (Pi.single i 1 - y) ⬝ᵥ (Pi.single i 1 - y) = 0 := by
      rw [star_dotProduct_single_sub hy hyi, hr, mul_zero, coe_zero]
    rw [star_dotProduct_self_quaternion, ← coe_zero, Quaternion.coe_inj] at hvv
    have hv0 : Pi.single i 1 - y = 0 := funext fun k ↦ normSq_eq_zero.1 <|
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ normSq_nonneg).1 hvv k (Finset.mem_univ k)
    rw [quaternionHouseholder_def, hre, hr, inv_zero, zero_smul, sub_zero, Matrix.one_mulVec]
    exact sub_eq_zero.1 hv0
  · set v : ι → ℍ := Pi.single i 1 - y
    have hvi : star v ⬝ᵥ Pi.single i 1 = ((1 - r : ℝ) : ℍ) := by
      simp [v, dotProduct_single, hyi]
    have hv' : op ((1 - r : ℝ) : ℍ) • v = (1 - r) • v := by
      funext k
      rw [Pi.smul_apply, Pi.smul_apply, op_smul_eq_mul, mul_coe_eq_smul]
    rw [quaternionHouseholder_def, hre, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, hvi, hv', smul_smul, inv_mul_cancel₀ hr, one_smul]
    simp [v]

end Householder

section Transitive

variable [DecidableEq ι]

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
    · exact ⟨(‖x i‖⁻¹ : ℝ) • star (x i), Quaternion.normSq_inv_norm_smul_star h, ‖x i‖,
        Quaternion.mul_inv_norm_smul_star (x i)⟩
  have hnu : ‖u‖ = 1 := by
    rw [normSq_eq_norm_mul_self] at hu
    nlinarith [norm_nonneg u]
  have hy : star (WithLp.ofLp (x <• u)) ⬝ᵥ WithLp.ofLp (x <• u) = 1 := by
    rw [star_dotProduct_self_ofLp, norm_smul, norm_op, hnu, hx]
    simp
  have hyi : WithLp.ofLp (x <• u) i = r := by
    rw [WithLp.ofLp_smul, Pi.smul_apply, op_smul_eq_mul, hr]
  have hH : quaternionHouseholder i (WithLp.ofLp (x <• u)) ∈ unitary (Matrix ι ι ℍ) :=
    quaternionHouseholder_mem_unitary hy hyi
  have hHy : quaternionHouseholder i (WithLp.ofLp (x <• u)) *ᵥ Pi.single i 1 =
      WithLp.ofLp (x <• u) :=
    quaternionHouseholder_mulVec_single_one hy hyi
  -- The diagonal unitary matrix with `ū` in position `i` corrects the phase.
  have hDu : Matrix.diagonal (Function.update 1 i (star u)) ∈ unitary (Matrix ι ι ℍ) :=
    Matrix.diagonal_update_one_mem_unitary_iff.2 <| Unitary.star_mem
      ⟨by rw [star_mul_self, hu, coe_one], by rw [self_mul_star, hu, coe_one]⟩
  refine ⟨⟨quaternionHouseholder i (WithLp.ofLp (x <• u)) *
      Matrix.diagonal (Function.update 1 i (star u)), mul_mem hH hDu⟩, ?_⟩
  have hsingle : Pi.single i (star u) = op (star u) • (Pi.single i 1 : ι → ℍ) := by
    rw [← Pi.single_smul', op_smul_eq_mul, one_mul]
  rw [quaternionUnitaryIsometry_apply, Subtype.coe_mk, WithLp.ofLp_toLp, ← Matrix.mulVec_mulVec,
    Matrix.diagonal_mulVec_single, Function.update_self, mul_one, hsingle, Matrix.mulVec_smul, hHy]
  simp [smul_smul, -MulOpposite.op_star, ← op_mul, self_mul_star, hu]

end Transitive

section SphereAction

variable [DecidableEq ι]

/-- The compact symplectic group acts on the unit sphere of `ℍⁿ = PiLp 2 (fun _ : ι ↦ ℍ)` by
left multiplication `A • x = A x`. -/
instance instMulActionUnitaryMatrixQuaternionSphere :
    MulAction (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :=
  .compHom _ (quaternionUnitaryIsometry ι)

/-- The action of a quaternionic unitary matrix on the unit sphere of `ℍⁿ` is the restriction of
`TauCeti.quaternionUnitaryIsometry`. -/
theorem quaternionUnitary_smul_sphere_def (A : unitary (Matrix ι ι ℍ))
    (x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :
    A • x = quaternionUnitaryIsometry ι A • x :=
  MulAction.compHom_smul_def (quaternionUnitaryIsometry ι) A x

/-- Coercing `A • x` from the unit sphere to `ℍⁿ` gives `quaternionUnitaryIsometry ι A x`. -/
@[simp]
theorem coe_quaternionUnitary_smul_sphere (A : unitary (Matrix ι ι ℍ))
    (x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :
    ((A • x : sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) : PiLp 2 fun _ : ι ↦ ℍ) =
      quaternionUnitaryIsometry ι A x := by
  rw [quaternionUnitary_smul_sphere_def, LinearIsometryEquiv.coe_smul_unitSphere]

/-- The action of the compact symplectic group on the unit sphere of `ℍⁿ` commutes with right
multiplication by unit quaternions. -/
instance instSMulCommClassUnitaryMatrixQuaternionSphere :
    SMulCommClass (unitary (Matrix ι ι ℍ)) (sphere (0 : ℍ) 1)ᵐᵒᵖ
      (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) where
  smul_comm A c x := Subtype.ext <| by
    simp only [coe_quaternionUnitary_smul_sphere, Sphere.coe_op_sphere_smul,
      quaternionUnitaryIsometry_op_smul]

/-- The compact symplectic group acts on the unit sphere of `ℍⁿ` by isometries. -/
instance instIsIsometricSMulUnitaryMatrixQuaternionSphere :
    IsIsometricSMul (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) :=
  ⟨fun A x y ↦ by
    simp only [quaternionUnitary_smul_sphere_def]
    exact isometry_smul _ (quaternionUnitaryIsometry ι A) x y⟩

/-- The action of the compact symplectic group on the unit sphere of `ℍⁿ` is jointly
continuous. -/
instance instContinuousSMulUnitaryMatrixQuaternionSphere :
    ContinuousSMul (unitary (Matrix ι ι ℍ)) (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) where
  continuous_smul := continuous_induced_rng.2 <|
    (continuous_quaternionUnitaryIsometry_apply.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).congr fun p ↦
        (coe_quaternionUnitary_smul_sphere p.1 p.2).symm

/-- The compact symplectic group `Sp(ι)` acts transitively on the unit sphere of `ℍⁿ` (vacuously
when `ι` is empty, since the unit sphere is then empty). -/
instance instIsPretransitiveUnitaryMatrixQuaternionSphere :
    MulAction.IsPretransitive (unitary (Matrix ι ι ℍ))
      (sphere (0 : PiLp 2 fun _ : ι ↦ ℍ) 1) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · refine ⟨fun x ↦ False.elim ?_⟩
    have hx : (x : PiLp 2 fun _ : ι ↦ ℍ) = 0 := Subsingleton.elim _ _
    simpa [hx] using mem_sphere_zero_iff_norm.1 x.property
  · refine .of_orbit (x₀ := ⟨WithLp.toLp 2 (Pi.single i 1), by simp⟩) fun x ↦ ?_
    obtain ⟨A, hA⟩ := exists_quaternionUnitaryIsometry_apply_single_eq i
      (mem_sphere_zero_iff_norm.1 x.property)
    exact ⟨A, Subtype.ext ((coe_quaternionUnitary_smul_sphere A _).trans hA)⟩

end SphereAction

end TauCeti
