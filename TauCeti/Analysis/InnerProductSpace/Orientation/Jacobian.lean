/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.InnerProductSpace.Orientation
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The oriented Jacobian of a linear map

For oriented finite-dimensional real inner product spaces `V`, `W` of the same dimension `n`
and a linear map `A : V →ₗ[ℝ] W`, the oriented Jacobian `oV.orientedJacobian oW A` is the real
number `J(A)` with

`oW.volumeForm (A ∘ v) = J(A) * oV.volumeForm v`

for every family `v : Fin n → V` (`Orientation.volumeForm_apply_comp`,
`Orientation.orientedJacobian_eq_iff`). It is the signed volume distortion of `A`: on a
positively oriented orthonormal basis `b` of `V` it is `oW.volumeForm (A ∘ b)`
(`Orientation.orientedJacobian_eq_volumeForm`).

The main results are:

* `Orientation.orientedJacobian_comp`: multiplicativity, `J(B ∘ A) = J(B) J(A)`;
* `Orientation.orientedJacobian_self`: for one orientation on both sides, `J(A) = det A`;
* `Orientation.orientedJacobian_neg_left`, `Orientation.orientedJacobian_neg_right`: reversing
  exactly one orientation negates `J(A)`;
* `Orientation.abs_orientedJacobian`: `|J(A)|` is Mathlib's unsigned volume factor
  `LinearMap.normDet A`;
* `Orientation.abs_orientedJacobian_le`: Hadamard's inequality `|J(A)| ≤ ‖A‖ ^ n`;
* `Orientation.orientedJacobian_ne_zero_iff`, `Orientation.orientedJacobian_pos_iff`: `J(A) ≠ 0`
  exactly when `A` is invertible, and `J(A) > 0` exactly when moreover `A` carries `oV` to `oW`;
* `Orientation.orientedJacobian_positiveOrientation`: in dimension `0`, where the volume forms
  are the constants `±1`, `J(A) = 1` for the positive orientations on both sides.

This is the linear algebra behind the Jacobian `J_f(x) = J(Df(x))` of a map between oriented
Riemannian manifolds of the same dimension, taken for the tangent inner products and tangent
orientations; Hadamard's inequality bounds it by the `n`-th power of the operator norm of the
differential.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 15 (volume forms and
  orientations).
-/

public section

noncomputable section

open Module

namespace Orientation

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]

/-- The oriented Jacobian `J(A)` of a linear map `A : V →ₗ[ℝ] W` between oriented real inner
product spaces of the same finite dimension `n`: the unique real number with
`oW.volumeForm (A ∘ v) = J(A) * oV.volumeForm v` for every family `v`
(`Orientation.orientedJacobian_eq_iff`). It is computed here on a fixed basis of `V`; any basis
gives the same value (`Orientation.orientedJacobian_eq_div`). -/
def orientedJacobian (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : ℝ :=
  oW.volumeForm (A ∘ finBasisOfFinrankEq ℝ V Fact.out) /
    oV.volumeForm (finBasisOfFinrankEq ℝ V Fact.out)

omit [FiniteDimensional ℝ V] in
/-- The volume form of `V` does not vanish on a basis of `V`. -/
private theorem volumeForm_basis_ne_zero (oV : Orientation ℝ V (Fin n))
    (b : Basis (Fin n) ℝ V) : oV.volumeForm b ≠ 0 :=
  volumeForm_apply_ne_zero_iff.2 b.linearIndependent

/-- The pullback of the volume form of `W` along `A` is `J(A)` times the volume form of `V`. -/
theorem volumeForm_compLinearMap (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) :
    oW.volumeForm.compLinearMap A = oV.orientedJacobian oW A • oV.volumeForm := by
  set b := finBasisOfFinrankEq ℝ V (Fact.out : finrank ℝ V = n)
  conv_lhs => rw [(oW.volumeForm.compLinearMap A).eq_smul_basis_det b]
  conv_rhs => rw [oV.volumeForm.eq_smul_basis_det b]
  rw [smul_smul, orientedJacobian, div_mul_cancel₀ _ (oV.volumeForm_basis_ne_zero b),
    AlternatingMap.compLinearMap_apply, Function.comp_def]

/-- **Defining property of the oriented Jacobian**:
`oW.volumeForm (A ∘ v) = J(A) * oV.volumeForm v` for every family `v`. -/
theorem volumeForm_apply_comp (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) (v : Fin n → V) :
    oW.volumeForm (A ∘ v) = oV.orientedJacobian oW A * oV.volumeForm v :=
  congr($(oV.volumeForm_compLinearMap oW A) v)

/-- The oriented Jacobian is the unique real number `c` with
`oW.volumeForm (A ∘ v) = c * oV.volumeForm v` for every family `v`. -/
theorem orientedJacobian_eq_iff {oV : Orientation ℝ V (Fin n)} {oW : Orientation ℝ W (Fin n)}
    {A : V →ₗ[ℝ] W} {c : ℝ} :
    oV.orientedJacobian oW A = c ↔
      ∀ v : Fin n → V, oW.volumeForm (A ∘ v) = c * oV.volumeForm v := by
  refine ⟨fun h v ↦ h ▸ oV.volumeForm_apply_comp oW A v, fun h ↦ ?_⟩
  set b := finBasisOfFinrankEq ℝ V (Fact.out : finrank ℝ V = n)
  rw [orientedJacobian, h b, mul_div_cancel_right₀ _ (oV.volumeForm_basis_ne_zero b)]

/-- The oriented Jacobian can be computed on any basis `b` of `V`. -/
theorem orientedJacobian_eq_div (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) (b : Basis (Fin n) ℝ V) :
    oV.orientedJacobian oW A = oW.volumeForm (A ∘ b) / oV.volumeForm b := by
  rw [oV.volumeForm_apply_comp oW A b, mul_div_cancel_right₀ _ (oV.volumeForm_basis_ne_zero b)]

/-- On a positively oriented orthonormal basis `b` of `V`, the oriented Jacobian is the volume
of the image family: `J(A) = oW.volumeForm (A ∘ b)`. -/
theorem orientedJacobian_eq_volumeForm (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = oV) :
    oV.orientedJacobian oW A = oW.volumeForm (A ∘ b) := by
  rw [oV.orientedJacobian_eq_div oW A b.toBasis, oV.volumeForm_robust b hb, Basis.det_self,
    div_one, OrthonormalBasis.coe_toBasis]

/-- **Multiplicativity of the oriented Jacobian**: `J(B ∘ A) = J(B) J(A)`. -/
theorem orientedJacobian_comp (oU : Orientation ℝ U (Fin n)) (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : U →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) :
    oU.orientedJacobian oW (B ∘ₗ A) = oV.orientedJacobian oW B * oU.orientedJacobian oV A := by
  refine orientedJacobian_eq_iff.2 fun v ↦ ?_
  rw [LinearMap.coe_comp, Function.comp_assoc, oV.volumeForm_apply_comp oW B,
    oU.volumeForm_apply_comp oV A, mul_assoc]

/-- For one orientation on both sides, the oriented Jacobian is the determinant. -/
@[simp]
theorem orientedJacobian_self (oV : Orientation ℝ V (Fin n)) (A : V →ₗ[ℝ] V) :
    oV.orientedJacobian oV A = LinearMap.det A := by
  refine orientedJacobian_eq_iff.2 fun v ↦ ?_
  exact congr($(oV.volumeForm.compLinearMap_eq_det_smul (finBasisOfFinrankEq ℝ V Fact.out) A) v)

/-- The oriented Jacobian of the identity is `1`. -/
theorem orientedJacobian_id (oV : Orientation ℝ V (Fin n)) :
    oV.orientedJacobian oV LinearMap.id = 1 := by
  simp

/-- Reversing the orientation of the source negates the oriented Jacobian. -/
@[simp]
theorem orientedJacobian_neg_left (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : (-oV).orientedJacobian oW A = -oV.orientedJacobian oW A := by
  refine orientedJacobian_eq_iff.2 fun v ↦ ?_
  rw [volumeForm_neg_orientation, neg_apply, neg_mul_neg,
    oV.volumeForm_apply_comp oW A]

/-- Reversing the orientation of the target negates the oriented Jacobian. -/
@[simp]
theorem orientedJacobian_neg_right (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →ₗ[ℝ] W) : oV.orientedJacobian (-oW) A = -oV.orientedJacobian oW A := by
  refine orientedJacobian_eq_iff.2 fun v ↦ ?_
  rw [volumeForm_neg_orientation, neg_apply, oV.volumeForm_apply_comp oW A, neg_mul]

/-- The absolute value of the oriented Jacobian is the unsigned volume factor
`LinearMap.normDet`. -/
theorem abs_orientedJacobian [FiniteDimensional ℝ W] (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (A : V →ₗ[ℝ] W) :
    |oV.orientedJacobian oW A| = A.normDet := by
  let bV : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  let bW : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr Fact.out)
  have hmat : bW.toBasis.toMatrix (A ∘ bV) = LinearMap.toMatrix bV.toBasis bW.toBasis A := by
    ext i j
    simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  rw [oV.orientedJacobian_eq_div oW A bV.toBasis, abs_div, OrthonormalBasis.coe_toBasis,
    oV.abs_volumeForm_apply_of_orthonormal bV, div_one, oW.volumeForm_robust' bW,
    Basis.det_apply, hmat, A.normDet_eq_norm_det_toMatrix bV bW, Real.norm_eq_abs]

/-- **Hadamard's inequality** for the oriented Jacobian: `|J(A)| ≤ ‖A‖ ^ n`. -/
theorem abs_orientedJacobian_le (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (A : V →L[ℝ] W) : |oV.orientedJacobian oW (A : V →ₗ[ℝ] W)| ≤ ‖A‖ ^ n := by
  let b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  rw [oV.orientedJacobian_eq_div oW A b.toBasis, abs_div, OrthonormalBasis.coe_toBasis,
    oV.abs_volumeForm_apply_of_orthonormal b, div_one]
  calc |oW.volumeForm ((A : V →ₗ[ℝ] W) ∘ b)| ≤ ∏ i : Fin n, ‖A (b i)‖ :=
        oW.abs_volumeForm_apply_le _
    _ ≤ ∏ _i : Fin n, ‖A‖ := by
        gcongr with i
        simpa [b.orthonormal.1 i] using A.le_opNorm (b i)
    _ = ‖A‖ ^ n := by simp

/-- The oriented Jacobian of `A` is nonzero exactly when `A` is invertible. -/
theorem orientedJacobian_ne_zero_iff [FiniteDimensional ℝ W] {oV : Orientation ℝ V (Fin n)}
    {oW : Orientation ℝ W (Fin n)} {A : V →ₗ[ℝ] W} :
    oV.orientedJacobian oW A ≠ 0 ↔ Function.Bijective A := by
  have hrank : finrank ℝ V = finrank ℝ W :=
    (Fact.out : finrank ℝ V = n).trans (Fact.out : finrank ℝ W = n).symm
  rw [← abs_ne_zero, abs_orientedJacobian, Ne, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    not_not, LinearMap.ker_eq_bot, Function.Bijective,
    ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank, and_self]

/-- A linear equivalence carries the orientation `oV` to `oW` exactly when its oriented Jacobian
is positive. -/
theorem map_eq_iff_orientedJacobian_pos [FiniteDimensional ℝ W] (oV : Orientation ℝ V (Fin n))
    (oW : Orientation ℝ W (Fin n)) (e : V ≃ₗ[ℝ] W) :
    Orientation.map (Fin n) e oV = oW ↔ 0 < oV.orientedJacobian oW (e : V →ₗ[ℝ] W) := by
  set b := finBasisOfFinrankEq ℝ V (Fact.out : finrank ℝ V = n)
  have hcard : Fintype.card (Fin n) = finrank ℝ W := by simp [Fact.out (p := finrank ℝ W = n)]
  have hJ : oV.orientedJacobian oW (e : V →ₗ[ℝ] W) ≠ 0 :=
    orientedJacobian_ne_zero_iff.2 (by simpa using e.bijective)
  -- For the orientation of `b`, the sign of `J(e)` is the sign of `oW.volumeForm (e ∘ b)`.
  have hb : Orientation.map (Fin n) e b.orientation = oW ↔
      0 < b.orientation.orientedJacobian oW (e : V →ₗ[ℝ] W) := by
    rw [← b.orientation_map e, ← volumeForm_apply_pos_iff,
      b.orientation.orientedJacobian_eq_div oW e b,
      div_pos_iff_of_pos_right (volumeForm_apply_pos_iff.2 rfl), Basis.coe_map,
      LinearEquiv.coe_coe]
  rcases eq_or_ne oV b.orientation with rfl | h
  · exact hb
  · rw [(b.orientation_ne_iff_eq_neg oV).1 h, orientedJacobian_neg_left] at hJ ⊢
    rw [Orientation.map_neg, neg_pos, eq_comm, ← ne_iff_eq_neg _ _ hcard, ne_comm, Ne, hb,
      not_lt]
    exact ⟨fun h ↦ h.lt_of_ne (neg_ne_zero.1 hJ), le_of_lt⟩

/-- The oriented Jacobian of `A` is positive exactly when `A` is invertible and carries the
orientation `oV` to `oW`. -/
theorem orientedJacobian_pos_iff [FiniteDimensional ℝ W] {oV : Orientation ℝ V (Fin n)}
    {oW : Orientation ℝ W (Fin n)} {A : V →ₗ[ℝ] W} :
    0 < oV.orientedJacobian oW A ↔
      ∃ e : V ≃ₗ[ℝ] W, (e : V →ₗ[ℝ] W) = A ∧ Orientation.map (Fin n) e oV = oW := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · let e := LinearEquiv.ofBijective A (orientedJacobian_ne_zero_iff.1 h.ne')
    exact ⟨e, rfl, (oV.map_eq_iff_orientedJacobian_pos oW e).2 h⟩
  · rintro ⟨e, rfl, he⟩
    exact (oV.map_eq_iff_orientedJacobian_pos oW e).1 he

end Orientation

namespace Orientation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fact (finrank ℝ V = 0)]
  [Fact (finrank ℝ W = 0)]

/-- In dimension `0`, the oriented Jacobian between the positive orientations is `1`. Together
with `Orientation.orientedJacobian_neg_left` and `Orientation.orientedJacobian_neg_right` this
gives `J(A) = 1` when the two orientations agree and `-1` otherwise. -/
@[simp]
theorem orientedJacobian_positiveOrientation (A : V →ₗ[ℝ] W) :
    (positiveOrientation : Orientation ℝ V (Fin 0)).orientedJacobian positiveOrientation A = 1 :=
  orientedJacobian_eq_iff.2 fun v ↦ by simp

end Orientation
