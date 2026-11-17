/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Geometry.Lie.Subgroup.Symplectic
public import TauCeti.LinearAlgebra.Matrix.Signature
import TauCeti.Analysis.Matrix.Exponential.Spectrum
import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The signature axiom of the Conley–Zehnder index

This file proves the signature axiom of the Conley–Zehnder index
`TauCeti.GLSymplectic.conleyZehnderIndex` of paths of symplectic matrices, in the convention
`CZ(Ψ) = -μ_RS(Γ(Ψ), Δ)` of `TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder`
(`TauCeti.GLSymplectic.conleyZehnderIndex_expPath_J_mul_eq_neg_signature_div_two`): for a
symmetric invertible matrix `S` with `‖S‖ < 2π` in the `ℓ²` operator norm, the path
`t ↦ exp (t J S)`, `t ∈ [0, 1]` (`TauCeti.GLSymplectic.expPath`), has index `-signature (S) / 2`.

For the form `ω(x, y) = xᵀ J y`, `exp (t J S)` is the linearized flow of the quadratic Hamiltonian
`H(x) = xᵀ S x / 2` with `ι_{X_H} ω = dH`. The case of the rotations `S = diag (α, α)` is
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`.

## Proof

A symplectic matrix `A` without eigenvalue `-1` has the Cayley generator
`B = J (1 - A) (1 + A)⁻¹`, a symmetric matrix
(`SymplecticGroup.isSymm_J_mul_one_sub_mul_inv_one_add`), and the straightened graph `T Γ(A)` is
the graph `{x + i B x}` of `B`, so its Souriau map is the Cayley transform of `B`
(`TauCeti.GLSymplectic.souriau_graphUnitaryFrame_eq_cayley`). Along `t ↦ exp (t J S)` with
`‖S‖ < π` there is no eigenvalue `-1` (`Matrix.isUnit_exp_add_one`), and the crossing form formula
`Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley` applies to
`B t = J (1 - exp (t J S)) (1 + exp (t J S))⁻¹`. Its only crossing is at `t = 0`, since
`exp (t J S)` has no eigenvalue `1` for `0 < t ≤ 1` (`Matrix.isUnit_exp_sub_one`). There
`B 0 = 0` and `B' 0 = S / 2`, so the crossing contributes half the signature of `S`. For
`‖S‖ < 2π` the path is the catenation of the path of `S / 2` with a path along which
`exp (t J S)` has no eigenvalue `1`, whose index vanishes by the zero axiom
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_forall_isUnit_sub_one`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as a Maslov index, and its normalization on `exp (t J S)`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Theorem 2.3 (the zero and signature axioms).
-/

public section

open Matrix NormedSpace Set
open scoped unitInterval Matrix.Norms.L2Operator

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace GLSymplectic

open Matrix.GeneralLinearGroup Matrix.UnitaryGroup

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The signature axiom -/

/-- The Cayley generator `J (1 - exp (t J S)) (1 + exp (t J S))⁻¹` has derivative `S / 2` at
`t = 0`. -/
private theorem hasDerivAt_cayleyGen (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    HasDerivAt (fun t : ℝ ↦ J n ℝ * (1 - exp (t • (J n ℝ * S))) * (1 + exp (t • (J n ℝ * S)))⁻¹)
      ((2⁻¹ : ℝ) • S) 0 := by
  set X := J n ℝ * S with hX
  have hE : HasDerivAt (fun t : ℝ ↦ exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 : IsUnit (1 + exp ((0 : ℝ) • X)) := by
    rw [zero_smul, NormedSpace.exp_zero, ← two_smul ℝ, ← Algebra.algebraMap_eq_smul_one]
    exact (IsUnit.mk0 (2 : ℝ) two_ne_zero).map _
  have hinv : HasDerivAt (fun t : ℝ ↦ Ring.inverse (1 + exp (t • X)))
      (-(((h2.unit⁻¹ : _) : Matrix (n ⊕ n) (n ⊕ n) ℝ) * X *
        ((h2.unit⁻¹ : _) : Matrix (n ⊕ n) (n ⊕ n) ℝ))) 0 := by
    have := (hasFDerivAt_ringInverse (𝕜 := ℝ) h2.unit).comp_hasDerivAt (0 : ℝ) (hE.const_add 1)
    simp only [Function.comp_def, neg_apply,
      ContinuousLinearMap.mulLeftRight_apply] at this
    exact this
  have hprod := ((hE.const_sub 1).const_mul (J n ℝ)).mul hinv
  simp only [nonsing_inv_eq_ringInverse]
  convert hprod using 1
  have hhalf : (1 + 1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) * ((2⁻¹ : ℝ) • 1) = 1 := by
    rw [← two_smul ℝ, smul_mul_smul, Matrix.one_mul, mul_inv_cancel₀ two_ne_zero, one_smul]
  have hz : J n ℝ * (1 - exp ((0 : ℝ) • X)) = 0 := by
    rw [zero_smul, NormedSpace.exp_zero, sub_self, Matrix.mul_zero]
  have hi : Ring.inverse (1 + exp ((0 : ℝ) • X)) = (2⁻¹ : ℝ) • 1 := by
    rw [zero_smul, NormedSpace.exp_zero, ← nonsing_inv_eq_ringInverse, inv_eq_right_inv hhalf]
  rw [hz, Matrix.zero_mul, add_zero, hi, hX, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg,
    ← Matrix.mul_assoc, J_squared, neg_mul, Matrix.one_mul, neg_neg]

/-- The Cayley generator `J (1 - exp (t J S)) (1 + exp (t J S))⁻¹` is continuous where
`1 + exp (t J S)` is invertible. -/
private theorem continuousOn_cayleyGen (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) {s : Set ℝ}
    (hs : ∀ t ∈ s, IsUnit (1 + exp (t • (J n ℝ * S)))) :
    ContinuousOn (fun t : ℝ ↦
      J n ℝ * (1 - exp (t • (J n ℝ * S))) * (1 + exp (t • (J n ℝ * S)))⁻¹) s := by
  let +nondep : NormedAlgebra ℚ (Matrix (n ⊕ n) (n ⊕ n) ℝ) := .restrictScalars ℚ ℝ _
  have hE : Continuous fun t : ℝ ↦ exp (t • (J n ℝ * S)) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  simp only [nonsing_inv_eq_ringInverse]
  refine ((continuous_const.mul (continuous_const.sub hE)).continuousOn).mul fun t ht ↦ ?_
  exact ((NormedRing.inverse_continuousAt (hs t ht).unit).comp_of_eq
    (continuous_const.add hE).continuousAt (hs t ht).unit_spec.symm).continuousWithinAt

/-- For `‖S‖ < π` and `0 ≤ t ≤ 1`, `exp (t J S)` has no eigenvalue `-1`. -/
private theorem isUnit_one_add_exp_smul_J_mul {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hSπ : ‖S‖ < Real.pi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 + exp (t • (J n ℝ * S))) := by
  rw [add_comm]
  refine isUnit_exp_add_one (lt_of_le_of_lt ?_ hSπ)
  rw [norm_smul, Real.norm_eq_abs, l2_opNorm_J_mul, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg S) ht.2

/-- For `S` invertible with `‖S‖ < π`, the Cayley generator
`J (1 - exp (t J S)) (1 + exp (t J S))⁻¹` is invertible for `0 < t ≤ 1`. -/
private theorem det_cayleyGen_ne_zero {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hdet : S.det ≠ 0)
    (hSπ : ‖S‖ < Real.pi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : t ≠ 0) :
    (J n ℝ * (1 - exp (t • (J n ℝ * S))) * (1 + exp (t • (J n ℝ * S)))⁻¹).det ≠ 0 := by
  have h1 : IsUnit (exp (t • (J n ℝ * S)) - 1) :=
    isUnit_exp_sub_one ((isUnit_iff_isUnit_det _).2 (by simp [ht0, hdet]))
      (by rw [norm_smul, Real.norm_eq_abs, l2_opNorm_J_mul, abs_of_nonneg ht.1]
          nlinarith [norm_nonneg S, ht.2, Real.pi_pos])
  have h1' : IsUnit (1 - exp (t • (J n ℝ * S))) := by rw [← neg_sub]; exact h1.neg
  rw [det_mul, det_mul]
  exact mul_ne_zero (mul_ne_zero (isUnit_det_J n ℝ).ne_zero
    ((isUnit_iff_isUnit_det _).1 h1').ne_zero)
    ((isUnit_iff_isUnit_det _).1 (isUnit_nonsing_inv_iff.2
      (isUnit_one_add_exp_smul_J_mul hSπ ht))).ne_zero

/-- The signature axiom for `‖S‖ < π`, where `exp (t J S)` has no eigenvalue `-1` and the crossing
form formula applies to the whole path. -/
private theorem conleyZehnderIndex_expPath_J_mul_of_norm_lt_pi {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsSymm) (hdet : S.det ≠ 0) (hSπ : ‖S‖ < Real.pi) :
    conleyZehnderIndex (expPath (J n ℝ * S) (LieAlgebra.Symplectic.J_mul_mem_sp_iff.2 hS)) =
      -(signature S : ℝ) / 2 := by
  set X := J n ℝ * S
  have hXsp : X ∈ LieAlgebra.Symplectic.sp n ℝ := LieAlgebra.Symplectic.J_mul_mem_sp_iff.2 hS
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ,
      A = fun t ↦ J n ℝ * (1 - exp (t • X)) * (1 + exp (t • X))⁻¹ := ⟨_, rfl⟩
  have hunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : IsUnit (1 + exp (t • X)) :=
    isUnit_one_add_exp_smul_J_mul hSπ ht
  have hsymp (t : ℝ) : exp (t • X) ∈ symplecticGroup n ℝ :=
    exp_mem_symplecticGroup_of_mem_sp _ ((LieAlgebra.Symplectic.sp n ℝ).smul_mem t hXsp)
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t).IsHermitian := by
    rw [hAdef]
    exact isHermitian_iff_isSymm.2
      (SymplecticGroup.isSymm_J_mul_one_sub_mul_inv_one_add (hsymp t) (hunit t ht))
  have hdetA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : t ≠ 0) : (A t).det ≠ 0 := by
    rw [hAdef]
    exact det_cayleyGen_ne_zero hdet hSπ ht ht0
  have hA0 : A 0 = 0 := by simp [hAdef]
  have hγ (t : I) : (souriau (((expPath X hXsp).map continuous_graphUnitaryFrame) t) :
      Matrix (n ⊕ n) (n ⊕ n) ℂ) = cayley ((A t).map ((↑) : ℝ → ℂ)) := by
    have h := souriau_graphUnitaryFrame_eq_cayley (expPath X hXsp t)
      (by rw [coe_expPath_apply]; exact hunit t t.2)
    simpa only [coe_expPath_apply, hAdef, Path.map_coe, Function.comp_apply] using h
  -- The only crossing is at `t = 0`, where `A 0 = 0` and `A' 0 = S / 2`.
  have hcross (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hdt : (A t).det = 0) : t = 0 := by
    by_contra h0
    exact hdetA t ht h0 hdt
  have hmas := Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley
    ((expPath X hXsp).map continuous_graphUnitaryFrame) (A' := fun _ ↦ (2⁻¹ : ℝ) • S)
    (hAdef ▸ continuousOn_cayleyGen S hunit) hA hγ
    (fun t ht hdt i j ↦ by
      obtain rfl := hcross t ht hdt
      let L : Matrix (n ⊕ n) (n ⊕ n) ℝ →L[ℝ] ℝ :=
        LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℝ i j)
      rw [hAdef]
      exact (L.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_cayleyGen S)).hasDerivWithinAt)
    (fun t ht hdt ↦ by
      obtain rfl := hcross t ht hdt
      rw [hA0]
      exact nondegenerate_crossingForm_zero (hS.smul _)
        (by rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet))
  rw [conleyZehnderIndex_def, hmas, hA0, sigPos_sub_sigNeg_crossingForm_zero,
    signature_smul_of_pos (by norm_num),
    sigPos_sub_sigNeg_crossingForm_eq_zero (hdetA 1 (right_mem_Icc.2 zero_le_one) one_ne_zero),
    finsum_mem_eq_zero_of_forall_eq_zero fun t ht ↦ sigPos_sub_sigNeg_crossingForm_eq_zero
      (hdetA t (Ioo_subset_Icc_self ht) ht.1.ne') _]
  push_cast
  ring

/-- **The signature axiom.** For a symmetric invertible matrix `S` with `‖S‖ < 2π` in the `ℓ²`
operator norm, the path `t ↦ exp (t J S)`, `t ∈ [0, 1]`, has Conley–Zehnder index
`-signature (S) / 2`. -/
theorem conleyZehnderIndex_expPath_J_mul_eq_neg_signature_div_two {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsSymm) (hdet : S.det ≠ 0) (hS2π : ‖S‖ < 2 * Real.pi) :
    conleyZehnderIndex (expPath (J n ℝ * S) (LieAlgebra.Symplectic.J_mul_mem_sp_iff.2 hS)) =
      -(signature S : ℝ) / 2 := by
  set X := J n ℝ * S
  have hXsp : X ∈ LieAlgebra.Symplectic.sp n ℝ := LieAlgebra.Symplectic.J_mul_mem_sp_iff.2 hS
  have hS' : ((2⁻¹ : ℝ) • S).IsSymm := hS.smul _
  have hX' : J n ℝ * ((2⁻¹ : ℝ) • S) = (2⁻¹ : ℝ) • X := Matrix.mul_smul _ _ _
  -- The second half `t ↦ exp (t X)`, `t ∈ [1/2, 1]`, of the path.
  let δ : Path (expOfMemSp (J n ℝ * ((2⁻¹ : ℝ) • S)) (LieAlgebra.Symplectic.J_mul_mem_sp_iff.2 hS'))
      (expOfMemSp X hXsp) :=
    { toFun s := expOfMemSp (((1 + (s : ℝ)) / 2) • X)
        ((LieAlgebra.Symplectic.sp n ℝ).smul_mem _ hXsp)
      continuous_toFun :=
        continuous_expOfMemSp_smul ((continuous_const.add continuous_subtype_val).div_const _) _
      source' := by
        refine Subtype.ext (Units.ext ?_)
        simp [hX']
      target' := by
        refine Subtype.ext (Units.ext ?_)
        simp }
  have hδ (s : I) : ((δ s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      exp (((1 + (s : ℝ)) / 2) • X) :=
    coe_expOfMemSp _ _
  have hsplit : (expPath (J n ℝ * ((2⁻¹ : ℝ) • S))
      (LieAlgebra.Symplectic.J_mul_mem_sp_iff.2 hS')).trans δ = expPath X hXsp := by
    refine Path.ext (funext fun s ↦ ?_)
    rw [Path.trans_apply]
    split_ifs with h
    · refine Subtype.ext (Units.ext ?_)
      rw [coe_expPath_apply, coe_expPath_apply, hX', smul_smul]
      congr 2
      ring
    · refine Subtype.ext (Units.ext ?_)
      rw [coe_expPath_apply, hδ]
      congr 2
      ring
  have hnorm : ‖(2⁻¹ : ℝ) • S‖ < Real.pi := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  rw [← hsplit, conleyZehnderIndex_trans, conleyZehnderIndex_expPath_J_mul_of_norm_lt_pi hS'
    (by rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet) hnorm,
    signature_smul_of_pos (by norm_num), conleyZehnderIndex_eq_zero_of_forall_isUnit_sub_one δ
    fun s ↦ ?_, add_zero]
  have hs : 0 < (1 + (s : ℝ)) / 2 := by linarith [s.2.1]
  rw [hδ]
  refine isUnit_exp_sub_one ((isUnit_iff_isUnit_det _).2 (by simp [X, hs.ne', hdet])) ?_
  rw [norm_smul, Real.norm_eq_abs, l2_opNorm_J_mul, abs_of_pos hs]
  nlinarith [s.2.2, norm_nonneg S]

end GLSymplectic

end TauCeti
