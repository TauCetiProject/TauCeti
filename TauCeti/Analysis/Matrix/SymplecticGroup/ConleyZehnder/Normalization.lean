/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
public import TauCeti.LinearAlgebra.Matrix.Signature
import TauCeti.Algebra.Lie.Symplectic.Basic
import TauCeti.Analysis.Matrix.Exponential.Spectrum
import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Cayley
import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Zero
import TauCeti.Analysis.Matrix.SymplecticGroup.L2OpNorm
import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing
import TauCeti.Geometry.Lie.Subgroup.Symplectic
import TauCeti.LinearAlgebra.Eigenspace.Matrix
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The normalization of the Conley–Zehnder index

The Conley–Zehnder index `TauCeti.GLSymplectic.conleyZehnderIndex` of a path of symplectic matrices
is minus the Robbin–Salamon index of its graphs relative to the diagonal. This file computes it for
paths that never meet the eigenvalue `-1`, and proves the normalization (signature) axiom: for a
nondegenerate symmetric matrix `S` with `‖S‖ < 2π` in the `ℓ²` operator norm, the path
`t ↦ exp (t J S)`, `t ∈ [0, 1]`, has index `-signature(S) / 2`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`). Its filter form, for every
sufficiently small nondegenerate symmetric `S`, is
`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_eq_neg_signature_div_two`. For nondegenerate
`S = diag (α, α)` this agrees with the computation on rotations
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`; here `S` is an
arbitrary nondegenerate symmetric matrix, in particular a Hessian that is not diagonalized by a
symplectic basis.

For the form `ω(x, y) = xᵀ J y`, `exp (t J S)` is the linearized flow of the quadratic Hamiltonian
`H(x) = xᵀ S x / 2` with `ι_{X_H} ω = dH`. Since `J` is unitary, `‖J S‖ = ‖S‖`
(`Matrix.l2_opNorm_J_mul`), which is how the bound on `S` controls `exp (t J S)`.

## Paths avoiding `-1`

The diagonal straightening `T` sends the graph of a real matrix `Ψ` to the real span of
`(Ψ + 1) + i (-J (Ψ - 1))`. If `Ψ` is symplectic and `Ψ + 1` is invertible, this is the graph
`{x + i A x}` of the symmetric matrix

`A = (Ψ + 1)⁻ᵀ (Ψᵀ J - J Ψ) (Ψ + 1)⁻¹`,

the Cayley transform of `Ψ`, since `Ψᵀ J Ψ = J` gives `(Ψ + 1)ᵀ (-J (Ψ - 1)) = Ψᵀ J - J Ψ`. The
localization axiom `Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley` then
computes the index of a path `γ` none of whose matrices has eigenvalue `-1` from its endpoints,
and Sylvester's law of inertia removes the congruence by `(Ψ + 1)⁻¹`:

`CZ(γ) = (signature (Ψ₀ᵀ J - J Ψ₀) - signature (Ψ₁ᵀ J - J Ψ₁)) / 2`, `Ψᵢ = γ i`

(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one`). At `Ψ = 1` the
matrix `Ψᵀ J - J Ψ` vanishes.

## The path `exp (t J S)`

A symplectic matrix `A` without eigenvalue `-1` has the symmetric symplectic Cayley transform
`B = J (1 - A) (1 + A)⁻¹` (`Matrix.isSymm_symplecticCayley`), and the straightened graph `T Γ(A)`
is the graph `{x + i B x}` of `B`, so its Souriau map is the Cayley transform of `B`
(`TauCeti.GLSymplectic.coe_souriau_graphUnitaryFrame_eq_cayley`). Along `t ↦ exp (t J S)` with
`‖S‖ < π` there is no eigenvalue `-1` (`Matrix.isUnit_exp_add_one_real`), and the crossing form
formula `Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley` applies to
`B t = J (1 - exp (t J S)) (1 + exp (t J S))⁻¹`. Its only crossing is at `t = 0`, since
`exp (t J S)` has no eigenvalue `1` for `0 < t ≤ 1` (`Matrix.isUnit_exp_sub_one_real`). There
`B 0 = 0` and `B' 0 = S / 2`, so the crossing contributes half the signature of `S`. For
`‖S‖ < 2π` the path is the catenation of the path of `S / 2` with a path along which
`exp (t J S)` has no eigenvalue `1`, whose index vanishes by the zero axiom
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the index of graphs relative to the diagonal, and its
  normalization on `exp (t J S)`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2, Theorem 2.3 (the axioms of the Conley–Zehnder index,
  including the normalization for symmetric `S` with `‖S‖ < 2π`).
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup Complex
open scoped unitInterval Topology
open Filter

namespace TauCeti

namespace GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The straightened graph frame of a real matrix `Ψ` is
`(1/√2) ((Ψ + 1) + i (-J (Ψ - 1)))`. -/
private theorem diagonalStraightening_mul_graphFrame_eq (Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    diagonalStraightening n * graphFrame Ψ = ((√2 : ℝ) : ℂ)⁻¹ •
      ((Ψ + 1).map ((↑) : ℝ → ℂ) + Complex.I • (-(J n ℝ * (Ψ - 1))).map ((↑) : ℝ → ℂ)) := by
  refine ext_of_mulVec_single fun j ↦ ?_
  have hx : (Pi.single j 1 : n ⊕ n → ℂ) =
      fun k ↦ (((Pi.single j (1 : ℝ) : n ⊕ n → ℝ) k : ℝ) : ℂ) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hx, ← mulVec_mulVec, graphFrame_mulVec]
  generalize (Pi.single j (1 : ℝ) : n ⊕ n → ℝ) = x
  have hmap (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (k : n ⊕ n) :
      (A.map ((↑) : ℝ → ℂ) *ᵥ fun k ↦ (x k : ℂ)) k = ((A *ᵥ x) k : ℂ) := by
    simp [mulVec, dotProduct]
  have hJ : ((J n ℝ * (Ψ - 1)) *ᵥ x) = J n ℝ *ᵥ (Ψ *ᵥ x - x) := by
    rw [← mulVec_mulVec, sub_mulVec, one_mulVec]
  ext (i | i) <;>
    simp only [smul_mulVec, add_mulVec, Pi.smul_apply, Pi.add_apply, hmap, neg_mulVec, Pi.neg_apply,
      diagonalStraightening_def, fromBlocks_mulVec, hJ, one_mulVec] <;>
    simp [J, fromBlocks_mulVec, neg_mulVec, one_mulVec]
  · ring
  · linear_combination (-(x (Sum.inr i) : ℂ) - ((Ψ *ᵥ x) (Sum.inr i) : ℂ)) * I_sq

/-- The symmetric matrix `(Ψ + 1)⁻ᵀ (Ψᵀ J - J Ψ) (Ψ + 1)⁻¹` whose graph is the straightened graph
of `Ψ`, when `Ψ` is symplectic and `Ψ + 1` is invertible. -/
private noncomputable def graphSymm (Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  ((Ψ + 1)⁻¹)ᵀ * (Ψᵀ * J n ℝ - J n ℝ * Ψ) * (Ψ + 1)⁻¹

private theorem isHermitian_graphSymm (Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphSymm Ψ).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, graphSymm, transpose_mul, transpose_mul,
    transpose_transpose, transpose_transpose_mul_J_sub_J_mul, Matrix.mul_assoc]

private theorem graphSymm_mul {Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨ : Ψ ∈ symplecticGroup n ℝ)
    (h : IsUnit (Ψ + 1).det) : graphSymm Ψ * (Ψ + 1) = -(J n ℝ * (Ψ - 1)) := by
  rw [graphSymm, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one,
    transpose_mul_J_sub_J_mul_eq_transpose_mul_neg_J_mul hΨ, ← Matrix.mul_assoc,
    ← transpose_mul, mul_nonsing_inv _ h, transpose_one, Matrix.one_mul]

private theorem signature_graphSymm {Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (Ψ + 1).det) :
    signature (graphSymm Ψ) = signature (Ψᵀ * J n ℝ - J n ℝ * Ψ) := by
  have := signature_congr (P := ((Ψ + 1)⁻¹)ᵀ)
    (by rw [det_transpose]; exact isUnit_nonsing_inv_det _ h) (Ψᵀ * J n ℝ - J n ℝ * Ψ)
  rwa [transpose_transpose] at this



/-- The straightened graph of a symplectic matrix `Ψ` with `Ψ + 1` invertible is the graph
`{x + i A x}` of the symmetric matrix `A = graphSymm Ψ`. -/
private theorem realImage_diagonalStraightening_mul_graphFrame {Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hΨ : Ψ ∈ symplecticGroup n ℝ) (h : IsUnit (Ψ + 1).det) :
    (diagonalStraightening n * graphFrame Ψ).realImage =
      (1 + Complex.I • (graphSymm Ψ).map ((↑) : ℝ → ℂ)).realImage := by
  have hu : IsUnit (((√2 : ℝ)⁻¹) • (Ψ + 1)) :=
    (isUnit_iff_isUnit_det _).2 (by
      rw [det_smul]
      exact ((IsUnit.mk0 _ (by positivity)).pow _).mul h)
  have heq : diagonalStraightening n * graphFrame Ψ =
      (1 + Complex.I • (graphSymm Ψ).map ((↑) : ℝ → ℂ)) *
        ((((√2 : ℝ)⁻¹) • (Ψ + 1)).map ((↑) : ℝ → ℂ)) := by
    have hs : (((√2 : ℝ)⁻¹) • (Ψ + 1)).map ((↑) : ℝ → ℂ) = ((√2 : ℝ) : ℂ)⁻¹ • (Ψ + 1).map (↑) := by
      ext i j
      simp [mul_add]
    rw [diagonalStraightening_mul_graphFrame_eq, ← graphSymm_mul hΨ h, map_ofReal_mul, hs,
      Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [heq, realImage_mul_map_ofReal _ hu]

/-- **The Conley–Zehnder index of a path avoiding the eigenvalue `-1`.** If no matrix of the path
`γ` of symplectic matrices has eigenvalue `-1`, its Conley–Zehnder index is half the drop of the
signature of the symmetric matrix `Ψᵀ J - J Ψ` from `Ψ = γ 0` to `Ψ = γ 1`. -/
theorem conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one {A B : GLSymplectic n ℝ}
    (γ : Path A B)
    (hγ : ∀ t, IsUnit (((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) + 1).det) :
    conleyZehnderIndex γ =
      (signature (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * J n ℝ -
          J n ℝ * ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) -
        signature (((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * J n ℝ -
          J n ℝ * ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) : ℝ) / 2 := by
  set Ψ : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ ((γ t : GL (n ⊕ n) ℝ) : Matrix _ _ ℝ)
  have hΨc : Continuous Ψ :=
    Units.continuous_val.comp (continuous_subtypeVal.comp γ.continuous)
  -- The straightened graph of `γ t` is the graph of the symmetric matrix `graphSymm (γ t)`.
  set S : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ graphSymm (Ψ t) with hSdef
  have hinv : Continuous fun t ↦ (Ψ t + 1)⁻¹ :=
    continuous_iff_continuousAt.2 fun t ↦
      (continuousAt_matrix_inv _ (by
        rw [Ring.inverse_eq_inv']
        exact continuousAt_inv₀ (hγ t).ne_zero)).comp (hΨc.add continuous_const).continuousAt
  have hSc : Continuous S :=
    (hinv.matrix_transpose.mul ((hΨc.matrix_transpose.mul continuous_const).sub
      (continuous_const.mul hΨc))).mul hinv
  have hS (t : I) : (S t).IsHermitian := isHermitian_graphSymm _
  obtain ⟨U, V, δ, hδ⟩ := exists_path_realImage_eq_and_souriau_eq_cayley hSc hS
  have hreal (t : I) : (δ t : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage = (diagonalStraightening n *
      graphFrame ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage := by
    rw [(hδ t).1, realImage_diagonalStraightening_mul_graphFrame
      (mem_iff_mem_symplecticGroup.1 (γ t).property) (hγ t)]
  rw [conleyZehnderIndex_eq_neg_maslovIndex γ δ hreal,
    maslovIndex_eq_signature_sub_of_souriau_eq_cayley δ hSc hS fun t ↦ (hδ t).2, hSdef]
  dsimp only
  rw [signature_graphSymm (hγ 1), signature_graphSymm (hγ 0), γ.source, γ.target]
  ring

/-! ### The signature axiom -/

section SignatureAxiom

open NormedSpace Set Module
open scoped Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Since `J` is unitary, `‖t J S‖ = |t| ‖S‖`. -/
private theorem norm_smul_J_mul (t : ℝ) (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    ‖t • (J n ℝ * S)‖ = |t| * ‖S‖ := by
  rw [norm_smul, Real.norm_eq_abs, l2_opNorm_J_mul]

/-- The symplectic Cayley transform `J (1 - exp (t J S)) (1 + exp (t J S))⁻¹` of `exp (t J S)`. -/
private noncomputable def cayleyGen (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) (t : ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  symplecticCayley (exp (t • (J n ℝ * S)))

/-- The Cayley generator `cayleyGen S` has derivative `S / 2` at `t = 0`. -/
private theorem hasDerivAt_cayleyGen (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    HasDerivAt (cayleyGen S) ((2⁻¹ : ℝ) • S) 0 := by
  unfold cayleyGen
  simp only [symplecticCayley_def]
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
  rw [hz, hi]
  simp [hX, ← Matrix.mul_assoc, J_squared]

/-- The Cayley generator `cayleyGen S` is continuous where `1 + exp (t J S)` is invertible. -/
private theorem continuousOn_cayleyGen (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) {s : Set ℝ}
    (hs : ∀ t ∈ s, IsUnit (1 + exp (t • (J n ℝ * S)))) :
    ContinuousOn (cayleyGen S) s := by
  unfold cayleyGen
  simp only [symplecticCayley_def]
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
  refine isUnit_exp_add_one_real (lt_of_le_of_lt ?_ hSπ)
  rw [norm_smul_J_mul, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg S) ht.2

/-- For `S` invertible, `0 < t` and `t ‖S‖ < 2π`, `exp (t J S)` has no eigenvalue `1`. -/
private theorem isUnit_exp_smul_J_mul_sub_one {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hdet : S.det ≠ 0)
    {t : ℝ} (ht : 0 < t) (hb : t * ‖S‖ < 2 * Real.pi) :
    IsUnit (exp (t • (J n ℝ * S)) - 1) := by
  refine isUnit_exp_sub_one_real ((isUnit_iff_isUnit_det _).2 (by simp [ht.ne', hdet])) ?_
  rwa [norm_smul_J_mul, abs_of_pos ht]

/-- For `S` symmetric with `‖S‖ < π`, the Cayley generator `cayleyGen S t` is symmetric for
`0 ≤ t ≤ 1`. -/
private theorem isSymm_cayleyGen {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hS : S.IsSymm)
    (hSπ : ‖S‖ < Real.pi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (cayleyGen S t).IsSymm :=
  isSymm_symplecticCayley
    (exp_mem_symplecticGroup_of_mem_sp _
      ((LieAlgebra.Symplectic.sp n ℝ).smul_mem t (LieAlgebra.Symplectic.J_mul_mem_sp hS)))
    ((isUnit_iff_isUnit_det _).1 (isUnit_one_add_exp_smul_J_mul hSπ ht))

/-- For `S` invertible with `‖S‖ < π`, the Cayley generator `cayleyGen S t` is invertible for
`0 < t ≤ 1`. -/
private theorem det_cayleyGen_ne_zero {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hdet : S.det ≠ 0)
    (hSπ : ‖S‖ < Real.pi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : t ≠ 0) :
    (cayleyGen S t).det ≠ 0 := by
  have h1 : IsUnit (exp (t • (J n ℝ * S)) - 1) :=
    isUnit_exp_smul_J_mul_sub_one hdet (ht.1.lt_of_ne' ht0)
      (by nlinarith [norm_nonneg S, ht.2, Real.pi_pos])
  rw [cayleyGen, symplecticCayley_def, det_mul]
  exact mul_ne_zero
    ((isUnit_iff_isUnit_det _).1 ((isUnit_J n ℝ).mul (IsUnit.sub_iff.1 h1))).ne_zero
    ((isUnit_iff_isUnit_det _).1 (isUnit_nonsing_inv_iff.2
      (isUnit_one_add_exp_smul_J_mul hSπ ht))).ne_zero

/-- The signature axiom for `‖S‖ < π`, where `exp (t J S)` has no eigenvalue `-1` and the crossing
form formula applies to the whole path. -/
private theorem conleyZehnderIndex_expPath_J_mul_of_norm_lt_pi {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsSymm) (hdet : S.det ≠ 0) (hSπ : ‖S‖ < Real.pi) :
    conleyZehnderIndex (expPath (J n ℝ * S) (LieAlgebra.Symplectic.J_mul_mem_sp hS)) =
      -(signature S : ℝ) / 2 := by
  set X := J n ℝ * S
  have hXsp : X ∈ LieAlgebra.Symplectic.sp n ℝ := LieAlgebra.Symplectic.J_mul_mem_sp hS
  have hunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : IsUnit (1 + exp (t • X)) :=
    isUnit_one_add_exp_smul_J_mul hSπ ht
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (cayleyGen S t).IsHermitian :=
    isHermitian_iff_isSymm.2 (isSymm_cayleyGen hS hSπ ht)
  have hdetA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : t ≠ 0) : (cayleyGen S t).det ≠ 0 :=
    det_cayleyGen_ne_zero hdet hSπ ht ht0
  have hA0 : cayleyGen S 0 = 0 := by simp [cayleyGen]
  have hγ (t : I) : (souriau (((expPath X hXsp).map continuous_graphUnitaryFrame) t) :
      Matrix (n ⊕ n) (n ⊕ n) ℂ) = cayley ((cayleyGen S t).map ((↑) : ℝ → ℂ)) := by
    have h := coe_souriau_graphUnitaryFrame_eq_cayley (A := expPath X hXsp t)
      (by rw [coe_expPath_apply]; exact (isUnit_iff_isUnit_det _).1 (hunit t t.property))
    simpa only [coe_expPath_apply, cayleyGen, Path.map_coe, Function.comp_apply] using h
  -- The only crossing is at `t = 0`, where `cayleyGen S` vanishes with derivative `S / 2`.
  have hmas := Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley
    ((expPath X hXsp).map continuous_graphUnitaryFrame) (A' := fun _ ↦ (2⁻¹ : ℝ) • S)
    (continuousOn_cayleyGen S hunit) hA hγ
    (fun t ht hdt i j ↦ by
      obtain rfl : t = 0 := by_contra fun h0 ↦ hdetA t ht h0 hdt
      let L : Matrix (n ⊕ n) (n ⊕ n) ℝ →L[ℝ] ℝ :=
        LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℝ i j)
      exact (L.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_cayleyGen S)).hasDerivWithinAt)
    (fun t ht hdt ↦ by
      obtain rfl : t = 0 := by_contra fun h0 ↦ hdetA t ht h0 hdt
      rw [hA0]
      exact nondegenerate_crossingForm_zero (hS.smul _) (by simp [hdet]))
  rw [conleyZehnderIndex_def, hmas, hA0, sigPos_sub_sigNeg_crossingForm_zero,
    signature_smul_of_pos (by norm_num),
    sigPos_sub_sigNeg_crossingForm_eq_zero (hA 1 (right_mem_Icc.2 zero_le_one)).isSymm
      (hdetA 1 (right_mem_Icc.2 zero_le_one) one_ne_zero),
    finsum_mem_eq_zero_of_forall_eq_zero fun t ht ↦ sigPos_sub_sigNeg_crossingForm_eq_zero
      (hA t (Ioo_subset_Icc_self ht)).isSymm (hdetA t (Ioo_subset_Icc_self ht) ht.1.ne') _]
  push_cast
  ring

/-- The signature axiom for the path `TauCeti.GLSymplectic.expPath` of `J S`, with `‖S‖ < 2π`: the
path of `S / 2` followed by a path along which `exp (t J S)` has no eigenvalue `1`. -/
private theorem conleyZehnderIndex_expPath_J_mul_eq_neg_signature_div_two
    {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hS : S.IsSymm) (hdet : S.det ≠ 0) (hS2π : ‖S‖ < 2 * Real.pi) :
    conleyZehnderIndex (expPath (J n ℝ * S) (LieAlgebra.Symplectic.J_mul_mem_sp hS)) =
      -(signature S : ℝ) / 2 := by
  set X := J n ℝ * S
  have hXsp : X ∈ LieAlgebra.Symplectic.sp n ℝ := LieAlgebra.Symplectic.J_mul_mem_sp hS
  have hS' : ((2⁻¹ : ℝ) • S).IsSymm := hS.smul _
  have hdet' : ((2⁻¹ : ℝ) • S).det ≠ 0 := by simp [hdet]
  have hX' : J n ℝ * ((2⁻¹ : ℝ) • S) = (2⁻¹ : ℝ) • X := Matrix.mul_smul _ _ _
  -- The second half `t ↦ exp (t X)`, `t ∈ [1/2, 1]`, of the path.
  let δ : Path (expOfMemSp (J n ℝ * ((2⁻¹ : ℝ) • S)) (LieAlgebra.Symplectic.J_mul_mem_sp hS'))
      (expOfMemSp X hXsp) :=
    { toFun s := expOfMemSp (((1 + (s : ℝ)) / 2) • X)
        ((LieAlgebra.Symplectic.sp n ℝ).smul_mem _ hXsp)
      continuous_toFun :=
        continuous_expOfMemSp
          (((continuous_const.add continuous_subtypeVal).div_const _).smul continuous_const) _
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
      (LieAlgebra.Symplectic.J_mul_mem_sp hS')).trans δ = expPath X hXsp := by
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
  -- Along `δ` the matrices `exp (t X)`, `t ∈ [1/2, 1]`, have no eigenvalue `1`.
  have hδ1 (s : I) : IsUnit (((δ s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - (1 : ℝ) • 1) := by
    have hs : 0 < (1 + (s : ℝ)) / 2 := by linarith [s.property.1]
    rw [one_smul, hδ]
    exact isUnit_exp_smul_J_mul_sub_one hdet hs (by nlinarith [s.property.2, norm_nonneg S])
  rw [← hsplit, conleyZehnderIndex_trans,
    conleyZehnderIndex_expPath_J_mul_of_norm_lt_pi hS' hdet' hnorm,
    signature_smul_of_pos (by norm_num), conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq δ
    (k := 0) fun s ↦ finrank_eigenspace_toLin'_eq_zero (hδ1 s), add_zero]

/-- **Normalization of the Conley–Zehnder index (the signature axiom).** If `S` is a nondegenerate
symmetric matrix with `‖S‖ < 2π` for the `ℓ²` operator norm, the path `t ↦ exp (t J S)`,
`t ∈ [0, 1]`, of symplectic matrices has Conley–Zehnder index `-signature(S) / 2`. -/
theorem conleyZehnderIndex_eq_neg_signature_div_two {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsHermitian) (hSdet : IsUnit S.det) (hS2π : ‖S‖ < 2 * Real.pi)
    {A B : GLSymplectic n ℝ} (γ : Path A B)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      NormedSpace.exp ((t : ℝ) • (J n ℝ * S))) :
    conleyZehnderIndex γ = -(signature S : ℝ) / 2 := by
  have hXsp := LieAlgebra.Symplectic.J_mul_mem_sp hS.isSymm
  have hγ' (t : I) : γ t = expPath (J n ℝ * S) hXsp t :=
    Subtype.ext (Units.ext (by rw [hγ, coe_expPath_apply]))
  obtain rfl : A = 1 := by rw [← γ.source, hγ' 0, Path.source]
  obtain rfl : B = expOfMemSp (J n ℝ * S) hXsp := by rw [← γ.target, hγ' 1, Path.target]
  obtain rfl : γ = expPath (J n ℝ * S) hXsp := Path.ext (funext hγ')
  exact conleyZehnderIndex_expPath_J_mul_eq_neg_signature_div_two hS.isSymm hSdet.ne_zero hS2π

/-- **Normalization of the Conley–Zehnder index near `0`.** For every sufficiently small
nondegenerate symmetric matrix `S`, the path `t ↦ exp (t J S)`, `t ∈ [0, 1]`, of symplectic
matrices has Conley–Zehnder index `-signature(S) / 2`. The explicit bound `‖S‖ < 2π` is
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`. -/
theorem eventually_conleyZehnderIndex_eq_neg_signature_div_two :
    ∀ᶠ S in 𝓝 (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ), S.IsHermitian → IsUnit S.det →
      ∀ {A B : GLSymplectic n ℝ} (γ : Path A B),
        (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
          NormedSpace.exp ((t : ℝ) • (J n ℝ * S))) →
        conleyZehnderIndex γ = -(signature S : ℝ) / 2 := by
  have h : ∀ᶠ S in 𝓝 (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ), ‖S‖ < 2 * Real.pi :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by simpa using Real.two_pi_pos)
  filter_upwards [h] with S hS2π hS hSdet A B γ hγ
  exact conleyZehnderIndex_eq_neg_signature_div_two hS hSdet hS2π γ hγ

end SignatureAxiom

end GLSymplectic

end TauCeti
