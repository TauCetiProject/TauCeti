/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Matrix.Exponential.FixedPoints
import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The normalization of the Conley–Zehnder index

The Conley–Zehnder index `TauCeti.GLSymplectic.conleyZehnderIndex` of a path of symplectic matrices
is minus the Robbin–Salamon index of its graphs relative to the diagonal. This file computes it for
paths that never meet the eigenvalue `-1`, and deduces the normalization axiom: for every
sufficiently small nondegenerate symmetric matrix `S`, the path `t ↦ exp (t J S)`, `t ∈ [0, 1]`,
has index `-signature(S) / 2`. The bound is explicit, `2 ‖J S‖ < log 2` for the operator norm
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`), and its filter form is
`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_eq_neg_signature_div_two`; for a fixed
nondegenerate `S`, the paths `t ↦ exp (t J (ε S))` have this index for small `ε > 0`
(`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_exp_smul_eq_neg_signature_div_two`). For small
nondegenerate `S = diag (α, α)` this agrees with the computation on rotations
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`, which covers
all `|αⱼ| < 2π` but only diagonal `S`; here `S` is an arbitrary small nondegenerate symmetric
matrix, in particular a Hessian that is not diagonalized by a symplectic basis.

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

Let `K = J S` with `2 ‖K‖ < log 2` for the operator norm. For `|u| ≤ 1` the vectors fixed by
`exp (u K) ^ 2` are then the kernel of `u K` (`Matrix.mulVec_eq_zero_of_exp_mulVec_exp_mulVec_eq`).
This shows that `exp (u K)` never has the eigenvalue `-1` (`Matrix.isUnit_det_exp_add_one`), and
that
`Ψ_uᵀ J - J Ψ_u = J (exp (-u K) - exp (u K))`, `Ψ_u = exp (u K)`, is nondegenerate for
`0 < |u| ≤ 1` when `S` is. Divided by `u`, these matrices tend to their derivative
`Kᵀ J - J K = 2 S` at `u = 0`, so they form a continuous path of nondegenerate symmetric matrices
from `2 S` to `Ψ₁ᵀ J - J Ψ₁` along which the signature is constant
(`Matrix.IsHermitian.eventually_signature_eq_of_continuousAt`). Hence
`signature (Ψ₁ᵀ J - J Ψ₁) = signature S`, and the index is `-signature(S) / 2`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the index of graphs relative to the diagonal, and its
  normalization on `exp (t J S)`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the axioms of the Conley–Zehnder index, including the
  normalization for symmetric `S` with `‖S‖ < 2π`).
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
  have hm (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) : (X * Y).map ((↑) : ℝ → ℂ) = X.map (↑) * Y.map (↑) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  have heq : diagonalStraightening n * graphFrame Ψ =
      (1 + Complex.I • (graphSymm Ψ).map ((↑) : ℝ → ℂ)) *
        ((((√2 : ℝ)⁻¹) • (Ψ + 1)).map ((↑) : ℝ → ℂ)) := by
    have hs : (((√2 : ℝ)⁻¹) • (Ψ + 1)).map ((↑) : ℝ → ℂ) = ((√2 : ℝ) : ℂ)⁻¹ • (Ψ + 1).map (↑) := by
      ext i j
      simp [mul_add]
    rw [diagonalStraightening_mul_graphFrame_eq, ← graphSymm_mul hΨ h, hm, hs, Matrix.add_mul,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
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

/-! ### Exponentials of small Hamiltonian matrices -/

open scoped Matrix.Norms.L2Operator in
/-- If `S` is nondegenerate, `u ≠ 0` and `2 ‖u J S‖ < log 2`, then for the symplectic matrix
`Ψ = exp (u J S)` the symmetric matrix `Ψᵀ J - J Ψ` is nondegenerate. -/
private theorem isUnit_det_transpose_mul_J_sub_J_mul_exp {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : IsUnit S.det) {u : ℝ} (hu0 : u ≠ 0) (hK : 2 * ‖u • (J n ℝ * S)‖ < Real.log 2)
    (hΨ : NormedSpace.exp (u • (J n ℝ * S)) ∈ symplecticGroup n ℝ) :
    IsUnit ((NormedSpace.exp (u • (J n ℝ * S)))ᵀ * J n ℝ -
      J n ℝ * NormedSpace.exp (u • (J n ℝ * S))).det := by
  set Ψ := NormedSpace.exp (u • (J n ℝ * S))
  set Ψ' := NormedSpace.exp (-(u • (J n ℝ * S)))
  have hJ := mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_det_J n ℝ))
  have hΨΨ' : Ψ * Ψ' = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (u • (J n ℝ * S))).neg_right),
      add_neg_cancel, NormedSpace.exp_zero]
  -- `Ψᵀ J = J Ψ⁻¹`, since `Ψᵀ J Ψ = J`.
  have hT : Ψᵀ * J n ℝ = J n ℝ * Ψ' := by
    rw [← Matrix.mul_one (Ψᵀ * J n ℝ), ← hΨΨ', ← Matrix.mul_assoc, SymplecticGroup.mem_iff'.1 hΨ]
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  rw [hT, sub_mulVec, sub_eq_zero, ← mulVec_mulVec, ← mulVec_mulVec] at hv
  have hfix : Ψ *ᵥ (Ψ *ᵥ v) = v := by
    rw [← hJ hv, mulVec_mulVec, hΨΨ', one_mulVec]
  have hker := mulVec_eq_zero_of_exp_mulVec_exp_mulVec_eq hK hfix
  rw [smul_mulVec, smul_eq_zero, ← mulVec_mulVec] at hker
  have hSv : S *ᵥ v = 0 := hJ (by rw [hker.resolve_left hu0, mulVec_zero])
  exact hv0 ((mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det S).2 hS))
    (hSv.trans (mulVec_zero S).symm))

open scoped Matrix.Norms.L2Operator in
/-- If `S` is symmetric and nondegenerate, and `2 ‖u J S‖ < log 2` and `exp (u J S)` is symplectic
for `u ∈ [0, 1]`, then for `Ψ = exp (J S)` the symmetric matrix `Ψᵀ J - J Ψ` has the signature of
`S`. Along `u ∈ [0, 1]` the matrices `(Ψ_uᵀ J - J Ψ_u) / u`, `Ψ_u = exp (u J S)`, extended by their
limit `2 S` at `u = 0`, form a continuous path of nondegenerate symmetric matrices. -/
private theorem signature_exp_transpose_mul_J_sub_J_mul_exp {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsHermitian) (hSdet : IsUnit S.det)
    (hK : ∀ u : I, 2 * ‖(u : ℝ) • (J n ℝ * S)‖ < Real.log 2)
    (hΨ : ∀ u : I, NormedSpace.exp ((u : ℝ) • (J n ℝ * S)) ∈ symplecticGroup n ℝ) :
    signature ((NormedSpace.exp (J n ℝ * S))ᵀ * J n ℝ - J n ℝ * NormedSpace.exp (J n ℝ * S)) =
      signature S := by
  set K := J n ℝ * S
  let f : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun u ↦
    NormedSpace.exp (u • Kᵀ) * J n ℝ - J n ℝ * NormedSpace.exp (u • K)
  have hf (u : ℝ) : f u = (NormedSpace.exp (u • K))ᵀ * J n ℝ - J n ℝ * NormedSpace.exp (u • K) := by
    simp only [f, ← Matrix.exp_transpose, transpose_smul]
  have hderiv (t : ℝ) : HasDerivAt f (NormedSpace.exp (t • Kᵀ) * Kᵀ * J n ℝ -
      J n ℝ * (NormedSpace.exp (t • K) * K)) t :=
    ((hasDerivAt_exp_smul_const Kᵀ t).mul_const _).sub
      ((hasDerivAt_exp_smul_const K t).const_mul _)
  have hK0 : Kᵀ * J n ℝ - J n ℝ * K = (2 : ℝ) • S := transpose_J_mul_mul_J_sub_J_mul_J_mul hS.isSymm
  have hf0 : f 0 = 0 := by simp [f]
  -- The slope of `f` at `0`, extended by the derivative `2 S`.
  set g := dslope f 0 with hgdef
  have hg0 : g 0 = (2 : ℝ) • S := by
    rw [hgdef, dslope_same, (hderiv 0).deriv, ← hK0]
    simp
  have hgu {u : ℝ} (hu : u ≠ 0) : g u = u⁻¹ • f u := by
    rw [hgdef, dslope_of_ne _ hu, slope_def_module, hf0, sub_zero, sub_zero]
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun u ↦ by
    rcases eq_or_ne u 0 with rfl | hu
    · exact continuousAt_dslope_same.2 (hderiv 0).differentiableAt
    · exact (continuousAt_dslope_of_ne hu).2 (hderiv u).continuousAt
  have hgh (u : I) : (g u).IsHermitian := by
    rcases eq_or_ne (u : ℝ) 0 with hu | hu
    · rw [hu, hg0]
      exact hS.smul (IsSelfAdjoint.all _)
    · rw [hgu hu, hf]
      refine IsHermitian.smul ?_ (IsSelfAdjoint.all _)
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_transpose_mul_J_sub_J_mul]
  have hgdet (u : I) : IsUnit (g u).det := by
    rcases eq_or_ne (u : ℝ) 0 with hu | hu
    · rw [hu, hg0, det_smul]
      exact ((IsUnit.mk0 _ two_ne_zero).pow _).mul hSdet
    · rw [hgu hu, det_smul, hf]
      exact ((IsUnit.mk0 _ (inv_ne_zero hu)).pow _).mul
        (isUnit_det_transpose_mul_J_sub_J_mul_exp hSdet hu (hK u) (hΨ u))
  -- The signature of `g` is locally constant on `[0, 1]`, hence constant.
  have hloc : IsLocallyConstant fun u : I ↦ signature (g u) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun u ↦ ?_
    filter_upwards [IsHermitian.eventually_signature_eq_of_continuousAt hgh
      (hgc.comp continuous_subtypeVal).continuousAt (hgdet u)] with w hw
    exact (IsHermitian.signature_map_ofReal (𝕜 := ℝ) (hgh w)).symm.trans
      (hw.trans (IsHermitian.signature_map_ofReal (𝕜 := ℝ) (hgh u)))
  have h := hloc.apply_eq_of_preconnectedSpace 1 0
  simp only [Set.Icc.coe_one, Set.Icc.coe_zero, hg0,
    signature_smul_of_pos (c := (2 : ℝ)) two_pos] at h
  rw [hgu one_ne_zero, inv_one, one_smul, hf, one_smul] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- Near `0`, the matrices `S` satisfy `2 ‖J S‖ < log 2` for the operator norm. -/
private theorem eventually_two_mul_norm_J_mul_lt :
    ∀ᶠ S in 𝓝 (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ), 2 * ‖J n ℝ * S‖ < Real.log 2 := by
  have hc : Continuous fun S : Matrix (n ⊕ n) (n ⊕ n) ℝ ↦ 2 * ‖J n ℝ * S‖ := by fun_prop
  exact hc.continuousAt.eventually_lt continuousAt_const
    (by simpa using Real.log_pos one_lt_two)

open scoped Matrix.Norms.L2Operator in
/-- **Normalization of the Conley–Zehnder index.** If `S` is a nondegenerate symmetric matrix with
`2 ‖J S‖ < log 2` for the operator norm, the path `t ↦ exp (t J S)`, `t ∈ [0, 1]`, of symplectic
matrices has Conley–Zehnder index `-signature(S) / 2`. -/
theorem conleyZehnderIndex_eq_neg_signature_div_two {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsHermitian) (hSdet : IsUnit S.det) (hK : 2 * ‖J n ℝ * S‖ < Real.log 2)
    {A B : GLSymplectic n ℝ} (γ : Path A B)
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      NormedSpace.exp ((t : ℝ) • (J n ℝ * S))) :
    conleyZehnderIndex γ = -(signature S : ℝ) / 2 := by
  have hK' (t : I) : 2 * ‖(t : ℝ) • (J n ℝ * S)‖ < Real.log 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1, mul_left_comm]
    exact (mul_le_of_le_one_left (by positivity) t.property.2).trans_lt hK
  rw [conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one γ fun t ↦ by
    rw [hγ t]; exact isUnit_det_exp_add_one (hK' t)]
  have hΨ (t : I) : NormedSpace.exp ((t : ℝ) • (J n ℝ * S)) ∈ symplecticGroup n ℝ := by
    rw [← hγ t]
    exact mem_iff_mem_symplecticGroup.1 (γ t).property
  have hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 1 := by
    rw [← γ.source, hγ 0, Set.Icc.coe_zero, zero_smul, NormedSpace.exp_zero]
  have hB : ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = NormedSpace.exp (J n ℝ * S) := by
    rw [← γ.target, hγ 1, Set.Icc.coe_one, one_smul]
  rw [hA, hB, signature_exp_transpose_mul_J_sub_J_mul_exp hS hSdet hK' hΨ]
  simp

/-- **Normalization of the Conley–Zehnder index near `0`.** For every sufficiently small
nondegenerate symmetric matrix `S`, the path `t ↦ exp (t J S)`, `t ∈ [0, 1]`, of symplectic
matrices has Conley–Zehnder index `-signature(S) / 2`. The explicit bound is
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`. -/
theorem eventually_conleyZehnderIndex_eq_neg_signature_div_two :
    ∀ᶠ S in 𝓝 (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ), S.IsHermitian → IsUnit S.det →
      ∀ {A B : GLSymplectic n ℝ} (γ : Path A B),
        (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
          NormedSpace.exp ((t : ℝ) • (J n ℝ * S))) →
        conleyZehnderIndex γ = -(signature S : ℝ) / 2 := by
  filter_upwards [eventually_two_mul_norm_J_mul_lt] with S hK hS hSdet A B γ hγ
  exact conleyZehnderIndex_eq_neg_signature_div_two hS hSdet hK γ hγ

/-- **Normalization of the Conley–Zehnder index for small multiples.** For a nondegenerate
symmetric matrix `S` and every small `ε > 0`, the path `t ↦ exp (t J (ε S))`, `t ∈ [0, 1]`, of
symplectic matrices has Conley–Zehnder index `-signature(S) / 2`. -/
theorem eventually_conleyZehnderIndex_exp_smul_eq_neg_signature_div_two
    {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hS : S.IsHermitian) (hSdet : IsUnit S.det) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ {A B : GLSymplectic n ℝ} (γ : Path A B),
      (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        NormedSpace.exp ((t : ℝ) • (J n ℝ * (ε • S)))) →
      conleyZehnderIndex γ = -(signature S : ℝ) / 2 := by
  have ht : Tendsto (fun ε : ℝ ↦ ε • S) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.smul_const S).mono_left nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ ↦ ε • S) (𝓝[>] 0) (𝓝 ((0 : ℝ) • S)))
  filter_upwards [ht.eventually eventually_conleyZehnderIndex_eq_neg_signature_div_two,
    self_mem_nhdsWithin] with ε hε hε0 A B γ hγ
  rw [hε (hS.smul (IsSelfAdjoint.all ε))
      (by rw [det_smul]; exact ((IsUnit.mk0 ε (ne_of_gt hε0)).pow _).mul hSdet) γ hγ,
    signature_smul_of_pos hε0]

end GLSymplectic

end TauCeti
