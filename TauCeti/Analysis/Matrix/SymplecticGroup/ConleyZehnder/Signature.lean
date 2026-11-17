/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.Analysis.Matrix.Cayley
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.LinearAlgebra.Matrix.Signature
import TauCeti.Analysis.Matrix.Exponential.Spectrum
import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing
import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic

/-!
# The zero and signature axioms of the Conley–Zehnder index

This file proves two normalization properties of the Conley–Zehnder index
`TauCeti.GLSymplectic.conleyZehnderIndex` of paths of symplectic matrices, in the convention
`CZ(Ψ) = -μ_RS(Γ(Ψ), Δ)` of `TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder`.

* **The zero axiom** (`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_forall_isUnit_sub_one`):
  a path of symplectic matrices none of which has the eigenvalue `1` has index zero. Its graphs
  stay transverse to the diagonal, so the Souriau maps of their straightenings never have the
  eigenvalue `1` (`TauCeti.GLSymplectic.not_isRoot_one_charpoly_souriau_graphUnitaryFrame`).
* **The signature axiom**
  (`TauCeti.GLSymplectic.conleyZehnderIndex_expPath_J_mul_eq_neg_signature_div_two`): for a
  symmetric invertible matrix `S` with `‖S‖ < 2π` in the `ℓ²` operator norm, the path
  `t ↦ exp (t J S)`, `t ∈ [0, 1]` (`TauCeti.GLSymplectic.expPath`), has index
  `-signature (S) / 2`.

For the form `ω(x, y) = xᵀ J y`, `exp (t J S)` is the linearized flow of the quadratic Hamiltonian
`H(x) = xᵀ S x / 2` with `ι_{X_H} ω = dH`. The case of the rotations `S = diag (α, α)` is
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`.

## Main definitions

* `TauCeti.GLSymplectic.expOfMemSp`: the exponential of an element of the symplectic Lie algebra,
  as a symplectic matrix.
* `TauCeti.GLSymplectic.expPath`: the path `t ↦ exp (t X)`, `t ∈ [0, 1]`.

## Proof

A symplectic matrix `A` without eigenvalue `-1` has the Cayley generator
`B = J (1 - A) (1 + A)⁻¹`, a symmetric matrix (`TauCeti.isSymm_J_mul_one_sub_mul_inv_one_add`),
and the straightened graph `T Γ(A)` is the graph `{x + i B x}` of `B`
(`TauCeti.diagonalStraightening_mul_graphFrame_eq_mul`), so its Souriau map is the Cayley
transform of `B` (`TauCeti.GLSymplectic.souriau_graphUnitaryFrame_eq_cayley`). Along
`t ↦ exp (t J S)` with `‖S‖ < π` there is no eigenvalue `-1` (`Matrix.isUnit_exp_add_one`), and
the crossing form formula
`Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley` applies to
`B t = J (1 - exp (t J S)) (1 + exp (t J S))⁻¹`. Its only crossing is at `t = 0`, since
`exp (t J S)` has no eigenvalue `1` for `0 < t ≤ 1` (`Matrix.isUnit_exp_sub_one`). There
`B 0 = 0` and `B' 0 = S / 2`, so the crossing contributes half the signature of `S`. For
`‖S‖ < 2π` the path is the catenation of the path of `S / 2` with a path along which
`exp (t J S)` has no eigenvalue `1`, whose index vanishes by the zero axiom.

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

/-! ### Graphs of symplectic matrices without eigenvalue `-1` -/

/-- The straightened graph frame of a real matrix `A` is `((1 + A) + i J (1 - A)) / √2`. -/
theorem diagonalStraightening_mul_graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    diagonalStraightening n * graphFrame A = ((√2 : ℝ) : ℂ)⁻¹ •
      ((1 + A).map ((↑) : ℝ → ℂ) + Complex.I • (J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ)) := by
  rw [diagonalStraightening_def, Matrix.smul_mul]
  congr 1
  rw [← fromBlocks_toBlocks A, graphFrame_def, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, J, ← fromBlocks_one, fromBlocks_add, sub_eq_add_neg, fromBlocks_neg,
    fromBlocks_multiply, fromBlocks_map, fromBlocks_smul]
  congr 1
  all_goals
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.smul_mul, Matrix.mul_smul, zero_add, add_zero, neg_neg, neg_zero, Matrix.mul_add,
      smul_smul, Complex.I_mul_I, neg_smul, one_smul, Matrix.map_add _ Complex.ofReal_add,
      Matrix.map_neg _ Complex.ofReal_neg, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
      smul_add, smul_neg]
    abel

/-- For a symplectic matrix `A` without eigenvalue `-1`, the Cayley generator
`J (1 - A) (1 + A)⁻¹` is symmetric. -/
theorem isSymm_J_mul_one_sub_mul_inv_one_add {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) (h1 : IsUnit (1 + A)) :
    (J n ℝ * (1 - A) * (1 + A)⁻¹).IsSymm := by
  have hJ : Aᵀ * J n ℝ * A = J n ℝ := SymplecticGroup.mem_iff'.1 hA
  have hP : IsUnit (1 + A).det := (isUnit_iff_isUnit_det _).1 h1
  have hPT : IsUnit (1 + A)ᵀ.det := by rwa [det_transpose]
  -- Conjugating `Bᵀ - B` by `1 + A` gives `-2 J + 2 Aᵀ J A = 0`.
  have key : (1 + A)ᵀ * ((J n ℝ * (1 - A) * (1 + A)⁻¹)ᵀ - J n ℝ * (1 - A) * (1 + A)⁻¹) *
      (1 + A) = 0 := by
    have h₁ : (1 + A)ᵀ * ((1 + A)⁻¹)ᵀ = 1 := by
      rw [← transpose_mul, nonsing_inv_mul _ hP, transpose_one]
    have h₂ : (1 + A)⁻¹ * (1 + A) = 1 := nonsing_inv_mul _ hP
    calc (1 + A)ᵀ * ((J n ℝ * (1 - A) * (1 + A)⁻¹)ᵀ - J n ℝ * (1 - A) * (1 + A)⁻¹) * (1 + A)
        = ((1 + A)ᵀ * ((1 + A)⁻¹)ᵀ) * (1 - A)ᵀ * (J n ℝ)ᵀ * (1 + A) -
            (1 + A)ᵀ * J n ℝ * (1 - A) * ((1 + A)⁻¹ * (1 + A)) := by
          simp only [transpose_mul]
          noncomm_ring
      _ = -2 • J n ℝ + 2 • (Aᵀ * J n ℝ * A) := by
          rw [h₁, h₂, J_transpose]
          simp only [transpose_sub, transpose_add, transpose_one]
          noncomm_ring
      _ = 0 := by rw [hJ]; abel
  have hcancel := congrArg (fun X ↦ ((1 + A)ᵀ)⁻¹ * X * (1 + A)⁻¹) key
  simp only [Matrix.mul_zero, Matrix.zero_mul] at hcancel
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hPT, Matrix.one_mul,
    Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one, sub_eq_zero] at hcancel
  exact hcancel

/-- The straightened graph frame of a matrix `A` without eigenvalue `-1` is the frame
`1 + i B` of the graph of its Cayley generator `B = J (1 - A) (1 + A)⁻¹`, times a real invertible
matrix. -/
theorem diagonalStraightening_mul_graphFrame_eq_mul {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (h1 : IsUnit (1 + A)) :
    diagonalStraightening n * graphFrame A =
      (1 + Complex.I • (J n ℝ * (1 - A) * (1 + A)⁻¹).map ((↑) : ℝ → ℂ)) *
        ((√2 : ℝ)⁻¹ • (1 + A)).map ((↑) : ℝ → ℂ) := by
  have hP : IsUnit (1 + A).det := (isUnit_iff_isUnit_det _).1 h1
  have hmap (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
      X.map ((↑) : ℝ → ℂ) * Y.map ((↑) : ℝ → ℂ) = (X * Y).map ((↑) : ℝ → ℂ) :=
    (map_mul Complex.ofRealHom.mapMatrix X Y).symm
  rw [diagonalStraightening_mul_graphFrame, Matrix.map_smul' _ _ _ Complex.ofReal_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hmap, Matrix.mul_assoc,
    nonsing_inv_mul _ hP, Matrix.mul_one, Complex.ofReal_inv]

namespace GLSymplectic

open Matrix.GeneralLinearGroup Matrix.UnitaryGroup

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **The Souriau map of a graph without eigenvalue `-1`.** If the symplectic matrix `A` has no
eigenvalue `-1`, the straightened graph `T Γ(A)` is the graph `{x + i B x}` of the symmetric
matrix `B = J (1 - A) (1 + A)⁻¹`, so its Souriau map is the Cayley transform of `B`. -/
theorem souriau_graphUnitaryFrame_eq_cayley (A : GLSymplectic n ℝ)
    (h1 : IsUnit (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))) :
    (souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      cayley ((J n ℝ * (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
        (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹).map ((↑) : ℝ → ℂ)) := by
  set M : Matrix (n ⊕ n) (n ⊕ n) ℝ := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  set B : Matrix (n ⊕ n) (n ⊕ n) ℝ := J n ℝ * (1 - M) * (1 + M)⁻¹
  have hB : B.IsHermitian := isHermitian_iff_isSymm.2
    (isSymm_J_mul_one_sub_mul_inv_one_add (mem_iff_mem_symplecticGroup.1 A.2) h1)
  have hBc := hB.map_ofReal
  set F : GL (n ⊕ n) ℂ := ((isUnit_iff_isUnit_det _).2 hBc.isUnit_det_one_add_I_smul).unit
  have hF : (F : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 + Complex.I • B.map ((↑) : ℝ → ℂ) :=
    IsUnit.unit_spec _
  -- The frame `1 + i B` is Lagrangian: `(1 + i B)ᴴ (1 + i B) = 1 + B²` is real.
  have hlag : ((F : Matrix (n ⊕ n) (n ⊕ n) ℂ)ᴴ * F).map Complex.im = 0 := by
    have hFF : (F : Matrix (n ⊕ n) (n ⊕ n) ℂ)ᴴ * F = (1 + B * B).map ((↑) : ℝ → ℂ) := by
      rw [hF, conjTranspose_add, conjTranspose_one, conjTranspose_smul, hBc.eq, Complex.star_def,
        Complex.conj_I, Matrix.map_add _ Complex.ofReal_add, Matrix.map_one _ Complex.ofReal_zero
          Complex.ofReal_one]
      rw [show (B * B).map ((↑) : ℝ → ℂ) = B.map (↑) * B.map (↑) from
        map_mul Complex.ofRealHom.mapMatrix B B]
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
      abel
    rw [hFF]
    ext i j
    simp
  let U : unitaryGroup (n ⊕ n) ℂ := ⟨realOrthonormalize F, realOrthonormalize_mem_unitaryGroup hlag⟩
  have hU : (souriau U : Matrix (n ⊕ n) (n ⊕ n) ℂ) = cayley (B.map ((↑) : ℝ → ℂ)) :=
    souriau_eq_cayley_of_coe_eq_mul hB ((coe_realOrthonormalize F).trans (by rw [hF]))
  have hreal : (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (U : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage := by
    have hunit : IsUnit ((√2 : ℝ)⁻¹ • (1 + M)) :=
      (isUnit_iff_isUnit_det _).2 (by
        rw [det_smul]
        exact (IsUnit.mk0 _ (pow_ne_zero _ (inv_ne_zero (Real.sqrt_pos.2 two_pos).ne'))).mul
          ((isUnit_iff_isUnit_det _).1 h1))
    rw [realImage_graphUnitaryFrame, diagonalStraightening_mul_graphFrame_eq_mul h1,
      realImage_mul_map_ofReal _ hunit, realImage_realOrthonormalize, hF]
  rw [souriau_eq_of_realImage_eq hreal, hU]

/-! ### The zero axiom -/

/-- **Graphs transverse to the diagonal.** If the symplectic matrix `A` has no eigenvalue `1`, the
Souriau map of its straightened graph does not have the eigenvalue `1`. -/
theorem not_isRoot_one_charpoly_souriau_graphUnitaryFrame (A : GLSymplectic n ℝ)
    (h1 : IsUnit (((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - 1)) :
    ¬(souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ).charpoly.IsRoot 1 := by
  set M : Matrix (n ⊕ n) (n ⊕ n) ℝ := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hT : IsUnit (diagonalStraightening n).det := by
    have h := congrArg Matrix.det
      (mem_unitaryGroup_iff.1 (diagonalStraightening_mem_unitaryGroup (n := n)))
    rw [det_mul, det_one] at h
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h)
  set G : GL (n ⊕ n) ℂ := ((isUnit_iff_isUnit_det _).2 (by
    rw [det_mul]
    exact hT.mul (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.2)))).unit
  have hG : (G : Matrix (n ⊕ n) (n ⊕ n) ℂ) = diagonalStraightening n * graphFrame M :=
    IsUnit.unit_spec _
  set U : GL (n ⊕ n) ℂ := Unitary.toUnits (graphUnitaryFrame A)
  have hU : (U : Matrix (n ⊕ n) (n ⊕ n) ℂ) = graphUnitaryFrame A := rfl
  obtain ⟨O, hO⟩ := exists_eq_mul_map_ofReal (M := G) (M' := U) (by
    rw [hG, hU, realImage_graphUnitaryFrame])
  -- The imaginary part of `T Γ(A)` is `J (1 - A) / √2`, which is invertible.
  have hImG : (G : Matrix (n ⊕ n) (n ⊕ n) ℂ).map Complex.im = (√2 : ℝ)⁻¹ • (J n ℝ * (1 - M)) := by
    have hs : √2 / 2 = (√2 : ℝ)⁻¹ := by
      field_simp
      simp
    rw [hG, diagonalStraightening_mul_graphFrame]
    ext i j
    simp [hs]
  have hdetO : O.det ≠ 0 := by
    intro h0
    have h := (isUnit_iff_isUnit_det _).1 U.isUnit
    rw [hO, det_mul, show (O.map ((↑) : ℝ → ℂ)).det = (O.det : ℂ) from
      (Complex.ofRealHom.map_det O).symm, h0, Complex.ofReal_zero, mul_zero] at h
    exact not_isUnit_zero h
  have hIm : ((G : Matrix (n ⊕ n) (n ⊕ n) ℂ) * O.map ((↑) : ℝ → ℂ)).map Complex.im =
      (G : Matrix (n ⊕ n) (n ⊕ n) ℂ).map Complex.im * O :=
    map_mul_algebraMap Complex.imLm O _
  rw [isRoot_one_charpoly_souriau_iff, ← hU, hO, hIm, hImG, det_mul, det_smul,
    det_mul]
  have h1' : IsUnit (1 - M) := by rw [← neg_sub]; exact h1.neg
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Real.sqrt_pos.2 two_pos).ne'))
    (mul_ne_zero (isUnit_det_J n ℝ).ne_zero ((isUnit_iff_isUnit_det _).1 h1').ne_zero)) hdetO

/-- **The zero axiom.** A path of symplectic matrices none of which has the eigenvalue `1` has
Conley–Zehnder index zero. -/
theorem conleyZehnderIndex_eq_zero_of_forall_isUnit_sub_one {A B : GLSymplectic n ℝ}
    (γ : Path A B) (h : ∀ t, IsUnit (((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) - 1)) :
    conleyZehnderIndex γ = 0 := by
  rw [conleyZehnderIndex_def, maslovIndex_eq_zero_of_forall_not_isRoot _ fun t ↦ by
    rw [Path.map_coe, Function.comp_apply]
    exact not_isRoot_one_charpoly_souriau_graphUnitaryFrame (γ t) (h t), neg_zero]

/-! ### The one-parameter subgroups of the symplectic group -/

/-- The exponential of an element of the symplectic Lie algebra, as a symplectic matrix. -/
noncomputable def expOfMemSp (X : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ) : GLSymplectic n ℝ :=
  ⟨(isUnit_exp X).unit, mem_iff_mem_symplecticGroup.2 <| by
    rw [IsUnit.unit_spec]
    exact exp_mem_symplecticGroup_of_mem_sp X hX⟩

@[simp]
theorem coe_expOfMemSp (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ) :
    ((expOfMemSp X hX : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = exp X :=
  IsUnit.unit_spec _

/-- The one-parameter subgroup `t ↦ exp (t X)`, `t ∈ [0, 1]`, generated by an element `X` of the
symplectic Lie algebra, as a path of symplectic matrices from the identity to `exp X`. -/
noncomputable def expPath (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ) :
    Path (1 : GLSymplectic n ℝ) (expOfMemSp X hX) where
  toFun t := expOfMemSp ((t : ℝ) • X) ((LieAlgebra.Symplectic.sp n ℝ).smul_mem _ hX)
  continuous_toFun := by
    refine Continuous.subtype_mk (Units.isOpenEmbedding_val.continuous_iff.2 ?_) _
    simp only [Function.comp_def, IsUnit.unit_spec]
    let +nondep : NormedAlgebra ℚ (Matrix (n ⊕ n) (n ⊕ n) ℝ) := .restrictScalars ℚ ℝ _
    exact NormedSpace.exp_continuous.comp (continuous_subtype_val.smul continuous_const)
  source' := by
    refine Subtype.ext (Units.ext ?_)
    simp [expOfMemSp]
  target' := by
    refine Subtype.ext (Units.ext ?_)
    simp [expOfMemSp]

@[simp]
theorem coe_expPath_apply (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ)
    (t : I) : ((expPath X hX t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = exp ((t : ℝ) • X) :=
  IsUnit.unit_spec _

/-! ### The signature axiom -/

/-- The `ℓ²` operator norm of `t J S` is `|t| ‖S‖`, as `J` is orthogonal. -/
private theorem norm_smul_J_mul (t : ℝ) (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    ‖t • (J n ℝ * S)‖ = |t| * ‖S‖ := by
  rw [norm_smul, Real.norm_eq_abs, CStarRing.norm_mem_unitary_mul S (J_mem_unitaryGroup n ℝ)]

/-- `t J S` is invertible for `t ≠ 0` and `S` invertible. -/
private theorem isUnit_smul_J_mul {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hdet : S.det ≠ 0) {t : ℝ}
    (ht : t ≠ 0) : IsUnit (t • (J n ℝ * S)) := by
  rw [isUnit_iff_isUnit_det, det_smul, det_mul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ ht) (mul_ne_zero (isUnit_det_J n ℝ).ne_zero hdet)

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
  rw [norm_smul_J_mul, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg S) ht.2

/-- For `S` invertible with `‖S‖ < π`, the Cayley generator
`J (1 - exp (t J S)) (1 + exp (t J S))⁻¹` is invertible for `0 < t ≤ 1`. -/
private theorem det_cayleyGen_ne_zero {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hdet : S.det ≠ 0)
    (hSπ : ‖S‖ < Real.pi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : t ≠ 0) :
    (J n ℝ * (1 - exp (t • (J n ℝ * S))) * (1 + exp (t • (J n ℝ * S)))⁻¹).det ≠ 0 := by
  have h1 : IsUnit (exp (t • (J n ℝ * S)) - 1) := isUnit_exp_sub_one (isUnit_smul_J_mul hdet ht0)
    (by rw [norm_smul_J_mul, abs_of_nonneg ht.1]; nlinarith [norm_nonneg S, ht.2, Real.pi_pos])
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
    exact isHermitian_iff_isSymm.2 (isSymm_J_mul_one_sub_mul_inv_one_add (hsymp t) (hunit t ht))
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
      continuous_toFun := by
        refine Continuous.subtype_mk (Units.isOpenEmbedding_val.continuous_iff.2 ?_) _
        simp only [Function.comp_def, IsUnit.unit_spec]
        let +nondep : NormedAlgebra ℚ (Matrix (n ⊕ n) (n ⊕ n) ℝ) := .restrictScalars ℚ ℝ _
        exact NormedSpace.exp_continuous.comp
          (((continuous_const.add continuous_subtype_val).div_const _).smul continuous_const)
      source' := by
        refine Subtype.ext (Units.ext ?_)
        simp [expOfMemSp, hX']
      target' := by
        refine Subtype.ext (Units.ext ?_)
        simp [expOfMemSp] }
  have hδ (s : I) : ((δ s : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      exp (((1 + (s : ℝ)) / 2) • X) :=
    IsUnit.unit_spec _
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
  rw [hδ]
  refine isUnit_exp_sub_one (isUnit_smul_J_mul hdet (by linarith [s.2.1])) ?_
  rw [norm_smul_J_mul, abs_of_pos (by linarith [s.2.1])]
  nlinarith [s.2.2, norm_nonneg S]

end GLSymplectic

end TauCeti
