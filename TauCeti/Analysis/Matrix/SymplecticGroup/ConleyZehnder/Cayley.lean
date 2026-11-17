/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
public import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Integral
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Topology.Instances.Matrix

/-!
# The Conley–Zehnder index through the symplectic Cayley transform

For a real `2n × 2n` matrix `A` with `1 + A` invertible, the **symplectic Cayley transform** is
`C(A) = J (1 - A) (1 + A)⁻¹` (`Matrix.symplecticCayley`). When `A` is symplectic, `C(A)` is
symmetric (`Matrix.isHermitian_symplecticCayley`), and it describes the graph of `A` relative to
the diagonal: in the coordinates of `TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder`, the
diagonal straightening `T` carries the graph `Γ(A)` to the graph `{x + i C(A) x}` of `C(A)`
(`TauCeti.diagonalStraightening_mul_graphFrame`). Hence the Souriau map of the unitary graph
frame of `A` is the Cayley transform `(1 + i C(A)) (1 - i C(A))⁻¹`
(`TauCeti.GLSymplectic.coe_souriau_graphUnitaryFrame_eq_cayley`).

The localization axiom of Robbin and Salamon
(`Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley`) then computes the
Conley–Zehnder index of every path of symplectic matrices avoiding the eigenvalue `-1`: it is
minus half the change of the signature of `C`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_symplecticCayley_sub_div_two`). The
index of such a path only depends on its endpoints.

This gives the **normalization of the Conley–Zehnder index**: for every sufficiently small
nondegenerate symmetric matrix `S`, the path `t ↦ exp (t J S)` has index `-signature(S) / 2`
(`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_eq_neg_signature_div_two`). With the
convention `ι_{X_H} ω = dH` of the parent file, `exp (t J S)` is the linearized flow of the
quadratic Hamiltonian `H(x) = xᵀ S x / 2`, so a nondegenerate critical point `p` of a
`C²`-small Hamiltonian, read as a constant orbit, has index `ind_Morse(H, p) - n`. The rotation
case `S = diag (α, α)` is
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`.

For the normalization, write `1 - exp Y = -Y Φ(-Y)` with `Φ(a) = (1 - exp (-a)) / a`
(`mul_oneSubExpNegDivSelf`), which is continuous in `a` (`continuous_oneSubExpNegDivSelf`) and
equals `1` at `a = 0`. Along `Y = t J S` this gives
`C(exp (t J S)) = t b(t)` with `b(t) = S Φ(-t J S) (1 + exp (t J S))⁻¹`. For `S` near `0` the
symmetric matrices `b(t)`, `t ∈ [0, 1]`, are nonsingular, so their signature is constant, and
`b(0) = S / 2`. The neighbourhood of `0` is not made explicit.

## Main definitions

* `Matrix.symplecticCayley`: the symplectic Cayley transform `J (1 - A) (1 + A)⁻¹`.

## Main results

* `Matrix.isHermitian_symplecticCayley`: the symplectic Cayley transform of a symplectic matrix
  is symmetric.
* `TauCeti.GLSymplectic.coe_souriau_graphUnitaryFrame_eq_cayley`: the straightened graph of a
  symplectic matrix away from `-1` is the graph of its symplectic Cayley transform.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_symplecticCayley_sub_div_two`: the
  Conley–Zehnder index of a path avoiding `-1` is minus half the change of the signature of its
  symplectic Cayley transform.
* `TauCeti.GLSymplectic.eventually_conleyZehnderIndex_eq_neg_signature_div_two`: the
  normalization `CZ(exp (t J S)) = -signature(S) / 2` for small nondegenerate symmetric `S`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index through graphs relative to the diagonal, and its
  normalization on `exp (t J S)`).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Section 2.4 (the signature axiom of the Conley–Zehnder index).
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup Complex
open scoped unitInterval

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **symplectic Cayley transform** `J (1 - A) (1 + A)⁻¹` of a real matrix `A`. -/
noncomputable def symplecticCayley (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  J n ℝ * (1 - A) * (1 + A)⁻¹

/-- The definition of the symplectic Cayley transform. -/
theorem symplecticCayley_def (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    symplecticCayley A = J n ℝ * (1 - A) * (1 + A)⁻¹ :=
  (rfl)

/-- The symplectic Cayley transform of the identity vanishes. -/
@[simp]
theorem symplecticCayley_one : symplecticCayley (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 0 := by
  simp [symplecticCayley]

/-- The characterization `C(A) (1 + A) = J (1 - A)` of the symplectic Cayley transform, when
`1 + A` is invertible. -/
theorem symplecticCayley_mul_one_add {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (1 + A).det) :
    symplecticCayley A * (1 + A) = J n ℝ * (1 - A) := by
  rw [symplecticCayley, Matrix.nonsing_inv_mul_cancel_right _ _ h]

/-- **The symplectic Cayley transform of a symplectic matrix is symmetric.** If `Aᵀ J A = J` and
`1 + A` is invertible, then `J (1 - A) (1 + A)⁻¹` is symmetric: both `-(1 - A)ᵀ J (1 + A)` and
`(1 + A)ᵀ J (1 - A)` equal `Aᵀ J - J A`. -/
theorem isHermitian_symplecticCayley {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) (h : IsUnit (1 + A).det) :
    (symplecticCayley A).IsHermitian := by
  have hP : IsUnit (1 + A)ᵀ.det := by rwa [det_transpose]
  have hkey : -((1 - A)ᵀ * J n ℝ) * (1 + A) = (1 + A)ᵀ * (J n ℝ * (1 - A)) := by
    have hJ := SymplecticGroup.mem_iff'.1 hA
    simp only [transpose_sub, transpose_add, transpose_one, Matrix.sub_mul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
      ← Matrix.mul_assoc, hJ]
    abel
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, symplecticCayley, transpose_mul,
    transpose_mul, J_transpose, transpose_nonsing_inv, Matrix.mul_neg]
  calc ((1 + A)ᵀ)⁻¹ * -((1 - A)ᵀ * J n ℝ)
      = ((1 + A)ᵀ)⁻¹ * (-((1 - A)ᵀ * J n ℝ) * (1 + A)) * (1 + A)⁻¹ := by
        rw [Matrix.mul_assoc _ _ (1 + A)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ h]
    _ = J n ℝ * (1 - A) * (1 + A)⁻¹ := by
        rw [hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]

end Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix

/-- The straightened graph frame of `A` is the frame `1 + i C` of the graph of the symplectic
Cayley transform `C` of `A`, followed by a real change of basis. -/
private theorem diagonalStraightening_mul_graphFrame_eq_mul {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (h : IsUnit (1 + A).det) :
    diagonalStraightening n * graphFrame A =
      (1 + Complex.I • (symplecticCayley A).map ((↑) : ℝ → ℂ)) *
        ((√2 : ℝ)⁻¹ • (1 + A)).map ((↑) : ℝ → ℂ) := by
  have hmul : ((symplecticCayley A * (1 + A)).map ((↑) : ℝ → ℂ)) =
      (symplecticCayley A).map (↑) * (1 + A).map (↑) := Matrix.map_mul (f := Complex.ofRealHom)
  have hsmul : ((√2 : ℝ)⁻¹ • (1 + A)).map ((↑) : ℝ → ℂ) =
      ((√2 : ℝ) : ℂ)⁻¹ • (1 + A).map ((↑) : ℝ → ℂ) := by
    ext i j
    simp [mul_add]
  rw [diagonalStraightening_mul_graphFrame, ← symplecticCayley_mul_one_add h, hmul, hsmul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]

namespace GLSymplectic

/-- **The straightened graph of a symplectic matrix away from `-1`.** If `1 + A` is invertible,
the straightened graph `T Γ(A)` is the graph `{x + i C x}` of the symplectic Cayley transform
`C = J (1 - A) (1 + A)⁻¹`, so the Souriau map of its unitary frames is the Cayley transform
`(1 + i C) (1 - i C)⁻¹`. -/
theorem coe_souriau_graphUnitaryFrame_eq_cayley {A : GLSymplectic n ℝ}
    (h : IsUnit (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    (souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      cayley ((symplecticCayley ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map (↑)) := by
  set M : Matrix (n ⊕ n) (n ⊕ n) ℝ := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hC : (symplecticCayley M).IsHermitian :=
    isHermitian_symplecticCayley (mem_iff_mem_symplecticGroup.1 A.2) h
  have hCc := hC.map_ofReal
  set X : GL (n ⊕ n) ℂ :=
    ((Matrix.isUnit_iff_isUnit_det _).2 hCc.isUnit_det_one_add_I_smul).unit with hXdef
  have hX : (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      1 + Complex.I • (symplecticCayley M).map ((↑) : ℝ → ℂ) := by
    rw [hXdef, IsUnit.unit_spec]
  have hXim : ((X : Matrix (n ⊕ n) (n ⊕ n) ℂ)ᴴ * X).map Complex.im = 0 := by
    have hXH : (1 + Complex.I • (symplecticCayley M).map ((↑) : ℝ → ℂ))ᴴ =
        1 - Complex.I • (symplecticCayley M).map ((↑) : ℝ → ℂ) := by
      rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, hCc.eq, star_def, conj_I,
        neg_smul, sub_eq_add_neg]
    have hsq : (symplecticCayley M * symplecticCayley M).map ((↑) : ℝ → ℂ) =
        (symplecticCayley M).map (↑) * (symplecticCayley M).map (↑) :=
      Matrix.map_mul (f := Complex.ofRealHom)
    have hprod : (1 - Complex.I • (symplecticCayley M).map ((↑) : ℝ → ℂ)) *
        (1 + Complex.I • (symplecticCayley M).map ((↑) : ℝ → ℂ)) =
        (1 + symplecticCayley M * symplecticCayley M).map ((↑) : ℝ → ℂ) := by
      rw [Matrix.map_add _ ofReal_add, hsq, Matrix.map_one _ ofReal_zero ofReal_one]
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, smul_sub, smul_smul, I_mul_I, neg_one_smul]
      abel
    rw [hX, hXH, hprod]
    ext i j
    simp
  -- The real orthonormalization of `1 + i C` is a unitary frame `(1 + i C) N` with `N` real.
  let V : unitaryGroup (n ⊕ n) ℂ :=
    ⟨realOrthonormalize X, realOrthonormalize_mem_unitaryGroup hXim⟩
  have hunit : IsUnit ((√2 : ℝ)⁻¹ • (1 + M)) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_smul]
    exact ((IsUnit.mk0 _ (inv_ne_zero (Real.sqrt_pos.2 two_pos).ne')).pow _).mul h
  have hreal : (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (V : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage := by
    rw [realImage_graphUnitaryFrame, diagonalStraightening_mul_graphFrame_eq_mul h,
      realImage_mul_map_ofReal _ hunit, realImage_realOrthonormalize, hX]
  rw [souriau_eq_of_realImage_eq hreal]
  exact souriau_eq_cayley_of_coe_eq_mul hC ((coe_realOrthonormalize X).trans (by rw [hX]))

/-- **The Conley–Zehnder index away from `-1`.** For a path `γ` of symplectic matrices none of
which has the eigenvalue `-1`, the Conley–Zehnder index is minus half the change of the signature
of the symplectic Cayley transforms `J (1 - γ t) (1 + γ t)⁻¹`: it depends only on the endpoints. -/
theorem conleyZehnderIndex_eq_neg_signature_symplecticCayley_sub_div_two {A B : GLSymplectic n ℝ}
    (γ : Path A B)
    (hγ : ∀ t, IsUnit (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    conleyZehnderIndex γ =
      -(signature (symplecticCayley ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) -
        signature (symplecticCayley ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) : ℝ) /
          2 := by
  set m : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t => ((γ t : GL (n ⊕ n) ℝ) : _)
  have hmc : Continuous m := Units.continuous_val.comp (continuous_subtype_val.comp γ.continuous)
  have hc : Continuous fun t => symplecticCayley (m t) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hinv : ContinuousAt (fun t => (1 + m t)⁻¹) t :=
      ((continuous_const.add hmc).continuousAt).matrix_inv (hγ t).ne_zero
    exact ((continuous_const.mul (continuous_const.sub hmc)).continuousAt).mul hinv
  rw [conleyZehnderIndex_def, maslovIndex_eq_signature_sub_of_souriau_eq_cayley _ hc
    (fun t => isHermitian_symplecticCayley (mem_iff_mem_symplecticGroup.1 (γ t).2) (hγ t))
    (fun t => coe_souriau_graphUnitaryFrame_eq_cayley (hγ t))]
  simp only [m, Path.source, Path.target]
  ring

section Normalization

open Filter Topology
open scoped Matrix.Norms.Operator

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- For `S` near `0`, both `1 + exp (t J S)` and `Φ(-t J S) = ∫₀¹ exp (u t J S) du` are invertible
for every `t ∈ [0, 1]`, by compactness of `[0, 1]`. -/
private theorem eventually_isUnit_det_one_add_exp_and_oneSubExpNegDivSelf :
    ∀ᶠ S in 𝓝 (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit (1 + NormedSpace.exp (t • (J n ℝ * S))).det ∧
        IsUnit (oneSubExpNegDivSelf ℝ (-(t • (J n ℝ * S)))).det := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
  have hc : Continuous fun z : Matrix (n ⊕ n) (n ⊕ n) ℝ × ℝ => z.2 • (J n ℝ * z.1) := by
    fun_prop
  have hc₁ : Continuous fun z : Matrix (n ⊕ n) (n ⊕ n) ℝ × ℝ =>
      (1 + NormedSpace.exp (z.2 • (J n ℝ * z.1))).det :=
    (continuous_const.add (NormedSpace.exp_continuous.comp hc)).matrix_det
  have hc₂ : Continuous fun z : Matrix (n ⊕ n) (n ⊕ n) ℝ × ℝ =>
      (oneSubExpNegDivSelf ℝ (-(z.2 • (J n ℝ * z.1)))).det :=
    (continuous_oneSubExpNegDivSelf.comp hc.neg).matrix_det
  have h₁ : (1 + NormedSpace.exp (t • (J n ℝ * 0))).det ≠ 0 := by
    rw [Matrix.mul_zero, smul_zero, NormedSpace.exp_zero, ← two_smul ℝ, det_smul, det_one, mul_one]
    positivity
  have h₂ : (oneSubExpNegDivSelf ℝ (-(t • (J n ℝ * 0)))).det ≠ 0 := by
    rw [Matrix.mul_zero, smul_zero, neg_zero, oneSubExpNegDivSelf_zero, det_one]
    exact one_ne_zero
  filter_upwards [hc₁.continuousAt.eventually_ne h₁, hc₂.continuousAt.eventually_ne h₂]
    with z hz₁ hz₂
  exact ⟨isUnit_iff_ne_zero.2 hz₁, isUnit_iff_ne_zero.2 hz₂⟩

/-- The symplectic Cayley transform of `exp (t J S)` is `t S Φ(-t J S) (1 + exp (t J S))⁻¹`, from
`-Y Φ(-Y) = 1 - exp Y` and `J² = -1`. -/
private theorem symplecticCayley_exp_smul (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) (t : ℝ) :
    symplecticCayley (NormedSpace.exp (t • (J n ℝ * S))) =
      t • (S * oneSubExpNegDivSelf ℝ (-(t • (J n ℝ * S))) *
        (1 + NormedSpace.exp (t • (J n ℝ * S)))⁻¹) := by
  have hJ : J n ℝ * (1 - NormedSpace.exp (t • (J n ℝ * S))) =
      t • (S * oneSubExpNegDivSelf ℝ (-(t • (J n ℝ * S)))) := by
    have h : -(t • (J n ℝ * S)) * oneSubExpNegDivSelf ℝ (-(t • (J n ℝ * S))) =
        1 - NormedSpace.exp (-(-(t • (J n ℝ * S)))) :=
      mul_oneSubExpNegDivSelf _
    rw [neg_neg] at h
    rw [← h, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, J_squared]
    simp
  rw [symplecticCayley, hJ, smul_mul_assoc]

/-- If `S` is symmetric and nonsingular, and `1 + exp (t J S)` and `Φ(-t J S)` are invertible for
`t ∈ [0, 1]`, then the symplectic Cayley transform of `exp (J S)` has the signature of `S`. Along
`t ↦ S Φ(-t J S) (1 + exp (t J S))⁻¹`, which is `S / 2` at
`t = 0` and `C(exp (t J S)) / t` for `t > 0`, the matrices stay symmetric and nonsingular, so the
signature does not change. -/
private theorem signature_symplecticCayley_exp {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hSh : S.IsHermitian) (hSdet : IsUnit S.det)
    (hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 + NormedSpace.exp (t • (J n ℝ * S))).det ∧
      IsUnit (oneSubExpNegDivSelf ℝ (-(t • (J n ℝ * S)))).det)
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, NormedSpace.exp (t • (J n ℝ * S)) ∈ symplecticGroup n ℝ) :
    signature (symplecticCayley (NormedSpace.exp (J n ℝ * S))) = signature S := by
  set b : I → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t =>
    S * oneSubExpNegDivSelf ℝ (-((t : ℝ) • (J n ℝ * S))) *
      (1 + NormedSpace.exp ((t : ℝ) • (J n ℝ * S)))⁻¹ with hb
  have hb₀ : b 0 = (2 : ℝ)⁻¹ • S := by
    have hinv : ((2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹ = (2 : ℝ)⁻¹ • 1 :=
      Matrix.inv_eq_left_inv (by rw [smul_mul_smul, Matrix.mul_one, inv_mul_cancel₀ two_ne_zero,
        one_smul])
    simp only [hb, Set.Icc.coe_zero, zero_smul, neg_zero, oneSubExpNegDivSelf_zero,
      NormedSpace.exp_zero,
      Matrix.mul_one, ← two_smul ℝ (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ), hinv, Matrix.mul_smul]
  have hbh (t : I) : (b t).IsHermitian := by
    by_cases ht : (t : ℝ) = 0
    · rw [show t = 0 from Subtype.ext ht, hb₀, IsHermitian, conjTranspose_smul, hSh.eq,
        star_trivial]
    · have hC := isHermitian_symplecticCayley (hsymp t t.2) (hS t t.2).1
      rw [symplecticCayley_exp_smul] at hC
      rw [show b t = (t : ℝ)⁻¹ • ((t : ℝ) • b t) by rw [smul_smul, inv_mul_cancel₀ ht, one_smul],
        IsHermitian, conjTranspose_smul, hC.eq, star_trivial]
  have hbu (t : I) : IsUnit (b t).det := by
    simp only [hb, det_mul]
    exact (hSdet.mul (hS t t.2).2).mul (isUnit_nonsing_inv_det_iff.2 (hS t t.2).1)
  have hbc : Continuous b := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hY : Continuous fun t : I => (t : ℝ) • (J n ℝ * S) :=
      continuous_subtype_val.smul continuous_const
    have hinv : ContinuousAt (fun t : I => (1 + NormedSpace.exp ((t : ℝ) • (J n ℝ * S)))⁻¹) t :=
      ((continuous_const.add (NormedSpace.exp_continuous.comp hY)).continuousAt).matrix_inv
        (hS t t.2).1.ne_zero
    exact ((continuous_const.mul (continuous_oneSubExpNegDivSelf.comp hY.neg)).continuousAt).mul
      hinv
  have hsig (t : I) : (hbh t).signature = signature (b t) :=
    IsHermitian.signature_map_ofReal (𝕜 := ℝ) (hbh t)
  have hloc : IsLocallyConstant fun t => (hbh t).signature :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun t =>
      IsHermitian.eventually_signature_eq_of_continuousAt hbh hbc.continuousAt (hbu t)
  have h₁ : symplecticCayley (NormedSpace.exp (J n ℝ * S)) = b 1 := by
    simpa [hb] using symplecticCayley_exp_smul S 1
  rw [h₁, ← hsig 1, hloc.apply_eq_of_preconnectedSpace 1 0, hsig 0, hb₀,
    signature_smul_of_pos (by norm_num)]

/-- **Normalization of the Conley–Zehnder index.** For every nondegenerate real symmetric matrix
`S` in some neighbourhood of `0`, a path `γ` of symplectic matrices with `γ t = exp (t J S)` has
Conley–Zehnder index `-signature(S) / 2`. -/
theorem eventually_conleyZehnderIndex_eq_neg_signature_div_two :
    ∀ᶠ S in 𝓝 (0 : Matrix (n ⊕ n) (n ⊕ n) ℝ), S.IsHermitian → IsUnit S.det →
      ∀ {A B : GLSymplectic n ℝ} (γ : Path A B),
        (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
          NormedSpace.exp ((t : ℝ) • (J n ℝ * S))) →
        conleyZehnderIndex γ = -(signature S : ℝ) / 2 := by
  filter_upwards [eventually_isUnit_det_one_add_exp_and_oneSubExpNegDivSelf]
    with S hS hSh hSdet A B γ hγ
  have hγu : ∀ t : I, IsUnit (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det :=
    fun t => by rw [hγ t]; exact (hS t t.2).1
  have hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      NormedSpace.exp (t • (J n ℝ * S)) ∈ symplecticGroup n ℝ := fun t ht => by
    simpa [hγ ⟨t, ht⟩] using mem_iff_mem_symplecticGroup.1 (γ ⟨t, ht⟩).2
  have hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 1 := by
    rw [← γ.source, hγ 0]
    simp
  have hB : ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = NormedSpace.exp (J n ℝ * S) := by
    rw [← γ.target, hγ 1]
    simp
  rw [conleyZehnderIndex_eq_neg_signature_symplecticCayley_sub_div_two γ hγu, hA,
    symplecticCayley_one, signature_zero, hB, signature_symplecticCayley_exp hSh hSdet hS hsymp]
  simp

end Normalization

end GLSymplectic

end TauCeti
