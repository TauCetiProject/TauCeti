/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
public import TauCeti.LinearAlgebra.SymplecticGroup.Cayley
import TauCeti.Topology.Instances.Matrix

/-!
# The Conley–Zehnder index through the symplectic Cayley transform

For a symplectic matrix `A` with `1 + A` invertible, the symmetric **symplectic Cayley
transform** `C(A) = J (1 - A) (1 + A)⁻¹` (`Matrix.symplecticCayley`, in
`TauCeti.LinearAlgebra.SymplecticGroup.Cayley`) describes the graph of `A` relative to
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

The normalization of the Conley–Zehnder index on the paths `t ↦ exp (t J S)` for small
nondegenerate symmetric `S` is proved in
`TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Normalization`, with an explicit bound on
`S`. The rotation case `S = diag (α, α)` is
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`.

## Main results

* `TauCeti.GLSymplectic.coe_souriau_graphUnitaryFrame_eq_cayley`: the straightened graph of a
  symplectic matrix away from `-1` is the graph of its symplectic Cayley transform.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_symplecticCayley_sub_div_two`: the
  Conley–Zehnder index of a path avoiding `-1` is minus half the change of the signature of its
  symplectic Cayley transform.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index through graphs relative to the diagonal).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Section 2.4 (the signature axiom of the Conley–Zehnder index).
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup Complex
open scoped unitInterval

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
  have hsmul : ((√2 : ℝ)⁻¹ • (1 + A)).map ((↑) : ℝ → ℂ) =
      ((√2 : ℝ) : ℂ)⁻¹ • (1 + A).map ((↑) : ℝ → ℂ) := by
    ext i j
    simp [mul_add]
  rw [diagonalStraightening_mul_graphFrame, ← symplecticCayley_mul_one_add h, map_ofReal_mul, hsmul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]

namespace GLSymplectic

open scoped MatrixOrder Matrix.Norms.L2Operator in
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
    isHermitian_iff_isSymm.2 (isSymm_symplecticCayley (mem_iff_mem_symplecticGroup.1 A.property) h)
  set N : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
    ((graphFrame M)ᴴ * graphFrame M).map Complex.re ^ (-(1 / 2) : ℝ)
  refine souriau_eq_cayley_of_coe_eq_mul hC (M := (√2 : ℝ)⁻¹ • (1 + M) * N) ?_
  rw [coe_graphUnitaryFrame, diagonalStraightening_mul_graphFrame_eq_mul h, Matrix.mul_assoc]
  exact congrArg ((1 + Complex.I • (symplecticCayley M).map ((↑) : ℝ → ℂ)) * ·)
    (map_ofReal_mul _ _).symm

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
  have hmc : Continuous m := Units.continuous_val.comp (continuous_subtypeVal.comp γ.continuous)
  have hc : Continuous fun t => symplecticCayley (m t) := by
    simp only [symplecticCayley_def]
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hinv : ContinuousAt (fun t => (1 + m t)⁻¹) t :=
      ((continuous_const.add hmc).continuousAt).matrix_inv (hγ t).ne_zero
    exact ((continuous_const.mul (continuous_const.sub hmc)).continuousAt).mul hinv
  rw [conleyZehnderIndex_def, maslovIndex_eq_signature_sub_of_souriau_eq_cayley _ hc
    (fun t => isHermitian_iff_isSymm.2
      (isSymm_symplecticCayley (mem_iff_mem_symplecticGroup.1 (γ t).property) (hγ t)))
    (fun t => coe_souriau_graphUnitaryFrame_eq_cayley (hγ t))]
  simp only [m, Path.source, Path.target]
  ring

end GLSymplectic

end TauCeti
