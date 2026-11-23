/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Homotopy.Product
import TauCeti.Analysis.Complex.Circle
import TauCeti.LinearAlgebra.Matrix.ConjTranspose

/-!
# The Conley–Zehnder index of a path of symplectic matrices

Following Robbin and Salamon, the Conley–Zehnder index of a path `Ψ : [0, 1] → Sp(2n, ℝ)` is the
Maslov index of its path of graphs relative to the diagonal, in `ℝ^{2n} × ℝ^{2n}` with the
symplectic form `(-ω) ⊕ ω`. We use the opposite sign,

`CZ(Ψ) = -μ_RS(Γ(Ψ), Δ)`,

so that a small positive rotation of `ℝ²` has index `-1`. This is the sign convention in which
the Floer complex of a small Hamiltonian `H` is graded like the Morse complex of `-H`.

In `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`, with the identification of
`TauCeti.Analysis.Matrix.SymplecticGroup.Graph`, the graph of `A` is the real span `Γ(A)` of the
columns of the graph frame `Matrix.graphFrame A`, and the diagonal is `Γ(1) = {(conj z, z)}`.
The unitary matrix `T = (1/√2) [[1, 1], [i, -i]]` (`TauCeti.diagonalStraightening`) sends
`(conj z, z)` to `√2 (Re z, Im z)`, so it carries the diagonal onto the real points `ℝ^{n ⊕ n}`
(`TauCeti.realImage_diagonalStraightening_mul_graphFrame_one`). The index relative to the diagonal
is therefore the index of the path `T Γ(Ψ t)` relative to `ℝ^{n ⊕ n}`, which is
`Matrix.UnitaryGroup.maslovIndex`, defined on paths of unitary frames. The graph of a symplectic
matrix is Lagrangian (`Matrix.map_im_conjTranspose_graphFrame_mul_graphFrame`), so the real
orthonormalization of its graph frame is unitary
(`Matrix.GeneralLinearGroup.realOrthonormalize_mem_unitaryGroup`). Together with `T` this gives a
continuous unitary frame of `T Γ(A)` (`TauCeti.GLSymplectic.graphUnitaryFrame`,
`TauCeti.GLSymplectic.realImage_graphUnitaryFrame`), and the index does not depend on the choice
of unitary frames (`Matrix.UnitaryGroup.souriau_eq_of_realImage_eq`).

The **Conley–Zehnder index** `TauCeti.GLSymplectic.conleyZehnderIndex` is defined for every path,
as a real number, and it does not depend on the choice of unitary frames of the graphs
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_maslovIndex`). It inherits from the Maslov index
the invariance under homotopies fixing the endpoints, additivity under catenation, and the change
of sign under reversal.

It is additive under direct sums (`TauCeti.GLSymplectic.conleyZehnderIndex_sum`): the graph of
`A ⊕ B` is the product of the graphs of `A` and `B`, in the regrouped coordinates of
`Matrix.symplecticSum`, so the direct sum of unitary frames of the two straightened graphs frames
the straightened graph of the sum, and the Maslov index of such a direct sum of frames is the sum
of the indices (`Matrix.UnitaryGroup.maslovIndex_eq_add_of_coe_eq_symplecticSum`).

On a loop `γ` of symplectic matrices it is `-2 μ(γ)`, where `μ` is the Maslov index of loops
`TauCeti.GLSymplectic.maslovIndex`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_two_mul_maslovIndex`). Indeed the unitary graph
frames then form a loop, whose Maslov index is twice the degree of their determinants; the
squares of these determinants are, up to a constant factor, the determinant phases of the graph
frames, whose degree is `2 μ(γ)` (`TauCeti.GLSymplectic.maslovIndex_graphLoop`). Since `φ γ` is
homotopic to the catenation of `t ↦ φ t A` and `γ`, this gives the **loop axiom**: multiplying a
path `γ` by a loop `φ` based at the identity, a change of symplectic trivialization along a loop,
changes the index by `-2 μ(φ)` (`TauCeti.GLSymplectic.conleyZehnderIndex_mul`). For instance the
full rotation `t ↦ e^{2π i t}` of `ℝ²` has `μ = 1` and Conley–Zehnder index `-2`.

Inverting a path pointwise negates the index, `CZ(t ↦ Ψ(t)⁻¹) = -CZ(Ψ)`
(`TauCeti.GLSymplectic.conleyZehnderIndex_inv`). The graph of `A⁻¹` is the image of the graph of
`A` under the involution `(u, v) ↦ (conj v, conj u)` of `ℂⁿ × ℂⁿ`
(`Matrix.graphFrame_mul_map_ofReal_of_mul_eq_one`), which is anti-symplectic for `Im ⟪·, ·⟫` and
fixes the diagonal, and `T` turns it into complex conjugation, which negates the Maslov index of
paths of unitary frames (`Matrix.UnitaryGroup.maslovIndex_map_map_star`). Consequently, for a path
`Ψ` from `1` to `B`, the reflected path `t ↦ Ψ(1 - t) B⁻¹` has index `-CZ(Ψ)`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_of_apply_eq_symm_mul_inv`). If `Ψ` is the
linearized flow along a one-periodic orbit `x` of a Hamiltonian `H`, then by periodicity
`Ψ(-t) = Ψ(1 - t) Ψ(1)⁻¹`, so the reflected path is the linearized flow of the reflected
Hamiltonian `H∨_t = -H_{-t}` along the reflected orbit `x∨(t) = x(-t)`, in the reflected
trivialization: this is the index identity `CZ(H∨, x∨) = -CZ(H, x)` used to compare the Floer
theories of `H` and `H∨`.

On a path of realified diagonal unitary matrices `diag (e^{i θ_j(t)})` it is computed explicitly
(`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_of_diagonal`): each angle
contributes `-(c(θ_j 1) - c(θ_j 0))`, where `c(θ) = ⌊θ / 2π⌋ + ⌈θ / 2π⌉`. Thus each multiple of
`2π` crossed by `θ_j` counts twice, with sign, since there the graph meets the diagonal in a real
plane, and a multiple of `2π` at an endpoint counts once. The graph of the realification of a
unitary matrix `W` is framed in these coordinates by
`(1/2) [[1 + W, -i (1 - W)], [i (1 - W), 1 + W]]`, whose Souriau map is `fromBlocks W 0 0 W` when
`W` is symmetric
(`TauCeti.GLSymplectic.coe_souriau_graphUnitaryFrame_ofUnitary_of_transpose_eq`). In particular the
rotation path `t ↦ diag (e^{i α_j t})` with `|α_j| < 2π`, which is `exp (t J S)` with
`S = diag (α, α)`, has index `-∑ j, sign α_j = -signature(S) / 2`
(`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`). For the
form `ω(x, y) = xᵀ J y` of `TauCeti.Analysis.Matrix.SymplecticGroup.Graph`, `exp (t J S)` is the
flow of `H(x) = xᵀ S x / 2` with `ι_{X_H} ω = dH`. For `n = 1` this says that a counterclockwise
rotation path `t ↦ e^{i α t}`, `0 < α < 2π`, has index `-1`, and a clockwise one has index `1`.
The standard form `dx ∧ dy` is `-xᵀ J y`, and for it the flow of `H = ε (x² + y²) / 2` with
`ι_{X_H} (dx ∧ dy) = dH` is clockwise, with index `1`.

## Main definitions

* `TauCeti.diagonalStraightening`: the unitary matrix `(1/√2) [[1, 1], [i, -i]]` carrying the
  diagonal onto the real points.
* `TauCeti.GLSymplectic.graphUnitaryFrame`: a continuous unitary frame of `T Γ(A)`.
* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a path of symplectic
  matrices.

## Main results

* `TauCeti.diagonalStraightening_mul_graphFrame`: the straightened graph frame of a real matrix
  `A` is `(1/√2) ((1 + A) + i J (1 - A))`.
* `TauCeti.map_star_diagonalStraightening_mul_graphFrame_sub`: the imaginary part of the
  straightened graph frame, `conj (T Γ(A)) - T Γ(A) = i √2 J (A - 1)`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_maslovIndex`: the index is minus the Maslov
  index of any path of unitary frames of the straightened graphs.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopic`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_trans`, `TauCeti.GLSymplectic.conleyZehnderIndex_symm`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_refl`: homotopy invariance, catenation, reversal and
  the constant path.
* `TauCeti.GLSymplectic.conleyZehnderIndex_inv`: inverting a path negates the index.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_of_apply_eq_symm_mul_inv`: the reflected path
  `t ↦ Ψ(1 - t) Ψ(1)⁻¹` of a path from `1` has the opposite index.
* `TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_of_diagonal`: the index of a
  path of diagonal unitary matrices.
* `TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`: the
  normalization on rotations, `CZ = -∑ j, sign α_j`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_sum`: the direct-sum axiom.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_two_mul_maslovIndex`: the index of a loop is
  `-2 μ`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_mul`: the loop axiom, `CZ(φ γ) = CZ(γ) - 2 μ(φ)`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the Maslov index of the graph relative to the diagonal).
* C. Conley and E. Zehnder, *Morse-type index theory for flows and periodic solutions for
  Hamiltonian equations*, Comm. Pure Appl. Math. **37** (1984), 207–253.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999 (the axioms and the normalization of the Conley–Zehnder index,
  among them the product and loop axioms).
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup Complex
open scoped unitInterval ComplexConjugate

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

variable (n) in
/-- The **diagonal straightening** `T = (1/√2) [[1, 1], [i, -i]]` of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`. It is
unitary and sends the point `(conj z, z)` of the diagonal `Γ(1)` to `√2 (Re z, Im z)`, so it
carries the diagonal onto the real points. -/
noncomputable def diagonalStraightening : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ((√2 : ℝ) : ℂ)⁻¹ • fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))

omit [Fintype n] in
theorem diagonalStraightening_def :
    diagonalStraightening n =
      ((√2 : ℝ) : ℂ)⁻¹ • fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1)) :=
  (rfl)

private theorem sqrt_two_ne_zero : ((√2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'

private theorem sqrt_two_mul_sqrt_two : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt zero_le_two

private theorem inv_sqrt_two : ((√2 : ℝ) : ℂ)⁻¹ = ((√2 : ℝ) : ℂ) * (2 : ℂ)⁻¹ := by
  field_simp
  rw [sq, sqrt_two_mul_sqrt_two]

omit [Fintype n] in
/-- The real scalar matrix `√2 • 1`, viewed as a complex matrix. -/
private theorem map_ofReal_sqrt_two_smul_one :
    ((√2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) = ((√2 : ℝ) : ℂ) • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- The real matrix `√2 • 1` is invertible. -/
private theorem isUnit_sqrt_two_smul_one :
    IsUnit ((√2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.mk0 _ (Real.sqrt_pos.2 two_pos).ne').map _

/-- The unnormalized straightening `[[1, 1], [i, -i]]` has orthogonal rows of norm `√2`. -/
private theorem straightening_mul_conjTranspose :
    fromBlocks (1 : Matrix n n ℂ) 1 (Complex.I • 1) (-(Complex.I • 1)) *
      (fromBlocks (1 : Matrix n n ℂ) 1 (Complex.I • 1) (-(Complex.I • 1)))ᴴ =
        (2 : ℂ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
  simp only [conjTranspose_one, conjTranspose_smul, conjTranspose_neg, star_def, conj_I,
    Matrix.mul_one, Matrix.mul_smul, smul_smul, neg_smul, Matrix.mul_neg, neg_neg, I_mul_I,
    smul_zero]
  congr 1 <;> match_scalars <;> norm_num

/-- The diagonal straightening is unitary. -/
theorem diagonalStraightening_mem_unitaryGroup :
    diagonalStraightening n ∈ unitaryGroup (n ⊕ n) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonalStraightening_def,
    conjTranspose_smul, smul_mul_smul, straightening_mul_conjTranspose]
  simp [smul_smul, ← mul_inv, sqrt_two_mul_sqrt_two]

/-- **The straightened graph frame.** The diagonal straightening `T` times the graph frame of a
real matrix `A` is `(1/√2) ((1 + A) + i J (1 - A))`: its real and imaginary parts are
`(1 + A) / √2` and `J (1 - A) / √2`. -/
theorem diagonalStraightening_mul_graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    diagonalStraightening n * graphFrame A = ((√2 : ℝ) : ℂ)⁻¹ •
      ((1 + A).map ((↑) : ℝ → ℂ) + Complex.I • (J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ)) := by
  -- Compare the two matrices on the real basis vectors.
  refine ext_of_mulVec_single fun j => ?_
  have hj : (Pi.single j 1 : n ⊕ n → ℂ) = fun k => ((Pi.single j 1 : n ⊕ n → ℝ) k : ℂ) := by
    ext k
    by_cases hk : k = j <;> simp [hk]
  rw [hj]
  generalize (Pi.single j 1 : n ⊕ n → ℝ) = x
  have hmap (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
      M.map ((↑) : ℝ → ℂ) *ᵥ (fun k => (x k : ℂ)) = fun i => ((M *ᵥ x) i : ℂ) :=
    funext fun i => (RingHom.map_mulVec ofRealHom M x i).symm
  rw [← Matrix.mulVec_mulVec, graphFrame_mulVec, diagonalStraightening_def]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, hmap]
  rw [← Matrix.mulVec_mulVec, J]
  ext (i | i) <;>
    simp [Matrix.smul_mulVec, fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
      Matrix.sub_mulVec, -Matrix.mulVec_mulVec]
  · ring
  · linear_combination (-(x (.inr i) : ℂ) - ((A *ᵥ x) (.inr i) : ℂ)) * I_sq

/-- The diagonal straightening of the graph frame of the identity, whose columns span the
diagonal, is the real matrix `√2 • 1`. -/
theorem diagonalStraightening_mul_graphFrame_one :
    diagonalStraightening n * graphFrame 1 =
      ((√2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) := by
  rw [diagonalStraightening_mul_graphFrame, sub_self, Matrix.mul_zero, ← two_smul ℝ 1,
    map_ofReal_sqrt_two_smul_one]
  ext i j
  by_cases hij : i = j <;> simp [hij, inv_sqrt_two]

/-- The complex conjugate of the diagonal straightening exchanges its two columns of blocks:
`T P = conj T`, where `P` exchanges the two factors of `ℂⁿ × ℂⁿ`. So `T` turns the involution
`(u, v) ↦ (conj v, conj u)` of `ℂⁿ × ℂⁿ`, which fixes the diagonal, into complex conjugation, which
fixes the real points. -/
private theorem diagonalStraightening_mul_submatrix_swap (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    diagonalStraightening n * M.submatrix Sum.swap id = (diagonalStraightening n).map star * M := by
  have hT : (diagonalStraightening n).map star =
      ((√2 : ℝ) : ℂ)⁻¹ • fromBlocks 1 1 (-(Complex.I • 1)) (Complex.I • 1) := by
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [diagonalStraightening_def, hij]
  rw [hT, diagonalStraightening_def, Matrix.smul_mul, Matrix.smul_mul, ← fromBlocks_toBlocks M,
    fromBlocks_submatrix_sum_swap_left, submatrix_id_id, fromBlocks_multiply, fromBlocks_multiply]
  congr 2 <;> simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.neg_mul] <;> abel

/-- **The diagonal straightening carries the diagonal onto the real points**: the image under it
of the graph `Γ(1)` of the identity is `ℝ^{n ⊕ n}`. -/
theorem realImage_diagonalStraightening_mul_graphFrame_one :
    (diagonalStraightening n * graphFrame 1).realImage = realSubspace (n ⊕ n) := by
  rw [diagonalStraightening_mul_graphFrame_one, realImage_map_ofReal isUnit_sqrt_two_smul_one]

omit [Fintype n] in
/-- The diagonal straightening of `ℂ^{(n ⊕ m) ⊕ (n ⊕ m)}` is the symplectic direct sum of the
diagonal straightenings of `ℂ^{n ⊕ n}` and of `ℂ^{m ⊕ m}`. -/
theorem diagonalStraightening_sum {m : Type*} [DecidableEq m] :
    diagonalStraightening (n ⊕ m) =
      symplecticSum (diagonalStraightening n) (diagonalStraightening m) := by
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [diagonalStraightening_def, symplecticSum_def, Equiv.sumSumSumComm, ← fromBlocks_one]

/-- The imaginary part of the straightened graph frame: for every real matrix `A` on
`ℝ^{n ⊕ n}`, `conj (T Γ(A)) - T Γ(A) = i √2 J (A - 1)`, where `T` is the diagonal straightening
and `Γ(A)` the graph frame. So the straightened graph meets the real points nontrivially, that
is, the graph of `A` meets the diagonal, exactly when `A` has the eigenvalue `1`. -/
theorem map_star_diagonalStraightening_mul_graphFrame_sub (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (diagonalStraightening n * graphFrame A).map star - diagonalStraightening n * graphFrame A =
      (Complex.I * ((√2 : ℝ) : ℂ)) • (J n ℝ * (A - 1)).map ((↑) : ℝ → ℂ) := by
  conv_rhs => rw [← fromBlocks_toBlocks (A - 1), J, fromBlocks_multiply]
  rw [diagonalStraightening_def, graphFrame_def, Matrix.smul_mul, fromBlocks_multiply]
  ext (i | i) (j | j) <;>
  simp [Matrix.one_apply, Complex.ext_iff, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂] <;>
  split_ifs <;> simp <;> ring

namespace GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The graph frame of a symplectic matrix, as an invertible matrix. -/
private noncomputable def graphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  ((Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.property))).unit

private theorem coe_graphFrameUnit (A : GLSymplectic n ℝ) :
    (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  IsUnit.unit_spec _

open scoped Matrix.Norms.L2Operator in
private theorem continuous_graphFrameUnit : Continuous (graphFrameUnit (n := n)) := by
  have hF : Continuous fun A : GLSymplectic n ℝ ↦
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtypeVal)
  exact Units.isOpenEmbedding_val.continuous_iff.2 (hF.congr fun A ↦ (coe_graphFrameUnit A).symm)

/-- The **unitary graph frame** of a symplectic matrix `A`: the diagonal straightening `T` times
the real orthonormalization of the graph frame. It is a unitary frame of the image `T Γ(A)` of the
graph of `A` (`TauCeti.GLSymplectic.realImage_graphUnitaryFrame`), and depends continuously on `A`
(`TauCeti.GLSymplectic.continuous_graphUnitaryFrame`). -/
noncomputable def graphUnitaryFrame (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  ⟨diagonalStraightening n * realOrthonormalize (graphFrameUnit A),
    mul_mem diagonalStraightening_mem_unitaryGroup (realOrthonormalize_mem_unitaryGroup (by
      rw [coe_graphFrameUnit]
      exact map_im_conjTranspose_graphFrame_mul_graphFrame
        (mem_iff_mem_symplecticGroup.1 A.property)))⟩

/-- **The unitary graph frame frames the straightened graph**: its columns span the image
`T Γ(A)` of the graph of `A` under the diagonal straightening. -/
theorem realImage_graphUnitaryFrame (A : GLSymplectic n ℝ) :
    (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (diagonalStraightening n *
        graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage := by
  rw [graphUnitaryFrame, realImage_mul, realImage_mul, realImage_realOrthonormalize,
    coe_graphFrameUnit]

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- The unitary graph frame is the straightened graph frame `T Γ(A)` followed by the real
change of basis `Re (Γ(A)ᴴ Γ(A)) ^ (-1/2)`. -/
theorem coe_graphUnitaryFrame (A : GLSymplectic n ℝ) :
    (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalStraightening n * graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        (((graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ *
          graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map Complex.re ^
            (-(1 / 2) : ℝ)).map ((↑) : ℝ → ℂ) := by
  rw [graphUnitaryFrame, Subtype.coe_mk, coe_realOrthonormalize, coe_graphFrameUnit,
    Matrix.mul_assoc]

/-- The unitary graph frame depends continuously on the symplectic matrix. -/
theorem continuous_graphUnitaryFrame : Continuous (graphUnitaryFrame (n := n)) :=
  Continuous.subtype_mk (continuous_const.mul (Units.continuous_val.comp
    (continuous_realOrthonormalize continuous_graphFrameUnit))) _

/-- The unitary graph frame of `A` is the straightened graph frame `T Γ(A)` times a positive
definite real matrix, the real orthonormalization. -/
theorem exists_posDef_coe_graphUnitaryFrame (A : GLSymplectic n ℝ) :
    ∃ P : Matrix (n ⊕ n) (n ⊕ n) ℝ, P.PosDef ∧
      (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
        diagonalStraightening n * graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
          P.map ((↑) : ℝ → ℂ) := by
  obtain ⟨P, hP, h⟩ := exists_posDef_coe_realOrthonormalize (graphFrameUnit A)
  exact ⟨P, hP, by rw [graphUnitaryFrame, Subtype.coe_mk, h, coe_graphFrameUnit, Matrix.mul_assoc]⟩

/-- At the identity, the unitary graph frame frames the real points: the Souriau map of the
straightened diagonal is the identity. -/
theorem souriau_graphUnitaryFrame_one :
    souriau (graphUnitaryFrame (1 : GLSymplectic n ℝ)) = 1 := by
  have h : (graphUnitaryFrame (1 : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      ((1 : unitaryGroup (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage := by
    simpa [realImage_graphUnitaryFrame, realImage_diagonalStraightening_mul_graphFrame_one]
      using (realImage_map_ofReal (isUnit_one (M := Matrix (n ⊕ n) (n ⊕ n) ℝ))).symm
  rw [souriau_eq_of_realImage_eq h]
  exact Subtype.ext (by simp)

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices: minus the Robbin–Salamon
Maslov index of its path of graphs relative to the diagonal, computed as the Maslov index of the
path `t ↦ T Γ(γ t)` relative to the real points, framed by the unitary graph frames. -/
noncomputable def conleyZehnderIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  -Matrix.UnitaryGroup.maslovIndex (γ.map continuous_graphUnitaryFrame)

theorem conleyZehnderIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ = -Matrix.UnitaryGroup.maslovIndex (γ.map continuous_graphUnitaryFrame) :=
  (rfl)

/-- **The index depends only on the path of graphs.** For any path `δ` of unitary frames of the
straightened graphs `T Γ(γ t)`, the Conley–Zehnder index of `γ` is minus the Maslov index of `δ`.
-/
theorem conleyZehnderIndex_eq_neg_maslovIndex {A B : GLSymplectic n ℝ} (γ : Path A B)
    {U V : unitaryGroup (n ⊕ n) ℂ} (δ : Path U V)
    (h : ∀ t, (δ t : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage = (diagonalStraightening n *
      graphFrame ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage) :
    conleyZehnderIndex γ = -Matrix.UnitaryGroup.maslovIndex δ := by
  rw [conleyZehnderIndex, maslovIndex_eq_of_souriau_eq _ δ fun t ↦
    souriau_eq_of_realImage_eq ((realImage_graphUnitaryFrame (γ t)).trans (h t).symm)]

/-- The Conley–Zehnder index only depends on the path as a function of time, not on the way its
endpoints are written. -/
theorem conleyZehnderIndex_congr {A B A' B' : GLSymplectic n ℝ} (γ : Path A B) (γ' : Path A' B')
    (h : ∀ t, γ t = γ' t) : conleyZehnderIndex γ = conleyZehnderIndex γ' := by
  rw [conleyZehnderIndex, conleyZehnderIndex, maslovIndex_eq_of_souriau_eq
    (γ.map continuous_graphUnitaryFrame) (γ'.map continuous_graphUnitaryFrame) fun t ↦ by
      rw [Path.map_coe, Path.map_coe, Function.comp_apply, Function.comp_apply, h t]]

/-- **Homotopy invariance.** Paths of symplectic matrices that are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex, conleyZehnderIndex,
    Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_graphUnitaryFrame⟩)]

/-- The constant path has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl (A : GLSymplectic n ℝ) :
    conleyZehnderIndex (Path.refl A) = 0 := by
  have h : (Path.refl A).map continuous_graphUnitaryFrame = Path.refl (graphUnitaryFrame A) := by
    ext
    simp
  rw [conleyZehnderIndex, h, Matrix.UnitaryGroup.maslovIndex_refl, neg_zero]

/-- **Catenation.** The Conley–Zehnder index is additive under concatenation of paths. -/
@[simp]
theorem conleyZehnderIndex_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    conleyZehnderIndex (γ₁.trans γ₂) = conleyZehnderIndex γ₁ + conleyZehnderIndex γ₂ := by
  rw [conleyZehnderIndex, Path.map_trans, Matrix.UnitaryGroup.maslovIndex_trans, conleyZehnderIndex,
    conleyZehnderIndex, neg_add]

/-- Reversing a path negates its Conley–Zehnder index. -/
@[simp]
theorem conleyZehnderIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ.symm = -conleyZehnderIndex γ := by
  rw [conleyZehnderIndex, ← Path.map_symm, Matrix.UnitaryGroup.maslovIndex_symm,
    conleyZehnderIndex]

/-! ### Inverse and reflected paths -/

/-- **The inverse path.** Inverting a path of symplectic matrices pointwise negates its
Conley–Zehnder index, `CZ(t ↦ Ψ(t)⁻¹) = -CZ(Ψ)`: the graphs of the inverses are the images of the
graphs under an anti-symplectic involution of `ℂⁿ × ℂⁿ` fixing the diagonal. -/
@[simp]
theorem conleyZehnderIndex_inv {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ.inv = -conleyZehnderIndex γ := by
  rw [conleyZehnderIndex_eq_neg_maslovIndex γ.inv
      ((γ.map continuous_graphUnitaryFrame).map continuous_map_star) fun t ↦ ?_,
    maslovIndex_map_map_star, conleyZehnderIndex]
  set A' : GL (n ⊕ n) ℝ := (γ t).val
  have hinv : (((γ.inv t : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
      (A' : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 1 := by
    rw [Path.inv_apply, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Path.map_coe, Function.comp_apply, map_star_coe]
  refine (realImage_map_star_eq_of_realImage_eq (realImage_graphUnitaryFrame (γ t))).trans ?_
  conv_rhs => rw [← realImage_mul_map_ofReal _ (Units.isUnit A'), Matrix.mul_assoc,
    graphFrame_mul_map_ofReal_of_mul_eq_one hinv, diagonalStraightening_mul_submatrix_swap]
  simp only [A', map_star_eq_map_starRingEnd, Matrix.map_mul]

/-- **The reflected path.** For a path `Ψ` of symplectic matrices from `A` to `B`, the reflected
path `t ↦ Ψ(1 - t) B⁻¹` from `1` to `A B⁻¹` has the Conley–Zehnder index of the path
`t ↦ A Ψ(t)⁻¹`: the two paths are homotopic relative to their endpoints. -/
theorem conleyZehnderIndex_eq_of_apply_eq_symm_mul_inv {A B C : GLSymplectic n ℝ}
    (γ : Path A B) (δ : Path 1 C) (hδ : ∀ t, δ t = γ (σ t) * B⁻¹) :
    conleyZehnderIndex δ = conleyZehnderIndex ((Path.refl A).mul γ.inv) := by
  have hC : C = A * B⁻¹ := by simpa using hδ 1
  subst hC
  -- The path `t ↦ A Ψ(t)⁻¹`, written from `1`.
  let ι : Path 1 (A * B⁻¹) := ((Path.refl A).mul γ.inv).cast (mul_inv_cancel A).symm rfl
  -- The homotopy `(s, t) ↦ Ψ(s (1 - t)) Ψ(s + (1 - s) t)⁻¹`, with `s + (1 - s) t` written as
  -- `σ (σ s σ t)`.
  have H : Path.Homotopy ι δ :=
    { toFun := fun p ↦ γ (p.1 * σ p.2) * (γ (σ (σ p.1 * σ p.2)))⁻¹
      continuous_toFun := by fun_prop
      map_zero_left := fun t ↦ by simp [ι, Path.mul_apply]
      map_one_left := fun t ↦ by simp [hδ]
      prop' := fun s t ht ↦ by
        rcases ht with rfl | ht
        · simp [ι]
        · rw [Set.mem_singleton_iff] at ht
          subst ht
          simp [ι] }
  exact (conleyZehnderIndex_eq_of_homotopic ⟨H⟩).symm.trans
    (conleyZehnderIndex_congr ι _ fun _ ↦ rfl)

/-- **The reflection identity.** If `Ψ` is a path of symplectic matrices from the identity to `B`,
the reflected path `t ↦ Ψ(1 - t) B⁻¹` from the identity to `B⁻¹` has the opposite Conley–Zehnder
index. For the linearized flow `Ψ` along a one-periodic orbit `x` of a Hamiltonian `H`, the
reflected path is the linearized flow of `H∨_t = -H_{-t}` along `x∨(t) = x(-t)`, since
`Ψ(-t) = Ψ(1 - t) Ψ(1)⁻¹` by periodicity, so this reads `CZ(H∨, x∨) = -CZ(H, x)`. -/
theorem conleyZehnderIndex_eq_neg_of_apply_eq_symm_mul_inv {B C : GLSymplectic n ℝ}
    (γ : Path 1 B) (δ : Path 1 C) (hδ : ∀ t, δ t = γ (σ t) * B⁻¹) :
    conleyZehnderIndex δ = -conleyZehnderIndex γ := by
  rw [conleyZehnderIndex_eq_of_apply_eq_symm_mul_inv γ δ hδ, ← conleyZehnderIndex_inv γ]
  exact conleyZehnderIndex_congr _ _ fun t ↦ by simp [Path.mul_apply]

/-! ### Paths of unitary matrices -/

/-- The straightened graph frame of the realification of a complex matrix `W` is
`(1/√2) [[1 + W, -i (1 - W)], [i (1 - W), 1 + W]]`. -/
private theorem diagonalStraightening_mul_graphFrame_realify (W : Matrix n n ℂ) :
    diagonalStraightening n * graphFrame W.realify = ((√2 : ℝ) : ℂ)⁻¹ •
      fromBlocks (1 + W) (-(Complex.I • (1 - W))) (Complex.I • (1 - W)) (1 + W) := by
  rw [graphFrame_realify, diagonalStraightening_def, Matrix.smul_mul, fromBlocks_multiply]
  congr 1
  simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, I_mul_I, neg_smul, one_smul, neg_neg, smul_sub]
  congr 1 <;> match_scalars <;> simp

/-- The Gram matrix of the graph frame of a realified unitary matrix is `2`: its graph is
Lagrangian, and its columns have norm `√2` since `|x|² + |W x|² = 2 |x|²`. -/
private theorem conjTranspose_graphFrame_realify_mul_self (W : unitaryGroup n ℂ) :
    (graphFrame (W : Matrix n n ℂ).realify)ᴴ * graphFrame (W : Matrix n n ℂ).realify =
      (2 : ℂ) • 1 := by
  have hsymp : (W : Matrix n n ℂ).realify ∈ symplecticGroup n ℝ :=
    realify_mem_symplecticGroup_iff.2 W.property
  have horth : ((W : Matrix n n ℂ).realify)ᵀ * (W : Matrix n n ℂ).realify = 1 :=
    (mem_orthogonalGroup_iff' _ _).1 (realify_mem_orthogonalGroup_iff.2 W.property)
  rw [conjTranspose_graphFrame_mul_graphFrame, horth, SymplecticGroup.mem_iff'.1 hsymp, sub_self]
  ext i j
  by_cases hij : i = j
  · simp only [hij, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply_eq, Matrix.smul_apply]
    norm_num
  · simp [hij]

/-- The frame `(1/2) [[1 + W, -i (1 - W)], [i (1 - W), 1 + W]]` of the straightened graph of a
realified unitary matrix `W`. -/
private noncomputable def realifyGraphFrame (W : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (2 : ℂ)⁻¹ • fromBlocks (1 + W) (-(Complex.I • (1 - W))) (Complex.I • (1 - W)) (1 + W)

private theorem diagonalStraightening_mul_graphFrame_realify_eq (W : Matrix n n ℂ) :
    diagonalStraightening n * graphFrame W.realify =
      realifyGraphFrame W * ((√2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) := by
  rw [diagonalStraightening_mul_graphFrame_realify, map_ofReal_sqrt_two_smul_one, Matrix.mul_smul,
    Matrix.mul_one, realifyGraphFrame, smul_smul, inv_sqrt_two]

private theorem realifyGraphFrame_mem_unitaryGroup (W : unitaryGroup n ℂ) :
    realifyGraphFrame (W : Matrix n n ℂ) ∈ unitaryGroup (n ⊕ n) ℂ := by
  set c : ℂ := (2 : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)
  have hTT : ∀ X, (diagonalStraightening n)ᴴ * (diagonalStraightening n * X) = X := fun X ↦ by
    rw [← Matrix.mul_assoc, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.1 diagonalStraightening_mem_unitaryGroup, Matrix.one_mul]
  have hV : realifyGraphFrame (W : Matrix n n ℂ) =
      c • (diagonalStraightening n * graphFrame (W : Matrix n n ℂ).realify) := by
    rw [diagonalStraightening_mul_graphFrame_realify, smul_smul, realifyGraphFrame, mul_assoc,
      mul_inv_cancel₀ sqrt_two_ne_zero, mul_one]
  have hc : star c * c * 2 = 1 := by
    simp only [c, star_mul', star_inv₀, star_def, conj_ofReal, map_ofNat]
    linear_combination (1 / 2 : ℂ) * sqrt_two_mul_sqrt_two
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, hV]
  simp only [conjTranspose_smul, conjTranspose_mul, smul_mul_smul, Matrix.mul_assoc, hTT,
    conjTranspose_graphFrame_realify_mul_self, smul_smul, hc, one_smul]

/-- **The graph of a realified symmetric unitary matrix.** If `W` is a unitary matrix with
`Wᵀ = W`, for instance a diagonal one, the straightened graph of its realification is framed by
`(1/2) [[1 + W, -i (1 - W)], [i (1 - W), 1 + W]]`, whose Souriau map is `fromBlocks W 0 0 W`. -/
theorem coe_souriau_graphUnitaryFrame_ofUnitary_of_transpose_eq {W : unitaryGroup n ℂ}
    (hW : (W : Matrix n n ℂ)ᵀ = W) :
    (souriau (graphUnitaryFrame (ofUnitary W)) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      fromBlocks (W : Matrix n n ℂ) 0 0 W := by
  have hreal : (graphUnitaryFrame (ofUnitary W) : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      ((⟨_, realifyGraphFrame_mem_unitaryGroup W⟩ : unitaryGroup (n ⊕ n) ℂ) :
        Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage := by
    rw [realImage_graphUnitaryFrame, coe_ofUnitary, diagonalStraightening_mul_graphFrame_realify_eq,
      realImage_mul_map_ofReal _ isUnit_sqrt_two_smul_one]
  rw [souriau_eq_of_realImage_eq hreal, coe_souriau]
  dsimp only
  rw [realifyGraphFrame, transpose_smul, fromBlocks_transpose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, fromBlocks_multiply]
  simp only [transpose_add, transpose_one, transpose_neg, transpose_smul, transpose_sub, hW,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one,
    fromBlocks_smul]
  congr 1 <;> match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring

/-- **The Conley–Zehnder index of a path of diagonal unitary matrices.** For a path of realified
diagonal unitary matrices `diag (e^{i θ_j t})` with continuous angles `θ_j`, the Conley–Zehnder
index is `-∑ j, (c(θ_j 1) - c(θ_j 0))`, where `c(θ) = ⌊θ / 2π⌋ + ⌈θ / 2π⌉`: each multiple of `2π`
crossed by an angle counts twice, with sign, and a multiple of `2π` at an endpoint counts once. -/
theorem conleyZehnderIndex_map_ofUnitary_eq_neg_sum_of_diagonal {U V : unitaryGroup n ℂ}
    (γ : Path U V) {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, (γ t : Matrix n n ℂ) = diagonal fun j ↦ Complex.exp (θ j t * Complex.I)) :
    conleyZehnderIndex (γ.map continuous_ofUnitary) =
      -∑ j, (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) -
        ((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ)) := by
  -- Compare with the path of diagonal frames `diag (e^{i θ_j / 2}) ⊕ diag (e^{i θ_j / 2})`.
  set φ : n ⊕ n → I → ℝ := Sum.elim (fun j t ↦ θ j t / 2) (fun j t ↦ θ j t / 2) with hφdef
  have hφ (k : n ⊕ n) : Continuous (φ k) := by
    rcases k with j | j <;> exact (hθ j).div_const 2
  let D : I → unitaryGroup (n ⊕ n) ℂ := fun t ↦ unitaryTorusHom (n ⊕ n) fun k ↦ Circle.exp (φ k t)
  have hD : Continuous D := by fun_prop
  let δ : Path (D 0) (D 1) := ⟨⟨D, hD⟩, rfl, rfl⟩
  have hs (t : I) : souriau (((γ.map continuous_ofUnitary).map continuous_graphUnitaryFrame) t) =
      souriau (δ t) := by
    refine Subtype.ext ?_
    have hWt : ((γ t : unitaryGroup n ℂ) : Matrix n n ℂ)ᵀ = γ t := by
      rw [hγ t, diagonal_transpose]
    rw [Path.map_coe, Function.comp_apply, Path.map_coe, Function.comp_apply,
      coe_souriau_graphUnitaryFrame_ofUnitary_of_transpose_eq hWt,
      coe_souriau_of_coe_eq_diagonal (U := δ t) (coe_unitaryTorusHom _), hγ t,
      fromBlocks_diagonal]
    congr 1
    funext k
    rcases k with j | j <;>
    · simp only [Sum.elim_inl, Sum.elim_inr, hφdef, Circle.coe_exp, ← Complex.exp_natCast_mul]
      congr 1
      push_cast
      ring
  rw [conleyZehnderIndex, maslovIndex_eq_of_souriau_eq _ δ hs,
    maslovIndex_eq_sum_of_diagonal δ hφ fun t ↦
      (coe_unitaryTorusHom _).trans (by simp only [Circle.coe_exp]), Fintype.sum_sum_type]
  simp only [hφdef, Sum.elim_inl, Sum.elim_inr, div_div]
  rw [← two_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **Normalization on rotations.** The path `t ↦ diag (e^{i α_j t})` of realified unitary
matrices, which is `exp (t J S)` with `S = diag (α, α)`, has Conley–Zehnder
index `-∑ j, sign α_j = -signature(S) / 2` when every `|α_j| < 2π`. In particular a small
counterclockwise rotation of `ℝ²` has index `-1` and a small clockwise one has index `1`. -/
theorem conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation {U V : unitaryGroup n ℂ}
    (γ : Path U V) {α : n → ℝ} (hα : ∀ j, |α j| < 2 * Real.pi)
    (hγ : ∀ t : I, (γ t : Matrix n n ℂ) = diagonal fun j ↦ Complex.exp (α j * t * Complex.I)) :
    conleyZehnderIndex (γ.map continuous_ofUnitary) = -∑ j, Real.sign (α j) := by
  rw [conleyZehnderIndex_map_ofUnitary_eq_neg_sum_of_diagonal γ (θ := fun j t ↦ α j * t)
    (fun j ↦ continuous_const.mul continuous_subtypeVal) fun t ↦ by rw [hγ t]; push_cast; simp]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- Since `|α_j / 2π| < 1`, the count `⌊α_j / 2π⌋ + ⌈α_j / 2π⌉` is `sign α_j`.
  simp only [Set.Icc.coe_one, mul_one, Set.Icc.coe_zero, mul_zero, zero_div, Int.floor_zero,
    Int.ceil_zero, add_zero, Int.cast_zero, sub_zero]
  exact floor_add_ceil_div_eq_sign_of_abs_lt (hα j)

/-! ### Direct sums -/

section Sum

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The unitary graph frame and the straightened graph frame span the same real subspace, as
invertible matrices. -/
private theorem realImage_graphUnitaryFrame_toUnits (A : GLSymplectic n ℝ) :
    ((Unitary.toUnits (graphUnitaryFrame A) : GL (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      ((Unitary.toUnits (⟨_, diagonalStraightening_mem_unitaryGroup⟩ : unitaryGroup (n ⊕ n) ℂ) *
        graphFrameUnit A : GL (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage := by
  rw [Unitary.val_toUnits_apply, Units.val_mul, Unitary.val_toUnits_apply, coe_graphFrameUnit]
  exact realImage_graphUnitaryFrame A

/-- The symplectic direct sum of the unitary graph frames of `A` and `B` frames the straightened
graph of their direct sum. -/
private theorem realImage_symplecticSum_graphUnitaryFrame (A : GLSymplectic n ℝ)
    (B : GLSymplectic m ℝ) :
    (symplecticSum (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ)
        (graphUnitaryFrame B : Matrix (m ⊕ m) (m ⊕ m) ℂ)).realImage =
      (diagonalStraightening (n ⊕ m) *
        graphFrame ((sum (A, B) : GL ((n ⊕ m) ⊕ (n ⊕ m)) ℝ) : Matrix _ _ ℝ)).realImage := by
  have h := realImage_symplecticSum_congr (realImage_graphUnitaryFrame_toUnits A)
    (realImage_graphUnitaryFrame_toUnits B)
  simp only [Unitary.val_toUnits_apply, Units.val_mul, coe_graphFrameUnit] at h
  rw [h, symplecticSum_mul, coe_sum, graphFrame_symplecticSum, diagonalStraightening_sum]

/-- **The direct-sum axiom.** The Conley–Zehnder index of the direct sum `A ⊕ B` of two paths of
symplectic matrices is the sum of their Conley–Zehnder indices. -/
theorem conleyZehnderIndex_sum {A B : GLSymplectic n ℝ} {C D : GLSymplectic m ℝ}
    (γ₁ : Path A B) (γ₂ : Path C D) :
    conleyZehnderIndex ((γ₁.prod γ₂).map continuous_sum) =
      conleyZehnderIndex γ₁ + conleyZehnderIndex γ₂ := by
  -- Frame the straightened graphs of the direct sum by the direct sums of the unitary frames.
  let f : I → unitaryGroup ((n ⊕ m) ⊕ (n ⊕ m)) ℂ := fun t ↦
    ⟨symplecticSum (graphUnitaryFrame (γ₁ t) : Matrix (n ⊕ n) (n ⊕ n) ℂ)
      (graphUnitaryFrame (γ₂ t) : Matrix (m ⊕ m) (m ⊕ m) ℂ),
      symplecticSum_mem_unitaryGroup (graphUnitaryFrame _).property (graphUnitaryFrame _).property⟩
  have hf : Continuous f := Continuous.subtype_mk
    (Continuous.matrix_symplecticSum
      (continuous_subtypeVal.comp (continuous_graphUnitaryFrame.comp γ₁.continuous))
      (continuous_subtypeVal.comp (continuous_graphUnitaryFrame.comp γ₂.continuous))) _
  let δ : Path (f 0) (f 1) := ⟨⟨f, hf⟩, rfl, rfl⟩
  rw [conleyZehnderIndex_eq_neg_maslovIndex _ δ fun t ↦
      realImage_symplecticSum_graphUnitaryFrame (γ₁ t) (γ₂ t),
    maslovIndex_eq_add_of_coe_eq_symplecticSum (γ₁.map continuous_graphUnitaryFrame)
      (γ₂.map continuous_graphUnitaryFrame) δ fun t ↦ rfl,
    conleyZehnderIndex, conleyZehnderIndex, neg_add]

end Sum

/-! ### Loops of symplectic matrices -/

/-- The square of the determinant of the unitary graph frame of `A` is the graph phase of `A`, up
to the constant factor `(det T) ^ 2` of the diagonal straightening `T`. -/
private theorem detCircle_graphUnitaryFrame_sq (A : GLSymplectic n ℝ) :
    detCircle (graphUnitaryFrame A) ^ 2 =
      detCircle (⟨_, diagonalStraightening_mem_unitaryGroup⟩ : unitaryGroup (n ⊕ n) ℂ) ^ 2 *
        graphPhase A := by
  obtain ⟨r, -, hr⟩ := exists_pos_det_realOrthonormalize_eq_mul_det (graphFrameUnit A)
  set T : unitaryGroup (n ⊕ n) ℂ := ⟨_, diagonalStraightening_mem_unitaryGroup⟩
  set d := (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
  -- The determinant of the unitary graph frame is `det T * r * d`.
  have hu : (detCircle (graphUnitaryFrame A) : ℂ) = (detCircle T : ℂ) * (r * d) := by
    rw [coe_detCircle, coe_detCircle, graphUnitaryFrame, det_mul, hr, coe_graphFrameUnit]
  -- Both determinants lie on the unit circle.
  have huu := Circle.coe_mul_conj (detCircle (graphUnitaryFrame A))
  rw [hu, map_mul, map_mul, conj_ofReal] at huu
  have hd : conj d ≠ 0 := (map_ne_zero _).2 (det_graphFrame_ne_zero A)
  refine Circle.ext ?_
  rw [Circle.coe_pow, Circle.coe_mul, Circle.coe_pow, coe_graphPhase, hu, mul_div_assoc',
    eq_div_iff hd]
  linear_combination ((detCircle T : ℂ) ^ 2 * d) * huu -
    ((detCircle T : ℂ) ^ 2 * d * r ^ 2 * d * conj d) * Circle.coe_mul_conj (detCircle T)

/-- **The Conley–Zehnder index of a loop.** A loop `γ` of symplectic matrices has
Conley–Zehnder index `-2 μ(γ)`, where `μ` is the Maslov index of loops of symplectic matrices. -/
theorem conleyZehnderIndex_eq_neg_two_mul_maslovIndex {A : GLSymplectic n ℝ} (γ : Path A A) :
    conleyZehnderIndex γ = -2 * maslovIndex γ := by
  set T : unitaryGroup (n ⊕ n) ℂ := ⟨_, diagonalStraightening_mem_unitaryGroup⟩
  -- The path of unitary graph frames is a loop, so its Maslov index is twice the degree of its
  -- determinants. Their squares are the graph phases up to a constant factor, and the degree of
  -- the graph phases is the Maslov index of the graph loop, which is `2 μ(γ)`.
  have hsq : Circle.degree (((γ.map continuous_graphUnitaryFrame).map continuous_detCircle).map
      (continuous_pow 2)) = Circle.degree ((Path.refl (detCircle T ^ 2)).mul
        (γ.map continuous_graphPhase)) :=
    Circle.degree_congr _ _ fun t ↦ by
      simp only [Path.map_coe, Function.comp_apply, Path.mul_apply, Path.refl_apply]
      exact detCircle_graphUnitaryFrame_sq (γ t)
  have hphase : Circle.degree (γ.map continuous_graphPhase) = (graphLoop γ).maslovIndex :=
    ((graphLoop γ).maslovIndex_eq_degree isMaximalTotallyReal_realSubspace _ fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, coe_graphPhase_eq_maslovPhase]
      exact IsMaximalTotallyReal.maslovPhase_congr _ _ _ (graphLoop_apply γ t).symm).symm
  rw [Circle.degree_map_pow, Circle.degree_mul, Circle.degree_refl, zero_add, hphase,
    maslovIndex_graphLoop] at hsq
  rw [conleyZehnderIndex, Matrix.UnitaryGroup.maslovIndex_eq_two_mul_degree]
  have hdeg : Circle.degree ((γ.map continuous_graphUnitaryFrame).map continuous_detCircle) =
      maslovIndex γ := by
    omega
  rw [hdeg]
  ring

/-- **The loop axiom.** Multiplying a path `γ` of symplectic matrices by a loop `φ` of symplectic
matrices based at the identity, a change of symplectic trivialization along a loop, changes its
Conley–Zehnder index by `-2 μ(φ)`, where `μ` is the Maslov index of loops of symplectic
matrices. -/
theorem conleyZehnderIndex_mul (φ : Path (1 : GLSymplectic n ℝ) 1) {A B : GLSymplectic n ℝ}
    (γ : Path A B) :
    conleyZehnderIndex (φ.mul γ) = conleyZehnderIndex γ - 2 * maslovIndex φ := by
  -- `φ γ` is homotopic to `(t ↦ φ t A)` followed by `γ`.
  have h : (φ.mul γ).Homotopic ((φ.mul (Path.refl A)).trans ((Path.refl 1).mul γ)) := by
    have H := (Path.Homotopic.prodHomotopy (Path.Homotopy.transRefl φ).symm
      (Path.Homotopy.reflTrans γ).symm).map ⟨_, continuous_mul⟩
    rw [← Path.trans_prod_eq_prod_trans, Path.map_trans] at H
    exact ⟨H⟩
  rw [conleyZehnderIndex_eq_of_homotopic h, conleyZehnderIndex_trans,
    conleyZehnderIndex_eq_neg_two_mul_maslovIndex, maslovIndex_mul, GLSymplectic.maslovIndex_refl,
    conleyZehnderIndex_congr ((Path.refl 1).mul γ) γ fun t ↦ by simp]
  push_cast
  ring

end GLSymplectic

end TauCeti
