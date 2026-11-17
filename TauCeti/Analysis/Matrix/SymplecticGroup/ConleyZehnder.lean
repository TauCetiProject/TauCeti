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
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_maslovIndex`: the index is minus the Maslov
  index of any path of unitary frames of the straightened graphs.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopic`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_trans`, `TauCeti.GLSymplectic.conleyZehnderIndex_symm`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_refl`: homotopy invariance, catenation, reversal and
  the constant path.
* `TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_of_diagonal`: the index of a
  path of diagonal unitary matrices.
* `TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`: the
  normalization on rotations, `CZ = -∑ j, sign α_j`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the Maslov index of the graph relative to the diagonal).
* C. Conley and E. Zehnder, *Morse-type index theory for flows and periodic solutions for
  Hamiltonian equations*, Comm. Pure Appl. Math. **37** (1984), 207–253.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999 (the axioms and the normalization of the Conley–Zehnder index).
-/

public section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup Complex
open scoped unitInterval

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
private theorem diagonalStraightening_mul_graphFrame_one :
    diagonalStraightening n * graphFrame 1 =
      ((√2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) := by
  rw [diagonalStraightening_mul_graphFrame, sub_self, Matrix.mul_zero, ← two_smul ℝ 1,
    map_ofReal_sqrt_two_smul_one]
  ext i j
  by_cases hij : i = j <;> simp [hij, inv_sqrt_two]

/-- **The diagonal straightening carries the diagonal onto the real points**: the image under it
of the graph `Γ(1)` of the identity is `ℝ^{n ⊕ n}`. -/
theorem realImage_diagonalStraightening_mul_graphFrame_one :
    (diagonalStraightening n * graphFrame 1).realImage = realSubspace (n ⊕ n) := by
  rw [diagonalStraightening_mul_graphFrame_one, realImage_map_ofReal isUnit_sqrt_two_smul_one]

namespace GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The graph frame of a symplectic matrix, as an invertible matrix. -/
private noncomputable def graphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  ((Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.2))).unit

private theorem coe_graphFrameUnit (A : GLSymplectic n ℝ) :
    (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  IsUnit.unit_spec _

open scoped Matrix.Norms.L2Operator in
private theorem continuous_graphFrameUnit : Continuous (graphFrameUnit (n := n)) := by
  have hF : Continuous fun A : GLSymplectic n ℝ ↦
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtype_val)
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
        (mem_iff_mem_symplecticGroup.1 A.2)))⟩

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
    realify_mem_symplecticGroup_iff.2 W.2
  have horth : ((W : Matrix n n ℂ).realify)ᵀ * (W : Matrix n n ℂ).realify = 1 :=
    (mem_orthogonalGroup_iff' _ _).1 (realify_mem_orthogonalGroup_iff.2 W.2)
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
    · simp only [Sum.elim_inl, Sum.elim_inr, hφdef, Circle.coe_exp, ← Complex.exp_nat_mul]
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
    (fun j ↦ continuous_const.mul continuous_subtype_val) fun t ↦ by rw [hγ t]; push_cast; simp]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- Since `|α_j / 2π| < 1`, the count `⌊α_j / 2π⌋ + ⌈α_j / 2π⌉` is `sign α_j`.
  simp only [Set.Icc.coe_one, mul_one, Set.Icc.coe_zero, mul_zero, zero_div, Int.floor_zero,
    Int.ceil_zero, add_zero, Int.cast_zero, sub_zero]
  exact floor_add_ceil_div_eq_sign_of_abs_lt (hα j)

end GLSymplectic

end TauCeti
