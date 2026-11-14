/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.OfReal
public import TauCeti.LinearAlgebra.Matrix.Realify
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
import TauCeti.Analysis.Matrix.UnitaryGroup.Torus

/-!
# The Conley–Zehnder index of a path of symplectic matrices

Following Robbin and Salamon, the Conley–Zehnder index of a path `Ψ` of symplectic matrices is
read off from the path of graphs of `Ψ`, a path of Lagrangian subspaces of the doubled space, by
the Maslov index of Lagrangian paths relative to the diagonal. This file builds that index from
the Souriau Maslov index `Matrix.UnitaryGroup.maslovIndex` of paths of Lagrangian frames.

Matrices act on `ℝ²ⁿ = ℝ^(n ⊕ n)`, whose two blocks are the real and imaginary parts of `ℂⁿ`
(see `Matrix.realify`), and `Matrix.J n ℝ = [[0, -1], [1, 0]]` is multiplication by `i`. The
symplectic matrices `Ψ`, those with `Ψᵀ J Ψ = J`, preserve the form `ω₀(u, v) = -uᵀ J v`, which is
`dx ∧ dy` for `n = 1`. The graph `{(x, Ψ x)}` of `Ψ` is a Lagrangian subspace of
`(ℝ²ⁿ × ℝ²ⁿ, -ω₀ ⊕ ω₀)`, and the diagonal is the graph of the identity. The real-linear
isomorphism

`T(u, w) = ((u + w) + i J (u - w)) / √2 : ℝ²ⁿ × ℝ²ⁿ → ℂ^(n ⊕ n)`

carries, by a direct computation, `-ω₀ ⊕ ω₀` to the standard symplectic form `Im ⟪·, ·⟫` and
the diagonal to the real subspace `ℝ^(n ⊕ n)`. It carries the graph of `Ψ` to the image of
`ℝ^(n ⊕ n)` under the complex matrix

`N(Ψ) = ((1 + Ψ) + i J (1 - Ψ)) / √2` (`Matrix.symplecticGraphFrame`),

since `N(Ψ) x = T(x, Ψ x)` for real `x` (`Matrix.symplecticGraphFrame_mulVec`). For symplectic
`Ψ` its Gram matrix is real, `N(Ψ)ᴴ N(Ψ) = 1 + Ψᵀ Ψ`
(`Matrix.conjTranspose_symplecticGraphFrame_mul_self`), which says both that the image is
Lagrangian and that `N(Ψ)` is invertible. The image meets the diagonal `ℝ^(n ⊕ n)` exactly in the
images of the fixed vectors of `Ψ`
(`Matrix.forall_im_symplecticGraphFrame_mulVec_eq_zero_iff`), so the crossings of a path of graphs
with the diagonal are the times at which `Ψ` has the eigenvalue `1`.

The unitary polar factor of `N(Ψ)` (`TauCeti.GLSymplectic.graphFrame`, so that
`N(Ψ) = graphFrame Ψ * √(N(Ψ)ᴴ N(Ψ))` by
`TauCeti.GLSymplectic.graphFrame_mul_sqrt_conjTranspose_mul_self`) is a unitary frame of the
same Lagrangian (`TauCeti.GLSymplectic.realImage_graphFrame`), depending continuously on `Ψ`, and
equal to `1` at `Ψ = 1`. The Maslov index of the path of these frames is the Robbin–Salamon index
`μ_RS(graph Ψ, Δ)` of the path of graphs relative to the diagonal
(`TauCeti.GLSymplectic.graphMaslovIndex`), and for a path starting at `1` the **Conley–Zehnder
index** is

`CZ(Ψ) = -μ_RS(graph Ψ, Δ)` (`TauCeti.GLSymplectic.conleyZehnder`).

It is invariant under homotopies with fixed endpoints, and the graph index is additive under
catenation. For a path of rotations `Ψ t = diag (e^{iθ_j(t)})`, realified, the index is computed
explicitly (`TauCeti.GLSymplectic.conleyZehnder_eq_neg_sum_of_realify_diagonal`):
`CZ(Ψ) = -∑ j, (⌊θ_j(1) / 2π⌋ + ⌈θ_j(1) / 2π⌉)` when every `θ_j(0) = 0`. In particular a small
positive (counterclockwise) rotation of `ℝ²` has index `-1` and a small negative one has index `1`
(`TauCeti.GLSymplectic.conleyZehnder_eq_neg_card_of_realify_diagonal`,
`TauCeti.GLSymplectic.conleyZehnder_eq_card_of_realify_diagonal`).

## Main definitions

* `Matrix.symplecticGraphFrame`: the complex frame `N(Ψ)` of the graph of `Ψ`.
* `TauCeti.GLSymplectic.graphFrame`: its unitary polar factor, a unitary frame of the graph.
* `TauCeti.GLSymplectic.graphMaslovIndex`: the Maslov index of a path of graphs relative to the
  diagonal.
* `TauCeti.GLSymplectic.conleyZehnder`: the Conley–Zehnder index of a path starting at `1`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Sections 2 and 4 (the index of symplectic paths through their graphs).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford Graduate
  Texts in Mathematics 27, Oxford University Press, 2017, Section 2.4.
-/

public section

open Matrix
open scoped MatrixOrder ComplexOrder unitInterval Matrix.Norms.L2Operator

private theorem ofReal_sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'

private theorem ofReal_sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt zero_le_two

/-- The `√2` normalization of the graph frame squares to `1 / 2`. -/
private theorem inv_ofReal_sqrt_two_mul_inv :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← sq, ofReal_sqrt_two_sq]

/-- The `√2` normalization in a Gram matrix `(c N)ᴴ (c N)`: `star c * c = 1 / 2`. -/
private theorem star_inv_ofReal_sqrt_two_mul_inv :
    star (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, inv_ofReal_sqrt_two_mul_inv]

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- The real matrix `1 + 1` is `2 • 1` as a complex matrix: the scalar in the graph frame of the
identity and in the Gram matrix of the graph frame of an orthogonal matrix. -/
private theorem map_ofReal_one_add_one :
    (1 + 1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).map ((↑) : ℝ → ℂ) = (2 : ℂ) • 1 := by
  rw [Matrix.map_add _ Complex.ofReal_add, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
    two_smul]

/-- The complex frame `N(A) = ((1 + A) + i J (1 - A)) / √2` of the graph of a real matrix `A` on
`ℝ^(n ⊕ n)`: for real `x`, `N(A) x` is the image of `(x, A x)` under the isomorphism
`(u, w) ↦ ((u + w) + i J (u - w)) / √2` from `ℝ^(n ⊕ n) × ℝ^(n ⊕ n)` to `ℂ^(n ⊕ n)`, which
carries `-ω₀ ⊕ ω₀` to `Im ⟪·, ·⟫` and the diagonal to `ℝ^(n ⊕ n)`. -/
noncomputable def symplecticGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    ((1 + A).map ((↑) : ℝ → ℂ) + Complex.I • (J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ))

/-- On a real vector `x`, the graph frame of `A` is the image of `(x, A x)`: its real part is
`(x + A x) / √2` and its imaginary part is `J (x - A x) / √2`. -/
theorem symplecticGraphFrame_mulVec (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (x : n ⊕ n → ℝ) :
    symplecticGraphFrame A *ᵥ (fun j ↦ (x j : ℂ)) = fun i ↦ (Real.sqrt 2 : ℂ)⁻¹ *
      (((x + A *ᵥ x) i : ℂ) + Complex.I * ((J n ℝ *ᵥ (x - A *ᵥ x)) i : ℂ)) := by
  ext i
  have hP : (((1 + A) *ᵥ x) i : ℂ) = ((1 + A).map ((↑) : ℝ → ℂ) *ᵥ fun j ↦ (x j : ℂ)) i :=
    Complex.ofRealHom.map_mulVec (1 + A) x i
  have hQ : (((J n ℝ * (1 - A)) *ᵥ x) i : ℂ) =
      ((J n ℝ * (1 - A)).map ((↑) : ℝ → ℂ) *ᵥ fun j ↦ (x j : ℂ)) i :=
    Complex.ofRealHom.map_mulVec (J n ℝ * (1 - A)) x i
  rw [add_mulVec, one_mulVec] at hP
  rw [← mulVec_mulVec, sub_mulVec, one_mulVec] at hQ
  simp only [symplecticGraphFrame, smul_mulVec, add_mulVec, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, ← hP, ← hQ]

/-- **Crossings with the diagonal.** The graph frame of `A` sends a real vector `x` to a real
vector exactly when `x` is a fixed vector of `A`. So the graph of `A` meets the diagonal in the
graph of the fixed vectors of `A`. -/
theorem forall_im_symplecticGraphFrame_mulVec_eq_zero_iff (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (x : n ⊕ n → ℝ) :
    (∀ i, ((symplecticGraphFrame A *ᵥ fun j ↦ (x j : ℂ)) i).im = 0) ↔ A *ᵥ x = x := by
  have hc : (Real.sqrt 2)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 two_pos).ne'
  simp only [symplecticGraphFrame_mulVec, ← Complex.ofReal_inv, Complex.mul_im,
    Complex.add_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul,
    one_mul, zero_add, add_zero, mul_eq_zero, hc, false_or]
  constructor
  · intro h
    -- `J` is invertible, with `J * J = -1`.
    have hv := congrArg (J n ℝ *ᵥ ·) (funext h : J n ℝ *ᵥ (x - A *ᵥ x) = 0)
    simp only [mulVec_mulVec, J_squared, neg_mulVec, one_mulVec, mulVec_zero, neg_eq_zero,
      sub_eq_zero] at hv
    exact hv.symm
  · intro h i
    simp [h]

/-- The graph of the identity, the diagonal, is framed by a multiple of the identity, so it is
carried to `ℝ^(n ⊕ n)`. -/
@[simp]
theorem symplecticGraphFrame_one :
    symplecticGraphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = (Real.sqrt 2 : ℂ) • 1 := by
  rw [symplecticGraphFrame, sub_self, Matrix.mul_zero, Matrix.map_zero _ Complex.ofReal_zero,
    smul_zero, add_zero, map_ofReal_one_add_one, smul_smul, ← ofReal_sqrt_two_sq, sq,
    inv_mul_cancel_left₀ ofReal_sqrt_two_ne_zero]

/-- **The graph of a symplectic matrix is Lagrangian.** The Gram matrix of the graph frame of a
symplectic matrix `A` is the real matrix `1 + Aᵀ A`. The vanishing of its imaginary part is the
Lagrangian condition, and is equivalent to `Aᵀ J A = J`. -/
theorem conjTranspose_symplecticGraphFrame_mul_self {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (symplecticGraphFrame A)ᴴ * symplecticGraphFrame A = (1 + Aᵀ * A).map ((↑) : ℝ → ℂ) := by
  have hJ : (J n ℝ)ᵀ * J n ℝ = 1 := by rw [J_transpose, neg_mul, J_squared, neg_neg]
  have hre : (1 + A)ᵀ * (1 + A) + (J n ℝ * (1 - A))ᵀ * (J n ℝ * (1 - A)) =
      (2 : ℝ) • (1 + Aᵀ * A) := by
    rw [transpose_mul, transpose_add, transpose_sub, transpose_one, Matrix.mul_assoc (1 - Aᵀ),
      ← Matrix.mul_assoc (J n ℝ)ᵀ, hJ, Matrix.one_mul, two_smul]
    noncomm_ring
  have him : (1 + A)ᵀ * (J n ℝ * (1 - A)) - (J n ℝ * (1 - A))ᵀ * (1 + A) = 0 := by
    have h := SymplecticGroup.mem_iff'.1 hA
    rw [transpose_mul, J_transpose, transpose_add, transpose_sub, transpose_one]
    have e : (1 + Aᵀ) * (J n ℝ * (1 - A)) - (1 - Aᵀ) * -J n ℝ * (1 + A) =
        (J n ℝ - Aᵀ * J n ℝ * A) + (J n ℝ - Aᵀ * J n ℝ * A) := by noncomm_ring
    rw [e, h, sub_self, add_zero]
  rw [symplecticGraphFrame, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    conjTranspose_mul_self_map_ofReal_add_I_smul, hre, him, star_inv_ofReal_sqrt_two_mul_inv]
  ext i j
  simp [← mul_add]

/-- The graph frame of a symplectic matrix is invertible. -/
theorem isUnit_symplecticGraphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) : IsUnit (symplecticGraphFrame A) := by
  have hpos : (1 + Aᵀ * A).PosDef := by
    have h := posSemidef_conjTranspose_mul_self A
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact PosDef.one.add_posSemidef h
  have hu : IsUnit ((1 + Aᵀ * A).map ((↑) : ℝ → ℂ)) := hpos.isUnit.map Complex.ofRealHom.mapMatrix
  rw [← conjTranspose_symplecticGraphFrame_mul_self hA] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- The graph frame depends continuously on the matrix. -/
@[fun_prop]
theorem continuous_symplecticGraphFrame :
    Continuous (symplecticGraphFrame : Matrix (n ⊕ n) (n ⊕ n) ℝ → _) := by
  unfold symplecticGraphFrame
  fun_prop

/-- The graph frame of the realification of a diagonal matrix `diag e`, in block form. -/
theorem symplecticGraphFrame_realify_diagonal (e : n → ℂ) :
    symplecticGraphFrame (diagonal e).realify = (Real.sqrt 2 : ℂ)⁻¹ •
      fromBlocks (diagonal fun j ↦ 1 + e j) (diagonal fun j ↦ Complex.I * (e j - 1))
        (diagonal fun j ↦ -(Complex.I * (e j - 1))) (diagonal fun j ↦ 1 + e j) := by
  rw [symplecticGraphFrame]
  congr 1
  ext (i | i) (j | j) <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Matrix.one_apply,
      Complex.ext_iff, *]

/-- For the realification of `diag e`, the graph frame satisfies `N Nᵀ = 2 diag (e, e)`. For a
unitary `diag e` this computes the Souriau map of the graph. -/
theorem symplecticGraphFrame_realify_diagonal_mul_transpose (e : n → ℂ) :
    symplecticGraphFrame (diagonal e).realify * (symplecticGraphFrame (diagonal e).realify)ᵀ =
      (2 : ℂ) • diagonal (Sum.elim e e) := by
  -- The diagonal blocks reduce to this scalar identity; the off-diagonal blocks cancel.
  have hdiag (z : ℂ) :
      (1 + z) * (1 + z) + Complex.I * (z - 1) * (Complex.I * (z - 1)) = 4 * z := by
    linear_combination (z - 1) ^ 2 * Complex.I_mul_I
  rw [symplecticGraphFrame_realify_diagonal, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, fromBlocks_transpose, fromBlocks_multiply]
  simp only [diagonal_transpose, diagonal_mul_diagonal, diagonal_add]
  rw [← fromBlocks_diagonal]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp only [Matrix.smul_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, diagonal_apply, hij, ite_true, ite_false, Matrix.zero_apply, smul_eq_mul,
      mul_zero]
  · rw [inv_ofReal_sqrt_two_mul_inv]
    linear_combination 2⁻¹ * hdiag (e j)
  · ring
  · ring
  · rw [inv_ofReal_sqrt_two_mul_inv]
    linear_combination 2⁻¹ * hdiag (e j)

end Matrix

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The graph frame of a symplectic matrix, as an invertible matrix. -/
private noncomputable def graphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  (isUnit_symplecticGraphFrame (mem_iff_mem_symplecticGroup.1 A.2)).unit

private theorem coe_graphFrameUnit (A : GLSymplectic n ℝ) :
    (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  rw [graphFrameUnit, IsUnit.unit_spec]

private theorem continuous_graphFrameUnit :
    Continuous (graphFrameUnit : GLSymplectic n ℝ → GL (n ⊕ n) ℂ) := by
  refine Units.isOpenEmbedding_val.isEmbedding.continuous_iff.2 ?_
  simp only [Function.comp_def, coe_graphFrameUnit]
  exact continuous_symplecticGraphFrame.comp
    (Units.continuous_val.comp continuous_subtype_val)

/-- The **unitary graph frame** of a symplectic matrix `A`: the unitary polar factor of the graph
frame `N(A)` (`Matrix.symplecticGraphFrame`). It frames the same Lagrangian subspace, the image of
the graph of `A` in `ℂ^(n ⊕ n)` (`TauCeti.GLSymplectic.realImage_graphFrame`). -/
noncomputable def graphFrame (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  (graphFrameUnit A).polarUnitary

/-- The unitary graph frame depends continuously on the symplectic matrix. -/
@[fun_prop]
theorem continuous_graphFrame : Continuous (graphFrame : GLSymplectic n ℝ → _) :=
  ((contMDiff_coe_polarUnitary (n := n ⊕ n) (𝕜 := ℂ) (k := 0)).continuous.comp
    continuous_graphFrameUnit).subtype_mk _

/-- **The polar decomposition of the graph frame.** The unitary graph frame of `A` is the unitary
polar factor of `N(A)`: `N(A) = graphFrame A * √(N(A)ᴴ N(A))`. -/
theorem graphFrame_mul_sqrt_conjTranspose_mul_self (A : GLSymplectic n ℝ) :
    (graphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
        CFC.sqrt ((symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ *
          symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) =
      symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  have h := Units.polarUnitary_mul_sqrt_star_mul (graphFrameUnit A)
  rwa [coe_graphFrameUnit, star_eq_conjTranspose] at h

private theorem star_graphFrameUnit_mul_self (A : GLSymplectic n ℝ) :
    star (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
        (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) := by
  rw [coe_graphFrameUnit, star_eq_conjTranspose,
    conjTranspose_symplecticGraphFrame_mul_self (mem_iff_mem_symplecticGroup.1 A.2)]

/-- The unitary graph frame of `A` frames the image of the graph of `A`: it carries `ℝ^(n ⊕ n)`
to the same Lagrangian subspace as the graph frame `N(A)`. -/
theorem realImage_graphFrame (A : GLSymplectic n ℝ) :
    (graphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage := by
  rw [graphFrame, realImage_polarUnitary _ (by rw [← star_eq_conjTranspose,
    star_graphFrameUnit_mul_self]), coe_graphFrameUnit]

/-- For an orthogonal symplectic matrix `A`, the graph frame `N(A)` is `√2` times a unitary
matrix, which is therefore the unitary graph frame. -/
theorem coe_graphFrame_of_transpose_mul_self {A : GLSymplectic n ℝ}
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 1) :
    (graphFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (Real.sqrt 2 : ℂ)⁻¹ • symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix _ _ ℝ) := by
  have hv : (Real.sqrt 2 : ℂ)⁻¹ • symplecticGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix _ _ ℝ) ∈
      unitaryGroup (n ⊕ n) ℂ := by
    rw [mem_unitaryGroup_iff', star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      star_eq_conjTranspose,
      conjTranspose_symplecticGraphFrame_mul_self (mem_iff_mem_symplecticGroup.1 A.2), hA,
      star_inv_ofReal_sqrt_two_mul_inv]
    rw [map_ofReal_one_add_one, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hmul : (⟨_, hv⟩ : unitaryGroup (n ⊕ n) ℂ) *
      ((Real.sqrt 2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ)) = graphFrameUnit A := by
    rw [coe_graphFrameUnit, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    exact mul_inv_cancel_left₀ ofReal_sqrt_two_ne_zero _
  have hq : 0 ≤ (Real.sqrt 2 : ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    smul_nonneg (Real.sqrt_nonneg 2) zero_le_one
  exact congrArg Subtype.val (Units.polarUnitary_eq_of_mul_eq' _ hq hmul)

/-- The diagonal, the graph of the identity, is framed by the identity. -/
@[simp]
theorem graphFrame_one : graphFrame (1 : GLSymplectic n ℝ) = 1 := by
  refine Subtype.ext ?_
  rw [coe_graphFrame_of_transpose_mul_self (by simp)]
  simp only [OneMemClass.coe_one, Units.val_one, symplecticGraphFrame_one, smul_smul,
    inv_mul_cancel₀ ofReal_sqrt_two_ne_zero, one_smul]

/-- The **Maslov index of a path of graphs**: the Robbin–Salamon index `μ_RS(graph γ, Δ)` of the
path of graphs of a path `γ` of symplectic matrices, relative to the diagonal, computed as the
Souriau Maslov index of the path of unitary graph frames. -/
noncomputable def graphMaslovIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  maslovIndex (γ.map continuous_graphFrame)

/-- The graph Maslov index is the Maslov index of the path of unitary graph frames. -/
theorem graphMaslovIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    graphMaslovIndex γ = maslovIndex (γ.map continuous_graphFrame) :=
  (rfl)

/-- **Homotopy invariance.** Paths of symplectic matrices that are homotopic relative to their
endpoints have the same graph Maslov index. -/
theorem graphMaslovIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : graphMaslovIndex γ₀ = graphMaslovIndex γ₁ :=
  maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_graphFrame⟩)

/-- The constant path has graph Maslov index zero. -/
@[simp]
theorem graphMaslovIndex_refl (A : GLSymplectic n ℝ) : graphMaslovIndex (Path.refl A) = 0 := by
  rw [graphMaslovIndex, ← maslovIndex_refl (graphFrame A)]
  exact maslovIndex_eq_of_souriau_eq _ _ fun _ ↦ rfl

/-- **Catenation.** The graph Maslov index is additive under concatenation of paths. -/
@[simp]
theorem graphMaslovIndex_trans {A B C : GLSymplectic n ℝ} (γ : Path A B) (δ : Path B C) :
    graphMaslovIndex (γ.trans δ) = graphMaslovIndex γ + graphMaslovIndex δ := by
  rw [graphMaslovIndex, Path.map_trans, maslovIndex_trans, graphMaslovIndex, graphMaslovIndex]

/-- Reversing a path negates its graph Maslov index. -/
@[simp]
theorem graphMaslovIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    graphMaslovIndex γ.symm = -graphMaslovIndex γ := by
  rw [graphMaslovIndex, ← Path.map_symm, maslovIndex_symm, graphMaslovIndex]

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices starting at the identity,
with the sign convention `CZ(γ) = -μ_RS(graph γ, Δ)`: minus the Robbin–Salamon Maslov index of
the path of graphs relative to the diagonal. With this convention a small positive rotation of
`ℝ²` has index `-1` (`TauCeti.GLSymplectic.conleyZehnder_eq_neg_card_of_realify_diagonal`). -/
noncomputable def conleyZehnder {A : GLSymplectic n ℝ} (γ : Path 1 A) : ℝ :=
  -graphMaslovIndex γ

/-- The Conley–Zehnder index is minus the graph Maslov index. -/
theorem conleyZehnder_eq_neg_graphMaslovIndex {A : GLSymplectic n ℝ} (γ : Path 1 A) :
    conleyZehnder γ = -graphMaslovIndex γ :=
  (rfl)

/-- **Homotopy invariance.** Homotopic paths from the identity, with the same end point, have the
same Conley–Zehnder index. -/
theorem conleyZehnder_eq_of_homotopic {A : GLSymplectic n ℝ} {γ₀ γ₁ : Path 1 A}
    (h : γ₀.Homotopic γ₁) : conleyZehnder γ₀ = conleyZehnder γ₁ := by
  rw [conleyZehnder, conleyZehnder, graphMaslovIndex_eq_of_homotopic h]

/-- The constant path at the identity has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnder_refl : conleyZehnder (Path.refl (1 : GLSymplectic n ℝ)) = 0 := by
  simp [conleyZehnder]

/-- **Catenation.** Extending a path `γ` from the identity by a path `δ` changes its
Conley–Zehnder index by minus the graph Maslov index of `δ`. -/
@[simp]
theorem conleyZehnder_trans {A B : GLSymplectic n ℝ} (γ : Path 1 A) (δ : Path A B) :
    conleyZehnder (γ.trans δ) = conleyZehnder γ - graphMaslovIndex δ := by
  rw [conleyZehnder, conleyZehnder, graphMaslovIndex_trans]
  ring

/-- The Souriau map of the unitary graph frame of the realification of a diagonal unitary
matrix `diag e` is `diag (e, e)`. -/
theorem coe_souriau_graphFrame_of_realify_diagonal {A : GLSymplectic n ℝ} {e : n → ℂ}
    (he : ∀ j, star (e j) * e j = 1)
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = (diagonal e).realify) :
    (souriau (graphFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) = diagonal (Sum.elim e e) := by
  -- `A` is the realification of a unitary matrix, hence orthogonal.
  have horth : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 1 := by
    rw [hA, ← realify_conjTranspose, ← realify_mul, diagonal_conjTranspose,
      diagonal_mul_diagonal]
    simp only [Pi.star_apply, he, diagonal_one, realify_one]
  rw [coe_souriau, coe_graphFrame_of_transpose_mul_self horth, transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA,
    symplecticGraphFrame_realify_diagonal_mul_transpose, smul_smul]
  convert one_smul ℂ _
  rw [inv_ofReal_sqrt_two_mul_inv, inv_mul_cancel₀ two_ne_zero]

/-- **Paths of rotations.** If `γ t` is the realification of the diagonal unitary matrix
`diag (e^{iθ_j(t)})` with continuous angles `θ_j`, the graph Maslov index of `γ` is
`∑ j, (c(θ_j 1) - c(θ_j 0))` with `c(θ) = ⌊θ / 2π⌋ + ⌈θ / 2π⌉`: each angle counts twice the
multiples of `2π` it crosses, with half weight at the endpoints. -/
theorem graphMaslovIndex_eq_sum_of_realify_diagonal {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j ↦ Complex.exp (θ j t * Complex.I)).realify) :
    graphMaslovIndex γ = ∑ j,
      ((((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ)) : ℝ) -
        (((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ)) : ℝ)) := by
  have hunit (x : ℝ) : star (Complex.exp (x * Complex.I)) * Complex.exp (x * Complex.I) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
    simp
  -- The Souriau map of the unitary graph frame of `γ t` is `diag (e^{iθ(t)}, e^{iθ(t)})`.
  have hW (t : I) := coe_souriau_graphFrame_of_realify_diagonal (fun j ↦ hunit (θ j t)) (hγ t)
  -- It is also the Souriau map of the diagonal frame `diag (e^{iθ(t)/2}, e^{iθ(t)/2})`.
  set φ : n ⊕ n → I → ℝ := Sum.elim (fun j t ↦ θ j t / 2) (fun j t ↦ θ j t / 2)
  have hφ (k : n ⊕ n) : Continuous (φ k) := by
    rcases k with j | j <;> exact (hθ j).div_const 2
  let U : I → unitaryGroup (n ⊕ n) ℂ := fun t ↦ unitaryTorusHom (n ⊕ n) fun k ↦ Circle.exp (φ k t)
  have hU : Continuous U :=
    continuous_unitaryTorusHom.comp (continuous_pi fun k ↦ Circle.exp.continuous.comp (hφ k))
  let δ : Path (U 0) (U 1) := ⟨⟨U, hU⟩, rfl, rfl⟩
  have hsame : maslovIndex (γ.map continuous_graphFrame) = maslovIndex δ := by
    refine maslovIndex_eq_of_souriau_eq _ _ fun t ↦ Subtype.ext ?_
    rw [Path.map_coe, Function.comp_apply, hW t,
      coe_souriau_of_coe_eq_diagonal (U := δ t) (coe_unitaryTorusHom _)]
    congr 1
    funext k
    rcases k with j | j <;>
    · simp only [φ, Sum.elim_inl, Sum.elim_inr, Circle.coe_exp, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
  rw [graphMaslovIndex, hsame, maslovIndex_eq_sum_of_diagonal δ hφ fun _ ↦ coe_unitaryTorusHom _,
    Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [φ, Sum.elim_inl, Sum.elim_inr, div_div, mul_comm (2 : ℝ) Real.pi]
  ring

/-- **Normalization on rotations.** If `γ t` is the realification of `diag (e^{iθ_j(t)})` with
continuous angles starting at `θ_j(0) = 0`, then
`CZ(γ) = -∑ j, (⌊θ_j(1) / 2π⌋ + ⌈θ_j(1) / 2π⌉)`. -/
theorem conleyZehnder_eq_neg_sum_of_realify_diagonal {A : GLSymplectic n ℝ} (γ : Path 1 A)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j)) (hθ₀ : ∀ j, θ j 0 = 0)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j ↦ Complex.exp (θ j t * Complex.I)).realify) :
    conleyZehnder γ =
      -∑ j, (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ)) : ℝ) := by
  rw [conleyZehnder, graphMaslovIndex_eq_sum_of_realify_diagonal γ hθ hγ]
  simp [hθ₀]

/-- **Small positive rotations.** If `γ t` is the realification of `diag (e^{iθ_j(t)})` with
continuous angles from `θ_j(0) = 0` to `θ_j(1) ∈ (0, 2π)`, then `CZ(γ) = -n`. In particular a
small positive rotation of `ℝ²` has Conley–Zehnder index `-1`. -/
theorem conleyZehnder_eq_neg_card_of_realify_diagonal {A : GLSymplectic n ℝ} (γ : Path 1 A)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j)) (hθ₀ : ∀ j, θ j 0 = 0)
    (hθ₁ : ∀ j, 0 < θ j 1 ∧ θ j 1 < 2 * Real.pi)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j ↦ Complex.exp (θ j t * Complex.I)).realify) :
    conleyZehnder γ = -Fintype.card n := by
  rw [conleyZehnder_eq_neg_sum_of_realify_diagonal γ hθ hθ₀ hγ, Fintype.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hpos : 0 < θ j 1 / (2 * Real.pi) := div_pos (hθ₁ j).1 Real.two_pi_pos
  have hlt : θ j 1 / (2 * Real.pi) < 1 := (div_lt_one Real.two_pi_pos).2 (hθ₁ j).2
  rw [Int.floor_eq_zero_iff.2 ⟨hpos.le, hlt⟩,
    (Int.ceil_eq_iff (z := 1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩]
  norm_num

/-- **Small negative rotations.** If `γ t` is the realification of `diag (e^{iθ_j(t)})` with
continuous angles from `θ_j(0) = 0` to `θ_j(1) ∈ (-2π, 0)`, then `CZ(γ) = n`. In particular a
small negative (clockwise) rotation of `ℝ²` has Conley–Zehnder index `1`. -/
theorem conleyZehnder_eq_card_of_realify_diagonal {A : GLSymplectic n ℝ} (γ : Path 1 A)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j)) (hθ₀ : ∀ j, θ j 0 = 0)
    (hθ₁ : ∀ j, -(2 * Real.pi) < θ j 1 ∧ θ j 1 < 0)
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j ↦ Complex.exp (θ j t * Complex.I)).realify) :
    conleyZehnder γ = Fintype.card n := by
  rw [conleyZehnder_eq_neg_sum_of_realify_diagonal γ hθ hθ₀ hγ, Fintype.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hneg : θ j 1 / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (hθ₁ j).2 Real.two_pi_pos
  have hgt : -1 < θ j 1 / (2 * Real.pi) := by
    rw [lt_div_iff₀ Real.two_pi_pos]
    linarith [(hθ₁ j).1]
  rw [(Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
    (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩]
  norm_num

end TauCeti.GLSymplectic
