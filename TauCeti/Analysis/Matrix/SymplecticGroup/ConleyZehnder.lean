/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
public import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
import TauCeti.Topology.Instances.Matrix

/-!
# The Conley–Zehnder index of a path of symplectic matrices

Let `Ψ : [0, 1] → Sp(2n)` be a path of real symplectic matrices on `ℝ^{n ⊕ n}`. Its graphs form a
path of Lagrangian subspaces `Γ(Ψ t) ⊆ ℂⁿ × ℂⁿ` (`Matrix.graphFrame`), and the diagonal
`Δ = Γ(1)` is one more Lagrangian. The **Conley–Zehnder index** of `Ψ`
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is

`CZ(Ψ) = -μ_RS(Γ ∘ Ψ, Δ)`,

minus the Robbin–Salamon index of the graph path relative to the diagonal. For paths that start at
the identity and end at a matrix without eigenvalue `1`, it is the Conley–Zehnder index used to
grade Hamiltonian Floer complexes. With this sign a small positive rotation of `ℝ²` has index `-1`.

**The chart.** The complex matrix `W = diagonalChart n`, `(a, b) ↦ (a + b, i (a - b))`, is `√2`
times a unitary matrix and carries `Δ` onto the real points `ℝ^{n ⊕ n}`. So `Γ(A)` relative to `Δ`
is `W Γ(A)` relative to `ℝ^{n ⊕ n}`, and `W Γ(A)` is spanned by the columns of

`W * graphFrame A = (1 + A) - i J (A - 1)`

(`Matrix.diagonalChart_mul_graphFrame`, `Matrix.diagonalGraphFrame`). For symplectic `A` its Gram
matrix is the real matrix `2 (1 + Aᵀ A)` (`Matrix.conjTranspose_diagonalGraphFrame_mul_self`), so
`W Γ(A)` is Lagrangian and the real orthonormalization of this frame is a unitary frame of it
(`TauCeti.GLSymplectic.graphUnitaryFrame`). The index is then
`-Matrix.UnitaryGroup.maslovIndex` of the resulting path of unitary frames, which is Souriau's
formula for the Robbin–Salamon index relative to `ℝ^{n ⊕ n}`.

**Formal properties.** Being a Robbin–Salamon index, `CZ` is invariant under homotopies with fixed
endpoints, additive under catenation, and odd under reversal
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopic`,
`TauCeti.GLSymplectic.conleyZehnderIndex_trans`,
`TauCeti.GLSymplectic.conleyZehnderIndex_symm`).

**The signature formula.** If `1 + A` is invertible, then `Γ(A)` is transverse to the graph of
`-1`, and `W Γ(A)` is the graph `{v + i B v}` of the symmetric matrix

`B = J (1 - A) (1 + A)⁻¹`

(`Matrix.symplecticCayley`, `Matrix.isHermitian_symplecticCayley`,
`Matrix.diagonalGraphFrame_eq_mul`).
By the localization axiom of Robbin and Salamon, along a path with `1 + Ψ t` invertible for every
`t` the index is minus half the change of the signature of `B`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_signature`).

**Normalization.** For a symmetric matrix `S` the matrix `J S` lies in the symplectic Lie algebra,
and `t ↦ exp (t ε J S)` is a path of symplectic matrices from the identity
(`TauCeti.GLSymplectic.expPath`). If `S` is nondegenerate, then for all small `ε > 0`

`CZ(t ↦ exp (t ε J S)) = -sign (S) / 2`

(`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_expPath`). The proof computes that
`ε⁻¹ B(exp (ε J S))` tends to `S / 2` as `ε → 0`, so these symmetric matrices eventually have the
signature of `S`. For `S = 1` the path `t ↦ exp (t ε J)` turns each complex coordinate of
`ℂⁿ = ℝ^{n ⊕ n}` positively by the angle `t ε`, and its index is `-n`
(`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_expPath_J`).

For a Hamiltonian `H` with `ι_{X_H} ω = dH`, the linearized flow at a critical point is
`exp (t J S)` with `S = -Hess H`, so this normalization gives the index `n - ind_Morse (H)` of the
constant orbit at a critical point of a small Morse function.

## Main definitions

* `Matrix.diagonalChart`: the chart `(a, b) ↦ (a + b, i (a - b))` carrying the diagonal to
  `ℝ^{n ⊕ n}`.
* `Matrix.diagonalGraphFrame`: the frame `(1 + A) - i J (A - 1)` of the graph in this chart.
* `Matrix.symplecticCayley`: the symmetric matrix `J (1 - A) (1 + A)⁻¹` of a symplectic `A`.
* `TauCeti.GLSymplectic.graphUnitaryFrame`: the unitary frame of the graph in this chart.
* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a path.
* `TauCeti.GLSymplectic.expPath`: the path `t ↦ exp (t X)` for `X` in the symplectic Lie algebra.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Sections 2 and 4 (the index of a path of Lagrangians, its localization axiom, and the index of a
  symplectic path as the index of its graph relative to the diagonal).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Section 2.4 (the Conley–Zehnder index and its normalization on
  `exp (t J S)`).
-/

public section

open Matrix Filter Topology
open scoped unitInterval Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix `1 + 1` on `ℝ^{n ⊕ n}` is invertible. -/
private theorem det_one_add_one_ne_zero : (1 + 1 : Matrix (n ⊕ n) (n ⊕ n) ℝ).det ≠ 0 := by
  rw [← two_smul ℝ (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ), det_smul, det_one, mul_one]
  exact pow_ne_zero _ two_ne_zero

/-! ### The graph relative to the diagonal -/

/-- The **diagonal chart** of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`, the complex matrix
`(a, b) ↦ (a + b, i (a - b))` (`Matrix.diagonalChart_mulVec`). It is `√2` times a unitary matrix
(`Matrix.conjTranspose_diagonalChart_mul_self`), and it carries the diagonal `{(conj z, z)}`, the
graph of the identity, onto the real points `ℝ^{n ⊕ n}` (`Matrix.realImage_diagonalGraphFrame_one`).
-/
noncomputable def diagonalChart (n : Type*) [DecidableEq n] :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 1 (Complex.I • 1) (-(Complex.I • 1))

/-- The diagonal chart sends `(a, b)` to `(a + b, i (a - b))`. -/
theorem diagonalChart_mulVec (a b : n → ℂ) :
    diagonalChart n *ᵥ Sum.elim a b = Sum.elim (a + b) (Complex.I • (a - b)) := by
  ext (i | i) <;>
    simp [diagonalChart, fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.neg_mulVec, sub_eq_add_neg]

/-- The diagonal chart is `√2` times a unitary matrix. -/
theorem conjTranspose_diagonalChart_mul_self :
    (diagonalChart n)ᴴ * diagonalChart n = (2 : ℂ) • 1 := by
  rw [diagonalChart, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_smul]
  simp only [conjTranspose_one, conjTranspose_neg, conjTranspose_smul, Complex.star_def,
    Complex.conj_I, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, smul_smul, neg_smul, neg_neg,
    smul_neg]
  congr 1 <;> simp [two_smul]

/-- The **graph frame relative to the diagonal** of a real matrix `A` on `ℝ^{n ⊕ n}`: the complex
matrix `(1 + A) - i J (A - 1)`. It is the graph frame `Matrix.graphFrame A` followed by the
diagonal chart (`Matrix.diagonalChart_mul_graphFrame`), so its columns span the image under the
diagonal chart of the graph of `A`. -/
noncomputable def diagonalGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (1 + A).map ((↑) : ℝ → ℂ) - Complex.I • (J n ℝ * (A - 1)).map ((↑) : ℝ → ℂ)

/-- The graph frame relative to the diagonal is the graph frame followed by the diagonal chart. -/
@[simp]
theorem diagonalChart_mul_graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    diagonalChart n * graphFrame A = diagonalGraphFrame A := by
  have hmap (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (x : n ⊕ n → ℝ) :
      M.map ((↑) : ℝ → ℂ) *ᵥ (fun k => (x k : ℂ)) = fun k => ((M *ᵥ x) k : ℂ) :=
    funext fun k => (RingHom.map_mulVec Complex.ofRealHom M x k).symm
  have hJ (v : n ⊕ n → ℝ) : J n ℝ *ᵥ v = Sum.elim (-(v ∘ Sum.inr)) (v ∘ Sum.inl) := by
    ext (i | i) <;> simp [J, fromBlocks_mulVec, Matrix.neg_mulVec]
  have key (x : n ⊕ n → ℝ) : (diagonalChart n * graphFrame A) *ᵥ (fun k => (x k : ℂ)) =
      diagonalGraphFrame A *ᵥ (fun k => (x k : ℂ)) := by
    rw [← Matrix.mulVec_mulVec, graphFrame_mulVec, diagonalChart_mulVec, diagonalGraphFrame,
      Matrix.sub_mulVec, Matrix.smul_mulVec, hmap, hmap, ← Matrix.mulVec_mulVec, hJ]
    ext (i | i) <;> simp [Matrix.add_mulVec, Matrix.sub_mulVec] <;> ring_nf; simp
  -- Two complex matrices agreeing on the real vectors are equal.
  ext i j
  have hx : (fun k => ((Pi.single j (1 : ℝ) : n ⊕ n → ℝ) k : ℂ)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  simpa [hx, mulVec_single_one] using congrFun (key (Pi.single j 1)) i

/-- The columns of the graph frame relative to the diagonal span the image of the graph `Γ(A)`
under the diagonal chart. -/
theorem realImage_diagonalGraphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (diagonalGraphFrame A).realImage = (graphSubspace A).map
      (((toEuclideanCLM (𝕜 := ℂ) (diagonalChart n) :
        EuclideanSpace ℂ (n ⊕ n) →L[ℂ] EuclideanSpace ℂ (n ⊕ n)) :
          EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ) := by
  rw [← diagonalChart_mul_graphFrame, realImage_mul]
  congr 1
  -- `Matrix.graphSubspace A` is the real span of the columns of `Matrix.graphFrame A`.
  ext w
  rw [mem_graphSubspace_iff, mem_realImage]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : WithLp.ofLp v = fun k => ((v k).re : ℂ) :=
      funext fun k => Complex.ext rfl (by simp [mem_realSubspace.1 hv k])
    refine ⟨fun k => (v k).re, ?_⟩
    rw [toEuclideanCLM_apply, toLpLin_apply, hv', graphFrame_mulVec]
    simp only [Complex.ofReal_re]
  · rintro ⟨x, rfl⟩
    refine ⟨WithLp.toLp 2 fun k => (x k : ℂ), mem_realSubspace.2 fun _ => by simp, ?_⟩
    rw [toEuclideanCLM_apply]
    exact congrArg (WithLp.toLp 2) (graphFrame_mulVec A x)

/-- At the identity the graph frame relative to the diagonal is the real matrix `2`. -/
theorem diagonalGraphFrame_one :
    diagonalGraphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (2 : Matrix (n ⊕ n) (n ⊕ n) ℝ).map ((↑) : ℝ → ℂ) := by
  rw [diagonalGraphFrame, sub_self, Matrix.mul_zero, Matrix.map_zero _ (by simp), smul_zero,
    sub_zero, one_add_one_eq_two]

/-- The diagonal chart carries the diagonal, the graph of the identity, onto the real points. -/
theorem realImage_diagonalGraphFrame_one :
    (diagonalGraphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage = realSubspace (n ⊕ n) := by
  rw [diagonalGraphFrame_one]
  refine realImage_map_ofReal ((isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ ?_))
  rw [← one_add_one_eq_two]
  exact det_one_add_one_ne_zero

/-- The graph frame relative to the diagonal depends continuously on the matrix. -/
@[fun_prop]
theorem continuous_diagonalGraphFrame :
    Continuous (diagonalGraphFrame : Matrix (n ⊕ n) (n ⊕ n) ℝ → _) := by
  unfold diagonalGraphFrame
  fun_prop

/-- **The graph of a symplectic matrix is Lagrangian.** For symplectic `A` the Gram matrix of the
graph frame relative to the diagonal is the real matrix `2 (1 + Aᵀ A)`; its imaginary part, the
standard symplectic form on the columns, vanishes. -/
theorem conjTranspose_diagonalGraphFrame_mul_self {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (diagonalGraphFrame A)ᴴ * diagonalGraphFrame A =
      (2 * (1 + Aᵀ * A)).map ((↑) : ℝ → ℂ) := by
  have hA' : Aᵀ * J n ℝ * A = J n ℝ := SymplecticGroup.mem_iff'.1 hA
  -- The Gram matrix of `P + i Q` for real `P` and `Q`.
  have hgram (P Q : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
      (P.map ((↑) : ℝ → ℂ) + Complex.I • Q.map ((↑) : ℝ → ℂ))ᴴ *
          (P.map ((↑) : ℝ → ℂ) + Complex.I • Q.map ((↑) : ℝ → ℂ)) =
        (Pᵀ * P + Qᵀ * Q).map ((↑) : ℝ → ℂ) +
          Complex.I • (Pᵀ * Q - Qᵀ * P).map ((↑) : ℝ → ℂ) := by
    ext i j
    apply Complex.ext <;>
      simp [Matrix.mul_apply, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib] <;> ring
  rw [diagonalGraphFrame, sub_eq_add_neg, ← smul_neg, ← Matrix.map_neg _ Complex.ofReal_neg, hgram]
  have hJ : (J n ℝ)ᵀ * J n ℝ = 1 := by rw [J_transpose, Matrix.neg_mul, J_squared, neg_neg]
  have h1 : (1 + A)ᵀ * (1 + A) + (-(J n ℝ * (A - 1)))ᵀ * -(J n ℝ * (A - 1)) =
      2 * (1 + Aᵀ * A) := by
    rw [transpose_neg, neg_mul_neg, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (J n ℝ)ᵀ, hJ, Matrix.one_mul, transpose_add, transpose_sub,
      transpose_one]
    noncomm_ring
  have h2 : (1 + A)ᵀ * -(J n ℝ * (A - 1)) - (-(J n ℝ * (A - 1)))ᵀ * (1 + A) = 0 := by
    rw [transpose_neg, transpose_mul, J_transpose, transpose_add, transpose_sub, transpose_one]
    calc _ = 2 * (J n ℝ - Aᵀ * J n ℝ * A) := by noncomm_ring
      _ = 0 := by rw [hA', sub_self, mul_zero]
  rw [h1, h2, Matrix.map_zero _ (by simp), smul_zero, add_zero]

/-- For symplectic `A` the graph frame relative to the diagonal is invertible. -/
theorem isUnit_det_diagonalGraphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) : IsUnit (diagonalGraphFrame A).det := by
  have hpos : (2 * (1 + Aᵀ * A)).PosDef := by
    have h1 : (1 + Aᵀ * A).PosDef := (PosDef.one (R := ℝ) (n := n ⊕ n)).add_posSemidef
      (by simpa using posSemidef_conjTranspose_mul_self A)
    rw [two_mul]
    exact h1.add h1
  have h : star (diagonalGraphFrame A).det * (diagonalGraphFrame A).det =
      ((2 * (1 + Aᵀ * A)).det : ℂ) := by
    rw [← det_conjTranspose, ← det_mul, conjTranspose_diagonalGraphFrame_mul_self hA]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at h
  exact hpos.det_pos.ne' (by exact_mod_cast h.symm)

/-! ### The symplectic Cayley transform -/

/-- The **symplectic Cayley transform** `J (1 - A) (1 + A)⁻¹` of a real matrix `A` on
`ℝ^{n ⊕ n}`. When `A` is symplectic and `1 + A` is invertible, it is symmetric
(`Matrix.isHermitian_symplecticCayley`), and the diagonal chart carries the graph of `A` to the
graph `{v + i B v}` of `B = symplecticCayley A` (`Matrix.diagonalGraphFrame_eq_mul`). -/
noncomputable def symplecticCayley (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  J n ℝ * (1 - A) * (1 + A)⁻¹

/-- The symplectic Cayley transform of the identity is zero. -/
@[simp]
theorem symplecticCayley_one : symplecticCayley (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 0 := by
  simp [symplecticCayley]

/-- If `1 + A` is invertible, then `symplecticCayley A * (1 + A) = J (1 - A)`. -/
theorem symplecticCayley_mul {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (1 + A).det) :
    symplecticCayley A * (1 + A) = J n ℝ * (1 - A) := by
  rw [symplecticCayley, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]

/-- The symplectic Cayley transform of a symplectic matrix `A` with `1 + A` invertible is
symmetric. -/
theorem isHermitian_symplecticCayley {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) (h : IsUnit (1 + A).det) :
    (symplecticCayley A).IsHermitian := by
  have hA' : Aᵀ * J n ℝ * A = J n ℝ := SymplecticGroup.mem_iff'.1 hA
  have hP : IsUnit (1 + A) := (isUnit_iff_isUnit_det _).2 h
  have hPT : IsUnit (1 + A)ᵀ := (isUnit_iff_isUnit_det _).2 (by rwa [det_transpose])
  have hT : (1 + A)ᵀ * (symplecticCayley A)ᵀ = (J n ℝ * (1 - A))ᵀ := by
    rw [← transpose_mul, symplecticCayley_mul h]
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  -- Compare `(1 + A)ᵀ * Bᵀ * (1 + A)` with `(1 + A)ᵀ * B * (1 + A)`.
  refine hPT.mul_left_cancel (hP.mul_right_cancel ?_)
  rw [hT, Matrix.mul_assoc, symplecticCayley_mul h, transpose_mul, transpose_sub, transpose_one,
    J_transpose, transpose_add, transpose_one]
  calc _ = (1 + Aᵀ) * (J n ℝ * (1 - A)) + 2 * (Aᵀ * J n ℝ * A - J n ℝ) := by noncomm_ring
    _ = _ := by rw [hA', sub_self, mul_zero, add_zero]

/-- If `1 + A` is invertible, the graph frame relative to the diagonal is
`(1 + i B) (1 + A)` for `B = symplecticCayley A`: the diagonal chart carries the graph of `A` to
the graph `{v + i B v}` of `B`. -/
theorem diagonalGraphFrame_eq_mul {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (h : IsUnit (1 + A).det) :
    diagonalGraphFrame A =
      (1 + Complex.I • (symplecticCayley A).map ((↑) : ℝ → ℂ)) * (1 + A).map ((↑) : ℝ → ℂ) := by
  have hM : (symplecticCayley A).map ((↑) : ℝ → ℂ) * (1 + A).map ((↑) : ℝ → ℂ) =
      (symplecticCayley A * (1 + A)).map ((↑) : ℝ → ℂ) :=
    (Matrix.map_mul (f := Complex.ofRealHom)).symm
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hM, symplecticCayley_mul h,
    diagonalGraphFrame, sub_eq_add_neg, ← smul_neg, ← Matrix.map_neg _ Complex.ofReal_neg,
    ← Matrix.mul_neg, neg_sub]

/-- The rescaled symplectic Cayley transforms `ε⁻¹ B(exp (ε J S))` tend to `S / 2` as `ε → 0`. -/
theorem tendsto_inv_smul_symplecticCayley_exp (S : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ • symplecticCayley (NormedSpace.exp (ε • (J n ℝ * S)))) (𝓝[≠] 0)
      (𝓝 ((2⁻¹ : ℝ) • S)) := by
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) (J n ℝ * S) 0
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at hd
  -- The difference quotient of `ε ↦ exp (ε J S)` at `0` tends to `J S`.
  have h1 : Tendsto (fun ε : ℝ => ε⁻¹ • (NormedSpace.exp (ε • (J n ℝ * S)) - 1)) (𝓝[≠] 0)
      (𝓝 (J n ℝ * S)) := by
    refine hd.tendsto_slope.congr fun ε => ?_
    rw [slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero]
  -- The inverses `(1 + exp (ε J S))⁻¹` tend to `(1 + 1)⁻¹`.
  have h2 : Tendsto (fun ε : ℝ => (1 + NormedSpace.exp (ε • (J n ℝ * S)))⁻¹) (𝓝[≠] 0)
      (𝓝 (1 + 1)⁻¹) := by
    have h0 : 1 + NormedSpace.exp ((0 : ℝ) • (J n ℝ * S)) = 1 + 1 := by
      rw [zero_smul, NormedSpace.exp_zero]
    have hc : ContinuousAt (fun ε : ℝ => 1 + NormedSpace.exp (ε • (J n ℝ * S))) 0 :=
      continuousAt_const.add hd.continuousAt
    have h := (hc.matrix_inv (by rw [h0]; exact det_one_add_one_ne_zero)).tendsto
    replace h := h.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [h0] at h
  have hlim : J n ℝ * -(J n ℝ * S) * (1 + 1)⁻¹ = (2⁻¹ : ℝ) • S := by
    have hinv : (1 + 1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)⁻¹ = (2⁻¹ : ℝ) • 1 := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.mul_smul, Matrix.mul_one, ← two_smul ℝ (1 : Matrix _ _ ℝ), smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [hinv, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, J_squared]
    simp
  rw [← hlim]
  refine ((h1.neg.const_mul (J n ℝ)).mul h2).congr' (Eventually.of_forall fun ε => ?_)
  dsimp only
  rw [symplecticCayley, Matrix.mul_neg, Matrix.mul_smul, Matrix.neg_mul, Matrix.smul_mul,
    ← smul_neg, ← Matrix.neg_mul, ← Matrix.mul_neg, neg_sub]

/-- Near `τ = 0` the matrix `1 + exp (τ X)` is invertible. -/
theorem eventually_isUnit_det_one_add_exp_smul (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), IsUnit (1 + NormedSpace.exp (τ • X)).det := by
  have hc : ContinuousAt (fun τ : ℝ => (1 + NormedSpace.exp (τ • X)).det) 0 :=
    ContinuousAt.comp (g := det) continuous_id.matrix_det.continuousAt
      (continuousAt_const.add (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).continuousAt)
  have h0 : (1 + NormedSpace.exp ((0 : ℝ) • X)).det ≠ 0 := by
    rw [zero_smul, NormedSpace.exp_zero]
    exact det_one_add_one_ne_zero
  filter_upwards [hc.eventually_ne h0] with τ hτ using isUnit_iff_ne_zero.2 hτ

/-- For a nondegenerate symmetric matrix `S` and all small `ε > 0`, the symplectic Cayley
transform of `exp (ε J S)` has the signature of `S`: after rescaling by `ε⁻¹` it tends to the
nondegenerate matrix `S / 2`. -/
theorem eventually_signature_symplecticCayley_exp {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsHermitian) (hdet : IsUnit S.det) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      signature (symplecticCayley (NormedSpace.exp (ε • (J n ℝ * S)))) = signature S := by
  have hL : ((2⁻¹ : ℝ) • S).IsHermitian := hS.smul (IsSelfAdjoint.all _)
  have hLdet : IsUnit ((2⁻¹ : ℝ) • S).det := by
    rw [det_smul]
    exact ((IsUnit.mk0 _ (inv_ne_zero two_ne_zero)).pow _).mul hdet
  have hlim := (tendsto_inv_smul_symplecticCayley_exp S).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  filter_upwards [hlim.eventually (hL.eventually_signature_eq hLdet), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_isUnit_det_one_add_exp_smul (J n ℝ * S))] with ε hε hpos hεU
  have hB : (ε⁻¹ • symplecticCayley (NormedSpace.exp (ε • (J n ℝ * S)))).IsHermitian :=
    (isHermitian_symplecticCayley (exp_mem_symplecticGroup_of_mem_sp _
      ((LieAlgebra.Symplectic.sp n ℝ).smul_mem ε (LieAlgebra.Symplectic.J_mul_mem_sp hS)))
        hεU).smul (IsSelfAdjoint.all _)
  calc signature (symplecticCayley (NormedSpace.exp (ε • (J n ℝ * S))))
      = signature (ε⁻¹ • symplecticCayley (NormedSpace.exp (ε • (J n ℝ * S)))) :=
        (signature_smul_of_pos (inv_pos.2 hpos) _).symm
    _ = hB.signature := (IsHermitian.signature_map_ofReal (𝕜 := ℝ) (M := _) hB).symm
    _ = hL.signature := hε hB
    _ = signature ((2⁻¹ : ℝ) • S) := IsHermitian.signature_map_ofReal (𝕜 := ℝ) (M := _) hL
    _ = signature S := signature_smul_of_pos (inv_pos.2 two_pos) _

end Matrix

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The unitary frame of the graph relative to the diagonal -/

/-- The graph frame relative to the diagonal of a symplectic matrix, as an invertible matrix. -/
private noncomputable def diagonalGraphFrameGL (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  ((isUnit_iff_isUnit_det _).2
    (isUnit_det_diagonalGraphFrame (mem_iff_mem_symplecticGroup.1 A.2))).unit

private theorem coe_diagonalGraphFrameGL (A : GLSymplectic n ℝ) :
    (diagonalGraphFrameGL A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  (rfl)

private theorem continuous_diagonalGraphFrameGL : Continuous (diagonalGraphFrameGL (n := n)) :=
  IsOpenUnits.isOpenEmbedding_unitsVal.continuous_iff.2 <|
    continuous_diagonalGraphFrame.comp (Units.continuous_val.comp continuous_subtype_val)

/-- The **unitary frame of the graph** of a symplectic matrix `A` relative to the diagonal: the real
orthonormalization of `Matrix.diagonalGraphFrame A`. Its columns span the image of the graph of `A`
under the diagonal chart (`TauCeti.GLSymplectic.realImage_graphUnitaryFrame`); that it is unitary
says that the graph is Lagrangian. -/
noncomputable def graphUnitaryFrame (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  ⟨GeneralLinearGroup.realOrthonormalize (diagonalGraphFrameGL A),
    GeneralLinearGroup.realOrthonormalize_mem_unitaryGroup (by
      rw [coe_diagonalGraphFrameGL,
        conjTranspose_diagonalGraphFrame_mul_self (mem_iff_mem_symplecticGroup.1 A.2)]
      ext
      simp)⟩

/-- The unitary frame of the graph spans the same real subspace as the graph frame relative to the
diagonal. -/
theorem realImage_graphUnitaryFrame (A : GLSymplectic n ℝ) :
    (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).realImage := by
  rw [graphUnitaryFrame, Subtype.coe_mk, GeneralLinearGroup.realImage_realOrthonormalize,
    coe_diagonalGraphFrameGL]

/-- The unitary frame of the graph depends continuously on the symplectic matrix. -/
theorem continuous_graphUnitaryFrame : Continuous (graphUnitaryFrame (n := n)) :=
  (Units.continuous_val.comp
    (GeneralLinearGroup.continuous_realOrthonormalize continuous_diagonalGraphFrameGL)).subtype_mk _

/-- If `1 + A` is invertible, the unitary frame of the graph of `A` has Souriau map the Cayley
transform of `symplecticCayley A`: it frames the graph `{v + i B v}` of this symmetric matrix. -/
theorem souriau_graphUnitaryFrame {A : GLSymplectic n ℝ}
    (h : IsUnit (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    (UnitaryGroup.souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      cayley ((symplecticCayley ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map (↑)) := by
  obtain ⟨R, hR⟩ : ∃ R : Matrix (n ⊕ n) (n ⊕ n) ℝ,
      (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
        diagonalGraphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) * R.map (↑) :=
    ⟨_, by rw [graphUnitaryFrame, Subtype.coe_mk, GeneralLinearGroup.coe_realOrthonormalize,
      coe_diagonalGraphFrameGL]⟩
  refine UnitaryGroup.souriau_eq_cayley_of_coe_eq_mul
    (M := (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) * R)
    (isHermitian_symplecticCayley (mem_iff_mem_symplecticGroup.1 A.2) h) ?_
  rw [hR, diagonalGraphFrame_eq_mul h, Matrix.mul_assoc]
  exact congrArg _ (Matrix.map_mul (f := Complex.ofRealHom)).symm

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** of a path `γ` of real symplectic matrices: minus the
Robbin–Salamon index of the path of graphs `Γ(γ t)` relative to the diagonal `Γ(1)`. It is computed
as `-Matrix.UnitaryGroup.maslovIndex` of the unitary frames of the graphs in the diagonal chart,
which carries the diagonal onto `ℝ^{n ⊕ n}`. -/
noncomputable def conleyZehnderIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  -UnitaryGroup.maslovIndex (γ.map continuous_graphUnitaryFrame)

/-- **Homotopy invariance.** Paths of symplectic matrices that are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex, conleyZehnderIndex,
    UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_graphUnitaryFrame⟩)]

/-- The constant path has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl (A : GLSymplectic n ℝ) :
    conleyZehnderIndex (Path.refl A) = 0 := by
  have h : (Path.refl A).map continuous_graphUnitaryFrame = Path.refl _ := rfl
  rw [conleyZehnderIndex, h, UnitaryGroup.maslovIndex_refl, neg_zero]

/-- **Catenation.** The Conley–Zehnder index of a concatenation of paths is the sum of their
indices. -/
@[simp]
theorem conleyZehnderIndex_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    conleyZehnderIndex (γ₁.trans γ₂) = conleyZehnderIndex γ₁ + conleyZehnderIndex γ₂ := by
  rw [conleyZehnderIndex, Path.map_trans, UnitaryGroup.maslovIndex_trans, neg_add]
  rfl

/-- Reversing a path negates its Conley–Zehnder index. -/
@[simp]
theorem conleyZehnderIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ.symm = -conleyZehnderIndex γ := by
  rw [conleyZehnderIndex, ← Path.map_symm, UnitaryGroup.maslovIndex_symm, conleyZehnderIndex]

/-- **The signature formula.** Along a path `γ` of symplectic matrices with `1 + γ t` invertible
for every `t`, the Conley–Zehnder index is minus half the change of the signature of the symmetric
matrices `symplecticCayley (γ t)`. -/
theorem conleyZehnderIndex_eq_signature {A B : GLSymplectic n ℝ} (γ : Path A B)
    (h : ∀ t, IsUnit (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    conleyZehnderIndex γ =
      -(signature (symplecticCayley ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) -
        signature (symplecticCayley ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) : ℝ) / 2 := by
  have hγc : Continuous fun t => ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
    Units.continuous_val.comp (continuous_subtype_val.comp γ.continuous)
  have hc : Continuous fun t =>
      symplecticCayley ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    refine (continuous_const.matrix_mul (continuous_const.sub hγc)).matrix_mul ?_
    exact continuous_iff_continuousAt.2 fun t =>
      (continuous_const.add hγc).continuousAt.matrix_inv (h t).ne_zero
  have key := UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley
    (γ.map continuous_graphUnitaryFrame) hc
    (fun t => isHermitian_symplecticCayley (mem_iff_mem_symplecticGroup.1 (γ t).2) (h t))
    (fun t => souriau_graphUnitaryFrame (h t))
  simp only [Path.source, Path.target] at key
  rw [conleyZehnderIndex, key, neg_div]

/-! ### Normalization on exponential paths -/

/-- The exponential of an element of the symplectic Lie algebra, as a symplectic matrix. -/
noncomputable def exp (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ) :
    GLSymplectic n ℝ :=
  ⟨(Matrix.isUnit_exp X).unit, mem_iff_mem_symplecticGroup.2 <| by
    rw [IsUnit.unit_spec]
    exact Matrix.exp_mem_symplecticGroup_of_mem_sp X hX⟩

/-- The exponential of `X` as a symplectic matrix is the matrix exponential of `X`. -/
@[simp]
theorem coe_exp (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ) :
    ((exp X hX : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = NormedSpace.exp X :=
  (rfl)

/-- The path `t ↦ exp (t X)` of symplectic matrices from the identity to `exp X`, for `X` in the
symplectic Lie algebra. -/
noncomputable def expPath (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ) :
    Path (1 : GLSymplectic n ℝ) (exp X hX) where
  toFun t := exp ((t : ℝ) • X) ((LieAlgebra.Symplectic.sp n ℝ).smul_mem t hX)
  continuous_toFun := by
    refine Continuous.subtype_mk (IsOpenUnits.isOpenEmbedding_unitsVal.continuous_iff.2 ?_) _
    exact continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (t : ℝ)).continuousAt.comp
        continuous_subtype_val.continuousAt
  source' := Subtype.ext (Units.ext (by simp))
  target' := Subtype.ext (Units.ext (by simp))

/-- At time `t` the exponential path is `exp (t X)`. -/
theorem expPath_apply (X : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ)
    (t : I) : expPath X hX t = exp ((t : ℝ) • X) ((LieAlgebra.Symplectic.sp n ℝ).smul_mem t hX) :=
  (rfl)

/-- **Normalization of the Conley–Zehnder index.** For a nondegenerate symmetric matrix `S` and all
small `ε > 0`, the path `t ↦ exp (t ε J S)` has Conley–Zehnder index `-sign (S) / 2`. -/
theorem eventually_conleyZehnderIndex_expPath {S : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hS : S.IsHermitian) (hdet : IsUnit S.det) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), conleyZehnderIndex (expPath (ε • (J n ℝ * S))
      ((LieAlgebra.Symplectic.sp n ℝ).smul_mem ε (LieAlgebra.Symplectic.J_mul_mem_sp hS))) =
        -(signature S : ℝ) / 2 := by
  obtain ⟨δ, hδ, hδU⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_isUnit_det_one_add_exp_smul (J n ℝ * S))
  filter_upwards [eventually_signature_symplecticCayley_exp hS hdet, Ioo_mem_nhdsGT hδ]
    with ε hε hεδ
  rw [conleyZehnderIndex_eq_signature _ fun t => ?_]
  · simp [hε]
  · -- Along the path, `1 + exp (t ε J S)` is invertible since `0 ≤ t ε < δ`.
    rw [expPath_apply, coe_exp, smul_smul]
    refine hδU ?_
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg t.2.1, abs_of_pos hεδ.1]
    exact (mul_le_of_le_one_left hεδ.1.le t.2.2).trans_lt hεδ.2

/-- **A small positive rotation of `ℂⁿ` has Conley–Zehnder index `-n`.** For all small `ε > 0`,
the path `t ↦ exp (t ε J)`, which turns each complex coordinate of `ℂⁿ = ℝ^{n ⊕ n}` positively by
the angle `t ε`, has Conley–Zehnder index `-n`. -/
theorem eventually_conleyZehnderIndex_expPath_J :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), conleyZehnderIndex (expPath (ε • J n ℝ)
      ((LieAlgebra.Symplectic.sp n ℝ).smul_mem ε
        (by simp))) =
        -(Fintype.card n : ℝ) := by
  filter_upwards [eventually_conleyZehnderIndex_expPath (isHermitian_one (n := n ⊕ n) (α := ℝ))
    (by simp)] with ε hε
  have hsig : signature (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 2 * Fintype.card n := by
    rw [← diagonal_one, signature_diagonal]
    simp [Fintype.card_sum, two_mul]
  have hcongr : ∀ (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hX : X ∈ LieAlgebra.Symplectic.sp n ℝ)
      (hY : Y ∈ LieAlgebra.Symplectic.sp n ℝ), X = Y →
        conleyZehnderIndex (expPath X hX) = conleyZehnderIndex (expPath Y hY) := by
    rintro X Y hX hY rfl
    rfl
  rw [hcongr (ε • J n ℝ) (ε • (J n ℝ * 1)) _
    ((LieAlgebra.Symplectic.sp n ℝ).smul_mem ε (LieAlgebra.Symplectic.J_mul_mem_sp
      (isSymm_one (n := n ⊕ n) (α := ℝ)))) (by rw [Matrix.mul_one]), hε, hsig]
  push_cast
  ring

end TauCeti.GLSymplectic
