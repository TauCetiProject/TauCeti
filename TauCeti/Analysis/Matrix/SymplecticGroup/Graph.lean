/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The graph of a loop of symplectic matrices and its Maslov index

Identify `ℝ^{n ⊕ n}` with `ℂⁿ` by `φ (x, y) = x + i y`, the convention of `Matrix.realify`, so that
the standard symplectic form and complex structure of `ℝ^{n ⊕ n}` are those of `ℂⁿ`. The graph of
a symplectic matrix `A` is a Lagrangian subspace of `ℝ^{n ⊕ n} × ℝ^{n ⊕ n}` with the symplectic
form `(-ω) ⊕ ω`. Its first factor carries the complex structure `-J`, which `conj ∘ φ` turns into
multiplication by `i`. So in `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}` the graph is the real subspace

`Γ(A) = {(conj (φ x), φ (A x)) | x ∈ ℝ^{n ⊕ n}}`

(`Matrix.graphSubspace`, characterized by `Matrix.mem_graphSubspace_iff`). It is the image
`Matrix.realImage` of the real points `TauCeti.realSubspace` of `ℂ^{n ⊕ n}` under the complex
matrix `Matrix.graphFrame A`, whose columns are the images of the real basis vectors. That matrix
is invertible when `A` is symplectic (`Matrix.isUnit_det_graphFrame`), so the graphs
of a loop `γ` of symplectic matrices form a loop of maximal totally real subspaces with a continuous
frame (`TauCeti.GLSymplectic.graphLoop`).

The main result is that **the Maslov index of the graph loop is twice the Maslov index of the
loop**, `μ(Γ ∘ γ) = 2 μ(γ)` (`TauCeti.GLSymplectic.maslovIndex_graphLoop`). Here `μ(γ)` is the
degree of `t ↦ ρ(γ t)` (`TauCeti.GLSymplectic.maslovIndex`) and `μ(Γ ∘ γ)` is the native Maslov
index of loops of totally real subspaces (`TauCeti.TotallyRealLoop.maslovIndex`), the degree of the
determinant phase `det / conj det` of a frame. This fixes the factor two between the Maslov index of
a loop of symplectic matrices, which measures the winding of a symplectic trivialization along a
loop, and the Maslov index of its graph.

Graphs relative to the diagonal are also how the Conley–Zehnder index of symplectic paths is
expressed as a Robbin–Salamon index, which needs unitary frames. For symplectic `A` the graph frame
`F` has the real positive definite Gram matrix `Fᴴ F = 1 + Aᵀ A`
(`Matrix.conjTranspose_graphFrame_mul_graphFrame`), so its real orthonormalization
(`Matrix.GeneralLinearGroup.realOrthonormalize`) `F (1 + Aᵀ A) ^ (-1/2)` is a unitary frame of the
graph (`TauCeti.GLSymplectic.graphUnitary`), depending continuously on `A`. Moving it by the
inverse of the unitary frame of the diagonal gives `TauCeti.GLSymplectic.graphDiagonalFrame`, which
is the identity at `A = 1`.

## Proof

The determinant of the frame is `det ((A₁₂ - A₂₁) + i (A₁₁ + A₂₂))` by a Schur complement
(`Matrix.det_graphFrame`), and its phase is the Maslov phase of the graph
(`TauCeti.GLSymplectic.coe_graphPhase_eq_maslovPhase`). The realification of
`(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)` is `A J + J A`, which is invertible when `A` is symplectic
(`SymplecticGroup.isUnit_det_mul_J_add_J_mul`), so the frame is invertible. For a realified
unitary matrix `A = U_ℝ` the complex matrix is `2 i U`, so the graph phase is
`(-1)ⁿ (det U)² = (-1)ⁿ ρ(A)²`
(`TauCeti.GLSymplectic.coe_graphPhase_inclusion`). A general loop is deformed to its loop of
orthogonal polar factors through symplectic matrices, which changes no degree
(`TauCeti.GLSymplectic.degree_map_inclusion_polarUnitary`).

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford Graduate
  Texts in Mathematics 27, Oxford University Press, 2017, Section 2.3 (the Maslov index of loops
  of Lagrangian subspaces and of loops of symplectic matrices).
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (graphs of symplectic paths and the Conley–Zehnder index).
-/

public section

open Matrix Matrix.GeneralLinearGroup Complex
open scoped unitInterval ComplexConjugate

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The graph frame -/

/-- The **graph frame** of a real matrix `A` on `ℝ^{n ⊕ n}`: the complex matrix sending the real
point `x` of `ℂ^{n ⊕ n}` to `(conj (φ x), φ (A x))`, where `φ (x, y) = x + i y`. Its columns are the
images of the real basis vectors, so it frames the graph `Matrix.graphSubspace A`. -/
noncomputable def graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 (-(Complex.I • 1))
    (A.toBlocks₁₁.map (↑) + Complex.I • A.toBlocks₂₁.map (↑))
    (A.toBlocks₁₂.map (↑) + Complex.I • A.toBlocks₂₂.map (↑))

omit [Fintype n] in
/-- The graph frame in blocks: `fromBlocks 1 (-i) (A₁₁ + i A₂₁) (A₁₂ + i A₂₂)`. -/
theorem graphFrame_def (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    graphFrame A = fromBlocks 1 (-(Complex.I • 1))
      (A.toBlocks₁₁.map (↑) + Complex.I • A.toBlocks₂₁.map (↑))
      (A.toBlocks₁₂.map (↑) + Complex.I • A.toBlocks₂₂.map (↑)) :=
  (rfl)

omit [Fintype n] in
/-- The graph frame of the realification of a complex matrix `W` is `fromBlocks 1 (-i) W (i W)`. -/
theorem graphFrame_realify (W : Matrix n n ℂ) :
    graphFrame W.realify = fromBlocks 1 (-(Complex.I • 1)) W (Complex.I • W) := by
  rw [graphFrame_def]
  congr 1 <;> ext i j <;> apply Complex.ext <;>
    simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

/-- The graph frame sends the real point `x` to `(conj (φ x), φ (A x))`, where `φ (x, y) = x + i y`.
-/
theorem graphFrame_mulVec (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (x : n ⊕ n → ℝ) :
    graphFrame A *ᵥ (fun k => (x k : ℂ)) =
      Sum.elim (fun i => conj ((x (.inl i) : ℂ) + x (.inr i) * Complex.I))
        (fun i => ((A *ᵥ x) (.inl i) : ℂ) + (A *ᵥ x) (.inr i) * Complex.I) := by
  ext (i | i)
  · simp [graphFrame, fromBlocks_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      mul_comm]
  · simp only [mulVec, dotProduct, Fintype.sum_sum_type, graphFrame, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, toBlocks₁₁,
      toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, Sum.elim_inr, smul_eq_mul, ofReal_add,
      ofReal_sum, ofReal_mul]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring

/-- The complex `n × n` matrix `(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)`, whose determinant is that of the
graph frame and whose realification is `A J + J A`. -/
private noncomputable def graphCore (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) : Matrix n n ℂ :=
  (A.toBlocks₁₂ - A.toBlocks₂₁).map ((↑) : ℝ → ℂ) +
    Complex.I • (A.toBlocks₁₁ + A.toBlocks₂₂).map ((↑) : ℝ → ℂ)

/-- The determinant of the graph frame is that of `(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)`. -/
private theorem det_graphFrame_eq_det_graphCore (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphFrame A).det = (graphCore A).det := by
  rw [graphFrame, graphCore, det_fromBlocks_one₁₁]
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_apply, smul_eq_mul, ofReal_sub,
    ofReal_add]
  linear_combination (A.toBlocks₂₁ i j : ℂ) * I_sq

/-- The determinant of the graph frame is `det ((A₁₂ - A₂₁) + i (A₁₁ + A₂₂))`. -/
theorem det_graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphFrame A).det =
      ((A.toBlocks₁₂ - A.toBlocks₂₁).map ((↑) : ℝ → ℂ) +
    Complex.I • (A.toBlocks₁₁ + A.toBlocks₂₂).map ((↑) : ℝ → ℂ)).det :=
  det_graphFrame_eq_det_graphCore A

/-- The realification of `(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)` is `A J + J A`. -/
private theorem realify_graphCore (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphCore A).realify = A * J n ℝ + J n ℝ * A := by
  ext (i | i) (j | j) <;>
    simp [graphCore, J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, toBlocks₁₁,
      toBlocks₁₂, toBlocks₂₁, toBlocks₂₂] <;> ring

omit [Fintype n] [DecidableEq n] in
/-- On a realified complex matrix `U`, the matrix `(A₁₂ - A₂₁) + i (A₁₁ + A₂₂)` is `2 i U`. -/
private theorem graphCore_realify (U : Matrix n n ℂ) :
    graphCore U.realify = (2 * Complex.I) • U := by
  ext i j
  apply Complex.ext <;>
    simp [graphCore, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, realify_apply_inl_inl,
      realify_apply_inl_inr, realify_apply_inr_inl, realify_apply_inr_inr] <;> ring

/-- **The graph frame of a symplectic matrix is invertible.** -/
theorem isUnit_det_graphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hA : A ∈ symplecticGroup n ℝ) :
    IsUnit (graphFrame A).det := by
  have h := SymplecticGroup.isUnit_det_mul_J_add_J_mul hA
  rw [← realify_graphCore, det_realify] at h
  rw [det_graphFrame_eq_det_graphCore, isUnit_iff_ne_zero]
  intro h0
  apply (isUnit_iff_ne_zero.1 h)
  simp [h0]

omit [Fintype n] in
/-- The graph frame depends continuously on the matrix. -/
theorem continuous_graphFrame : Continuous (graphFrame : Matrix (n ⊕ n) (n ⊕ n) ℝ → _) := by
  refine Continuous.matrix_fromBlocks continuous_const continuous_const ?_ ?_ <;>
  refine continuous_matrix fun i j => ?_ <;>
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, toBlocks₁₁,
    toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply] <;>
  fun_prop

/-! ### The graph subspace -/

/-- The **graph** of a real matrix `A` on `ℝ^{n ⊕ n}`, as a real subspace of
`ℂ^{n ⊕ n} = ℂⁿ × ℂⁿ`: the image `Matrix.realImage` of the real points under the graph frame, that
is, the set of `(conj (φ x), φ (A x))` (`Matrix.mem_graphSubspace_iff`). -/
noncomputable def graphSubspace (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Submodule ℝ (EuclideanSpace ℂ (n ⊕ n)) :=
  (graphFrame A).realImage

/-- The graph of `A` is the image of the real points under the graph frame. -/
@[simp]
theorem realImage_graphFrame (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphFrame A).realImage = graphSubspace A :=
  (rfl)

/-- A vector of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}` lies on the graph of `A` exactly when it is
`(conj (φ x), φ (A x))` for a real vector `x`, where `φ (x, y) = x + i y`. -/
theorem mem_graphSubspace_iff {A : Matrix (n ⊕ n) (n ⊕ n) ℝ} {w : EuclideanSpace ℂ (n ⊕ n)} :
    w ∈ graphSubspace A ↔ ∃ x : n ⊕ n → ℝ,
      WithLp.toLp 2 (Sum.elim (fun i => conj ((x (.inl i) : ℂ) + x (.inr i) * Complex.I))
        (fun i => ((A *ᵥ x) (.inl i) : ℂ) + (A *ᵥ x) (.inr i) * Complex.I)) = w := by
  rw [graphSubspace, mem_realImage]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : WithLp.ofLp v = fun k => ((v k).re : ℂ) :=
      funext fun k => Complex.ext rfl (by simp [mem_realSubspace.1 hv k])
    refine ⟨fun k => (v k).re, ?_⟩
    refine (congrArg (WithLp.toLp 2) (graphFrame_mulVec A fun k => (v k).re).symm).trans ?_
    rw [toEuclideanCLM_apply, toLpLin_apply, ← hv']
  · rintro ⟨x, rfl⟩
    refine ⟨WithLp.toLp 2 fun k => (x k : ℂ), mem_realSubspace.2 fun _ => by simp, ?_⟩
    rw [toEuclideanCLM_apply]
    exact congrArg (WithLp.toLp 2) (graphFrame_mulVec A x)

/-- The graph of a symplectic matrix is maximal totally real. -/
theorem isMaximalTotallyReal_graphSubspace {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (EuclideanSpace ℂ (n ⊕ n)) Complex.I).restrictScalars ℝ)
      (graphSubspace A) :=
  isMaximalTotallyReal_realImage (isUnit_det_graphFrame hA).ne_zero

/-- **The Gram matrix of the graph frame.** For a symplectic matrix `A`, the columns of the graph
frame have the real Gram matrix `1 + Aᵀ A`: the imaginary part of the Hermitian Gram matrix is
`ω(A x, A y) - ω(x, y) = 0`. -/
theorem conjTranspose_graphFrame_mul_graphFrame {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) :
    (graphFrame A)ᴴ * graphFrame A = (1 + Aᵀ * A).map ((↑) : ℝ → ℂ) := by
  -- Work with the ring homomorphism `Complex.ofRealHom.mapMatrix` of entrywise coercion.
  have hc : (⇑Complex.ofRealHom : ℝ → ℂ) = (↑) := funext Complex.ofRealHom_eq_coe
  -- The graph frame is `E₁ + E₂ A`, for the blocks `E₁ = (1, -i; 0, 0)` and `E₂ = (0, 0; 1, i)`.
  have hF : graphFrame A = fromBlocks 1 (-(Complex.I • 1)) 0 0 +
      fromBlocks 0 0 1 (Complex.I • 1) * Complex.ofRealHom.mapMatrix A := by
    rw [RingHom.mapMatrix_apply, hc, ← fromBlocks_toBlocks A, fromBlocks_map, fromBlocks_multiply,
      fromBlocks_add, graphFrame_def, fromBlocks_toBlocks]
    simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.smul_mul, zero_add, add_zero]
  set E₁ : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 1 (-(Complex.I • 1)) 0 0
  set E₂ : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks 0 0 1 (Complex.I • 1)
  have h12 : E₁ᴴ * E₂ = 0 := by
    simp [E₁, E₂, fromBlocks_conjTranspose, fromBlocks_multiply]
  have h21 : E₂ᴴ * E₁ = 0 := by
    simp [E₁, E₂, fromBlocks_conjTranspose, fromBlocks_multiply]
  have h11 : E₁ᴴ * E₁ = 1 + Complex.I • J n ℂ := by
    simp [E₁, J, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one,
      fromBlocks_add, smul_smul]
  have h22 : E₂ᴴ * E₂ = 1 - Complex.I • J n ℂ := by
    simp [E₂, J, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one,
      sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, smul_smul]
  -- `A` is real and symplectic: `Aᴴ = Aᵀ` and `Aᵀ J A = J`.
  have hA' : (Complex.ofRealHom.mapMatrix A)ᴴ = Complex.ofRealHom.mapMatrix Aᵀ := by
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hc,
      ← conjTranspose_map _ fun _ => (Complex.conj_ofReal _).symm,
      conjTranspose_eq_transpose_of_trivial]
  have hJ : Complex.ofRealHom.mapMatrix Aᵀ * J n ℂ * Complex.ofRealHom.mapMatrix A = J n ℂ := by
    have hJ' : Complex.ofRealHom.mapMatrix (J n ℝ) = J n ℂ := by
      unfold J
      rw [RingHom.mapMatrix_apply, fromBlocks_map, Matrix.map_zero _ (map_zero _),
        Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hJ', ← map_mul, ← map_mul, SymplecticGroup.mem_iff'.1 hA]
  -- So `(E₁ + E₂ A)ᴴ (E₁ + E₂ A) = (1 + i J) + Aᵀ (1 - i J) A = 1 + Aᵀ A`.
  rw [← hc, ← RingHom.mapMatrix_apply, map_add, map_one, map_mul, hF, conjTranspose_add,
    conjTranspose_mul, hA', Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h11,
    ← Matrix.mul_assoc E₁ᴴ, h12, Matrix.mul_assoc, h21, Matrix.mul_assoc, ← Matrix.mul_assoc E₂ᴴ,
    h22, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hJ,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one]
  abel

end Matrix

namespace TauCeti.GLSymplectic

open Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of the graph frame of a symplectic matrix does not vanish. -/
theorem det_graphFrame_ne_zero (A : GLSymplectic n ℝ) :
    (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0 :=
  (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.2)).ne_zero

/-- The graph frame of a symplectic matrix, as a complex-linear automorphism of `ℂ^{n ⊕ n}`. -/
noncomputable def graphFrameEquiv (A : GLSymplectic n ℝ) :
    EuclideanSpace ℂ (n ⊕ n) ≃L[ℂ] EuclideanSpace ℂ (n ⊕ n) :=
  (graphFrame (A : GL (n ⊕ n) ℝ)).toEuclideanCLE (det_graphFrame_ne_zero A)

/-- The graph frame automorphism acts as its matrix. -/
@[simp]
theorem graphFrameEquiv_apply (A : GLSymplectic n ℝ) (v : EuclideanSpace ℂ (n ⊕ n)) :
    graphFrameEquiv A v = WithLp.toLp 2 (graphFrame (A : GL (n ⊕ n) ℝ) *ᵥ WithLp.ofLp v) := by
  rw [graphFrameEquiv, toEuclideanCLE_apply, toLpLin_apply]

/-- The graph of a symplectic matrix is the image of the real points under its graph frame
automorphism. -/
theorem graphSubspace_eq_map (A : GLSymplectic n ℝ) :
    graphSubspace (A : GL (n ⊕ n) ℝ) =
      (realSubspace (n ⊕ n)).map
        (((graphFrameEquiv A).toLinearEquiv :
          EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ) :=
  realImage_eq_map_toEuclideanCLE (det_graphFrame_ne_zero A)

/-- The graph frame automorphism depends continuously on the symplectic matrix. -/
theorem continuous_graphFrameEquiv :
    Continuous fun A : GLSymplectic n ℝ =>
      (graphFrameEquiv A : EuclideanSpace ℂ (n ⊕ n) →L[ℂ] EuclideanSpace ℂ (n ⊕ n)) := by
  simp only [graphFrameEquiv, coe_toEuclideanCLE]
  exact continuous_toEuclideanCLM.comp
    (continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtype_val))

/-! ### The graph phase -/

/-- The **graph phase** of a symplectic matrix `A`: the determinant phase `det F / conj (det F)` of
its graph frame `F`, which is the Maslov phase of the graph of `A` relative to the real points. -/
noncomputable def graphPhase (A : GLSymplectic n ℝ) : Circle :=
  Circle.ofConjDivSelf (conj (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det)
    ((map_ne_zero _).2 (det_graphFrame_ne_zero A))

/-- The graph phase is `det F / conj (det F)` for the graph frame `F`. -/
theorem coe_graphPhase (A : GLSymplectic n ℝ) :
    (graphPhase A : ℂ) =
      (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det /
        conj (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det := by
  simp [graphPhase]

/-- **The graph phase is the Maslov phase of the graph** relative to the real points of
`ℂ^{n ⊕ n}`. -/
theorem coe_graphPhase_eq_maslovPhase (A : GLSymplectic n ℝ) :
    (graphPhase A : ℂ) = isMaximalTotallyReal_realSubspace.maslovPhase
      (isMaximalTotallyReal_graphSubspace (mem_iff_mem_symplecticGroup.1 A.2)) := by
  -- `graphSubspace A` is the image of the real points under the graph frame
  -- (`graphSubspace_eq_map`), so the two maximal-totally-real proofs concern the same subspace.
  rw [IsMaximalTotallyReal.maslovPhase_congr _ _
      (isMaximalTotallyReal_realSubspace.map_linearEquiv (graphFrameEquiv A).toLinearEquiv)
      (graphSubspace_eq_map A),
    isMaximalTotallyReal_realSubspace.maslovPhase_map, coe_graphPhase]
  simp [graphFrameEquiv]

/-- The graph phase depends continuously on the symplectic matrix. -/
theorem continuous_graphPhase : Continuous (graphPhase : GLSymplectic n ℝ → Circle) := by
  have hd : Continuous fun A : GLSymplectic n ℝ =>
      (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det :=
    (continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtype_val)).matrix_det
  refine Continuous.subtype_mk ?_ _
  refine (hd.div (continuous_conj.comp hd) fun A => ?_).congr fun A => (coe_graphPhase A).symm
  exact (map_ne_zero _).2 (det_graphFrame_ne_zero A)

/-- On an orthogonal symplectic matrix, the realification of a unitary matrix `U`, the graph phase
is `(-1)ⁿ (det U)² = (-1)ⁿ ρ²`: the graph frame has determinant `det (2 i U) = (2 i)ⁿ det U`. -/
theorem coe_graphPhase_inclusion (U : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    (graphPhase (Subgroup.inclusion inf_le_left U) : ℂ) =
      (-1) ^ Fintype.card n * (maslovPhase (Subgroup.inclusion inf_le_left U) : ℂ) ^ 2 := by
  set V := unitaryGroupEquivSymplecticInfOrthogonal.symm U
  have hV : (((Subgroup.inclusion inf_le_left U : GLSymplectic n ℝ) : GL (n ⊕ n) ℝ) :
      Matrix (n ⊕ n) (n ⊕ n) ℝ) = (V : Matrix n n ℂ).realify := by
    rw [Subgroup.coe_inclusion,
      ← realify_toUnits_unitaryGroupEquivSymplecticInfOrthogonal_symm_apply,
      GeneralLinearGroup.coe_realify, Unitary.val_toUnits_apply]
  have hdet : (graphFrame (((Subgroup.inclusion inf_le_left U : GLSymplectic n ℝ) :
      GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det =
      (2 * Complex.I) ^ Fintype.card n * (V : Matrix n n ℂ).det := by
    rw [det_graphFrame_eq_det_graphCore, hV, graphCore_realify, det_smul]
  have hρ : (maslovPhase (Subgroup.inclusion inf_le_left U) : ℂ) = (V : Matrix n n ℂ).det := by
    rw [maslovPhase_inclusion, coe_detCircle]
  have hconj : conj (V : Matrix n n ℂ).det = ((V : Matrix n n ℂ).det)⁻¹ := by
    rw [← coe_detCircle, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  have hne : (V : Matrix n n ℂ).det ≠ 0 := by
    rw [← coe_detCircle]
    exact Circle.coe_ne_zero _
  have h2I : (2 * Complex.I) ^ Fintype.card n ≠ 0 := pow_ne_zero _ (by simp)
  have hs : (-1 : ℂ) ^ Fintype.card n * (-1) ^ Fintype.card n = 1 := by
    rw [← mul_pow]
    norm_num
  -- The scalar identity `c d / (s c d⁻¹) = s d²` for a sign `s` with `s² = 1`.
  have key (s c d : ℂ) (hs : s * s = 1) (hd : d ≠ 0) (hc : c ≠ 0) :
      c * d / (s * c * d⁻¹) = s * d ^ 2 := by
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one hs) hc) (inv_ne_zero hd))]
    linear_combination (-(c * d)) * mul_inv_cancel₀ hd - c * d * d * d⁻¹ * hs
  rw [coe_graphPhase, hdet, hρ, map_mul, map_pow, hconj, map_mul, map_ofNat, conj_I,
    show 2 * -Complex.I = (-1) * (2 * Complex.I) by ring, mul_pow (-1 : ℂ)]
  exact key _ _ _ hs hne h2I

/-! ### The Maslov index of the graph loop -/

/-- The **graph loop** of a loop `γ` of symplectic matrices: the loop `t ↦ Γ(γ t)` of graphs, as a
loop of maximal totally real subspaces of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`, framed by the graph frames. -/
noncomputable def graphLoop {A : GLSymplectic n ℝ} (γ : Path A A) :
    TotallyRealLoop (EuclideanSpace ℂ (n ⊕ n)) where
  toFun t := graphSubspace (γ t : GL (n ⊕ n) ℝ)
  exists_frame := ⟨_, isMaximalTotallyReal_realSubspace, fun t => graphFrameEquiv (γ t),
    continuous_graphFrameEquiv.comp γ.continuous, fun t => graphSubspace_eq_map (γ t)⟩
  toFun_zero_eq_toFun_one := by simp

/-- The graph loop at time `t` is the graph of `γ t`. -/
@[simp]
theorem graphLoop_apply {A : GLSymplectic n ℝ} (γ : Path A A) (t : I) :
    graphLoop γ t = graphSubspace (γ t : GL (n ⊕ n) ℝ) :=
  (rfl)

/-- **The Maslov index of the graph loop is twice the Maslov index of the loop.** For a loop `γ`
of symplectic matrices, the loop of graphs `t ↦ Γ(γ t)` in `ℂⁿ × ℂⁿ` has native Maslov index
`2 μ(γ)`. -/
theorem maslovIndex_graphLoop {A : GLSymplectic n ℝ} (γ : Path A A) :
    (graphLoop γ).maslovIndex = 2 * maslovIndex γ := by
  have hL₀ := isMaximalTotallyReal_realSubspace (n := n ⊕ n)
  -- The Maslov phase of the graph relative to the real points is the graph phase.
  have hphase (t : I) : ((γ.map continuous_graphPhase) t : ℂ) =
      hL₀.maslovPhase ((graphLoop γ).isMaximalTotallyReal t) :=
    coe_graphPhase_eq_maslovPhase (γ t)
  -- On the orthogonal polar factors the graph phase is `(-1)ⁿ ρ²`.
  let c : Circle := ⟨(-1) ^ Fintype.card n, mem_sphere_zero_iff_norm.2 (by simp)⟩
  have hunit : Circle.degree ((γ.map continuous_inclusion_polarUnitary).map continuous_graphPhase) =
      Circle.degree ((Path.refl c).mul ((γ.map continuous_maslovPhase).map (continuous_pow 2))) :=
    Circle.degree_congr _ _ fun t => by
      rw [Path.mul_apply, Path.refl_apply]
      refine Circle.ext ?_
      simp only [Path.map_coe, Function.comp_apply, Circle.coe_mul]
      rw [coe_graphPhase_inclusion, maslovPhase_inclusion_polarUnitary]
      simp [c]
  rw [(graphLoop γ).maslovIndex_eq_degree hL₀ _ hphase, ← degree_map_inclusion_polarUnitary,
    hunit, Circle.degree_mul, Circle.degree_refl, Circle.degree_map_pow, maslovIndex_def]
  push_cast
  ring

section UnitaryFrame

open scoped MatrixOrder Matrix.Norms.L2Operator NNReal

/-! ### The unitary frame of a graph -/

/-- The graph frame of a symplectic matrix, as an invertible complex matrix. -/
noncomputable def graphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  ((isUnit_iff_isUnit_det _).2 (isUnit_det_graphFrame (mem_iff_mem_symplecticGroup.1 A.2))).unit

/-- The invertible graph frame of `A` is the graph frame of `A`. -/
@[simp]
theorem coe_graphFrameUnit (A : GLSymplectic n ℝ) :
    (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) = graphFrame (A : GL (n ⊕ n) ℝ) :=
  IsUnit.unit_spec _

/-- The invertible graph frame depends continuously on the symplectic matrix. -/
theorem continuous_graphFrameUnit :
    Continuous (graphFrameUnit : GLSymplectic n ℝ → GL (n ⊕ n) ℂ) :=
  Units.isOpenEmbedding_val.continuous_iff.2 <| by
    simpa only [Function.comp_def, coe_graphFrameUnit] using
      continuous_graphFrame.comp (Units.continuous_val.comp continuous_subtype_val)

/-- The real orthonormalization of the graph frame of a symplectic matrix is unitary, since the
Gram matrix `1 + Aᵀ A` of the graph frame is real. -/
private theorem realOrthonormalize_graphFrameUnit_mem (A : GLSymplectic n ℝ) :
    (realOrthonormalize (graphFrameUnit A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) ∈
      unitaryGroup (n ⊕ n) ℂ :=
  realOrthonormalize_mem_unitaryGroup <| by
    rw [coe_graphFrameUnit]
    exact conjTranspose_graphFrame_mul_graphFrame (mem_iff_mem_symplecticGroup.1 A.2)

/-- The **unitary frame of the graph** of a symplectic matrix `A`: the real orthonormalization
`F Re (Fᴴ F) ^ (-1/2)` (`Matrix.GeneralLinearGroup.realOrthonormalize`) of the graph frame `F`.
Since `Fᴴ F = 1 + Aᵀ A` is real, it is the unitary matrix `F (1 + Aᵀ A) ^ (-1/2)`
(`TauCeti.GLSymplectic.coe_graphUnitary`). It frames the graph of `A`
(`TauCeti.GLSymplectic.realImage_graphUnitary`). -/
noncomputable def graphUnitary (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  ⟨realOrthonormalize (graphFrameUnit A), realOrthonormalize_graphFrameUnit_mem A⟩

/-- The unitary frame of the graph of `A` is the real orthonormalization of the graph frame. -/
theorem coe_graphUnitary_eq_realOrthonormalize (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) = realOrthonormalize (graphFrameUnit A) :=
  (rfl)

/-- The unitary frame of the graph of `A` is `F (1 + Aᵀ A) ^ (-1/2)`, for the graph frame `F`:
the real Gram matrix of `F` is `1 + Aᵀ A`. -/
theorem coe_graphUnitary (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      graphFrame (A : GL (n ⊕ n) ℝ) *
        ((1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ)) ^
          (-(1 / 2) : ℝ)).map ((↑) : ℝ → ℂ) := by
  have hre : (Complex.re ∘ ((↑) : ℝ → ℂ)) = id := funext Complex.ofReal_re
  rw [coe_graphUnitary_eq_realOrthonormalize, coe_realOrthonormalize, coe_graphFrameUnit,
    conjTranspose_graphFrame_mul_graphFrame (mem_iff_mem_symplecticGroup.1 A.2), Matrix.map_map,
    hre, Matrix.map_id]

/-- The unitary frame of the graph of `A` frames the graph of `A`. -/
@[simp]
theorem realImage_graphUnitary (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage = graphSubspace (A : GL (n ⊕ n) ℝ) := by
  rw [coe_graphUnitary_eq_realOrthonormalize, realImage_realOrthonormalize, coe_graphFrameUnit,
    realImage_graphFrame]

/-- The unitary frame of the graph depends continuously on the symplectic matrix. -/
theorem continuous_graphUnitary :
    Continuous (graphUnitary : GLSymplectic n ℝ → unitaryGroup (n ⊕ n) ℂ) :=
  (Units.continuous_val.comp (continuous_realOrthonormalize continuous_graphFrameUnit)).subtype_mk _

/-- For an orthogonal symplectic matrix `A`, `1 + Aᵀ A = 2`, so the unitary frame of the graph is
the graph frame divided by `√2`. -/
theorem coe_graphUnitary_of_transpose_mul_self {A : GLSymplectic n ℝ}
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ) = 1) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      ((Real.sqrt 2)⁻¹ : ℂ) • graphFrame (A : GL (n ⊕ n) ℝ) := by
  have h2 : (1 + 1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = algebraMap ℝ≥0 _ 2 := by
    rw [Algebra.algebraMap_eq_smul_one, two_smul]
  rw [coe_graphUnitary, hA, h2, CFC.rpow_algebraMap, Algebra.algebraMap_eq_smul_one,
    NNReal.smul_def, NNReal.coe_rpow, NNReal.coe_ofNat, Real.rpow_neg (by norm_num),
    ← Real.sqrt_eq_rpow]
  have hmap : ((√2)⁻¹ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) =
      ((√2)⁻¹ : ℂ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hmap, Matrix.mul_smul, Matrix.mul_one]

/-- The square of the determinant of the unitary frame of the graph is the graph phase
`det F / conj (det F)` of the graph frame `F`. -/
theorem detCircle_graphUnitary_sq (A : GLSymplectic n ℝ) :
    detCircle (graphUnitary A) ^ 2 = graphPhase A := by
  set F := graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  set r := (((1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ)) ^
    (-(1 / 2) : ℝ)).det)
  have hdet : (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det = F.det * r := by
    rw [coe_graphUnitary, det_mul]
    exact congrArg _ (RingHom.map_det Complex.ofRealHom _).symm
  -- The determinant `w = det F * r` of a unitary matrix satisfies `conj w * w = 1`.
  have hw : star (F.det * r) * (F.det * r) = 1 := by
    rw [← hdet, ← det_conjTranspose, ← det_mul, ← star_eq_conjTranspose,
      Matrix.UnitaryGroup.star_mul_self, det_one]
  have hF : F.det ≠ 0 := det_graphFrame_ne_zero A
  refine Circle.ext ?_
  rw [Circle.coe_pow, coe_detCircle, coe_graphPhase, hdet, eq_div_iff ((map_ne_zero _).2 hF)]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal] at hw
  linear_combination F.det * hw

/-! ### The graph relative to the diagonal -/

/-- The unitary frame of the graph of `A`, moved by the inverse of the unitary frame of the diagonal
`Γ(1)`. It frames the image of the graph of `A` under a fixed unitary map which carries the
diagonal to the real points (`TauCeti.GLSymplectic.realImage_graphDiagonalFrame`,
`TauCeti.GLSymplectic.graphDiagonalFrame_one`). -/
noncomputable def graphDiagonalFrame (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  star (graphUnitary 1) * graphUnitary A

/-- The frame of the graph relative to the diagonal is `U(1)⋆ U(A)`, for the unitary frames `U` of
the graphs. -/
theorem graphDiagonalFrame_def (A : GLSymplectic n ℝ) :
    graphDiagonalFrame A = star (graphUnitary 1) * graphUnitary A :=
  (rfl)

/-- The frame of the diagonal relative to itself is the identity: the diagonal is moved to the real
points. -/
@[simp]
theorem graphDiagonalFrame_one : graphDiagonalFrame (1 : GLSymplectic n ℝ) = 1 :=
  Subtype.ext (Matrix.UnitaryGroup.star_mul_self (graphUnitary 1))

/-- The frame `graphDiagonalFrame A` frames the image of the graph of `A` under the inverse of the
unitary frame of the diagonal. -/
theorem realImage_graphDiagonalFrame (A : GLSymplectic n ℝ) :
    (graphDiagonalFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).realImage =
      (graphSubspace (A : GL (n ⊕ n) ℝ)).map
        (((toEuclideanCLM (𝕜 := ℂ)
          (star (graphUnitary (1 : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
            EuclideanSpace ℂ (n ⊕ n) →L[ℂ] EuclideanSpace ℂ (n ⊕ n)) :
              EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ) := by
  rw [graphDiagonalFrame_def, Submonoid.coe_mul, Unitary.coe_star, realImage_mul,
    realImage_graphUnitary]

/-- The frame of the graph relative to the diagonal depends continuously on the matrix. -/
theorem continuous_graphDiagonalFrame :
    Continuous (graphDiagonalFrame : GLSymplectic n ℝ → unitaryGroup (n ⊕ n) ℂ) :=
  continuous_const.mul continuous_graphUnitary

/-- For an orthogonal symplectic matrix `A`, the frame of the graph relative to the diagonal is
`F(1)ᴴ F(A) / 2`, for the graph frames `F`. -/
theorem coe_graphDiagonalFrame_of_transpose_mul_self {A : GLSymplectic n ℝ}
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ) = 1) :
    (graphDiagonalFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (1 / 2 : ℂ) •
        ((graphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ * graphFrame (A : GL (n ⊕ n) ℝ)) := by
  have h1 := coe_graphUnitary_of_transpose_mul_self (A := (1 : GLSymplectic n ℝ)) (by simp)
  rw [graphDiagonalFrame_def, Submonoid.coe_mul, Unitary.coe_star, h1,
    coe_graphUnitary_of_transpose_mul_self hA, star_eq_conjTranspose, conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

end UnitaryFrame

end TauCeti.GLSymplectic
