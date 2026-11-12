/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Localization
import TauCeti.Topology.Instances.Matrix

/-!
# The Conley–Zehnder index of a path of symplectic matrices

The graph `Γ(A)` of a symplectic matrix `A` is a Lagrangian subspace of `ℂ^{n ⊕ n} = ℂⁿ × ℂⁿ`,
the model of `ℝ^{n ⊕ n} × ℝ^{n ⊕ n}` with the symplectic form `(-ω) ⊕ ω` of
`TauCeti/Analysis/Matrix/SymplecticGroup/Graph.lean`. Its graph frame `F` has the real Gram matrix
`Fᴴ F = 1 + Aᵀ A`, so the unitary polar factor `U = F (Fᴴ F)^{-1/2}` of `F` is a unitary frame of
the same Lagrangian (`TauCeti.GLSymplectic.graphUnitary`). The diagonal `Δ = Γ(1)` is framed by
`V = U(1)`, and `V⁻¹` is a unitary, hence symplectic, automorphism taking `Δ` to the real points.

The **graph Maslov index** `μ(Γ ∘ γ, Δ)` of a path `γ` of symplectic matrices
(`TauCeti.GLSymplectic.graphMaslovIndex`) is the Robbin–Salamon index of the path of graphs
`Γ(γ t)` relative to the diagonal, computed as the index `Matrix.UnitaryGroup.maslovIndex` of the
path of frames `V⁻¹ U(γ t)` relative to the real points. It is invariant under homotopies with
fixed endpoints, additive under catenation, and, on a loop, twice the Maslov index of the loop of
symplectic matrices (`TauCeti.GLSymplectic.graphMaslovIndex_eq_two_mul_maslovIndex`).

The **Conley–Zehnder index** of a path `γ` of symplectic matrices starting at the identity is
`CZ(γ) = -μ(Γ ∘ γ, Δ)` (`TauCeti.GLSymplectic.conleyZehnderIndex`). It is real-valued here; the
endpoint at the identity, where `Γ(1) = Δ`, contributes half of a crossing. It is invariant under
homotopies with fixed endpoints, and running a loop `φ` first changes it by `-2 μ(φ)`, the loop
law (`TauCeti.GLSymplectic.conleyZehnderIndex_trans_of_loop`). The sign is the one for which a
small positive rotation of `ℝ²` has index `-1`.

## The Cayley transform

When `1 + A` is invertible, the graph of `A` meets the anti-diagonal `Γ(-1)` trivially, and
`V⁻¹ Γ(A)` is the graph `{x + i B x}` of the real symmetric matrix `B = J (1 - A) (1 + A)⁻¹`
(`TauCeti.GLSymplectic.souriau_star_graphUnitary_one_mul_eq_cayley`). By the localization axiom
of Robbin and Salamon, along a path of symplectic matrices that never has `-1` as an eigenvalue,
the graph Maslov index is half the change of the signature of `B`
(`TauCeti.GLSymplectic.graphMaslovIndex_eq_signature_sub`). Since `B = 0` at the identity, the
Conley–Zehnder index of such a path from the identity to `A` is `-sign (J (1 - A) (1 + A)⁻¹) / 2`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature`). For the simultaneous rotation by an
angle `θ ∈ (-π, π)` in every coordinate plane, `B = tan (θ / 2) • 1`, which gives the
normalization `CZ = -sign (θ) · n`
(`TauCeti.GLSymplectic.conleyZehnderIndex_scalarRotationPath`).

## Main definitions

* `TauCeti.GLSymplectic.graphUnitary`: the unitary frame of the graph of a symplectic matrix.
* `TauCeti.GLSymplectic.graphMaslovIndex`: the Robbin–Salamon index of a path of graphs relative
  to the diagonal.
* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a path from the
  identity.
* `TauCeti.GLSymplectic.scalarRotation`, `TauCeti.GLSymplectic.scalarRotationPath`: the rotation
  `e^{i θ}` in every coordinate plane, and the path `t ↦ e^{i θ t}` of rotations.

## Main results

* `TauCeti.GLSymplectic.coe_graphUnitary_mul_sqrt`: `U(A) √(1 + Aᵀ A) = F(A)`.
* `TauCeti.GLSymplectic.graphMaslovIndex_eq_two_mul_maslovIndex`: on loops, the graph Maslov index
  is twice the Maslov index.
* `TauCeti.GLSymplectic.conleyZehnderIndex_trans_of_loop`: catenating a loop `φ` in front changes
  the Conley–Zehnder index by `-2 μ(φ)`.
* `TauCeti.GLSymplectic.graphMaslovIndex_eq_signature_sub`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature`: the indices of a path avoiding the
  eigenvalue `-1`, through the Cayley transform.
* `TauCeti.GLSymplectic.conleyZehnderIndex_scalarRotationPath`: the normalization on rotations.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index as the Maslov index of the graph relative to the diagonal)
  and Theorem 2.3 (the axioms of the index for paths).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Mathematics Series 7, American Mathematical Society, 1999, Section 2.4 (the Conley–Zehnder
  index and its normalization).
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup Matrix.UnitaryGroup Complex
open scoped MatrixOrder ComplexOrder ComplexConjugate unitInterval

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The unitary graph frame -/

/-- The graph frame of a symplectic matrix, as an invertible complex matrix. -/
private def graphFrameUnit (A : GLSymplectic n ℝ) : GL (n ⊕ n) ℂ :=
  mkOfDetNeZero (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
    (det_graphFrame_ne_zero A)

private theorem coe_graphFrameUnit (A : GLSymplectic n ℝ) :
    (graphFrameUnit A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  (rfl)

/-- The underlying matrix of a symplectic matrix depends continuously on it. -/
private theorem continuous_coe :
    Continuous fun A : GLSymplectic n ℝ ↦ ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) :=
  Units.continuous_val.comp continuous_subtype_val

private theorem continuous_graphFrameUnit : Continuous (graphFrameUnit (n := n)) := by
  have hF := continuous_graphFrame.comp (continuous_coe (n := n))
  refine Units.continuous_iff.2 ⟨hF, continuous_iff_continuousAt.2 fun A ↦ ?_⟩
  simp only [coe_units_inv, coe_graphFrameUnit]
  exact hF.continuousAt.matrix_inv (det_graphFrame_ne_zero A)

/-- The transpose of a symplectic matrix `A` satisfies `Aᵀ J A = J`. -/
private theorem transpose_mul_J_mul (A : GLSymplectic n ℝ) :
    ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * J n ℝ *
      ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = J n ℝ :=
  SymplecticGroup.mem_iff'.1 (mem_iff_mem_symplecticGroup.1 A.2)

/-- **The Gram matrix of the graph frame** of a symplectic matrix `A` is the real matrix
`1 + Aᵀ A`. -/
theorem conjTranspose_graphFrame_mul_graphFrame_self (A : GLSymplectic n ℝ) :
    (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ *
        graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
        ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) := by
  rw [conjTranspose_graphFrame_mul_graphFrame, transpose_mul_J_mul, sub_self,
    Matrix.map_zero _ (by simp), smul_zero, add_zero]

/-- The real Gram matrix `1 + Aᵀ A` is positive definite. -/
private theorem posDef_one_add_transpose_mul (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (1 + Aᵀ * A).PosDef := by
  have h := posSemidef_conjTranspose_mul_self A
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact PosDef.one.add_posSemidef h

/-- The **unitary graph frame** of a symplectic matrix `A`: the unitary polar factor
`F (Fᴴ F)^{-1/2}` of its graph frame `F`. Since `Fᴴ F = 1 + Aᵀ A` is real, it is `F` times a real
matrix (`TauCeti.GLSymplectic.coe_graphUnitary`), so its columns are an orthonormal basis of the
graph `Γ(A)` and `U ℝ^{n ⊕ n} = Γ(A)`. -/
def graphUnitary (A : GLSymplectic n ℝ) : unitaryGroup (n ⊕ n) ℂ :=
  Units.polarUnitary (graphFrameUnit A)

/-- **The polar decomposition of the graph frame.** The graph frame of a symplectic matrix `A` is
its unitary graph frame times the real positive definite matrix `√(1 + Aᵀ A)`. -/
theorem coe_graphUnitary_mul_sqrt (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) *
        (CFC.sqrt (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
          ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))).map (↑) =
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  set M := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hs : CFC.sqrt ((1 + Mᵀ * M).map ((↑) : ℝ → ℂ)) = (CFC.sqrt (1 + Mᵀ * M)).map (↑) :=
    sqrt_map_ofReal (posDef_one_add_transpose_mul M).posSemidef.nonneg
  have h := Units.polarUnitary_mul_sqrt_star_mul (graphFrameUnit A)
  rwa [coe_graphFrameUnit, star_eq_conjTranspose, conjTranspose_graphFrame_mul_graphFrame_self,
    hs] at h

/-- **The unitary graph frame is the graph frame times a real matrix**:
`U(A) = F(A) (√(1 + Aᵀ A))⁻¹`. -/
theorem coe_graphUnitary (A : GLSymplectic n ℝ) :
    (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) *
        ((CFC.sqrt (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
          ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)))⁻¹).map (↑) := by
  set M := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hmul (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
      (X * Y).map ((↑) : ℝ → ℂ) = X.map (↑) * Y.map (↑) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [← coe_graphUnitary_mul_sqrt, Matrix.mul_assoc, ← hmul,
    mul_nonsing_inv _ (posDef_one_add_transpose_mul M).isUnit_det_sqrt,
    Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]

/-- The unitary graph frame depends continuously on the symplectic matrix. -/
theorem continuous_graphUnitary : Continuous (graphUnitary (n := n)) := by
  -- The unitary polar factor is the end of the polar deformation, which is continuous.
  have h := (Matrix.GeneralLinearGroup.polarHomotopy (n ⊕ n) ℂ).continuous.comp
    (continuous_const.prodMk continuous_id : Continuous fun A : GL (n ⊕ n) ℂ ↦ ((1 : I), A))
  simp only [Function.comp_def, polarHomotopy_apply, Set.Icc.coe_one, polarDeformation_one] at h
  exact ((Units.continuous_val.comp h).comp continuous_graphFrameUnit).subtype_mk _

/-! ### The graph Maslov index -/

/-- The frames `V⁻¹ U(A)`, with `V = U(1)` the unitary frame of the diagonal, depend continuously
on `A`. -/
private theorem continuous_star_graphUnitary_one_mul :
    Continuous fun A : GLSymplectic n ℝ ↦ star (graphUnitary (1 : GLSymplectic n ℝ)) *
      graphUnitary A :=
  continuous_const.mul continuous_graphUnitary

/-- The **graph Maslov index** `μ(Γ ∘ γ, Δ)` of a path `γ` of symplectic matrices: the
Robbin–Salamon index of the path of graphs `Γ(γ t)` relative to the diagonal `Δ = Γ(1)`. It is
the index `Matrix.UnitaryGroup.maslovIndex`, relative to the real points, of the path of unitary
frames `V⁻¹ U(γ t)`, where `U` is the unitary graph frame and `V = U(1)` frames the diagonal:
`V⁻¹ = Vᴴ` is a unitary, hence symplectic, map taking the diagonal to the real points. -/
def graphMaslovIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  UnitaryGroup.maslovIndex (γ.map continuous_star_graphUnitary_one_mul)

/-- The graph Maslov index is the index of the path of frames `V⁻¹ U(γ t)`. -/
theorem graphMaslovIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    graphMaslovIndex γ = UnitaryGroup.maslovIndex (γ.map (continuous_const.mul
      continuous_graphUnitary : Continuous fun A : GLSymplectic n ℝ ↦
        star (graphUnitary 1) * graphUnitary A)) :=
  (rfl)

/-- **Homotopy invariance.** Paths of symplectic matrices that are homotopic relative to their
endpoints have the same graph Maslov index. -/
theorem graphMaslovIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : graphMaslovIndex γ₀ = graphMaslovIndex γ₁ :=
  UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_star_graphUnitary_one_mul⟩)

/-- The constant path has graph Maslov index zero. -/
@[simp]
theorem graphMaslovIndex_refl (A : GLSymplectic n ℝ) : graphMaslovIndex (Path.refl A) = 0 := by
  rw [graphMaslovIndex, UnitaryGroup.maslovIndex_eq_of_souriau_eq _
    (Path.refl (star (graphUnitary 1) * graphUnitary A)) fun _ ↦ by simp,
    UnitaryGroup.maslovIndex_refl]

/-- **Catenation.** The graph Maslov index of a concatenation is the sum of the indices. -/
@[simp]
theorem graphMaslovIndex_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    graphMaslovIndex (γ₁.trans γ₂) = graphMaslovIndex γ₁ + graphMaslovIndex γ₂ := by
  rw [graphMaslovIndex, Path.map_trans, UnitaryGroup.maslovIndex_trans, graphMaslovIndex,
    graphMaslovIndex]

/-- Reversing a path negates its graph Maslov index. -/
@[simp]
theorem graphMaslovIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    graphMaslovIndex γ.symm = -graphMaslovIndex γ := by
  rw [graphMaslovIndex, ← Path.map_symm, UnitaryGroup.maslovIndex_symm, graphMaslovIndex]

/-- The square of the determinant of the unitary graph frame is the graph phase
`det F / conj (det F)` of the graph frame `F`. -/
private theorem detCircle_graphUnitary_sq (A : GLSymplectic n ℝ) :
    detCircle (graphUnitary A) ^ 2 = graphPhase A := by
  set S := CFC.sqrt (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ *
    ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
  -- `det F = det U · det S` with `det S` real and nonzero, and `conj (det U) = (det U)⁻¹`.
  have hF : (graphFrame ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det =
      (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det * (S.det : ℂ) := by
    rw [← coe_graphUnitary_mul_sqrt, det_mul, ← Complex.ofRealHom_eq_coe, RingHom.map_det,
      RingHom.mapMatrix_apply]
    rfl
  have hS : (S.det : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (posDef_one_add_transpose_mul _).isUnit_det_sqrt.ne_zero
  have hU : (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det ≠ 0 := by
    rw [← coe_detCircle]
    exact Circle.coe_ne_zero _
  have hconj : conj (graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det =
      ((graphUnitary A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det)⁻¹ := by
    rw [← coe_detCircle, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  refine Circle.ext ?_
  rw [Circle.coe_pow, coe_detCircle, coe_graphPhase, hF, map_mul, Complex.conj_ofReal, hconj]
  field_simp

/-- **The graph Maslov index of a loop is twice its Maslov index.** For a loop `γ` of
symplectic matrices, `μ(Γ ∘ γ, Δ) = 2 μ(γ)`, where `μ(γ)` is the degree of `t ↦ ρ(γ t)`. -/
theorem graphMaslovIndex_eq_two_mul_maslovIndex {A : GLSymplectic n ℝ} (γ : Path A A) :
    graphMaslovIndex γ = 2 * maslovIndex γ := by
  have hL₀ := isMaximalTotallyReal_realSubspace (n := n ⊕ n)
  have hphase (t : I) : ((γ.map continuous_graphPhase) t : ℂ) =
      hL₀.maslovPhase ((graphLoop γ).isMaximalTotallyReal t) :=
    (coe_graphPhase_eq_maslovPhase (γ t)).trans
      (hL₀.maslovPhase_congr _ _ (graphLoop_apply γ t).symm)
  have hloop := maslovIndex_graphLoop γ
  rw [(graphLoop γ).maslovIndex_eq_degree hL₀ _ hphase] at hloop
  -- Along the loop, `det (V⁻¹ U)² = det (V)⁻² · det (U)²` is a constant times the graph phase.
  let c : Circle := (detCircle (graphUnitary (1 : GLSymplectic n ℝ)))⁻¹ ^ 2
  have hdeg : Circle.degree ((detSouriauPath (γ.map continuous_star_graphUnitary_one_mul)).cast
      rfl rfl) = Circle.degree ((Path.refl c).mul (γ.map continuous_graphPhase)) :=
    Circle.degree_congr _ _ fun t ↦ by
      simp only [Path.cast_coe, detSouriauPath_apply, Path.map_coe, Function.comp_apply,
        Path.mul_apply, Path.refl_apply, detCircle_souriau, map_mul, mul_pow, c,
        ← detCircle_graphUnitary_sq, Unitary.star_eq_inv, map_inv]
  rw [graphMaslovIndex, UnitaryGroup.maslovIndex_eq_degree _ rfl, hdeg, Circle.degree_mul,
    Circle.degree_refl, zero_add, hloop]
  push_cast
  ring

/-! ### The Cayley transform -/

/-- **The Cayley transform of a symplectic matrix is symmetric.** For a symplectic matrix `A`
with `1 + A` invertible, `J (1 - A) (1 + A)⁻¹` is symmetric. -/
theorem isHermitian_J_mul_one_sub_mul_inv (A : GLSymplectic n ℝ)
    (hA : IsUnit (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    (J n ℝ * (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
      (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹).IsHermitian := by
  set M := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  set P := 1 + M with hP
  have hPT : IsUnit Pᵀ.det := by rwa [det_transpose]
  -- From `Aᵀ J A = J`: `-(1 - Aᵀ) J (1 + A) = (1 + A)ᵀ J (1 - A)`.
  have key : -((1 - Mᵀ) * J n ℝ * P) = Pᵀ * J n ℝ * (1 - M) := by
    have h : -((1 - Mᵀ) * J n ℝ * P) - Pᵀ * J n ℝ * (1 - M) =
        (Mᵀ * J n ℝ * M - J n ℝ) + (Mᵀ * J n ℝ * M - J n ℝ) := by
      rw [hP, transpose_add, transpose_one]
      noncomm_ring
    rw [← sub_eq_zero, h, transpose_mul_J_mul, sub_self, add_zero]
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_mul,
    J_transpose, transpose_nonsing_inv]
  calc (Pᵀ)⁻¹ * ((1 - M)ᵀ * -J n ℝ) = (Pᵀ)⁻¹ * -((1 - Mᵀ) * J n ℝ * P) * P⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, mul_nonsing_inv _ hA,
          Matrix.mul_one, transpose_sub, transpose_one]
    _ = J n ℝ * (1 - M) * P⁻¹ := by
        rw [key, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hPT, Matrix.one_mul]

/-- The square root `√(1 + 1ᵀ 1) = √2` of the Gram matrix of the diagonal. -/
private theorem sqrt_one_add_transpose_one_mul_one :
    CFC.sqrt (1 + (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * 1) = Real.sqrt 2 • 1 := by
  refine CFC.sqrt_unique ?_ (nonneg_iff_posSemidef.2 (PosSemidef.one.smul (Real.sqrt_nonneg 2)))
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt zero_le_two,
    transpose_one, Matrix.one_mul, two_smul]

/-- The unitary frame of the diagonal is `2^{-1/2}` times its graph frame. -/
private theorem coe_graphUnitary_one :
    (graphUnitary (1 : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      ((Real.sqrt 2)⁻¹ : ℂ) • graphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  have h := coe_graphUnitary_mul_sqrt (1 : GLSymplectic n ℝ)
  simp only [OneMemClass.coe_one, Units.val_one, sqrt_one_add_transpose_one_mul_one] at h
  have hs : (Real.sqrt 2 • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)).map ((↑) : ℝ → ℂ) =
      (Real.sqrt 2 : ℂ) • 1 := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  rw [hs, Matrix.mul_smul, Matrix.mul_one] at h
  rw [← h, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- **The graph relative to the diagonal is the graph of a symmetric matrix.** For a symplectic
matrix `A` with `1 + A` invertible, the unitary frame `V⁻¹ U(A)` frames the graph `{x + i B x}`
of the real symmetric matrix `B = J (1 - A) (1 + A)⁻¹`: its Souriau map is the Cayley transform
of `B`. -/
theorem souriau_star_graphUnitary_one_mul_eq_cayley (A : GLSymplectic n ℝ)
    (hA : IsUnit (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    (souriau (star (graphUnitary 1) * graphUnitary A) : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      cayley ((J n ℝ * (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
        (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹).map ((↑) : ℝ → ℂ)) := by
  set M := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) with hM
  set B := J n ℝ * (1 - M) * (1 + M)⁻¹
  have hmul (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
      (X * Y).map ((↑) : ℝ → ℂ) = X.map (↑) * Y.map (↑) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  have hB : B * (1 + M) = J n ℝ - J n ℝ * M := by
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  -- `V⁻¹ U(A) = 2^{-1/2} F(1)ᴴ F(A) S⁻¹`, and `F(1)ᴴ F(A) = (1 + A) + i (J - J A)` is
  -- `(1 + i B) (1 + A)`.
  have hF : (graphFrame (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))ᴴ * graphFrame M =
      (1 + Complex.I • B.map ((↑) : ℝ → ℂ)) * (1 + M).map (↑) := by
    rw [conjTranspose_graphFrame_mul_graphFrame, transpose_one, Matrix.one_mul, Matrix.one_mul,
      Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, ← hmul, hB]
  refine souriau_eq_cayley_of_coe_eq_mul (isHermitian_J_mul_one_sub_mul_inv A hA)
    (M := (Real.sqrt 2)⁻¹ • ((1 + M) * (CFC.sqrt (1 + Mᵀ * M))⁻¹)) ?_
  have hsmul : ((Real.sqrt 2)⁻¹ • ((1 + M) * (CFC.sqrt (1 + Mᵀ * M))⁻¹)).map ((↑) : ℝ → ℂ) =
      ((Real.sqrt 2)⁻¹ : ℂ) • ((1 + M).map (↑) * (CFC.sqrt (1 + Mᵀ * M))⁻¹.map (↑)) := by
    rw [← hmul]
    ext i j
    simp
  rw [Submonoid.coe_mul, Unitary.coe_star, coe_graphUnitary_one, coe_graphUnitary, hsmul,
    star_eq_conjTranspose, conjTranspose_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hF,
    Matrix.mul_smul, Matrix.mul_assoc]
  simp [← Complex.ofReal_inv, ← hM]

/-- **The graph Maslov index of a path avoiding the eigenvalue `-1`.** Along a path `γ` of
symplectic matrices none of which has the eigenvalue `-1`, the graph Maslov index is half the
change of the signature of the Cayley transform `J (1 - γ t) (1 + γ t)⁻¹`. -/
theorem graphMaslovIndex_eq_signature_sub {A B : GLSymplectic n ℝ} (γ : Path A B)
    (hγ : ∀ t, IsUnit (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    graphMaslovIndex γ =
      (signature (J n ℝ * (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
          (1 + ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹) -
        signature (J n ℝ * (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
          (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹) : ℝ) / 2 := by
  have hM := continuous_coe.comp γ.continuous
  have hcont : Continuous fun t ↦ J n ℝ * (1 - ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
      (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹ :=
    (continuous_const.mul (continuous_const.sub hM)).mul (continuous_iff_continuousAt.2 fun t ↦
      (continuous_const.add hM).continuousAt.matrix_inv (hγ t).ne_zero)
  have h := maslovIndex_eq_signature_sub_of_souriau_eq_cayley
    (γ.map continuous_star_graphUnitary_one_mul) hcont
    (fun t ↦ isHermitian_J_mul_one_sub_mul_inv (γ t) (hγ t))
    (fun t ↦ souriau_star_graphUnitary_one_mul_eq_cayley (γ t) (hγ t))
  rw [graphMaslovIndex]
  simpa only [Path.source, Path.target] using h

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** `CZ(γ) = -μ(Γ ∘ γ, Δ)` of a path `γ` of symplectic matrices
starting at the identity: minus the Robbin–Salamon index of its path of graphs relative to the
diagonal (`TauCeti.GLSymplectic.graphMaslovIndex`). It is real-valued; at the identity the graph
is the diagonal, which contributes half of a crossing. -/
def conleyZehnderIndex {A : GLSymplectic n ℝ} (γ : Path 1 A) : ℝ :=
  -graphMaslovIndex γ

/-- The Conley–Zehnder index is minus the graph Maslov index. -/
theorem conleyZehnderIndex_def {A : GLSymplectic n ℝ} (γ : Path 1 A) :
    conleyZehnderIndex γ = -graphMaslovIndex γ :=
  (rfl)

/-- **Homotopy invariance.** Paths from the identity that are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopic {A : GLSymplectic n ℝ} {γ₀ γ₁ : Path 1 A}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, graphMaslovIndex_eq_of_homotopic h]

/-- The constant path at the identity has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl : conleyZehnderIndex (Path.refl (1 : GLSymplectic n ℝ)) = 0 := by
  simp [conleyZehnderIndex]

/-- **Catenation.** Continuing a path `γ` from the identity by a path `δ` changes its
Conley–Zehnder index by minus the graph Maslov index of `δ`. -/
theorem conleyZehnderIndex_trans {A B : GLSymplectic n ℝ} (γ : Path 1 A) (δ : Path A B) :
    conleyZehnderIndex (γ.trans δ) = conleyZehnderIndex γ - graphMaslovIndex δ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, graphMaslovIndex_trans]
  ring

/-- **The loop law.** Running a loop `φ` of symplectic matrices at the identity before a path `γ`
changes the Conley–Zehnder index by `-2 μ(φ)`, minus twice the Maslov index of the loop. -/
theorem conleyZehnderIndex_trans_of_loop {A : GLSymplectic n ℝ} (φ : Path 1 1) (γ : Path 1 A) :
    conleyZehnderIndex (φ.trans γ) = conleyZehnderIndex γ - 2 * maslovIndex φ := by
  rw [conleyZehnderIndex, conleyZehnderIndex, graphMaslovIndex_trans,
    graphMaslovIndex_eq_two_mul_maslovIndex]
  ring

/-- **The Conley–Zehnder index of a path avoiding the eigenvalue `-1`.** If no matrix along the
path `γ` from the identity to `A` has the eigenvalue `-1`, then
`CZ(γ) = -sign (J (1 - A) (1 + A)⁻¹) / 2`. -/
theorem conleyZehnderIndex_eq_neg_signature {A : GLSymplectic n ℝ} (γ : Path 1 A)
    (hγ : ∀ t, IsUnit (1 + ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :
    conleyZehnderIndex γ =
      -(signature (J n ℝ * (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
        (1 + ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹) : ℝ) / 2 := by
  rw [conleyZehnderIndex, graphMaslovIndex_eq_signature_sub γ hγ]
  simp [neg_div]

/-! ### Normalization on rotations -/

variable (n) in
/-- The **scalar rotation** by the angle `θ`: the realification of `e^{i θ} I`, the rotation by
`θ` in every coordinate plane of `ℝ^{n ⊕ n}`. -/
def scalarRotation (θ : ℝ) : GLSymplectic n ℝ :=
  ofUnitary ⟨(Circle.exp θ : ℂ) • (1 : Matrix n n ℂ),
    Unitary.smul_mem_of_mem (Circle.exp θ).coe_mem_unitary (one_mem _)⟩

/-- The scalar rotation by `θ` is `cos θ + sin θ J`. -/
theorem coe_scalarRotation (θ : ℝ) :
    ((scalarRotation n θ : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      Real.cos θ • 1 + Real.sin θ • J n ℝ := by
  rw [scalarRotation, coe_ofUnitary]
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [J, h, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The scalar rotation by `0` is the identity. -/
@[simp]
theorem scalarRotation_zero : scalarRotation n 0 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_scalarRotation]
  simp

/-- The scalar rotation depends continuously on the angle. -/
theorem continuous_scalarRotation : Continuous (scalarRotation n) := by
  refine continuous_ofUnitary.comp (Continuous.subtype_mk ?_ _)
  fun_prop

variable (n) in
/-- The path `t ↦ scalarRotation n (θ t)` of rotations from the identity to the rotation by `θ`. -/
def scalarRotationPath (θ : ℝ) : Path (1 : GLSymplectic n ℝ) (scalarRotation n θ) where
  toFun t := scalarRotation n (θ * t)
  continuous_toFun := continuous_scalarRotation.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

@[simp]
theorem scalarRotationPath_apply (θ : ℝ) (t : I) :
    scalarRotationPath n θ t = scalarRotation n (θ * t) :=
  (rfl)

/-- For `|α| < π`, the matrix `1 + R(α)` is invertible, and the Cayley transform
`J (1 - R(α)) (1 + R(α))⁻¹` of the rotation `R(α)` is `tan (α / 2) • 1`. -/
private theorem isUnit_det_one_add_scalarRotation_and {α : ℝ} (h₁ : -Real.pi < α)
    (h₂ : α < Real.pi) :
    IsUnit (1 + ((scalarRotation n α : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ∧
      J n ℝ * (1 - ((scalarRotation n α : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *
          (1 + ((scalarRotation n α : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))⁻¹ =
        Real.tan (α / 2) • 1 := by
  set x := α / 2
  have hα : α = 2 * x := by ring
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : Real.cos α = 2 * Real.cos x ^ 2 - 1 := by rw [hα, Real.cos_two_mul]
  have hs : Real.sin α = 2 * Real.sin x * Real.cos x := by rw [hα, Real.sin_two_mul]
  have hsq := Real.sin_sq_add_cos_sq x
  have htan : Real.tan x = Real.sin x / Real.cos x := Real.tan_eq_sin_div_cos x
  rw [coe_scalarRotation]
  -- `(1 + R) ((1 + cos α) - sin α J) = 4 cos² (α / 2)`, since `J² = -1`.
  have hprod : (1 + (Real.cos α • 1 + Real.sin α • J n ℝ)) *
      ((1 + Real.cos α) • 1 - Real.sin α • J n ℝ) = (4 * Real.cos x ^ 2) • 1 := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, J_squared, smul_neg]
    rw [hc, hs]
    linear_combination (norm := module)
      ((4 * Real.cos x ^ 2) * hsq) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hinv : (1 + (Real.cos α • 1 + Real.sin α • J n ℝ)) *
      ((4 * Real.cos x ^ 2)⁻¹ • ((1 + Real.cos α) • 1 - Real.sin α • J n ℝ)) = 1 := by
    rw [Matrix.mul_smul, hprod, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  have hunit : IsUnit (1 + (Real.cos α • 1 + Real.sin α • J n ℝ)).det :=
    isUnit_det_of_right_inverse hinv
  refine ⟨hunit, ?_⟩
  -- `J (1 - R) = tan (α / 2) (1 + R)`.
  have hJ : J n ℝ * (1 - (Real.cos α • 1 + Real.sin α • J n ℝ)) =
      Real.tan x • (1 + (Real.cos α • 1 + Real.sin α • J n ℝ)) := by
    have e₁ : Real.sin α = Real.tan x * (1 + Real.cos α) := by
      rw [htan, hc, hs]
      field_simp
      ring
    have e₂ : 1 - Real.cos α = Real.tan x * Real.sin α := by
      have h : Real.tan x * Real.sin α = 2 * Real.sin x ^ 2 := by
        rw [htan, hs]
        field_simp
      rw [h, hc]
      linear_combination (-2) * hsq
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, J_squared,
      smul_neg]
    linear_combination (norm := module) e₁ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + e₂ • J n ℝ
  rw [hJ, Matrix.smul_mul, mul_nonsing_inv _ hunit]

/-- **Normalization of the Conley–Zehnder index.** For `θ ∈ (-π, π)`, the path of rotations by
the angles `θ t` in every coordinate plane of `ℝ^{n ⊕ n}` has Conley–Zehnder index
`-sign (θ) · n`. In particular a small positive rotation of `ℝ²` has index `-1`. -/
theorem conleyZehnderIndex_scalarRotationPath {θ : ℝ} (h₁ : -Real.pi < θ) (h₂ : θ < Real.pi) :
    conleyZehnderIndex (scalarRotationPath n θ) = -(SignType.sign θ * Fintype.card n) := by
  have hbound (t : I) : -Real.pi < θ * t ∧ θ * t < Real.pi := by
    have ht₀ := t.2.1
    have ht₁ := t.2.2
    rcases le_total θ 0 with hθ | hθ
    · exact ⟨by nlinarith [hθ], by nlinarith [hθ, Real.pi_pos]⟩
    · exact ⟨by nlinarith [hθ, Real.pi_pos], by nlinarith [hθ]⟩
  have hγ (t : I) := (isUnit_det_one_add_scalarRotation_and (n := n) (hbound t).1 (hbound t).2).1
  rw [conleyZehnderIndex_eq_neg_signature _ hγ, (isUnit_det_one_add_scalarRotation_and h₁ h₂).2,
    smul_one_eq_diagonal, signature_diagonal]
  -- The scalar `tan (θ / 2)` has the sign of `θ`.
  rcases lt_trichotomy θ 0 with h | h | h
  · have ht : Real.tan (θ / 2) < 0 :=
      Real.tan_neg_of_neg_of_pi_div_two_lt (by linarith) (by linarith)
    simp [ht, ht.not_gt, h]
  · simp [h]
  · have ht : 0 < Real.tan (θ / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
    simp [ht, h]

end TauCeti.GLSymplectic
