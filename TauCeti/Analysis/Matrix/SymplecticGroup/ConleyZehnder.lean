/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.OfReal
import TauCeti.Algebra.Order.Floor.Ring

/-!
# The Conley–Zehnder index of a path of symplectic matrices

Identify `ℝ^{n ⊕ n}` with `ℂⁿ` by `φ (x, y) = x + i y`. The graph `Γ(A)` of a symplectic matrix `A`
is the real subspace `{(conj (φ x), φ (A x))}` of `ℂⁿ × ℂⁿ = ℂ^{n ⊕ n}`
(`Matrix.graphSubspace`), a Lagrangian subspace for the standard symplectic form `Im ⟪·, ·⟫`, whose
first factor carries `-ω`. Following Robbin and Salamon, the **Conley–Zehnder index** of a path
`Ψ` of symplectic matrices is read off from the path of graphs `t ↦ Γ(Ψ t)` relative to the
diagonal `Δ = Γ(1)`. With the sign convention `CZ = -μ_RS` it is

`CZ(Ψ) = -μ_RS(t ↦ Γ(Ψ t), Δ)`

(`TauCeti.GLSymplectic.conleyZehnderIndex`), where `μ_RS` is Souriau's formula for the
Robbin–Salamon index (`Matrix.UnitaryGroup.maslovIndex`).

To apply Souriau's formula, which is stated for paths of unitary frames relative to the real
points `ℝ^{n ⊕ n}`, two normalizations are made.

* The graph frame `F` of `A` (`Matrix.graphFrame`) has Gram matrix `Fᴴ F = 1 + Aᵀ A`, a real
  positive definite matrix (`Matrix.conjTranspose_graphFrame_mul_graphFrame`). Multiplying `F` on
  the right by the real matrix `(1 + Aᵀ A) ^ (-1/2)` gives a unitary frame of the same graph
  (`TauCeti.GLSymplectic.graphUnitary`, `TauCeti.GLSymplectic.realImage_graphUnitary`), depending
  continuously on `A`.
* Multiplying on the left by the inverse of the unitary frame of the diagonal moves the diagonal to
  the real points: the resulting frame `TauCeti.GLSymplectic.graphDiagonalFrame` is the identity at
  `A = 1`, and frames the image of the graph of `A` under a fixed unitary map
  (`TauCeti.GLSymplectic.realImage_graphDiagonalFrame`). The Robbin–Salamon index is invariant
  under unitary maps, which are symplectic.

The index is invariant under homotopies with fixed endpoints, additive under catenation, and odd
under reversal. It is normalized by the rotations: for a path of rotations
`t ↦ diag (e^{i θ_j t})` of `ℂⁿ`, each angle `θ_j` contributes minus twice the half-integer count
of the multiples of `π` crossed by `θ_j / 2`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_sum_of_diagonal`). In particular a counterclockwise
rotation by an angle in `(0, 2π)` of each complex coordinate has index `-n`, and a clockwise one
has index `n` (`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_card_of_rotation`,
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_card_of_rotation`): a small positive rotation of `ℝ²`
has index `-1`. On a loop it is minus twice the Maslov index of the loop
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_two_mul_maslovIndex`).

## Main definitions

* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a path of symplectic
  matrices.

## Main results

* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopic`,
  `TauCeti.GLSymplectic.conleyZehnderIndex_trans`: homotopy invariance and catenation.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_sum_of_diagonal`: the index of a path of rotations.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_rotation`: a path of rotations from the identity
  whose angles all end in `(2 π k, 2 π (k + 1))` has index `-(2 k + 1) n`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_two_mul_maslovIndex`: on a loop the index is
  minus twice the Maslov index.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Sections 2 and 4 (the index of a path of Lagrangians, and the Conley–Zehnder index through
  graphs).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117–148.
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Mathematics Series **7** (1999),
  Section 2.4 (the Conley–Zehnder index and its normalization).
-/

public section

noncomputable section

open Matrix Matrix.UnitaryGroup Complex
open scoped unitInterval MatrixOrder Matrix.Norms.L2Operator NNReal

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The Conley–Zehnder index -/

/-- The **Conley–Zehnder index** of a path `γ` of symplectic matrices, in the convention
`CZ = -μ_RS`: minus the Robbin–Salamon index of the path of graphs `t ↦ Γ(γ t)` relative to the
diagonal `Γ(1)`, computed by Souriau's formula `Matrix.UnitaryGroup.maslovIndex` on the frames
`TauCeti.GLSymplectic.graphDiagonalFrame`. -/
def conleyZehnderIndex {A B : GLSymplectic n ℝ} (γ : Path A B) : ℝ :=
  -Matrix.UnitaryGroup.maslovIndex (γ.map continuous_graphDiagonalFrame)

/-- The Conley–Zehnder index is minus the Souriau index of the frames of the graphs relative to the
diagonal. -/
theorem conleyZehnderIndex_def {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ = -Matrix.UnitaryGroup.maslovIndex (γ.map continuous_graphDiagonalFrame) :=
  (rfl)

/-- **Homotopy invariance.** Paths of symplectic matrices that are homotopic relative to their
endpoints have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopic {A B : GLSymplectic n ℝ} {γ₀ γ₁ : Path A B}
    (h : γ₀.Homotopic γ₁) : conleyZehnderIndex γ₀ = conleyZehnderIndex γ₁ := by
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def,
    Matrix.UnitaryGroup.maslovIndex_eq_of_homotopic (h.map ⟨_, continuous_graphDiagonalFrame⟩)]

/-- The constant path has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl (A : GLSymplectic n ℝ) :
    conleyZehnderIndex (Path.refl A) = 0 := by
  rw [conleyZehnderIndex_def, Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq _
      (Path.refl (graphDiagonalFrame A)) fun _ => by simp,
    Matrix.UnitaryGroup.maslovIndex_refl, neg_zero]

/-- **Catenation.** The Conley–Zehnder index of a concatenation of paths is the sum of their
indices. -/
@[simp]
theorem conleyZehnderIndex_trans {A B C : GLSymplectic n ℝ} (γ₁ : Path A B) (γ₂ : Path B C) :
    conleyZehnderIndex (γ₁.trans γ₂) = conleyZehnderIndex γ₁ + conleyZehnderIndex γ₂ := by
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, conleyZehnderIndex_def, Path.map_trans,
    Matrix.UnitaryGroup.maslovIndex_trans, neg_add]

/-- Reversing a path negates its Conley–Zehnder index. -/
@[simp]
theorem conleyZehnderIndex_symm {A B : GLSymplectic n ℝ} (γ : Path A B) :
    conleyZehnderIndex γ.symm = -conleyZehnderIndex γ := by
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, ← Path.map_symm,
    Matrix.UnitaryGroup.maslovIndex_symm]

/-! ### Frames of graphs of rotations -/

/-- **The graph of a rotation relative to the diagonal.** For the rotation
`A = diag (e^{2 i ψ_j})` of `ℂⁿ`, the frame of the graph of `A` relative to the diagonal is the
diagonal frame `diag (e^{i ψ_j}, e^{i ψ_j})` times the real orthogonal matrix of the rotation
`diag (e^{i ψ_j})`. -/
private theorem coe_graphDiagonalFrame_of_diagonal {A : GLSymplectic n ℝ} (ψ : n → ℝ)
    (hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (↑(2 * ψ j) * Complex.I)).realify) :
    (graphDiagonalFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonal (Sum.elim (fun j => Complex.exp (ψ j * Complex.I))
        (fun j => Complex.exp (ψ j * Complex.I))) *
      (diagonal fun j => Complex.exp (ψ j * Complex.I)).realify.map ((↑) : ℝ → ℂ) := by
  have hAA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * (A : GL (n ⊕ n) ℝ) = 1 := by
    rw [hA, ← realify_conjTranspose, ← realify_mul, ← star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem (diagonal_exp_mem_unitaryGroup (2 * ψ ·)), realify_one]
  -- Both sides are block matrices: `F(1)ᴴ F(A) / 2` for the graph frames
  -- `F(W.realify) = (1, -i; W, i W)`, and `diag (e^{i ψ}, e^{i ψ})` times the realification.
  rw [coe_graphDiagonalFrame_of_transpose_mul_self hAA, hA, ← realify_one (𝕜 := ℂ),
    graphFrame_realify, graphFrame_realify, ← fromBlocks_diagonal,
    ← fromBlocks_toBlocks ((diagonal _).realify.map _), fromBlocks_conjTranspose,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  -- Every block is diagonal. On the diagonal, write `e^{i x} = cos x + i sin x` and use the
  -- double angle formulas, `sin² x + cos² x = 1` and `i² = -1`.
  congr 1 <;> ext i j <;> by_cases hij : i = j <;>
    simp [hij, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, diagonal_mul, Complex.exp_mul_I]
  · linear_combination (1 / 2 : ℂ) * Complex.cos_two_mul (ψ j : ℂ) +
      Complex.I / 2 * Complex.sin_two_mul (ψ j : ℂ)
  · linear_combination Complex.I / 2 * Complex.cos_two_mul (ψ j : ℂ) +
      Complex.I ^ 2 / 2 * Complex.sin_two_mul (ψ j : ℂ) +
      Complex.I * Complex.sin_sq_add_cos_sq (ψ j : ℂ) +
      Complex.sin (ψ j) * Complex.cos (ψ j) * Complex.I_sq
  · linear_combination -Complex.I / 2 * Complex.cos_two_mul (ψ j : ℂ) -
      Complex.I ^ 2 / 2 * Complex.sin_two_mul (ψ j : ℂ) -
      Complex.I * Complex.sin_sq_add_cos_sq (ψ j : ℂ) -
      Complex.sin (ψ j) * Complex.cos (ψ j) * Complex.I_sq
  · linear_combination -Complex.I ^ 2 / 2 * Complex.cos_two_mul (ψ j : ℂ) -
      Complex.I ^ 3 / 2 * Complex.sin_two_mul (ψ j : ℂ) +
      (1 / 2 - Complex.cos (ψ j) ^ 2 - Complex.sin (ψ j) * Complex.cos (ψ j) * Complex.I) *
        Complex.I_sq

/-- **Normalization by rotations.** For a path of rotations `γ t = diag (e^{i θ_j t})` of `ℂⁿ`, with
continuous angles `θ_j`, the Conley–Zehnder index is `-2 ∑ j, (c(θ_j 1 / 2) - c(θ_j 0 / 2))`,
where `c(x) = (⌊x / π⌋ + ⌈x / π⌉) / 2` is the half-integer step function with `c(k π) = k` and
`c(x) = k + 1/2` on `(k π, (k + 1) π)`. So `c(θ_j 1 / 2) - c(θ_j 0 / 2)` is the signed
half-integer count of the multiples of `π` crossed by `θ_j / 2`. -/
theorem conleyZehnderIndex_eq_sum_of_diagonal {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify) :
    conleyZehnderIndex γ = -2 * ∑ j,
      (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2 -
        ((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2) := by
  -- Half angles `ψ = θ / 2`. The frame of the graph of `γ t` relative to the diagonal is the
  -- diagonal frame `δ t = diag (e^{i ψ}, e^{i ψ})` times the realified rotation `diag (e^{i ψ})`,
  -- a real orthogonal matrix, which does not change the Souriau map.
  set ψ : n → I → ℝ := fun j t => θ j t / 2
  have hψ (t : I) : ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (↑(2 * ψ j t) * Complex.I)).realify := by
    rw [hγ t]
    simp only [ψ, mul_div_cancel₀ _ (two_ne_zero' ℝ)]
  have hφ (k : n ⊕ n) : Continuous (Sum.elim ψ ψ k) := by
    rcases k with k | k <;> exact (hθ k).div_const 2
  let δ : Path _ _ :=
    ⟨⟨fun t => unitaryTorusHom (n ⊕ n) fun k => Circle.exp (Sum.elim ψ ψ k t),
      continuous_unitaryTorusHom.comp (continuous_pi fun k => Circle.exp.continuous.comp (hφ k))⟩,
      rfl, rfl⟩
  have hδ (t : I) : (δ t : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      diagonal fun k => Complex.exp (Sum.elim ψ ψ k t * Complex.I) := by
    simp only [δ, Path.coe_mk_mk, coe_unitaryTorusHom, Circle.coe_exp]
  have horth (t : I) :
      (diagonal fun j => Complex.exp (ψ j t * Complex.I)).realify ∈ orthogonalGroup (n ⊕ n) ℝ :=
    realify_mem_orthogonalGroup_iff.2 (diagonal_exp_mem_unitaryGroup (ψ · t))
  have hframe (t : I) :
      graphDiagonalFrame (γ t) = δ t * ⟨_, map_ofReal_mem_unitaryGroup (horth t)⟩ := by
    refine Subtype.ext ?_
    rw [coe_graphDiagonalFrame_of_diagonal (ψ · t) (hψ t), Submonoid.coe_mul, hδ]
    -- The diagonal factors agree entrywise on each summand of `n ⊕ n`.
    congr 2
    ext (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  rw [conleyZehnderIndex_def, Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq _ δ fun t => by
      rw [Path.map_coe, Function.comp_apply, hframe,
        Matrix.UnitaryGroup.souriau_mul_of_mul_transpose_eq_one (δ t)
          ⟨_, map_ofReal_mem_unitaryGroup (horth t)⟩ (map_ofReal_mul_transpose_eq_one (horth t))],
    Matrix.UnitaryGroup.maslovIndex_eq_sum_of_diagonal δ hφ hδ, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ψ, div_div]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Rotations by angles in a band.** A path of rotations `diag (e^{i θ_j t})` of `ℂⁿ` starting at
the identity, whose angles all end in `(2 π k, 2 π (k + 1))`, has Conley–Zehnder index
`-(2 k + 1) n`. -/
theorem conleyZehnderIndex_eq_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify)
    (h0 : ∀ j, θ j 0 = 0) (k : ℤ)
    (h1 : ∀ j, θ j 1 ∈ Set.Ioo (2 * Real.pi * k) (2 * Real.pi * (k + 1))) :
    conleyZehnderIndex γ = -(2 * k + 1) * Fintype.card n := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h1' (j : n) : θ j 1 / (2 * Real.pi) ∈ Set.Ioo (k : ℝ) (k + 1) :=
    ⟨(lt_div_iff₀ hπ).2 (by rw [mul_comm]; exact (h1 j).1),
      (div_lt_iff₀ hπ).2 (by rw [mul_comm]; exact (h1 j).2)⟩
  have key (j : n) : (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2 -
      ((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2) = k + 1 / 2 := by
    rw [floor_add_ceil_of_mem_Ioo (h1' j), h0 j, zero_div, Int.floor_zero, Int.ceil_zero]
    push_cast
    ring
  rw [conleyZehnderIndex_eq_sum_of_diagonal γ hθ hγ, Finset.sum_congr rfl fun j _ => key j,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **A counterclockwise rotation has index `-n`.** A path of rotations `diag (e^{i θ_j t})` of `ℂⁿ`
starting at the identity, whose angles all end in `(0, 2π)`, has Conley–Zehnder index `-n`. In
particular a small positive rotation of `ℝ² = ℂ` has index `-1`. -/
theorem conleyZehnderIndex_eq_neg_card_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify)
    (h0 : ∀ j, θ j 0 = 0) (h1 : ∀ j, θ j 1 ∈ Set.Ioo 0 (2 * Real.pi)) :
    conleyZehnderIndex γ = -Fintype.card n := by
  rw [conleyZehnderIndex_eq_of_rotation γ hθ hγ h0 0 fun j => by simpa using h1 j]
  norm_num

/-- **A clockwise rotation has index `n`.** A path of rotations `diag (e^{i θ_j t})` of `ℂⁿ`
starting at the identity, whose angles all end in `(-2π, 0)`, has Conley–Zehnder index `n`. In
particular a small negative rotation of `ℝ² = ℂ` has index `1`. -/
theorem conleyZehnderIndex_eq_card_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify)
    (h0 : ∀ j, θ j 0 = 0) (h1 : ∀ j, θ j 1 ∈ Set.Ioo (-(2 * Real.pi)) 0) :
    conleyZehnderIndex γ = Fintype.card n := by
  rw [conleyZehnderIndex_eq_of_rotation γ hθ hγ h0 (-1) fun j => by simpa using h1 j]
  norm_num

/-! ### Loops -/

/-- **The loop property.** On a loop of symplectic matrices, the Conley–Zehnder index is minus twice
the Maslov index of the loop. -/
theorem conleyZehnderIndex_eq_neg_two_mul_maslovIndex {A : GLSymplectic n ℝ} (γ : Path A A) :
    conleyZehnderIndex γ = -2 * maslovIndex γ := by
  -- Twice the degree of `det` along the frames is the degree of the graph phase.
  set c := detCircle (star (graphUnitary (1 : GLSymplectic n ℝ))) ^ 2
  have hdeg : Circle.degree
      (((γ.map continuous_graphDiagonalFrame).map continuous_detCircle).map (continuous_pow 2)) =
      Circle.degree ((Path.refl c).mul (γ.map continuous_graphPhase)) :=
    Circle.degree_congr _ _ fun t => by
      simp only [Path.map_coe, Function.comp_apply, Path.mul_apply, Path.refl_apply,
        graphDiagonalFrame_def, map_mul, mul_pow, detCircle_graphUnitary_sq, c]
  rw [Circle.degree_map_pow, Circle.degree_mul, Circle.degree_refl, zero_add] at hdeg
  -- The degree of the graph phase is the Maslov index of the graph loop, `2 μ(γ)`.
  have hμ : Circle.degree (γ.map continuous_graphPhase) = 2 * maslovIndex γ := by
    rw [← maslovIndex_graphLoop,
      (graphLoop γ).maslovIndex_eq_degree isMaximalTotallyReal_realSubspace
        (γ.map continuous_graphPhase) fun t => (coe_graphPhase_eq_maslovPhase (γ t)).trans
          (IsMaximalTotallyReal.maslovPhase_congr _ _ _ (graphLoop_apply γ t).symm)]
  rw [conleyZehnderIndex_def, Matrix.UnitaryGroup.maslovIndex_eq_two_mul_degree]
  have h := congrArg ((↑) : ℤ → ℝ) (hdeg.trans hμ)
  push_cast at h
  linear_combination -h

end TauCeti.GLSymplectic
