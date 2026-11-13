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

* `TauCeti.GLSymplectic.graphUnitary`: the unitary frame of the graph of a symplectic matrix.
* `TauCeti.GLSymplectic.graphDiagonalFrame`: the unitary frame of the graph, moved so that the
  diagonal becomes the real points.
* `TauCeti.GLSymplectic.conleyZehnderIndex`: the Conley–Zehnder index of a path of symplectic
  matrices.

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
  -- Write `e^{i x} = cos x + i sin x` (`Complex.exp_ofReal_mul_I`) and
  -- `e^{2 i x} = (cos² x - sin² x) + i (2 sin x cos x)`.
  have hre (x : ℝ) : (Complex.exp (2 * x * Complex.I)).re = Real.cos x ^ 2 - Real.sin x ^ 2 := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Real.cos_two_mul]
    linear_combination Real.sin_sq_add_cos_sq x
  have him (x : ℝ) : (Complex.exp (2 * x * Complex.I)).im = 2 * Real.sin x * Real.cos x := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_im,
      Real.sin_two_mul]
  -- Off the diagonal both sides vanish; the four diagonal entries are trigonometric identities,
  -- from `sin² + cos² = 1` and `i² = -1`.
  rw [coe_graphDiagonalFrame_of_transpose_mul_self hAA, hA]
  ext (i | i) (j | j) <;>
  by_cases hij : i = j <;>
  simp only [hij, hre, him, one_div, graphFrame_def, toBlocks₁₁, Matrix.one_apply, Sum.inl.injEq,
    toBlocks₂₁, ne_eq, reduceCtorEq, not_false_eq_true, Ne.symm, toBlocks₁₂, toBlocks₂₂,
    Sum.inr.injEq, ofReal_mul, ofReal_ofNat, realify_apply_inl_inl, diagonal_apply,
    RCLike.re_to_complex, apply_ite Complex.re, zero_re, realify_apply_inr_inl,
    RCLike.im_to_complex, apply_ite Complex.im, zero_im, realify_apply_inl_inr,
    realify_apply_inr_inr, Matrix.smul_apply, Matrix.mul_apply, conjTranspose_apply,
    RCLike.star_def, Fintype.sum_sum_type, fromBlocks_apply₁₁, apply_ite (starRingEnd ℂ), map_one,
    map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    fromBlocks_apply₂₁, Matrix.add_apply, map_apply, of_apply, apply_ite     ((↑) : ℝ → ℂ),
    ofReal_one, ofReal_zero, smul_eq_mul, add_zero, ofReal_sub, ofReal_pow, ofReal_cos, ofReal_sin,
    ite_mul, one_mul, zero_mul, exp_ofReal_mul_I, Sum.elim_inl, Finset.sum_ite_eq, add_re, mul_re,
    I_re, sin_ofReal_im, I_im, sub_self, ofReal_cos_ofReal_re, fromBlocks_apply₁₂, Matrix.neg_apply,
    mul_neg, Finset.sum_neg_distrib, fromBlocks_apply₂₂, ofReal_neg, add_im, cos_ofReal_im, mul_im,
    zero_add, ofReal_sin_ofReal_re, neg_zero, map_neg, conj_I, neg_neg, neg_mul, Sum.elim_inr,
    I_mul_I]
  · linear_combination (-1 / 2 : ℂ) * Complex.sin_sq_add_cos_sq (ψ j : ℂ)
  · linear_combination (Complex.I / 2) * Complex.sin_sq_add_cos_sq (ψ j : ℂ)
  · linear_combination (-Complex.I / 2) * Complex.sin_sq_add_cos_sq (ψ j : ℂ) -
      Complex.sin (ψ j : ℂ) * Complex.cos (ψ j : ℂ) * Complex.I_sq
  · linear_combination (-1 / 2 : ℂ) * Complex.sin_sq_add_cos_sq (ψ j : ℂ) +
      (Complex.sin (ψ j : ℂ) ^ 2 / 2 - Complex.cos (ψ j : ℂ) ^ 2 / 2) * Complex.I_sq

/-- **Normalization by rotations.** For a path of rotations `γ t = diag (e^{i θ_j t})` of `ℂⁿ`, with
continuous angles `θ_j`, the Conley–Zehnder index is `-2 ∑ j, (c(θ_j 1 / 2) - c(θ_j 0 / 2))`,
where `c(x) = (⌊x / π⌋ + ⌈x / π⌉) / 2` is the half-integer count of the multiples of `π` below
`x`. -/
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

/-- A path of rotations `diag (e^{i θ_j t})` of `ℂⁿ` starting at the identity, whose angles all end
in `(2 π k, 2 π (k + 1))`, has Conley–Zehnder index `-(2 k + 1) n`. -/
private theorem conleyZehnderIndex_eq_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify)
    (h0 : ∀ j, θ j 0 = 0) (k : ℤ) (h1 : ∀ j, θ j 1 / (2 * Real.pi) ∈ Set.Ioo (k : ℝ) (k + 1)) :
    conleyZehnderIndex γ = -(2 * k + 1) * Fintype.card n := by
  have key (j : n) : (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2 -
      ((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2) = k + 1 / 2 := by
    rw [floor_add_ceil_of_mem_Ioo (h1 j), h0 j, zero_div, Int.floor_zero, Int.ceil_zero]
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
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [conleyZehnderIndex_eq_of_rotation γ hθ hγ h0 0 fun j => ?_]
  · norm_num
  · rw [Int.cast_zero, zero_add]
    exact ⟨div_pos (h1 j).1 hπ, (div_lt_one hπ).2 (h1 j).2⟩

/-- **A clockwise rotation has index `n`.** A path of rotations `diag (e^{i θ_j t})` of `ℂⁿ`
starting at the identity, whose angles all end in `(-2π, 0)`, has Conley–Zehnder index `n`. In
particular a small negative rotation of `ℝ² = ℂ` has index `1`. -/
theorem conleyZehnderIndex_eq_card_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify)
    (h0 : ∀ j, θ j 0 = 0) (h1 : ∀ j, θ j 1 ∈ Set.Ioo (-(2 * Real.pi)) 0) :
    conleyZehnderIndex γ = Fintype.card n := by
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [conleyZehnderIndex_eq_of_rotation γ hθ hγ h0 (-1) fun j => ?_]
  · norm_num
  · rw [Int.cast_neg, Int.cast_one, neg_add_cancel]
    exact ⟨(lt_div_iff₀ hπ).2 (by linarith [(h1 j).1]), div_neg_of_neg_of_pos (h1 j).2 hπ⟩

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
