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
  rw [conleyZehnderIndex_def, neg_eq_zero,
    ← Matrix.UnitaryGroup.maslovIndex_refl (graphDiagonalFrame A)]
  rfl

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

/-- For an orthogonal symplectic matrix `A`, `1 + Aᵀ A = 2`, so the unitary frame of the graph is
the graph frame divided by `√2`. -/
private theorem coe_graphUnitary_of_transpose_mul_self {A : GLSymplectic n ℝ}
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

/-- For an orthogonal symplectic matrix `A`, the frame of the graph relative to the diagonal is
`F(1)ᴴ F(A) / 2`, for the graph frames `F`. -/
private theorem coe_graphDiagonalFrame_of_transpose_mul_self {A : GLSymplectic n ℝ}
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
  rcases eq_or_ne i j with rfl | hij <;>
  simp [graphFrame_def, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply, toBlocks₁₁,
    toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ),
    apply_ite Complex.re, apply_ite Complex.im, apply_ite (starRingEnd ℂ), ite_mul, mul_ite,
    Finset.sum_ite_eq', Complex.exp_ofReal_mul_I, *, Ne.symm]
  · linear_combination (-1 / 2 : ℂ) * Complex.sin_sq_add_cos_sq (ψ i : ℂ)
  · linear_combination (Complex.I / 2) * Complex.sin_sq_add_cos_sq (ψ i : ℂ)
  · linear_combination (-Complex.I / 2) * Complex.sin_sq_add_cos_sq (ψ i : ℂ) -
      Complex.sin (ψ i : ℂ) * Complex.cos (ψ i : ℂ) * Complex.I_sq
  · linear_combination (-1 / 2 : ℂ) * Complex.sin_sq_add_cos_sq (ψ i : ℂ) +
      (Complex.sin (ψ i : ℂ) ^ 2 / 2 - Complex.cos (ψ i : ℂ) ^ 2 / 2) * Complex.I_sq

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
  -- Half angles, the diagonal frames `diag (e^{i θ / 2}, e^{i θ / 2})` and the real orthogonal
  -- factors `diag (e^{i θ / 2})`, realified.
  set ψ : n → I → ℝ := fun j t => θ j t / 2
  have hψ (t : I) : ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (↑(2 * ψ j t) * Complex.I)).realify := by
    rw [hγ t]
    simp only [ψ, mul_div_cancel₀ _ (two_ne_zero' ℝ)]
  set e : n → I → ℂ := fun j t => Complex.exp (ψ j t * Complex.I)
  let D : I → unitaryGroup (n ⊕ n) ℂ := fun t =>
    ⟨diagonal (Sum.elim (e · t) (e · t)), by
      convert diagonal_exp_mem_unitaryGroup (Sum.elim (ψ · t) (ψ · t)) using 2
      ext (k | k) <;> rfl⟩
  have horth (t : I) : (diagonal (e · t)).realify ∈ orthogonalGroup (n ⊕ n) ℝ :=
    realify_mem_orthogonalGroup_iff.2 (diagonal_exp_mem_unitaryGroup (ψ · t))
  let O : I → unitaryGroup (n ⊕ n) ℂ := fun t =>
    ⟨(diagonal (e · t)).realify.map ((↑) : ℝ → ℂ), map_ofReal_mem_unitaryGroup (horth t)⟩
  have hOc (t : I) : (O t : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      (diagonal (e · t)).realify.map ((↑) : ℝ → ℂ) :=
    rfl
  have hO (t : I) : (O t : Matrix (n ⊕ n) (n ⊕ n) ℂ) * (O t : Matrix (n ⊕ n) (n ⊕ n) ℂ)ᵀ = 1 := by
    have h := congrArg Complex.ofRealHom.mapMatrix ((mem_orthogonalGroup_iff _ _).1 (horth t))
    rw [map_mul, map_one] at h
    rw [hOc, ← transpose_map]
    exact h
  have hDc : Continuous D := by
    refine Continuous.subtype_mk (continuous_pi fun k => continuous_pi fun l => ?_) _
    rcases k with k | k <;> rcases l with l | l <;>
      simp only [diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false,
        Sum.elim_inl, Sum.elim_inr] <;>
      first | exact continuous_const | (split_ifs <;> fun_prop)
  let δ : Path (D 0) (D 1) := ⟨⟨D, hDc⟩, rfl, rfl⟩
  have hδ (t : I) : (δ t : Matrix (n ⊕ n) (n ⊕ n) ℂ) = diagonal (Sum.elim (e · t) (e · t)) :=
    rfl
  have hframe (t : I) : graphDiagonalFrame (γ t) = D t * O t :=
    Subtype.ext (coe_graphDiagonalFrame_of_diagonal (ψ · t) (hψ t))
  rw [conleyZehnderIndex_def, Matrix.UnitaryGroup.maslovIndex_eq_of_souriau_eq _ δ fun t => by
      rw [Path.map_coe, Function.comp_apply, hframe,
        Matrix.UnitaryGroup.souriau_mul_of_mul_transpose_eq_one _ _ (hO t)]
      rfl,
    Matrix.UnitaryGroup.maslovIndex_eq_sum_of_diagonal δ (φ := Sum.elim ψ ψ)
      (fun k => by rcases k with k | k <;> exact (hθ k).div_const 2)
      fun t => by
        -- On each summand, `Sum.elim (e · t) (e · t)` is `e^{i ψ}` by definition of `e`.
        rw [hδ]
        congr 1
        ext (k | k) <;> rfl,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ψ, div_div]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
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
  have key (j : n) : (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2 -
      ((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2) = 1 / 2 := by
    have hπ : 0 < 2 * Real.pi := by positivity
    have hlo : 0 < θ j 1 / (2 * Real.pi) := div_pos (h1 j).1 hπ
    have hhi : θ j 1 / (2 * Real.pi) < 1 := (div_lt_one hπ).2 (h1 j).2
    rw [h0 j, zero_div, Int.floor_zero, Int.ceil_zero,
      (Int.floor_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩]
    norm_num
  rw [conleyZehnderIndex_eq_sum_of_diagonal γ hθ hγ, Finset.sum_congr rfl fun j _ => key j]
  simp
  ring

/-- **A clockwise rotation has index `n`.** A path of rotations `diag (e^{i θ_j t})` of `ℂⁿ`
starting at the identity, whose angles all end in `(-2π, 0)`, has Conley–Zehnder index `n`. In
particular a small negative rotation of `ℝ² = ℂ` has index `1`. -/
theorem conleyZehnderIndex_eq_card_of_rotation {A B : GLSymplectic n ℝ} (γ : Path A B)
    {θ : n → I → ℝ} (hθ : ∀ j, Continuous (θ j))
    (hγ : ∀ t, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (diagonal fun j => Complex.exp (θ j t * Complex.I)).realify)
    (h0 : ∀ j, θ j 0 = 0) (h1 : ∀ j, θ j 1 ∈ Set.Ioo (-(2 * Real.pi)) 0) :
    conleyZehnderIndex γ = Fintype.card n := by
  have key (j : n) : (((⌊θ j 1 / (2 * Real.pi)⌋ + ⌈θ j 1 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2 -
      ((⌊θ j 0 / (2 * Real.pi)⌋ + ⌈θ j 0 / (2 * Real.pi)⌉ : ℤ) : ℝ) / 2) = -(1 / 2) := by
    have hπ : 0 < 2 * Real.pi := by positivity
    have hlo : -1 < θ j 1 / (2 * Real.pi) := by
      rw [lt_div_iff₀ hπ]; linarith [(h1 j).1]
    have hhi : θ j 1 / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (h1 j).2 hπ
    rw [h0 j, zero_div, Int.floor_zero, Int.ceil_zero,
      (Int.floor_eq_iff (z := -1)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩,
      (Int.ceil_eq_iff (z := 0)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩]
    norm_num
  rw [conleyZehnderIndex_eq_sum_of_diagonal γ hθ hγ, Finset.sum_congr rfl fun j _ => key j]
  simp
  ring

/-! ### Loops -/

/-- The square of the determinant of the unitary frame of the graph is the graph phase
`det F / conj (det F)` of the graph frame `F`. -/
private theorem detCircle_graphUnitary_sq (A : GLSymplectic n ℝ) :
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
