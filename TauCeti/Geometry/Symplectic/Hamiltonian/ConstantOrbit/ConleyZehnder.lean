/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Normalization
public import TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit
public import TauCeti.LinearAlgebra.Matrix.Signature
import TauCeti.Algebra.Lie.Symplectic.Basic
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic

/-!
# The Conley–Zehnder index of the constant orbits of a small Hamiltonian

Let `(V, ω)` be a symplectic vector space of dimension `2n`, `F : V → ℝ` a `C²` function and `p` a
nondegenerate critical point of `F`, with the convention `ι_{X_F} ω = dF`. For small `ε > 0` the
constant orbit at `p` is a nondegenerate one-periodic orbit of the autonomous Hamiltonian `εF`
(`TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit`), and the derivative at `p` of its
evolution from time `0` to time `t` is `exp (t ε dX_F(p))`
(`TauCeti.SymplecticForm.fderiv_timeDependentHamiltonianFlow_const_mul`). This file computes the
Conley–Zehnder index (`TauCeti.GLSymplectic.conleyZehnderIndex`) of this linearized flow, read as a
path of symplectic matrices in a basis `b` of `V` indexed by `n ⊕ n`. When `ω` has matrix `-J` in
`b` (the coordinates of `ℂⁿ`), for small `ε > 0` it is `n - ind_p(F)`, where `ind_p(F)` is the
Morse index (`TauCeti.morseIndex`); when `ω` has matrix `J` in `b` it is `ind_p(F) - n`. The former
is the grading of the generators of the Floer complex of a `C²`-small Morse Hamiltonian, through
which capped Hamiltonian Floer theory with `μ = -CZ` grades the critical point `p`, capped by the
constant disc, in degree `μ = ind_p(F) - n`.

The computation has three steps.

* **The linearized vector field.** Contracting `dX_F(p)` with `ω` gives the Hessian,
  `ω(dX_F(p) u, v) = d²F(p)(u, v)`. In matrices, if `G` is the matrix of `ω` and `S` the matrix of
  the Hessian in the basis `b`, the matrix `M` of `dX_F(p)` satisfies `Mᵀ G = S`
  (`TauCeti.SymplecticForm.transpose_toMatrix_fderiv_hamiltonianVectorField_mul`). Since `ω` is
  antisymmetric and the Hessian symmetric, `G M = -S`
  (`TauCeti.SymplecticForm.toMatrix_mul_toMatrix_fderiv_hamiltonianVectorField`), so `M = J S` when
  `G = J` and `M = J (-S)` when `G = -J`.
* **The linearized flow.** Hence the matrix of `exp (t ε dX_F(p))` is `exp (t ε M)`
  (`TauCeti.SymplecticForm.toMatrix_fderiv_timeDependentHamiltonianFlow_const_mul`). When `G` is
  `±J` this is `exp (t J T)` with `T = ±ε S` symmetric and nondegenerate, and the normalization of
  the Conley–Zehnder index on such paths
  (`TauCeti.GLSymplectic.eventually_conleyZehnderIndex_eq_neg_signature_div_two`) gives
  `CZ = -signature (T) / 2` for small `ε`.
* **The Morse index.** The signature of the Hessian matrix is `2n - 2 ind_p(F)`
  (`TauCeti.IsNondegenerateCriticalPoint.signature_toMatrix_toBilinForm_fderiv_fderiv`), since the
  positive and negative indices of a nondegenerate Hessian add up to the dimension.

The sign of the index depends on the orientation of the basis. In a basis with
`ω (b (inl i)) (b (inr j)) = δᵢⱼ`, that is, in which `ω` has matrix `-J` for Mathlib's `Matrix.J`,
the coordinates `(b (inl i), b (inr i))` are the real and imaginary parts of `ℂⁿ`, with `ω` the
imaginary part of the Hermitian product and `J` the multiplication by `i`. There the index is
`n - ind_p(F)` for small `ε`
(`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`). For example, on
`ℂ` the counterclockwise rotations `exp (t J θ)`, `θ > 0` small, are the flow of the maximum
`-θ |z|² / 2`, and have index `-1 = 1 - 2`, as in
`TauCeti.GLSymplectic.conleyZehnderIndex_map_ofUnitary_eq_neg_sum_sign_of_rotation`; the clockwise
ones are the flow of the minimum `θ |z|² / 2` and have index `1 = 1 - 0`. In a basis in which `ω`
has matrix `J`, such as `TauCeti.stdSymplecticBasis`, the same computation gives `ind_p(F) - n`
(`TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_morseIndex_sub_card`). The smallness of
`ε` is needed: for `F = π |z|²` and `ε = 1` the time-one map is the identity.

The paths are the actual matrices of the derivatives of the global Hamiltonian evolution, which
form a path of symplectic matrices for every `ε`
(`TauCeti.SymplecticForm.exists_path_toMatrix_fderiv_timeDependentHamiltonianFlow`). The target is
a symplectic vector space, the local model at a critical point of a symplectic manifold.

## Main results

* `TauCeti.SymplecticForm.transpose_toMatrix_fderiv_hamiltonianVectorField_mul`: the matrix of
  `dX_F(p)` contracted with the matrix of `ω` is the Hessian matrix.
* `TauCeti.SymplecticForm.toMatrix_mul_toMatrix_fderiv_hamiltonianVectorField`: the matrix of `ω`
  times the matrix of `dX_F(p)` is minus the Hessian matrix.
* `TauCeti.SymplecticForm.toMatrix_fderiv_hamiltonianVectorField_eq_J_mul` and
  `TauCeti.SymplecticForm.toMatrix_fderiv_hamiltonianVectorField_eq_J_mul_neg`: in a basis in which
  `ω` has matrix `±J`, this matrix is `±J S`.
* `TauCeti.SymplecticForm.toMatrix_fderiv_timeDependentHamiltonianFlow_const_mul`: the matrix of
  the linearized evolution of `εF` at a critical point is a matrix exponential.
* `TauCeti.SymplecticForm.exists_path_toMatrix_fderiv_timeDependentHamiltonianFlow`: these matrices
  form a path of symplectic matrices.
* `TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`: for small
  `ε > 0`, its Conley–Zehnder index is `n - ind_p(F)` in a basis in which `ω` has matrix `-J`.
* `TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_morseIndex_sub_card`: it is
  `ind_p(F) - n` in a basis in which `ω` has matrix `J`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the normalization of the Conley–Zehnder index and the grading of
  the Floer complex of a small Morse function).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844.
-/

public section

open Filter Matrix NormedSpace Topology unitInterval
open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {F : V → ℝ} {p : V}

/-! ### Matrices of the linearized Hamiltonian vector field and flow -/

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The matrix of the linearized Hamiltonian vector field.** In a basis `b`, the transpose of the
matrix of `dX_F(p)` times the matrix of `ω` is the matrix of the Hessian of `F` at `p`: this is the
identity `ω(dX_F(p) u, v) = d²F(p)(u, v)` in coordinates. -/
theorem transpose_toMatrix_fderiv_hamiltonianVectorField_mul (b : Module.Basis ι ℝ V)
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) :
    (LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p))ᵀ *
        LinearMap.BilinForm.toMatrix b ω.toBilinForm =
      LinearMap.BilinForm.toMatrix b (fderiv ℝ (fderiv ℝ F) p).toBilinForm := by
  rw [← LinearMap.BilinForm.toMatrix_compLeft]
  congr 1
  ext u v
  exact ω.apply_fderiv_hamiltonianVectorField hF u v

/-- **The matrix of the linearized Hamiltonian vector field, contracted on the left.** In a basis
`b`, the matrix of `ω` times the matrix of `dX_F(p)` is minus the matrix of the Hessian of `F` at
`p`, since `ω` is antisymmetric and the Hessian is symmetric. -/
theorem toMatrix_mul_toMatrix_fderiv_hamiltonianVectorField (b : Module.Basis ι ℝ V)
    (hF : ContDiffAt ℝ 2 F p) :
    LinearMap.BilinForm.toMatrix b ω.toBilinForm *
        LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p) =
      -LinearMap.BilinForm.toMatrix b (fderiv ℝ (fderiv ℝ F) p).toBilinForm := by
  have hω : (LinearMap.BilinForm.toMatrix b ω.toBilinForm)ᵀ =
      -LinearMap.BilinForm.toMatrix b ω.toBilinForm := by
    ext i j
    simpa [LinearMap.BilinForm.toMatrix_apply] using (ω.isAlt.neg_eq (b i) (b j)).symm
  -- Transposing `Mᵀ G = S` gives `Gᵀ M = Sᵀ`, that is `-(G M) = S`.
  have h := congrArg transpose (ω.transpose_toMatrix_fderiv_hamiltonianVectorField_mul b
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero))
  rw [transpose_mul, transpose_transpose, hω,
    (isHermitian_toMatrix_toBilinForm_fderiv_fderiv b hF).isSymm.eq] at h
  rw [← h, Matrix.neg_mul, neg_neg]

/-- **The matrix of the linearized evolution at a critical point.** If `p` is a critical point of a
`C²` function `F`, the matrix in a basis `b` of the derivative at `p` of the Hamiltonian evolution
of `εF` from time `s` to time `t` is the exponential of `(t - s) ε` times the matrix of
`dX_F(p)`. -/
theorem toMatrix_fderiv_timeDependentHamiltonianFlow_const_mul (b : Module.Basis ι ℝ V)
    (hF : ContDiff ℝ 2 F) (hp : fderiv ℝ F p = 0) (ε : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) (s t : ℝ) :
    LinearMap.toMatrix b b
        (fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX s t) p) =
      exp (((t - s) * ε) • LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p)) := by
  rw [ω.fderiv_timeDependentHamiltonianFlow_const_mul hF hp ε hX s t,
    ContinuousLinearMap.toMatrix_exp, ContinuousLinearMap.toLinearMap_smul, LinearEquiv.map_smul]

end Matrices

section SymplecticBasis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Bases in which `ω` has matrix `±J` -/

/-- **The matrix of the linearized Hamiltonian vector field in a symplectic basis.** In a basis
`b` in which `ω` has matrix `J`, the matrix of `dX_F(p)` is `J S`, for the matrix `S` of the
Hessian of `F` at `p`. The point `p` need not be critical. -/
theorem toMatrix_fderiv_hamiltonianVectorField_eq_J_mul (b : Module.Basis (n ⊕ n) ℝ V)
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J n ℝ) (hF : ContDiffAt ℝ 2 F p) :
    LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p) =
      J n ℝ * LinearMap.BilinForm.toMatrix b (fderiv ℝ (fderiv ℝ F) p).toBilinForm := by
  have h := ω.toMatrix_mul_toMatrix_fderiv_hamiltonianVectorField b hF
  rw [hb] at h
  set M := LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p)
  -- `J M = -S`, so `M = -J (J M) = J S`.
  calc M = -J n ℝ * (J n ℝ * M) := by rw [← Matrix.mul_assoc, neg_J_mul_J, Matrix.one_mul]
    _ = _ := by rw [h, neg_mul_neg]

/-- **The matrix of the linearized Hamiltonian vector field in a complex basis.** In a basis `b` in
which `ω` has matrix `-J`, the matrix of `dX_F(p)` is `J (-S)`, for the matrix `S` of the Hessian
of `F` at `p`. The point `p` need not be critical. -/
theorem toMatrix_fderiv_hamiltonianVectorField_eq_J_mul_neg (b : Module.Basis (n ⊕ n) ℝ V)
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = -J n ℝ) (hF : ContDiffAt ℝ 2 F p) :
    LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p) =
      J n ℝ * -LinearMap.BilinForm.toMatrix b (fderiv ℝ (fderiv ℝ F) p).toBilinForm := by
  have h := ω.toMatrix_mul_toMatrix_fderiv_hamiltonianVectorField b hF
  rw [hb] at h
  set M := LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p)
  -- `-J M = -S`, so `M = J (-J M) = J (-S)`.
  calc M = J n ℝ * (-J n ℝ * M) := by rw [← Matrix.mul_assoc, J_mul_neg_J, Matrix.one_mul]
    _ = _ := by rw [h]

/-- In a basis in which `ω` has matrix `±J`, the matrix of `dX_F(p)` is `J T` for a symmetric
`T`. -/
private theorem exists_isHermitian_toMatrix_fderiv_hamiltonianVectorField_eq
    (b : Module.Basis (n ⊕ n) ℝ V)
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J n ℝ ∨
      LinearMap.BilinForm.toMatrix b ω.toBilinForm = -J n ℝ) (hF : ContDiffAt ℝ 2 F p) :
    ∃ T : Matrix (n ⊕ n) (n ⊕ n) ℝ, T.IsHermitian ∧
      LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p) = J n ℝ * T := by
  rcases hb with hb | hb
  · exact ⟨_, isHermitian_toMatrix_toBilinForm_fderiv_fderiv b hF,
      ω.toMatrix_fderiv_hamiltonianVectorField_eq_J_mul b hb hF⟩
  · exact ⟨_, (isHermitian_toMatrix_toBilinForm_fderiv_fderiv b hF).neg,
      ω.toMatrix_fderiv_hamiltonianVectorField_eq_J_mul_neg b hb hF⟩

/-! ### The path of linearized evolutions -/

/-- The linearized evolution of `εF` at a critical point, in a basis in which the matrix of
`dX_F(p)` is `J T` for a symmetric `T`, is `exp (t (J (ε T)))`. -/
private theorem toMatrix_fderiv_timeDependentHamiltonianFlow_eq_exp (b : Module.Basis (n ⊕ n) ℝ V)
    {T : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hM : LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p) = J n ℝ * T)
    (hF : ContDiff ℝ 2 F) (hp : fderiv ℝ F p = 0) (ε : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) (t : ℝ) :
    LinearMap.toMatrix b b
        (fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX 0 t) p) =
      exp (t • (J n ℝ * (ε • T))) := by
  rw [ω.toMatrix_fderiv_timeDependentHamiltonianFlow_const_mul b hF hp ε hX 0 t, hM, sub_zero,
    Matrix.mul_smul, smul_smul]

open scoped Matrix.Norms.L2Operator in
/-- **The linearized evolution is a path of symplectic matrices.** If, in a basis `b` of `V`
indexed by `n ⊕ n`, the matrix of `ω` is `J` or `-J`, then for every critical point `p` of a `C²`
function `F` and every `ε`, the matrices in `b` of the derivatives at `p` of the Hamiltonian
evolution of `εF` from time `0` to the times `t ∈ [0, 1]` form a path of symplectic matrices
starting at the identity. -/
theorem exists_path_toMatrix_fderiv_timeDependentHamiltonianFlow (b : Module.Basis (n ⊕ n) ℝ V)
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J n ℝ ∨
      LinearMap.BilinForm.toMatrix b ω.toBilinForm = -J n ℝ)
    (hF : ContDiff ℝ 2 F) (hp : fderiv ℝ F p = 0) (ε : ℝ) {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y)) :
    ∃ (B : GLSymplectic n ℝ) (γ : Path (1 : GLSymplectic n ℝ) B), ∀ t : I,
      ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        LinearMap.toMatrix b b
          (fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX 0 t) p) := by
  obtain ⟨T, hT, hM⟩ :=
    ω.exists_isHermitian_toMatrix_fderiv_hamiltonianVectorField_eq b hb (hF.contDiffAt (x := p))
  let +nondep : NormedAlgebra ℚ (Matrix (n ⊕ n) (n ⊕ n) ℝ) := .restrictScalars ℚ ℝ _
  set K' := J n ℝ * (ε • T)
  have hmem (t : ℝ) : expUnit (t • K') ∈ GLSymplectic n ℝ := by
    rw [GLSymplectic.mem_iff_mem_symplecticGroup, expUnit_coe]
    exact (forall_exp_smul_mem_symplecticGroup_iff_mem_sp K').2
      (LieAlgebra.Symplectic.J_mul_mem_sp (hT.smul (IsSelfAdjoint.all ε)).isSymm) t
  let γ : Path (1 : GLSymplectic n ℝ) ⟨expUnit K', by simpa using hmem 1⟩ :=
    { toFun := fun t ↦ ⟨expUnit ((t : ℝ) • K'), hmem t⟩
      continuous_toFun := (continuous_expUnit.comp
        (continuous_subtypeVal.smul continuous_const)).subtype_mk _
      source' := by ext : 2; simp
      target' := by ext : 2; simp }
  exact ⟨_, γ, fun t ↦ by
    simp [γ, ω.toMatrix_fderiv_timeDependentHamiltonianFlow_eq_exp b hM hF hp ε hX t, K']⟩

/-! ### The Conley–Zehnder index -/

/-- **The index from the normalization.** If the matrix of `dX_F(p)` in `b` is `J T` for a
nondegenerate symmetric `T`, then for small `ε > 0` the path of linearized evolutions of `εF` has
Conley–Zehnder index `-signature (T) / 2`. -/
private theorem eventually_conleyZehnderIndex_eq_neg_signature_div_two
    (b : Module.Basis (n ⊕ n) ℝ V) {T : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hT : T.IsHermitian)
    (hTdet : IsUnit T.det)
    (hM : LinearMap.toMatrix b b (fderiv ℝ (ω.hamiltonianVectorField F) p) = J n ℝ * T)
    (hF : ContDiff ℝ 2 F) (hp : fderiv ℝ F p = 0) :
    ∀ᶠ ε in 𝓝[>] 0, ∀ {K : ℝ≥0}
      (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y))
      {A B : GLSymplectic n ℝ} (γ : Path A B),
      (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        LinearMap.toMatrix b b
          (fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX 0 t) p)) →
      GLSymplectic.conleyZehnderIndex γ = -(signature T : ℝ) / 2 := by
  have ht : Tendsto (fun ε : ℝ ↦ ε • T) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.smul_const T).mono_left nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ ↦ ε • T) (𝓝[>] 0) (𝓝 ((0 : ℝ) • T)))
  filter_upwards [ht.eventually (GLSymplectic.eventually_conleyZehnderIndex_eq_neg_signature_div_two
    (n := n)), self_mem_nhdsWithin] with ε hε hε0 K hX A B γ hγ
  rw [hε (hT.smul (IsSelfAdjoint.all ε))
      (by rw [det_smul]; exact ((IsUnit.mk0 ε (ne_of_gt hε0)).pow _).mul hTdet) γ
      fun t ↦ by rw [hγ t, ω.toMatrix_fderiv_timeDependentHamiltonianFlow_eq_exp b hM hF hp ε hX],
    signature_smul_of_pos hε0]

variable (b : Module.Basis (n ⊕ n) ℝ V)

/-- **The Conley–Zehnder index of the constant orbits of a small Hamiltonian.** Let `b` be a
basis of `V` indexed by `n ⊕ n` with `ω (b (inl i)) (b (inr j)) = δᵢⱼ`, that is, in which `ω` has
matrix `-J`, and let `p` be a nondegenerate critical point of a `C²` function `F`. For every small
`ε > 0`, the path `t ↦ dφ_{0,t}(p)`, `t ∈ [0, 1]`, of the matrices in `b` of the derivatives of the
Hamiltonian evolution of `εF` has Conley–Zehnder index `n - ind_p(F)`. Such paths exist by
`TauCeti.SymplecticForm.exists_path_toMatrix_fderiv_timeDependentHamiltonianFlow`. -/
theorem eventually_conleyZehnderIndex_eq_card_sub_morseIndex
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = -J n ℝ) (hF : ContDiff ℝ 2 F)
    (hp : IsNondegenerateCriticalPoint F p) :
    ∀ᶠ ε in 𝓝[>] 0, ∀ {K : ℝ≥0}
      (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y))
      {A B : GLSymplectic n ℝ} (γ : Path A B),
      (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        LinearMap.toMatrix b b
          (fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX 0 t) p)) →
      GLSymplectic.conleyZehnderIndex γ = Fintype.card n - morseIndex F p := by
  filter_upwards [ω.eventually_conleyZehnderIndex_eq_neg_signature_div_two b
    (isHermitian_toMatrix_toBilinForm_fderiv_fderiv b hp.contDiffAt).neg
    (by
      rw [det_neg]
      exact ((isUnit_neg_one (α := ℝ)).pow _).mul
        (hp.isUnit_det_toMatrix_toBilinForm_fderiv_fderiv b))
    (ω.toMatrix_fderiv_hamiltonianVectorField_eq_J_mul_neg b hb hp.contDiffAt) hF
    hp.fderiv_eq_zero] with ε hε K hX A B γ hγ
  rw [hε hX γ hγ, signature_neg, hp.signature_toMatrix_toBilinForm_fderiv_fderiv b,
    Module.finrank_eq_card_basis b, Fintype.card_sum]
  push_cast
  ring

/-- **The Conley–Zehnder index in the opposite orientation.** In a basis `b` in which `ω` has
matrix `J`, as for `TauCeti.stdSymplecticBasis`, the path of the linearized evolutions of `εF` at a
nondegenerate critical point `p` has Conley–Zehnder index `ind_p(F) - n` for every small `ε > 0`:
the opposite of `TauCeti.SymplecticForm.eventually_conleyZehnderIndex_eq_card_sub_morseIndex`, since
this change of orientation is antisymplectic. -/
theorem eventually_conleyZehnderIndex_eq_morseIndex_sub_card
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J n ℝ) (hF : ContDiff ℝ 2 F)
    (hp : IsNondegenerateCriticalPoint F p) :
    ∀ᶠ ε in 𝓝[>] 0, ∀ {K : ℝ≥0}
      (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension fun _ y ↦ ε * F y))
      {A B : GLSymplectic n ℝ} (γ : Path A B),
      (∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
        LinearMap.toMatrix b b
          (fderiv ℝ (ω.timeDependentHamiltonianFlow (fun _ y ↦ ε * F y) hX 0 t) p)) →
      GLSymplectic.conleyZehnderIndex γ = morseIndex F p - Fintype.card n := by
  filter_upwards [ω.eventually_conleyZehnderIndex_eq_neg_signature_div_two b
    (isHermitian_toMatrix_toBilinForm_fderiv_fderiv b hp.contDiffAt)
    (hp.isUnit_det_toMatrix_toBilinForm_fderiv_fderiv b)
    (ω.toMatrix_fderiv_hamiltonianVectorField_eq_J_mul b hb hp.contDiffAt) hF
    hp.fderiv_eq_zero] with ε hε K hX A B γ hγ
  rw [hε hX γ hγ, hp.signature_toMatrix_toBilinForm_fderiv_fderiv b,
    Module.finrank_eq_card_basis b, Fintype.card_sum]
  push_cast
  ring

end SymplecticBasis

end TauCeti.SymplecticForm
