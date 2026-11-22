/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Lagrange
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Mostow's lemma on positive conjugations

Let `X` be a Hermitian matrix over `𝕜 = ℝ` or `ℂ` and let `W` be a real subspace of the square
matrices. If conjugation by the positive definite matrix `exp X` maps `W` into itself, then so does
the commutator with `X`:

`Y ∈ W → X * Y - Y * X ∈ W`.

In a unitary eigenbasis of `X`, with eigenvalues `d i`, conjugation by `exp X` multiplies the
entry `(i, j)` by `exp (d i - d j)` and the commutator with `X` multiplies it by `d i - d j`. As
the exponential is injective on the finitely many differences, Lagrange interpolation gives a real
polynomial `q` with `q (exp (d i - d j)) = d i - d j`, so the commutator is `q` evaluated at the
conjugation and preserves every subspace that the conjugation preserves. Since the commutator
with `X` is the derivative at `t = 0` of conjugation by `exp (t X)`, this is the step of
G. D. Mostow's argument that passes from the single positive element `exp X` of a group to the
whole line through it.

## Main results

* `Matrix.IsHermitian.commutator_mem_of_exp_mul_mul_exp_neg_mem`: Mostow's lemma.

## References

* G. D. Mostow, *Self-adjoint groups*, Annals of Mathematics (2) 62 (1955), 44–55, Lemma 1.
* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Lemma 1.142.
-/

public section

noncomputable section

open NormedSpace

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise multiplication by a real matrix of weights, as a real algebra homomorphism from the
weights to the real linear endomorphisms of `Matrix n n 𝕜`. -/
private def weightEnd : (n → n → ℝ) →ₐ[ℝ] Module.End ℝ (Matrix n n 𝕜) where
  toFun r :=
    { toFun Y := of fun i j ↦ (r i j : 𝕜) * Y i j
      map_add' Y Z := by ext i j; simp [mul_add]
      map_smul' c Y := by ext i j; simp [RCLike.real_smul_eq_coe_mul]; ring }
  map_one' := by ext Y i j; simp
  map_mul' r s := by ext Y i j; simp [mul_assoc]
  map_zero' := by ext Y i j; simp
  map_add' r s := by ext Y i j; simp [add_mul]
  commutes' c := by ext Y i j; simp [RCLike.real_smul_eq_coe_mul]

omit [Fintype n] [DecidableEq n] in
private theorem weightEnd_apply (r : n → n → ℝ) (Y : Matrix n n 𝕜) :
    weightEnd (𝕜 := 𝕜) r Y = of fun i j ↦ (r i j : 𝕜) * Y i j :=
  (rfl)

/-- A polynomial in an endomorphism maps every subspace that the endomorphism maps into itself
into itself. -/
private theorem aeval_apply_mem {M : Type*} [AddCommGroup M] [Module ℝ M] {W : Submodule ℝ M}
    {f : Module.End ℝ M} (hf : ∀ y ∈ W, f y ∈ W) (q : Polynomial ℝ) {y : M} (hy : y ∈ W) :
    Polynomial.aeval f q y ∈ W := by
  have hpow (k : ℕ) : (f ^ k) y ∈ W := by
    induction k with
    | zero => simpa using hy
    | succ k ih => rw [pow_succ']; exact hf _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  exact W.sum_mem fun k _ ↦ W.smul_mem _ (hpow k)

omit [Fintype n] [DecidableEq n] in
/-- **Mostow's lemma in a diagonal basis.** If multiplying the entry `(i, j)` by
`exp (d i - d j)` maps a real subspace of matrices into itself, so does multiplying it by
`d i - d j`. -/
theorem sub_mul_mem_of_exp_sub_mul_mem [Finite n] (d : n → ℝ) {W : Submodule ℝ (Matrix n n 𝕜)}
    (hW : ∀ Y ∈ W, (of fun i j ↦ (Real.exp (d i - d j) : 𝕜) * Y i j) ∈ W) {Y : Matrix n n 𝕜}
    (hY : Y ∈ W) : (of fun i j ↦ ((d i - d j : ℝ) : 𝕜) * Y i j) ∈ W := by
  classical
  have := Fintype.ofFinite n
  let r : n → n → ℝ := fun i j ↦ Real.exp (d i - d j)
  let s : Finset ℝ := Finset.univ.image fun p : n × n ↦ r p.1 p.2
  let q : Polynomial ℝ := Lagrange.interpolate s id Real.log
  have hq : Polynomial.aeval r q = fun i j ↦ d i - d j := by
    ext i j
    rw [Polynomial.aeval_pi_apply₂, Polynomial.aeval_pi_apply₂, Polynomial.coe_aeval_eq_eval]
    have hmem : r i j ∈ s := Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩
    exact (Lagrange.eval_interpolate_at_node (v := id) Real.log (Set.injOn_id _) hmem).trans
      (Real.log_exp _)
  have h := aeval_apply_mem (f := weightEnd (𝕜 := 𝕜) r) (fun Y hY ↦ hW Y hY) q hY
  rwa [Polynomial.aeval_algHom_apply, hq, weightEnd_apply] at h

namespace IsHermitian

/-- In a unitary eigenbasis of a Hermitian matrix `X`, the exponential of `c • X` is the diagonal
matrix of the `exp (c * d i)`, for the eigenvalues `d i` of `X`. -/
private theorem star_mul_exp_smul_mul {X : Matrix n n 𝕜} (hX : X.IsHermitian) (c : ℝ) :
    star (hX.eigenvectorUnitary : Matrix n n 𝕜) * NormedSpace.exp (c • X) *
        hX.eigenvectorUnitary =
      diagonal fun i ↦ (Real.exp (c * hX.eigenvalues i) : 𝕜) := by
  have h := exp_units_conj' (Unitary.toUnits hX.eigenvectorUnitary) (c • X)
  have hinv : ((Unitary.toUnits hX.eigenvectorUnitary)⁻¹ : (Matrix n n 𝕜)ˣ) =
      star (hX.eigenvectorUnitary : Matrix n n 𝕜) :=
    Units.inv_eq_of_mul_eq_one_left (Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.property)
  have hD := hX.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at hD
  simp only [hinv, Unitary.val_toUnits_apply, Matrix.mul_smul, Matrix.smul_mul, hD] at h
  rw [← h, ← diagonal_smul, exp_diagonal]
  congr 1
  funext i
  simp [RCLike.real_smul_eq_coe_mul, ← RCLike.exp_ofReal]

/-- **Mostow's lemma.** Let `X` be a Hermitian matrix. If conjugation by the positive definite
matrix `exp X` maps a real subspace `W` of matrices into itself, then so does the commutator
with `X`. -/
theorem commutator_mem_of_exp_mul_mul_exp_neg_mem {X : Matrix n n 𝕜} (hX : X.IsHermitian)
    {W : Submodule ℝ (Matrix n n 𝕜)}
    (hW : ∀ Y ∈ W, NormedSpace.exp X * Y * NormedSpace.exp (-X) ∈ W)
    {Y : Matrix n n 𝕜} (hY : Y ∈ W) : X * Y - Y * X ∈ W := by
  -- Pass to a unitary eigenbasis of `X`, where `X` is the real diagonal matrix of the `d i`.
  set U := hX.eigenvectorUnitary
  set d := hX.eigenvalues
  let φ := Unitary.conjStarAlgAut ℝ (Matrix n n 𝕜) (star U)
  let e := φ.toAlgEquiv.toLinearEquiv
  have he (Z : Matrix n n 𝕜) : e Z = star (U : Matrix n n 𝕜) * Z * U := by
    simp [e, φ, Unitary.conjStarAlgAut_apply]
  have he_mul (Z Z' : Matrix n n 𝕜) : e (Z * Z') = e Z * e Z' := map_mul φ Z Z'
  have hD : e X = diagonal fun i ↦ (d i : 𝕜) := by
    have h := hX.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
    rw [he]
    exact h
  -- The transported subspace is preserved by the transported conjugation.
  have hW' : ∀ Z ∈ W.map (e : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜),
      (of fun i j ↦ (Real.exp (d i - d j) : 𝕜) * Z i j) ∈
        W.map (e : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜) := by
    intro Z hZ
    obtain ⟨Z₀, hZ₀, rfl⟩ := Submodule.mem_map.1 hZ
    refine Submodule.mem_map.2 ⟨_, hW Z₀ hZ₀, ?_⟩
    have h1 := star_mul_exp_smul_mul hX 1
    have h2 := star_mul_exp_smul_mul hX (-1)
    simp only [one_smul, one_mul, neg_smul, neg_mul] at h1 h2
    simp only [LinearEquiv.coe_coe]
    rw [he_mul, he_mul, he, he (NormedSpace.exp (-X)), h1, h2]
    ext i j
    simp [diagonal_mul, mul_diagonal, d, Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
    ring
  have h := sub_mul_mem_of_exp_sub_mul_mem d hW' (Submodule.mem_map_of_mem hY)
  rw [Submodule.mem_map_equiv] at h
  convert h using 1
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, map_sub, he_mul, he_mul, hD]
  ext i j
  simp [diagonal_mul, mul_diagonal, sub_mul, RCLike.algebraMap_eq_ofReal, mul_comm]

end IsHermitian

end Matrix
