/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.Quaternion.ComplexMatrix
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Complex representations of the real quaternions

An `ℝ`-algebra homomorphism `ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S` gives `ψ q` complex trace
`q.re * finrank ℂ S` (`TauCeti.trace_quaternionAlgHom`), and on any two-dimensional complex inner
product space where `ψ` intertwines `star` with `LinearMap.adjoint`, `S` admits an orthonormal basis
in which `ψ` has matrix `Quaternion.toComplexMatrix`
(`TauCeti.exists_orthonormalBasis_toMatrix_eq_toComplexMatrix`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 8.
-/

public section

noncomputable section

namespace TauCeti

open Module Module.End
open scoped InnerProductSpace Matrix Quaternion

/-- An `ℝ`-algebra action of `ℍ[ℝ]` on a complex module commutes with real scalar multiplication via
the canonical coercion `ℝ → ℂ`. -/
theorem quaternionAlgHom_map_smul {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) (r : ℝ) (q : ℍ[ℝ]) :
    ψ (r • q) = ((r : ℝ) : ℂ) • ψ q := by
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul, ← Complex.coe_smul]

/-- On any complex module `S`, the complex trace of `ψ q` is `q.re * finrank ℂ S`, since the
imaginary quaternion units are commutators in `ℍ[ℝ]`. -/
theorem trace_quaternionAlgHom {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) (q : ℍ[ℝ]) :
    LinearMap.trace ℂ S (ψ q) = (q.re : ℂ) * finrank ℂ S := by
  by_cases hfin : FiniteDimensional ℂ S
  swap
  · rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin, LinearMap.zero_apply,
      Module.finrank_of_not_finite hfin, Nat.cast_zero, mul_zero]
  have h0 {a b c : ℍ[ℝ]} (h : c = (2⁻¹ : ℝ) • (a * b - b * a)) :
      LinearMap.trace ℂ S (ψ c) = 0 := by
    rw [h, quaternionAlgHom_map_smul, map_smul, map_sub, map_mul, map_mul, map_sub,
      LinearMap.trace_mul_comm, sub_self, smul_zero]
  have hi := h0 (a := ⟨0, 0, 1, 0⟩) (b := ⟨0, 0, 0, 1⟩) (c := ⟨0, 1, 0, 0⟩) (by ext <;> norm_num)
  have hj := h0 (a := ⟨0, 0, 0, 1⟩) (b := ⟨0, 1, 0, 0⟩) (c := ⟨0, 0, 1, 0⟩) (by ext <;> norm_num)
  have hk := h0 (a := ⟨0, 1, 0, 0⟩) (b := ⟨0, 0, 1, 0⟩) (c := ⟨0, 0, 0, 1⟩) (by ext <;> norm_num)
  have hdecomp : q = algebraMap ℝ ℍ[ℝ] q.re + q.imI • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) +
      q.imJ • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) + q.imK • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by ext <;> simp
  conv_lhs => rw [hdecomp]
  simp only [map_add, Algebra.algebraMap_eq_smul_one, quaternionAlgHom_map_smul]
  simp [hi, hj, hk]

/-- Every nontrivial finite-dimensional complex normed space carrying an `ℝ`-algebra action of
`ℍ[ℝ]` admits a unit eigenvector of `ψ ⟨0, 1, 0, 0⟩` with eigenvalue `Complex.I`. -/
theorem exists_unit_eigenvector_quaternionAlgHom_i
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S] [Nontrivial S]
    (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) :
    ∃ e₀ : S, ‖e₀‖ = 1 ∧ ψ ⟨0, 1, 0, 0⟩ e₀ = Complex.I • e₀ := by
  let A : Module.End ℂ S := (-Complex.I) • ψ ⟨0, 1, 0, 0⟩
  have hA_inv (x : S) : A (A x) = x := by
    have hmul : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ = -1 := by ext <;> simp
    exact LinearMap.congr_fun (by simp [A, ← map_mul, hmul, smul_smul] : A * A = 1) x
  have hcompl := isCompl_eigenspace_one_neg_one (two_ne_zero : (2 : ℂ) ≠ 0).isUnit hA_inv
  have hne : eigenspace A 1 ≠ ⊥ := fun hbot ↦ by
    have htop : eigenspace A (-1) = ⊤ := by simpa [hbot] using hcompl.sup_eq_top
    have hA_neg : A = -1 := LinearMap.ext fun x ↦ by
      simpa [mem_eigenspace_iff] using (htop ▸ Submodule.mem_top : x ∈ eigenspace A (-1))
    have htr₀ : LinearMap.trace ℂ S A = 0 := by simp [A, trace_quaternionAlgHom]
    rw [hA_neg, map_neg, LinearMap.trace_one] at htr₀
    exact Module.finrank_pos.ne' (Nat.cast_eq_zero.mp (neg_eq_zero.mp htr₀))
  have : Nontrivial (eigenspace A 1) := Submodule.nontrivial_iff_ne_bot.mpr hne
  let := NormedSpace.restrictScalars ℝ ℂ (eigenspace A 1)
  obtain ⟨u, hu⟩ := exists_norm_eq (eigenspace A 1) zero_le_one
  have huA : (-Complex.I) • ψ ⟨0, 1, 0, 0⟩ u = (u : S) := by
    simpa [A, mem_eigenspace_iff] using u.property
  refine ⟨u, by simpa using hu, ?_⟩
  calc ψ ⟨0, 1, 0, 0⟩ u = Complex.I • ((-Complex.I) • ψ ⟨0, 1, 0, 0⟩ u) := by simp [smul_smul]
    _ = Complex.I • (u : S) := by rw [huA]

/-- For a `star`-compatible complex representation `ψ` of `ℍ[ℝ]`, a unit `+i`-eigenvector `e₀` of
`ψ ⟨0, 1, 0, 0⟩` and `-(ψ ⟨0, 0, 1, 0⟩ e₀)` form an orthonormal pair on which `i` and `j` act by
standard `SU(2)` columns. -/
theorem orthonormal_pair_of_quaternionAlgHom
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) (hstar : ∀ q, LinearMap.adjoint (ψ q) = ψ (star q))
    {e₀ : S} (he₀_norm : ‖e₀‖ = 1) (he₀_i : ψ ⟨0, 1, 0, 0⟩ e₀ = Complex.I • e₀) :
    Orthonormal ℂ ![e₀, -(ψ ⟨0, 0, 1, 0⟩ e₀)] ∧
      ψ ⟨0, 1, 0, 0⟩ (-(ψ ⟨0, 0, 1, 0⟩ e₀)) = -Complex.I • -(ψ ⟨0, 0, 1, 0⟩ e₀) ∧
      ψ ⟨0, 0, 1, 0⟩ (-(ψ ⟨0, 0, 1, 0⟩ e₀)) = e₀ := by
  set e₁ : S := -(ψ ⟨0, 0, 1, 0⟩ e₀)
  have he₁_j : ψ ⟨0, 0, 1, 0⟩ e₁ = e₀ := by
    have hjj : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ = -1 := by ext <;> simp
    simp [e₁, ← mul_apply_eq_comp, ← map_mul, hjj]
  have he₁_i : ψ ⟨0, 1, 0, 0⟩ e₁ = -Complex.I • e₁ := by
    have hij : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ =
        -((⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩) := by ext <;> simp
    calc ψ ⟨0, 1, 0, 0⟩ e₁ = -((ψ ⟨0, 1, 0, 0⟩ * ψ ⟨0, 0, 1, 0⟩) e₀) := by
          simp [e₁, mul_apply_eq_comp]
      _ = (ψ ⟨0, 0, 1, 0⟩ * ψ ⟨0, 1, 0, 0⟩) e₀ := by
          rw [← map_mul, hij, map_neg, LinearMap.neg_apply, neg_neg, map_mul]
      _ = -Complex.I • e₁ := by simp [mul_apply_eq_comp, he₀_i, e₁]
  have hstar_i : star (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = -⟨0, 1, 0, 0⟩ := by ext <;> simp
  have hstar_j : star (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = -⟨0, 0, 1, 0⟩ := by ext <;> simp
  have hadj_i : LinearMap.adjoint (ψ ⟨0, 1, 0, 0⟩) = -ψ ⟨0, 1, 0, 0⟩ := by
    rw [hstar, hstar_i, map_neg]
  have hadj_j : LinearMap.adjoint (ψ ⟨0, 0, 1, 0⟩) = -ψ ⟨0, 0, 1, 0⟩ := by
    rw [hstar, hstar_j, map_neg]
  have horth : ⟪e₀, e₁⟫_ℂ = 0 := by
    have h₁ : Complex.I * ⟪e₀, e₁⟫_ℂ = -Complex.I * ⟪e₀, e₁⟫_ℂ := calc
      Complex.I * ⟪e₀, e₁⟫_ℂ = ⟪LinearMap.adjoint (ψ ⟨0, 1, 0, 0⟩) e₀, e₁⟫_ℂ := by
        rw [hadj_i, LinearMap.neg_apply, he₀_i]; simp [inner_smul_left]
      _ = -Complex.I * ⟪e₀, e₁⟫_ℂ := by rw [LinearMap.adjoint_inner_left, he₁_i, inner_smul_right]
    have h₂ : (2 * Complex.I) * ⟪e₀, e₁⟫_ℂ = 0 := by linear_combination h₁
    exact (mul_eq_zero.mp h₂).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hjj_e₀ : ψ ⟨0, 0, 1, 0⟩ (ψ ⟨0, 0, 1, 0⟩ e₀) = -e₀ := by
    rw [← neg_neg (ψ ⟨0, 0, 1, 0⟩ e₀), map_neg, he₁_j]
  have he₁_norm : ‖e₁‖ = 1 := by
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
    rw [← RCLike.ofReal_inj (K := ℂ), RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K]
    calc ⟪e₁, e₁⟫_ℂ = ⟪ψ ⟨0, 0, 1, 0⟩ e₀, ψ ⟨0, 0, 1, 0⟩ e₀⟫_ℂ := by simp [e₁]
      _ = ⟪e₀, e₀⟫_ℂ := by
        rw [← LinearMap.adjoint_inner_right, hadj_j, LinearMap.neg_apply, hjj_e₀, neg_neg]
      _ = (((1 : ℝ) ^ 2 : ℝ) : ℂ) := by simp [inner_self_eq_norm_sq_to_K, he₀_norm]
  refine ⟨orthonormal_iff_ite.mpr fun a b ↦ ?_, he₁_i, he₁_j⟩
  fin_cases a <;> fin_cases b
  · simp [inner_self_eq_norm_sq_to_K, he₀_norm]
  · simpa using horth
  · simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) horth
  · simp [inner_self_eq_norm_sq_to_K, he₁_norm]

/-- Every `star`-compatible `ℝ`-algebra action of `ℍ[ℝ]` on a two-dimensional complex inner product
space is represented in an orthonormal basis by `Quaternion.toComplexMatrix`. -/
theorem exists_orthonormalBasis_toMatrix_eq_toComplexMatrix
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    (hS : finrank ℂ S = 2) (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S)
    (hstar : ∀ q, LinearMap.adjoint (ψ q) = ψ (star q)) :
    ∃ c : OrthonormalBasis (Fin 2) ℂ S,
      ∀ q : ℍ[ℝ], LinearMap.toMatrix c.toBasis c.toBasis (ψ q) = Quaternion.toComplexMatrix q := by
  have : Nontrivial S := Module.nontrivial_of_finrank_pos (by rw [hS]; positivity)
  obtain ⟨e₀, he₀_norm, he₀_i⟩ := exists_unit_eigenvector_quaternionAlgHom_i ψ
  obtain ⟨hon, he₁_i, he₁_j⟩ := orthonormal_pair_of_quaternionAlgHom ψ hstar he₀_norm he₀_i
  let c : OrthonormalBasis (Fin 2) ℂ S :=
    (basisOfOrthonormalOfCardEqFinrank hon (by simp [hS])).toOrthonormalBasis
      (by rwa [coe_basisOfOrthonormalOfCardEqFinrank])
  have hc (i : Fin 2) : c i = ![e₀, -(ψ ⟨0, 0, 1, 0⟩ e₀)] i := by
    rw [← c.coe_toBasis, Module.Basis.toBasis_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
  have h_i₀ : ψ ⟨0, 1, 0, 0⟩ (c 0) = Complex.I • c 0 := by rw [hc 0]; exact he₀_i
  have h_i₁ : ψ ⟨0, 1, 0, 0⟩ (c 1) = (-Complex.I) • c 1 := by simpa [hc 1, neg_smul] using he₁_i
  have h_j₀ : ψ ⟨0, 0, 1, 0⟩ (c 0) = -(c 1) := by rw [hc 0, hc 1]; simp
  have h_j₁ : ψ ⟨0, 0, 1, 0⟩ (c 1) = c 0 := by rw [hc 1, hc 0]; exact he₁_j
  let Φ : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    ((LinearMap.toMatrixAlgEquiv c.toBasis).toAlgHom.restrictScalars ℝ).comp ψ
  have hΦ_i : Φ (QuaternionAlgebra.Basis.self ℝ).i =
      Quaternion.toComplexMatrix.toAlgHom (QuaternionAlgebra.Basis.self ℝ).i := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Φ, LinearMap.toMatrixAlgEquiv_apply, h_i₀, h_i₁, Quaternion.toComplexMatrix_apply]
  have hΦ_j : Φ (QuaternionAlgebra.Basis.self ℝ).j =
      Quaternion.toComplexMatrix.toAlgHom (QuaternionAlgebra.Basis.self ℝ).j := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Φ, LinearMap.toMatrixAlgEquiv_apply, h_j₀, h_j₁, Quaternion.toComplexMatrix_apply]
  have hΦ := Quaternion.hom_ext hΦ_i hΦ_j
  refine ⟨c, fun q ↦ ?_⟩
  ext i j
  simpa [Φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply] using
    congr_fun₂ (AlgHom.congr_fun hΦ q) i j

end TauCeti

end
