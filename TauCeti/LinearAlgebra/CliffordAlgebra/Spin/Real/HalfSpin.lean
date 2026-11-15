/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.TorusCharacter
import TauCeti.Algebra.Algebra.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.HalfSpinor
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Frame
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# Quaternion and `SU(2)` models of the compact four-dimensional half-spin representations

Under the compact Spin isomorphism
`TauCeti.realSpinFourEquivQuaternionUnitaryProd : Spin(4) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` and its
complex matrix form `TauCeti.realSpinFourEquivSpecialUnitaryProd : Spin(4) ≃* SU(2) × SU(2)`,
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Chirality` identifies the kernels of the half-spin
representations along a positively oriented orthonormal frame `b` of an oriented four-space `(V, o)`
with `Q v = -‖v‖²`. This file upgrades that kernel comparison to explicit algebra actions,
orthonormal half-spinor bases, characters on the full compact `Spin(4)` and `Spinᶜ(4)` groups, and
the quaternion coordinates of the coordinate-plane torus `OrthonormalBasis.spinTorus`.

Specifically, for a positively oriented orthonormal basis `b` (`hb : b.toBasis.orientation = o`):

* `CliffordAlgebra.positiveQuaternionAction` and `CliffordAlgebra.negativeQuaternionAction` factor
  the even Clifford actions on `W⁺` and `W⁻` into unital `ℝ`-algebra homomorphisms from `ℍ[ℝ]`, so
  that `halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)` is the action of the **second** unit
  quaternion `(realSpinFourEquivQuaternionUnitaryProd s).2` and
  `halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)` is the action of the **first** unit quaternion
  `(realSpinFourEquivQuaternionUnitaryProd s).1`.
* On a Hermitian Clifford module (`c(v)* = -c(v)`), both quaternion actions send quaternion
  conjugation to the Hilbert-space adjoint (`adjoint_positiveQuaternionAction`,
  `adjoint_negativeQuaternionAction`). When `dim_ℂ W⁺ = 2`, there exist orthonormal bases of `W⁺`
  and `W⁻` in which the matrices of `halfSpinRep` at `b.realSpinGroupEquiv hQ s` are literally the
  second and first `SU(2)` factors `(realSpinFourEquivSpecialUnitaryProd s).2` and
  `(realSpinFourEquivSpecialUnitaryProd s).1`
  (`exists_orthonormalBasis_toMatrix_halfSpinRep_one`,
  `exists_orthonormalBasis_toMatrix_halfSpinRep_neg_one`).
* Since the imaginary quaternion units are commutators in `ℍ[ℝ]`, every `ℝ`-algebra action of `ℍ[ℝ]`
  on a finite-dimensional complex space `S` has trace `q.re * dim_ℂ S`. This yields closed-form
  character formulas on the entire groups `Spin(4)` and `Spinᶜ(4)` in terms of the real parts of the
  unit quaternions and the traces of the two `SU(2)` matrices.
* Along `OrthonormalBasis.spinTorus`, the torus element `(w₁, w₂)` corresponds in
  `unitary ℍ[ℝ] × unitary ℍ[ℝ]` to `(re(w₁ w₂⁻¹) + im(w₁ w₂⁻¹) k, re(w₁ w₂) + im(w₁ w₂) k)`
  (`OrthonormalBasis.coe_realSpinFourEquivQuaternionUnitaryProd_symm_spinTorus`), matching the
  weights `w₁ w₂⁻¹` on `W⁻` and `w₁ w₂` on `W⁺`.
* In any dimension `n`, changing between two equally oriented orthonormal frames conjugates both
  `OrthonormalBasis.realSpinGroupEquiv` and `OrthonormalBasis.realSpinCGroupHom` by a compact Spin
  element (`OrthonormalBasis.exists_realSpinGroupEquiv_eq_conj`,
  `OrthonormalBasis.exists_realSpinCGroupHom_eq_conj`).

## Main definitions

* `CliffordAlgebra.positiveQuaternionAction o hQ b ρ hb`: the `ℝ`-algebra action of `ℍ[ℝ]` on `W⁺`
  through which the second factor of `Spin(4)` acts.
* `CliffordAlgebra.negativeQuaternionAction o hQ b ρ hb`: the `ℝ`-algebra action of `ℍ[ℝ]` on `W⁻`
  through which the first factor of `Spin(4)` acts.

## Main results

* `CliffordAlgebra.halfSpinRep_one_realSpinGroupEquiv_eq`,
  `CliffordAlgebra.halfSpinRep_neg_one_realSpinGroupEquiv_eq`: factorization of `halfSpinRep`
  through the second and first unit-quaternion factors.
* `CliffordAlgebra.adjoint_positiveQuaternionAction`,
  `CliffordAlgebra.adjoint_negativeQuaternionAction`: compatibility with `star` and `adjoint`.
* `CliffordAlgebra.exists_orthonormalBasis_toMatrix_halfSpinRep_one`,
  `CliffordAlgebra.exists_orthonormalBasis_toMatrix_halfSpinRep_neg_one`: orthonormal half-spinor
  bases realizing `SU(2)₊` (second factor) on `W⁺` and `SU(2)₋` (first factor) on `W⁻`.
* `CliffordAlgebra.trace_halfSpinRep_one_realSpinGroupEquiv_specialUnitary`,
  `CliffordAlgebra.trace_halfSpinRep_neg_one_realSpinGroupEquiv_specialUnitary`,
  `CliffordAlgebra.trace_spinCGroupHalfSpinRep_one_realSpinCGroupHom`,
  `CliffordAlgebra.trace_spinCGroupHalfSpinRep_neg_one_realSpinCGroupHom`: characters on `Spin(4)`
  and `Spinᶜ(4)`.
* `OrthonormalBasis.coe_realSpinFourEquivQuaternionUnitaryProd_symm_spinTorus`: quaternion-pair
  coordinates of `OrthonormalBasis.spinTorus`.
* `OrthonormalBasis.exists_realSpinGroupEquiv_eq_conj`,
  `OrthonormalBasis.exists_realSpinCGroupHom_eq_conj`: inner-automorphism comparison of
  `realSpinGroupEquiv` and `realSpinCGroupHom` across equally oriented orthonormal frames.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open Module Module.End CliffordAlgebra TauCeti
open scoped InnerProductSpace Matrix Quaternion

/-! ### Private helpers on complex representations of `ℍ[ℝ]` -/

section QuaternionHelpers

private theorem quaternionAlgHom_map_smul {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) (r : ℝ) (q : ℍ[ℝ]) :
    ψ (r • q) = ((r : ℝ) : ℂ) • ψ q := by
  rw [Algebra.smul_def, map_mul, AlgHom.commutes,
    IsScalarTower.algebraMap_apply ℝ ℂ (Module.End ℂ S),
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rfl

private theorem trace_quaternionAlgHom {S : Type*} [AddCommGroup S] [Module ℂ S]
    [FiniteDimensional ℂ S] (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) (q : ℍ[ℝ]) :
    LinearMap.trace ℂ S (ψ q) = (q.re : ℂ) * finrank ℂ S := by
  have hcomm (x y : ℍ[ℝ]) : LinearMap.trace ℂ S (ψ (x * y - y * x)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_sub, LinearMap.trace_mul_comm, sub_self]
  have hi : LinearMap.trace ℂ S (ψ ⟨0, 1, 0, 0⟩) = 0 := by
    have hq : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) =
        (2⁻¹ : ℝ) • ((⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 0, 1⟩ -
          (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩) := by ext <;> norm_num
    rw [hq, quaternionAlgHom_map_smul, map_smul, hcomm, smul_zero]
  have hj : LinearMap.trace ℂ S (ψ ⟨0, 0, 1, 0⟩) = 0 := by
    have hq : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) =
        (2⁻¹ : ℝ) • ((⟨0, 0, 0, 1⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ -
          (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 0, 1⟩) := by ext <;> norm_num
    rw [hq, quaternionAlgHom_map_smul, map_smul, hcomm, smul_zero]
  have hk : LinearMap.trace ℂ S (ψ ⟨0, 0, 0, 1⟩) = 0 := by
    have hq : (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) =
        (2⁻¹ : ℝ) • ((⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ -
          (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩) := by ext <;> norm_num
    rw [hq, quaternionAlgHom_map_smul, map_smul, hcomm, smul_zero]
  have hdecomp : q = algebraMap ℝ ℍ[ℝ] q.re + q.imI • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) +
      q.imJ • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) + q.imK • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
    ext <;> simp
  conv_lhs => rw [hdecomp]
  simp only [map_add, Algebra.algebraMap_eq_smul_one, quaternionAlgHom_map_smul]
  simp [hi, hj, hk]

private theorem exists_unit_eigenvector_quaternionAlgHom_i
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    (hS : finrank ℂ S = 2) (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) :
    ∃ e₀ : S, ‖e₀‖ = 1 ∧ ψ ⟨0, 1, 0, 0⟩ e₀ = Complex.I • e₀ := by
  let A : Module.End ℂ S := (-Complex.I) • ψ ⟨0, 1, 0, 0⟩
  have hA_inv (x : S) : A (A x) = x := by
    have hmul : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ = -1 := by ext <;> simp
    have hsq : A * A = 1 := by
      simp only [A, smul_mul_smul_comm, ← map_mul, hmul, map_neg, map_one]
      have hI : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by simp
      rw [hI, smul_neg, neg_one_smul, neg_neg]
    exact LinearMap.congr_fun hsq x
  have hcompl : IsCompl (eigenspace A 1) (eigenspace A (-1)) :=
    TauCeti.isCompl_eigenspace_one_neg_one (two_ne_zero : (2 : ℂ) ≠ 0).isUnit hA_inv
  have hne : eigenspace A 1 ≠ ⊥ := by
    intro hbot
    have htop : eigenspace A (-1) = ⊤ := by
      simpa [hbot] using hcompl.sup_eq_top
    have hA_neg : A = -1 := by
      ext x
      have hx : x ∈ eigenspace A (-1) := htop ▸ Submodule.mem_top
      simpa [mem_eigenspace_iff] using hx
    have htr₀ : LinearMap.trace ℂ S A = 0 := by
      simp [A, trace_quaternionAlgHom]
    rw [hA_neg, map_neg, LinearMap.trace_one, hS] at htr₀
    norm_num at htr₀
  have : Nontrivial (eigenspace A 1) := Submodule.nontrivial_iff_ne_bot.mpr hne
  let := NormedSpace.restrictScalars ℝ ℂ (eigenspace A 1)
  obtain ⟨u, hu⟩ := exists_norm_eq (eigenspace A 1) zero_le_one
  refine ⟨u, by simpa using hu, ?_⟩
  have huA : (-Complex.I) • ψ ⟨0, 1, 0, 0⟩ u = (u : S) := by
    simpa [A, mem_eigenspace_iff] using u.2
  calc
    ψ ⟨0, 1, 0, 0⟩ u = Complex.I • ((-Complex.I) • ψ ⟨0, 1, 0, 0⟩ u) := by
      rw [smul_smul]; simp
    _ = Complex.I • (u : S) := by rw [huA]

private theorem orthonormal_pair_of_quaternionAlgHom
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S) (hstar : ∀ q, LinearMap.adjoint (ψ q) = ψ (star q))
    {e₀ : S} (he₀_norm : ‖e₀‖ = 1) (he₀_i : ψ ⟨0, 1, 0, 0⟩ e₀ = Complex.I • e₀) :
    Orthonormal ℂ ![e₀, -(ψ ⟨0, 0, 1, 0⟩ e₀)] ∧
      ψ ⟨0, 1, 0, 0⟩ (-(ψ ⟨0, 0, 1, 0⟩ e₀)) = -Complex.I • -(ψ ⟨0, 0, 1, 0⟩ e₀) ∧
      ψ ⟨0, 0, 1, 0⟩ (-(ψ ⟨0, 0, 1, 0⟩ e₀)) = e₀ := by
  set e₁ : S := -(ψ ⟨0, 0, 1, 0⟩ e₀)
  have he₁_j : ψ ⟨0, 0, 1, 0⟩ e₁ = e₀ := by
    have hjj : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ = -1 := by ext <;> simp
    simp only [e₁, map_neg, ← mul_apply_eq_comp, ← map_mul, hjj, map_one, LinearMap.neg_apply,
      one_apply_eq_self, neg_neg]
  have he₁_i : ψ ⟨0, 1, 0, 0⟩ e₁ = -Complex.I • e₁ := by
    have hij : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ =
        -((⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩) := by ext <;> simp
    calc
      ψ ⟨0, 1, 0, 0⟩ e₁ = -((ψ ⟨0, 1, 0, 0⟩ * ψ ⟨0, 0, 1, 0⟩) e₀) := by
        simp [e₁, mul_apply_eq_comp]
      _ = (ψ ⟨0, 0, 1, 0⟩ * ψ ⟨0, 1, 0, 0⟩) e₀ := by
        rw [← map_mul, hij, map_neg, LinearMap.neg_apply, neg_neg, map_mul]
      _ = -Complex.I • e₁ := by
        rw [mul_apply_eq_comp, he₀_i, map_smul]
        simp [e₁]
  have hadj_i : LinearMap.adjoint (ψ ⟨0, 1, 0, 0⟩) = -ψ ⟨0, 1, 0, 0⟩ := by
    rw [hstar, show star (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = -⟨0, 1, 0, 0⟩ by ext <;> simp, map_neg]
  have hadj_j : LinearMap.adjoint (ψ ⟨0, 0, 1, 0⟩) = -ψ ⟨0, 0, 1, 0⟩ := by
    rw [hstar, show star (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = -⟨0, 0, 1, 0⟩ by ext <;> simp, map_neg]
  have horth : ⟪e₀, e₁⟫_ℂ = 0 := by
    have h₁ : Complex.I * ⟪e₀, e₁⟫_ℂ = -Complex.I * ⟪e₀, e₁⟫_ℂ := calc
      Complex.I * ⟪e₀, e₁⟫_ℂ = ⟪-Complex.I • e₀, e₁⟫_ℂ := by simp [inner_smul_left]
      _ = ⟪LinearMap.adjoint (ψ ⟨0, 1, 0, 0⟩) e₀, e₁⟫_ℂ := by
        rw [hadj_i, LinearMap.neg_apply, he₀_i, neg_smul]
      _ = -Complex.I * ⟪e₀, e₁⟫_ℂ := by
        rw [LinearMap.adjoint_inner_left, he₁_i, inner_smul_right]
    have h₂ : (2 * Complex.I) * ⟪e₀, e₁⟫_ℂ = 0 := by linear_combination h₁
    exact (mul_eq_zero.mp h₂).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have he₁_norm : ‖e₁‖ = 1 := by
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
    rw [← RCLike.ofReal_inj (K := ℂ), RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K]
    calc
      ⟪e₁, e₁⟫_ℂ = ⟪ψ ⟨0, 0, 1, 0⟩ e₀, ψ ⟨0, 0, 1, 0⟩ e₀⟫_ℂ := by simp [e₁]
      _ = ⟪e₀, e₀⟫_ℂ := by
        rw [← LinearMap.adjoint_inner_right, hadj_j, LinearMap.neg_apply,
          show ψ ⟨0, 0, 1, 0⟩ (ψ ⟨0, 0, 1, 0⟩ e₀) = -e₀ by
            rw [← neg_neg (ψ ⟨0, 0, 1, 0⟩ e₀), map_neg, he₁_j],
          neg_neg]
      _ = (((1 : ℝ) ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, he₀_norm]; simp
  refine ⟨orthonormal_iff_ite.mpr fun a b ↦ ?_, he₁_i, he₁_j⟩
  fin_cases a <;> fin_cases b
  · simp [inner_self_eq_norm_sq_to_K, he₀_norm]
  · simpa using horth
  · simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) horth
  · simp [inner_self_eq_norm_sq_to_K, he₁_norm]

private theorem exists_orthonormalBasis_toMatrix_eq_toComplexMatrix
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    (hS : finrank ℂ S = 2) (ψ : ℍ[ℝ] →ₐ[ℝ] Module.End ℂ S)
    (hstar : ∀ q, LinearMap.adjoint (ψ q) = ψ (star q)) :
    ∃ c : OrthonormalBasis (Fin 2) ℂ S,
      ∀ q : ℍ[ℝ], LinearMap.toMatrix c.toBasis c.toBasis (ψ q) = Quaternion.toComplexMatrix q := by
  obtain ⟨e₀, he₀_norm, he₀_i⟩ := exists_unit_eigenvector_quaternionAlgHom_i hS ψ
  obtain ⟨hon, he₁_i, he₁_j⟩ := orthonormal_pair_of_quaternionAlgHom ψ hstar he₀_norm he₀_i
  let c : OrthonormalBasis (Fin 2) ℂ S :=
    (basisOfOrthonormalOfCardEqFinrank hon (by simp [hS])).toOrthonormalBasis
      (by rwa [coe_basisOfOrthonormalOfCardEqFinrank])
  have hc₀ : c 0 = e₀ := by
    rw [← c.coe_toBasis, Module.Basis.toBasis_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
    rfl
  have hc₁ : c 1 = -(ψ ⟨0, 0, 1, 0⟩ e₀) := by
    rw [← c.coe_toBasis, Module.Basis.toBasis_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
    rfl
  have h_i₀ : ψ ⟨0, 1, 0, 0⟩ (c 0) = Complex.I • c 0 := by rw [hc₀, he₀_i]
  have h_i₁ : ψ ⟨0, 1, 0, 0⟩ (c 1) = (-Complex.I) • c 1 := by rw [hc₁, he₁_i, neg_smul]
  have h_j₀ : ψ ⟨0, 0, 1, 0⟩ (c 0) = -(c 1) := by rw [hc₀, hc₁, neg_neg]
  have h_j₁ : ψ ⟨0, 0, 1, 0⟩ (c 1) = c 0 := by rw [hc₁, he₁_j, hc₀]
  let Φ : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    ((LinearMap.toMatrixAlgEquiv c.toBasis).toAlgHom.restrictScalars ℝ).comp ψ
  have hΦ_i : Φ ⟨0, 1, 0, 0⟩ = Quaternion.toComplexMatrix ⟨0, 1, 0, 0⟩ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Φ, LinearMap.toMatrixAlgEquiv_apply, h_i₀, h_i₁, Quaternion.toComplexMatrix_apply]
  have hΦ_j : Φ ⟨0, 0, 1, 0⟩ = Quaternion.toComplexMatrix ⟨0, 0, 1, 0⟩ := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Φ, LinearMap.toMatrixAlgEquiv_apply, h_j₀, h_j₁, Quaternion.toComplexMatrix_apply]
  have hΦ_k : Φ ⟨0, 0, 0, 1⟩ = Quaternion.toComplexMatrix ⟨0, 0, 0, 1⟩ := by
    have hk : (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ := by ext <;> simp
    rw [hk, map_mul, map_mul, hΦ_i, hΦ_j]
  refine ⟨c, fun q ↦ ?_⟩
  have hdecomp : q = algebraMap ℝ ℍ[ℝ] q.re + q.imI • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) +
      q.imJ • (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) + q.imK • (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
    ext <;> simp
  change Φ q = Quaternion.toComplexMatrix.toAlgHom q
  conv_lhs => rw [hdecomp]
  conv_rhs => rw [hdecomp]
  simp only [map_add, map_smul, AlgHom.commutes, hΦ_i, hΦ_j, hΦ_k]
  rfl

end QuaternionHelpers

/-! ### Quaternion factor actions and characters on `W⁺` and `W⁻` -/

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

omit [Fact (finrank ℝ V = 4)] in
private theorem realEvenCliffordEquiv_reverseEven (x : even (realCliffordForm 4 0)) :
    b.realEvenCliffordEquiv hQ (reverseEven (realCliffordForm 4 0) x) =
      reverseEven Q (b.realEvenCliffordEquiv hQ x) := by
  have heq (y : even (realCliffordForm 4 0)) :
      b.realEvenCliffordEquiv hQ y =
        evenEquivOfIsometry (b.negRealCliffordFormIsometryEquiv hQ)
          (evenEquivEvenNeg (realCliffordForm 4 0) y) := by
    apply Subtype.ext
    rw [b.coe_realEvenCliffordEquiv_apply hQ, coe_evenEquivOfIsometry_apply,
      equivOfIsometry_apply]
  rw [heq, heq, evenEquivEvenNeg_reverseEven, evenEquivOfIsometry_reverseEven]

section Module

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

private def quaternionProdAction (ε : ℂ) :
    ℍ[ℝ] × ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) ε) :=
  (evenHalfSpinAction o ρ ε).comp
    ((b.realEvenCliffordEquiv hQ).toAlgHom.comp
      realCliffordFourZeroEvenEquivQuaternionProd.symm.toAlgHom)

include hQ in
private theorem halfSpinRep_realSpinGroupEquiv_eq_quaternionProdAction (ε : ℂ)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s) =
      quaternionProdAction o hQ b ρ ε
        ((realSpinFourEquivQuaternionUnitaryProd s).1,
          (realSpinFourEquivQuaternionUnitaryProd s).2) := by
  rw [coe_realSpinFourEquivQuaternionUnitaryProd_apply,
    evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, halfSpinRep_apply,
    OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv]
  simp [quaternionProdAction]

include hQ in
private theorem quaternionProdAction_neg_one_one (hb : b.toBasis.orientation = o) (ε : ℂ) :
    quaternionProdAction o hQ b ρ ε (-1, 1) = algebraMap ℂ _ ε := by
  ext ψ
  have hchir : chirality Q o = b.realEvenCliffordEquiv hQ
      (realCliffordFourZeroEvenEquivQuaternionProd.symm (-1, 1)) := by
    rw [realCliffordFourZeroEvenEquivQuaternionProd_symm_neg_one_one, map_neg, map_mul,
      OrthonormalBasis.realEvenCliffordEquiv_ι, OrthonormalBasis.realEvenCliffordEquiv_ι,
      chirality_eq o hQ b hb]
    simp [coe_even_ι_bilin, mul_assoc]
  simp only [quaternionProdAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    coe_evenHalfSpinAction_apply, ← hchir, mem_eigenspace_iff.1 ψ.2]
  simp [Algebra.algebraMap_eq_smul_one]

include hQ in
private theorem quaternionProdAction_zero_one (hb : b.toBasis.orientation = o) :
    quaternionProdAction o hQ b ρ 1 (0, 1) = 1 := by
  have h01 : ((0, 1) : ℍ[ℝ] × ℍ[ℝ]) = (2 : ℝ)⁻¹ • (1 + (-1, 1)) := by
    ext <;> simp; norm_num
  rw [h01, map_smul, map_add, map_one, quaternionProdAction_neg_one_one o hQ b ρ hb, map_one]
  module

include hQ in
private theorem quaternionProdAction_one_zero (hb : b.toBasis.orientation = o) :
    quaternionProdAction o hQ b ρ (-1) (1, 0) = 1 := by
  have h10 : ((1, 0) : ℍ[ℝ] × ℍ[ℝ]) = (2 : ℝ)⁻¹ • (1 - (-1, 1)) := by
    ext <;> simp; norm_num
  rw [h10, map_smul, map_sub, map_one, quaternionProdAction_neg_one_one o hQ b ρ hb,
    map_neg, map_one]
  module

/-- **The quaternion action on the positive half-spinors `W⁺`** induced by a positively oriented
orthonormal frame `b`: `q : ℍ[ℝ]` acts through the second factor `(0, q)` of
`Cl⁺(4, 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`. -/
def positiveQuaternionAction (hb : b.toBasis.orientation = o) :
    ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) 1) :=
  AlgHom.prodFirst
    ((quaternionProdAction o hQ b ρ 1).comp
      ((AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ])))
    (by simpa using quaternionProdAction_zero_one o hQ b ρ hb)

/-- **The quaternion action on the negative half-spinors `W⁻`** induced by a positively oriented
orthonormal frame `b`: `q : ℍ[ℝ]` acts through the first factor `(q, 0)` of
`Cl⁺(4, 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]`. -/
def negativeQuaternionAction (hb : b.toBasis.orientation = o) :
    ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) (-1)) :=
  AlgHom.prodFirst (quaternionProdAction o hQ b ρ (-1))
    (quaternionProdAction_one_zero o hQ b ρ hb)

/-- Unfolding `positiveQuaternionAction` as the even half-spin action at `(0, q)`. -/
theorem positiveQuaternionAction_apply (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    positiveQuaternionAction o hQ b ρ hb q =
      evenHalfSpinAction o ρ 1
        (b.realEvenCliffordEquiv hQ (realCliffordFourZeroEvenEquivQuaternionProd.symm (0, q))) := by
  simp [positiveQuaternionAction, quaternionProdAction]

/-- Unfolding `negativeQuaternionAction` as the even half-spin action at `(q, 0)`. -/
theorem negativeQuaternionAction_apply (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    negativeQuaternionAction o hQ b ρ hb q =
      evenHalfSpinAction o ρ (-1)
        (b.realEvenCliffordEquiv hQ (realCliffordFourZeroEvenEquivQuaternionProd.symm (q, 0))) := by
  simp [negativeQuaternionAction, quaternionProdAction]

include hQ in
/-- **Factorization of the positive half-spin representation**: along a positively oriented frame
`b`, `halfSpinRep` on `W⁺` factors through the **second** unit quaternion of compact `Spin(4)`. -/
theorem halfSpinRep_one_realSpinGroupEquiv_eq (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s) =
      positiveQuaternionAction o hQ b ρ hb (realSpinFourEquivQuaternionUnitaryProd s).2 := by
  let φ := (quaternionProdAction o hQ b ρ 1).comp
    ((AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ]))
  have hφ : φ (1, 0) = 1 := by simpa [φ] using quaternionProdAction_zero_one o hQ b ρ hb
  rw [halfSpinRep_realSpinGroupEquiv_eq_quaternionProdAction, positiveQuaternionAction,
    AlgHom.prodFirst_apply, ← AlgHom.map_eq_map_fst φ hφ
      ((realSpinFourEquivQuaternionUnitaryProd s).2,
        (realSpinFourEquivQuaternionUnitaryProd s).1)]
  rfl

include hQ in
/-- **Factorization of the negative half-spin representation**: along a positively oriented frame
`b`, `halfSpinRep` on `W⁻` factors through the **first** unit quaternion of compact `Spin(4)`. -/
theorem halfSpinRep_neg_one_realSpinGroupEquiv_eq (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s) =
      negativeQuaternionAction o hQ b ρ hb (realSpinFourEquivQuaternionUnitaryProd s).1 := by
  let φ := quaternionProdAction o hQ b ρ (-1)
  have hφ : φ (1, 0) = 1 := quaternionProdAction_one_zero o hQ b ρ hb
  rw [halfSpinRep_realSpinGroupEquiv_eq_quaternionProdAction, negativeQuaternionAction,
    AlgHom.prodFirst_apply, ← AlgHom.map_eq_map_fst φ hφ
      ((realSpinFourEquivQuaternionUnitaryProd s).1,
        (realSpinFourEquivQuaternionUnitaryProd s).2)]

section Characters

variable [FiniteDimensional ℂ W]

include hQ in
/-- **Character of `W⁺` on compact `Spin(4)`** in quaternion coordinates: the trace of `s` acting
on `W⁺` is `Re q₂ · dim_ℂ W⁺`, where `q₂` is the second unit quaternion of `s`. -/
theorem trace_halfSpinRep_one_realSpinGroupEquiv (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)) =
      (((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ]).re : ℂ) *
        finrank ℂ (eigenspace (ρ (chirality Q o)) 1) := by
  rw [halfSpinRep_one_realSpinGroupEquiv_eq o hQ b ρ hb, trace_quaternionAlgHom]

include hQ in
/-- **Character of `W⁻` on compact `Spin(4)`** in quaternion coordinates: the trace of `s` acting
on `W⁻` is `Re q₁ · dim_ℂ W⁻`, where `q₁` is the first unit quaternion of `s`. -/
theorem trace_halfSpinRep_neg_one_realSpinGroupEquiv (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)) =
      (((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]).re : ℂ) *
        finrank ℂ (eigenspace (ρ (chirality Q o)) (-1)) := by
  rw [halfSpinRep_neg_one_realSpinGroupEquiv_eq o hQ b ρ hb, trace_quaternionAlgHom]

include hQ in
/-- **Character of `W⁺` on compact `Spin(4)` in `SU(2)` coordinates**: when `dim_ℂ W⁺ = 2`, the
trace of `halfSpinRep` on `W⁺` is the matrix trace of the **second** `SU(2)` factor. -/
theorem trace_halfSpinRep_one_realSpinGroupEquiv_specialUnitary (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)) =
      ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  have hsnd : ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).2 :=
    congrArg Prod.snd (coe_realSpinFourEquivSpecialUnitaryProd_apply s)
  rw [trace_halfSpinRep_one_realSpinGroupEquiv o hQ b ρ hb, h₂, hsnd,
    Quaternion.trace_toComplexMatrix]
  push_cast
  ring

include hQ in
/-- **Character of `W⁻` on compact `Spin(4)` in `SU(2)` coordinates**: when `dim_ℂ W⁺ = 2`, the
trace of `halfSpinRep` on `W⁻` is the matrix trace of the **first** `SU(2)` factor. -/
theorem trace_halfSpinRep_neg_one_realSpinGroupEquiv_specialUnitary (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) :
    LinearMap.trace ℂ _ (halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)) =
      ((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  have hfst : ((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).1 :=
    congrArg Prod.fst (coe_realSpinFourEquivSpecialUnitaryProd_apply s)
  rw [trace_halfSpinRep_neg_one_realSpinGroupEquiv o hQ b ρ hb,
    finrank_eigenspace_chirality_neg o ρ 1, h₂, hfst, Quaternion.trace_toComplexMatrix]
  push_cast
  ring

include hQ in
/-- **Character of `W⁺` on compact `Spinᶜ(4)`**: at `[s, z]` transported along a positively
oriented frame `b`, the trace on a rank-two `W⁺` is `z` times the trace of the second `SU(2)`
factor of `s`. -/
theorem trace_spinCGroupHalfSpinRep_one_realSpinCGroupHom (hb : b.toBasis.orientation = o)
    (hpos : realCliffordForm 4 0 ≠ 0) (hQ₀ : Q ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ 1 hQ₀
          (b.realSpinCGroupHom hQ hpos hQ₀ (spinCGroup.mk _ hpos (s, z)))) =
      (z : ℂ) * ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  rw [OrthonormalBasis.realSpinCGroupHom_mk, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply,
    map_smul, trace_halfSpinRep_one_realSpinGroupEquiv_specialUnitary o hQ b ρ hb h₂, smul_eq_mul]

include hQ in
/-- **Character of `W⁻` on compact `Spinᶜ(4)`**: at `[s, z]` transported along a positively
oriented frame `b`, the trace on `W⁻` (when `dim_ℂ W⁺ = 2`) is `z` times the trace of the first
`SU(2)` factor of `s`. -/
theorem trace_spinCGroupHalfSpinRep_neg_one_realSpinCGroupHom (hb : b.toBasis.orientation = o)
    (hpos : realCliffordForm 4 0 ≠ 0) (hQ₀ : Q ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2)
    (s : spinGroup (realCliffordForm 4 0)) (z : Circle) :
    LinearMap.trace ℂ _
        (spinCGroupHalfSpinRep o ρ (-1) hQ₀
          (b.realSpinCGroupHom hQ hpos hQ₀ (spinCGroup.mk _ hpos (s, z)))) =
      (z : ℂ) * ((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ).trace := by
  rw [OrthonormalBasis.realSpinCGroupHom_mk, spinCGroupHalfSpinRep_mk, spinCHalfSpinRep_apply,
    map_smul, trace_halfSpinRep_neg_one_realSpinGroupEquiv_specialUnitary o hQ b ρ hb h₂,
    smul_eq_mul]

end Characters

end Module

/-! ### Hermitian adjoint compatibility and explicit `SU(2)₋ × SU(2)₊` spinor bases -/

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

include hQ in
/-- On a Hermitian Clifford module, `positiveQuaternionAction` carries quaternion conjugation to
the Hilbert-space adjoint. -/
theorem adjoint_positiveQuaternionAction
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    LinearMap.adjoint (positiveQuaternionAction o hQ b ρ hb q) =
      positiveQuaternionAction o hQ b ρ hb (star q) := by
  have hsymm : reverseEven (realCliffordForm 4 0)
      (realCliffordFourZeroEvenEquivQuaternionProd.symm (0, q)) =
      realCliffordFourZeroEvenEquivQuaternionProd.symm (0, star q) := by
    apply realCliffordFourZeroEvenEquivQuaternionProd.injective
    rw [realCliffordFourZeroEvenEquivQuaternionProd_reverseEven,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    exact Prod.ext (by simp) rfl
  rw [positiveQuaternionAction_apply, adjoint_evenHalfSpinAction o hρ,
    ← realEvenCliffordEquiv_reverseEven hQ b, hsymm, ← positiveQuaternionAction_apply]

include hQ in
/-- On a Hermitian Clifford module, `negativeQuaternionAction` carries quaternion conjugation to
the Hilbert-space adjoint. -/
theorem adjoint_negativeQuaternionAction
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o) (q : ℍ[ℝ]) :
    LinearMap.adjoint (negativeQuaternionAction o hQ b ρ hb q) =
      negativeQuaternionAction o hQ b ρ hb (star q) := by
  have hsymm : reverseEven (realCliffordForm 4 0)
      (realCliffordFourZeroEvenEquivQuaternionProd.symm (q, 0)) =
      realCliffordFourZeroEvenEquivQuaternionProd.symm (star q, 0) := by
    apply realCliffordFourZeroEvenEquivQuaternionProd.injective
    rw [realCliffordFourZeroEvenEquivQuaternionProd_reverseEven,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    exact Prod.ext rfl (by simp)
  rw [negativeQuaternionAction_apply, adjoint_evenHalfSpinAction o hρ,
    ← realEvenCliffordEquiv_reverseEven hQ b, hsymm, ← negativeQuaternionAction_apply]

include hQ in
/-- **Orthonormal half-spinor basis for `W⁺`**: on a Hermitian Clifford module of half-spin rank
two, `W⁺` admits an orthonormal basis in which `halfSpinRep` at `b.realSpinGroupEquiv hQ s` has
matrix equal to the **second** `SU(2)` factor `(realSpinFourEquivSpecialUnitaryProd s).2`. -/
theorem exists_orthonormalBasis_toMatrix_halfSpinRep_one
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2) :
    ∃ c : OrthonormalBasis (Fin 2) ℂ (eigenspace (ρ (chirality Q o)) 1),
      ∀ s : spinGroup (realCliffordForm 4 0),
        LinearMap.toMatrix c.toBasis c.toBasis (halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s)) =
          ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨c, hc⟩ := exists_orthonormalBasis_toMatrix_eq_toComplexMatrix h₂
    (positiveQuaternionAction o hQ b ρ hb) (adjoint_positiveQuaternionAction o hQ b hρ hb)
  refine ⟨c, fun s ↦ ?_⟩
  rw [halfSpinRep_one_realSpinGroupEquiv_eq o hQ b ρ hb, hc]
  exact (congrArg Prod.snd (coe_realSpinFourEquivSpecialUnitaryProd_apply s)).symm

include hQ in
/-- **Orthonormal half-spinor basis for `W⁻`**: on a Hermitian Clifford module of half-spin rank
two, `W⁻` admits an orthonormal basis in which `halfSpinRep` at `b.realSpinGroupEquiv hQ s` has
matrix equal to the **first** `SU(2)` factor `(realSpinFourEquivSpecialUnitaryProd s).1`. -/
theorem exists_orthonormalBasis_toMatrix_halfSpinRep_neg_one
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (hb : b.toBasis.orientation = o)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2) :
    ∃ c : OrthonormalBasis (Fin 2) ℂ (eigenspace (ρ (chirality Q o)) (-1)),
      ∀ s : spinGroup (realCliffordForm 4 0),
        LinearMap.toMatrix c.toBasis c.toBasis (halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s)) =
          ((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h₂_neg : finrank ℂ (eigenspace (ρ (chirality Q o)) (-1)) = 2 := by
    rw [finrank_eigenspace_chirality_neg o ρ 1, h₂]
  obtain ⟨c, hc⟩ := exists_orthonormalBasis_toMatrix_eq_toComplexMatrix h₂_neg
    (negativeQuaternionAction o hQ b ρ hb) (adjoint_negativeQuaternionAction o hQ b hρ hb)
  refine ⟨c, fun s ↦ ?_⟩
  rw [halfSpinRep_neg_one_realSpinGroupEquiv_eq o hQ b ρ hb, hc]
  exact (congrArg Prod.fst (coe_realSpinFourEquivSpecialUnitaryProd_apply s)).symm

end Hermitian

end CliffordAlgebra

/-! ### Quaternion-pair coordinates of `OrthonormalBasis.spinTorus` -/

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} (b : OrthonormalBasis (Fin 4) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

include hQ in
/-- **Quaternion-pair coordinates of `OrthonormalBasis.spinTorus`**: pulling `(w₁, w₂)` back along
`b.realSpinGroupEquiv hQ` into compact `Spin(4) ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` gives
`re(w₁ w₂⁻¹) + im(w₁ w₂⁻¹) k` in the first factor (which acts on `W⁻`) and
`re(w₁ w₂) + im(w₁ w₂) k` in the second factor (which acts on `W⁺`). -/
theorem coe_realSpinFourEquivQuaternionUnitaryProd_symm_spinTorus (w₁ w₂ : Circle) :
    (((realSpinFourEquivQuaternionUnitaryProd
        ((b.realSpinGroupEquiv hQ).symm (b.spinTorus hQ (w₁, w₂)))).1 : ℍ[ℝ]),
      ((realSpinFourEquivQuaternionUnitaryProd
        ((b.realSpinGroupEquiv hQ).symm (b.spinTorus hQ (w₁, w₂)))).2 : ℍ[ℝ])) =
      (⟨((w₁ * w₂⁻¹ : Circle) : ℂ).re, 0, 0, ((w₁ * w₂⁻¹ : Circle) : ℂ).im⟩,
        ⟨((w₁ * w₂ : Circle) : ℂ).re, 0, 0, ((w₁ * w₂ : Circle) : ℂ).im⟩) := by
  let s := (b.realSpinGroupEquiv hQ).symm (b.spinTorus hQ (w₁, w₂))
  let B₀₁ := (even.ι (realCliffordForm 4 0)).bilin (Pi.single 0 1) (Pi.single 1 1)
  let B₂₃ := (even.ι (realCliffordForm 4 0)).bilin (Pi.single 2 1) (Pi.single 3 1)
  have hs_even : b.realEvenCliffordEquiv hQ
      (evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (spinGroupToEvenUnitary (realCliffordForm 4 0) s)) =
      spinGroupToEven Q (b.spinTorus hQ (w₁, w₂)) := by
    rw [evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply,
      ← b.spinGroupToEven_realSpinGroupEquiv hQ s, MulEquiv.apply_symm_apply]
  have htorus : spinGroupToEven Q (b.spinTorus hQ (w₁, w₂)) =
      b.realEvenCliffordEquiv hQ
        ((algebraMap ℝ _ (w₁ : ℂ).re - (w₁ : ℂ).im • B₀₁) *
          (algebraMap ℝ _ (w₂ : ℂ).re - (w₂ : ℂ).im • B₂₃)) := by
    apply Subtype.ext
    rw [coe_spinGroupToEven_apply, b.coe_spinTorus_apply hQ]
    simp [B₀₁, B₂₃, OrthonormalBasis.realEvenCliffordEquiv_ι, coe_even_ι_bilin]
  have hcoord : evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (spinGroupToEvenUnitary (realCliffordForm 4 0) s) =
      (algebraMap ℝ _ (w₁ : ℂ).re - (w₁ : ℂ).im • B₀₁) *
        (algebraMap ℝ _ (w₂ : ℂ).re - (w₂ : ℂ).im • B₂₃) :=
    (b.realEvenCliffordEquiv hQ).injective (hs_even.trans htorus)
  change (((realSpinFourEquivQuaternionUnitaryProd s).1 : ℍ[ℝ]),
      ((realSpinFourEquivQuaternionUnitaryProd s).2 : ℍ[ℝ])) = _
  rw [coe_realSpinFourEquivQuaternionUnitaryProd_apply, hcoord]
  simp only [B₀₁, B₂₃, map_mul, map_sub, map_smul, AlgEquiv.commutes,
    realCliffordFourZeroEvenEquivQuaternionProd_ι]
  apply Prod.ext <;> ext <;>
    simp [Circle.coe_mul, QuaternionAlgebra.mk_mul_mk, Algebra.algebraMap_eq_smul_one]

section FrameChange

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {n : ℕ} (c c' : OrthonormalBasis (Fin n) ℝ V)
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- For two equally oriented orthonormal frames `c` and `c'`, the negative-metric Spin frame
comparisons `c.realSpinGroupEquiv hQ` and `c'.realSpinGroupEquiv hQ` differ by conjugation in
compact `Spin(n)`. -/
theorem exists_realSpinGroupEquiv_eq_conj (hc : c.toBasis.orientation = c'.toBasis.orientation) :
    ∃ s₀ : spinGroup (realCliffordForm n 0), ∀ s : spinGroup (realCliffordForm n 0),
      c'.realSpinGroupEquiv hQ s = c.realSpinGroupEquiv hQ (s₀ * s * s₀⁻¹) := by
  have hQneg : ∀ v, (-Q) v = ‖v‖ ^ 2 := fun v ↦ by simp [hQ]
  obtain ⟨s₀, hs₀⟩ := (c'.exists_spinVectorAction_eq_iff_orientation_eq c hQneg).mpr hc.symm
  have hact (x : Fin (n + 0) → ℝ) :
      spinVectorAction Q (c.realSpinGroupEquiv hQ s₀)
        (c.negRealCliffordFormIsometryEquiv hQ x) =
        c'.negRealCliffordFormIsometryEquiv hQ x := by
    rw [c.spinVectorAction_realSpinGroupEquiv hQ s₀ x]
    have hsymm : spinVectorAction (realCliffordForm n 0) s₀ x =
        (c.negRealCliffordFormIsometryEquiv hQ).symm
          (c'.negRealCliffordFormIsometryEquiv hQ x) := by
      ext i
      have hi : c'.isometryEquivRealCliffordFormZero hQneg
          (c'.negRealCliffordFormIsometryEquiv hQ x) = x := by
        ext j
        rw [isometryEquivRealCliffordFormZero_apply,
          ← c'.negRealCliffordFormIsometryEquiv_symm_apply hQ,
          QuadraticMap.IsometryEquiv.symm_apply_apply]
      rw [c.negRealCliffordFormIsometryEquiv_symm_apply hQ,
        ← isometryEquivRealCliffordFormZero_apply c hQneg,
        ← hs₀ (c'.negRealCliffordFormIsometryEquiv hQ x), hi]
    rw [hsymm, QuadraticMap.IsometryEquiv.apply_symm_apply]
  have heq (s : spinGroup (realCliffordForm n 0)) (f : OrthonormalBasis (Fin n) ℝ V) :
      f.realSpinGroupEquiv hQ s =
        (f.negRealCliffordFormIsometryEquiv hQ).spinGroupEquiv
          (spinGroupEquivNeg (realCliffordForm n 0) s) :=
    Subtype.ext <| by
      rw [← coe_spinGroupToEven_apply, f.spinGroupToEven_realSpinGroupEquiv hQ,
        f.coe_realEvenCliffordEquiv_apply hQ, QuadraticMap.IsometryEquiv.spinGroupEquiv_apply,
        QuadraticMap.Isometry.coe_spinGroupMap_apply, ← coe_spinGroupEquivNeg_apply]
  refine ⟨s₀, fun s ↦ ?_⟩
  rw [heq s c', (c.negRealCliffordFormIsometryEquiv hQ).spinGroupEquiv_apply_eq_conj _
      (c.realSpinGroupEquiv hQ s₀) hact, ← heq s c, ← map_inv, ← map_mul, ← map_mul]

/-- For two equally oriented orthonormal frames `c` and `c'`, the descended `Spinᶜ(n)` frame
comparisons `c.realSpinCGroupHom` and `c'.realSpinCGroupHom` differ by conjugation by a compact
Spin element. -/
theorem exists_realSpinCGroupHom_eq_conj (hc : c.toBasis.orientation = c'.toBasis.orientation)
    (hpos : realCliffordForm n 0 ≠ 0) (hQ₀ : Q ≠ 0) :
    ∃ s₀ : spinGroup (realCliffordForm n 0), ∀ x : spinCGroup (realCliffordForm n 0) hpos,
      c'.realSpinCGroupHom hQ hpos hQ₀ x =
        c.realSpinCGroupHom hQ hpos hQ₀
          (spinCGroup.ofSpin _ hpos s₀ * x * (spinCGroup.ofSpin _ hpos s₀)⁻¹) := by
  obtain ⟨s₀, hs₀⟩ := exists_realSpinGroupEquiv_eq_conj c c' hQ hc
  refine ⟨s₀, fun x ↦ ?_⟩
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective _ hpos x
  simp [spinCGroup.ofSpin_apply, ← map_inv, ← map_mul, hs₀ s]

end FrameChange

end OrthonormalBasis
