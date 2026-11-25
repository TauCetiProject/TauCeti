/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Eigenvalues of the Hermitian part and comparison by a unitary

Let `T` be an endomorphism of a finite-dimensional inner product space `E` over `𝕜 = ℝ, ℂ`, and
let `H` be its Hermitian part, the symmetric operator with `2 • H = T + T†`. The decreasingly
sorted eigenvalues of `H` are bounded by the singular values of `T`, index by index. Two
symmetric operators whose sorted eigenvalues are comparable index by index are comparable in the
Loewner order after conjugating the larger one by a unitary; together, the Hermitian part of `T`
is below a unitary conjugate of the modulus `|T|`.

## Main results

* `LinearMap.re_inner_apply_self_eq_of_two_smul_eq`: `T` and its Hermitian part have the same
  real quadratic form `re ⟪T x, x⟫`.
* `LinearMap.isSymmetric_of_two_smul_eq`: the Hermitian part is symmetric.
* `LinearMap.IsSymmetric.eigenvalues_le_singularValues_of_two_smul_eq`: the **Fan–Hoffman
  inequality** `λⱼ(H) ≤ sⱼ(T)`.
* `LinearMap.IsSymmetric.exists_unitary_le_conj_of_eigenvalues_le`: **comparison by a unitary**;
  if `λⱼ(X) ≤ λⱼ(Y)` for every `j`, then `X ≤ U Y U⁻¹` for some unitary `U`.
* `LinearMap.exists_unitary_le_conj_operatorAbs_of_two_smul_eq`: `H ≤ U |T| U⁻¹` for some
  unitary `U`.

## References

* R. Bhatia, *Matrix Analysis*, Springer, 1997: Proposition III.5.1 (p. 73) and
  Exercise III.5.5 (p. 74).
* A. W. Marshall, I. Olkin and B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer, 2011: 9.F.4 (p. 327).
-/

public section

open Module
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace LinearMap

/-- An endomorphism `T` and its Hermitian part `H`, given by `2 • H = T + T†`, have the same real
quadratic form: `re ⟪H x, x⟫ = re ⟪T x, x⟫`. -/
theorem re_inner_apply_self_eq_of_two_smul_eq {T H : E →ₗ[𝕜] E}
    (hHT : (2 : 𝕜) • H = T + adjoint T) (x : E) :
    RCLike.re ⟪H x, x⟫_𝕜 = RCLike.re ⟪T x, x⟫_𝕜 := by
  have h := congrArg (fun y ↦ RCLike.re ⟪y, x⟫_𝕜) (LinearMap.congr_fun hHT x)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_add_left, inner_smul_left,
    adjoint_inner_left, map_add, map_ofNat, RCLike.ofNat_mul_re] at h
  rw [inner_re_symm x] at h
  linarith

/-- A solution `H` of `2 • H = T + T†`, the Hermitian part of `T`, is symmetric. -/
theorem isSymmetric_of_two_smul_eq {T H : E →ₗ[𝕜] E} (hHT : (2 : 𝕜) • H = T + adjoint T) :
    H.IsSymmetric := by
  refine (isSymmetric_iff_isSelfAdjoint H).mpr (smul_right_injective _ (two_ne_zero (α := 𝕜)) ?_)
  have h := congrArg adjoint hHT
  rw [LinearEquiv.map_smulₛₗ, map_ofNat, map_add, adjoint_adjoint, add_comm, ← hHT] at h
  simpa [star_eq_adjoint] using h

namespace IsSymmetric

/-- **Fan–Hoffman inequality.** If `H` is the Hermitian part of `T`, given by `2 • H = T + T†`,
then the `j`-th largest eigenvalue of `H` is at most the `j`-th singular value of `T`. -/
theorem eigenvalues_le_singularValues_of_two_smul_eq {T H : E →ₗ[𝕜] E} (hH : H.IsSymmetric)
    (hHT : (2 : 𝕜) • H = T + adjoint T) {n : ℕ} (hn : finrank 𝕜 E = n) (j : Fin n) :
    hH.eigenvalues hn j ≤ T.singularValues j := by
  -- A unit vector `x` in the span of the top `j + 1` eigenvectors of `H` with `‖T x‖ ≤ sⱼ(T)`.
  obtain ⟨V, hVdim, hV⟩ := hH.exists_submodule_forall_unit_eigenvalue_le_re_inner hn j
  obtain ⟨x, hxV, hx1, hx⟩ := T.exists_unit_vector_norm_apply_le_singularValues V hVdim.ge
  calc hH.eigenvalues hn j ≤ RCLike.re ⟪H x, x⟫_𝕜 := hV x hxV hx1
    _ = RCLike.re ⟪T x, x⟫_𝕜 := re_inner_apply_self_eq_of_two_smul_eq hHT x
    _ ≤ ‖⟪T x, x⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ T.singularValues j := by rwa [hx1, mul_one]

/-- **Comparison by a unitary.** If the sorted eigenvalues of the symmetric operators `X` and
`Y` satisfy `λⱼ(X) ≤ λⱼ(Y)` for every `j`, then `X ≤ U Y U⁻¹` for some unitary `U`. -/
theorem exists_unitary_le_conj_of_eigenvalues_le {X Y : E →ₗ[𝕜] E} (hX : X.IsSymmetric)
    (hY : Y.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n)
    (h : ∀ j, hX.eigenvalues hn j ≤ hY.eigenvalues hn j) :
    ∃ U : E ≃ₗᵢ[𝕜] E,
      ((U : E →ₗ[𝕜] E) ∘ₗ Y ∘ₗ (U.symm : E →ₗ[𝕜] E) - X).IsPositive := by
  -- `U` maps the eigenbasis of `Y` to that of `X`, so `U Y U⁻¹ - X` is diagonal in the latter.
  set bX := hX.eigenvectorBasis hn
  set U := (hY.eigenvectorBasis hn).equiv bX (Equiv.refl _)
  refine ⟨U, ((isSymmetric_linearIsometryEquiv_conj_iff Y U).mpr hY).sub hX, fun x ↦ ?_⟩
  have hD : ∀ i, ((U : E →ₗ[𝕜] E) ∘ₗ Y ∘ₗ (U.symm : E →ₗ[𝕜] E) - X) (bX i) =
      ((hY.eigenvalues hn i - hX.eigenvalues hn i : ℝ) : 𝕜) • bX i := fun i ↦ by
    simp [U, bX, hY.apply_eigenvectorBasis, hX.apply_eigenvectorBasis, sub_smul]
  rw [re_inner_apply_self_eq_sum_of_eigenbasis _ bX hD]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (sub_nonneg.mpr (h i)) (sq_nonneg _)

end IsSymmetric

/-- The Hermitian part `H` of `T`, given by `2 • H = T + T†`, satisfies `H ≤ U |T| U⁻¹` for some
unitary `U`. -/
theorem exists_unitary_le_conj_operatorAbs_of_two_smul_eq {T H : E →ₗ[𝕜] E}
    (hHT : (2 : 𝕜) • H = T + adjoint T) :
    ∃ U : E ≃ₗᵢ[𝕜] E,
      ((U : E →ₗ[𝕜] E) ∘ₗ T.operatorAbs ∘ₗ (U.symm : E →ₗ[𝕜] E) - H).IsPositive :=
  have hH := isSymmetric_of_two_smul_eq hHT
  hH.exists_unitary_le_conj_of_eigenvalues_le T.isSymmetric_operatorAbs rfl fun j ↦ by
    rw [T.isPositive_operatorAbs.eigenvalues_eq_singularValues, singularValues_operatorAbs]
    exact hH.eigenvalues_le_singularValues_of_two_smul_eq hHT rfl j

end LinearMap
