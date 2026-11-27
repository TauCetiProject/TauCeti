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

* `LinearMap.IsSymmetric.eigenvalues_le_singularValues_of_two_smul_eq`: the **Fan–Hoffman
  inequality** `λⱼ(H) ≤ sⱼ(T)`.
* `LinearMap.exists_unitary_le_conj_operatorAbs_of_two_smul_eq`: `H ≤ U |T| U⁻¹` for some
  unitary `U`.

The Hermitian part has the real quadratic form of `T` and is symmetric
(`LinearMap.re_inner_apply_self_eq_of_two_smul_eq` and `LinearMap.isSymmetric_of_two_smul_eq`,
in `TauCeti.Analysis.InnerProductSpace.Adjoint`); the comparison by a unitary is
`LinearMap.IsSymmetric.exists_unitary_le_conj_of_eigenvalues_le`, in
`TauCeti.Analysis.InnerProductSpace.CourantFischer`.

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
