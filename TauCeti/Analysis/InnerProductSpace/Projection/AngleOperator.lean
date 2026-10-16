/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle

/-!
# The cosine and sine angle operators of two subspaces

Let `U` and `V` be subspaces of a Hilbert space `E` with orthogonal projections `P_U` and `P_V`.
The *cosine angle operator* of `(U, V)` is the modulus `|P_V P_U|` of the cosine map, and the
*sine angle operator* is the modulus `|P_U - P_V|` of the difference of the two projections. They
are the operator-valued `cos Θ` and `sin Θ` of the pair, defined in every dimension through the
modulus `ContinuousLinearMap.modulus` of a bounded operator.

The two operators satisfy the operator form of `cos² Θ + sin² Θ = 1` on `U`:

`|P_V P_U|² + |P_U - P_V|² P_U = P_U`.

The sine angle operator is symmetric in `U` and `V`, commutes with `P_U` (hence, by symmetry,
with `P_V`) and with the cosine angle operator, and its compression to `U` is the modulus of the
directed sine map `P_{Vᗮ} P_U`. Its operator norm is the projection gap `‖P_U - P_V‖`, and its
kernel is `(U ⊓ V) ⊔ (Uᗮ ⊓ Vᗮ)`, the vectors on which the two projections agree.

## Main definitions

* `Submodule.cosAngleOperator U V`: the cosine angle operator `|P_V P_U|`.
* `Submodule.sinAngleOperator U V`: the sine angle operator `|P_U - P_V|`.

## Main results

* `Submodule.cosAngleOperator_sq`, `Submodule.sinAngleOperator_sq`: the squares are `P_U P_V P_U`
  and `(P_U - P_V)²`.
* `Submodule.cosAngleOperator_sq_add_sinAngleOperator_sq_mul_starProjection`: the Pythagorean
  identity `cos² Θ + sin² Θ P_U = P_U`.
* `Submodule.commute_starProjection_sinAngleOperator`,
  `Submodule.commute_cosAngleOperator_sinAngleOperator`: the sine angle operator commutes with
  `P_U` and with the cosine angle operator.
* `Submodule.sinAngleOperator_mul_starProjection`: `|P_U - P_V| P_U = |P_{Vᗮ} P_U|`.
* `Submodule.norm_sinAngleOperator`: `‖|P_U - P_V|‖` is the projection gap.
* `Submodule.ker_sinAngleOperator`: the kernel of the sine angle operator is
  `(U ⊓ V) ⊔ (Uᗮ ⊓ Vᗮ)`; `Submodule.sinAngleOperator_eq_zero_iff`: it vanishes exactly when
  `U = V`.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed., Springer (1976), §I.4.6.
-/

public section

noncomputable section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The cosine angle operator `|P_V P_U|` of two subspaces: the modulus of the cosine map. -/
def cosAngleOperator : E →L[𝕜] E :=
  (U.cosThetaMap V).modulus

/-- The sine angle operator `|P_U - P_V|` of two subspaces: the modulus of the difference of the
orthogonal projections. -/
def sinAngleOperator : E →L[𝕜] E :=
  (U.starProjection - V.starProjection).modulus

theorem cosAngleOperator_def : U.cosAngleOperator V = (U.cosThetaMap V).modulus :=
  (rfl)

theorem sinAngleOperator_def :
    U.sinAngleOperator V = (U.starProjection - V.starProjection).modulus :=
  (rfl)

theorem isPositive_cosAngleOperator : (U.cosAngleOperator V).IsPositive :=
  isPositive_modulus _

theorem isPositive_sinAngleOperator : (U.sinAngleOperator V).IsPositive :=
  isPositive_modulus _

/-! ### Squares, norms and kernels -/

/-- The square of the cosine angle operator is the compression `P_U P_V P_U`. -/
theorem cosAngleOperator_sq :
    U.cosAngleOperator V ^ 2 = U.starProjection * V.starProjection * U.starProjection := by
  rw [sq, ContinuousLinearMap.mul_def, cosAngleOperator, modulus_comp_modulus, cosThetaMap_def,
    adjoint_comp, (isSelfAdjoint_starProjection U).adjoint_eq,
    (isSelfAdjoint_starProjection V).adjoint_eq]
  simp only [← ContinuousLinearMap.mul_def, mul_assoc]
  rw [← mul_assoc V.starProjection, V.isIdempotentElem_starProjection.eq]

/-- The square of the sine angle operator is the square of the difference of the projections. -/
theorem sinAngleOperator_sq :
    U.sinAngleOperator V ^ 2 = (U.starProjection - V.starProjection) ^ 2 := by
  rw [sq, sq, ContinuousLinearMap.mul_def, sinAngleOperator, modulus_comp_modulus,
    ((isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)).adjoint_eq,
    ContinuousLinearMap.mul_def]

@[simp]
theorem norm_cosAngleOperator_apply (x : E) :
    ‖U.cosAngleOperator V x‖ = ‖V.starProjection (U.starProjection x)‖ := by
  rw [cosAngleOperator, norm_modulus_apply, cosThetaMap_apply]

@[simp]
theorem norm_sinAngleOperator_apply (x : E) :
    ‖U.sinAngleOperator V x‖ = ‖U.starProjection x - V.starProjection x‖ := by
  rw [sinAngleOperator, norm_modulus_apply, sub_apply]

/-- The operator norm of the cosine angle operator is that of the cosine map `P_V P_U`. -/
@[simp]
theorem norm_cosAngleOperator : ‖U.cosAngleOperator V‖ = ‖U.cosThetaMap V‖ := by
  rw [cosAngleOperator, norm_modulus]

/-- The operator norm of the sine angle operator is the projection gap `‖P_U - P_V‖`. -/
@[simp]
theorem norm_sinAngleOperator : ‖U.sinAngleOperator V‖ = U.projectionGap V := by
  rw [sinAngleOperator, norm_modulus, projectionGap_def]

theorem norm_cosAngleOperator_le_one : ‖U.cosAngleOperator V‖ ≤ 1 :=
  (U.norm_cosAngleOperator V).trans_le (U.norm_cosThetaMap_le_one V)

theorem norm_sinAngleOperator_le_one : ‖U.sinAngleOperator V‖ ≤ 1 :=
  (U.norm_sinAngleOperator V).trans_le (U.projectionGap_le_one V)

/-- The kernel of the cosine angle operator is the set of vectors whose projection to `U` is
orthogonal to `V`. -/
theorem mem_ker_cosAngleOperator {x : E} :
    x ∈ (U.cosAngleOperator V).ker ↔ U.starProjection x ∈ Vᗮ := by
  rw [cosAngleOperator, ker_modulus, LinearMap.mem_ker, coe_coe, cosThetaMap_apply,
    starProjection_apply_eq_zero_iff]

/-- The kernel of the sine angle operator is `(U ⊓ V) ⊔ (Uᗮ ⊓ Vᗮ)`: a vector is annihilated by
`|P_U - P_V|` exactly when its components in `U` and in `V` coincide. -/
theorem ker_sinAngleOperator : (U.sinAngleOperator V).ker = U ⊓ V ⊔ Uᗮ ⊓ Vᗮ := by
  ext x
  rw [sinAngleOperator, ker_modulus, LinearMap.mem_ker, coe_coe, sub_apply, sub_eq_zero,
    mem_sup]
  constructor
  · intro h
    refine ⟨U.starProjection x, ⟨U.starProjection_apply_mem x, h ▸ V.starProjection_apply_mem x⟩,
      x - U.starProjection x, ⟨U.sub_starProjection_mem_orthogonal x, ?_⟩, add_sub_cancel _ _⟩
    exact h ▸ V.sub_starProjection_mem_orthogonal x
  · rintro ⟨a, ⟨haU, haV⟩, b, ⟨hbU, hbV⟩, rfl⟩
    rw [map_add, map_add, starProjection_eq_self_iff.2 haU, starProjection_eq_self_iff.2 haV,
      U.starProjection_apply_eq_zero_iff.2 hbU, V.starProjection_apply_eq_zero_iff.2 hbV]

/-- The cosine angle operator vanishes exactly when `U` and `V` are orthogonal. -/
@[simp]
theorem cosAngleOperator_eq_zero_iff : U.cosAngleOperator V = 0 ↔ U ⟂ V := by
  rw [← norm_eq_zero, norm_cosAngleOperator, norm_eq_zero, cosThetaMap_eq_zero_iff]

/-- The sine angle operator vanishes exactly when `U = V`. -/
@[simp]
theorem sinAngleOperator_eq_zero_iff : U.sinAngleOperator V = 0 ↔ U = V := by
  rw [← norm_eq_zero, norm_sinAngleOperator, projectionGap_def, norm_eq_zero, sub_eq_zero,
    starProjection_inj]

/-! ### Symmetries and special cases -/

/-- The sine angle operator is symmetric in the two subspaces. -/
theorem sinAngleOperator_comm : V.sinAngleOperator U = U.sinAngleOperator V := by
  rw [sinAngleOperator, sinAngleOperator, ← neg_sub, modulus_neg]

/-- Passing to orthogonal complements does not change the sine angle operator. -/
@[simp]
theorem sinAngleOperator_orthogonal : Uᗮ.sinAngleOperator Vᗮ = U.sinAngleOperator V := by
  rw [sinAngleOperator, starProjection_orthogonal' U, starProjection_orthogonal' V,
    sub_sub_sub_cancel_left, sinAngleOperator_comm, sinAngleOperator]

@[simp]
theorem sinAngleOperator_self : U.sinAngleOperator U = 0 :=
  (U.sinAngleOperator_eq_zero_iff U).2 rfl

/-- The cosine angle operator of a subspace with itself is its orthogonal projection. -/
@[simp]
theorem cosAngleOperator_self : U.cosAngleOperator U = U.starProjection := by
  have hP := U.isIdempotentElem_starProjection.eq
  have hpos := isPositive_adjoint_comp_self U.starProjection
  rw [(isSelfAdjoint_starProjection U).adjoint_eq, ← ContinuousLinearMap.mul_def, hP] at hpos
  rw [cosAngleOperator, cosThetaMap_def, ← ContinuousLinearMap.mul_def, hP, hpos.modulus_eq]

/-! ### Interaction with the projections -/

/-- The cosine angle operator vanishes on `Uᗮ`: `|P_V P_U| P_U = |P_V P_U|`. -/
@[simp]
theorem cosAngleOperator_mul_starProjection :
    U.cosAngleOperator V * U.starProjection = U.cosAngleOperator V := by
  ext x
  rw [ContinuousLinearMap.mul_def, comp_apply, ← sub_eq_zero, ← map_sub, ← norm_eq_zero,
    norm_cosAngleOperator_apply, map_sub,
    starProjection_eq_self_iff.2 (U.starProjection_apply_mem x), sub_self, map_zero, norm_zero]

/-- The cosine angle operator takes values in `U`: `P_U |P_V P_U| = |P_V P_U|`. -/
@[simp]
theorem starProjection_mul_cosAngleOperator :
    U.starProjection * U.cosAngleOperator V = U.cosAngleOperator V := by
  have h := congrArg adjoint (U.cosAngleOperator_mul_starProjection V)
  rwa [← star_eq_adjoint, star_mul, star_eq_adjoint, star_eq_adjoint,
    (isSelfAdjoint_starProjection U).adjoint_eq,
    (U.isPositive_cosAngleOperator V).isSelfAdjoint.adjoint_eq] at h

omit [CompleteSpace E] in
/-- Compressing `(P_U - P_V)²` to `U` from either side gives `P_U - P_U P_V P_U`. -/
private theorem sub_sq_mul_starProjection :
    (U.starProjection - V.starProjection) ^ 2 * U.starProjection =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection ∧
    U.starProjection * (U.starProjection - V.starProjection) ^ 2 =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
  have hP := U.isIdempotentElem_starProjection.eq
  have hQ := V.isIdempotentElem_starProjection.eq
  have hP' : ∀ T : E →L[𝕜] E, U.starProjection * (U.starProjection * T) = U.starProjection * T :=
    fun T ↦ by rw [← mul_assoc, hP]
  constructor <;>
  · simp only [sq, sub_mul, mul_sub, mul_assoc, hP, hQ, hP']
    abel

/-- The sine angle operator commutes with the projection onto `U`. -/
theorem commute_starProjection_sinAngleOperator :
    Commute U.starProjection (U.sinAngleOperator V) := by
  refine commute_modulus_of_commute ?_
  rw [((isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)).adjoint_eq,
    ← ContinuousLinearMap.mul_def, ← sq, commute_iff_eq, (U.sub_sq_mul_starProjection V).1,
    (U.sub_sq_mul_starProjection V).2]

/-- **Pythagorean identity.** On `U`, the squares of the cosine and sine angle operators add up
to the identity: `|P_V P_U|² + |P_U - P_V|² P_U = P_U`. -/
theorem cosAngleOperator_sq_add_sinAngleOperator_sq_mul_starProjection :
    U.cosAngleOperator V ^ 2 + U.sinAngleOperator V ^ 2 * U.starProjection = U.starProjection := by
  rw [cosAngleOperator_sq, sinAngleOperator_sq, (U.sub_sq_mul_starProjection V).1,
    add_sub_cancel]

/-- The compression of the sine angle operator to `U` is the modulus of the directed sine map:
`|P_U - P_V| P_U = |P_{Vᗮ} P_U|`. -/
theorem sinAngleOperator_mul_starProjection :
    U.sinAngleOperator V * U.starProjection = (U.sinThetaMap V).modulus := by
  have hc := U.commute_starProjection_sinAngleOperator V
  have hP := U.isIdempotentElem_starProjection.eq
  have hQ := Vᗮ.isIdempotentElem_starProjection.eq
  -- `|P_U - P_V| P_U = P_U |P_U - P_V| P_U` is positive and squares to `P_U P_{Vᗮ} P_U`.
  have hconj : U.sinAngleOperator V * U.starProjection =
      U.starProjection * (U.sinAngleOperator V * U.starProjection) := by
    rw [← mul_assoc, hc.eq, mul_assoc, hP]
  have hsq : U.sinAngleOperator V * U.starProjection * (U.sinAngleOperator V * U.starProjection) =
      U.sinAngleOperator V ^ 2 * U.starProjection := by
    rw [sq, mul_assoc, ← mul_assoc U.starProjection, hc.eq]
    simp only [mul_assoc, hP]
  refine eq_modulus_iff.2 ⟨hconj ▸ (U.isPositive_sinAngleOperator V).conj_starProjection U, ?_⟩
  rw [← ContinuousLinearMap.mul_def, hsq, sinAngleOperator_sq, (U.sub_sq_mul_starProjection V).1,
    sinThetaMap_def, adjoint_comp, (isSelfAdjoint_starProjection U).adjoint_eq,
    (isSelfAdjoint_starProjection Vᗮ).adjoint_eq]
  simp only [← ContinuousLinearMap.mul_def, mul_assoc]
  rw [← mul_assoc Vᗮ.starProjection, hQ, starProjection_orthogonal' V, sub_mul, one_mul, mul_sub,
    hP]

/-- The cosine and sine angle operators commute. -/
theorem commute_cosAngleOperator_sinAngleOperator :
    Commute (U.cosAngleOperator V) (U.sinAngleOperator V) := by
  have hQ : Commute V.starProjection (U.sinAngleOperator V) := by
    rw [← sinAngleOperator_comm]
    exact V.commute_starProjection_sinAngleOperator U
  have hP := U.commute_starProjection_sinAngleOperator V
  refine (commute_modulus_of_commute ?_).symm
  have h : (U.cosThetaMap V)† ∘L U.cosThetaMap V = U.cosAngleOperator V ^ 2 := by
    rw [sq, ContinuousLinearMap.mul_def, cosAngleOperator, modulus_comp_modulus]
  rw [h, cosAngleOperator_sq]
  exact ((hP.mul_left hQ).mul_left hP).symm

end Submodule
