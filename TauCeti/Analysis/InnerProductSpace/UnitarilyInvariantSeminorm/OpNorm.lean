/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic

/-!
# The operator norm as a unitarily invariant seminorm

On linear maps `A : E →ₗ[𝕜] F` out of a finite-dimensional inner product space, every linear map
is continuous, and the operator norm `‖A‖` of the continuous linear map
`LinearMap.toContinuousLinearMap A` is a seminorm on `E →ₗ[𝕜] F`. Composing with unitaries of the
source or the target does not change it, so it is a unitarily invariant seminorm. Only the source
needs to be finite-dimensional for the seminorm definition; orthogonal maximality additionally
assumes a finite-dimensional codomain.

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm.opNorm`: the operator norm as a unitarily invariant
  seminorm on `E →ₗ[𝕜] F`.
* `TauCeti.UnitarilyInvariantSeminorm.opNorm_apply`: its value is the operator norm of the
  associated continuous linear map.
* `TauCeti.UnitarilyInvariantSeminorm.opNorm_apply_adjoint_comp_self`: the C⋆-identity
  `‖A† A‖ = ‖A‖²`.
* `TauCeti.UnitarilyInvariantSeminorm.opNorm_add_eq_max_of_twoSidedOrthogonal`: for
  finite-dimensional source and target, if `A† B = 0` and `A B† = 0`, then
  `‖A + B‖ = max ‖A‖ ‖B‖`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
-/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The **operator norm** `A ↦ ‖A‖` on linear maps out of a finite-dimensional inner product
space, as a unitarily invariant seminorm. -/
noncomputable def opNorm : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := (normSeminorm 𝕜 (E →L[𝕜] F)).comp LinearMap.toContinuousLinearMap.toLinearMap
  map_linearIsometryEquiv_comp_comp' U V A := by
    have h : LinearMap.toContinuousLinearMap ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) =
        (U : F →L[𝕜] F).comp ((LinearMap.toContinuousLinearMap A).comp (V : E →L[𝕜] E)) := by
      ext; simp
    simp only [Seminorm.comp_apply, coe_normSeminorm, LinearEquiv.coe_coe, h]
    rcases subsingleton_or_nontrivial E with hE | _
    · simp [Subsingleton.elim (LinearMap.toContinuousLinearMap A) 0]
    · simp

variable {𝕜 E F}

/-- The operator-norm seminorm evaluates to the operator norm of the associated continuous linear
map. -/
@[simp]
theorem opNorm_apply (A : E →ₗ[𝕜] F) : opNorm 𝕜 E F A = ‖LinearMap.toContinuousLinearMap A‖ :=
  (rfl)

/-- The operator norm of the Gram operator `A† A` is the square of the operator norm of `A`. -/
theorem opNorm_apply_adjoint_comp_self [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) :
    opNorm 𝕜 E E (LinearMap.adjoint A ∘ₗ A) = opNorm 𝕜 E F A ^ 2 := by
  have := FiniteDimensional.completeSpace 𝕜 E
  have := FiniteDimensional.completeSpace 𝕜 F
  have h : LinearMap.toContinuousLinearMap (LinearMap.adjoint A ∘ₗ A) =
      (LinearMap.toContinuousLinearMap A).adjoint ∘L LinearMap.toContinuousLinearMap A :=
    ContinuousLinearMap.ext fun x ↦ by simp [LinearMap.adjoint_eq_toCLM_adjoint]
  rw [opNorm_apply, opNorm_apply, h, ContinuousLinearMap.norm_adjoint_comp_self, sq]

open scoped InnerProductSpace in
/-- **Orthogonal maximality of the operator norm**: between finite-dimensional inner product
spaces, if `A† B = 0` and `A B† = 0`, then `‖A + B‖ = max ‖A‖ ‖B‖`. -/
theorem opNorm_add_eq_max_of_twoSidedOrthogonal [FiniteDimensional 𝕜 F] {A B : E →ₗ[𝕜] F}
    (h₁ : LinearMap.adjoint A ∘ₗ B = 0) (h₂ : A ∘ₗ LinearMap.adjoint B = 0) :
    opNorm 𝕜 E F (A + B) = max (opNorm 𝕜 E F A) (opNorm 𝕜 E F B) := by
  -- Split the domain along `V = range A†` and `Vᗮ = ker A`: `A` lives on `V` and `B` lives on `Vᗮ`.
  let V : Submodule 𝕜 E := LinearMap.range (LinearMap.adjoint A)
  have hV_orth : Vᗮ = LinearMap.ker A := by
    dsimp only [V]
    rw [← LinearMap.orthogonal_ker, Submodule.orthogonal_orthogonal]
  have hA_orth (x : E) : A (Vᗮ.starProjection x) = 0 :=
    LinearMap.mem_ker.mp (hV_orth ▸ Vᗮ.starProjection_apply_mem x)
  have hBA : B ∘ₗ LinearMap.adjoint A = 0 :=
    LinearMap.comp_adjoint_eq_zero_comm.mp h₂
  have hB_proj (x : E) : B (V.starProjection x) = 0 := by
    obtain ⟨y, hy⟩ := V.starProjection_apply_mem x
    exact hy ▸ LinearMap.congr_fun hBA y
  have hA_proj (x : E) : A (V.starProjection x) = A x := by
    conv_rhs => rw [← V.starProjection_add_starProjection_orthogonal x, map_add, hA_orth, add_zero]
  have hB_orth (x : E) : B (Vᗮ.starProjection x) = B x := by
    conv_rhs => rw [← V.starProjection_add_starProjection_orthogonal x, map_add, hB_proj, zero_add]
  have hAB_inner (x : E) : ⟪A x, B x⟫_𝕜 = 0 := by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, h₁, LinearMap.zero_apply,
      inner_zero_right]
  have hcompV : (A + B) ∘ₗ (V.starProjection : E →ₗ[𝕜] E) = A := by
    ext x
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.add_apply,
      hA_proj, hB_proj, add_zero]
  have hcompV_orth : (A + B) ∘ₗ (Vᗮ.starProjection : E →ₗ[𝕜] E) = B := by
    ext x
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.add_apply,
      hA_orth, hB_orth, zero_add]
  refine le_antisymm ?_ (max_le
    (by simpa only [hcompV] using (opNorm 𝕜 E F).map_comp_starProjection_le V (A + B))
    (by simpa only [hcompV_orth] using (opNorm 𝕜 E F).map_comp_starProjection_le Vᗮ (A + B)))
  -- Upper bound via Pythagoras on both the codomain (`A x ⊥ B x`) and the domain (`V ⊥ Vᗮ`).
  set M := max (opNorm 𝕜 E F A) (opNorm 𝕜 E F B)
  have hM : 0 ≤ M := le_max_of_le_left (apply_nonneg _ A)
  have h_proj_le (T : E →ₗ[𝕜] F) (U : Submodule 𝕜 E)
      (hT : ∀ x, T (U.starProjection x) = T x) (x : E) :
      ‖T x‖ ≤ opNorm 𝕜 E F T * ‖U.starProjection x‖ := by
    rw [← hT x, ← LinearMap.coe_toContinuousLinearMap' T, opNorm_apply]
    exact (LinearMap.toContinuousLinearMap T).le_opNorm (U.starProjection x)
  rw [opNorm_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hA_le : ‖A x‖ ≤ M * ‖V.starProjection x‖ :=
    (h_proj_le A V hA_proj x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hB_le : ‖B x‖ ≤ M * ‖Vᗮ.starProjection x‖ :=
    (h_proj_le B Vᗮ hB_orth x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hsq : ‖LinearMap.toContinuousLinearMap (A + B) x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    calc ‖LinearMap.toContinuousLinearMap (A + B) x‖ ^ 2
        = ‖A x + B x‖ ^ 2 := by rw [LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply]
      _ = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
          simpa only [sq] using
            norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (A x) (B x) (hAB_inner x)
      _ ≤ (M * ‖V.starProjection x‖) ^ 2 + (M * ‖Vᗮ.starProjection x‖) ^ 2 :=
          add_le_add (pow_le_pow_left₀ (norm_nonneg _) hA_le 2)
            (pow_le_pow_left₀ (norm_nonneg _) hB_le 2)
      _ = M ^ 2 * (‖V.starProjection x‖ ^ 2 + ‖Vᗮ.starProjection x‖ ^ 2) := by ring
      _ = M ^ 2 * ‖x‖ ^ 2 := by rw [← V.norm_sq_eq_add_norm_sq_starProjection x]
      _ = (M * ‖x‖) ^ 2 := by ring
  exact le_of_sq_le_sq hsq (mul_nonneg hM (norm_nonneg x))

end TauCeti.UnitarilyInvariantSeminorm
