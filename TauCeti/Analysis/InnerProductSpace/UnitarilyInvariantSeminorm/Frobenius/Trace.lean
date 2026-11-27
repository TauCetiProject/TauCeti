/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Symmetric.Projection
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Trace

/-!
# The Frobenius seminorm through traces

For linear maps `A B : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
Hilbert–Schmidt inner product of `A` and `B` is the trace `tr (A† B)`, and the Frobenius seminorm
`‖A‖_F` of `TauCeti.UnitarilyInvariantSeminorm.frobenius` is its square root on the diagonal. This
file records that identity, the Cauchy–Schwarz inequality `‖tr (A† B)‖ ≤ ‖A‖_F ‖B‖_F`, and the
behaviour of `‖·‖_F` under orthogonal projections, the tools for second-moment arguments with
linear maps.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_eq_trace`: `‖A‖_F² = tr (A† A)`.
* `TauCeti.UnitarilyInvariantSeminorm.norm_trace_adjoint_comp_le`: Cauchy–Schwarz,
  `‖tr (A† B)‖ ≤ ‖A‖_F ‖B‖_F`.
* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_starProjection`: the orthogonal projection onto
  `U` has `‖pr_U‖_F² = dim U`.
* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_comp_starProjection` and
  `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_starProjection_comp`: `‖A pr_U‖_F²` and
  `‖pr_U Y‖_F²` as the Hilbert–Schmidt inner products `tr (pr_U† (A† A))` and `tr (pr_U† (Y Y†))`.
* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_eq_sq_frobenius_add_sq_frobenius`: an
  orthogonal projection `p` splits `‖A‖_F² = ‖p A‖_F² + ‖(1 - p) A‖_F²`.
* `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_one_sub_mul_comp_le`: for an orthogonal
  projection `p` and any endomorphism `q`, `‖(1 - p q) A‖_F² ≤ ‖(1 - p) A‖_F² + ‖(1 - q) A‖_F²`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* `sq_frobenius_one_sub_mul_comp_le` is adapted from grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), file
  `src/New/Spanning/SecondMoment/FewTranslates.lean`,
  `New.hilbertSchmidtNorm_one_sub_mul_comp_sq_le`.
-/

public section

open Module LinearMap

open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The Frobenius seminorm through the trace**: `‖A‖_F² = tr (A† A)`. -/
theorem sq_frobenius_eq_trace (A : E →ₗ[𝕜] F) :
    ((frobenius 𝕜 E F A ^ 2 : ℝ) : 𝕜) = trace 𝕜 E (A.adjoint ∘ₗ A) := by
  rw [A.trace_adjoint_comp_self_eq_sum_norm_apply_sq (stdOrthonormalBasis 𝕜 E),
    sq_frobenius_apply (stdOrthonormalBasis 𝕜 E)]

/-- The real part of `tr (A† A)` is `‖A‖_F²`. -/
theorem sq_frobenius_eq_re_trace (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A ^ 2 = RCLike.re (trace 𝕜 E (A.adjoint ∘ₗ A)) := by
  rw [← sq_frobenius_eq_trace, RCLike.ofReal_re]

/-- **Cauchy–Schwarz for the Hilbert–Schmidt inner product**: `‖tr (A† B)‖ ≤ ‖A‖_F ‖B‖_F`. -/
theorem norm_trace_adjoint_comp_le (A B : E →ₗ[𝕜] F) :
    ‖trace 𝕜 E (A.adjoint ∘ₗ B)‖ ≤ frobenius 𝕜 E F A * frobenius 𝕜 E F B := by
  set b := stdOrthonormalBasis 𝕜 E
  rw [A.trace_adjoint_comp_eq_sum_inner b, frobenius_apply b, frobenius_apply b]
  calc ‖∑ i, ⟪A (b i), B (b i)⟫_𝕜‖ ≤ ∑ i, ‖A (b i)‖ * ‖B (b i)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_inner_le_norm _ _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The real part of the Hilbert–Schmidt inner product is at most `‖A‖_F ‖B‖_F`. -/
theorem re_trace_adjoint_comp_le (A B : E →ₗ[𝕜] F) :
    RCLike.re (trace 𝕜 E (A.adjoint ∘ₗ B)) ≤ frobenius 𝕜 E F A * frobenius 𝕜 E F B :=
  (RCLike.re_le_norm _).trans (norm_trace_adjoint_comp_le A B)

omit [FiniteDimensional 𝕜 F] in
/-- The squared Frobenius seminorm of the orthogonal projection onto `U` is `dim U`. -/
theorem sq_frobenius_starProjection (U : Submodule 𝕜 E) :
    frobenius 𝕜 E E (U.starProjection : E →ₗ[𝕜] E) ^ 2 = finrank 𝕜 U := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [sq_frobenius_eq_trace, U.isSymmetricProjection_starProjection.isSymmetric.adjoint_eq,
    U.starProjection_toLinearMap_comp_self, U.trace_starProjection, RCLike.ofReal_natCast]

/-- The squared Frobenius seminorm of `A pr_U` is the Hilbert–Schmidt inner product of `pr_U` with
`A† A`: `‖A pr_U‖_F² = tr (pr_U† (A† A))`. -/
theorem sq_frobenius_comp_starProjection (A : E →ₗ[𝕜] F) (U : Submodule 𝕜 E) :
    ((frobenius 𝕜 E F (A ∘ₗ (U.starProjection : E →ₗ[𝕜] E)) ^ 2 : ℝ) : 𝕜) =
      trace 𝕜 E ((U.starProjection : E →ₗ[𝕜] E).adjoint ∘ₗ (A.adjoint ∘ₗ A)) := by
  have hU := U.isSymmetricProjection_starProjection
  rw [sq_frobenius_eq_trace, adjoint_comp, hU.isSymmetric.adjoint_eq, comp_assoc,
    trace_comp_comm', comp_assoc, comp_assoc, U.starProjection_toLinearMap_comp_self,
    ← comp_assoc, trace_comp_comm']

/-- The squared Frobenius seminorm of `pr_U Y` is the Hilbert–Schmidt inner product of `pr_U` with
`Y Y†`: `‖pr_U Y‖_F² = tr (pr_U† (Y Y†))`. -/
theorem sq_frobenius_starProjection_comp (U : Submodule 𝕜 F) (Y : E →ₗ[𝕜] F) :
    ((frobenius 𝕜 E F ((U.starProjection : F →ₗ[𝕜] F) ∘ₗ Y) ^ 2 : ℝ) : 𝕜) =
      trace 𝕜 F ((U.starProjection : F →ₗ[𝕜] F).adjoint ∘ₗ (Y ∘ₗ Y.adjoint)) := by
  have hU := U.isSymmetricProjection_starProjection
  rw [sq_frobenius_eq_trace, adjoint_comp, hU.isSymmetric.adjoint_eq, comp_assoc,
    ← comp_assoc Y, U.starProjection_toLinearMap_comp_self, trace_comp_comm',
    comp_assoc]

omit [FiniteDimensional 𝕜 F] in
/-- Restricting to a subspace does not increase the Frobenius seminorm:
`‖A pr_U‖_F ≤ ‖A‖_F`. -/
theorem frobenius_comp_starProjection_le [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F)
    (U : Submodule 𝕜 E) :
    frobenius 𝕜 E F (A ∘ₗ (U.starProjection : E →ₗ[𝕜] E)) ≤ frobenius 𝕜 E F A := by
  rw [← frobenius_adjoint, ← frobenius_adjoint A, adjoint_comp,
    (U.isSymmetricProjection_starProjection).isSymmetric.adjoint_eq]
  exact frobenius_le_frobenius_of_norm_le fun x ↦ U.norm_starProjection_apply_le (A.adjoint x)

omit [FiniteDimensional 𝕜 F] in
/-- **Pythagoras for the Frobenius seminorm.** An orthogonal projection `p` of the target splits
`‖A‖_F² = ‖p A‖_F² + ‖(1 - p) A‖_F²`. -/
theorem sq_frobenius_eq_sq_frobenius_add_sq_frobenius {p : F →ₗ[𝕜] F}
    (hp : p.IsSymmetricProjection) (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F A ^ 2 = frobenius 𝕜 E F (p ∘ₗ A) ^ 2 + frobenius 𝕜 E F ((1 - p) ∘ₗ A) ^ 2 := by
  simp only [sq_frobenius_apply (stdOrthonormalBasis 𝕜 E), ← Finset.sum_add_distrib, comp_apply]
  exact Finset.sum_congr rfl fun i _ ↦ hp.norm_sq_eq_add_norm_sq _

omit [FiniteDimensional 𝕜 F] in
/-- For an orthogonal projection `p` and any endomorphism `q` of the target: in squared Frobenius
seminorm, the part `(1 - p q) A` that `p q` misses is at most the sum of the parts that `p` and `q`
miss. -/
theorem sq_frobenius_one_sub_mul_comp_le {p : F →ₗ[𝕜] F} (hp : p.IsSymmetricProjection)
    (q : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F ((1 - p * q) ∘ₗ A) ^ 2 ≤
      frobenius 𝕜 E F ((1 - p) ∘ₗ A) ^ 2 +
        frobenius 𝕜 E F ((1 - q) ∘ₗ A) ^ 2 := by
  simp only [sq_frobenius_apply (stdOrthonormalBasis 𝕜 E), ← Finset.sum_add_distrib, comp_apply]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  generalize A (stdOrthonormalBasis 𝕜 E i) = y
  -- Split `1 - p q` into the orthogonal parts `p (1 - q)` and `1 - p`.
  have h_range : p * (1 - p * q) = p * (1 - q) := by
    simp [mul_sub, ← mul_assoc, hp.isIdempotentElem.eq]
  have h_ker : (1 - p) * (1 - p * q) = 1 - p := by
    simp [mul_sub, ← mul_assoc, hp.isIdempotentElem.one_sub_mul_self]
  have h_split : ‖(1 - p * q) y‖ ^ 2 = ‖p ((1 - q) y)‖ ^ 2 + ‖(1 - p) y‖ ^ 2 := by
    rw [hp.norm_sq_eq_add_norm_sq, ← mul_apply_eq_comp,
      ← mul_apply_eq_comp (1 - p), h_range, h_ker, mul_apply_eq_comp]
  have h_contract : ‖p ((1 - q) y)‖ ^ 2 ≤ ‖(1 - q) y‖ ^ 2 := by
    linarith [hp.norm_sq_eq_add_norm_sq ((1 - q) y),
      sq_nonneg ‖(1 - p) ((1 - q) y)‖]
  linarith

end TauCeti.UnitarilyInvariantSeminorm
