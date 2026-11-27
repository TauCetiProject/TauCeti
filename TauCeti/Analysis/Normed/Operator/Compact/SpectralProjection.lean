/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Riesz
public import TauCeti.Analysis.Normed.Operator.Compact.Decomposition
import TauCeti.Analysis.Normed.Algebra.GelfandRadius
import TauCeti.Analysis.Normed.Operator.RangePow

/-!
# Riesz idempotents of compact operators

Let `T` be a compact operator on a Banach space and `μ` a nonzero scalar. The point `μ` is
isolated in the spectrum of `T`, so `{μ}` is a clopen part of the spectrum
(`IsCompactOperator.isClopen_setOf_coe_eq`); it is empty when `μ` is not a spectral value.

Over `ℂ`, the Riesz idempotent of this part, defined by the holomorphic calculus as the contour
integral `(2πi)⁻¹ ∫_Γ (z - T)⁻¹ dz` over a small circle `Γ` around `μ`, is the coordinate
projection of the stable Riesz splitting of `T - μ`
(`IsCompactOperator.exists_projection_ker_range_pow_sub_smul`). Its range is the stable kernel
and its kernel is the stable range of the powers of `T - μ`
(`IsCompactOperator.exists_forall_range_rieszIdempotent_eq_ker_pow`). The proof checks that the
coordinate projection `P` satisfies the characterization `TauCeti.rieszIdempotent_eq_iff`:
`T - μ` is nilpotent on the range of `P` and invertible on its kernel.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4 and VII.7.
-/

public section

open Filter Topology TopologicalSpace TauCeti

namespace IsCompactOperator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {T : E →L[ℂ] E}

/-- **The Riesz idempotent of a nonzero point of the spectrum of a compact operator.** For a
compact operator `T` on a complex Banach space and `μ ≠ 0`, the Riesz idempotent of the part
`{μ}` of the spectrum is the coordinate projection of the stable Riesz splitting of `T - μ`: from
some power on, its range is the kernel and its kernel is the range of the powers of `T - μ`.
When `μ` is not a spectral value, both sides are trivial. -/
theorem exists_forall_range_rieszIdempotent_eq_ker_pow (hT : IsCompactOperator T) {μ : ℂ}
    (hμ : μ ≠ 0) {K : Clopens (spectrum ℂ T)} (hK : ∀ x : spectrum ℂ T, x ∈ K ↔ (x : ℂ) = μ) :
    ∃ p : ℕ, ∀ n, p ≤ n →
      (rieszIdempotent T K).range =
          LinearMap.ker (((T - μ • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) ^ n) ∧
        (rieszIdempotent T K).ker =
          LinearMap.range (((T - μ • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) ^ n) := by
  obtain ⟨p, P, hP, hPT, hPn⟩ := hT.exists_projection_ker_range_pow_sub_smul hμ
  suffices h : rieszIdempotent T K = P from ⟨p, fun n hn ↦ h ▸ hPn n hn⟩
  set g : E →L[ℂ] E := T - μ • 1
  obtain ⟨hr, hk'⟩ := hPn (p + 1) p.le_succ
  have hgP : Commute g P := hPT.symm.sub_left ((Commute.one_left P).smul_left μ)
  have hc : algebraMap ℂ (E →L[ℂ] E) μ - T = -g := by
    simp [g, Algebra.algebraMap_eq_smul_one]
  -- `g` is invertible on the kernel of `P`; multiplying by the involution `P - (1 - P)` flips
  -- the sign of `g (1 - P)`.
  have hU := ContinuousLinearMap.isUnit_mul_one_sub_add_of_stable hP hgP hr hk'
  have hinv : (P - (1 - P)) * (P - (1 - P)) = 1 := by
    simp [mul_sub, sub_mul, hP.eq]
  have hneg : -g * (1 - P) + P = (g * (1 - P) + P) * (P - (1 - P)) := by
    simp [mul_sub, sub_mul, add_mul, mul_assoc, hP.eq]
    abel
  refine (rieszIdempotent_eq_iff T hK).mpr
    ⟨hP, hPT, ?_, hc ▸ hneg ▸ hU.mul ⟨⟨_, _, hinv, hinv⟩, rfl⟩⟩
  -- `(μ - T) P = -g P` is nilpotent, hence quasinilpotent.
  have hnil : (g * P) ^ (p + 1) = 0 := by
    rw [hgP.mul_pow, hP.pow_succ_eq]
    ext x
    have hx : P x ∈ LinearMap.ker ((g : E →ₗ[ℂ] E) ^ (p + 1)) :=
      hr ▸ LinearMap.mem_range_self (P : E →ₗ[ℂ] E) x
    simpa [← ContinuousLinearMap.toLinearMap_pow] using hx
  rw [hc, neg_mul, spectralRadius_eq_zero_iff_gelfandRadius_eq_zero, gelfandRadius_neg]
  exact IsNilpotent.gelfandRadius_eq_zero ⟨p + 1, hnil⟩

end IsCompactOperator
