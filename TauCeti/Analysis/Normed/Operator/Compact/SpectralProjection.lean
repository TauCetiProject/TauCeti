/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Riesz
public import TauCeti.Analysis.Normed.Operator.Compact.Decomposition
import TauCeti.Analysis.Normed.Operator.Compact.Spectrum

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

/-- For a compact operator on a Banach space and a nonzero scalar `μ`, the points of the spectrum
equal to `μ` form a clopen part of the spectrum, empty when `μ` is not a spectral value. -/
theorem isClopen_setOf_coe_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsCompactOperator T) {μ : 𝕜}
    (hμ : μ ≠ 0) : IsClopen {x : spectrum 𝕜 T | (x : 𝕜) = μ} := by
  refine ⟨isClosed_eq continuous_subtypeVal continuous_const,
    isOpen_iff_mem_nhds.mpr fun x (hx : (x : 𝕜) = μ) ↦ ?_⟩
  have h : ∀ᶠ y in 𝓝 μ, ¬(y ≠ μ ∧ y ∈ spectrum 𝕜 T) :=
    not_frequently.mp fun h ↦ hμ (hT.eq_zero_of_accPt_spectrum (accPt_iff_frequently.mpr h))
  rw [← hx] at h
  filter_upwards [(continuous_subtypeVal.tendsto x).eventually h] with y hy
  by_contra hne
  exact hy ⟨fun h ↦ hne (h.trans hx), y.property⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {T : E →L[ℂ] E}

/-- Let `P` be an idempotent commuting with `g` whose range is the kernel of `g ^ (p + 1)` and
whose kernel is the range of both `g ^ p` and `g ^ (p + 1)`. Then `g` is invertible on the kernel
of `P`: the operator `-g (1 - P) + P` is invertible. -/
private theorem isUnit_neg_mul_one_sub_add {g P : E →L[ℂ] E} {p : ℕ} (hP : IsIdempotentElem P)
    (hgP : Commute g P) (hr : LinearMap.range (P : E →ₗ[ℂ] E) =
      LinearMap.ker ((g : E →ₗ[ℂ] E) ^ (p + 1)))
    (hk : LinearMap.ker (P : E →ₗ[ℂ] E) = LinearMap.range ((g : E →ₗ[ℂ] E) ^ p))
    (hk' : LinearMap.ker (P : E →ₗ[ℂ] E) = LinearMap.range ((g : E →ₗ[ℂ] E) ^ (p + 1))) :
    IsUnit (-g * (1 - P) + P) := by
  have hPP (x : E) : P (P x) = P x := congr($(hP.eq) x)
  have hPg (x : E) : P (g x) = g (P x) := congr($(hgP.eq) x).symm
  have happly (x : E) : (-g * (1 - P) + P) x = -g (x - P x) + P x := by simp
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · rw [happly] at hx
    have hPx : P x = 0 := by
      have h := congr(P $hx)
      rwa [map_add, map_neg, hPg, map_sub, hPP, sub_self, map_zero, neg_zero, zero_add,
        map_zero] at h
    rw [hPx, sub_zero, add_zero, neg_eq_zero] at hx
    have hmem : x ∈ LinearMap.ker ((g : E →ₗ[ℂ] E) ^ (p + 1)) := by
      rw [LinearMap.mem_ker, pow_succ, mul_apply_eq_comp]
      simp [hx]
    obtain ⟨z, rfl⟩ := hr ▸ hmem
    simpa [hPP] using hPx
  · have hy : y - P y ∈ LinearMap.range ((g : E →ₗ[ℂ] E) ^ (p + 1)) := by
      rw [← hk', LinearMap.mem_ker]
      simp [hPP]
    obtain ⟨z, hz⟩ := hy
    set u := ((g : E →ₗ[ℂ] E) ^ p) z
    have hu : P u = 0 := by
      have h : u ∈ LinearMap.ker (P : E →ₗ[ℂ] E) := hk ▸ LinearMap.mem_range_self _ z
      simpa using h
    have hgu : g u = y - P y := by
      rw [← hz, pow_succ', mul_apply_eq_comp]
      rfl
    have hPu : P (P y - u) = P y := by rw [map_sub, hPP, hu, sub_zero]
    refine ⟨P y - u, ?_⟩
    rw [happly, hPu, sub_sub_cancel_left, map_neg, neg_neg, hgu, sub_add_cancel]

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
  refine (rieszIdempotent_eq_iff T hK).mpr
    ⟨hP, hPT, ?_, hc ▸ isUnit_neg_mul_one_sub_add hP hgP hr (hPn p le_rfl).2 hk'⟩
  -- `(μ - T) P = -g P` is nilpotent, hence quasinilpotent.
  have hnil : (g * P) ^ (p + 1) = 0 := by
    rw [hgP.mul_pow, hP.pow_succ_eq]
    ext x
    have hx : P x ∈ LinearMap.ker ((g : E →ₗ[ℂ] E) ^ (p + 1)) :=
      hr ▸ LinearMap.mem_range_self (P : E →ₗ[ℂ] E) x
    simpa [← ContinuousLinearMap.toLinearMap_pow] using hx
  have hrad : gelfandRadius (-(g * P)) = 0 := by
    have h := gelfandRadius_pow_of_ne_zero (-(g * P)) p.succ_ne_zero
    rwa [neg_pow, hnil, mul_zero, gelfandRadius_zero, eq_comm,
      pow_eq_zero_iff p.succ_ne_zero] at h
  rw [hc, neg_mul, spectrum.spectralRadius_eq_gelfandRadius, hrad, ENNReal.ofReal_zero]

end IsCompactOperator
