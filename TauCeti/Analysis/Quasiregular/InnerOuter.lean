/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quasiregular.Euclidean
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Inner and outer inequalities of a Euclidean quasiregular map

Let `E` be a real inner product space of dimension `n`, `Ω ⊆ E` open and `f : E → E` with a weak
derivative `Du` on `Ω`. The *outer inequality* `‖Du‖ⁿ ≤ K det Du` defines Euclidean
`K`-quasiregularity (`TauCeti.IsQuasiregularOn`); the *inner inequality* is
`det Du ≤ K ℓ(Du)ⁿ`, with `ℓ` the minimal stretch (`LinearMap.minimalStretch`). This file proves
the comparison of Martio–Rickman–Väisälä (2.25) in the Euclidean setting, without the distortion
functions:

* `TauCeti.IsQuasiregularOn.det_le_pow_mul_minimalStretch_pow`: a Euclidean `K`-quasiregular map
  satisfies the inner inequality with constant `K ^ (n - 1)` (this is `K_I ≤ K_O ^ (n - 1)`);
* `TauCeti.IsQuasiregularOn.of_det_le_mul_minimalStretch_pow`: a quasiregular map satisfying the
  inner inequality with constant `K ≥ 1` is Euclidean `K ^ (n - 1)`-quasiregular (this is
  `K_O ≤ K_I ^ (n - 1)`).

Both follow from the pointwise statements `TauCeti.det_le_pow_mul_minimalStretch_pow_of_norm_pow_le`
and `TauCeti.norm_pow_le_pow_mul_det_of_det_le_mul_minimalStretch_pow`, which use the
singular-value bounds `|det A| ≤ ‖A‖ⁿ⁻¹ ℓ(A)` and `‖A‖ ℓ(A)ⁿ⁻¹ ≤ |det A|`
(`LinearMap.normDet_le_norm_pow_mul_minimalStretch`,
`LinearMap.norm_mul_minimalStretch_pow_le_normDet`). Where `det A ≤ 0`, the outer inequality
forces `A = 0`.

## References

* O. Martio, S. Rickman, J. Väisälä, *Definitions for quasiregular mappings*, Ann. Acad. Sci.
  Fenn. Ser. A I 448 (1969), (2.25).
-/

public section

open MeasureTheory Module TopologicalSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Outer to inner, pointwise.** If `‖A‖ⁿ ≤ K det A` with `0 ≤ K`, `n = dim E`, then
`det A ≤ K ^ (n - 1) ℓ(A)ⁿ`. -/
theorem det_le_pow_mul_minimalStretch_pow_of_norm_pow_le {K : ℝ} (hK : 0 ≤ K) {A : E →L[ℝ] E}
    (h : ‖A‖ ^ finrank ℝ E ≤ K * LinearMap.det (A : E →ₗ[ℝ] E)) :
    LinearMap.det (A : E →ₗ[ℝ] E) ≤
      K ^ (finrank ℝ E - 1) * (A : E →ₗ[ℝ] E).minimalStretch ^ finrank ℝ E := by
  have hℓ := (A : E →ₗ[ℝ] E).minimalStretch_nonneg
  rcases le_or_gt (LinearMap.det (A : E →ₗ[ℝ] E)) 0 with hd | hd
  · exact hd.trans (by positivity)
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · have : Subsingleton E := finrank_zero_iff (R := ℝ).1 h0
    simp [LinearMap.det_eq_one_of_subsingleton, h0]
  -- `det A ≤ ‖A‖ⁿ⁻¹ ℓ`, from the singular values.
  have hdℓ := (A : E →ₗ[ℝ] E).normDet_le_norm_pow_mul_minimalStretch hpos
  rw [LinearMap.normDet_eq_abs_det, abs_of_pos hd, LinearMap.toContinuousLinearMap_coe] at hdℓ
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
  rw [hm, Nat.add_sub_cancel] at hdℓ ⊢
  rw [hm] at h
  set d := LinearMap.det (A : E →ₗ[ℝ] E)
  set ℓ := (A : E →ₗ[ℝ] E).minimalStretch
  -- Raise to the power `m + 1` and use `‖A‖ᵐ⁺¹ ≤ K d`.
  have key : d ^ m * d ≤ d ^ m * (K ^ m * ℓ ^ (m + 1)) := by
    calc d ^ m * d = d ^ (m + 1) := (pow_succ d m).symm
      _ ≤ (‖A‖ ^ m * ℓ) ^ (m + 1) := pow_le_pow_left₀ hd.le hdℓ _
      _ = (‖A‖ ^ (m + 1)) ^ m * ℓ ^ (m + 1) := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring
      _ ≤ (K * d) ^ m * ℓ ^ (m + 1) := by gcongr
      _ = d ^ m * (K ^ m * ℓ ^ (m + 1)) := by ring
  exact le_of_mul_le_mul_left key (pow_pos hd _)

/-- **Inner to outer, pointwise.** If `‖A‖ⁿ ≤ K' det A` with `0 ≤ K'`, and `det A ≤ K ℓ(A)ⁿ`,
`n = dim E`, then `‖A‖ⁿ ≤ K ^ (n - 1) det A`. -/
theorem norm_pow_le_pow_mul_det_of_det_le_mul_minimalStretch_pow {K K' : ℝ}
    (hK' : 0 ≤ K') {A : E →L[ℝ] E}
    (hout : ‖A‖ ^ finrank ℝ E ≤ K' * LinearMap.det (A : E →ₗ[ℝ] E))
    (hin : LinearMap.det (A : E →ₗ[ℝ] E) ≤ K * (A : E →ₗ[ℝ] E).minimalStretch ^ finrank ℝ E) :
    ‖A‖ ^ finrank ℝ E ≤ K ^ (finrank ℝ E - 1) * LinearMap.det (A : E →ₗ[ℝ] E) := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · have : Subsingleton E := finrank_zero_iff (R := ℝ).1 h0
    simp [LinearMap.det_eq_one_of_subsingleton, h0]
  rcases le_or_gt (LinearMap.det (A : E →ₗ[ℝ] E)) 0 with hd | hd
  · -- The outer inequality forces `‖A‖ⁿ ≤ 0`, hence `A = 0` and `det A = 0`.
    have hA : ‖A‖ ^ finrank ℝ E ≤ 0 := hout.trans (mul_nonpos_of_nonneg_of_nonpos hK' hd)
    have hA0 : A = 0 :=
      norm_eq_zero.1 ((pow_eq_zero_iff hpos.ne').1 (le_antisymm hA (by positivity)))
    have hdet : LinearMap.det (A : E →ₗ[ℝ] E) = 0 := by
      rw [hA0, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
      exact zero_pow hpos.ne'
    rw [hdet, mul_zero]
    exact hA
  -- `‖A‖ ℓⁿ⁻¹ ≤ det A`, from the singular values.
  have hAℓ := (A : E →ₗ[ℝ] E).norm_mul_minimalStretch_pow_le_normDet
  rw [LinearMap.normDet_eq_abs_det, abs_of_pos hd, LinearMap.toContinuousLinearMap_coe] at hAℓ
  have hℓ := (A : E →ₗ[ℝ] E).minimalStretch_nonneg
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
  rw [hm, Nat.add_sub_cancel] at hAℓ ⊢
  rw [hm] at hin
  set d := LinearMap.det (A : E →ₗ[ℝ] E)
  set ℓ := (A : E →ₗ[ℝ] E).minimalStretch
  set N := ‖A‖ ^ (m + 1)
  -- `0 < d ≤ K ℓᵐ⁺¹` forces `0 < K`.
  have hK : 0 < K := pos_of_mul_pos_left (hd.trans_le hin) (pow_nonneg hℓ _)
  -- `N (d / K)ᵐ ≤ N ℓ^((m + 1) m) = (‖A‖ ℓᵐ)ᵐ⁺¹ ≤ dᵐ⁺¹`.
  have hdK : d / K ≤ ℓ ^ (m + 1) := (div_le_iff₀' hK).2 hin
  have key : N * (d / K) ^ m ≤ (K ^ m * d) * (d / K) ^ m := by
    calc N * (d / K) ^ m ≤ N * (ℓ ^ (m + 1)) ^ m := by gcongr
      _ = (‖A‖ * ℓ ^ m) ^ (m + 1) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (m + 1) m]
      _ ≤ d ^ (m + 1) := pow_le_pow_left₀ (by positivity) hAℓ _
      _ = (K ^ m * d) * (d / K) ^ m := by
        rw [div_pow]
        field_simp
        ring
  exact le_of_mul_le_mul_right key (by positivity)

variable [MeasurableSpace E] [BorelSpace E] {K K' : ℝ} {Ω : Opens E} {f : E → E}

/-- **`K_I ≤ K_O ^ (n - 1)`, Euclidean form.** If `f` is Euclidean `K`-quasiregular on `Ω`, then
every weak derivative `Du` of `f` on `Ω` satisfies the inner inequality
`det Du(x) ≤ K ^ (n - 1) ℓ(Du(x))ⁿ` for almost every `x ∈ Ω`, `n = dim E`. -/
theorem IsQuasiregularOn.det_le_pow_mul_minimalStretch_pow (hf : IsQuasiregularOn K Ω f)
    {Du : E → E →L[ℝ] E} (hDu : HasWeakFDerivOn volume Ω f Du) :
    ∀ᵐ x ∂volume.restrict (Ω : Set E), LinearMap.det (Du x : E →ₗ[ℝ] E) ≤
      K ^ (finrank ℝ E - 1) * (Du x : E →ₗ[ℝ] E).minimalStretch ^ finrank ℝ E := by
  filter_upwards [hf.ae_norm_pow_le_mul_det hDu] with x hx
  exact det_le_pow_mul_minimalStretch_pow_of_norm_pow_le (zero_le_one.trans hf.one_le) hx

/-- **`K_O ≤ K_I ^ (n - 1)`, Euclidean form.** If `f` is Euclidean quasiregular on `Ω` (for some
constant `K'`), `1 ≤ K`, and a weak derivative `Du` of `f` on `Ω` satisfies the inner inequality
`det Du(x) ≤ K ℓ(Du(x))ⁿ` for almost every `x ∈ Ω`, then `f` is Euclidean
`K ^ (n - 1)`-quasiregular on `Ω`, `n = dim E`. -/
theorem IsQuasiregularOn.of_det_le_mul_minimalStretch_pow (hf : IsQuasiregularOn K' Ω f)
    (hK : 1 ≤ K) {Du : E → E →L[ℝ] E} (hDu : HasWeakFDerivOn volume Ω f Du)
    (hin : ∀ᵐ x ∂volume.restrict (Ω : Set E),
      LinearMap.det (Du x : E →ₗ[ℝ] E) ≤ K * (Du x : E →ₗ[ℝ] E).minimalStretch ^ finrank ℝ E) :
    IsQuasiregularOn (K ^ (finrank ℝ E - 1)) Ω f := by
  refine (isQuasiregularOn_iff hDu).2 ⟨one_le_pow₀ hK, hf.continuousOn,
    hf.locallyIntegrableOn_norm_pow hDu, ?_⟩
  filter_upwards [hf.ae_norm_pow_le_mul_det hDu, hin] with x hout hx
  exact norm_pow_le_pow_mul_det_of_det_le_mul_minimalStretch_pow (zero_le_one.trans hf.one_le)
    hout hx

end TauCeti
