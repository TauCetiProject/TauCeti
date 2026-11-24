/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.DvoretzkyRogers
public import TauCeti.Probability.Distributions.Uniform.Sphere.Norm

/-!
# The mean of a norm in John's position on a half-dimensional section

Let `T : E ≃L[ℝ] F` be a maximal-volume ellipsoid from an `n`-dimensional real inner product space
`E`, so that the norm `x ↦ ‖T x‖` on `E` is in John's position. By the Dvoretzky–Rogers lemma
(`ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_orthonormalBasis_forall_le_norm_apply`) there
are `m = ⌊n / 2⌋` orthonormal vectors `v₀, …, vₘ₋₁` with `‖T vᵢ‖ ≥ 1 / 4`. On their span `Y`,
identified with `ℓ²ₘ` through `u ↦ ∑ uᵢ vᵢ`, the mean of the norm over the Euclidean unit sphere is
therefore at least `√(log m / m) / 128`, by the Gaussian lower bound for spherical means of
`TauCeti.Probability.Distributions.Uniform.Sphere.Norm`.

This is the lower bound on `θ_Y = ∫ ‖x‖ dσ(x)` used in the proof of Dvoretzky's theorem: a
random `k`-dimensional subspace of `Y` is close to Euclidean for every `k` up to a small multiple
of `m θ_Y²`, which by this bound is at least a constant multiple of `log m`.

## Main declarations

* `exists_orthonormal_sqrt_log_div_le_integral_norm_apply`, in the namespace
  `ContinuousLinearEquiv.IsMaxVolumeEllipsoid`: there are `m = ⌊n / 2⌋` orthonormal
  vectors `vᵢ` with `‖T vᵢ‖ ≥ 1 / 4` and `√(log m / m) / 128 ≤ ∫ u, ‖T (∑ uᵢ • vᵢ)‖ dσ(u)` over the
  unit sphere of `ℓ²ₘ`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Lemma 13.3.5 and Theorem 13.3.7.
-/

public section

open MeasureTheory Metric Module TauCeti.Probability

namespace ContinuousLinearEquiv.IsMaxVolumeEllipsoid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {T : E ≃L[ℝ] F}

/-- **The mean norm on a Dvoretzky–Rogers section.** If `T` is a maximal-volume ellipsoid on a real
inner product space of dimension `n`, there are `m = ⌊n / 2⌋` orthonormal vectors `vᵢ` with
`1 / 4 ≤ ‖T vᵢ‖` such that the mean of `u ↦ ‖T (∑ uᵢ • vᵢ)‖` over the unit sphere of
`EuclideanSpace ℝ (Fin m)` is at least `√(log m / m) / 128`. For `n < 2` this is vacuous: then
`m = 0` and the bound is `0`. -/
theorem exists_orthonormal_sqrt_log_div_le_integral_norm_apply (hT : T.IsMaxVolumeEllipsoid) :
    ∃ v : Fin (finrank ℝ E / 2) → E, Orthonormal ℝ v ∧ (∀ i, 1 / 4 ≤ ‖T (v i)‖) ∧
      √(Real.log (finrank ℝ E / 2 : ℕ) / (finrank ℝ E / 2 : ℕ)) / 128 ≤
        ∫ u : sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E / 2))) 1, ‖T (∑ i, u.val i • v i)‖
          ∂uniformSphereMeasure (EuclideanSpace ℝ (Fin (finrank ℝ E / 2))) := by
  obtain ⟨b, hb⟩ := hT.exists_orthonormalBasis_forall_le_norm_apply
  -- The first `⌊n / 2⌋` vectors of the Dvoretzky–Rogers basis.
  set v : Fin (finrank ℝ E / 2) → E := fun i ↦ b (Fin.castLE (Nat.div_le_self _ 2) i)
  have hv (i : Fin (finrank ℝ E / 2)) : 1 / 4 ≤ ‖T (v i)‖ :=
    hb _ (by simp only [Fin.val_castLE]; omega)
  refine ⟨v, b.orthonormal.comp _ (Fin.castLE_injective _), hv, ?_⟩
  rcases Nat.eq_zero_or_pos (finrank ℝ E / 2) with hm | hm
  · have hm' : ((finrank ℝ E / 2 : ℕ) : ℝ) = 0 := by simp [hm]
    rw [hm', Real.log_zero, zero_div, Real.sqrt_zero, zero_div]
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have : Nonempty (Fin (finrank ℝ E / 2)) := ⟨⟨0, hm⟩⟩
  have h := mul_sqrt_log_card_div_le_integral_norm_sum_smul_uniformSphereMeasure
    (fun i ↦ T (v i)) (by norm_num) hv
  simp only [Fintype.card_fin] at h
  simp only [map_sum, map_smul]
  linarith

end ContinuousLinearEquiv.IsMaxVolumeEllipsoid
