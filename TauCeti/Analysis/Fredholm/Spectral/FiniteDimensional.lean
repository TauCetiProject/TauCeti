/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Flow
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

/-!
# Spectral flow in finite dimension

On a finite-dimensional real or complex Hilbert space `H`, Phillips' spectral flow
`TauCeti.spectralFlow` of a continuous path `A` of self-adjoint operators on `[a, b]` is the
number of negative eigenvalues of `A a` minus that of `A b`, counted with multiplicity:

`spectralFlow A a b = n₋(A a) - n₋(A b)`,

where `n₋(T)` is the dimension of `Module.End.pointSpectralSubspace T (Iio 0)`, the sum of the
eigenspaces of `T` at negative eigenvalues. In particular the spectral flow only depends on the
endpoints of the path.

In finite dimension the count `TauCeti.spectralCount c T` of eigenvalues in `[0, c]` is the
dimension of the sum of the eigenspaces of `T` at eigenvalues in `[0, c]`, because the spectral
projection `cfc ((Icc 0 c).indicator 1) T` is the orthogonal projection onto it
(`ContinuousLinearMap.cfc_indicator_eq_starProjection`). Every `c` exceeding the norms of the
operators along `[a, b]` is a spectral cut of the whole path: `±c` are not in any spectrum, and
every spectral projection has finite rank. For such `c`, the eigenvalues in `[0, c]` are all the
nonnegative eigenvalues, so the count is `dim H - n₋`, and the spectral flow is the change of this
count from `a` to `b`.

## Main results

* `TauCeti.spectralCount_eq_finrank_pointSpectralSubspace`: in finite dimension, the count of
  eigenvalues in `[0, c]` is the dimension of the corresponding sum of eigenspaces.
* `TauCeti.isSpectralCutOn_of_forall_norm_lt`: in finite dimension, a bound `c` on the norms along
  a set of times is a spectral cut there.
* `TauCeti.spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank`: the spectral flow is the
  number of negative eigenvalues at the start minus that at the end.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Set

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace TauCeti

variable [FiniteDimensional 𝕜 H]

/-- In finite dimension, a positive `c` exceeding the norms of a path at every time of `s` is a
spectral cut of the path on `s`. -/
theorem isSpectralCutOn_of_forall_norm_lt {A : ℝ → H →L[𝕜] H} {c : ℝ} {s : Set ℝ} (hc : 0 < c)
    (hA : ∀ u ∈ s, ‖A u‖ < c) : IsSpectralCutOn A c s := by
  -- A real `r` with `‖T‖ < |r|` is not in the spectrum of `T`, since `‖1‖ ≤ 1`.
  have hnot {T : H →L[𝕜] H} {r : ℝ} (hr : ‖T‖ < |r|) : r ∉ spectrum ℝ T := fun h ↦ by
    have h₁ := spectrum.norm_le_norm_mul_of_mem h
    rw [Real.norm_eq_abs] at h₁
    exact (h₁.trans (mul_le_of_le_one_right (norm_nonneg T)
      (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := H)))).not_gt hr
  refine isSpectralCutOn_iff.2 ⟨hc, fun u hu ↦ ⟨hnot ?_, hnot ?_, inferInstance⟩⟩
  · rw [abs_neg, abs_of_pos hc]
    exact hA u hu
  · rw [abs_of_pos hc]
    exact hA u hu

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- In finite dimension, the number of eigenvalues of a self-adjoint operator `T` in `[0, c]` is
the dimension of the sum of the eigenspaces of `T` at the eigenvalues in `[0, c]`. -/
theorem spectralCount_eq_finrank_pointSpectralSubspace (c : ℝ) {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) :
    spectralCount c T =
      Module.finrank 𝕜 (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Icc 0 c)) := by
  rw [spectralCount_def, ContinuousLinearMap.cfc_indicator_eq_starProjection _ hT,
    Submodule.range_starProjection]

/-- For a self-adjoint operator `T` on a finite-dimensional space and `c > ‖T‖`, the number of
eigenvalues in `[0, c]` is the dimension of the space minus the number of negative eigenvalues. -/
private theorem spectralCount_eq_finrank_sub_finrank {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    {c : ℝ} (hc : ‖T‖ < c) :
    (spectralCount c T : ℤ) = Module.finrank 𝕜 H -
      Module.finrank 𝕜 (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Iio 0)) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  -- Up to eigenvalues of absolute value larger than `‖T‖`, which do not occur, the interval
  -- `[0, c]` selects the complement of the negative reals.
  have hΩ : Icc 0 c ∩ Metric.closedBall 0 ‖T‖ = (Iio 0)ᶜ ∩ Metric.closedBall 0 ‖T‖ := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_compl_iff, mem_Iio, not_lt, mem_closedBall_zero_iff,
      Real.norm_eq_abs]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, (le_abs_self x).trans (h.2.trans hc.le)⟩, h.2⟩⟩
  rw [spectralCount_eq_finrank_pointSpectralSubspace c hT,
    ← T.pointSpectralSubspace_inter_closedBall_norm, hΩ,
    T.pointSpectralSubspace_inter_closedBall_norm, ← hs.orthogonal_pointSpectralSubspace,
    ← (Module.End.pointSpectralSubspace (T : H →ₗ[𝕜] H) (Iio 0)).finrank_add_finrank_orthogonal]
  push_cast
  ring

/-- **Spectral flow in finite dimension.** On a finite-dimensional space, the spectral flow of a
continuous path `A` of self-adjoint operators from `a` to `b ≥ a` is the number of negative
eigenvalues of `A a` minus the number of negative eigenvalues of `A b`, counted with
multiplicity. -/
theorem spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank {A : ℝ → H →L[𝕜] H} {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) :
    spectralFlow A a b =
      (Module.finrank 𝕜 (Module.End.pointSpectralSubspace (A a : H →ₗ[𝕜] H) (Iio 0)) : ℤ) -
        Module.finrank 𝕜 (Module.End.pointSpectralSubspace (A b : H →ₗ[𝕜] H) (Iio 0)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hlt : ∀ t ∈ Icc a b, ‖A t‖ < max C 0 + 1 := fun t ht ↦
    (hC t ht).trans_lt (by linarith [le_max_left C 0])
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rw [spectralFlow_eq_of_isSpectralCutOn hab hA hsa
      (isSpectralCutOn_of_forall_norm_lt (by positivity) hlt),
    spectralCount_eq_finrank_sub_finrank (hsa b hb) (hlt b hb),
    spectralCount_eq_finrank_sub_finrank (hsa a ha) (hlt a ha)]
  ring

end TauCeti
