/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Overlap
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.FrameResidual

/-!
# Population-gap Frobenius sin-theta bound

The Yu--Wang--Samworth population-gap residual estimate bounds the squared
cross-block overlap of the ordered eigenbases of two symmetric operators.
The orthonormal-basis overlap formula identifies this with the squared
Frobenius sine of the corresponding selected subspaces.

Only the eigenvalues of the population operator are assumed separated. No spectral
gap is imposed on the perturbed operator. The frames select the same sorted
eigenvalue indices and may vary inside repeated eigenspaces. The canonical
ordered eigenbases give a specialization.

## Main results

* `LinearMap.IsSymmetric.sinThetaFrobenius_orderedEigenframe_le`: the bound for
  arbitrary ordered eigenframes, including repeated sample eigenvalues.
* `LinearMap.IsSymmetric.sinThetaFrobenius_eigenvectorSpan_le`: a population-gap
  estimate with the minimum of the rank-scaled operator norm and Frobenius norm
  of the perturbation.

## References

* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika 102 (2015), 315--323.
* AIQ-Kitware DKPS formalization, `YuWangSamworth2015/Core/Statistics.lean`
  (Kitware, Inc.; Apache-2.0).
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} {n : ℕ}

/-- **Population-gap sine theorem for arbitrary ordered eigenframes.**
The frames select the same sorted indices. Only the population eigenvalues
need a gap from the unselected indices; the perturbed frame may be any
orthonormal choice inside repeated sample eigenspaces.

Adapted from `yuWangSamworth_sinTheta_frame_le` in
`YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean`, Kitware DKPS
(Jon Crall and GPT 5.6 High; Apache-2.0). -/
theorem sinThetaFrobenius_orderedEigenframe_le
    {hA : A.IsSymmetric} {hB : B.IsSymmetric} {hn : finrank 𝕜 E = n}
    {ι : Type*} [Fintype ι] {e : ι ↪ Fin n} {u v : ι → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {δ : ℝ} (hd : 0 < δ)
    (hgap : ∀ (i : ι) (k : Fin n), k ∉ Set.range e →
      δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    (Submodule.span 𝕜 (Set.range u)).sinThetaFrobenius
        (Submodule.span 𝕜 (Set.range v)) ≤
      2 * min (Real.sqrt (Fintype.card ι) * ‖(B - A).toContinuousLinearMap‖)
        (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A)) / δ := by
  classical
  let U := Submodule.span 𝕜 (Set.range u)
  let V := Submodule.span 𝕜 (Set.range v)
  let s : Finset (Fin n) := Finset.univ.map e
  have hrange : Set.range e = (↑s : Set (Fin n)) := by ext k; simp [s]
  have hdim : finrank 𝕜 U = finrank 𝕜 V := hu.finrank_span.trans hv.finrank_span.symm
  have hsq : V.sinThetaFrobenius U ^ 2 =
      ∑ i, ∑ k ∈ sᶜ, ‖⟪hA.eigenvectorBasis hn k, v i⟫_𝕜‖ ^ 2 := by
    rw [V.sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal U
      (isOrderedEigenframe_iff.mp hv).orthonormal rfl]
    have hU : U = (hA.eigenvectorBasis hn).spanIndices (↑s : Set (Fin n)) :=
      (hu.span_eq_spanIndices hd hgap).trans (congrArg _ hrange)
    simp_rw [hU, OrthonormalBasis.norm_starProjection_orthogonal_spanIndices_sq]
  have hkey : δ ^ 2 * V.sinThetaFrobenius U ^ 2 ≤
      ∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2 := by
    rw [hsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦
      hA.sq_mul_sum_norm_inner_sq_le_norm_smul_sub_apply_sq hn hd.le ?_ (v i)
    intro k hk
    apply hgap i k
    rw [hrange]
    exact Finset.mem_compl.mp hk
  have key (C : ℝ) (hC : 0 ≤ C)
      (hSq : δ ^ 2 * V.sinThetaFrobenius U ^ 2 ≤ 4 * C ^ 2) :
      V.sinThetaFrobenius U ≤ 2 * C / δ := by
    rw [le_div_iff₀ hd]
    apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) hC)
    nlinarith
  have hfrob := hA.sum_sq_norm_frameResidual_le hB hn hv
  rw [← TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply
    (hA.eigenvectorBasis hn) (B - A)] at hfrob
  have hop := hA.sum_sq_norm_frameResidual_le_of_opNorm hB hn hv
    (fun x ↦ (B - A).toContinuousLinearMap.le_opNorm x)
  have hF := key _ (apply_nonneg (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E) _)
    (hkey.trans hfrob)
  have hO := key (Real.sqrt (Fintype.card ι) * ‖(B - A).toContinuousLinearMap‖) (by positivity)
    (hkey.trans (by
      simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι)), mul_assoc] using hop))
  rw [U.sinThetaFrobenius_comm V hdim]
  calc V.sinThetaFrobenius U ≤
      min (2 * (Real.sqrt (Fintype.card ι) * ‖(B - A).toContinuousLinearMap‖) / δ)
        (2 * TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A) / δ) := le_min hO hF
    _ = _ := by rw [min_div_div_right hd.le, ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]

/-! ### The population-gap estimate -/

/-- **Population-gap Frobenius sin-theta theorem.**
For the subspaces selected by the same indices in the canonical eigenbases of
symmetric operators `A` (population) and `B` (perturbed), a gap in the population
eigenvalues alone gives

`norm(sin Theta)_F <= 2 * min(sqrt(card s) * norm(B - A), norm(B - A)_F) / delta`.

No gap is required in the spectrum of `B`. The bases used are `eigenvectorBasis`;
other orthonormal eigenframes of `B` within repeated eigenspaces are not included. -/
theorem sinThetaFrobenius_eigenvectorSpan_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Finset (Fin n)) {delta : ℝ} (hd : 0 < delta)
    (hgap : ∀ j ∈ s, ∀ k ∉ s,
      delta ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    (hA.eigenvectorSpan hn (↑s : Set (Fin n))).sinThetaFrobenius
        (hB.eigenvectorSpan hn (↑s : Set (Fin n))) ≤
      2 * min (Real.sqrt s.card * ‖(B - A).toContinuousLinearMap‖)
        (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E (B - A)) / delta := by
  classical
  let e : s ↪ Fin n := Function.Embedding.subtype (· ∈ s)
  have hrange : Set.range e = (↑s : Set (Fin n)) := by ext k; simp [e]
  have h := sinThetaFrobenius_orderedEigenframe_le
    (isOrderedEigenframe_eigenvectorBasis hA hn e)
    (isOrderedEigenframe_eigenvectorBasis hB hn e) hd (fun i k hk ↦
      hgap (e i) i.property k (by simpa [hrange] using hk))
  simpa only [span_range_eigenvectorBasis_apply_eq_eigenvectorSpan, hrange,
    Fintype.card_coe] using h

end LinearMap.IsSymmetric
