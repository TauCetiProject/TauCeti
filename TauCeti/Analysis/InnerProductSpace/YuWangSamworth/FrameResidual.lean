/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.YuWangSamworth.Basic
public import TauCeti.Analysis.InnerProductSpace.Spectral.Eigenframe

/-!
# Population-gap residuals for arbitrary ordered eigenframes

The perturbed frame may be chosen freely inside repeated eigenspaces.
The squared residuals using population eigenvalues are bounded by four times
both the squared Frobenius perturbation and the dimension-scaled squared
operator perturbation. Frames may use any finite index type; the pointwise
residual identity needs no finiteness assumption on the indices.
No gap in the perturbed spectrum is required.

Adapted from `YuWangSamworth2015/YuWangSamworth2015/Core/Residual.lean` in
[AIQ-Kitware DKPS](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware 2026; Apache-2.0; Jon Crall and GPT 5.6 High).

## References

* Y. Yu, T. Wang and R. J. Samworth, *A useful variant of the Davis–Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315–323.
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ι : Type*} {T S : E →ₗ[𝕜] E}

/-- **The frame residual as a perturbation column.**
`λ_{e i}(T) wᵢ − T wᵢ = (S − T) wᵢ − (λ_{e i}(S) − λ_{e i}(T)) wᵢ`, using only the
eigenvalue equation of the frame. -/
theorem frameResidual_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : ι ↪ Fin n} {w : ι → E}
    (hw : IsOrderedEigenframe hS hn e w) (i : ι) :
    (hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)
      = (S - T) (w i)
        - ((hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i) : ℝ) : 𝕜) • w i := by
  rw [LinearMap.sub_apply, (isOrderedEigenframe_iff.mp hw).apply_eq i]
  push_cast
  module

/-- **Frame residual, Frobenius branch.**  `∑ᵢ ‖Rᵢ‖² ≤ 4 ‖S − T‖²_F` for an
arbitrary ordered eigenframe `w` of `S`: the perturbation columns are bounded by
orthonormal compression and the eigenvalue displacement by Hoffman--Wielandt,
each by `‖S − T‖²_F`. -/
theorem sum_sq_norm_frameResidual_le [Fintype ι] (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : ι ↪ Fin n} {w : ι → E}
    (hw : IsOrderedEigenframe hS hn e w) :
    ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ 4 * ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  set frob := ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 with hfrob
  -- The two halves, each bounded by the Frobenius norm.
  have hcols : ∑ i, ‖(S - T) (w i)‖ ^ 2 ≤ frob :=
    (S - T).sum_sq_norm_apply_orthonormal_le (hT.eigenvectorBasis hn)
      (isOrderedEigenframe_iff.mp hw).orthonormal
  have hHW : ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 ≤ frob := by
    have heigs : ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 ≤
        ∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2 :=
      Finset.sum_le_sum_of_injOn e e.injective.injOn (Finset.subset_univ _)
        (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ sq_nonneg _)
    refine heigs.trans ?_
    rw [show (∑ j, (hS.eigenvalues hn j - hT.eigenvalues hn j) ^ 2)
        = ∑ j, (hT.eigenvalues hn j - hS.eigenvalues hn j) ^ 2 from
        Finset.sum_congr rfl fun j _ => by ring]
    rw [hfrob]
    have hbase :=
      hT.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply hS hn (hT.eigenvectorBasis hn)
    exact hbase.trans_eq (Finset.sum_congr rfl fun k _ => by
      -- Expand the pointwise subtraction to reverse the norm difference.
      change ‖T (hT.eigenvectorBasis hn k) - S (hT.eigenvectorBasis hn k)‖ ^ 2 = _
      exact congrArg (fun r : ℝ => r ^ 2) (norm_sub_rev _ _))
  -- Per-column triangle inequality.
  have hcol : ∀ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ 2 * ‖(S - T) (w i)‖ ^ 2
        + 2 * (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 := by
    intro i
    have htri : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖
        ≤ ‖(S - T) (w i)‖ + |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)| := by
      rw [frameResidual_eq hT hS hn hw i]
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_smul, RCLike.norm_ofReal,
        (isOrderedEigenframe_iff.mp hw).orthonormal.norm_eq_one i, mul_one]
    have h1 : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
        ≤ (‖(S - T) (w i)‖
            + |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [h1, sq_nonneg (‖(S - T) (w i)‖
      - |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)|),
      sq_abs (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i))]
  calc ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ ∑ i, (2 * ‖(S - T) (w i)‖ ^ 2
          + 2 * (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2) :=
        Finset.sum_le_sum fun i _ => hcol i
    _ = 2 * ∑ i, ‖(S - T) (w i)‖ ^ 2
          + 2 * ∑ i, (hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * frob := by linarith

/-- **Frame residual, operator-norm branch.**  `∑ᵢ ‖Rᵢ‖² ≤ 4 |ι| ε²` when `S − T`
is `ε`-operator-close: each column splits as `‖(S − T) wᵢ‖ ≤ ε` and, by Weyl at
the *index* `e i`, `|λ_{e i}(S) − λ_{e i}(T)| ≤ ε`. -/
theorem sum_sq_norm_frameResidual_le_of_opNorm [Fintype ι] (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {e : ι ↪ Fin n} {w : ι → E}
    (hw : IsOrderedEigenframe hS hn e w) {ε : ℝ}
    (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ 4 * Fintype.card ι * ε ^ 2 := by
  have hcol : ∀ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ 4 * ε ^ 2 := by
    intro i
    have hEwi : ‖(S - T) (w i)‖ ≤ ε := by
      have := hε (w i)
      rwa [(isOrderedEigenframe_iff.mp hw).orthonormal.norm_eq_one i, mul_one] at this
    have hδ : |hS.eigenvalues hn (e i) - hT.eigenvalues hn (e i)| ≤ ε :=
      LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le hS hT hn hε (e i)
    have htri : ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ≤ 2 * ε := by
      rw [frameResidual_eq hT hS hn hw i]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, RCLike.norm_ofReal,
        (isOrderedEigenframe_iff.mp hw).orthonormal.norm_eq_one i, mul_one]
      linarith
    calc ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2 ≤ (2 * ε) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ = 4 * ε ^ 2 := by ring
  calc ∑ i, ‖(hT.eigenvalues hn (e i) : 𝕜) • w i - T (w i)‖ ^ 2
      ≤ ∑ _i : ι, 4 * ε ^ 2 := Finset.sum_le_sum fun i _ => hcol i
    _ = 4 * Fintype.card ι * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring


end LinearMap.IsSymmetric
