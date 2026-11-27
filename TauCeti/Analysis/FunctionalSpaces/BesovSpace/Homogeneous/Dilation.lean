/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LinearEquiv
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Homogeneous Besov spaces under dyadic dilations

Let `\dot B^s_{p,q}` be the homogeneous Besov space on a real inner product space `E` of dimension
`n`, built from the homogeneous Littlewood–Paley blocks `Pⱼ`, `j ∈ ℤ`, of a bump function. For
`λ = 2^m`, `m ∈ ℤ`, let `u (λ ·)` be the dilate of a tempered distribution `u`, the pullback
`TemperedDistribution.compCLMOfContinuousLinearEquiv` along the dilation `x ↦ λ x`. The Fourier
transform of `u (λ ·)` is that of `u`, dilated by `λ⁻¹`, so the dilation shifts the blocks:

`Pⱼ (u (λ ·)) = (P_{j-m} u) (λ ·)`

(`TemperedDistribution.homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv`). Since
`‖g (λ ·)‖_p = λ^{-n/p} ‖g‖_p`, each weighted block of `u (λ ·)` is `λ^{s - n/p}` times a weighted
block of `u`, and reindexing the `ℓ^q` norm over `ℤ` gives the **dilation law**

`‖u (λ ·)‖_{\dot B^s_{p,q}} = λ^{s - n/p} ‖u‖_{\dot B^s_{p,q}}`

(`TauCeti.HomogeneousBesovSpace.norm_eq_of_toDistr_eq_compCLMOfContinuousLinearEquiv`), with
`u (λ ·) ∈ \dot B^s_{p,q}` exactly when `u ∈ \dot B^s_{p,q}`
(`TemperedDistribution.memHomogeneousBesov_compCLMOfContinuousLinearEquiv_iff`). Here `n / p` is
`n / p.toReal`, which is `0` for `p = ∞`. The exponent `s - n/p` is the scaling degree of
`\dot B^s_{p,q}`, which fixes the regularity index in scale-invariant estimates. The inhomogeneous
spaces `B^s_{p,q}` have no such law: their low-frequency block collects all frequencies near `0`
and is not shifted by a dilation.

## Main declarations

* `TemperedDistribution.homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv`: the
  dyadic dilation `x ↦ 2^m x` shifts the homogeneous blocks by `m`.
* `TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv_eq`:
  the weighted blocks of the dilate are `2^{m(s - n/p)}` times shifted weighted blocks.
* `TemperedDistribution.memHomogeneousBesov_compCLMOfContinuousLinearEquiv_iff`: dyadic dilations
  preserve `\dot B^s_{p,q}`.
* `TauCeti.HomogeneousBesovSpace.norm_eq_of_toDistr_eq_compCLMOfContinuousLinearEquiv`: the
  dilation law `‖u (2^m ·)‖ = 2^{m(s - n/p)} ‖u‖`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Remark 2.19 (the
  scaling of the homogeneous Besov norms).
-/

public section

noncomputable section

open MeasureTheory FourierTransform Module
open scoped ENNReal SchwartzMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E))

/-- **The homogeneous blocks under dyadic dilations.** If `e` is the dilation `x ↦ 2^m x`, then the
blocks of the dilate `u ∘ e` are the dilates of the blocks of `u`, shifted by `m`:
`Pⱼ (u ∘ e) = (P_{j-m} u) ∘ e`. -/
theorem homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv {e : E ≃L[ℝ] E} {m : ℤ}
    (he : ∀ x, e x = (2 : ℝ) ^ m • x) (j : ℤ) (u : 𝓢'(E, F)) :
    homogeneousLittlewoodPaleyBlock F φ j (compCLMOfContinuousLinearEquiv F e u) =
      compCLMOfContinuousLinearEquiv F e (homogeneousLittlewoodPaleyBlock F φ (j - m) u) := by
  -- A real multiple of the identity is self-adjoint, so `e† = e`.
  have hadj (ξ : E) : e.adjointEquiv ξ = ((2 : ℝ) ^ (-m))⁻¹ • ξ := by
    rw [zpow_neg, inv_inv]
    refine ext_inner_right ℝ fun x ↦ ?_
    rw [ContinuousLinearEquiv.adjointEquiv_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearEquiv.coe_coe, he, inner_smul_right, real_inner_smul_left]
  rw [homogeneousLittlewoodPaleyBlock_apply, fourierMultiplierCLM_compCLMOfContinuousLinearEquiv_eq,
    homogeneousLittlewoodPaleyBlock_apply]
  congr 3
  ext ξ
  rw [Function.comp_apply, hadj, φ.littlewoodPaley_two_zpow_inv_smul, ← sub_eq_add_neg]

variable [CompleteSpace F] {φ} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The weighted blocks under dyadic dilations.** If `e` is the dilation `x ↦ 2^m x` and the block
`P_{j-m} u` is the `Lᵖ` function `f`, then the block `Pⱼ (u ∘ e)` is an `Lᵖ` function `w`, with
`2^{js} ‖w‖_p = 2^{m(s - n/p)} (2^{(j-m)s} ‖f‖_p)`, where `n` is the dimension of `E`. -/
theorem exists_homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv_eq {e : E ≃L[ℝ] E}
    {m : ℤ} (he : ∀ x, e x = (2 : ℝ) ^ m • x) {u : 𝓢'(E, F)} {j : ℤ}
    {f : Lp F p (volume : Measure E)} (hf : homogeneousLittlewoodPaleyBlock F φ (j - m) u = f) :
    ∃ w : Lp F p (volume : Measure E),
      homogeneousLittlewoodPaleyBlock F φ j (compCLMOfContinuousLinearEquiv F e u) = w ∧
        2 ^ (s * j) * ‖w‖ =
          2 ^ (m * (s - finrank ℝ E / p.toReal)) * (2 ^ (s * (j - m : ℤ)) * ‖f‖) := by
  obtain ⟨w, hw, -, hnorm⟩ :=
    exists_compCLMOfContinuousLinearEquiv_toTemperedDistribution_eq_and_norm_eq volume e f
  refine ⟨w, by rw [homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv φ he, hf, hw],
    ?_⟩
  -- `|det e| = 2^{mn}`, so the `Lᵖ` norm is multiplied by `2^{-mn/p}`.
  have hdet : |LinearMap.det (e : E →ₗ[ℝ] E)| = (2 : ℝ) ^ (m * finrank ℝ E : ℝ) := by
    have he' : (e : E →ₗ[ℝ] E) = (2 : ℝ) ^ m • LinearMap.id := LinearMap.ext fun x ↦ by simp [he]
    rw [he', LinearMap.det_smul, LinearMap.det_id, mul_one, ← zpow_natCast, ← zpow_mul,
      abs_of_pos (by positivity), ← Real.rpow_intCast]
    push_cast
    rfl
  rw [hnorm, hdet, ← Real.rpow_neg zero_le_two, ← Real.rpow_mul zero_le_two, ← mul_assoc,
    ← mul_assoc, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
  congr 2
  push_cast
  ring

variable (φ s p q) in
/-- **Dyadic dilations preserve `\dot B^s_{p,q}`:** if `e` is the dilation `x ↦ 2^m x`, then
`u ∘ e ∈ \dot B^s_{p,q}` exactly when `u ∈ \dot B^s_{p,q}`. -/
theorem memHomogeneousBesov_compCLMOfContinuousLinearEquiv_iff {e : E ≃L[ℝ] E} {m : ℤ}
    (he : ∀ x, e x = (2 : ℝ) ^ m • x) (u : 𝓢'(E, F)) :
    (compCLMOfContinuousLinearEquiv F e u).MemHomogeneousBesov φ s p q ↔
      u.MemHomogeneousBesov φ s p q := by
  -- One direction for every dyadic dilation; the other follows from it for `e⁻¹`.
  have key {e : E ≃L[ℝ] E} {m : ℤ} (he : ∀ x, e x = (2 : ℝ) ^ m • x) {u : 𝓢'(E, F)}
      (hu : u.MemHomogeneousBesov φ s p q) :
      (compCLMOfContinuousLinearEquiv F e u).MemHomogeneousBesov φ s p q := by
    obtain ⟨f, hf, hmem⟩ := memHomogeneousBesov_iff.1 hu
    choose w hw hwn using fun j ↦
      exists_homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv_eq (s := s) he
        (hf (j - m))
    refine memHomogeneousBesov_iff.2 ⟨w, hw, ?_⟩
    simp_rw [hwn]
    exact ((Equiv.subRight m).memℓp_apply_iff.2 hmem).const_mul _
  refine ⟨fun h ↦ ?_, key he⟩
  have he' (x : E) : e.symm x = (2 : ℝ) ^ (-m) • x := by
    rw [e.symm_apply_eq, he, smul_smul, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero,
      one_smul]
  simpa using key he' h

end TemperedDistribution

namespace TauCeti.HomogeneousBesovSpace

variable [CompleteSpace F] {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)]

/-- **The dilation law of the homogeneous Besov seminorm.** If `e` is the dilation `x ↦ 2^m x` and
`v` is the dilate `u ∘ e` of `u ∈ \dot B^s_{p,q}`, then `‖v‖ = 2^{m(s - n/p)} ‖u‖`, where `n` is
the dimension of `E` and `n / p` is `0` for `p = ∞`. -/
theorem norm_eq_of_toDistr_eq_compCLMOfContinuousLinearEquiv {e : E ≃L[ℝ] E} {m : ℤ}
    (he : ∀ x, e x = (2 : ℝ) ^ m • x) {u v : HomogeneousBesovSpace F φ s p q}
    (huv : v.toDistr = TemperedDistribution.compCLMOfContinuousLinearEquiv F e u.toDistr) :
    ‖v‖ = 2 ^ (m * (s - finrank ℝ E / p.toReal)) * ‖u‖ := by
  set c : ℝ := 2 ^ (m * (s - finrank ℝ E / p.toReal))
  have hc : 0 ≤ c := by positivity
  rw [← norm_weightedBlocks, ← norm_weightedBlocks, ← Complex.norm_of_nonneg hc, ← norm_smul]
  refine lp.norm_eq_of_forall_norm_eq_comp_equiv (Equiv.subRight m) fun j ↦ ?_
  obtain ⟨w, hw, hwn⟩ :=
    TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_compCLMOfContinuousLinearEquiv_eq
      (s := s) he (coe_block u (j - m)).symm
  -- The block of `v` is the `Lᵖ` function `w`, since both have the same distribution.
  have hvw : v.block j = w :=
    Lp.toTemperedDistribution_injective (by dsimp only; rw [coe_block, huv, hw])
  rw [norm_weightedBlocks_apply, hvw, hwn, Equiv.subRight_apply, lp.coeFn_smul, Pi.smul_apply,
    norm_smul, norm_weightedBlocks_apply, Complex.norm_of_nonneg hc]

end TauCeti.HomogeneousBesovSpace
