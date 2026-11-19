/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Calculus.IteratedGradient.RankOne
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Integral.ClosedBall

/-!
# Integrals of iterated-gradient fields

This file develops integral identities and uniform `Lᵖ → L^∞` estimates for fields valued in
`TauCeti.IteratedGradient E m`, without assuming any Sobolev or weak-derivative structure:

* Expanding a set integral `∫ y in s, Φ y (G y) ∂μ` along any finite orthonormal basis into a
  finite sum of rank-one coordinate integrals
  (`TauCeti.setIntegral_clm_apply_eq_sum_evalTupleL_rankOne`).
* Specializing to shifted full contractions `fullContractL m (x - y) (G y) * φ y`
  (`TauCeti.setIntegral_fullContractL_sub_mul_eq_sum`).
* Differentiating `x ↦ ∫ y in s, fullContractL m (x - y) (G y) * φ y ∂μ` along `h` in terms of any
  finite orthonormal basis (`TauCeti.fderiv_setIntegral_fullContractL_sub_mul_eq`).
* Bounding `‖∫ y in Ω, fullContractL k (x - y) (G y) * φ y ∂μ‖` for
  `G ∈ Lᵖ(Ω; IteratedGradient E k)` (`1 ≤ p ≤ ∞`) against a cutoff `φ` supported in a closed ball
  (`TauCeti.norm_setIntegral_fullContractL_sub_mul_le`).

## Main declarations

* `TauCeti.setIntegral_clm_apply_eq_sum_evalTupleL_rankOne`: orthonormal-basis expansion for
  operator-valued integrals of `IteratedGradient` fields.
* `TauCeti.setIntegral_fullContractL_sub_mul_eq_sum`: coordinate expansion for shifted full
  contractions against compactly supported weights continuous on their `tsupport`.
* `TauCeti.fderiv_setIntegral_fullContractL_sub_mul_eq`: spatial Fréchet derivative of a shifted
  full-contraction integral against a compactly supported weight continuous on its `tsupport`.
* `TauCeti.norm_setIntegral_fullContractL_sub_mul_le`: explicit `Lᵖ(Ω) → L^∞(closure Ω)` diameter
  and chunkiness bound for contracted `Lᵖ` fields.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace

section BasisExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Orthonormal-basis integral expansion for operator-valued pairings of iterated gradients.**
For any finite orthonormal basis `b` of `E`, any real normed space `F`, any
`G : E → IteratedGradient E m` locally integrable on `s`, and any compactly supported operator
family `Φ : E → IteratedGradient E m →L[ℝ] F` continuous on `tsupport Φ` with `tsupport Φ ⊆ s`,
the set integral `∫ y in s, Φ y (G y) ∂μ` expands as the finite sum of rank-one coordinate
integrals. -/
theorem setIntegral_clm_apply_eq_sum_evalTupleL_rankOne
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {s : Set E} (m : ℕ)
    {G : E → IteratedGradient E m} (hG : LocallyIntegrableOn G s μ)
    {Φ : E → IteratedGradient E m →L[ℝ] F} (hΦ : ContinuousOn Φ (tsupport Φ))
    (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ s) :
    ∫ y in s, Φ y (G y) ∂μ =
      ∑ I : Fin (m + 1) → ι,
        ∫ y in s, IteratedGradient.evalTupleL m (b ∘ I) (G y) •
          Φ y (IteratedGradient.rankOne m (b ∘ I)) ∂μ := by
  let L : (Fin (m + 1) → ι) → F →L[ℝ] IteratedGradient E m →L[ℝ] F := fun I =>
    ContinuousLinearMap.smulRightL ℝ (IteratedGradient E m) F
      (IteratedGradient.evalTupleL m (b ∘ I))
  let R : (Fin (m + 1) → ι) → (IteratedGradient E m →L[ℝ] F) →L[ℝ]
      IteratedGradient E m →L[ℝ] F := fun I =>
    (L I).comp (ContinuousLinearMap.apply ℝ F (IteratedGradient.rankOne m (b ∘ I)))
  let Ψ : (Fin (m + 1) → ι) → E → IteratedGradient E m →L[ℝ] F := fun I y => R I (Φ y)
  have hsub : ∀ I, Function.support (Ψ I) ⊆ Function.support Φ := fun I =>
    Function.support_subset_iff'.2 fun y hy => by simp [Ψ, Function.notMem_support.1 hy]
  have htsub : ∀ I, tsupport (Ψ I) ⊆ tsupport Φ := fun I => closure_mono (hsub I)
  have hint : ∀ I : Fin (m + 1) → ι, IntegrableOn
      (fun y => IteratedGradient.evalTupleL m (b ∘ I) (G y) •
        Φ y (IteratedGradient.rankOne m (b ∘ I))) s μ := fun I => by
    have hcont : ContinuousOn (Ψ I) (tsupport (Ψ I)) :=
      (R I).continuous.comp_continuousOn (hΦ.mono (htsub I))
    simpa only [Ψ, R, L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply] using
      (hG.integrable_clm_apply_of_hasCompactSupport hcont (hΦc.mono (hsub I))
        ((htsub I).trans hΦs)).integrableOn
  have hexp : ∀ y, Φ y (G y) = ∑ I : Fin (m + 1) → ι,
      IteratedGradient.evalTupleL m (b ∘ I) (G y) •
        Φ y (IteratedGradient.rankOne m (b ∘ I)) := fun y => by
    conv_lhs => rw [IteratedGradient.eq_sum_evalTupleL_rankOne b m (G y), map_sum]
    exact Finset.sum_congr rfl fun I _ => map_smul _ _ _
  simp_rw [hexp]
  exact integral_finsetSum _ fun I _ => hint I

/-- Expanding a shifted full-contraction integral along any finite orthonormal basis `b` reduces
`∫ y in s, fullContractL m (x - y) (G y) * φ y ∂μ` to a finite sum of coordinate pairings against
shifted inner-product products `∏ l, ⟪b (I l), x - y⟫_ℝ`. -/
theorem setIntegral_fullContractL_sub_mul_eq_sum
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {s : Set E} (m : ℕ)
    {G : E → IteratedGradient E m} (hG : LocallyIntegrableOn G s μ)
    {φ : E → ℝ} (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ s) (x : E) :
    ∫ y in s, IteratedGradient.fullContractL m (x - y) (G y) * φ y ∂μ =
      ∑ I : Fin (m + 1) → ι,
        ∫ y in s, (∏ l : Fin (m + 1), ⟪b (I l), x - y⟫_ℝ) * φ y *
          IteratedGradient.evalTupleL m (b ∘ I) (G y) ∂μ := by
  let Φ : E → IteratedGradient E m →L[ℝ] ℝ :=
    fun y => φ y • IteratedGradient.fullContractL m (x - y)
  have hsub : Function.support Φ ⊆ Function.support φ :=
    Function.support_subset_iff'.2 fun y hy => by simp [Φ, Function.notMem_support.1 hy]
  have htsub : tsupport Φ ⊆ tsupport φ := closure_mono hsub
  have hΦ : ContinuousOn Φ (tsupport Φ) :=
    (hφ.mono htsub).smul
      ((IteratedGradient.contDiff_fullContractL (n := 0) m).continuous.comp
        (continuous_const.sub continuous_id)).continuousOn
  have hlhs : ∫ y in s, IteratedGradient.fullContractL m (x - y) (G y) * φ y ∂μ =
      ∫ y in s, Φ y (G y) ∂μ :=
    integral_congr_ae (.of_forall fun y => by simp [Φ, mul_comm])
  rw [hlhs, setIntegral_clm_apply_eq_sum_evalTupleL_rankOne b m hG hΦ (hφc.mono hsub)
    (htsub.trans hφs)]
  refine Finset.sum_congr rfl fun I _ => integral_congr_ae (.of_forall fun y => ?_)
  dsimp only [Φ]
  simp only [smul_apply, smul_eq_mul, IteratedGradient.fullContractL_rankOne, Function.comp_apply]
  ring

/-- Spatial Fréchet derivative of a shifted full-contraction integral against a compactly supported
weight `φ` continuous on `tsupport φ`, expanded along any finite orthonormal basis `b` of `E`. -/
theorem fderiv_setIntegral_fullContractL_sub_mul_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {s : Set E} (m : ℕ)
    {G : E → IteratedGradient E m} (hG : LocallyIntegrableOn G s μ)
    {φ : E → ℝ} (hφ : ContinuousOn φ (tsupport φ)) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ s) (x h : E) :
    fderiv ℝ (fun x' => ∫ y in s,
        IteratedGradient.fullContractL m (x' - y) (G y) * φ y ∂μ) x h =
      ∫ y in s, φ y * (∑ I : Fin (m + 1) → ι,
        ∑ p : Fin (m + 1), ⟪b (I p), h⟫_ℝ *
          (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) *
          IteratedGradient.evalTupleL m (b ∘ I) (G y)) ∂μ := by
  let w : (Fin (m + 1) → ι) → E → ℝ :=
    fun I y => φ y * IteratedGradient.evalTupleL m (b ∘ I) (G y)
  have hint_g : ∀ (I : Fin (m + 1) → ι) {g : E → ℝ}, Continuous g →
      IntegrableOn (fun y => g y * w I y) s μ := fun I {g} hg => by
    have hA : ContinuousOn (fun y => g y • IteratedGradient.evalTupleL m (b ∘ I)) (tsupport φ) :=
      hg.continuousOn.smul continuousOn_const
    have heq : (fun y => φ y • (g y • IteratedGradient.evalTupleL m (b ∘ I)) (G y)) =
        fun y => g y * w I y :=
      funext fun y => by simp only [w, smul_apply, smul_eq_mul]; ring
    exact heq ▸ (hG.integrable_smul_clm_apply_of_hasCompactSupport hφ hφc hφs hA).integrableOn
  have hmom : ∀ (I : Fin (m + 1) → ι) (v : Finset (Fin (m + 1))), v ⊆ Finset.univ →
      IntegrableOn (fun y => (∏ l ∈ v, ⟪b (I l), y⟫_ℝ) * w I y) s μ := fun I v _ =>
    hint_g I (continuous_finsetProd v fun l _ => (innerSL ℝ (b (I l))).continuous)
  have hexp : (fun x' => ∫ y in s, IteratedGradient.fullContractL m (x' - y) (G y) * φ y ∂μ) =
      fun x' => ∑ I : Fin (m + 1) → ι, ∫ y in s, (∏ l : Fin (m + 1), ⟪b (I l), x' - y⟫_ℝ) *
        w I y ∂μ := funext fun x' => by
    simpa only [w, mul_assoc] using setIntegral_fullContractL_sub_mul_eq_sum b m hG hφ hφc hφs x'
  have hsum_d : HasFDerivAt
      (fun x' => ∑ I : Fin (m + 1) → ι,
        ∫ y in s, (∏ l : Fin (m + 1), ⟪b (I l), x' - y⟫_ℝ) * w I y ∂μ)
      (∑ I : Fin (m + 1) → ι, fderiv ℝ (fun x' =>
        ∫ y in s, (∏ l : Fin (m + 1), ⟪b (I l), x' - y⟫_ℝ) * w I y ∂μ) x) x :=
    HasFDerivAt.fun_sum fun I _ =>
      (((contDiff_setIntegral_prod_inner_sub_right_mul (m := 1) Finset.univ
        (fun l => b (I l)) (hmom I)).differentiable one_ne_zero) x).hasFDerivAt
  -- Differentiate each basis coordinate integral, then pull the finite sums back inside `∫`.
  rw [hexp, hsum_d.fderiv, FunLike.coe_sum, Finset.sum_apply]
  have hint_Ip : ∀ (I : Fin (m + 1) → ι) (p : Fin (m + 1)),
      IntegrableOn (fun y => ⟪b (I p), h⟫_ℝ *
        ((∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * w I y)) s μ := fun I p =>
    (hint_g I (continuous_finsetProd _ fun l _ =>
      (innerSL ℝ (b (I l))).continuous.comp (continuous_const.sub continuous_id))).const_mul _
  calc ∑ I : Fin (m + 1) → ι, fderiv ℝ (fun x' => ∫ y in s,
          (∏ l : Fin (m + 1), ⟪b (I l), x' - y⟫_ℝ) * w I y ∂μ) x h
      = ∑ I : Fin (m + 1) → ι, ∫ y in s, ∑ p : Fin (m + 1), ⟪b (I p), h⟫_ℝ *
          ((∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * w I y) ∂μ :=
        Finset.sum_congr rfl fun I _ => by
          rw [fderiv_setIntegral_prod_inner_sub_right_mul Finset.univ (fun l => b (I l))
            (hmom I) x h]
          simp_rw [← integral_const_mul]
          exact (integral_finsetSum _ fun p _ => hint_Ip I p).symm
    _ = ∫ y in s, ∑ I : Fin (m + 1) → ι, ∑ p : Fin (m + 1), ⟪b (I p), h⟫_ℝ *
          ((∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - y⟫_ℝ) * w I y) ∂μ :=
        (integral_finsetSum _ fun I _ => integrable_finsetSum _ fun p _ => hint_Ip I p).symm
    _ = _ := integral_congr_ae (.of_forall fun y => by
        dsimp only [w]; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring)

end BasisExpansion

section Bounds

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Uniform `Lᵖ(Ω) → L^∞(closure Ω)` diameter and chunkiness bound for contracted fields.** For
bounded `Ω`, `1 ≤ p ≤ ∞`, `G ∈ Lᵖ(Ω; IteratedGradient E k)`, `x ∈ closure Ω`, and `φ` supported in
`closedBall x₀ ρ` (`0 < ρ`, `diam Ω ≤ γ * ρ`) with `‖φ y‖ ≤ M * ρ ^ (-finrank ℝ E)` on `Ω`,
`‖∫_Ω fullContractL k (x - y) (G y) φ y‖` is bounded by
`M * μ(B(0,1))^{1-1/p} * γ^{n/p} * (diam Ω)^{k + 1 - n/p} * ‖G‖`. -/
theorem norm_setIntegral_fullContractL_sub_mul_le
    (hΩ_bdd : Bornology.IsBounded (Omega : Set E)) (k : ℕ)
    (G : Lp (IteratedGradient E k) p (mu.restrict Omega))
    {x : E} (hx : x ∈ closure (Omega : Set E)) {φ : E → ℝ} {x₀ : E} {ρ M γ : ℝ}
    (hρ : 0 < ρ) (hdiam : Metric.diam (Omega : Set E) ≤ γ * ρ)
    (hsupp : Function.support φ ⊆ Metric.closedBall x₀ ρ)
    (hφ : ∀ y ∈ (Omega : Set E), ‖φ y‖ ≤ M * ρ ^ (-(Module.finrank ℝ E : ℝ))) :
    ‖∫ y in Omega, IteratedGradient.fullContractL k (x - y) (G y) * φ y ∂mu‖ ≤
      M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Omega : Set E) ^ ((k + 1 : ℝ) - (Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖G‖ := by
  let d := Metric.diam (Omega : Set E)
  let n := Module.finrank ℝ E
  obtain ⟨y₀, hy₀⟩ := closure_nonempty_iff.1 ⟨x, hx⟩
  have hMρ : 0 ≤ M * ρ ^ (-(n : ℝ)) := (norm_nonneg (φ y₀)).trans (hφ y₀ hy₀)
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left hMρ (Real.rpow_pos_of_pos hρ _)
  have hγ : 0 ≤ γ := nonneg_of_mul_nonneg_left (Metric.diam_nonneg.trans hdiam) hρ
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).1 hn0
    have hzero : ∀ y, IteratedGradient.fullContractL k (x - y) (G y) * φ y = 0 := fun y => by
      rw [Subsingleton.elim (x - y) 0, IteratedGradient.fullContractL_zero_direction,
        zero_apply, zero_mul]
    simp only [hzero, integral_zero, norm_zero]
    positivity
  have := Module.nontrivial_of_finrank_pos hn_pos
  have hd_pos : 0 < d := Omega.isOpen.diam_pos hΩ_bdd hy₀
  refine (Lp.norm_setIntegral_le_of_support_subset_closedBall hΩ_bdd G
    (K := M * d ^ (k + 1)) hρ hdiam
    ((Function.support_mul_subset_right _ _).trans hsupp) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with y hy
    have hxy : ‖x - y‖ ≤ d := by
      dsimp only [d]; rw [← dist_eq_norm, ← Metric.diam_closure]
      exact Metric.dist_le_diam_of_mem hΩ_bdd.closure hx (subset_closure hy)
    calc ‖IteratedGradient.fullContractL k (x - y) (G y) * φ y‖
        ≤ (‖G y‖ * ‖x - y‖ ^ (k + 1)) * ‖φ y‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (IteratedGradient.norm_fullContractL_apply_le k _ _) (norm_nonneg _)
      _ ≤ (‖G y‖ * d ^ (k + 1)) * (M * ρ ^ (-(n : ℝ))) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxy _) (norm_nonneg _))
            (hφ y hy) (norm_nonneg _) (by positivity)
      _ = M * d ^ (k + 1) * ρ ^ (-(n : ℝ)) * ‖G y‖ := by ring
  · have hpow : d ^ (k + 1) * d ^ (-(n : ℝ) / p.toReal) =
        d ^ ((k + 1 : ℝ) - (n : ℝ) / p.toReal) := by
      rw [← Real.rpow_natCast d (k + 1), ← Real.rpow_add hd_pos]; congr 1; push_cast; ring
    linear_combination M * mu.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
      γ ^ ((n : ℝ) / p.toReal) * ‖G‖ * hpow

end Bounds

end TauCeti
