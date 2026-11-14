/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Cutoff Cauchy–Pompeiu representation and rational collar approximation

If `f` is holomorphic on an open set `U ⊆ ℂ` and `χ` is a compactly supported `C¹` cutoff supported
in `U` and equal to `1` near a compact set `K ⊆ U`, then `χ • f` is compactly supported and `C¹` on
the whole plane, with `\bar∂(χ • f) = (\bar∂χ) • f` because `\bar∂f = 0` on `U` and `χ` vanishes off
`U`. Applying the left-inverse Cauchy–Pompeiu identity to `χ • f` expresses `f` on `K` as an
integral against the smooth kernel `π⁻¹ (\bar∂χ)` supported in `tsupport χ \ interior (χ ⁻¹' {1})`,
away from `K`:
`f w = π⁻¹ • ∫ ζ, (w - ζ)⁻¹ • (conjWirtingerDeriv (fun y ↦ (χ y : ℂ)) ζ 1 • f ζ)`.

When `K` lies in the interior of a compact collar `L`, choosing `χ` supported in `interior L` places
the topological support `S` of this kernel inside `interior L \ K`, at positive distance from `K`
and with uniform closed-disc room inside `L`. Partitioning a square around `S` into fine half-open
grid cells and bounding the variation of `f` on each active cell by Cauchy's derivative estimate on
`L` approximates `f` uniformly on `K` by a finite linear combination of simple fractions
`(z - ζ_j)⁻¹` with poles `ζ_j ∈ interior L \ K` and weights depending only on `K`, `L`, and the
target relative error `ε > 0`. Pairing with continuous linear functionals via Hahn–Banach lifts the
resulting rational approximation from scalar functions to arbitrary complex normed spaces without
requiring completeness of the target space.

## Main results

* `DifferentiableOn.cauchyTransform_conjWirtingerDeriv_smul_eq` and
  `DifferentiableOn.eq_cauchyTransform_conjWirtingerDeriv_smul`: cutoff Cauchy–Pompeiu
  representation of a holomorphic map on an open subset of `ℂ`.
* `IsCompact.exists_contDiff_tsupport_subset_sdiff_eq_integral_sub_inv_mul`: existence of a smooth
  kernel supported in `interior L \ K` representing every scalar function holomorphic near `L`.
* `DifferentiableOn.norm_sub_sum_mul_smul_le_of_forall_differentiableOn`: upgrade of any
  finite-rank point-evaluation error bound from `ℂ`-valued to normed-space-valued holomorphic maps.
* `IsCompact.exists_fin_mem_sdiff_norm_sub_sum_mul_inv_le` and
  `IsCompact.exists_fin_mem_sdiff_norm_sub_sum_inv_smul_le`: uniform rational approximation on `K`
  with fixed poles in `interior L \ K` and relative error `ε * sSup ((fun x ↦ ‖f x‖) '' L)`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 10.3.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Real Topology

/-- **Vector-valued lifting for finite-rank point-evaluation bounds.** Any finite-rank
approximation bound on scalar holomorphic functions on `U` with relative error
`ε * sSup ((fun x ↦ ‖φ x‖) '' L)` transfers to holomorphic functions valued in an arbitrary complex
normed space `F`, with no completeness or openness assumption. -/
theorem DifferentiableOn.norm_sub_sum_mul_smul_le_of_forall_differentiableOn {ι F : Type*}
    [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F] {U L : Set ℂ} {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) (hL : IsCompact L) (hLU : L ⊆ U) {ζ : ι → ℂ} {w : ι → ℂ}
    {g : ι → ℂ → ℂ} {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ}
    (hscalar : ∀ ⦃φ : ℂ → ℂ⦄, DifferentiableOn ℂ φ U →
      ‖φ z - ∑ j, w j * φ (ζ j) * g j z‖ ≤ ε * sSup ((fun x ↦ ‖φ x‖) '' L)) :
    ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L) := by
  obtain ⟨ℓ, hℓnorm, hℓval⟩ := exists_dual_vector'' ℂ (f z - ∑ j, (w j * g j z) • f (ζ j))
  have hφ : DifferentiableOn ℂ (fun x ↦ ℓ (f x)) U := ℓ.differentiable.comp_differentiableOn hf
  have hlhs : ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ =
      ‖ℓ (f z) - ∑ j, w j * ℓ (f (ζ j)) * g j z‖ := by
    have hmap : ℓ (f z - ∑ j, (w j * g j z) • f (ζ j)) =
        ℓ (f z) - ∑ j, w j * ℓ (f (ζ j)) * g j z := by
      simp only [map_sub, map_sum, map_smul, smul_eq_mul]
      refine congrArg (ℓ (f z) - ·) (Finset.sum_congr rfl fun j _ ↦ ?_)
      ring
    have hnorm := congrArg Norm.norm (hmap.symm.trans hℓval)
    simpa [Complex.norm_real] using hnorm.symm
  rw [hlhs]
  refine (hscalar hφ).trans (mul_le_mul_of_nonneg_left ?_ hε)
  rcases L.eq_empty_or_nonempty with rfl | hLne
  · simp [Real.sSup_empty]
  · have hbdd : BddAbove ((fun x ↦ ‖f x‖) '' L) :=
      (hL.image_of_continuousOn
        (continuous_norm.comp_continuousOn (hf.continuousOn.mono hLU))).bddAbove
    refine csSup_le (hLne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle : ‖ℓ (f x)‖ ≤ ‖f x‖ :=
      (ℓ.le_opNorm (f x)).trans (mul_le_of_le_one_left (norm_nonneg _) hℓnorm)
    exact hle.trans (le_csSup hbdd ⟨x, hx, rfl⟩)

section CutoffRepresentation

open TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {U : Set ℂ} {f : ℂ → F} {χ : ℂ → ℝ}

/-- **Cutoff Cauchy–Pompeiu identity.** For `f` holomorphic on an open set `U ⊆ ℂ` with values in a
complex Banach space and a compactly supported `C¹` cutoff `χ` with `tsupport χ ⊆ U`, the Cauchy
transform of `(\bar∂χ) • f` recovers `χ • f` everywhere on `ℂ`. -/
theorem DifferentiableOn.cauchyTransform_conjWirtingerDeriv_smul_eq [CompleteSpace F]
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hχ : ContDiff ℝ 1 χ)
    (hcpt : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (w : ℂ) :
    cauchyTransform (fun ζ ↦ conjWirtingerDeriv (fun y ↦ (χ y : ℂ)) ζ 1 • f ζ) w = χ w • f w := by
  have hf1 : ContDiffOn ℝ 1 f U := ((hf.contDiffOn hU).restrict_scalars ℝ).of_le le_top
  have hu : ContDiff ℝ 1 (fun y ↦ χ y • f y) :=
    hf1.contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU
  have hcptu : HasCompactSupport (fun y ↦ χ y • f y) := hcpt.smul_right
  have heq : (fun ζ ↦ conjWirtingerDeriv (fun y ↦ (χ y : ℂ)) ζ 1 • f ζ) =
      fun ζ ↦ conjWirtingerDeriv (fun y ↦ χ y • f y) ζ 1 :=
    funext fun ζ ↦
      (hf.conjWirtingerDeriv_smul_of_tsupport_subset hU (hχ.differentiable one_ne_zero)
        hχU ζ 1).symm
  rw [heq, hcptu.cauchyTransform_conjWirtingerDeriv hu w]

/-- At any point `w` where `χ w = 1`, a holomorphic map `f` on `U` is represented by the Cauchy
transform of `(\bar∂χ) • f`. -/
theorem DifferentiableOn.eq_cauchyTransform_conjWirtingerDeriv_smul [CompleteSpace F]
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hχ : ContDiff ℝ 1 χ)
    (hcpt : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) {w : ℂ} (hχw : χ w = 1) :
    f w = cauchyTransform (fun ζ ↦ conjWirtingerDeriv (fun y ↦ (χ y : ℂ)) ζ 1 • f ζ) w := by
  simpa [hχw] using (hf.cauchyTransform_conjWirtingerDeriv_smul_eq hU hχ hcpt hχU w).symm

/-- **Smooth collar representation kernel.** If a compact set `K ⊆ ℂ` lies in `interior L`, there is
a smooth compactly supported function `φ : ℂ → ℂ` supported in `interior L \ K` such that every
scalar function holomorphic on an open neighbourhood of `interior L` satisfies
`f w = ∫ ζ, (w - ζ)⁻¹ * φ ζ * f ζ` for all `w ∈ K`. -/
theorem IsCompact.exists_contDiff_tsupport_subset_sdiff_eq_integral_sub_inv_mul
    {K L : Set ℂ} (hK : IsCompact K) (hKL : K ⊆ interior L) :
    ∃ φ : ℂ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ interior L \ K ∧
      ∀ ⦃U : Set ℂ⦄, IsOpen U → interior L ⊆ U → ∀ ⦃f : ℂ → ℂ⦄, DifferentiableOn ℂ f U →
        ∀ w ∈ K, f w = ∫ ζ, (w - ζ)⁻¹ * φ ζ * f ζ := by
  obtain ⟨χ, hχ, -, hK1, hcpt, hχL⟩ := hK.exists_contDiff_cutoff isOpen_interior hKL
  set ψ : ℂ → ℂ := fun ζ ↦ conjWirtingerDeriv (fun y ↦ (χ y : ℂ)) ζ 1
  set φ : ℂ → ℂ := fun ζ ↦ (Real.pi : ℂ)⁻¹ * ψ ζ
  have hχc : ContDiff ℝ ∞ (fun y ↦ (χ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_iff_contDiffAt.2 fun ζ ↦ hχc.contDiffAt.conjWirtingerDeriv_apply (by simp) 1
  have htsc : tsupport (fun y ↦ (χ y : ℂ)) = tsupport χ := by
    simp [tsupport, Function.support]
  have hsubψ : tsupport ψ ⊆ tsupport χ \ interior (χ ⁻¹' {1}) := by
    have hsub := tsupport_conjWirtingerDeriv_apply_subset_sdiff_interior_preimage_singleton
      (fun y ↦ (χ y : ℂ)) 1 (1 : ℂ)
    have hpre : (fun y ↦ (χ y : ℂ)) ⁻¹' {(1 : ℂ)} = χ ⁻¹' {1} := by ext y; simp
    rwa [hpre, htsc] at hsub
  have htsφ : tsupport φ ⊆ tsupport ψ := tsupport_mul_subset_right
  have hcptφ : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact hcpt
      ((subset_tsupport φ).trans (htsφ.trans (hsubψ.trans sdiff_subset)))
  refine ⟨φ, contDiff_const.mul hψ, hcptφ, htsφ.trans (hsubψ.trans (sdiff_subset_sdiff hχL hK1)),
    fun U hU hLU f hf w hw ↦ ?_⟩
  have hχw : χ w = 1 := interior_subset (hK1 hw)
  rw [hf.eq_cauchyTransform_conjWirtingerDeriv_smul hU (hχ.of_le (by simp)) hcpt
    (hχL.trans hLU) hχw, cauchyTransform_apply, ← integral_smul]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [φ, ψ, smul_eq_mul]
  ring

end CutoffRepresentation

section RationalApproximation

open TauCeti

/-- Half-open grid cell in `[-R, R) ×ℂ [-R, R)` indexed by `p : Fin M × Fin M`. -/
private noncomputable def gridCell (R : ℝ) (M : ℕ) (p : Fin M × Fin M) : Set ℂ :=
  let h := 2 * R / M
  Ico (-R + p.1 * h) (-R + (p.1 + 1 : ℝ) * h) ×ℂ
    Ico (-R + p.2 * h) (-R + (p.2 + 1 : ℝ) * h)

private theorem measurableSet_gridCell (R : ℝ) (M : ℕ) (p : Fin M × Fin M) :
    MeasurableSet (gridCell R M p) :=
  measurableSet_Ico.reProdIm measurableSet_Ico

private theorem volume_gridCell {R : ℝ} (hR : 0 ≤ R) {M : ℕ} (p : Fin M × Fin M) :
    volume (gridCell R M p) = ENNReal.ofReal ((2 * R / M) ^ 2) := by
  set h := 2 * R / M
  have hh : 0 ≤ h := by positivity
  have hv := Complex.setLIntegral_reProdIm_comp_re
    (Ico (-R + p.1 * h) (-R + (p.1 + 1 : ℝ) * h))
    (Ico (-R + p.2 * h) (-R + (p.2 + 1 : ℝ) * h))
    (measurable_const (a := (1 : ℝ≥0∞)))
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ico] at hv
  have hd₁ : -R + (p.1 + 1 : ℝ) * h - (-R + p.1 * h) = h := by ring
  have hd₂ : -R + (p.2 + 1 : ℝ) * h - (-R + p.2 * h) = h := by ring
  rw [gridCell, hv, hd₁, hd₂, ← ENNReal.ofReal_mul hh, sq]

private theorem volume_real_gridCell {R : ℝ} (hR : 0 ≤ R) {M : ℕ} (p : Fin M × Fin M) :
    volume.real (gridCell R M p) = (2 * R / M) ^ 2 := by
  rw [Measure.real, volume_gridCell hR p, ENNReal.toReal_ofReal (sq_nonneg _)]

private theorem pairwiseDisjoint_gridCell {R : ℝ} (hR : 0 ≤ R) (M : ℕ) :
    (↑(Finset.univ : Finset (Fin M × Fin M)) : Set (Fin M × Fin M)).PairwiseDisjoint
      (gridCell R M) := by
  intro p _ q _ hpq
  rw [Function.onFun, Set.disjoint_left]
  intro z hzp hzq
  simp only [gridCell, mem_reProdIm, mem_Ico] at hzp hzq
  have hh : 0 ≤ 2 * R / M := by positivity
  rcases not_and_or.mp (Prod.ext_iff.not.mp hpq) with h1 | h2
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h1) with hlt | hgt
    · have hle : (p.1 : ℝ) + 1 ≤ q.1 := by exact_mod_cast Nat.succ_le_of_lt hlt
      have := mul_le_mul_of_nonneg_right hle hh
      linarith [hzp.1.2, hzq.1.1]
    · have hle : (q.1 : ℝ) + 1 ≤ p.1 := by exact_mod_cast Nat.succ_le_of_lt hgt
      have := mul_le_mul_of_nonneg_right hle hh
      linarith [hzq.1.2, hzp.1.1]
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h2) with hlt | hgt
    · have hle : (p.2 : ℝ) + 1 ≤ q.2 := by exact_mod_cast Nat.succ_le_of_lt hlt
      have := mul_le_mul_of_nonneg_right hle hh
      linarith [hzp.2.2, hzq.2.1]
    · have hle : (q.2 : ℝ) + 1 ≤ p.2 := by exact_mod_cast Nat.succ_le_of_lt hgt
      have := mul_le_mul_of_nonneg_right hle hh
      linarith [hzq.2.2, hzp.2.1]

private theorem norm_sub_le_of_mem_gridCell {R : ℝ} {M : ℕ} {p : Fin M × Fin M}
    {w₁ w₂ : ℂ} (h₁ : w₁ ∈ gridCell R M p) (h₂ : w₂ ∈ gridCell R M p) :
    ‖w₁ - w₂‖ ≤ 2 * (2 * R / M) := by
  simp only [gridCell, mem_reProdIm, mem_Ico] at h₁ h₂
  have hre : |w₁.re - w₂.re| ≤ 2 * R / M := abs_le.mpr ⟨by linarith, by linarith⟩
  have him : |w₁.im - w₂.im| ≤ 2 * R / M := abs_le.mpr ⟨by linarith, by linarith⟩
  calc ‖w₁ - w₂‖ ≤ |(w₁ - w₂).re| + |(w₁ - w₂).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |w₁.re - w₂.re| + |w₁.im - w₂.im| := by simp
    _ ≤ 2 * (2 * R / M) := by linarith

private theorem mem_iUnion_gridCell_of_mem_ball {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 0 < M)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ∃ p : Fin M × Fin M, z ∈ gridCell R M p := by
  rw [mem_ball_zero_iff] at hz
  have h : 0 < 2 * R / M := by positivity
  have coord (x : ℝ) (hx : |x| < R) :
      ∃ k : Fin M, x ∈ Ico (-R + k * (2 * R / M)) (-R + (k + 1 : ℝ) * (2 * R / M)) := by
    obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hx
    let k := ⌊(x + R) / (2 * R / M)⌋₊
    have hnonneg : 0 ≤ (x + R) / (2 * R / M) := div_nonneg (by linarith) h.le
    have hltM : (x + R) / (2 * R / M) < M := by
      rw [div_lt_iff₀ h]
      have : (M : ℝ) * (2 * R / M) = 2 * R := mul_div_cancel₀ _ (by positivity)
      linarith
    have hkM : k < M := (Nat.floor_lt hnonneg).mpr hltM
    refine ⟨⟨k, hkM⟩, ?_, ?_⟩
    · dsimp only [k]
      have hle := (le_div_iff₀ h).mp (Nat.floor_le hnonneg)
      linarith
    · dsimp only [k]
      have hlt := (div_lt_iff₀ h).mp (Nat.lt_floor_add_one ((x + R) / (2 * R / M)))
      linarith
  obtain ⟨k₁, hk₁⟩ := coord z.re ((Complex.abs_re_le_norm z).trans_lt hz)
  obtain ⟨k₂, hk₂⟩ := coord z.im ((Complex.abs_im_le_norm z).trans_lt hz)
  exact ⟨(k₁, k₂), hk₁, hk₂⟩

/-- Pointwise telescoping bound on the Cauchy-kernel integrand over one active grid cell. -/
private theorem norm_integrand_sub_le {φ f : ℂ → ℂ} {z w ζ : ℂ} {r C Mf : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hrw : r ≤ ‖z - w‖) (hrζ : r ≤ ‖z - ζ‖)
    (hφw : ‖φ w‖ ≤ C) (hφζ : ‖φ ζ‖ ≤ C) (hφlip : ‖φ w - φ ζ‖ ≤ C * ‖w - ζ‖)
    (hfζ : ‖f ζ‖ ≤ Mf) (hflip : ‖f w - f ζ‖ ≤ Mf / r * ‖w - ζ‖) :
    ‖(z - w)⁻¹ * φ w * f w - (z - ζ)⁻¹ * φ ζ * f ζ‖ ≤
      C * (2 * r⁻¹ ^ 2 + r⁻¹) * Mf * ‖w - ζ‖ := by
  have hzw : z - w ≠ 0 := norm_ne_zero_iff.mp (hr.trans_le hrw).ne'
  have hzζ : z - ζ ≠ 0 := norm_ne_zero_iff.mp (hr.trans_le hrζ).ne'
  have hinv_w : ‖(z - w)⁻¹‖ ≤ r⁻¹ := by rw [norm_inv]; exact inv_anti₀ hr hrw
  have hinv_ζ : ‖(z - ζ)⁻¹‖ ≤ r⁻¹ := by rw [norm_inv]; exact inv_anti₀ hr hrζ
  have hinv_diff : ‖(z - w)⁻¹ - (z - ζ)⁻¹‖ ≤ r⁻¹ ^ 2 * ‖w - ζ‖ := by
    have hid : (z - w)⁻¹ - (z - ζ)⁻¹ = (w - ζ) * (z - w)⁻¹ * (z - ζ)⁻¹ := by
      field_simp [hzw, hzζ]; ring
    rw [hid, norm_mul, norm_mul]
    calc ‖w - ζ‖ * ‖(z - w)⁻¹‖ * ‖(z - ζ)⁻¹‖
        ≤ ‖w - ζ‖ * r⁻¹ * r⁻¹ := by gcongr
      _ = r⁻¹ ^ 2 * ‖w - ζ‖ := by ring
  have hsplit : (z - w)⁻¹ * φ w * f w - (z - ζ)⁻¹ * φ ζ * f ζ =
      (z - w)⁻¹ * φ w * (f w - f ζ) +
        (z - w)⁻¹ * (φ w - φ ζ) * f ζ + ((z - w)⁻¹ - (z - ζ)⁻¹) * φ ζ * f ζ := by
    ring
  rw [hsplit]
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
  have h1 : ‖(z - w)⁻¹ * φ w * (f w - f ζ)‖ ≤ r⁻¹ * C * (Mf / r * ‖w - ζ‖) := by
    rw [norm_mul, norm_mul]; gcongr
  have h2 : ‖(z - w)⁻¹ * (φ w - φ ζ) * f ζ‖ ≤ r⁻¹ * (C * ‖w - ζ‖) * Mf := by
    rw [norm_mul, norm_mul]; gcongr
  have h3 : ‖((z - w)⁻¹ - (z - ζ)⁻¹) * φ ζ * f ζ‖ ≤ r⁻¹ ^ 2 * ‖w - ζ‖ * C * Mf := by
    rw [norm_mul, norm_mul]; gcongr
  calc _ ≤ r⁻¹ * C * (Mf / r * ‖w - ζ‖) +
          r⁻¹ * (C * ‖w - ζ‖) * Mf + r⁻¹ ^ 2 * ‖w - ζ‖ * C * Mf := by gcongr
    _ = C * (2 * r⁻¹ ^ 2 + r⁻¹) * Mf * ‖w - ζ‖ := by
        rw [div_eq_mul_inv]; ring

/-- Continuity and integrability of the cutoff Cauchy integrand, and decomposition of its integral
over the grid cells meeting `tsupport φ`. -/
private theorem integrable_and_integral_eq_sum_filter_gridCell {φ f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hφ : Continuous φ) (hcptφ : HasCompactSupport φ) (hSU : tsupport φ ⊆ U)
    (hf : ContinuousOn f U) {R : ℝ} (hR : 0 < R) (hSball : tsupport φ ⊆ ball 0 R)
    {M : ℕ} (hM : 0 < M)
    [DecidablePred fun p : Fin M × Fin M ↦ (gridCell R M p ∩ tsupport φ).Nonempty]
    {z : ℂ} (hzS : ∀ w ∈ tsupport φ, z ≠ w) :
    Integrable (fun w ↦ (z - w)⁻¹ * φ w * f w) ∧
      ∫ w, (z - w)⁻¹ * φ w * f w =
        ∑ p ∈ Finset.univ.filter (fun p : Fin M × Fin M ↦ (gridCell R M p ∩ tsupport φ).Nonempty),
          ∫ w in gridCell R M p, (z - w)⁻¹ * φ w * f w := by
  set F : ℂ → ℂ := fun w ↦ (z - w)⁻¹ * φ w * f w
  have hFcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun w ↦ ?_
    by_cases hw : w ∈ U \ {z}
    · have hinv : ContinuousAt (fun y : ℂ ↦ (z - y)⁻¹) w :=
        (continuousAt_const.sub continuousAt_id).inv₀
          (sub_ne_zero.mpr (Ne.symm (mem_singleton_iff.not.mp hw.2)))
      exact (hinv.mul hφ.continuousAt).mul ((hf w hw.1).continuousAt (hU.mem_nhds hw.1))
    · have hnot : w ∉ tsupport φ := fun h ↦ hw ⟨hSU h, mem_singleton_iff.not.mpr (hzS w h).symm⟩
      have h0 : F =ᶠ[𝓝 w] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [F, hy]
      exact continuousAt_const.congr_of_eventuallyEq h0
  have hFint : Integrable F :=
    hFcont.integrable_of_hasCompactSupport (hcptφ.mul_left.mul_right)
  refine ⟨hFint, ?_⟩
  have hunion : ∫ w, F w =
      ∫ w in ⋃ p ∈ (Finset.univ : Finset (Fin M × Fin M)), gridCell R M p, F w := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ ?_).symm
    have hnot : w ∉ tsupport φ := fun hs ↦ by
      obtain ⟨p, hp⟩ := mem_iUnion_gridCell_of_mem_ball hR hM (hSball hs)
      exact hw (mem_biUnion (Finset.mem_univ p) hp)
    simp [F, image_eq_zero_of_notMem_tsupport hnot]
  rw [hunion, integral_biUnion_finset Finset.univ (fun p _ ↦ measurableSet_gridCell R M p)
    (pairwiseDisjoint_gridCell hR.le M) (fun p _ ↦ hFint.integrableOn)]
  refine (Finset.sum_filter_of_ne fun p _ hpne ↦ ?_).symm
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  refine hpne (setIntegral_eq_zero_of_forall_eq_zero fun w hw ↦ ?_)
  have hnot : w ∉ tsupport φ := fun hs ↦ Set.eq_empty_iff_forall_notMem.mp hempty w ⟨hw, hs⟩
  simp [F, image_eq_zero_of_notMem_tsupport hnot]

/-- Cellwise error estimate between the Cauchy integral over one active cell and its point-evaluated
simple-fraction term. -/
private theorem norm_setIntegral_gridCell_sub_le {φ f : ℂ → ℂ} {U L K : Set ℂ}
    (hU : IsOpen U) (hLU : L ⊆ U) (hf : DifferentiableOn ℂ f U)
    {z : ℂ} (hFint : Integrable fun w ↦ (z - w)⁻¹ * φ w * f w)
    {R r C Mf : ℝ} (hR : 0 < R) (hr : 0 < r) (hC : 0 ≤ C) (hMf : 0 ≤ Mf)
    (hML : ∀ x ∈ L, ‖f x‖ ≤ Mf) (hφnorm : ∀ w, ‖φ w‖ ≤ C)
    (hφlip : ∀ w₁ w₂, ‖φ w₁ - φ w₂‖ ≤ C * ‖w₁ - w₂‖)
    {M : ℕ} (hmesh : 2 * (2 * R / M) < r) {p : Fin M × Fin M} {ζ : ℂ}
    (hζcell : ζ ∈ gridCell R M p) (hball_sub : closedBall ζ (3 * r) ⊆ interior L \ K)
    (hz : z ∈ K) :
    ‖(∫ w in gridCell R M p, (z - w)⁻¹ * φ w * f w) -
        (((2 * R / M) ^ 2 : ℝ) : ℂ) * φ ζ * f ζ * (z - ζ)⁻¹‖ ≤
      C * (2 * r⁻¹ ^ 2 + r⁻¹) * Mf * (2 * (2 * R / M)) * (2 * R / M) ^ 2 := by
  set h := 2 * R / M
  have hz3r : 3 * r < ‖z - ζ‖ := by
    by_contra hle
    exact (hball_sub (mem_closedBall.mpr (by simpa [dist_eq_norm] using not_lt.mp hle))).2 hz
  have h2rL : closedBall ζ (2 * r) ⊆ L :=
    (closedBall_subset_closedBall (by linarith)).trans
      (hball_sub.trans (sdiff_subset.trans interior_subset))
  have hconst_int : (((h ^ 2 : ℝ) : ℂ) * φ ζ * f ζ * (z - ζ)⁻¹) =
      ∫ _ in gridCell R M p, (z - ζ)⁻¹ * φ ζ * f ζ := by
    rw [setIntegral_const, volume_real_gridCell hR.le p, Complex.real_smul]
    ring
  have hc_int : IntegrableOn (fun _ : ℂ ↦ (z - ζ)⁻¹ * φ ζ * f ζ) (gridCell R M p) :=
    integrableOn_const (by rw [volume_gridCell hR.le]; exact ENNReal.ofReal_lt_top.ne)
  rw [hconst_int, ← integral_sub hFint.integrableOn hc_int, ← volume_real_gridCell hR.le p]
  refine norm_setIntegral_le_of_norm_le_const
    (by rw [volume_gridCell hR.le]; exact ENNReal.ofReal_lt_top) fun w hw ↦ ?_
  have hwζ : ‖w - ζ‖ ≤ 2 * h := norm_sub_le_of_mem_gridCell hw hζcell
  have hw_ball : w ∈ ball ζ r := mem_ball.mpr (by rw [dist_eq_norm]; exact hwζ.trans_lt hmesh)
  have hrw : r ≤ ‖z - w‖ := by
    have htri : ‖z - ζ‖ ≤ ‖z - w‖ + ‖w - ζ‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub z w ζ
    linarith
  have hflip : ‖f w - f ζ‖ ≤ Mf / r * ‖w - ζ‖ := by
    simpa [dist_eq_norm] using dist_le_of_forall_mem_closedBall_two_mul_norm_le hU hf hr
      (h2rL.trans hLU) (fun x hx ↦ hML x (h2rL hx)) hw_ball (mem_ball_self hr)
  have hfζ : ‖f ζ‖ ≤ Mf := hML ζ (h2rL (mem_closedBall_self (by positivity)))
  exact (norm_integrand_sub_le hr hC hrw (by linarith) (hφnorm w) (hφnorm ζ) (hφlip w ζ)
    hfζ hflip).trans (by gcongr)

/-- Choice of a positive grid subdivision count `M` making the cell diameter smaller than `r` and
the total Riemann-sum error factor at most `ε`. -/
private theorem exists_mesh_lt_and_le (R K₀ : ℝ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ 2 * (2 * R / M) < r ∧ 4 * R ^ 2 * K₀ * (2 * (2 * R / M)) ≤ ε := by
  obtain ⟨M, hMgt⟩ := exists_nat_gt (max 1 (max (4 * R / r) (16 * R ^ 3 * K₀ / ε)))
  have hM1 : (1 : ℝ) < M := (le_max_left _ _).trans_lt hMgt
  have hM : 0 < M := Nat.cast_pos.mp (zero_lt_one.trans hM1)
  have hMpos : (0 : ℝ) < M := by positivity
  refine ⟨M, hM, ?_, ?_⟩
  · have hlt : 4 * R / r < M := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hMgt
    have heq : 2 * (2 * R / M) = 4 * R / M := by ring
    rw [div_lt_iff₀ hr] at hlt
    rw [heq, div_lt_iff₀ hMpos]
    linarith
  · have hlt : 16 * R ^ 3 * K₀ / ε < M :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hMgt
    have heq : 4 * R ^ 2 * K₀ * (2 * (2 * R / M)) = 16 * R ^ 3 * K₀ / M := by ring
    rw [div_lt_iff₀ hε] at hlt
    rw [heq, div_le_iff₀ hMpos]
    linarith

/-- Global Riemann-sum bound over the active grid cells meeting `tsupport φ`. -/
private theorem norm_integral_sub_sum_gridCell_le {φ f : ℂ → ℂ} {U L K : Set ℂ}
    (hU : IsOpen U) (hLU : L ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hφ : Continuous φ) (hcptφ : HasCompactSupport φ) (hS_sub : tsupport φ ⊆ interior L \ K)
    {R r C Mf ε : ℝ} (hR : 0 < R) (hr : 0 < r) (hC : 0 ≤ C) (hMf : 0 ≤ Mf)
    (hSball : tsupport φ ⊆ ball 0 R)
    (hML : ∀ x ∈ L, ‖f x‖ ≤ Mf) (hφnorm : ∀ w, ‖φ w‖ ≤ C)
    (hφlip : ∀ w₁ w₂, ‖φ w₁ - φ w₂‖ ≤ C * ‖w₁ - w₂‖)
    {M : ℕ} (hM : 0 < M) (hmesh : 2 * (2 * R / M) < r)
    (herr : 4 * R ^ 2 * (C * (2 * r⁻¹ ^ 2 + r⁻¹)) * (2 * (2 * R / M)) ≤ ε)
    [DecidablePred fun p : Fin M × Fin M ↦ (gridCell R M p ∩ tsupport φ).Nonempty]
    {J : Finset (Fin M × Fin M)}
    (hJ : J = Finset.univ.filter fun p : Fin M × Fin M ↦ (gridCell R M p ∩ tsupport φ).Nonempty)
    (e : Fin J.card ≃ J) {ζ : Fin J.card → ℂ}
    (hζcell : ∀ j, ζ j ∈ gridCell R M (e j))
    (h3r : ∀ j, closedBall (ζ j) (3 * r) ⊆ interior L \ K)
    {z : ℂ} (hz : z ∈ K) :
    ‖(∫ w, (z - w)⁻¹ * φ w * f w) -
        ∑ j, ((((2 * R / M) ^ 2 : ℝ) : ℂ) * φ (ζ j)) * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε * Mf := by
  set K₀ := C * (2 * r⁻¹ ^ 2 + r⁻¹)
  obtain ⟨hFint, hint_eq⟩ := integrable_and_integral_eq_sum_filter_gridCell hU hφ hcptφ
    (hS_sub.trans (sdiff_subset.trans (interior_subset.trans hLU))) hf.continuousOn hR hSball hM
    (fun w hw heq ↦ (hS_sub hw).2 (heq ▸ hz))
  have hsum_eq : ∫ w, (z - w)⁻¹ * φ w * f w =
      ∑ j : Fin J.card, ∫ w in gridCell R M (e j), (z - w)⁻¹ * φ w * f w := by
    rw [hint_eq, ← hJ, ← Finset.sum_coe_sort J]
    exact (Equiv.sum_comp e fun p ↦ ∫ w in gridCell R M p, (z - w)⁻¹ * φ w * f w).symm
  rw [hsum_eq, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hcard : (J.card : ℝ) * (2 * R / M) ^ 2 ≤ 4 * R ^ 2 := by
    have hJM : J.card ≤ M * M := (Finset.card_le_univ J).trans (by simp)
    have hJM' : (J.card : ℝ) ≤ (M : ℝ) ^ 2 := by rw [sq]; exact_mod_cast hJM
    have hMpos : (0 : ℝ) < M := by positivity
    calc (J.card : ℝ) * (2 * R / M) ^ 2 ≤ (M : ℝ) ^ 2 * (2 * R / M) ^ 2 := by gcongr
      _ = 4 * R ^ 2 := by field_simp [hMpos.ne']; ring
  calc ∑ j : Fin J.card, ‖(∫ w in gridCell R M (e j), (z - w)⁻¹ * φ w * f w) -
          ((((2 * R / M) ^ 2 : ℝ) : ℂ) * φ (ζ j)) * f (ζ j) * (z - ζ j)⁻¹‖
      ≤ ∑ _ : Fin J.card, K₀ * Mf * (2 * (2 * R / M)) * (2 * R / M) ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ norm_setIntegral_gridCell_sub_le hU hLU hf hFint hR hr hC hMf
          hML hφnorm hφlip hmesh (hζcell j) (h3r j) hz
    _ = ((J.card : ℝ) * (2 * R / M) ^ 2) * (K₀ * (2 * (2 * R / M)) * Mf) := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (4 * R ^ 2) * (K₀ * (2 * (2 * R / M)) * Mf) := by gcongr
    _ = (4 * R ^ 2 * K₀ * (2 * (2 * R / M))) * Mf := by ring
    _ ≤ ε * Mf := by gcongr

/-- **Uniform rational collar approximation (scalar form).** Let `K, L ⊆ ℂ` be compact with
`K ⊆ interior L`. For every `ε > 0` there exist `N : ℕ`, poles `ζ : Fin N → ℂ` in `interior L \ K`,
and weights `c : Fin N → ℂ`, depending only on `K`, `L`, and `ε`, such that every function `f`
holomorphic on an open set `U ⊇ L` satisfies
`‖f z - ∑ j, c j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L)` for all `z ∈ K`. -/
theorem IsCompact.exists_fin_mem_sdiff_norm_sub_sum_mul_inv_le
    {K L : Set ℂ} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧
      ∀ ⦃U : Set ℂ⦄, IsOpen U → L ⊆ U → ∀ ⦃f : ℂ → ℂ⦄, DifferentiableOn ℂ f U →
        ∀ z ∈ K, ‖f z - ∑ j, c j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ ε * sSup ((fun x ↦ ‖f x‖) '' L) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, Fin.elim0, Fin.elim0, fun j ↦ j.elim0, fun _ _ _ _ _ _ hz ↦ hz.elim⟩
  have hLne : L.Nonempty := hKne.mono (hKL.trans interior_subset)
  obtain ⟨φ, hφ, hcptφ, hS_sub, hrep⟩ :=
    hK.exists_contDiff_tsupport_subset_sdiff_eq_integral_sub_inv_mul hKL
  obtain ⟨δ, hδ, hcthick⟩ :=
    hcptφ.exists_cthickening_subset_open (isOpen_interior.sdiff hK.isClosed) hS_sub
  set r := δ / 3
  have hr : 0 < r := by positivity
  obtain ⟨R₀, hR₀⟩ := hcptφ.isBounded.subset_ball (0 : ℂ)
  set R := max R₀ 1
  have hR : 0 < R := by positivity
  have hSball : tsupport φ ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨C, hφH, hφnorm⟩ :=
    (hφ.of_le (by simp)).exists_holderWith_and_norm_le_of_hasCompactSupport hcptφ le_rfl
  have hφlip : ∀ w₁ w₂, ‖φ w₁ - φ w₂‖ ≤ (C : ℝ) * ‖w₁ - w₂‖ := fun w₁ w₂ ↦ by
    simpa [dist_eq_norm] using (holderWith_one.mp hφH).dist_le_mul w₁ w₂
  obtain ⟨M, hM, hmesh, herr⟩ := exists_mesh_lt_and_le R ((C : ℝ) * (2 * r⁻¹ ^ 2 + r⁻¹)) hr hε
  set J := Finset.univ.filter (fun p : Fin M × Fin M ↦ (gridCell R M p ∩ tsupport φ).Nonempty)
  let e : Fin J.card ≃ J := J.equivFin.symm
  let ζ : Fin J.card → ℂ := fun j ↦ ((Finset.mem_filter.mp (e j).2).2).choose
  have hζmem : ∀ j, ζ j ∈ gridCell R M (e j) ∧ ζ j ∈ tsupport φ :=
    fun j ↦ ((Finset.mem_filter.mp (e j).2).2).choose_spec
  have h3r : ∀ j, closedBall (ζ j) (3 * r) ⊆ interior L \ K := fun j ↦ by
    have h3 : 3 * r = δ := by simp [r]; ring
    exact h3.symm ▸ (closedBall_subset_cthickening (hζmem j).2 δ).trans hcthick
  refine ⟨J.card, ζ, fun j ↦ (((2 * R / M) ^ 2 : ℝ) : ℂ) * φ (ζ j), fun j ↦ hS_sub (hζmem j).2,
    fun U hU hLU f hf z hz ↦ ?_⟩
  have hbdd : BddAbove ((fun x ↦ ‖f x‖) '' L) :=
    (hL.image_of_continuousOn
      (continuous_norm.comp_continuousOn (hf.continuousOn.mono hLU))).bddAbove
  have hML : ∀ x ∈ L, ‖f x‖ ≤ sSup ((fun x ↦ ‖f x‖) '' L) := fun x hx ↦ le_csSup hbdd ⟨x, hx, rfl⟩
  rw [hrep hU (interior_subset.trans hLU) hf z hz]
  exact norm_integral_sub_sum_gridCell_le hU hLU hf hφ.continuous hcptφ hS_sub hR hr C.coe_nonneg
    ((norm_nonneg _).trans (hML hLne.some hLne.some_mem)) hSball hML hφnorm hφlip hM hmesh herr
    rfl e (fun j ↦ (hζmem j).1) h3r hz

/-- **Uniform rational collar approximation (normed-space form).** The poles and weights from
`IsCompact.exists_fin_mem_sdiff_norm_sub_sum_mul_inv_le` simultaneously approximate holomorphic
maps into any complex normed space `F`, with no completeness assumption on `F`. -/
theorem IsCompact.exists_fin_mem_sdiff_norm_sub_sum_inv_smul_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {K L : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ),
      (∀ j, ζ j ∈ interior L \ K) ∧
      ∀ ⦃U : Set ℂ⦄, IsOpen U → L ⊆ U → ∀ ⦃f : ℂ → F⦄, DifferentiableOn ℂ f U →
        ∀ z ∈ K, ‖f z - ∑ j, (c j * (z - ζ j)⁻¹) • f (ζ j)‖ ≤
          ε * sSup ((fun x ↦ ‖f x‖) '' L) := by
  obtain ⟨N, ζ, c, hζ, happrox⟩ := hK.exists_fin_mem_sdiff_norm_sub_sum_mul_inv_le hL hKL hε
  refine ⟨N, ζ, c, hζ, fun U hU hLU f hf z hz ↦ ?_⟩
  exact hf.norm_sub_sum_mul_smul_le_of_forall_differentiableOn (g := fun j y ↦ (y - ζ j)⁻¹)
    (z := z) hL hLU hε.le fun φ hφ ↦ happrox hU hLU hφ z hz

end RationalApproximation
