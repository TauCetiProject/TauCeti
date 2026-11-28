/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Momentum and force of a quadratic action

The inverse Riesz map turns the spatial derivative covector into a force vector. Its smoothness,
pairing formula and norm bound give integrable momentum and force for square-integrable velocities.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

-- Cache the canonical nested operator-space instances.
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticForceDualNormedAddCommGroup : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticForceDualNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticForceBilinearNormedAddCommGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticForceBilinearNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticForceTrilinearNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticForceTrilinearNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The Riesz representative of one-half the spatial kinetic derivative plus the spatial
potential derivative. -/
noncomputable def quadraticForceVector (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w : F) : F :=
  (InnerProductSpace.toDual ℝ F).symm
    ((1 / 2 : ℝ) • ((DG.flip w).flip w) + DV)

/-- The quadratic force is the inverse Riesz image of the spatial derivative covector. -/
theorem quadraticForceVector_def (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w : F) :
    quadraticForceVector DG DV w =
      (InnerProductSpace.toDual ℝ F).symm ((1 / 2 : ℝ) • ((DG.flip w).flip w) + DV) := by
  rfl

/-- The quadratic force depends smoothly on its two coefficient derivatives and velocity. -/
theorem contDiff_quadraticForceVector {n : ℕ∞ω} :
    ContDiff ℝ n (fun z : ((F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) × F ↦
      quadraticForceVector z.1.1 z.1.2 z.2) := by
  have hD : ContDiff ℝ n
      (fun z : ((F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) × F ↦ z.1.1) :=
    contDiff_fst.fst
  have hDf := (ContinuousLinearMap.flipₗᵢ ℝ F F (F →L[ℝ] ℝ)).contDiff.comp hD
  have hDq := hDf.clm_apply contDiff_snd
  have hDqf := (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).contDiff.comp hDq
  exact (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.contDiff.comp
    (((contDiff_const (c := (1 / 2 : ℝ))).smul (hDqf.clm_apply contDiff_snd)).add
      contDiff_fst.snd)

/-- Pairing the force vector with a test vector recovers the spatial kinetic-plus-potential
derivative. -/
theorem inner_quadraticForceVector (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w z : F) :
    inner ℝ z (quadraticForceVector DG DV w) = DG z w w / 2 + DV z := by
  rw [real_inner_comm, quadraticForceVector, InnerProductSpace.toDual_symm_apply]
  simp only [add_apply, smul_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring

/-- The force norm is bounded by one-half coefficient derivative norm times squared velocity
plus potential derivative norm. -/
theorem norm_quadraticForceVector_le (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w : F) :
    ‖quadraticForceVector DG DV w‖ ≤ ‖DG‖ * ‖w‖ ^ 2 / 2 + ‖DV‖ := by
  have hL : ‖(DG.flip w).flip w‖ ≤ ‖DG‖ * ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖(DG.flip w).flip‖ * ‖w‖ := ((DG.flip w).flip).le_opNorm w
      _ = ‖DG.flip w‖ * ‖w‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖DG.flip‖ * ‖w‖) * ‖w‖ := by
        gcongr
        exact DG.flip.le_opNorm w
      _ = ‖DG‖ * ‖w‖ ^ 2 := by rw [ContinuousLinearMap.opNorm_flip]; ring
  rw [quadraticForceVector, (InnerProductSpace.toDual ℝ F).symm.norm_map]
  calc
    _ ≤ ‖(1 / 2 : ℝ) • ((DG.flip w).flip w)‖ + ‖DV‖ := norm_add_le _ _
    _ = ‖(DG.flip w).flip w‖ / 2 + ‖DV‖ := by rw [norm_smul]; norm_num; ring
    _ ≤ _ := by gcongr

/-- Continuous bounded coefficients and L² velocities give integrable actual momentum and force. -/
theorem intervalIntegrable_quadraticMomentum_force {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → F) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (G : ℝ → F →L[ℝ] F →L[ℝ] ℝ)
    (DG : ℝ → F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (DV : ℝ → F →L[ℝ] ℝ)
    (hG : ContinuousOn G (Icc a b)) (hDG : ContinuousOn DG (Icc a b))
    (hDV : ContinuousOn DV (Icc a b)) :
    IntervalIntegrable (fun s ↦ InnerProductSpace.continuousLinearMapOfBilin (G s) (w s))
      volume a b ∧
      IntervalIntegrable (fun s ↦ quadraticForceVector (DG s) (DV s) (w s)) volume a b := by
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hDG
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hDV
  let μ := volume.restrict (Icc a b)
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G μ := hG.aestronglyMeasurable measurableSet_Icc
  have hDGm : AEStronglyMeasurable DG μ := hDG.aestronglyMeasurable measurableSet_Icc
  have hDVm : AEStronglyMeasurable DV μ := hDV.aestronglyMeasurable measurableSet_Icc
  have hAm := InnerProductSpace.continuous_continuousLinearMapOfBilin.comp_aestronglyMeasurable hGm
  have heval : Continuous (fun p : (F →L[ℝ] F) × F ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hPm : AEStronglyMeasurable
      (fun s ↦ InnerProductSpace.continuousLinearMapOfBilin (G s) (w s)) μ :=
    heval.comp_aestronglyMeasurable (hAm.prodMk hwm)
  have hDf : AEStronglyMeasurable (fun s ↦ (DG s).flip) μ :=
    (ContinuousLinearMap.flipₗᵢ ℝ F F (F →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable hDGm
  have hDfw := (ContinuousLinearMap.id ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (𝕜 := ℝ) hDf hwm
  have hDfwf : AEStronglyMeasurable (fun s ↦ ((DG s).flip (w s)).flip) μ :=
    (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).continuous.comp_aestronglyMeasurable hDfw
  have hL := (ContinuousLinearMap.id ℝ (F →L[ℝ] F →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (𝕜 := ℝ) hDfwf hwm
  have hQm : AEStronglyMeasurable (fun s ↦ quadraticForceVector (DG s) (DV s) (w s)) μ :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_aestronglyMeasurable
      ((hL.const_smul (1 / 2 : ℝ)).add hDVm)
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply ((MemLp.integrable (by norm_num) hw).norm.const_mul C₀).mono' hPm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [InnerProductSpace.norm_continuousLinearMapOfBilin_apply]
    exact ((G s).le_opNorm (w s)).trans
      (mul_le_mul_of_nonneg_right (hC₀ s hs) (norm_nonneg _))
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    have hi : Integrable (fun s ↦ C₁ * ‖w s‖ ^ 2 / 2 + C₂) μ :=
      ((hw.norm.integrable_sq.const_mul C₁).div_const 2).add (integrable_const C₂)
    apply hi.mono' hQm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    apply (norm_quadraticForceVector_le (DG s) (DV s) (w s)).trans
    gcongr
    · exact hC₁ s hs
    · exact hC₂ s hs

end TauCeti
