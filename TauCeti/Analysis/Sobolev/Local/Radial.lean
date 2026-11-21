/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Critical inverse-norm and radial singularities in local Sobolev classes

Near the origin of a nontrivial finite-dimensional real normed space `E` of dimension `d`, the
inverse norm `x ↦ ‖x‖⁻¹` belongs to `TauCeti.MemLpLoc p U` if and only if `p < d`
(`TauCeti.memLpLoc_norm_inv_iff`).

On a finite-dimensional real inner product space of dimension `d ≥ 2`, the normalized radial map
`NormedSpace.normalize : E → E` (`x ↦ ‖x‖⁻¹ • x`) belongs to `TauCeti.MemWkpLoc p U 1` near the
origin if and only if `p < d` (`TauCeti.memWkpLoc_one_normalize_iff`).

## Main declarations

* `TauCeti.memLpLoc_norm_inv_iff`: `x ↦ ‖x‖⁻¹` is locally `Lᵖ` near `0` iff `p < dim E`.
* `TauCeti.memWkpLoc_one_normalize`: `NormedSpace.normalize` is in `W^{1,p}_loc` everywhere for
  `p < dim E` when `1 < dim E`.
* `TauCeti.not_memWkpLoc_one_normalize`: `NormedSpace.normalize` is not in `W^{1,p}_loc` near `0`
  for `dim E ≤ p` when `1 < dim E`.
* `TauCeti.memWkpLoc_one_normalize_iff`: characterization `MemWkpLoc p U 1 NormedSpace.normalize ↔
  p < dim E` near the origin for `1 < dim E`.
-/

public noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology RealInnerProductSpace

namespace TauCeti

section RadialSingularity

/-- On any nontrivial finite-dimensional real normed space `E`, `‖x‖⁻¹` is locally `Lᵖ`
near the origin exactly when `p < dim E`. -/
theorem memLpLoc_norm_inv_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {p : ENNReal} {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK =>
    hK.isBounded.memLp_norm_inv_restrict h⟩
  by_contra! hpd
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hpd (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {p : ENNReal} {U : Set E}

private theorem memWkpLoc_one_norm_rpow_neg_one_mul_inner (hd : 1 < Module.finrank ℝ E)
    (hp : p < Module.finrank ℝ E) (v : E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫) := by
  have hs : -(Module.finrank ℝ E : ℝ) < (-1 : ℝ) := by
    have : (1 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
    linarith
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, _,
    hasWeakFDerivOn_norm_rpow_mul_inner hs v _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K _ hK => ?_)⟩
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖v‖
      (Eventually.of_forall fun x => by simpa using abs_norm_rpow_mul_inner_le (-1) v x)
  · have hker : MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict K) :=
      hK.isBounded.memLp_norm_inv_restrict hp
    refine (hker.const_mul ((1 + |(-1 : ℝ)|) * ‖v‖)).of_le
      (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_norm_rpow_smul_innerSL_add_le (-1) v x

/-- In dimension `d ≥ 2`, the normalized radial map `NormedSpace.normalize` (`x ↦ ‖x‖⁻¹ • x`)
lies in `MemWkpLoc p U 1` on every set whenever `p < d`. -/
theorem memWkpLoc_one_normalize (hd : 1 < Module.finrank ℝ E) (hp : p < Module.finrank ℝ E) :
    MemWkpLoc p U 1 (NormedSpace.normalize : E → E) := by
  let b := stdOrthonormalBasis ℝ E
  rw [b.toBasis.memWkpLoc_iff]
  intro i
  have heq : (fun x : E => b.toBasis.repr (NormedSpace.normalize x) i) =
      fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫ := by
    funext x
    rw [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply, NormedSpace.normalize,
      inner_smul_right, real_inner_comm, Real.rpow_neg_one]
  rw [heq]
  exact memWkpLoc_one_norm_rpow_neg_one_mul_inner hd hp (b i)

/-- In dimension `d ≥ 2`, the normalized radial map `NormedSpace.normalize` is not in
`MemWkpLoc p U 1` for any `p ≥ d` when `0 ∈ interior U`. -/
theorem not_memWkpLoc_one_normalize (hd : 1 < Module.finrank ℝ E)
    (hp : Module.finrank ℝ E ≤ p) (h0 : (0 : E) ∈ interior U) :
    ¬ MemWkpLoc p U 1 (NormedSpace.normalize : E → E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (zero_lt_one.trans hd)
  intro h
  obtain ⟨-, D, hD, hDLp⟩ := by simpa only [memWkpLoc_zero_iff] using memWkpLoc_succ_iff.1 h
  set Ω' : Opens E := Opens.interior U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hsmooth : ContDiffOn ℝ 1 (NormedSpace.normalize : E → E) (Ω' : Set E) := fun x hx =>
    (((contDiffAt_norm ℝ hx.2 : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).inv
      (norm_ne_zero_iff.2 hx.2)).smul contDiffAt_id).contDiffWithinAt
  have hfu : HasWeakFDerivOn volume Ω' (NormedSpace.normalize : E → E)
      (fderiv ℝ (NormedSpace.normalize : E → E)) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hsmooth.continuousOn_fderiv_of_isOpen Ω'.isOpen le_rfl).locallyIntegrableOn
        Ω'.isOpen.measurableSet)
      fun x hx => (hsmooth.differentiableOn one_ne_zero).differentiableAt (Ω'.isOpen.mem_nhds hx)
  have hae : D =ᵐ[volume.restrict Ω'] fderiv ℝ (NormedSpace.normalize : E → E) :=
    (hD.mono inf_le_left).ae_eq hfu
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hK : closedBall (0 : E) (r / 2) ⊆ interior U :=
    (closedBall_subset_ball (by linarith)).trans hrU
  have hDK : MemLp D p (volume.restrict (closedBall (0 : E) (r / 2))) :=
    memLpLoc_iff.1 hDLp _ (hK.trans interior_subset) (isCompact_closedBall 0 _)
  have hinvK :
      MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict (closedBall (0 : E) (r / 2))) := by
    refine hDK.of_le (by fun_prop : Measurable fun x : E => ‖x‖⁻¹).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_closedBall]
    have h1 := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 hae
    have hnull : ∀ᵐ x ∂(volume : Measure E), x ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [h1, hnull] with x hx hx0 hxb
    rw [hx ⟨hK hxb, hx0⟩, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x))]
    have horth : (Submodule.span ℝ ({x} : Set E))ᗮ ≠ ⊥ := by
      intro hbot
      have hsum := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({x} : Set E))
      rw [hbot, finrank_bot, add_zero] at hsum
      have hle : Module.finrank ℝ (Submodule.span ℝ ({x} : Set E)) ≤ 1 :=
        (finrank_span_singleton hx0).le
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
    have hxv : ⟪x, v⟫ = 0 := by
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv
    exact inv_norm_le_norm_fderiv_normalize hx0 hv0 hxv
  exact not_memLp_norm_inv_closedBall (half_pos hr) hp hinvK

/-- **Critical exponent for `NormedSpace.normalize`.** On a finite-dimensional real inner product
space of dimension `d ≥ 2`, `NormedSpace.normalize` lies in `MemWkpLoc p U 1` on any set whose
interior contains the origin iff `p < d`. -/
theorem memWkpLoc_one_normalize_iff (hd : 1 < Module.finrank ℝ E) (h0 : (0 : E) ∈ interior U) :
    MemWkpLoc p U 1 (NormedSpace.normalize : E → E) ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_one_normalize hd hp h0 h,
    fun hp => memWkpLoc_one_normalize hd hp⟩

end Normalize

end RadialSingularity

end TauCeti
