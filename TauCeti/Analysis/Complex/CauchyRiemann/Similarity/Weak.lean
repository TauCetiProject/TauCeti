/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.Wirtinger.Beurling.Lp
import TauCeti.Analysis.Complex.Wirtinger.Weyl
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Basic.Real.ConjExponents
import TauCeti.MeasureTheory.Function.LpSeminorm.ClosedBall
import TauCeti.MeasureTheory.Function.RankOne
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The similarity principle for weak solutions with `Lᵖ` coefficients

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, `2 < p < ∞`, and let
`ξ : ℂ → V` be a weak solution on `Ω` of the linear Cauchy–Riemann equation

`∂ₛξ + i ∂ₜξ + C ξ = 0`

in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`: `ξ` is continuous and of class
`W^{1,p}_loc`, and the equation holds almost everywhere, for a field `C ∈ Lᵖ_loc(Ω)` of
*real*-linear endomorphisms of `V`. The **similarity principle** (Carleman; McDuff–Salamon,
Theorem 2.3.5) says that near every point `z₀ ∈ Ω` the solution factors as `ξ = Φ σ`, with `Φ` a
continuous family of invertible complex-linear maps of class `W^{1,p}_loc` and `σ` holomorphic
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id`). So `ξ` inherits the zero
structure of a holomorphic map: unique continuation from an open set or from a zero of infinite
order, isolated zeros, and positive finite orders of its zeros. These consequences do not mention
the exponent and also hold for `p = ∞`, by passing to a finite exponent.

The proof is the one of `TauCeti.exists_similarity_of_contDiffOn` for classical solutions with
bounded coefficients, with two changes. The Cauchy integral equation `Ψ = 1 + T (½ Ψ D)` for the
absorbed complex-linear coefficient `D` (`TauCeti.rankOneDivNormSq`) is solved on a disc so small
that `‖C‖_{Lᵖ}` on it is small (`TauCeti.exists_cauchyTransform_eq_of_memLp`), the pointwise
bound for the Cauchy transform of `Lᵖ` data taking the place of the bound `‖C‖_∞ r`. And the weak
derivative of `σ = Ψ ξ` comes from the weak Leibniz rule
(`TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`), applied to the weak derivative of the Cauchy
transform of `Lᵖ` data (`TauCeti.exists_hasWeakFDerivOn_cauchyTransform_of_memLp`). Then
`bar∂σ = ½ Ψ D ξ - ½ Ψ C ξ = 0` weakly, so `σ` is holomorphic by Weyl's lemma, and `Φ = Ψ⁻¹` is
of class `W^{1,p}_loc` by the chain rule for inverses.

Some integrability hypothesis on `C` cannot be omitted altogether: `ξ = exp(-1/|z|²)` vanishes to
infinite order at `0` and solves the equation for a coefficient of size `|z|⁻³`, which is not in
`Lᵖ_loc` near `0` for any `p ≥ 1`.

## Main results

* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id`: the local factorization
  `ξ = Φ σ` on a disc, with `Φ` continuous, invertible and of class `W^{1,p}_loc`.
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id`: the
  factorization in the form consumed by `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_eqOn_zero` and
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_forall_isBigO`: unique
  continuation.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_I_smul_id` and
  `TauCeti.exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemannOn_I_smul_id`: isolated zeros with
  positive orders.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Small discs -/

/-- About a point `z₀` of an open set `Ω`, a field `C ∈ Lᵖ_loc(Ω)`, `1 ≤ p < ∞`, is dominated on a
small closed disc of radius `r` by a function `G ∈ Lᵖ` with `π⁻¹ ‖K_{2R}‖_{L^q} ‖G‖_{Lᵖ} ≤ 1/2`,
where `closedBall z₀ R ⊆ Ω` with `r ≤ R` and `K_{2R}` is the reciprocal kernel truncated at `2R`.
These are the hypotheses of `TauCeti.exists_cauchyTransform_eq_of_memLp`. -/
private theorem exists_closedBall_eLpNorm_le {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0}
    (hp1 : (1 : ℝ≥0∞) ≤ p) {Ω : Opens ℂ} {C : ℂ → F} (hC : MemLpLoc p Ω C) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (q : ℝ≥0∞) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ R ∧ closedBall z₀ R ⊆ Ω ∧ ∃ G : ℂ → ℝ, MemLp G p volume ∧
      (∀ z ∈ closedBall z₀ r, ‖C z‖ ≤ G z) ∧
      Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal *
        (eLpNorm G p volume).toReal ≤ 2⁻¹ := by
  -- a closed disc in `Ω` on which `C` is in `Lᵖ`
  obtain ⟨R', hR', hR'Ω⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  set R := R' / 2
  have hR : 0 < R := by positivity
  have hKΩ : closedBall z₀ R ⊆ Ω := (closedBall_subset_ball (half_lt_self hR')).trans hR'Ω
  have hCK : MemLp ((closedBall z₀ R).indicator C) p volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2
      (memLpLoc_iff.1 hC _ hKΩ (isCompact_closedBall _ _))
  -- a smaller disc on which the `Lᵖ` norm of `C` is small
  set κ := Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) q volume).toReal
  obtain ⟨r, hr, hrR, hsmallr⟩ := exists_eLpNorm_indicator_closedBall_le hp1
    ENNReal.coe_ne_top hCK.norm (measure_singleton z₀) hR
    (ε := ENNReal.ofReal (2 * (κ + 1))⁻¹) (ENNReal.ofReal_pos.2 (by positivity))
  have hrK : closedBall z₀ r ⊆ closedBall z₀ R := closedBall_subset_closedBall hrR
  refine ⟨r, R, hr, hrR, hKΩ, (closedBall z₀ r).indicator fun z ↦ ‖(closedBall z₀ R).indicator C z‖,
    hCK.norm.indicator measurableSet_closedBall.nullMeasurableSet, fun z hz ↦ ?_, ?_⟩
  · simp only [indicator_of_mem hz, indicator_of_mem (hrK hz), le_refl]
  · calc κ * (eLpNorm _ p volume).toReal ≤ κ * (2 * (κ + 1))⁻¹ := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsmallr
      _ ≤ 2⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
          linarith

/-! ### The similarity principle on a complex inner product space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The similarity principle** on a complex inner product space, for a weak solution with an
`Lᵖ` coefficient: the factorization on a disc. -/
private theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_innerProductSpace
    [FiniteDimensional ℂ E] {p : ℝ≥0} (hp : 2 < p) {Ω : Opens ℂ} {ξ : ℂ → E}
    {C : ℂ → E →L[ℝ] E} (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  have hp2 : (2 : ℝ≥0∞) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ≥0∞) < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp2
  set q := (p : ℝ≥0∞).conjExponent
  have : (p : ℝ≥0∞).HolderConjugate q := .conjExponent hp1.le
  have hq : q < 2 := ENNReal.conjExponent_lt_two hp2
  obtain ⟨hξc, hξp, Dξ, hDξ, hDξp, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 hξ
  -- a disc on which `C` has small `Lᵖ` norm
  obtain ⟨r, R, hr, hrR, hKΩ, G, hG, hCG, hsmall⟩ := exists_closedBall_eLpNorm_le hp1.le hC hz₀ q
  have hsubΩ : closedBall z₀ r ⊆ Ω := (closedBall_subset_closedBall hrR).trans hKΩ
  have hball : ball z₀ r ⊆ Ω := ball_subset_closedBall.trans hsubΩ
  -- absorb the real-linear coefficient and solve the Cauchy integral equation
  have hDm : AEStronglyMeasurable (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z))
      (volume.restrict (closedBall z₀ r)) :=
    (memLpLoc_iff.1 hC _ hsubΩ (isCompact_closedBall _ _)).aestronglyMeasurable
      |>.rankOneDivNormSq_apply ((hξc.mono hsubΩ).aestronglyMeasurable measurableSet_closedBall)
  have hDG (z : ℂ) (hz : z ∈ closedBall z₀ r) :
      ‖rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)‖ ≤ G z :=
    ((C z).norm_rankOneDivNormSq_map_le _).trans (hCG z hz)
  obtain ⟨g, hgp, hgs, hTg, hgeq, hTg1⟩ :=
    exists_cauchyTransform_eq_of_memLp hq hrR hDm hG hDG hsmall
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hΨc : Continuous Ψ := continuous_const.add hTg
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    simpa [hΨ] using isUnit_one_sub_of_norm_lt_one (x := -cauchyTransform g z)
      (by simpa using hTg1 z (ball_subset_closedBall hz))
  -- the weak derivative of `σ = ξ + (T g) ξ` on the open disc, by the Leibniz rule
  let U : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hUΩ : U ≤ Ω := hball
  obtain ⟨b, hb, hTgD⟩ :=
    exists_hasWeakFDerivOn_cauchyTransform_of_memLp hp1 ENNReal.coe_ne_top hgp hgs
  specialize hTgD U
  have hDT : MemLpLoc p U fun w ↦ wirtingerPartsCLM (b w) (g w) :=
    memLpLoc_iff.2 fun K _ _ ↦ (hb.wirtingerPartsCLM hgp).restrict K
  have : FiniteDimensional ℝ E := .complexToReal E
  let B : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hprod := hTgD.bilin_of_memLpLoc B hp (by exact_mod_cast hp1) le_rfl
    hTg.continuousOn.memLpLoc hDT (hDξ.mono hUΩ) (hξp.mono_set hball) (hDξp.mono_set hball)
  have hw := ((hDξ.mono hUΩ).add hprod).hasWeakConjWirtingerDerivOn
  have hw0 := hw.congr_ae_deriv (k := 0) <| by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hball hae,
      ae_restrict_mem U.isOpen.measurableSet] with z hz hzU
    have hgz := hgeq z (ball_subset_closedBall hzU)
    have hDz := (C z).rankOneDivNormSq_apply_map (𝕜 := ℂ) (ξ z)
    simp only [Pi.add_apply, add_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.precompR_apply, B, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars', Pi.zero_apply, ContinuousLinearMap.compL_apply,
      wirtingerPartsCLM_apply, hgz, smul_apply, one_smul, conj_I, map_one,
      ContinuousLinearMap.comp_apply, hDz, one_apply_eq_self]
    simp only [smul_apply, ContinuousLinearMap.id_apply] at hz
    have h1 : Dξ z 1 = -C z (ξ z) - I • Dξ z I := by
      rw [← sub_eq_zero, ← hz]
      abel
    rw [h1, map_sub, map_neg, map_smul]
    match_scalars <;> ring_nf <;> simp only [I_sq] <;> ring
  have hσ : (ξ + fun z ↦ B (cauchyTransform g z) (ξ z)) = fun z ↦ Ψ z (ξ z) := by
    ext1 z
    simp [B, hΨ]
  rw [hσ] at hw0
  -- `Ψ` is of class `W^{1,p}` on the disc, hence so is its pointwise inverse
  have hΨW : MemWkpLoc p (ball z₀ r) 1 Ψ :=
    (memWkpLoc_const 1).add (memWkpLoc_succ_iff_of_isOpen (Ω := U).2
      ⟨hTg.continuousOn.memLpLoc, _, hTgD, memWkpLoc_zero_iff.2 hDT⟩)
  refine ⟨r, hr, hball, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    fun z hz ↦ ?_, hΨW.ring_inverse hΨc.continuousOn hunit, fun z hz ↦ ?_,
    hw0.differentiableOn (hΨc.continuousOn.clm_apply (hξc.mono hball)), fun z hz ↦ ?_⟩
  · have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp hΨc.continuousAt).continuousWithinAt
  · exact (hunit z hz).ringInverse
  · beta_reduce
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ (hunit z hz), one_apply_eq_self]

/-! ### Finite-dimensional complex normed spaces -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {ξ : ℂ → V} {C : ℂ → V →L[ℝ] V} {z₀ : ℂ}

/-- **The similarity principle** (Carleman) for weak solutions with `Lᵖ` coefficients. Let
`2 < p < ∞`, let `C ∈ Lᵖ_loc(Ω)` be a field of real-linear endomorphisms of a finite-dimensional
complex normed space `V`, and let `ξ` be a `W^{1,p}_loc` weak solution of
`∂ₛξ + i ∂ₜξ + C ξ = 0` on the open set `Ω` (`TauCeti.IsWeakLinearCauchyRiemannOn p`). Then every
point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which `ξ = Φ σ`, with `Φ` a continuous family of
invertible complex-linear maps of class `W^{1,p}_loc` and `σ` holomorphic. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id (hp : 2 < p)
    (hp_top : p ≠ ∞) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  lift p to ℝ≥0 using hp_top
  -- transport the equation to a Euclidean space, whose inner product absorbs `C`
  let e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let A : V ≃L[ℝ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) := e.restrictScalars' ℝ
  have hξ' : IsWeakLinearCauchyRiemannOn p Ω
      (fun _ ↦ I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin (Module.finrank ℂ V))))
      (fun z ↦ A.arrowCongr A (C z)) (fun z ↦ A (ξ z)) := by
    convert hξ.continuousLinearEquiv_comp A using 1
    · ext z _ v
      simp [A]
    · ext z y
      simp [A]
  have hp' : (2 : ℝ≥0) < p := by exact_mod_cast hp
  have hC' : MemLpLoc p Ω (fun z ↦ A.arrowCongr A (C z)) :=
    by simpa only [ContinuousLinearEquiv.coe_coe] using
      hC.clm_comp (A.arrowCongr A).toContinuousLinearMap
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦ, hΦW, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_innerProductSpace hp' hC' hξ' hz₀
  -- conjugate the factor back to `V`
  let L : (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] _) →L[ℝ] V →L[ℂ] V :=
    (e.symm.arrowCongr e.symm).toContinuousLinearMap.restrictScalars ℝ
  have hL (Ψ : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] _) :
      L Ψ = e.symm.conjContinuousAlgEquiv Ψ := by
    ext v
    simp [L]
  refine ⟨r, hr, hrΩ, fun z ↦ L (Φ z), fun z ↦ e.symm (σ z),
    L.continuous.comp_continuousOn hΦ, hΦW.clm_comp L,
    fun z hz ↦ by simpa only [hL] using (hΦu z hz).map e.symm.conjContinuousAlgEquiv,
    ((e.symm : _ →L[ℂ] V).differentiable.comp_differentiableOn hσ).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  have h := congrArg e.symm (hξσ hz)
  simp only [A, ContinuousLinearEquiv.coe_restrictScalars', e.symm_apply_apply] at h
  simp [h, hL]

/-- Let `2 < p`, possibly `p = ∞`. A `W^{1,p}_loc` weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on
an open set `Ω` (`TauCeti.IsWeakLinearCauchyRiemannOn p`), with `C ∈ Lᵖ_loc(Ω)`, has a similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id (hp : 2 < p)
    (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  -- pass to the finite exponent `min p 3`, which is still greater than `2`
  have hq : min p 3 ≤ p := min_le_left _ _
  obtain ⟨r, hr, -, Φ, σ, hΦ, -, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id (lt_min hp (by norm_num))
      ((min_le_right _ _).trans_lt ENNReal.ofNat_lt_top).ne (hC.mono_exponent hq)
      (IsWeakCauchyRiemannOn.mono_exponent hξ hq) hz₀
  obtain ⟨u, hu⟩ := hΦu z₀ (mem_ball_self hr)
  -- restricting the scalars of the equivalence `Φ z₀` to `ℝ` keeps it invertible
  refine .of_eqOn_ball hr (Φ := fun z ↦ (Φ z).restrictScalars ℝ)
    ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℂ).continuous.comp_continuousOn hΦ)
    (hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩) hσ hξσ

/-- **Unique continuation** for weak solutions with `Lᵖ` coefficients. Let `2 < p`, possibly
`p = ∞`. On a connected open set `Ω`, a `W^{1,p}_loc` weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0`
(`TauCeti.IsWeakLinearCauchyRiemannOn p`), with `C ∈ Lᵖ_loc(Ω)`, that vanishes on a nonempty open
subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_eqOn_zero (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero Ω.isOpen hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hC hξ hz)
    hU hUne hUΩ h₀

/-- **Unique continuation from a zero of infinite order** for weak solutions with `Lᵖ`
coefficients. Let `2 < p`, possibly `p = ∞`. On a connected open set `Ω`, a `W^{1,p}_loc` weak
solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` (`TauCeti.IsWeakLinearCauchyRiemannOn p`), with
`C ∈ Lᵖ_loc(Ω)`, that vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_I_smul_id_of_forall_isBigO (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hC hξ hz)
    hz₀ h₀

/-- **Isolated zeros** of weak solutions with `Lᵖ` coefficients. Let `2 < p`, possibly `p = ∞`. On a
connected open set `Ω`, the zeros of a `W^{1,p}_loc` weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0`
(`TauCeti.IsWeakLinearCauchyRiemannOn p`), with `C ∈ Lᵖ_loc(Ω)`, that is not identically zero on
`Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_I_smul_id (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin (Ω : Set ℂ) := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt Ω.isOpen hΩc
    hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hC hξ hz)
    hne

/-- **Positive orders** of the zeros of weak solutions with `Lᵖ` coefficients. Let `2 < p`,
possibly `p = ∞`. On a connected open set `Ω`, let `ξ` be a `W^{1,p}_loc` weak solution of
`∂ₛξ + i ∂ₜξ + C ξ = 0` (`TauCeti.IsWeakLinearCauchyRiemannOn p`), with `C ∈ Lᵖ_loc(Ω)`, not
identically zero on `Ω`. At a zero `z₀ ∈ Ω`, every factorization `ξ = Φ σ` has `σ` of the same
finite positive analytic order `m`, and `‖ξ z‖` is comparable to `‖z - z₀‖ ^ m` near `z₀`. -/
theorem exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemannOn_I_smul_id (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  have := FiniteDimensional.completeSpace ℂ V
  exact exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt Ω.isOpen hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hC hξ hz)
    hne hz₀ hξ₀

end TauCeti
