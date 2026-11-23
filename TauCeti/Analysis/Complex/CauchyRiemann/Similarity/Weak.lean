/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Wirtinger.Beurling.Lp
import TauCeti.Analysis.Complex.Wirtinger.Weyl
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Data.ENNReal.Holder
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.RankOne
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The similarity principle for weak solutions with Sobolev coefficients

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open and `2 < p < ∞`. Let
`J ∈ W^{1,p}_loc(Ω; End_ℝ V)` be continuous with `J² = -1` on `Ω`, let `C ∈ Lᵖ_loc(Ω; End_ℝ V)`,
and let `ξ` be a weak solution of the linear Cauchy–Riemann equation

`∂ₛξ + J ∂ₜξ + C ξ = 0`

on `Ω` in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`: `ξ` is continuous on `Ω` with a weak
derivative in `Lᵖ_loc`, and the equation holds almost everywhere. The **similarity principle**
(Carleman; McDuff–Salamon, Theorem 2.3.5) says that near every point `z₀ ∈ Ω` the solution factors
as `ξ = Φ σ`, with `Φ` a continuous `W^{1,p}_loc` family of real-linear automorphisms of `V`
satisfying `J Φ = Φ i`, and `σ` holomorphic
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`). So `ξ` has a similarity
factorization at every point of `Ω`
(`TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn`) and inherits the zero
structure of a holomorphic map: unique continuation from a zero of infinite order
(`TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO`) or from a nonempty open
subset (`TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero`), and isolated zeros
(`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn`). These consequences
allow `p = ∞`, and the last three need only a finite-dimensional real normed space `V`, read in a
complex Euclidean model. This extends `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`,
for the constant structure `J = i`, to a variable `J`, and adds the `W^{1,p}_loc` regularity of
the factor `Φ`.

The proof has two steps.

* The standard frame of `TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame` turns the equation
  near `z₀` into one for the constant structure `i`, with a new coefficient that is still `Lᵖ_loc`
  (`TauCeti.isWeakLinearCauchyRiemannOn_iff_standardFrame`).
* For the structure `i`, as in the classical case, the real-linear term `C ξ` is absorbed into a
  complex-linear coefficient `D` with `D ξ = C ξ` that is `Lᵖ` with `C`, a rank-one map built in a
  Euclidean model of `V` (`MeasureTheory.MemLp.exists_memLp_clm_apply_eq`), and the Cauchy
  integral equation `Ψ = 1 + T (½ Ψ D)` is solved on a closed disc
  (`TauCeti.exists_eq_two_inv_smul_one_add_cauchyTransform_comp_of_memLp`). Since `D` is only
  `Lᵖ`, the disc is taken so small that the `Lᵖ` norm of `D` on it is small. The solution
  `Ψ = 1 + T g`, with `g = ½ Ψ D ∈ Lᵖ`, is continuous, invertible, and lies in `W^{1,p}_loc` with
  `bar∂Ψ = g` (`TauCeti.memWkpLoc_one_cauchyTransform_of_memLp_of_finiteDimensional`). The weak
  Leibniz rule for products of `W^{1,p}_loc` maps, `p > 2`, gives
  `bar∂(Ψ ξ) = Ψ (bar∂ξ + ½ D ξ) = Ψ (bar∂ξ + ½ C ξ) = 0` weakly, so `σ = Ψ ξ` is holomorphic
  by Weyl's lemma, and `ξ = Ψ⁻¹ σ`.

## Main results

* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`: the local factorization `ξ = Φ σ`.
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn`: the factorization in the
  form consumed by `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO`: unique continuation from a
  zero of infinite order.
* `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero`: unique continuation from a
  nonempty open subset.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn`: isolated zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-! ### The standard structure -/

section ComplexTarget

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Opens ℂ} {C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

omit [FiniteDimensional ℂ V] in
/-- The combination `∂ₛ + i ∂ₜ` of the weak derivative of `ξ + T ξ` vanishes where `ξ` solves
`∂ₛξ + i ∂ₜξ + C ξ = 0` and `T` has a weak derivative `DT` with `DT 1 + i DT i = 2 G`, for
`bar∂T = G = ½ (1 + T) D` with `D ξ = C ξ`. -/
private theorem add_I_smul_eq_zero {T G D : V →L[ℂ] V} {C : V →L[ℝ] V} {Dξ : ℂ →L[ℝ] V}
    {DT : ℂ →L[ℝ] V →L[ℂ] V} {x : V} (heq : Dξ 1 + I • Dξ I + C x = 0)
    (hT : DT 1 + I • DT I = (2 : ℂ) • G) (hG : G = (2 : ℂ)⁻¹ • (1 + T).comp D)
    (hD : D x = C x) :
    (Dξ 1 + (DT 1 x + T (Dξ 1))) + I • (Dξ I + (DT I x + T (Dξ I))) = 0 := by
  have hC : Dξ 1 = -C x - I • Dξ I := eq_sub_of_add_eq (eq_neg_of_add_eq_zero_left heq)
  have hTx : DT 1 x = (2 : ℂ) • G x - I • DT I x := by
    rw [← smul_apply, ← hT]
    simp
  rw [hTx, hG, hC]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply, one_apply_eq_self, hD,
    map_sub, map_neg, map_smul]
  module

/-- **The holomorphic factor.** Let `ξ` solve `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on an open set `U`,
`2 < p < ∞`, and let `g ∈ Lᵖ` be supported in a closed disc, with continuous Cauchy transform and
`g = ½ (1 + T g) D` on `U` for a field `D` with `D ξ = C ξ`. Then `(1 + T g) ξ` is holomorphic on
`U`: by the weak Leibniz rule, `bar∂ ((1 + T g) ξ) = bar∂ξ + g ξ + T g (bar∂ξ)`, which vanishes. -/
private theorem differentiableOn_one_add_cauchyTransform_apply {p : ℝ≥0} (hp : 2 < p)
    {U : Opens ℂ}
    (hξ : IsWeakLinearCauchyRiemannOn p U (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    {g D : ℂ → V →L[ℂ] V} (hgp : MemLp g p volume) {c : ℂ} {r : ℝ}
    (hgs : support g ⊆ closedBall c r) (hTg : Continuous (cauchyTransform g))
    (hgeq : ∀ z ∈ U, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z))
    (hD : ∀ z, D z (ξ z) = C z (ξ z)) :
    DifferentiableOn ℂ (fun z ↦ (1 + cauchyTransform g z) (ξ z)) U := by
  have := FiniteDimensional.completeSpace ℂ V
  have hp1 : 1 < p := one_lt_two.trans hp
  have hp1' : (1 : ℝ≥0∞) < p := by exact_mod_cast hp1
  obtain ⟨hξc, hξp, Dξ, hDξ, hDξp, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 hξ
  -- the weak derivative of `T g`, with `bar∂ (T g) = g`
  obtain ⟨DT, hDT, hDTp⟩ := (memWkpLoc_one_cauchyTransform_of_memLp_of_finiteDimensional hp1'
    ENNReal.coe_ne_top hgp hgs U).exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDTp
  have hbar := hDT.hasWeakConjWirtingerDerivOn.ae_eq
    (hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp (r := r.toNNReal) hp1'.le
      (hgp.restrict _) (hgs.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal r))) U)
  -- the weak Leibniz rule for `ξ + T g ξ`
  let B : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hleib := hDξ.add (hDT.bilin_of_memLpLoc B hp hp1 le_rfl hTg.continuousOn.memLpLoc hDTp
    hDξ hξp hDξp)
  have hσ : (ξ + fun z ↦ B (cauchyTransform g z) (ξ z)) =
      fun z ↦ (1 + cauchyTransform g z) (ξ z) := by
    ext1 z
    simp [B]
  rw [hσ] at hleib
  -- `(1 + T g) ξ` is weakly holomorphic on `U`, hence holomorphic
  have hzero : HasWeakConjWirtingerDerivOn volume U
      (fun z ↦ (1 + cauchyTransform g z) (ξ z)) 0 := by
    refine hleib.hasWeakConjWirtingerDerivOn.congr_ae_deriv ?_
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet, hae, hbar] with z hz hz' hz''
    have hT : DT z 1 + I • DT z I = (2 : ℂ) • g z := by
      rw [← hz'', smul_inv_smul₀ two_ne_zero]
    have h := add_I_smul_eq_zero (T := cauchyTransform g z) (by simpa using hz') hT
      (hgeq z hz) (hD z)
    simp [B]
    linear_combination (norm := module) (2⁻¹ : ℂ) • h
  exact hzero.differentiableOn ((continuous_const.add hTg).continuousOn.clm_apply hξc)

/-- **The similarity principle for the standard structure.** A weak solution of
`∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`, with `C ∈ Lᵖ_loc`, `2 < p < ∞`, is mapped to a holomorphic map
`σ = Ψ ξ` near every point of `Ω` by a continuous `W^{1,p}_loc` family `Ψ` of invertible
complex-linear maps. -/
private theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul {p : ℝ≥0} (hp : 2 < p)
    (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Ψ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Ψ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Ψ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Ψ z)) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn (fun z ↦ Ψ z (ξ z)) σ (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  have hp1' : (1 : ℝ≥0∞) < p := by exact_mod_cast one_lt_two.trans hp
  have : (p : ℝ≥0∞).HolderConjugate (p : ℝ≥0∞).conjExponent := .conjExponent hp1'.le
  have hq : (p : ℝ≥0∞).conjExponent < 2 :=
    ENNReal.HolderConjugate.lt_two (p := (p : ℝ≥0∞)) (by exact_mod_cast hp)
  -- a closed disc in `Ω`, and a complex-linear coefficient `D` with `D ξ = C ξ` on it
  obtain ⟨R, hR, hRΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hz₀)
  obtain ⟨D, hDp, hD⟩ :=
    (memLpLoc_iff.1 hC _ hRΩ (isCompact_closedBall _ _)).exists_memLp_clm_apply_eq
      ((hξ.continuousOn.mono hRΩ).aestronglyMeasurable measurableSet_closedBall)
  set K := Real.pi⁻¹ *
    (eLpNorm (truncatedCauchyKernel (R + R)) (p : ℝ≥0∞).conjExponent volume).toReal
  have hK : 0 ≤ K := by positivity
  -- a smaller disc on which `D` has `Lᵖ` norm at most `1 / (2 (K + 1))`
  have hDR : MemLp ((closedBall z₀ R).indicator D) p volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2 hDp
  obtain ⟨r, hDr, hr, hrR⟩ := ((((tendsto_eLpNorm_restrict_closedBall ENNReal.coe_ne_top hDR
    z₀).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < 2⁻¹ / (K + 1) by
      positivity)))).filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hR)).exists
  have hsub : closedBall z₀ r ⊆ closedBall z₀ R := closedBall_subset_closedBall hrR.le
  rw [eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_closedBall).2
    (ae_of_all _ fun z hz ↦ indicator_of_mem (hsub hz) D))] at hDr
  have hKD : K * (eLpNorm D p (volume.restrict (closedBall z₀ r))).toReal ≤ 2⁻¹ := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) hDr.le
    calc _ ≤ K * (2⁻¹ / (K + 1)) := by gcongr
      _ ≤ 2⁻¹ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have hball : ball z₀ r ⊆ Ω := ball_subset_closedBall.trans (hsub.trans hRΩ)
  -- the Cauchy integral equation on the smaller disc
  obtain ⟨g, hgp, hgs, hTg, hgeq, hTg1⟩ :=
    exists_eq_two_inv_smul_one_add_cauchyTransform_comp_of_memLp hq hK
      (fun f hf hfs w hw ↦ norm_cauchyTransform_le hq hf (hfs.trans hsub) (hsub hw))
      (hDp.mono_measure (Measure.restrict_mono hsub le_rfl)) hKD
  set Ψ : ℂ → V →L[ℂ] V := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    refine nonunits.subset_compl_ball h ?_
    rw [mem_ball_iff_norm, hΨ, add_sub_cancel_left]
    exact hTg1 z (ball_subset_closedBall hz)
  let Ω' : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  refine ⟨r, hr, hball, Ψ, fun z ↦ Ψ z (ξ z), (continuous_const.add hTg).continuousOn,
    (memWkpLoc_const (1 : V →L[ℂ] V)).add
      (memWkpLoc_one_cauchyTransform_of_memLp_of_finiteDimensional hp1' ENNReal.coe_ne_top hgp
        hgs _), hunit,
    differentiableOn_one_add_cauchyTransform_apply (U := Ω') hp (hξ.mono hball) hgp hgs hTg
      (fun z hz ↦ hgeq z (ball_subset_closedBall hz)) hD, fun _ _ ↦ rfl⟩

/-! ### A variable complex structure -/

/-- **The similarity principle** (Carleman) for weak solutions. Let `2 < p < ∞`, let
`J ∈ W^{1,p}_loc` be continuous on an open set `Ω` with `J² = -1` there, let `C ∈ Lᵖ_loc`, and let
`ξ` solve `∂ₛξ + J ∂ₜξ + C ξ = 0` weakly on `Ω`. Then every point `z₀ ∈ Ω` is the centre of a disc
in `Ω` on which `ξ = Φ σ`, with `Φ` a continuous `W^{1,p}_loc` family of invertible real-linear
maps satisfying `J Φ = Φ i`, and `σ` holomorphic. In particular `σ (z₀) = 0` exactly when
`ξ (z₀) = 0`. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞)
    {J : ℂ → V →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hJc : ContinuousOn J Ω)
    (hJ2 : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      (∀ z ∈ ball z₀ r, J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  lift p to ℝ≥0 using hp_top
  replace hp : 2 < p := by exact_mod_cast hp
  have hp1 : 1 < p := one_lt_two.trans hp
  -- the standard frame turns the equation into one for the structure `i` near `z₀`
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul (hJ2 z₀ hz₀)
  obtain ⟨r₁, hr₁, hr₁Ω, hu⟩ :=
    exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) Ω.isOpen hz₀ hJc (hJ2 z₀ hz₀)
  let Ω₁ : Opens ℂ := ⟨ball z₀ r₁, isOpen_ball⟩
  set Φs := standardFrame J z₀ Φ₁
  have hΦsc : ContinuousOn Φs Ω₁ := continuousOn_standardFrame (hJc.mono hr₁Ω)
  have hΦsW : MemWkpLoc p Ω₁ 1 Φs := (memWkpLoc_standardFrame hJ).mono hr₁Ω
  obtain ⟨DΦ, hDΦ, hDΦp⟩ := hΦsW.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΦp
  have hη := (isWeakLinearCauchyRiemannOn_iff_standardFrame hp (hJc.mono hr₁Ω)
    (fun z hz ↦ hJ2 z (hr₁Ω hz)) (hJ2 z₀ hz₀) hΦ₁ hu hDΦ hDΦp).1 (hξ.mono hr₁Ω)
  have hC' : MemLpLoc p Ω₁ (frameCoeff J C Φs DΦ) :=
    (memLpLoc_frameCoeff_iff isOpen_ball.measurableSet hΦsc hDΦp hu (hJc.mono hr₁Ω)).2
      (hC.mono_set hr₁Ω)
  -- the similarity principle for the structure `i`
  obtain ⟨r, hr, hrΩ₁, Ψ, σ, hΨc, hΨW, hΨu, hσ, hσeq⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul hp hC' hη (mem_ball_self hr₁)
  let Ω₂ : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hinvc : ContinuousOn (fun z ↦ Ring.inverse (Ψ z)) (ball z₀ r) := fun z hz ↦ by
    have h := NormedRing.inverse_continuousAt (hΨu z hz).unit
    rw [IsUnit.unit_spec] at h
    exact h.comp_continuousWithinAt (hΨc z hz)
  let R : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  refine ⟨r, hr, hrΩ₁.trans hr₁Ω, fun z ↦ Φs z ∘L R (Ring.inverse (Ψ z)), σ, ?_, ?_,
    fun z hz ↦ ?_, fun z hz ↦ ?_, hσ, fun z hz ↦ ?_⟩
  · exact (hΦsc.mono hrΩ₁).clm_comp (R.continuous.comp_continuousOn hinvc)
  · have hW : MemWkpLoc p Ω₂ 1 fun z ↦ R (Ring.inverse (Ψ z)) :=
      (hΨW.ring_inverse hΨc hΨu).clm_comp R
    exact (hΦsW.mono hrΩ₁ : MemWkpLoc p Ω₂ 1 Φs).bilin
      (ContinuousLinearMap.compL ℝ V V V) hp hp1 le_rfl hW
  · exact (hu z (hrΩ₁ hz)).mul (ContinuousLinearMap.isUnit_restrictScalars (hΨu z hz).ringInverse)
  · have h := comp_standardFrame (Φ₁ := Φ₁) (hJ2 z (hr₁Ω (hrΩ₁ hz))) (hJ2 z₀ hz₀) hΦ₁
    ext v
    have hv := congr($h (Ring.inverse (Ψ z) v))
    simpa [R, Φs] using hv
  · have h := congrArg (fun v ↦ Ring.inverse (Ψ z) v) (hσeq hz)
    simp only [ContinuousLinearMap.ringInverse_apply_apply (hΨu z hz)] at h
    simp only [ContinuousLinearMap.comp_apply, R, ContinuousLinearMap.coe_restrict_scalarsL',
      ContinuousLinearMap.coe_restrictScalars', ← h]
    exact (ContinuousLinearMap.apply_ringInverse_apply (hu z (hrΩ₁ hz)) (ξ z)).symm

/-- A weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on an open set `Ω`, with `2 < p ≤ ∞`,
`J ∈ W^{1,p}_loc` continuous with `J² = -1` on `Ω` and `C ∈ Lᵖ_loc`, has a similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn {p : ℝ≥0∞} (hp : 2 < p)
    {J : ℂ → V →L[ℝ] V} (hJ : MemWkpLoc p Ω 1 J) (hJc : ContinuousOn J Ω)
    (hJ2 : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  -- a finite exponent `min p 3 ∈ (2, p]`
  have hq : min p 3 ≤ p := min_le_left _ _
  obtain ⟨r, hr, -, Φ, σ, hΦ, -, hΦu, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn (lt_min hp (by norm_num))
      (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right p 3)) (hJ.mono_exponent hq) hJc hJ2
      (hC.mono_exponent hq) (hξ.mono_exponent hq) hz₀
  exact .of_eqOn_ball hr hΦ (hΦu z₀ (mem_ball_self hr)) hσ hξσ

end ComplexTarget

/-! ### Real targets -/

section RealTarget

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- A weak solution with values in a finite-dimensional real normed space, read in a complex
Euclidean model `e : V ≃ ℂⁿ`, has a similarity factorization at every point of `Ω`, provided
`Ω` is nonempty, `2 < p ≤ ∞`, `J ∈ W^{1,p}_loc` is continuous with `J² = -1` on `Ω` and
`C ∈ Lᵖ_loc`. -/
private theorem exists_continuousLinearEquiv_hasSimilarityFactorizationAt (hp : 2 < p)
    (hJ : MemWkpLoc p Ω 1 J) (hJc : ContinuousOn J Ω)
    (hJ2 : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hΩ : (Ω : Set ℂ).Nonempty) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℂ (Fin n)),
      ∀ z ∈ Ω, HasSimilarityFactorizationAt (fun w ↦ e (ξ w)) z := by
  obtain ⟨z₁, hz₁⟩ := hΩ
  obtain ⟨n, Φ, -⟩ :=
    (J z₁).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul (hJ2 z₁ hz₁)
  -- conjugation by `e = Φ⁻¹` carries the equation to `ℂⁿ`
  set e := Φ.symm
  let L : (V →L[ℝ] V) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    e.arrowCongr e
  have hL (A : V →L[ℝ] V) (v) : L A v = e (A (e.symm v)) := by simp [L]
  refine ⟨n, e, fun z hz ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp
    (J := fun w ↦ L (J w)) (C := fun w ↦ L (C w)) (hJ.clm_comp L)
    (L.continuous.comp_continuousOn hJc) (fun w hw ↦ ?_) (hC.clm_comp L) ?_ hz⟩
  · refine ContinuousLinearMap.ext fun v ↦ ?_
    have h := congr($(hJ2 w hw) (e.symm v))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      neg_apply] at h ⊢
    rw [hL, hL, e.symm_apply_apply, h, map_neg, e.apply_symm_apply]
  · convert hξ.continuousLinearEquiv_comp e using 3
    · exact ContinuousLinearMap.ext (hL _)
    · simp [hL]

/-- **Unique continuation** for weak solutions. On a connected open set `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` with values in a finite-dimensional real normed space, with
`2 < p ≤ ∞`, `J ∈ W^{1,p}_loc` continuous with `J² = -1` on `Ω` and `C ∈ Lᵖ_loc`, that vanishes
to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJ : MemWkpLoc p Ω 1 J)
    (hJc : ContinuousOn J Ω) (hJ2 : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  obtain ⟨n, e, he⟩ :=
    exists_continuousLinearEquiv_hasSimilarityFactorizationAt hp hJ hJc hJ2 hC hξ ⟨z₀, hz₀⟩
  have h := eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ he z hz) hz₀
    fun k ↦ (e.isBigO_comp ξ (𝓝 z₀)).trans (h₀ k)
  intro z hz
  simpa using h hz

/-- **Unique continuation** for weak solutions. On a connected open set `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` with values in a finite-dimensional real normed space, with
`2 < p ≤ ∞`, `J ∈ W^{1,p}_loc` continuous with `J² = -1` on `Ω` and `C ∈ Lᵖ_loc`, that vanishes
on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJ : MemWkpLoc p Ω 1 J)
    (hJc : ContinuousOn J Ω) (hJ2 : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨n, e, he⟩ :=
    exists_continuousLinearEquiv_hasSimilarityFactorizationAt hp hJ hJc hJ2 hC hξ (hUne.mono hUΩ)
  have h := eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero Ω.isOpen hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ he z hz) hU hUne hUΩ
    fun z hz ↦ by simp [h₀ hz]
  intro z hz
  simpa using h hz

/-- **Isolated zeros** of weak solutions. On a connected open set `Ω`, the zeros of a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` with values in a finite-dimensional real normed space, with
`2 < p ≤ ∞`, `J ∈ W^{1,p}_loc` continuous with `J² = -1` on `Ω` and `C ∈ Lᵖ_loc`, that is not
identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hJ : MemWkpLoc p Ω 1 J)
    (hJc : ContinuousOn J Ω) (hJ2 : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin (Ω : Set ℂ) := by
  obtain ⟨n, e, he⟩ := exists_continuousLinearEquiv_hasSimilarityFactorizationAt hp hJ hJc hJ2
    hC hξ (hne.imp fun _ h ↦ h.1)
  have h := setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt Ω.isOpen hΩc
    (e.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ he z hz) (by simpa using hne)
  simpa using h

end RealTarget

end TauCeti
