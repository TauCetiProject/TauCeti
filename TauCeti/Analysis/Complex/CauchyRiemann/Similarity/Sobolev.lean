/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundaryReflection
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The Sobolev vector similarity principle and unique continuation

Let `V` be a finite-dimensional complex normed space, let `2 < p < ∞`, and let `Ω ⊆ ℂ` be open.
For a continuous almost complex structure `J : ℂ → V →L[ℝ] V` in `W^{1,p}_loc(Ω)` satisfying
`J² = -1` on `Ω` and a real-linear coefficient field `C : ℂ → V →L[ℝ] V` in `Lᵖ_loc(Ω)`, this
file proves Carleman's vector similarity principle (McDuff–Salamon, Theorem 2.3.5) for weak
solutions `ξ` of the linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

on `Ω`, together with its interior and real-boundary unique continuation consequences.

## Proof outline

1. **Constant structure `J = i` on an inner product space.** Around any `z₀ ∈ Ω`, choose a closed
   disc `closedBall z₀ r₀ ⊆ Ω`. The complex-linear rank-one endomorphism field
   `D z = rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)` satisfies `D z (ξ z) = C z (ξ z)` and
   `‖D z‖ ≤ ‖C z‖`, hence belongs to `Lᵖ(closedBall z₀ r₀)`. Since `p > 2`, its Hölder conjugate
   `q` satisfies `q < 2`, so `‖K_{2r}‖_{L^q} → 0` as `r → 0`
   (`TauCeti.tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero`). On a sufficiently small subdisc
   `ball z₀ r`, `TauCeti.exists_cauchyTransform_eq_of_memLp` produces `g ∈ Lᵖ(ℂ)` supported in
   `closedBall z₀ r` with `Ψ = 1 + T g` continuous, `‖T g‖ < 1` on `closedBall z₀ r`, and
   `g = ½ Ψ D` there.
   Interior elliptic regularity (`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_one`) places `Ψ`
   in `W^{1,p}_loc`, the Banach-algebra inverse chain rule (`TauCeti.MemWkpLoc.ring_inverse`)
   places `Φ = Ψ⁻¹` in `W^{1,p}_loc`, and the weak Leibniz rule
   (`TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`) gives `\bar∂(Ψ ξ) = 0` weakly on `B(z₀, r)`, so
   `σ = Ψ ξ` is holomorphic by Weyl's lemma.
2. **General finite-dimensional spaces and variable `J`.** Linear equivalence with a Euclidean
   space gives the constant-`i` theorem on any finite-dimensional complex normed space `V`
   (`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id`). For a variable
   `J ∈ W^{1,p}_loc(Ω)`, `TauCeti.standardFrame` constructs an invertible `W^{1,p}_loc` frame `Θ`
   near `z₀` with `J Θ = Θ i` that reduces the equation for `ξ` to the constant-`i` equation for
   `η = Θ⁻¹ ξ` with `Lᵖ_loc` coefficient (`TauCeti.isWeakLinearCauchyRiemannOn_iff_standardFrame`,
   `TauCeti.memLpLoc_frameCoeff_iff`). Composing `Θ` with the complex-linear factor of `η` via
   `TauCeti.MemWkpLoc.bilin` yields `Φ = Θ Φ₀` in `W^{1,p}_loc` with `J Φ = Φ i` and `ξ = Φ σ`
   (`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`).
3. **Unique continuation and zero orders.** Every weak solution therefore satisfies
   `TauCeti.HasSimilarityFactorizationAt` at each point of `Ω`
   (`TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn`), unlocking unique
   continuation from open sets, neighbourhoods, and infinite-order zeros, discreteness of zeros,
   and finite positive vanishing orders.
4. **Real boundary condition on the upper half-plane (`J = i`).** Combining Schwarz reflection
   (`HasWeakConjWirtingerDerivRealBoundaryOn.isWeakLinearCauchyRiemannOn_starSchwarzReflection`)
   with the interior results yields half-disc similarity factorizations, boundary unique
   continuation from infinite-order vanishing within `{0 ≤ im}`, and isolation of boundary zeros.

## Main declarations

* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id`: the Sobolev similarity
  principle for the standard complex structure `i`, producing complex-linear equivalences
  `Φ : ℂ → V ≃L[ℂ] V` in `W^{1,p}_loc`.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`: Carleman's vector similarity
  principle for a variable `W^{1,p}_loc` complex structure `J`, producing real-linear equivalences
  `Φ : ℂ → V ≃L[ℝ] V` in `W^{1,p}_loc` with `J z ∘L Φ z = Φ z ∘L (i • id)`.
* `TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eventually_eq_zero`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero`,
  `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO`,
  `TauCeti.eventually_ne_zero_of_isWeakLinearCauchyRiemannOn`,
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn`,
  `TauCeti.exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemannOn`: interior unique continuation,
  isolated zeros, and positive integer zero orders for variable `J`.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_similarity`,
  `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_forall_isBigO`,
  `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_eventually_eq_zero`,
  `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eventually_ne_zero`: boundary similarity and
  unique continuation up to the real axis.
* `TauCeti.not_exists_eventually_id_eq_apply_of_I_smul_eq_neg` and
  `TauCeti.exists_contDiff_not_hasWeakConjWirtingerDerivRealBoundaryOn`: calibration checks
  ruling out the opposite intertwining sign `J Φ = -Φ i` and flat boundary solutions with `Lᵖ_loc`
  coefficients.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Section 2.3 (Theorem 2.3.5) and Appendix B.4.
-/

public noncomputable section

open Asymptotics Complex ContinuousLinearMap Filter Function MeasureTheory Metric Set
  TopologicalSpace Topology
open scoped ComplexConjugate ENNReal NNReal

namespace TauCeti

/-! ### Auxiliary lemmas -/

/-- The Hölder conjugate of an exponent `p > 2` is strictly less than `2`. -/
private theorem conjExponent_lt_two {p : ℝ≥0∞} (hp : 2 < p) : p.conjExponent < 2 := by
  have : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp.le⟩
  refine ENNReal.inv_lt_inv.1 (lt_of_not_ge fun hle ↦ (lt_self_iff_false (1 : ℝ≥0∞)).1 ?_)
  calc (1 : ℝ≥0∞) = p⁻¹ + p.conjExponent⁻¹ :=
        (ENNReal.HolderConjugate.inv_add_inv_eq_one p _).symm
    _ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_of_lt_of_le
        (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero _ p)) (ENNReal.inv_lt_inv.2 hp) hle
    _ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one 2 2

/-- Package a family of continuous linear endomorphisms that are units on `U` into continuous
linear equivalences agreeing with the original family on `U`. -/
private def equivOfIsUnit {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M]
    [Module R M] {U : Set ℂ} {A : ℂ → M →L[R] M} (h : ∀ z ∈ U, IsUnit (A z)) (z : ℂ) :
    M ≃L[R] M := by
  classical
  exact if hz : z ∈ U then ContinuousLinearEquiv.unitsEquiv R M (h z hz).unit
    else ContinuousLinearEquiv.refl R M

private theorem coe_equivOfIsUnit {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] {U : Set ℂ} {A : ℂ → M →L[R] M}
    (h : ∀ z ∈ U, IsUnit (A z)) {z : ℂ} (hz : z ∈ U) :
    (equivOfIsUnit h z : M →L[R] M) = A z := by
  rw [equivOfIsUnit, dite_eq_left_of_eq_true (eq_true hz)]
  ext x
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply, IsUnit.unit_spec]

/-- Shrinking the radius makes `2⁻¹ * π⁻¹ * ‖K_{2r}‖_{L^q} * ‖D‖_{Lᵖ(closedBall c r)} ≤ 1/4` when
`p > 2` and `D ∈ Lᵖ(closedBall c r₀)`, so the Cauchy integral equation is solvable on a subdisc. -/
private theorem exists_radius_cauchyTransform_eq_of_memLp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {p : ℝ≥0∞} (hp : 2 < p)
    {D : ℂ → E →L[ℂ] E} {c : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hD : MemLp D p (volume.restrict (closedBall c r₀))) :
    ∃ r, 0 < r ∧ r ≤ r₀ ∧ ∃ g : ℂ → E →L[ℂ] E,
      support g ⊆ closedBall c r ∧ MemLp g p volume ∧ Integrable g ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp.le⟩
  set q := p.conjExponent
  have hq : q < 2 := conjExponent_lt_two hp
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  have hlim : Tendsto (fun r : ℝ ↦ 2⁻¹ * Real.pi⁻¹ *
      (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall c r₀))).toReal) (𝓝 0) (𝓝 0) := by
    have hK := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((tendsto_eLpNorm_truncatedCauchyKernel_nhds_zero hq0 hq).comp
        ((continuous_id.add continuous_id).tendsto' 0 0 (add_zero 0)))
    simpa using (hK.const_mul (2⁻¹ * Real.pi⁻¹)).mul_const _
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀ ∧ 2⁻¹ * Real.pi⁻¹ *
      (eLpNorm (truncatedCauchyKernel (r + r)) q volume).toReal *
      (eLpNorm D p (volume.restrict (closedBall c r₀))).toReal ≤ 4⁻¹ :=
    Filter.inter_mem (Ioo_mem_nhdsGT hr₀)
      (nhdsWithin_le_nhds (hlim.eventually (Iic_mem_nhds (by positivity))))
  obtain ⟨r, ⟨hr, hrr₀⟩, hsmall₀⟩ := hev.exists
  have hDr : MemLp D p (volume.restrict (closedBall c r)) :=
    hD.mono_measure (Measure.restrict_mono (closedBall_subset_closedBall hrr₀.le) le_rfl)
  have hDmono : (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤
      (eLpNorm D p (volume.restrict (closedBall c r₀))).toReal :=
    ENNReal.toReal_mono hD.eLpNorm_ne_top
      (eLpNorm_mono_measure D (Measure.restrict_mono (closedBall_subset_closedBall hrr₀.le) le_rfl))
  refine ⟨r, hr, hrr₀.le, exists_cauchyTransform_eq_of_memLp (q := q) hq hDr ?_⟩
  exact (mul_le_mul_of_nonneg_left hDmono (by positivity)).trans hsmall₀

/-- Pointwise cancellation in the weak Leibniz formula for `\bar∂(Ψ ξ)` when `Ψ` is complex-linear
with `\bar∂Ψ = ½ Ψ D`, `D ξ = C ξ`, and `∂ₛξ + i ∂ₜξ + C ξ = 0`. -/
private theorem conjWirtingerDeriv_bilin_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ψ D : E →L[ℂ] E} {C : E →L[ℝ] E} {DΨ : ℂ →L[ℝ] E →L[ℂ] E}
    {Dξ : ℂ →L[ℝ] E} {ξ : E}
    (hΨbar : (2 : ℂ)⁻¹ • (DΨ 1 + I • DΨ I) = (2 : ℂ)⁻¹ • Ψ.comp D)
    (hD : D ξ = C ξ) (hξ : Dξ 1 + (I • ContinuousLinearMap.id ℝ E) (Dξ I) + C ξ = 0) :
    (2 : ℂ)⁻¹ •
      (((restrictScalarsL ℂ E E ℝ ℝ).precompL ℂ DΨ ξ +
          (restrictScalarsL ℂ E E ℝ ℝ).precompR ℂ Ψ Dξ) 1 +
        I • ((restrictScalarsL ℂ E E ℝ ℝ).precompL ℂ DΨ ξ +
          (restrictScalarsL ℂ E E ℝ ℝ).precompR ℂ Ψ Dξ) I) = 0 := by
  have hΨξ : (2 : ℂ)⁻¹ • (DΨ 1 ξ + I • DΨ I ξ) = (2 : ℂ)⁻¹ • Ψ (C ξ) := by
    have h := congr($hΨbar ξ)
    simpa only [smul_apply, add_apply, ContinuousLinearMap.comp_apply, hD] using h
  have hC : C ξ = -(Dξ 1 + I • Dξ I) := eq_neg_of_add_eq_zero_right (by simpa using hξ)
  change (2 : ℂ)⁻¹ • ((DΨ 1 ξ + Ψ (Dξ 1)) + I • (DΨ I ξ + Ψ (Dξ I))) = 0
  calc (2 : ℂ)⁻¹ • ((DΨ 1 ξ + Ψ (Dξ 1)) + I • (DΨ I ξ + Ψ (Dξ I)))
      = (2 : ℂ)⁻¹ • (DΨ 1 ξ + I • DΨ I ξ) + (2 : ℂ)⁻¹ • Ψ (Dξ 1 + I • Dξ I) := by
        simp only [map_add, map_smul, smul_add]; abel
    _ = (2 : ℂ)⁻¹ • Ψ (C ξ) + (2 : ℂ)⁻¹ • Ψ (Dξ 1 + I • Dξ I) := by rw [hΨξ]
    _ = 0 := by rw [hC, map_neg, smul_neg, neg_add_cancel]

/-- Given `Ψ : ℂ → E →L[ℂ] E` continuous and in `W^{1,p}_loc` on an open set `B` with
`\bar∂Ψ = g`, `g = ½ Ψ D` on `B`, `D z (ξ z) = C z (ξ z)`, and `ξ` a weak solution on `B`, the
product `z ↦ Ψ z (ξ z)` is complex differentiable on `B`. -/
private theorem differentiableOn_apply_of_isWeakLinearCauchyRiemannOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) {B : Opens ℂ} {Ψ g D : ℂ → E →L[ℂ] E} {C : ℂ → E →L[ℝ] E}
    {ξ : ℂ → E} (hΨc : ContinuousOn Ψ B) (hΨW : MemWkpLoc p B 1 Ψ)
    (hΨbar : HasWeakConjWirtingerDerivOn volume B Ψ g)
    (hgeq : ∀ z ∈ (B : Set ℂ), g z = (2 : ℂ)⁻¹ • (Ψ z).comp (D z))
    (hDξ_eq : ∀ z, D z (ξ z) = C z (ξ z))
    (hξB : IsWeakLinearCauchyRiemannOn p B (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ) :
    DifferentiableOn ℂ (fun z ↦ Ψ z (ξ z)) B := by
  have := FiniteDimensional.completeSpace ℂ E
  set p₀ : ℝ≥0 := p.toNNReal
  have hp_coe : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀ : 2 < p₀ := by exact_mod_cast hp_coe.symm ▸ hp
  have hp₀1 : 1 < p₀ := one_lt_two.trans hp₀
  obtain ⟨DΨ, hDΨ, hDΨp⟩ := (hp_coe ▸ hΨW : MemWkpLoc p₀ B 1 Ψ).exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΨp
  obtain ⟨hξBc, hξBp, Dξ, hDξ, hDξp, hξae⟩ :=
    isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 (hp_coe ▸ hξB)
  let L := restrictScalarsL ℂ E E ℝ ℝ
  have hDσ := hDΨ.bilin_of_memLpLoc L hp₀ hp₀1 le_rfl hΨc.memLpLoc hDΨp hDξ hξBp hDξp
  have hw0 : HasWeakConjWirtingerDerivOn volume B (fun z ↦ Ψ z (ξ z)) 0 := by
    refine hDσ.hasWeakConjWirtingerDerivOn.congr_ae_deriv ?_
    filter_upwards [ae_restrict_mem B.isOpen.measurableSet,
      hDΨ.hasWeakConjWirtingerDerivOn.ae_eq hΨbar, hξae] with z hz hΨz hξz
    rw [hgeq z hz] at hΨz
    exact conjWirtingerDeriv_bilin_eq_zero hΨz (hDξ_eq z) hξz
  exact hw0.differentiableOn (hΨc.clm_apply hξBc)

/-! ### The Sobolev similarity principle for the standard complex structure -/

/-- **The Sobolev similarity principle** on a finite-dimensional complex inner product space, for
`J = i`. -/
private theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_of_innerProductSpace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω) {C : ℂ → E →L[ℝ] E} {ξ : ℂ → E}
    (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E ≃L[ℂ] E) (σ : ℂ → E),
      ContinuousOn (fun z ↦ (Φ z : E →L[ℂ] E)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : E →L[ℂ] E)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hz₀)
  set D : ℂ → E →L[ℂ] E := fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)
  have hDr₀ : MemLp D p (volume.restrict (closedBall z₀ r₀)) :=
    (memLpLoc_iff.1 hC _ hr₀Ω (isCompact_closedBall z₀ r₀)).rankOneDivNormSq_apply (𝕜 := ℂ)
      ((hξ.continuousOn.mono hr₀Ω).aestronglyMeasurable measurableSet_closedBall)
  obtain ⟨r, hr, hrr₀, g, -, hgLp, hgi, hTg, hgeq, hTg1⟩ :=
    exists_radius_cauchyTransform_eq_of_memLp hp hr₀ hDr₀
  have hball : ball z₀ r ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hrr₀).trans hr₀Ω)
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  set Ψ : ℂ → E →L[ℂ] E := (fun _ ↦ 1) + cauchyTransform g with hΨ
  have hΨc : Continuous Ψ := continuous_const.add hTg
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    exact nonunits.subset_compl_ball h
      (by simpa [mem_ball_iff_norm, hΨ] using hTg1 z (ball_subset_closedBall hz))
  have hu_inv (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ring.inverse (Ψ z)) := by
    rw [← (hunit z hz).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  have hΨbar : HasWeakConjWirtingerDerivOn volume B Ψ g := by
    simpa only [zero_add] using ((differentiableOn_const (1 : E →L[ℂ] E)
      ).hasWeakConjWirtingerDerivOn_zero (μ := volume) (Ω := B)).add
      (hasWeakConjWirtingerDerivOn_cauchyTransform hgi B)
  have hΨW : MemWkpLoc p B 1 Ψ := hΨbar.memWkpLoc_one ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp)
    hp_top hΨc.continuousOn.memLpLoc (memLpLoc_iff.2 fun K _ _ ↦ hgLp.restrict K)
  have hinv_c : ContinuousOn (fun z ↦ Ring.inverse (Ψ z)) (ball z₀ r) := fun z hz ↦ by
    have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp hΨc.continuousAt).continuousWithinAt
  let Φ := equivOfIsUnit hu_inv
  have hΦ_eq : EqOn (fun z ↦ (Φ z : E →L[ℂ] E)) (fun z ↦ Ring.inverse (Ψ z)) (ball z₀ r) :=
    fun _ hz ↦ coe_equivOfIsUnit hu_inv hz
  refine ⟨r, hr, hball, Φ, fun z ↦ Ψ z (ξ z), hinv_c.congr hΦ_eq,
    (hΨW.ring_inverse hΨc.continuousOn hunit).congr hΦ_eq,
    differentiableOn_apply_of_isWeakLinearCauchyRiemannOn hp hp_top hΨc.continuousOn hΨW hΨbar
      (fun z hz ↦ hgeq z (ball_subset_closedBall hz))
      (fun z ↦ (C z).rankOneDivNormSq_apply_map (ξ z)) (hξ.mono hball),
    fun z hz ↦ ?_⟩
  have hmul : Ring.inverse (Ψ z) (Ψ z (ξ z)) = ξ z := by
    simpa using congr($(Ring.inverse_mul_cancel _ (hunit z hz)) (ξ z))
  simpa [← ContinuousLinearEquiv.coe_coe, hΦ_eq hz] using hmul.symm

section StandardStructure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- **The Sobolev similarity principle for `J = i`.** Let `V` be a finite-dimensional complex
normed space, let `2 < p < ∞`, let `Ω ⊆ ℂ` be open, and let `C ∈ Lᵖ_loc(Ω)` be a field of
real-linear endomorphisms of `V`. Every weak solution `ξ` of `∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`
factors on a disc `ball z₀ r ⊆ Ω` around each `z₀ ∈ Ω` as `ξ = Φ σ`, where `Φ : ℂ → V ≃L[ℂ] V` is
continuous and of class `W^{1,p}_loc` on the disc and `σ : ℂ → V` is holomorphic on the disc. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V ≃L[ℂ] V) (σ : ℂ → V),
      ContinuousOn (fun z ↦ (Φ z : V →L[ℂ] V)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : V →L[ℂ] V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let e : V ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V ≃L[ℝ] E := e.restrictScalars' ℝ
  let C' : ℂ → E →L[ℝ] E := fun z ↦ eR.arrowCongr eR (C z)
  have hC' : MemLpLoc p Ω C' := hC.clm_comp (eR.arrowCongr eR).toContinuousLinearMap
  have hξ' : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C'
      (fun z ↦ e (ξ z)) := by
    convert hξ.continuousLinearEquiv_comp eR using 2 with z y
    · ext
      simp [eR]
    · simp [C', eR]
    · simp [eR]
  obtain ⟨r, hr, hrΩ, Φ₀, σ₀, hΦ₀c, hΦ₀W, hσ₀, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_of_innerProductSpace hp hp_top hΩ hC' hξ' hz₀
  let conjL : (E →L[ℂ] E) →L[ℝ] V →L[ℂ] V :=
    (e.symm.arrowCongr e.symm).toContinuousLinearMap.restrictScalars ℝ
  let Φ : ℂ → V ≃L[ℂ] V := fun z ↦ (e.trans (Φ₀ z)).trans e.symm
  have hΦ_eq (z : ℂ) : (Φ z : V →L[ℂ] V) = conjL (Φ₀ z : E →L[ℂ] E) := by
    ext v
    simp [Φ, conjL]
  refine ⟨r, hr, hrΩ, Φ, fun z ↦ e.symm (σ₀ z),
    (conjL.continuous.comp_continuousOn hΦ₀c).congr (fun z _ ↦ hΦ_eq z), ?_,
    ((e.symm : E →L[ℂ] V).differentiable.comp_differentiableOn hσ₀).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  · simpa only [hΦ_eq] using hΦ₀W.clm_comp conjL
  · have h := congrArg e.symm (hξσ hz)
    simpa [Φ] using h

/-- A weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on an open set `Ω` with `C ∈ Lᵖ_loc(Ω)` and
`2 < p < ∞` has a similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hp_top hΩ hC hξ hz₀
  exact .of_eqOn_ball hr (Φ := fun z ↦ ((Φ z).restrictScalars ℝ : V →L[ℝ] V))
    ((restrictScalarsL ℂ V V ℝ ℝ).continuous.comp_continuousOn hΦc)
    ((Φ z₀).restrictScalars ℝ).toUnit.isUnit hσ hξσ

end StandardStructure

/-! ### The vector similarity principle and unique continuation for variable `J` -/

section VariableStructure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- Local reduction around `z₀ ∈ Ω` from a variable `W^{1,p}_loc` structure `J` to `i` via
`TauCeti.standardFrame`. -/
private theorem exists_standardFrame_reduction (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    ∃ (Φ₁ : V ≃L[ℝ] V) (r₁ : ℝ) (C' : ℂ → V →L[ℝ] V),
      J z₀ ∘L (Φ₁ : V →L[ℝ] V) = (Φ₁ : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V) ∧
      0 < r₁ ∧ ball z₀ r₁ ⊆ Ω ∧ (∀ z ∈ ball z₀ r₁, IsUnit (standardFrame J z₀ Φ₁ z)) ∧
      MemLpLoc p (ball z₀ r₁) C' ∧
      IsWeakLinearCauchyRiemannOn p (ball z₀ r₁) (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C'
        (fun z ↦ Ring.inverse (standardFrame J z₀ Φ₁ z) (ξ z)) := by
  have := FiniteDimensional.completeSpace ℂ V
  set p₀ : ℝ≥0 := p.toNNReal
  have hp_coe : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀ : 2 < p₀ := by exact_mod_cast hp_coe.symm ▸ hp
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul (hJsq z₀ hz₀)
  obtain ⟨r₁, hr₁, hr₁Ω, hu₁⟩ := exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) hΩ hz₀ hJc
    (hJsq z₀ hz₀)
  let B₁ : Opens ℂ := ⟨ball z₀ r₁, isOpen_ball⟩
  obtain ⟨DΘ, hDΘ, hDΘp⟩ :=
    (memWkpLoc_standardFrame (Φ₁ := Φ₁) (z₀ := z₀) (hp_coe ▸ hJ.mono hr₁Ω) :
      MemWkpLoc p₀ B₁ 1 _).exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDΘp
  refine ⟨Φ₁, r₁, frameCoeff J C (standardFrame J z₀ Φ₁) DΘ, hΦ₁, hr₁, hr₁Ω, hu₁,
    (memLpLoc_frameCoeff_iff (C := C) isOpen_ball.measurableSet
      (continuousOn_standardFrame (hJc.mono hr₁Ω)) (hp_coe ▸ hDΘp) hu₁ (hJc.mono hr₁Ω)).2
      (hC.mono_set hr₁Ω),
    hp_coe ▸ (isWeakLinearCauchyRiemannOn_iff_standardFrame (Ω := B₁) hp₀ (hJc.mono hr₁Ω)
      (fun z hz ↦ hJsq z (hr₁Ω hz)) (hJsq z₀ hz₀) hΦ₁ hu₁ hDΘ hDΘp).1 (hp_coe ▸ hξ.mono hr₁Ω)⟩

/-- **The vector similarity principle** (Carleman; McDuff–Salamon, Theorem 2.3.5). Let `V` be a
finite-dimensional complex normed space, let `2 < p < ∞`, and let `Ω ⊆ ℂ` be open. Suppose
`J : ℂ → V →L[ℝ] V` is continuous and of class `W^{1,p}_loc` on `Ω` with `J(z)² = -1` on `Ω`,
`C ∈ Lᵖ_loc(Ω)`, and `ξ` solves `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` weakly on `Ω`. Around every point
`z₀ ∈ Ω` there exist a disc `ball z₀ r ⊆ Ω`, a family `Φ : ℂ → V ≃L[ℝ] V` of real-linear
automorphisms continuous and of class `W^{1,p}_loc` on `ball z₀ r` satisfying the intertwining
identity `J z ∘L Φ z = Φ z ∘L (i • id)` on `ball z₀ r`, and a holomorphic map `σ : ℂ → V` on
`ball z₀ r` such that `ξ z = Φ z (σ z)` for all `z ∈ ball z₀ r`. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V ≃L[ℝ] V) (σ : ℂ → V),
      ContinuousOn (fun z ↦ (Φ z : V →L[ℝ] V)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : V →L[ℝ] V)) ∧
      (∀ z ∈ ball z₀ r,
        J z ∘L (Φ z : V →L[ℝ] V) = (Φ z : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  set p₀ : ℝ≥0 := p.toNNReal
  have hp_coe : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀ : 2 < p₀ := by exact_mod_cast hp_coe.symm ▸ hp
  obtain ⟨Φ₁, r₁, C', hΦ₁, hr₁, hr₁Ω, hu₁, hC', hη⟩ :=
    exists_standardFrame_reduction hp hp_top hΩ hJc hJ hJsq hC hξ hz₀
  obtain ⟨r, hr, hrB₁, Φ₀, σ, hΦ₀c, hΦ₀W, hσ, hησ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hp_top isOpen_ball hC' hη
      (mem_ball_self hr₁)
  have hrΩ : ball z₀ r ⊆ Ω := hrB₁.trans hr₁Ω
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  let Θ := equivOfIsUnit (U := ball z₀ r) fun z hz ↦ hu₁ z (hrB₁ hz)
  let Φ : ℂ → V ≃L[ℝ] V := fun z ↦ ((Φ₀ z).restrictScalars ℝ).trans (Θ z)
  have hΦ_eq {z : ℂ} (hz : z ∈ ball z₀ r) : (Φ z : V →L[ℝ] V) =
      standardFrame J z₀ Φ₁ z ∘L ((Φ₀ z : V →L[ℂ] V).restrictScalars ℝ) := by
    ext v
    simpa [Φ] using congr($(coe_equivOfIsUnit (fun w hw ↦ hu₁ w (hrB₁ hw)) hz) (Φ₀ z v))
  have hΘW : MemWkpLoc p₀ B 1 (standardFrame J z₀ Φ₁) :=
    memWkpLoc_standardFrame (hp_coe ▸ hJ.mono hrΩ)
  have hΦ₀WR : MemWkpLoc p₀ B 1 (fun z ↦ ((Φ₀ z : V →L[ℂ] V).restrictScalars ℝ)) :=
    (hp_coe ▸ hΦ₀W : MemWkpLoc p₀ B 1 _).clm_comp (restrictScalarsL ℂ V V ℝ ℝ)
  have hcompW : MemWkpLoc p (ball z₀ r) 1
      (fun z ↦ standardFrame J z₀ Φ₁ z ∘L ((Φ₀ z : V →L[ℂ] V).restrictScalars ℝ)) :=
    hp_coe ▸ hΘW.bilin (compL ℝ V V V) hp₀ (one_lt_two.trans hp₀) le_rfl hΦ₀WR
  refine ⟨r, hr, hrΩ, Φ, σ,
    ((continuousOn_standardFrame (hJc.mono hrΩ)).clm_comp
      ((restrictScalarsL ℂ V V ℝ ℝ).continuous.comp_continuousOn hΦ₀c)).congr (fun _ hz ↦ hΦ_eq hz),
    hcompW.congr (fun _ hz ↦ hΦ_eq hz), fun z hz ↦ ?_, hσ, fun z hz ↦ ?_⟩
  · rw [hΦ_eq hz]
    ext v
    have hJΘ := congr($(comp_standardFrame (hJsq z (hrΩ hz)) (hJsq z₀ hz₀) hΦ₁) (Φ₀ z v))
    simpa [ContinuousLinearMap.comp_apply] using hJΘ
  · change ξ z = (Φ z : V →L[ℝ] V) (σ z)
    have hηz : Ring.inverse (standardFrame J z₀ Φ₁ z) (ξ z) = Φ₀ z (σ z) := hησ hz
    rw [hΦ_eq hz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, ← hηz]
    exact (congr($(Ring.mul_inverse_cancel _ (hu₁ z (hrB₁ hz))) (ξ z))).symm

/-- A weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on an open set `Ω`, with `2 < p < ∞`, `J`
continuous and in `W^{1,p}_loc(Ω)` satisfying `J² = -1`, and `C ∈ Lᵖ_loc(Ω)`, admits a similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ hJsq hC hξ hz₀
  exact .of_eqOn_ball hr hΦc (Φ z₀).toUnit.isUnit hσ hξσ

/-- **Unique continuation from a neighbourhood.** On a preconnected open set `Ω`, a weak solution
of `∂ₛξ + J ∂ₜξ + C ξ = 0` vanishing near one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eventually_eq_zero (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω)
    (hJ : MemWkpLoc p Ω 1 J) (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, ξ z = 0) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ
      hJsq hC hξ hz) hz₀ h₀

/-- **Unique continuation from an open subset.** On a preconnected open set `Ω`, a weak solution
of `∂ₛξ + J ∂ₜξ + C ξ = 0` vanishing on a nonempty open subset `U ⊆ Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ
      hJsq hC hξ hz) hU hUne hUΩ h₀

/-- **Unique continuation from an infinite-order zero.** On a preconnected open set `Ω`, a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` satisfying `ξ = O((z - z₀)ⁿ)` near `z₀ ∈ Ω` for every `n : ℕ`
vanishes on `Ω`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ
      hJsq hC hξ hz) hz₀ h₀

/-- **Isolated zeros.** On a preconnected open set `Ω`, a weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`
not identically zero on `Ω` has no zeros in a punctured neighbourhood of any point of `Ω`. -/
theorem eventually_ne_zero_of_isWeakLinearCauchyRiemannOn (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω) :
    ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ
      hJsq hC hξ hz) hne hz₀

/-- **Discrete zero set.** On a preconnected open set `Ω`, the zeros of a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω)
    (hJ : MemWkpLoc p Ω 1 J) (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hC : MemLpLoc p Ω C) (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ
      hJsq hC hξ hz) hne

/-- **Positive integer zero orders.** On a preconnected open set `Ω`, at every zero `z₀ ∈ Ω` of a
nontrivial weak solution `ξ` of `∂ₛξ + J ∂ₜξ + C ξ = 0`, all local similarity factorizations
`ξ = Φ σ` assign the same positive integer analytic order `m` to `σ`, characterized by
`‖ξ z‖ ≍ ‖z - z₀‖ ^ m` near `z₀`. -/
theorem exists_analyticOrderAt_eq_of_isWeakLinearCauchyRiemannOn (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω)
    (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  have := FiniteDimensional.completeSpace ℂ V
  exact exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hJc hJ
      hJsq hC hξ hz) hne hz₀ hξ₀

end VariableStructure

/-! ### Real-boundary similarity principle and boundary unique continuation -/

section RealBoundary

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [ContinuousStar F] [FiniteDimensional ℂ F]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {C : ℂ → F →L[ℝ] F} {ξ : ℂ → F} {z₀ : ℂ}

/-- **Boundary similarity principle** for `J = i` and the real boundary condition `star ∘ ξ = ξ`
along `Ω ∩ ℝ`. Around every point `z₀ ∈ Ω ∩ {0 ≤ im}` — including real boundary points — a
continuous weak solution with `C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `2 < p < ∞`, factors on a half-disc
`ball z₀ r ∩ {0 ≤ im}` as `ξ = Φ σ`, where `Φ : ℂ → F ≃L[ℂ] F` is continuous and in `W^{1,p}_loc`
on the full disc `ball z₀ r` and `σ : ℂ → F` is holomorphic on `ball z₀ r`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.exists_similarity (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → F ≃L[ℂ] F) (σ : ℂ → F),
      ContinuousOn (fun z ↦ (Φ z : F →L[ℂ] F)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : F →L[ℂ] F)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn (starSchwarzReflection ξ) (fun z ↦ Φ z (σ z)) (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r ∩ {z | 0 ≤ z.im}) := by
  have h1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hrefl := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection h1 hp_top hΩ hC hξc hξr
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦW, hσ, heq⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hp_top Ω.isOpen
      (hC.starSchwarzReflectionCoeff hΩ) hrefl hz₀.1
  refine ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦW, hσ, heq, fun z hz ↦ ?_⟩
  exact (starSchwarzReflection_of_im_nonneg (ξ := ξ) hz.2).symm.trans (heq hz.1)

/-- The Schwarz reflection of a real-boundary weak solution admits a similarity factorization at
every point of the conjugation-invariant domain `Ω`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.hasSimilarityFactorizationAt_starSchwarzReflection
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt (starSchwarzReflection ξ) z₀ :=
  hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn_I_smul_id hp hp_top Ω.isOpen
    (hC.starSchwarzReflectionCoeff hΩ)
    (h.isWeakLinearCauchyRiemannOn_starSchwarzReflection
      ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp) hp_top hΩ hC hξc hξr)
    hz₀

/-- **Boundary unique continuation from an infinite-order zero.** On a conjugation-invariant
preconnected open set `Ω`, let `ξ` be continuous on `Ω ∩ {0 ≤ im}`, real on `Ω ∩ ℝ`, and solve
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition for
`C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `2 < p < ∞`. If `ξ = O((z - z₀)ⁿ)` within `{0 ≤ im}` at one point
`z₀ ∈ Ω ∩ {0 ≤ im}` (for instance a boundary point on `Ω ∩ ℝ`) for every `n : ℕ`, then `ξ`
vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_forall_isBigO (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hrefl₀ : EqOn (starSchwarzReflection ξ) 0 Ω :=
    eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc
      (continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr)
      (fun _ hz _ ↦ h.hasSimilarityFactorizationAt_starSchwarzReflection hp hp_top hΩ hC hξc hξr hz)
      hz₀.1 fun n ↦ isBigO_starSchwarzReflection_sub_pow hz₀.2 (h₀ n)
  exact fun z hz ↦ (starSchwarzReflection_of_im_nonneg hz.2).symm.trans (hrefl₀ hz.1)

/-- **Boundary unique continuation from a relative neighbourhood.** Under the hypotheses of
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_forall_isBigO`, if `ξ` vanishes on a
relative neighbourhood of `z₀ ∈ Ω ∩ {0 ≤ im}` within `{0 ≤ im}`, then `ξ` vanishes on
`Ω ∩ {0 ≤ im}`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_eventually_eq_zero (hp : 2 < p)
    (hp_top : p ≠ ⊤) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ᶠ z in 𝓝[{z | 0 ≤ z.im}] z₀, ξ z = 0) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
  h.eqOn_zero_of_forall_isBigO hp hp_top hΩ hΩc hC hξc hξr hz₀ fun n ↦
    (isBigO_zero (fun z : ℂ ↦ (z - z₀) ^ n) _).congr' (h₀.mono fun _ hz ↦ hz.symm) EventuallyEq.rfl

/-- **Isolation of interior and boundary zeros.** Under the hypotheses of
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.eqOn_zero_of_forall_isBigO`, if `ξ` does not
vanish identically on `Ω ∩ {0 ≤ im}`, then around every `z₀ ∈ Ω ∩ {0 ≤ im}` — including boundary
points on `Ω ∩ ℝ` — `ξ` has no zeros in `{0 ≤ im} \ {z₀}` near `z₀`. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.eventually_ne_zero (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0)
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, ξ z ≠ 0 := by
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨w, hw, hξw⟩ := hne
  have hrefl_ne : ∀ᶠ z in 𝓝[≠] z₀, starSchwarzReflection ξ z ≠ 0 :=
    eventually_ne_zero_of_hasSimilarityFactorizationAt Ω.isOpen hΩc
      (continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr)
      (fun _ hz _ ↦ h.hasSimilarityFactorizationAt_starSchwarzReflection hp hp_top hΩ hC hξc hξr hz)
      ⟨w, hw.1, by rwa [starSchwarzReflection_of_im_nonneg hw.2]⟩ hz₀.1
  filter_upwards [nhdsWithin_mono z₀ (s := {z | 0 ≤ z.im} \ {z₀}) (fun _ hw ↦ hw.2) hrefl_ne,
    self_mem_nhdsWithin] with z hz hmem
  rwa [starSchwarzReflection_of_im_nonneg hmem.1] at hz

end RealBoundary

/-! ### Calibration checks -/

/-- **Check: the opposite intertwining sign fails.** The identity map `z ↦ z` solves
`∂ₛξ + i ∂ₜξ = 0`, yet admits no local factorization `z = Φ z (σ z)` near `0` with `Φ` continuous
at `0`, `σ` complex differentiable at `0`, and `i • Φ 0 v = -Φ 0 (i • v)` (even without assuming
differentiability of `Φ`). -/
theorem not_exists_eventually_id_eq_apply_of_I_smul_eq_neg :
    ¬ ∃ (Φ : ℂ → ℂ ≃L[ℝ] ℂ) (σ : ℂ → ℂ),
      ContinuousAt (fun z ↦ (Φ z : ℂ →L[ℝ] ℂ)) 0 ∧ DifferentiableAt ℂ σ 0 ∧
      (∀ v, I • Φ 0 v = -Φ 0 (I • v)) ∧ ∀ᶠ z in 𝓝 0, z = Φ z (σ z) := by
  rintro ⟨Φ, σ, hΦ, hσ, hanti, heq⟩
  have h0 : σ 0 = 0 := (Φ 0).map_eq_zero_iff.1 heq.self_of_nhds.symm
  have hslope : Tendsto (fun w : ℂ ↦ w⁻¹ * σ w) (𝓝[≠] 0) (𝓝 (deriv σ 0)) := by
    simpa [h0, div_eq_inv_mul] using hasDerivAt_iff_tendsto_slope_zero.1 hσ.hasDerivAt
  have ht₁ : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto' 0 0 ofReal_zero).mono_left
      nhdsWithin_le_nhds, eventually_mem_nhdsWithin.mono fun t ht ↦ ofReal_ne_zero.2 ht⟩
  have ht₂ : Tendsto (fun t : ℝ ↦ (t : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨((continuous_ofReal.mul continuous_const).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono fun t ht ↦ mul_ne_zero (ofReal_ne_zero.2 ht) I_ne_zero⟩
  have happ {v : ℂ} : Tendsto (fun p : (ℂ →L[ℝ] ℂ) × ℂ ↦ p.1 p.2)
      (𝓝 ((Φ 0 : ℂ →L[ℝ] ℂ), v)) (𝓝 (Φ 0 v)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := ℂ) (F := ℂ)).continuous.tendsto _
  have hlim₁ : Tendsto (fun t : ℝ ↦ Φ t ((t : ℂ)⁻¹ * σ t)) (𝓝[≠] 0) (𝓝 (Φ 0 (deriv σ 0))) :=
    Filter.Tendsto.comp happ (Filter.Tendsto.prodMk_nhds
      (Filter.Tendsto.comp hΦ.tendsto (ht₁.mono_right nhdsWithin_le_nhds))
      (Filter.Tendsto.comp hslope ht₁))
  have hev₁ : (fun t : ℝ ↦ Φ t ((t : ℂ)⁻¹ * σ t)) =ᶠ[𝓝[≠] 0] fun _ ↦ (1 : ℂ) := by
    filter_upwards [ht₁.eventually (nhdsWithin_le_nhds heq), self_mem_nhdsWithin] with t ht ht0
    have hts : (t : ℂ)⁻¹ * σ t = t⁻¹ • σ t := by rw [Complex.real_smul, ofReal_inv]
    rw [hts, map_smul, ← ht, Complex.real_smul, ofReal_inv, inv_mul_cancel₀ (ofReal_ne_zero.2 ht0)]
  have hΦ1 : Φ 0 (deriv σ 0) = 1 :=
    tendsto_nhds_unique hlim₁ (tendsto_const_nhds.congr' hev₁.symm)
  have hlim₂ : Tendsto (fun t : ℝ ↦ Φ ((t : ℂ) * I) (I * (((t : ℂ) * I)⁻¹ * σ ((t : ℂ) * I))))
      (𝓝[≠] 0) (𝓝 (Φ 0 (I * deriv σ 0))) :=
    Filter.Tendsto.comp happ (Filter.Tendsto.prodMk_nhds
      (Filter.Tendsto.comp hΦ.tendsto (ht₂.mono_right nhdsWithin_le_nhds))
      (Filter.Tendsto.comp (((continuous_const.mul continuous_id).tendsto _).comp hslope) ht₂))
  have hev₂ : (fun t : ℝ ↦ Φ ((t : ℂ) * I) (I * (((t : ℂ) * I)⁻¹ * σ ((t : ℂ) * I)))) =ᶠ[𝓝[≠] 0]
      fun _ ↦ I := by
    filter_upwards [ht₂.eventually (nhdsWithin_le_nhds heq), self_mem_nhdsWithin] with t ht ht0
    have hts : I * (((t : ℂ) * I)⁻¹ * σ ((t : ℂ) * I)) = t⁻¹ • σ ((t : ℂ) * I) := by
      rw [Complex.real_smul, ofReal_inv, mul_inv, ← mul_assoc, ← mul_assoc,
        mul_comm I (t : ℂ)⁻¹, mul_assoc (t : ℂ)⁻¹, mul_inv_cancel₀ I_ne_zero, mul_one]
    rw [hts, map_smul, ← ht, Complex.real_smul, ofReal_inv, ← mul_assoc,
      inv_mul_cancel₀ (ofReal_ne_zero.2 ht0), one_mul]
  have hΦI : Φ 0 (I • deriv σ 0) = I := by
    simpa using tendsto_nhds_unique hlim₂ (tendsto_const_nhds.congr' hev₂.symm)
  have hbad : I = -I := by
    have h := hanti (deriv σ 0)
    rw [hΦI, hΦ1, smul_eq_mul, mul_one] at h
    exact h
  norm_num [Complex.ext_iff] at hbad

/-- **Check: `Lᵖ_loc` integrability of the boundary coefficient cannot be dropped.** There exists a
smooth map `ξ : ℂ → ℂ`, real on `ℝ`, vanishing to infinite order at the boundary point `0`, and
nonzero in the open upper half-plane, that solves no weak real-boundary Cauchy–Riemann equation on
`{0 ≤ im}` with `C ∈ Lᵖ_loc({0 ≤ im})` for `2 < p < ∞` (namely `exp (-1 / ‖z‖²)`). -/
theorem exists_contDiff_not_hasWeakConjWirtingerDerivRealBoundaryOn {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) :
    ∃ ξ : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) ξ ∧ (∀ x : ℝ, star (ξ x) = ξ x) ∧
      (∀ n : ℕ, ξ =O[𝓝 0] fun z ↦ (z - 0) ^ n) ∧ (∃ z, 0 < z.im ∧ ξ z ≠ 0) ∧
      ∀ C : ℂ → ℂ →L[ℝ] ℂ, MemLpLoc p {z : ℂ | 0 ≤ z.im} C →
        ¬ HasWeakConjWirtingerDerivRealBoundaryOn ⊤ ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) := by
  have hflat (n : ℕ) : expNegInvNormSq =O[𝓝 0] fun z ↦ (z - 0) ^ n :=
    (expNegInvNormSq_isLittleO_pow n).isBigO.trans (isBigO_of_le _ fun z ↦ by simp)
  refine ⟨expNegInvNormSq, contDiff_expNegInvNormSq, fun x ↦ by simp [expNegInvNormSq_def], hflat,
    ⟨I, by simp, expNegInvNormSq_ne_zero I_ne_zero⟩, fun C hC h ↦ ?_⟩
  have hC' : MemLpLoc p (((⊤ : Opens ℂ) : Set ℂ) ∩ {z | 0 ≤ z.im}) C := by
    simpa only [Opens.coe_top, univ_inter] using hC
  have hzero := h.eqOn_zero_of_forall_isBigO hp hp_top (mapsTo_univ _ _) isPreconnected_univ hC'
    contDiff_expNegInvNormSq.continuous.continuousOn
    (fun x _ ↦ by simp [expNegInvNormSq_def]) ⟨trivial, by simp⟩
    (fun n ↦ (hflat n).mono nhdsWithin_le_nhds)
  exact expNegInvNormSq_ne_zero I_ne_zero (hzero ⟨trivial, by simp⟩)

end TauCeti
