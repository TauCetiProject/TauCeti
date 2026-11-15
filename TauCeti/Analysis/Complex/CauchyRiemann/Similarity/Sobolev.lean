/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.RealBoundaryReflection
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported
import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundaryReflection
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The Sobolev Carleman similarity principle

Let `V` be a finite-dimensional complex normed space and `2 < p < ∞`. On an open set `Ω ⊆ ℂ`, let
`J : ℂ → V →L[ℝ] V` be continuous and in `W^{1,p}_loc(Ω)` with `J² = -1`, let `C : ℂ → V →L[ℝ] V`
lie in `Lᵖ_loc(Ω)`, and let `ξ : ℂ → V` solve the weak linear Cauchy–Riemann equation
`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` (`TauCeti.IsWeakLinearCauchyRiemannOn p Ω J C ξ`). Every point
`z₀ ∈ Ω` is the centre of a disc `ball z₀ r ⊆ Ω` on which `ξ = Φ σ`, where `Φ : ℂ → V ≃L[ℝ] V` is
continuous and in `W^{1,p}_loc` on the disc, intertwines `J` with multiplication by `i`
(`J(z) (Φ(z) v) = Φ(z) (i • v)`), and `σ : ℂ → V` is holomorphic on the disc. Unlike the classical
form in `TauCeti.Analysis.Complex.CauchyRiemann.Similarity`, neither boundedness of `C`, smoothness
of `ξ`, nor constancy of `J` is assumed.

The proof has three stages:

1. **Constant `i` on a complex inner product space.** On a closed disc in `Ω`, `C` is absorbed along
   `ξ` into the `Lᵖ` complex-linear coefficient `D(z) = rankOneDivNormSq ℂ (C(z) (ξ z)) (ξ z)`
   (`MeasureTheory.MemLp.rankOneDivNormSq_apply`). Since `p > 2`, its Hölder conjugate `q` satisfies
   `q < 2`, so `TauCeti.exists_pos_cauchyTransform_eq_of_memLp` solves `g = ½ (1 + T g) ∘ D` in
   `Lᵖ` on a smaller disc with `T g` continuous and `‖T g‖ < 1` there. Because `\bar∂(T g) = g`
   weakly (`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp`), interior `W^{1,p}`
   regularity (`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_one`) places `Ψ = 1 + T g` in
   `W^{1,p}_loc` on the open disc, and the normed-algebra chain rule
   (`TauCeti.MemWkpLoc.ring_inverse`) gives the same for `Ψ⁻¹`. Differentiating `σ = Ψ ξ` by the
   weak Leibniz rule (`TauCeti.HasWeakFDerivOn.bilin_of_memLpLoc`, using `p > 2`) cancels the
   zeroth-order term almost everywhere, so `σ` is holomorphic by Weyl's lemma.
2. **Constant `i` on a finite-dimensional complex normed space**
   (`TauCeti.exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn`): a complex-linear
   equivalence with `EuclideanSpace ℂ (Fin n)` transports the weak equation via
   `ContinuousLinearEquiv.isWeakCauchyRiemannOn_iff_comp` and yields a complex-linear frame
   `Φ : ℂ → V ≃L[ℂ] V`.
3. **Variable `J ∈ W^{1,p}_loc`** (`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann`):
   at `z₀`, `ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul` conjugates
   `J(z₀)` to `i`, and the standard frame `Φ₁(z) = ½(1 - J(z) J(z₀)) Φ₀`
   (`TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame`) reduces the equation on a disc to
   `J = i` with an `Lᵖ_loc` coefficient `frameCoeff`, after which `Φ = Φ₁ ∘ Φ₂` lies in
   `W^{1,p}_loc` by `TauCeti.MemWkpLoc.bilin`.

## Main results

* `TauCeti.exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn`: complex-linear `W^{1,p}`
  similarity factorization for `J = i` and `C ∈ Lᵖ_loc`, `2 < p < ∞`.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann`: **McDuff–Salamon Theorem 2.3.5**, the
  `W^{1,p}` similarity factorization for continuous `J ∈ W^{1,p}_loc` with `J² = -1` and
  `C ∈ Lᵖ_loc`, `2 < p < ∞`.
* `TauCeti.IsWeakLinearCauchyRiemannOn.hasSimilarityFactorizationAt`, together with interior unique
  continuation (`eqOn_zero_of_eventually_eq_zero`, `eqOn_zero_of_eqOn_zero`,
  `eqOn_zero_of_forall_isBigO`), isolated zeros (`eventually_ne_zero`,
  `setOf_ne_zero_mem_codiscreteWithin`), and positive finite zero orders
  (`exists_analyticOrderAt_eq`).
* Real-boundary consequences for `J = i` via Schwarz reflection
  (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_similarity_on_inter_im_nonneg`,
  `eqOn_zero_of_forall_isBigO`, `eventually_ne_zero`): local factorization up to the real axis,
  unique continuation from infinite-order vanishing at an interior or boundary point, and isolation
  of boundary zeros.
* `TauCeti.isWeakLinearCauchyRiemannOn_transportedComplexStructure`: converse in `W^{1,p}_loc`
  showing that for every continuous `W^{1,p}_loc` frame `Φ` and holomorphic `σ`, `ξ = Φ σ` solves a
  weak linear Cauchy–Riemann equation for `J = Φ i Φ⁻¹ ∈ W^{1,p}_loc` and an `Lᵖ_loc` coefficient
  absorbing `DΦ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Section 2.3 (Theorem 2.3.5) and Appendix B.4.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex ContinuousLinearMap Filter MeasureTheory Metric Set
  TopologicalSpace Topology
open scoped ComplexConjugate ENNReal NNReal

namespace TauCeti

/-! ### Supercritical conjugate exponent -/

/-- The Hölder conjugate of an exponent `p > 2` satisfies `q < 2`. -/
private theorem lt_two_of_holderConjugate {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : 2 < p) :
    q < 2 := by
  by_contra! h2q
  have hp2 : p⁻¹ < (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_lt_inv.2 hp
  have hq2 : q⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 h2q
  have h1 : p⁻¹ + q⁻¹ < (2 : ℝ≥0∞)⁻¹ + 2⁻¹ :=
    ENNReal.add_lt_add_of_lt_of_le (hq2.trans_lt (by norm_num)).ne hp2 hq2
  rw [ENNReal.HolderConjugate.inv_add_inv_eq_one p q,
    ENNReal.HolderConjugate.inv_add_inv_eq_one 2 2] at h1
  exact h1.false

private theorem continuousOn_ring_inverse {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {s : Set ℂ} {f : ℂ → R} (hf : ContinuousOn f s) (hu : ∀ z ∈ s, IsUnit (f z)) :
    ContinuousOn (fun z ↦ Ring.inverse (f z)) s := fun z hz ↦ by
  obtain ⟨u, hu'⟩ := hu z hz
  exact (hu' ▸ NormedRing.inverse_continuousAt u).comp_continuousWithinAt (hf z hz)

/-! ### Constant structure `i` on a complex inner product space -/

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Pointwise cancellation behind the weak Leibniz step: if `2 \bar∂Ψ = 2 g` with
`g = ½ Ψ ∘ D` and `D(ξ) = C(ξ)`, while `∂ₛξ + i ∂ₜξ + C(ξ) = 0`, then the weak `\bar∂` expression
for `Ψ ξ` vanishes. -/
private theorem weakConjWirtinger_bilin_eq_zero {Ψ g D : E →L[ℂ] E} {C : E →L[ℝ] E}
    {DΨ : ℂ →L[ℝ] E →L[ℂ] E} {Dξ : ℂ →L[ℝ] E} {x : E}
    (hΨ : (2 : ℂ)⁻¹ • (DΨ 1 + I • DΨ I) = g)
    (hξ : Dξ 1 + I • Dξ I + C x = 0)
    (hg : g = (2 : ℂ)⁻¹ • Ψ.comp D)
    (hDC : D x = C x) :
    (2 : ℂ)⁻¹ • ((DΨ 1 x + Ψ (Dξ 1)) + I • (DΨ I x + Ψ (Dξ I))) = 0 := by
  have hDΨ : DΨ 1 + I • DΨ I = (2 : ℂ) • g := by
    have := congrArg ((2 : ℂ) • ·) hΨ
    rwa [smul_inv_smul₀ (by norm_num : (2 : ℂ) ≠ 0)] at this
  have hDξ : Dξ 1 + I • Dξ I = -C x := eq_neg_of_add_eq_zero_left hξ
  have hsum : (DΨ 1 x + Ψ (Dξ 1)) + I • (DΨ I x + Ψ (Dξ I)) =
      (DΨ 1 + I • DΨ I) x + Ψ (Dξ 1 + I • Dξ I) := by
    simp only [add_apply, smul_apply, smul_add, map_add, map_smul]
    abel
  rw [hsum, hDΨ, hDξ, hg, smul_apply, smul_apply, ContinuousLinearMap.comp_apply, hDC, map_neg,
    smul_inv_smul₀ (by norm_num : (2 : ℂ) ≠ 0), add_neg_cancel, smul_zero]

/-- On an open disc `B = ball z₀ r`, if `g ∈ Lᵖ` is supported in `closedBall z₀ r` and satisfies
`g = ½ (1 + T g) ∘ D` there with `D(z)(ξ z) = C(z)(ξ z)`, and `ξ` solves the weak linear equation
for `i` and `C` on `B`, then `σ = (1 + T g) ξ` is holomorphic on `B` and `Ψ = 1 + T g` lies in
`W^{1,p}_loc(B)`. -/
private theorem memWkpLoc_and_differentiableOn_of_cauchyTransform_eq [FiniteDimensional ℂ E]
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {C : ℂ → E →L[ℝ] E} {D g : ℂ → E →L[ℂ] E} {ξ : ℂ → E}
    (hg : MemLp g p volume) (hgs : Function.support g ⊆ closedBall z₀ r)
    (hTg : Continuous (cauchyTransform g))
    (hgeq : ∀ z ∈ closedBall z₀ r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z))
    (hDC : ∀ z, D z (ξ z) = C z (ξ z))
    (hξ : IsWeakLinearCauchyRiemannOn p (ball z₀ r)
      (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ) :
    MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (1 : E →L[ℂ] E) + cauchyTransform g z) ∧
      DifferentiableOn ℂ (fun z ↦ ((1 : E →L[ℂ] E) + cauchyTransform g z) (ξ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  let r₀ : ℝ≥0 := ⟨r, hr.le⟩
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hwT : HasWeakConjWirtingerDerivOn volume B (cauchyTransform g) g :=
    hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp (c := z₀) (r := r₀) hp1.le
      (hg.restrict _) hgs B
  have hTw : MemWkpLoc p B 1 (cauchyTransform g) :=
    hwT.memWkpLoc_one hp1 hp_top hTg.continuousOn.memLpLoc (hg.restrict _).memLpLoc
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z
  have hΨw : MemWkpLoc p B 1 Ψ := (memWkpLoc_const (1 : E →L[ℂ] E)).add hTw
  have hΨbar : HasWeakConjWirtingerDerivOn volume B Ψ g := by
    have h := (differentiableOn_const (1 : E →L[ℂ] E)).hasWeakConjWirtingerDerivOn_zero.add hwT
    simpa only [Pi.add_def, zero_add] using h
  refine ⟨hΨw, ?_⟩
  obtain ⟨DΨ, hDΨ, hDΨp⟩ := hΨw.exists_weakFDeriv_of_isOpen
  obtain ⟨hξc, hξp, Dξ, hDξ, hDξp, hξae⟩ :=
    isWeakLinearCauchyRiemannOn_iff_of_isOpen (Ω := B).1 hξ
  rw [memWkpLoc_zero_iff] at hDΨp
  set p₀ : ℝ≥0 := p.toNNReal
  have hp₀ : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀2 : 2 < p₀ := by exact_mod_cast hp₀.symm ▸ hp
  let ev : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hΨc : ContinuousOn Ψ B := continuousOn_const.add hTg.continuousOn
  have hleib := hDΨ.bilin_of_memLpLoc ev hp₀2 (one_lt_two.trans hp₀2) le_rfl
    hΨc.memLpLoc (hp₀ ▸ hDΨp) hDξ (hp₀ ▸ hξp) (hp₀ ▸ hDξp)
  have hbar := hleib.hasWeakConjWirtingerDerivOn.congr_ae_deriv (k := 0) ?_
  · exact hbar.differentiableOn (hΨc.clm_apply hξc)
  · filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      hDΨ.hasWeakConjWirtingerDerivOn.ae_eq hΨbar, hξae] with z hz hΨz hξz
    simp only [smul_apply, id_apply] at hξz
    exact weakConjWirtinger_bilin_eq_zero hΨz hξz (hgeq z (ball_subset_closedBall hz)) (hDC z)

/-- The Sobolev similarity principle on a finite-dimensional complex inner product space for `J = i`
and `C ∈ Lᵖ_loc`, `2 < p < ∞`. -/
private theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_of_innerProductSpace
    [FiniteDimensional ℂ E] {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {C : ℂ → E →L[ℝ] E} (hC : MemLpLoc p Ω C) {ξ : ℂ → E}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧ DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  have : p.HolderConjugate p.conjExponent := .conjExponent (one_le_two.trans hp.le)
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  have hsubRΩ : closedBall z₀ (R / 2) ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRΩ
  set D : ℂ → E →L[ℂ] E := fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)
  have hDR : MemLp D p (volume.restrict (closedBall z₀ (R / 2))) :=
    (memLpLoc_iff.1 hC _ hsubRΩ (isCompact_closedBall z₀ (R / 2))).rankOneDivNormSq_apply
      ((hξ.continuousOn.mono hsubRΩ).aestronglyMeasurable measurableSet_closedBall)
  obtain ⟨r, ⟨hr, hrR⟩, g, hg, hgs, hTg, hgeq, hTg1⟩ :=
    exists_pos_cauchyTransform_eq_of_memLp
      (lt_two_of_holderConjugate (q := p.conjExponent) hp) (half_pos hR) hDR
  have hball : ball z₀ r ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hsubRΩ
  obtain ⟨hΨw, hσ⟩ := memWkpLoc_and_differentiableOn_of_cauchyTransform_eq hp hp_top hr hg hgs hTg
    hgeq (fun z ↦ (C z).rankOneDivNormSq_apply_map (ξ z)) (hξ.mono hball)
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z
  have hΨc : ContinuousOn Ψ (ball z₀ r) := continuousOn_const.add hTg.continuousOn
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    refine nonunits.subset_compl_ball h ?_
    rw [mem_ball_iff_norm, add_sub_cancel_left]
    exact hTg1 z (ball_subset_closedBall hz)
  refine ⟨r, hr, hball, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    continuousOn_ring_inverse hΨc hunit, hΨw.ring_inverse hΨc hunit, fun z hz ↦ ?_, hσ,
    fun z hz ↦ ?_⟩
  · beta_reduce
    rw [← (hunit z hz).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  · beta_reduce
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ (hunit z hz), one_apply_eq_self]

end InnerProductSpace

/-! ### Constant structure `i` on a finite-dimensional complex normed space -/

section ComplexNormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- Promotes a family `A : ℂ → W →L[𝕜] W` that is invertible on `U` to a globally defined family of
continuous linear equivalences equal to `A` on `U`. -/
private def toContinuousLinearEquivOn {𝕜 W : Type*} [Semiring 𝕜] [TopologicalSpace W]
    [AddCommMonoid W] [Module 𝕜 W] (U : Set ℂ) (A : ℂ → W →L[𝕜] W)
    (hu : ∀ z ∈ U, IsUnit (A z)) (z : ℂ) : W ≃L[𝕜] W :=
  open Classical in
  if hz : z ∈ U then ContinuousLinearEquiv.unitsEquiv 𝕜 W (hu z hz).unit
  else ContinuousLinearEquiv.refl 𝕜 W

private theorem coe_toContinuousLinearEquivOn {𝕜 W : Type*} [Semiring 𝕜] [TopologicalSpace W]
    [AddCommMonoid W] [Module 𝕜 W] {U : Set ℂ} {A : ℂ → W →L[𝕜] W}
    (hu : ∀ z ∈ U, IsUnit (A z)) {z : ℂ} (hz : z ∈ U) :
    (toContinuousLinearEquivOn U A hu z : W →L[𝕜] W) = A z := by
  classical
  ext v
  simp only [toContinuousLinearEquivOn, hz, ↓reduceDIte]
  exact congr($((hu z hz).unit_spec) v)

/-- **The complex-linear Sobolev similarity principle** for the constant structure `i`. Let `V` be a
finite-dimensional complex normed space, let `2 < p < ∞`, let `Ω ⊆ ℂ` be open, let
`C : ℂ → V →L[ℝ] V` be locally `Lᵖ` on `Ω`, and let `ξ` solve `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on
`Ω`. Around every `z₀ ∈ Ω` there is a disc `ball z₀ r ⊆ Ω` carrying a continuous `W^{1,p}_loc`
family `Φ : ℂ → V ≃L[ℂ] V` of complex-linear automorphisms and a holomorphic `σ : ℂ → V` with
`ξ = Φ σ` on `ball z₀ r`. -/
theorem exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {C : ℂ → V →L[ℝ] V} (hC : MemLpLoc p Ω C) {ξ : ℂ → V}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V ≃L[ℂ] V) (σ : ℂ → V),
      ContinuousOn (fun z ↦ (Φ z : V →L[ℂ] V)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : V →L[ℂ] V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      ∀ z ∈ ball z₀ r, ξ z = Φ z (σ z) := by
  have := FiniteDimensional.completeSpace ℂ V
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let e : V ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let eR : V ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse ((e : V →L[ℂ] E).restrictScalars ℝ)
    ((e.symm : E →L[ℂ] V).restrictScalars ℝ) (fun x ↦ e.symm_apply_apply x)
    (fun y ↦ e.apply_symm_apply y)
  set C' : ℂ → E →L[ℝ] E := fun z ↦ eR.arrowCongr eR (C z)
  have hC' : MemLpLoc p Ω C' := hC.clm_comp (eR.arrowCongr eR).toContinuousLinearMap
  have hξ' : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C'
      (fun z ↦ e (ξ z)) := by
    have h1 := (eR.isWeakCauchyRiemannOn_iff_comp (p := p) (U := Ω)
      (J := fun _ _ ↦ I • ContinuousLinearMap.id ℝ V) (η := fun z x ↦ -C z x) (u := ξ)).1 hξ
    refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h1
    · refine Eventually.of_forall fun z ↦ ContinuousLinearMap.ext fun y ↦ ?_
      simp only [comp_apply, smul_apply, id_apply, ContinuousLinearEquiv.coe_coe]
      change e (I • e.symm y) = I • y
      rw [e.map_smul, e.apply_symm_apply]
    · exact Eventually.of_forall fun z ↦ by simp [C', eR]
  obtain ⟨r, hr, hrΩ, Φ₀, σ₀, hΦ₀c, hΦ₀w, hΦ₀u, hσ₀, hξσ₀⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn_of_innerProductSpace hp hp_top hΩ hC' hξ' hz₀
  let conjE := e.symm.conjContinuousAlgEquiv
  set A : ℂ → V →L[ℂ] V := fun z ↦ conjE (Φ₀ z)
  have hAu (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (A z) := (hΦ₀u z hz).map conjE
  have hAc : ContinuousOn A (ball z₀ r) := conjE.continuous.comp_continuousOn hΦ₀c
  have hAw : MemWkpLoc p (ball z₀ r) 1 A :=
    hΦ₀w.clm_comp (conjE.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
  set Φ : ℂ → V ≃L[ℂ] V := toContinuousLinearEquivOn (ball z₀ r) A hAu
  have hΦeq : EqOn (fun z ↦ (Φ z : V →L[ℂ] V)) A (ball z₀ r) :=
    fun z hz ↦ coe_toContinuousLinearEquivOn hAu hz
  refine ⟨r, hr, hrΩ, Φ, fun z ↦ e.symm (σ₀ z), hAc.congr hΦeq, hAw.congr hΦeq,
    e.symm.differentiable.comp_differentiableOn hσ₀, fun z hz ↦ ?_⟩
  have hco := congr($((hΦeq hz)) (e.symm (σ₀ z)))
  simp only [ContinuousLinearEquiv.coe_coe, A, conjE,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_symm, e.apply_symm_apply] at hco
  have hξz : e (ξ z) = Φ₀ z (σ₀ z) := hξσ₀ hz
  rw [hco, ← hξz, e.symm_apply_apply]

/-! ### Variable complex structure `J ∈ W^{1,p}_loc` -/

/-- Local reduction around `z₀` via `standardFrame`: produces an invertible `W^{1,p}_loc`
real-linear frame `F₁` intertwining `J` with `i` on `ball z₀ R ⊆ Ω` and an `Lᵖ_loc` coefficient `C'`
for which `F₁⁻¹ ξ` solves the weak linear equation with constant structure `i`. -/
private theorem exists_ball_standardFrame_reduction
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {J : ℂ → V →L[ℝ] V} (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    {C : ℂ → V →L[ℝ] V} (hC : MemLpLoc p Ω C) {ξ : ℂ → V}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ R > 0, ball z₀ R ⊆ Ω ∧ ∃ (F₁ C' : ℂ → V →L[ℝ] V),
      ContinuousOn F₁ (ball z₀ R) ∧ MemWkpLoc p (ball z₀ R) 1 F₁ ∧
      (∀ z ∈ ball z₀ R, IsUnit (F₁ z)) ∧
      (∀ z ∈ ball z₀ R, J z ∘L F₁ z = F₁ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      MemLpLoc p (ball z₀ R) C' ∧
      IsWeakLinearCauchyRiemannOn p (ball z₀ R) (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C'
        (fun z ↦ Ring.inverse (F₁ z) (ξ z)) := by
  have := FiniteDimensional.completeSpace ℂ V
  have h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V := hJsq z₀ hz₀
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul h₀
  obtain ⟨R, hR, hRΩ, hu₁⟩ := exists_ball_isUnit_standardFrame hΩ hz₀ hJc h₀
  let B : Opens ℂ := ⟨ball z₀ R, isOpen_ball⟩
  set F₁ : ℂ → V →L[ℝ] V := standardFrame J z₀ Φ₁
  have hF₁c : ContinuousOn F₁ B := continuousOn_standardFrame (hJc.mono hRΩ)
  have hF₁w : MemWkpLoc p B 1 F₁ := memWkpLoc_standardFrame (hJ.mono hRΩ)
  obtain ⟨DF₁, hDF₁, hDF₁p⟩ := hF₁w.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDF₁p
  set p₀ : ℝ≥0 := p.toNNReal
  have hp₀ : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀2 : 2 < p₀ := by exact_mod_cast hp₀.symm ▸ hp
  refine ⟨R, hR, hRΩ, F₁, frameCoeff J C F₁ DF₁, hF₁c, hF₁w, hu₁,
    fun z hz ↦ comp_standardFrame (hJsq z (hRΩ hz)) h₀ hΦ₁,
    (memLpLoc_frameCoeff_iff isOpen_ball.measurableSet hF₁c hDF₁p hu₁ (hJc.mono hRΩ)).2
      (hC.mono_set hRΩ), ?_⟩
  rw [← hp₀]
  exact (isWeakLinearCauchyRiemannOn_iff_standardFrame (Ω := B) hp₀2 (hJc.mono hRΩ)
    (fun z hz ↦ hJsq z (hRΩ hz)) h₀ hΦ₁ hu₁ hDF₁ (hp₀ ▸ hDF₁p)).1 (hp₀ ▸ hξ.mono hRΩ)

/-- **The Carleman similarity principle** (McDuff–Salamon, Theorem 2.3.5). Let `V` be a
finite-dimensional complex normed space and `2 < p < ∞`. On an open set `Ω ⊆ ℂ`, let
`J : ℂ → V →L[ℝ] V` be continuous and in `W^{1,p}_loc(Ω)` with `J² = -1` on `Ω`, let
`C : ℂ → V →L[ℝ] V` lie in `Lᵖ_loc(Ω)`, and let `ξ : ℂ → V` solve `∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`
weakly on `Ω`. Around every `z₀ ∈ Ω` there are a disc `ball z₀ r ⊆ Ω`, a continuous `W^{1,p}_loc`
family `Φ : ℂ → V ≃L[ℝ] V` of real-linear automorphisms intertwining `J` with multiplication by
`i` (`J(z) (Φ(z) v) = Φ(z) (i • v)`), and a holomorphic `σ : ℂ → V` on `ball z₀ r` with
`ξ(z) = Φ(z) (σ(z))` on `ball z₀ r`. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemann
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {J : ℂ → V →L[ℝ] V} (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    {C : ℂ → V →L[ℝ] V} (hC : MemLpLoc p Ω C) {ξ : ℂ → V}
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V ≃L[ℝ] V) (σ : ℂ → V),
      ContinuousOn (fun z ↦ (Φ z : V →L[ℝ] V)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : V →L[ℝ] V)) ∧
      (∀ z ∈ ball z₀ r, ∀ v, J z (Φ z v) = Φ z (I • v)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      ∀ z ∈ ball z₀ r, ξ z = Φ z (σ z) := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨R, hR, hRΩ, F₁, C', hF₁c, hF₁w, hu₁, hJF₁, hC', hη⟩ :=
    exists_ball_standardFrame_reduction hp hp_top hΩ hJc hJ hJsq hC hξ hz₀
  obtain ⟨r, hr, hrB, Φ₂, σ, hΦ₂c, hΦ₂w, hσ, hησ⟩ :=
    exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top isOpen_ball hC' hη
      (mem_ball_self hR)
  let toR : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hΦ₂Rc : ContinuousOn (fun z ↦ (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ) (ball z₀ r) :=
    toR.continuous.comp_continuousOn hΦ₂c
  have hΦ₂Rw : MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ) :=
    hΦ₂w.clm_comp toR
  set A : ℂ → V →L[ℝ] V := fun z ↦ F₁ z ∘L (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ
  have hAu (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (A z) :=
    (hu₁ z (hrB hz)).mul ((Φ₂ z).restrictScalars ℝ).toUnit.isUnit
  have hAc : ContinuousOn A (ball z₀ r) := (hF₁c.mono hrB).clm_comp hΦ₂Rc
  set p₀ : ℝ≥0 := p.toNNReal
  have hp₀ : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀2 : 2 < p₀ := by exact_mod_cast hp₀.symm ▸ hp
  let B' : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hAw : MemWkpLoc p B' 1 A := by
    rw [← hp₀]
    exact (hp₀ ▸ hF₁w.mono hrB).bilin (compL ℝ V V V) hp₀2 (one_lt_two.trans hp₀2) le_rfl
      (hp₀ ▸ hΦ₂Rw)
  set Φ : ℂ → V ≃L[ℝ] V := toContinuousLinearEquivOn (ball z₀ r) A hAu
  have hΦeq : EqOn (fun z ↦ (Φ z : V →L[ℝ] V)) A (ball z₀ r) :=
    fun z hz ↦ coe_toContinuousLinearEquivOn hAu hz
  have hΦapp (z : ℂ) (hz : z ∈ ball z₀ r) (v : V) : Φ z v = F₁ z (Φ₂ z v) := by
    simpa [A] using congr($(hΦeq hz) v)
  refine ⟨r, hr, hrB.trans hRΩ, Φ, σ, hAc.congr hΦeq, hAw.congr hΦeq, fun z hz v ↦ ?_, hσ,
    fun z hz ↦ ?_⟩
  · have hJ' := congr($(hJF₁ z (hrB hz)) (Φ₂ z v))
    simp only [ContinuousLinearMap.comp_apply, smul_apply, id_apply] at hJ'
    rw [hΦapp z hz, hΦapp z hz, map_smul, ← hJ']
  · have hinv : F₁ z (Ring.inverse (F₁ z) (ξ z)) = ξ z := by
      simpa using congr($(Ring.mul_inverse_cancel _ (hu₁ z (hrB hz))) (ξ z))
    rw [hΦapp z hz, ← hησ z hz, hinv]

end ComplexNormedSpace

/-! ### Local factorization, interior unique continuation, and zero orders -/

namespace IsWeakLinearCauchyRiemannOn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- A weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` with `C ∈ Lᵖ_loc`, `2 < p < ∞`, admits a local
similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_I_smul_id (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ)
    (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, hσ, hξσ⟩ :=
    exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top hΩ hC hξ hz₀
  let toR : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hΦRc : ContinuousOn (fun z ↦ ((Φ z).restrictScalars ℝ : V →L[ℝ] V)) (ball z₀ r) :=
    toR.continuous.comp_continuousOn hΦc
  exact HasSimilarityFactorizationAt.of_eqOn_ball hr hΦRc
    ((Φ z₀).restrictScalars ℝ).toUnit.isUnit hσ hξσ

/-- A weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous `J ∈ W^{1,p}_loc`, `J² = -1`, and
`C ∈ Lᵖ_loc`, `2 < p < ∞`, admits a local similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemann hp hp_top hΩ hJc hJ hJsq hC hξ hz₀
  exact HasSimilarityFactorizationAt.of_eqOn_ball hr hΦc (Φ z₀).toUnit.isUnit hσ hξσ

/-- **Unique continuation** from a neighbourhood: on an open preconnected `Ω`, a weak solution for
`2 < p < ∞` vanishing near one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_eventually_eq_zero (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) (h₀ : ∀ᶠ z in 𝓝 z₀, ξ z = 0) :
    EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hp_top hΩ hJc hJ hJsq hC hz) hz₀ h₀

/-- **Unique continuation** from a nonempty open subset: on an open preconnected `Ω`, a weak
solution for `2 < p < ∞` vanishing on a nonempty open `U ⊆ Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_eqOn_zero (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hp_top hΩ hJc hJ hJsq hC hz) hU hUne hUΩ h₀

/-- **Unique continuation from infinite-order vanishing**: on an open preconnected `Ω`, a weak
solution for `2 < p < ∞` satisfying `ξ = O((z - z₀)ⁿ)` for every `n` at one `z₀ ∈ Ω` vanishes on
`Ω`. -/
theorem eqOn_zero_of_forall_isBigO (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hp_top hΩ hJc hJ hJsq hC hz) hz₀ h₀

/-- **Isolated zeros**: on an open preconnected `Ω`, a weak solution for `2 < p < ∞` not
identically zero on `Ω` has no zeros in a punctured neighbourhood of any point of `Ω`. -/
theorem eventually_ne_zero (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω) :
    ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hp_top hΩ hJc hJ hJsq hC hz) hne hz₀

/-- **Discrete zero set**: on an open preconnected `Ω`, the non-zeros of a weak solution for
`2 < p < ∞` not identically zero on `Ω` form a codiscrete subset within `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hp_top hΩ hJc hJ hJsq hC hz) hne

/-- **Positive finite zero orders**: on an open preconnected `Ω`, at every zero `z₀ ∈ Ω` of a weak
solution `ξ` (`2 < p < ∞`) not identically zero on `Ω`, there is a positive integer `m` with
`‖ξ z‖ ≍ ‖z - z₀‖ ^ m` near `z₀` equal to the analytic order of `σ` in every local similarity
factorization `ξ = Φ σ`. -/
theorem exists_analyticOrderAt_eq (hp : 2 < p) (hp_top : p ≠ ⊤) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω)
    (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  have := FiniteDimensional.completeSpace ℂ V
  exact exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hp_top hΩ hJc hJ hJsq hC hz) hne hz₀ hξ₀

end IsWeakLinearCauchyRiemannOn

/-! ### Real-boundary similarity and unique continuation for `J = i` -/

namespace HasWeakConjWirtingerDerivRealBoundaryOn

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [ContinuousStar F] [FiniteDimensional ℂ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {C : ℂ → F →L[ℝ] F} {ξ : ℂ → F} {z₀ : ℂ}

/-- **Boundary similarity factorization for `J = i`.** Let `2 < p < ∞`, let `Ω` be conjugation
invariant, let `C` be locally `Lᵖ` on `Ω ∩ {0 ≤ im}`, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}`,
real on `Ω ∩ ℝ`, and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary
condition. Around every point `z₀ ∈ Ω ∩ {0 ≤ im}` (including boundary points on `ℝ`) there are a
disc `ball z₀ r ⊆ Ω`, a continuous `W^{1,p}_loc` complex-linear frame `Φ : ℂ → F ≃L[ℂ] F`, and a
holomorphic `σ : ℂ → F` on `ball z₀ r` such that `ξ z = Φ z (σ z)` for all
`z ∈ ball z₀ r ∩ {0 ≤ im}`. -/
theorem exists_similarity_on_inter_im_nonneg (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → F ≃L[ℂ] F) (σ : ℂ → F),
      ContinuousOn (fun z ↦ (Φ z : F →L[ℂ] F)) (ball z₀ r) ∧
      MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ z : F →L[ℂ] F)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      ∀ z ∈ ball z₀ r ∩ {z | 0 ≤ z.im}, ξ z = Φ z (σ z) := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hσ, hRσ⟩ :=
    exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top Ω.isOpen
      (hC.starSchwarzReflectionCoeff hΩ) hR hz₀.1
  refine ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦw, hσ, fun z hz ↦ ?_⟩
  simpa [starSchwarzReflection_of_im_nonneg hz.2] using hRσ z hz.1

/-- **Boundary unique continuation from infinite-order vanishing** for `J = i`. On a
conjugation-invariant preconnected open set `Ω` (such as a disc centred on `ℝ`), if a continuous
real-boundary solution for `2 < p < ∞` satisfies `ξ = O((z - z₀)ⁿ)` within `{0 ≤ im}` for every
`n` at a point `z₀ ∈ Ω ∩ {0 ≤ im}` (interior or boundary), then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_forall_isBigO (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  have hC' := hC.starSchwarzReflectionCoeff hΩ
  have hR₀ := eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc
    hR.continuousOn (fun _ hz _ ↦ hR.hasSimilarityFactorizationAt_of_I_smul_id hp hp_top Ω.isOpen
      hC' hz) hz₀.1 fun n ↦ isBigO_starSchwarzReflection_sub_pow hz₀.2 (h₀ n)
  exact fun z hz ↦ by simpa [starSchwarzReflection_of_im_nonneg hz.2] using hR₀ hz.1

/-- **Isolated interior and boundary zeros** for `J = i`. On a conjugation-invariant preconnected
open set `Ω`, a continuous real-boundary solution for `2 < p < ∞` not identically zero on
`Ω ∩ {0 ≤ im}` is nonzero in a punctured half-plane neighbourhood of every point
`z₀ ∈ Ω ∩ {0 ≤ im}`, including points on `ℝ`. -/
theorem eventually_ne_zero (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0)
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, ξ z ≠ 0 := by
  have := FiniteDimensional.completeSpace ℂ F
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  have hC' := hC.starSchwarzReflectionCoeff hΩ
  obtain ⟨w, hw, hξw⟩ := hne
  have hRne : ∃ z ∈ (Ω : Set ℂ), starSchwarzReflection ξ z ≠ 0 :=
    ⟨w, hw.1, by rwa [starSchwarzReflection_of_im_nonneg hw.2]⟩
  have hev := eventually_ne_zero_of_hasSimilarityFactorizationAt Ω.isOpen hΩc hR.continuousOn
    (fun _ hz _ ↦ hR.hasSimilarityFactorizationAt_of_I_smul_id hp hp_top Ω.isOpen hC' hz) hRne
    hz₀.1
  have hsub : {z : ℂ | 0 ≤ z.im} \ {z₀} ⊆ ({z₀}ᶜ : Set ℂ) := fun _ hz ↦ hz.2
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono z₀ hsub hev] with z hz hzR
  rwa [starSchwarzReflection_of_im_nonneg hz.1] at hzR

end HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Converse in `W^{1,p}_loc`: transported complex structures -/

section Converse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Converse of the Sobolev similarity principle.** For `2 < p < ∞`, any continuous frame
`Φ : ℂ → V ≃L[ℝ] V` on an open set `Ω` with weak derivative `DΦ ∈ Lᵖ_loc(Ω)` makes the transported
complex structure `J = Φ i Φ⁻¹` continuous and in `W^{1,p}_loc(Ω)` with `J² = -1`, makes the
absorbing coefficient `C(z) = -(DΦ(z)(1) + J(z) DΦ(z)(i)) Φ(z)⁻¹` lie in `Lᵖ_loc(Ω)`, and turns
every holomorphic `σ : ℂ → V` on `Ω` into a weak solution `ξ = Φ σ` of `∂ₛξ + J ∂ₜξ + C ξ = 0`.
Thus every datum produced by `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemann` satisfies its
hypotheses. -/
theorem isWeakLinearCauchyRiemannOn_transportedComplexStructure {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) {Ω : Opens ℂ} {Φ : ℂ → V ≃L[ℝ] V} {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hΦc : ContinuousOn (fun z ↦ (Φ z : V →L[ℝ] V)) Ω)
    (hDΦ : HasWeakFDerivOn volume Ω (fun z ↦ (Φ z : V →L[ℝ] V)) DΦ)
    (hDΦp : MemLpLoc p Ω DΦ) {σ : ℂ → V} (hσ : DifferentiableOn ℂ σ Ω) :
    let J := transportedComplexStructure Φ
    let C : ℂ → V →L[ℝ] V := fun z ↦ -((DΦ z 1 + J z ∘L DΦ z I) ∘L ((Φ z).symm : V →L[ℝ] V))
    ContinuousOn J Ω ∧ MemWkpLoc p Ω 1 J ∧
      (∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) ∧ MemLpLoc p Ω C ∧
      IsWeakLinearCauchyRiemannOn p Ω J C (fun z ↦ Φ z (σ z)) := by
  have := FiniteDimensional.completeSpace ℂ V
  intro J C
  set F : ℂ → V →L[ℝ] V := fun z ↦ (Φ z : V →L[ℝ] V)
  have hu : ∀ z ∈ (Ω : Set ℂ), IsUnit (F z) := fun z _ ↦ (Φ z).toUnit.isUnit
  have hFw : MemWkpLoc p Ω 1 F :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hΦc.memLpLoc, DΦ, hDΦ, memWkpLoc_zero_iff.2 hDΦp⟩
  have hsymm_eq : ∀ z, Ring.inverse (F z) = ((Φ z).symm : V →L[ℝ] V) := fun z ↦ by
    ext v
    simp [F]
  have hΨw : MemWkpLoc p Ω 1 (fun z ↦ ((Φ z).symm : V →L[ℝ] V)) := by
    simpa only [hsymm_eq] using hFw.ring_inverse hΦc hu
  have hΨc : ContinuousOn (fun z ↦ ((Φ z).symm : V →L[ℝ] V)) Ω := by
    simpa only [hsymm_eq] using continuousOn_ring_inverse hΦc hu
  have hJeq : J = fun z ↦ F z ∘L ((I • ContinuousLinearMap.id ℝ V) ∘L ((Φ z).symm : V →L[ℝ] V)) :=
    funext fun z ↦ ContinuousLinearMap.ext fun v ↦ transportedComplexStructure_apply z v
  set p₀ : ℝ≥0 := p.toNNReal
  have hp₀ : (p₀ : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp_top
  have hp₀2 : 2 < p₀ := by exact_mod_cast hp₀.symm ▸ hp
  have hp₀1 : 1 < p₀ := one_lt_two.trans hp₀2
  have hJc : ContinuousOn J Ω := hJeq ▸ hΦc.clm_comp (continuousOn_const.clm_comp hΨc)
  have hJw : MemWkpLoc p Ω 1 J := by
    rw [hJeq, ← hp₀]
    exact (hp₀ ▸ hFw).bilin (compL ℝ V V V) hp₀2 hp₀1 le_rfl
      ((memWkpLoc_const (p := p₀) _).bilin (compL ℝ V V V) hp₀2 hp₀1 le_rfl (hp₀ ▸ hΨw))
  have hfc_zero : frameCoeff J C F DΦ = 0 := by
    ext z v
    simp [frameCoeff_apply, hsymm_eq, C, J, F]
  have hCp : MemLpLoc p Ω C := by
    refine (memLpLoc_frameCoeff_iff Ω.isOpen.measurableSet hΦc hDΦp hu hJc).1 ?_
    rw [hfc_zero]
    exact memLpLoc_zero
  refine ⟨hJc, hJw, fun z _ ↦ transportedComplexStructure_comp_self z, hCp, ?_⟩
  rw [← hp₀, isWeakLinearCauchyRiemannOn_iff_frame hp₀2 hΦc hDΦ (hp₀ ▸ hDΦp) hu
    (fun z _ ↦ ContinuousLinearMap.ext (transportedComplexStructure_apply_apply z)), hfc_zero]
  have h0eq : (fun (z : ℂ) (x : V) ↦ -(0 : ℂ → V →L[ℝ] V) z x) = fun _ _ ↦ 0 := by ext; simp
  have hσ_sol : IsWeakLinearCauchyRiemannOn p₀ Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ V) 0 σ := by
    rw [IsWeakLinearCauchyRiemannOn, h0eq]
    exact isWeakCauchyRiemannOn_I_smul_id_zero_iff.2 ⟨hσ.continuousOn,
      ((hσ.contDiffOn Ω.isOpen).restrict_scalars ℝ).memWkpLoc subset_rfl,
      hσ.hasWeakConjWirtingerDerivOn_zero⟩
  refine hσ_sol.congr fun z _ ↦ ?_
  simp [hsymm_eq, F]

end Converse

end TauCeti
