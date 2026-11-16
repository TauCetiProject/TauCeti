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
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.FDeriv.Semilinear
import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundaryReflection
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Normed.Ring.Units
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Data.ENNReal.Holder
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.MeasureTheory.Function.RankOne
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The Sobolev Carleman similarity principle

Let `V` be a finite-dimensional complex normed space and `2 < p < ∞`. On an open set `Ω ⊆ ℂ`, let
`J : ℂ → V →L[ℝ] V` be continuous and in `W^{1,p}_loc(Ω)` with `J² = -1`, let `C : ℂ → V →L[ℝ] V`
lie in `Lᵖ_loc(Ω)`, and let `ξ : ℂ → V` solve the weak linear Cauchy–Riemann equation
`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0` (`TauCeti.IsWeakLinearCauchyRiemannOn p Ω J C ξ`). Every point
`z₀ ∈ Ω` is the centre of a disc `ball z₀ r ⊆ Ω` on which `ξ = Φ σ`, where `Φ : ℂ → V ≃L[ℝ] V` is
continuous and in `W^{1,p}_loc` on the disc, intertwines `J` with multiplication by `i`
(`J(z) (Φ(z) v) = Φ(z) (i • v)`), and `σ : ℂ → V` is holomorphic on the disc. Unlike the classical
form in `TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Basic`, neither boundedness of `C`,
smoothness of `ξ`, nor constancy of `J` is assumed.

The proof has three stages:

1. **Constant `i` on a complex inner product space.** On a closed disc in `Ω`, `C` is absorbed along
   `ξ` into the `Lᵖ` complex-linear coefficient `D(z) = rankOneDivNormSq ℂ (C(z) (ξ z)) (ξ z)`
   (`MeasureTheory.MemLp.rankOneDivNormSq_apply`). Since `p > 2`, its Hölder conjugate `q` satisfies
   `q < 2` (`ENNReal.HolderConjugate.two_lt_iff_lt_two`), so
   `TauCeti.exists_mem_Ioo_memLp_eq_smul_one_add_cauchyTransform_comp` solves
   `g = ½ (1 + T g) ∘ D` in `Lᵖ` on a smaller disc with `T g` continuous and `‖T g‖ < 1` there.
   Because `\bar∂(T g) = g` weakly (`TauCeti.hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp`),
   interior `W^{1,p}` regularity (`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_one`) places
   `Ψ = 1 + T g` in `W^{1,p}_loc` on the open disc, and the normed-algebra chain rule
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
* `TauCeti.IsWeakLinearCauchyRiemannOn.hasSimilarityFactorizationAt` and
  `exists_analyticOrderAt_eq` for `p > 2` (including `p = ∞`), together with interior unique
  continuation (`eqOn_zero_of_eventually_eq_zero`, `eqOn_zero_of_eqOn_zero`,
  `eqOn_zero_of_forall_isBigO`) and isolated zeros (`eventually_ne_zero`,
  `setOf_ne_zero_mem_codiscreteWithin`) on any finite-dimensional real normed space `V`.
* Real-boundary consequences for `J = i` via Schwarz reflection
  (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.exists_similarity_on_inter_im_nonneg`,
  `eqOn_zero_of_forall_isBigO`, `eqOn_zero_of_eventually_eq_zero`, `eqOn_zero_of_eqOn_zero`,
  `eventually_ne_zero`, `exists_analyticOrderAt_eq`): local factorization up to the real axis with
  real-symmetric `Φ` and `σ`, unique continuation, isolated boundary zeros, and positive finite
  zero orders for `p > 2`.
* `TauCeti.memWkpLoc_transportedComplexStructure`,
  `TauCeti.memLpLoc_neg_add_transportedComplexStructure_comp_symm`, and
  `TauCeti.isWeakLinearCauchyRiemannOn_transportedComplexStructure`: converse in `W^{1,p}_loc` on
  any complete complex normed space for arbitrary `p`.

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

private theorem coe_restrictScalars_eq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (e : W ≃L[ℂ] W) :
    ((e.restrictScalars ℝ : W ≃L[ℝ] W) : W →L[ℝ] W) = (e : W →L[ℂ] W).restrictScalars ℝ := by
  ext
  simp

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
  lift p to ℝ≥0 using hp_top
  have := FiniteDimensional.completeSpace ℂ E
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  let r₀ : ℝ≥0 := ⟨r, hr.le⟩
  have hp2 : 2 < p := by exact_mod_cast hp
  have hp1 : 1 < (p : ℝ≥0∞) := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hwT : HasWeakConjWirtingerDerivOn volume B (cauchyTransform g) g :=
    hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp (c := z₀) (r := r₀) hp1.le
      (hg.restrict _) hgs B
  have hTw : MemWkpLoc p B 1 (cauchyTransform g) :=
    hwT.memWkpLoc_one hp1 ENNReal.coe_ne_top hTg.continuousOn.memLpLoc (hg.restrict _).memLpLoc
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
  let ev : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hΨc : ContinuousOn Ψ B := continuousOn_const.add hTg.continuousOn
  have hleib := hDΨ.bilin_of_memLpLoc ev hp2 (one_lt_two.trans hp2) le_rfl
    hΨc.memLpLoc hDΨp hDξ hξp hDξp
  have hev : (fun z ↦ ev (Ψ z) (ξ z)) = fun z ↦ Ψ z (ξ z) := by
    ext z
    simp [ev, ContinuousLinearMap.coe_restrict_scalarsL']
  rw [hev] at hleib
  have hbar := hleib.hasWeakConjWirtingerDerivOn.congr_ae_deriv (k := 0) ?_
  · exact hbar.differentiableOn (hΨc.clm_apply hξc)
  · filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      hDΨ.hasWeakConjWirtingerDerivOn.ae_eq hΨbar, hξae] with z hz hΨz hξz
    simp only [smul_apply, id_apply] at hξz
    simp only [ev, add_apply, precompL_apply, precompR_apply, compL_apply, comp_apply,
      coe_restrict_scalarsL', coe_restrictScalars']
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
    exists_mem_Ioo_memLp_eq_smul_one_add_cauchyTransform_comp
      ((ENNReal.HolderConjugate.two_lt_iff_lt_two p p.conjExponent).1 hp) (half_pos hR) hDR
  have hball : ball z₀ r ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hsubRΩ
  obtain ⟨hΨw, hσ⟩ := memWkpLoc_and_differentiableOn_of_cauchyTransform_eq hp hp_top hr hg hgs hTg
    hgeq (fun z ↦ (C z).rankOneDivNormSq_apply_map (ξ z)) (hξ.mono hball)
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z
  have hΨc : ContinuousOn Ψ (ball z₀ r) := continuousOn_const.add hTg.continuousOn
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    simpa [Ψ, sub_neg_eq_add] using
      IsUnit.one_sub_of_norm_lt_one (x := -cauchyTransform g z)
        (by simpa using hTg1 z (ball_subset_closedBall hz))
  refine ⟨r, hr, hball, fun z ↦ Ring.inverse (Ψ z), fun z ↦ Ψ z (ξ z),
    NormedRing.continuousOn_inverse hΨc hunit, hΨw.ring_inverse hΨc hunit,
    fun z hz ↦ (hunit z hz).ringInverse, hσ, fun z hz ↦ ?_⟩
  simp [ContinuousLinearMap.ringInverse_apply_apply (hunit z hz)]

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
  let eR : V ≃L[ℝ] E := e.restrictScalars' ℝ
  set C' : ℂ → E →L[ℝ] E := fun z ↦ eR.arrowCongr eR (C z)
  have hC' : MemLpLoc p Ω C' := hC.clm_comp (eR.arrowCongr eR).toContinuousLinearMap
  have hξ' : IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ E) C'
      (fun z ↦ e (ξ z)) := by
    have h1 := (eR.isWeakCauchyRiemannOn_iff_comp (p := p) (U := Ω)
      (J := fun _ _ ↦ I • ContinuousLinearMap.id ℝ V) (η := fun z x ↦ -C z x) (u := ξ)).1 hξ
    simp only [eR, ContinuousLinearEquiv.coe_restrictScalars'] at h1
    refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h1
    · exact Eventually.of_forall fun z ↦ by ext y; simp
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
  lift p to ℝ≥0 using hp_top
  have := FiniteDimensional.completeSpace ℂ V
  have hp2 : 2 < p := by exact_mod_cast hp
  have h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V := hJsq z₀ hz₀
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul h₀
  obtain ⟨R, hR, hRΩ, hu₁⟩ := exists_ball_isUnit_standardFrame hΩ hz₀ hJc h₀
  let B : Opens ℂ := ⟨ball z₀ R, isOpen_ball⟩
  set F₁ : ℂ → V →L[ℝ] V := standardFrame J z₀ Φ₁
  have hF₁c : ContinuousOn F₁ B := continuousOn_standardFrame (hJc.mono hRΩ)
  have hF₁w : MemWkpLoc p B 1 F₁ := memWkpLoc_standardFrame (hJ.mono hRΩ)
  obtain ⟨DF₁, hDF₁, hDF₁p⟩ := hF₁w.exists_weakFDeriv_of_isOpen
  rw [memWkpLoc_zero_iff] at hDF₁p
  refine ⟨R, hR, hRΩ, F₁, frameCoeff J C F₁ DF₁, hF₁c, hF₁w, hu₁,
    fun z hz ↦ comp_standardFrame (hJsq z (hRΩ hz)) h₀ hΦ₁,
    (memLpLoc_frameCoeff_iff isOpen_ball.measurableSet hF₁c hDF₁p hu₁ (hJc.mono hRΩ)).2
      (hC.mono_set hRΩ),
    (isWeakLinearCauchyRiemannOn_iff_standardFrame (Ω := B) hp2 (hJc.mono hRΩ)
      (fun z hz ↦ hJsq z (hRΩ hz)) h₀ hΦ₁ hu₁ hDF₁ hDF₁p).1 (hξ.mono hRΩ)⟩

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
  lift p to ℝ≥0 using hp_top
  have := FiniteDimensional.completeSpace ℂ V
  have hp2 : 2 < p := by exact_mod_cast hp
  obtain ⟨R, hR, hRΩ, F₁, C', hF₁c, hF₁w, hu₁, hJF₁, hC', hη⟩ :=
    exists_ball_standardFrame_reduction hp ENNReal.coe_ne_top hΩ hJc hJ hJsq hC hξ hz₀
  obtain ⟨r, hr, hrB, Φ₂, σ, hΦ₂c, hΦ₂w, hσ, hησ⟩ :=
    exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn hp ENNReal.coe_ne_top isOpen_ball
      hC' hη (mem_ball_self hR)
  let toR : (V →L[ℂ] V) →L[ℝ] V →L[ℝ] V := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have htoR : (fun z ↦ toR (Φ₂ z : V →L[ℂ] V)) =
      fun z ↦ (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ := by
    ext z v
    simp [toR, ContinuousLinearMap.coe_restrict_scalarsL']
  have hΦ₂Rc : ContinuousOn (fun z ↦ (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ) (ball z₀ r) := by
    rw [← htoR]
    exact toR.continuous.comp_continuousOn hΦ₂c
  have hΦ₂Rw : MemWkpLoc p (ball z₀ r) 1 (fun z ↦ (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ) := by
    rw [← htoR]
    exact hΦ₂w.clm_comp toR
  set A : ℂ → V →L[ℝ] V := fun z ↦ F₁ z ∘L (Φ₂ z : V →L[ℂ] V).restrictScalars ℝ
  have hAu (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (A z) := by
    simp only [A, ← ContinuousLinearMap.mul_def, ← coe_restrictScalars_eq]
    exact (hu₁ z (hrB hz)).mul ((Φ₂ z).restrictScalars ℝ).toUnit.isUnit
  have hAc : ContinuousOn A (ball z₀ r) := (hF₁c.mono hrB).clm_comp hΦ₂Rc
  let B' : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hAw : MemWkpLoc p B' 1 A :=
    (hF₁w.mono hrB).bilin (compL ℝ V V V) hp2 (one_lt_two.trans hp2) le_rfl hΦ₂Rw
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
  · rw [hΦapp z hz, ← hησ z hz, ContinuousLinearMap.apply_ringInverse_apply (hu₁ z (hrB hz))]

end ComplexNormedSpace

/-! ### Local factorization, interior unique continuation, and zero orders -/

namespace IsWeakLinearCauchyRiemannOn

section ComplexTarget

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- On an open set `Ω`, a weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous
`J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and `C ∈ Lᵖ_loc(Ω)`, `p > 2`, admits a local similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt (hp : 2 < p) (hΩ : IsOpen Ω)
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  set q : ℝ≥0∞ := min p 3
  have hq : 2 < q := lt_min hp (by norm_num)
  have hq_top : q ≠ ⊤ := ((min_le_right p 3).trans_lt (by norm_num)).ne
  have hqp : q ≤ p := min_le_left p 3
  obtain ⟨r, hr, -, Φ, σ, hΦc, -, -, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemann hq hq_top hΩ hJc (hJ.mono_exponent hqp) hJsq
      (hC.mono_exponent hqp) (hξ.mono_exponent hqp) hz₀
  exact HasSimilarityFactorizationAt.of_eqOn_ball hr hΦc (Φ z₀).toUnit.isUnit hσ hξσ

end ComplexTarget

section RealTarget

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- Transports a weak linear Cauchy–Riemann equation on a finite-dimensional real normed space `V`
with `J² = -1` on a nonempty open set `Ω` along a real-linear isomorphism to
`EuclideanSpace ℂ (Fin n)`. -/
private theorem exists_euclideanSpace_transport
    (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℂ (Fin n))
      (J' C' : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)),
      ContinuousOn J' Ω ∧ MemWkpLoc p Ω 1 J' ∧
      (∀ z ∈ Ω, (J' z).comp (J' z) = -ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))) ∧
      MemLpLoc p Ω C' ∧
      IsWeakLinearCauchyRiemannOn p Ω J' C' (fun z ↦ e (ξ z)) := by
  obtain ⟨n, Φ, -⟩ :=
    (J z₁).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul (hJsq z₁ hz₁)
  let e : V ≃L[ℝ] EuclideanSpace ℂ (Fin n) := Φ.symm
  set J' : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    fun z ↦ e.arrowCongr e (J z)
  set C' : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    fun z ↦ e.arrowCongr e (C z)
  refine ⟨n, e, J', C', (e.arrowCongr e).continuous.comp_continuousOn hJc,
    hJ.clm_comp (e.arrowCongr e).toContinuousLinearMap, fun z hz ↦ ?_,
    hC.clm_comp (e.arrowCongr e).toContinuousLinearMap, ?_⟩
  · refine ContinuousLinearMap.ext fun y ↦ ?_
    have hsq : J z (J z (e.symm y)) = -e.symm y := by simpa using congr($(hJsq z hz) (e.symm y))
    simp [J', hsq]
  · have h1 := (e.isWeakCauchyRiemannOn_iff_comp (p := p) (U := Ω)
      (J := fun z _ ↦ J z) (η := fun z x ↦ -C z x) (u := ξ)).1 hξ
    refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h1
    · exact Eventually.of_forall fun z ↦ by ext y; simp [J']
    · exact Eventually.of_forall fun z ↦ by simp [C']

/-- **Unique continuation** from a neighbourhood: on an open preconnected `Ω`, a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous `J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and `C ∈ Lᵖ_loc(Ω)`,
`p > 2`, vanishing near one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_eventually_eq_zero (hp : 2 < p) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω) (h₀ : ∀ᶠ z in 𝓝 z₀, ξ z = 0) :
    EqOn ξ 0 Ω := by
  obtain ⟨n, e, J', C', hJ'c, hJ', hJ'sq, hC', hξ'⟩ :=
    exists_euclideanSpace_transport hJc hJ hJsq hC hξ hz₀
  have h0' : ∀ᶠ z in 𝓝 z₀, e (ξ z) = 0 := h₀.mono fun z hz ↦ by simp [hz]
  have hEq := eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc
    hξ'.continuousOn (fun _ hz _ ↦ hξ'.hasSimilarityFactorizationAt hp hΩ hJ'c hJ' hJ'sq hC' hz)
    hz₀ h0'
  exact fun z hz ↦ e.map_eq_zero_iff.1 (hEq hz)

/-- **Unique continuation** from a nonempty open subset: on an open preconnected `Ω`, a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous `J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and
`C ∈ Lᵖ_loc(Ω)`, `p > 2`, vanishing on a nonempty open `U ⊆ Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_eqOn_zero (hp : 2 < p) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  obtain ⟨z₁, hz₁⟩ := hUne
  exact hξ.eqOn_zero_of_eventually_eq_zero hp hΩ hΩc hJc hJ hJsq hC (hUΩ hz₁)
    (eventually_of_mem (hU.mem_nhds hz₁) h₀)

/-- **Unique continuation from infinite-order vanishing**: on an open preconnected `Ω`, a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous `J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and
`C ∈ Lᵖ_loc(Ω)`, `p > 2`, satisfying `ξ = O((z - z₀)ⁿ)` for every `n` at one `z₀ ∈ Ω` vanishes on
`Ω`. -/
theorem eqOn_zero_of_forall_isBigO (hp : 2 < p) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 Ω := by
  obtain ⟨m, e, J', C', hJ'c, hJ', hJ'sq, hC', hξ'⟩ :=
    exists_euclideanSpace_transport hJc hJ hJsq hC hξ hz₀
  have hEq := eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ'.continuousOn
    (fun _ hz _ ↦ hξ'.hasSimilarityFactorizationAt hp hΩ hJ'c hJ' hJ'sq hC' hz) hz₀
    fun k ↦ (e.toContinuousLinearMap.isBigO_comp _ _).trans (h₀ k)
  exact fun z hz ↦ e.map_eq_zero_iff.1 (hEq hz)

/-- **Isolated zeros**: on an open preconnected `Ω`, a weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`
with continuous `J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and `C ∈ Lᵖ_loc(Ω)`, `p > 2`, not identically
zero on `Ω` has no zeros in a punctured neighbourhood of any point of `Ω`. -/
theorem eventually_ne_zero (hp : 2 < p) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω) :
    ∀ᶠ z in 𝓝[≠] z₀, ξ z ≠ 0 := by
  obtain ⟨w, hwΩ, hw⟩ := hne
  obtain ⟨n, e, J', C', hJ'c, hJ', hJ'sq, hC', hξ'⟩ :=
    exists_euclideanSpace_transport hJc hJ hJsq hC hξ hz₀
  have hev := eventually_ne_zero_of_hasSimilarityFactorizationAt hΩ hΩc hξ'.continuousOn
    (fun _ hz _ ↦ hξ'.hasSimilarityFactorizationAt hp hΩ hJ'c hJ' hJ'sq hC' hz)
    ⟨w, hwΩ, e.map_ne_zero_iff.2 hw⟩ hz₀
  exact hev.mono fun z hz ↦ e.map_ne_zero_iff.1 hz

/-- **Discrete zero set**: on an open preconnected `Ω`, the non-zeros of a weak solution of
`∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous `J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and `C ∈ Lᵖ_loc(Ω)`,
`p > 2`, not identically zero on `Ω` form a codiscrete subset within `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin (hp : 2 < p) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨w, hwΩ, hw⟩ := hne
  obtain ⟨n, e, J', C', hJ'c, hJ', hJ'sq, hC', hξ'⟩ :=
    exists_euclideanSpace_transport hJc hJ hJsq hC hξ hwΩ
  have hcd := setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc
    hξ'.continuousOn (fun _ hz _ ↦ hξ'.hasSimilarityFactorizationAt hp hΩ hJ'c hJ' hJ'sq hC' hz)
    ⟨w, hwΩ, e.map_ne_zero_iff.2 hw⟩
  have hset : {z | e (ξ z) ≠ 0} = {z | ξ z ≠ 0} := by
    ext z
    exact e.map_ne_zero_iff
  rwa [hset] at hcd

end RealTarget

section ComplexZeroOrder

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {p : ℝ≥0∞} {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- **Positive finite zero orders**: on an open preconnected `Ω`, at every zero `z₀ ∈ Ω` of a weak
solution `ξ` of `∂ₛξ + J ∂ₜξ + C ξ = 0` with continuous `J ∈ W^{1,p}_loc(Ω)`, `J² = -1`, and
`C ∈ Lᵖ_loc(Ω)`, `p > 2`, not identically zero on `Ω`, there is a positive integer `m` with
`‖ξ z‖ ≍ ‖z - z₀‖ ^ m` near `z₀` equal to the analytic order of `σ` in every local similarity
factorization `ξ = Φ σ`. -/
theorem exists_analyticOrderAt_eq (hp : 2 < p) (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJc : ContinuousOn J Ω) (hJ : MemWkpLoc p Ω 1 J)
    (hJsq : ∀ z ∈ Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V) (hC : MemLpLoc p Ω C)
    (hξ : IsWeakLinearCauchyRiemannOn p Ω J C ξ) (hne : ∃ z ∈ Ω, ξ z ≠ 0) (hz₀ : z₀ ∈ Ω)
    (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  have := FiniteDimensional.completeSpace ℂ V
  exact exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hξ.hasSimilarityFactorizationAt hp hΩ hJc hJ hJsq hC hz) hne hz₀ hξ₀

end ComplexZeroOrder

end IsWeakLinearCauchyRiemannOn

/-! ### Real-boundary similarity and unique continuation for `J = i` -/

namespace HasWeakConjWirtingerDerivRealBoundaryOn

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [ContinuousStar F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {C : ℂ → F →L[ℝ] F} {ξ : ℂ → F} {z₀ : ℂ}

/-- Conjugation by `star` on `F →L[ℂ] F` (`A ↦ star ∘ A ∘ star`) bundled as a continuous `ℝ`-linear
involution. -/
private def starConjCLM : (F →L[ℂ] F) →L[ℝ] (F →L[ℂ] F) :=
  let sc : (F →L[ℂ] F) ≃L⋆[ℂ] (F →L[ℂ] F) :=
    (starL ℂ : F ≃L⋆[ℂ] F).arrowCongrSL (starL ℂ : F ≃L⋆[ℂ] F)
  { toLinearMap :=
      { toFun := sc
        map_add' := sc.map_add
        map_smul' := fun (r : ℝ) A ↦ by
          rw [← Complex.coe_smul, sc.map_smulₛₗ, starRingEnd_apply, Complex.star_def,
            Complex.conj_ofReal, Complex.coe_smul]
          rfl }
    cont := sc.continuous }

@[simp]
private theorem starConjCLM_apply_apply (A : F →L[ℂ] F) (v : F) :
    starConjCLM A v = star (A (star v)) :=
  rfl

private theorem starConjCLM_involutive (A : F →L[ℂ] F) :
    starConjCLM (starConjCLM A) = A := by
  ext v
  simp

private theorem starConjCLM_one : starConjCLM (1 : F →L[ℂ] F) = 1 := by
  ext v
  simp

private theorem starConjCLM_mul (A B : F →L[ℂ] F) :
    starConjCLM (A * B) = starConjCLM A * starConjCLM B := by
  ext v
  simp

private theorem starConjCLM_ringInverse {A : F →L[ℂ] F} (hu : IsUnit A)
    (hA : starConjCLM A = A) : starConjCLM (Ring.inverse A) = Ring.inverse A := by
  obtain ⟨u, rfl⟩ := hu
  rw [Ring.inverse_unit]
  have hmul : (u : F →L[ℂ] F) * starConjCLM (↑u⁻¹ : F →L[ℂ] F) = 1 := by
    rw [← hA, ← starConjCLM_mul, Units.mul_inv, starConjCLM_one]
  calc starConjCLM (↑u⁻¹ : F →L[ℂ] F)
      = 1 * starConjCLM (↑u⁻¹ : F →L[ℂ] F) := (one_mul _).symm
    _ = (↑u⁻¹ * (u : F →L[ℂ] F)) * starConjCLM (↑u⁻¹ : F →L[ℂ] F) := by rw [Units.inv_mul]
    _ = ↑u⁻¹ * ((u : F →L[ℂ] F) * starConjCLM (↑u⁻¹ : F →L[ℂ] F)) := mul_assoc _ _ _
    _ = ↑u⁻¹ := by rw [hmul, mul_one]

variable [FiniteDimensional ℂ F]

/-- **Boundary similarity factorization for `J = i`.** Let `2 < p < ∞`, let `Ω` be conjugation
invariant, let `C` be locally `Lᵖ` on `Ω ∩ {0 ≤ im}`, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}`,
real on `Ω ∩ ℝ`, and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary
condition. Around every point `z₀ ∈ Ω ∩ {0 ≤ im}` (including boundary points on `ℝ`) there are a
disc `ball z₀ r ⊆ Ω`, a continuous `W^{1,p}_loc` complex-linear frame `Φ : ℂ → F ≃L[ℂ] F`, and a
holomorphic `σ : ℂ → F` on `ball z₀ r` such that `Φ` commutes with `star` and `σ` is fixed by
`star` along `ball z₀ r ∩ ℝ`, and `ξ z = Φ z (σ z)` for all `z ∈ ball z₀ r ∩ {0 ≤ im}`. -/
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
      (∀ x : ℝ, (x : ℂ) ∈ ball z₀ r → ∀ v, star (Φ x v) = Φ x (star v)) ∧
      (∀ x : ℝ, (x : ℂ) ∈ ball z₀ r → star (σ x) = σ x) ∧
      ∀ z ∈ ball z₀ r ∩ {z | 0 ≤ z.im}, ξ z = Φ z (σ z) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hp1 hp_top hΩ hC hξc hξr
  obtain ⟨r₁, hr₁, hr₁Ω, Φ₁, σ₁, hΦ₁c, hΦ₁w, hσ₁, hRσ₁⟩ :=
    exists_complexLinear_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top Ω.isOpen
      (hC.starSchwarzReflectionCoeff hΩ) hR hz₀.1
  rcases (show 0 ≤ z₀.im from hz₀.2).lt_or_eq with hpos | hzero
  · -- Interior point `0 < z₀.im`: shrink the disc so it misses the real axis.
    set r : ℝ := min r₁ z₀.im
    have hr : 0 < r := lt_min hr₁ hpos
    have hr_sub : ball z₀ r ⊆ ball z₀ r₁ := ball_subset_ball (min_le_left _ _)
    have hdisj (x : ℝ) (hx : (x : ℂ) ∈ ball z₀ r) : False := by
      have h1 : |((x : ℂ) - z₀).im| ≤ ‖(x : ℂ) - z₀‖ := Complex.abs_im_le_norm _
      have h2 : ‖(x : ℂ) - z₀‖ < z₀.im :=
        (mem_ball_iff_norm.1 hx).trans_le (min_le_right _ _)
      simp only [sub_im, ofReal_im, zero_sub, abs_neg, abs_of_pos hpos] at h1
      exact (h1.trans_lt h2).false
    refine ⟨r, hr, hr_sub.trans hr₁Ω, Φ₁, σ₁, hΦ₁c.mono hr_sub, hΦ₁w.mono hr_sub,
      hσ₁.mono hr_sub, fun x hx ↦ (hdisj x hx).elim, fun x hx ↦ (hdisj x hx).elim, fun z hz ↦ ?_⟩
    simpa [starSchwarzReflection_of_im_nonneg hz.2] using hRσ₁ z (hr_sub hz.1)
  · -- Boundary point `z₀.im = 0`: normalize at `z₀` and symmetrize across `ℝ`.
    have hz₀_im : z₀.im = 0 := hzero.symm
    have hz₀_conj : conj z₀ = z₀ := Complex.conj_eq_iff_im.2 hz₀_im
    have hball_conj {ρ : ℝ} : MapsTo (starRingEnd ℂ) (ball z₀ ρ) (ball z₀ ρ) := fun z hz ↦ by
      rw [mem_ball, ← hz₀_conj, starRingEnd_apply, Complex.star_def, Complex.dist_conj_conj]
      exact hz
    have hsymm_eq : (fun z ↦ ((Φ₁ z).symm : F →L[ℂ] F)) =
        fun z ↦ Ring.inverse (Φ₁ z : F →L[ℂ] F) := by
      ext z v
      simp
    have hu₁ : ∀ z ∈ ball z₀ r₁, IsUnit (Φ₁ z : F →L[ℂ] F) := fun z _ ↦ (Φ₁ z).toUnit.isUnit
    have hΦ₁_symm_c : ContinuousOn (fun z ↦ ((Φ₁ z).symm : F →L[ℂ] F)) (ball z₀ r₁) := by
      rw [hsymm_eq]
      exact NormedRing.continuousOn_inverse hΦ₁c hu₁
    have hΦ₁_symm_w : MemWkpLoc p (ball z₀ r₁) 1 (fun z ↦ ((Φ₁ z).symm : F →L[ℂ] F)) := by
      rw [hsymm_eq]
      exact hΦ₁w.ring_inverse hΦ₁c hu₁
    set Ψ₁ : ℂ → F →L[ℂ] F := fun z ↦ (Φ₁ z₀ : F →L[ℂ] F) ∘L ((Φ₁ z).symm : F →L[ℂ] F)
    set σ₂ : ℂ → F := fun z ↦ Φ₁ z₀ (σ₁ z)
    have hΨ₁c : ContinuousOn Ψ₁ (ball z₀ r₁) := continuousOn_const.clm_comp hΦ₁_symm_c
    have hΨ₁w : MemWkpLoc p (ball z₀ r₁) 1 Ψ₁ :=
      hΦ₁_symm_w.clm_comp ((compL ℂ F F F (Φ₁ z₀ : F →L[ℂ] F)).restrictScalars ℝ)
    have hΨ₁_z₀ : Ψ₁ z₀ = 1 := by
      ext v
      simp [Ψ₁]
    have hσ₂ : DifferentiableOn ℂ σ₂ (ball z₀ r₁) :=
      (Φ₁ z₀ : F →L[ℂ] F).differentiable.comp_differentiableOn hσ₁
    have hΨ₁_Rξ (z : ℂ) (hz : z ∈ ball z₀ r₁) : Ψ₁ z (starSchwarzReflection ξ z) = σ₂ z := by
      simp [Ψ₁, σ₂, hRσ₁ z hz]
    have hRξ_conj (z : ℂ) (hz : z ∈ ball z₀ r₁) :
        starSchwarzReflection ξ (conj z) = star (starSchwarzReflection ξ z) := by
      by_cases hzim : z.im = 0
      · have hzx : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hzim)
        rw [Complex.conj_eq_iff_im.2 hzim, starSchwarzReflection_of_im_nonneg hzim.ge, hzx,
          hξr z.re (hzx ▸ hr₁Ω hz)]
      · exact starSchwarzReflection_conj hzim
    set Ψ : ℂ → F →L[ℂ] F := fun z ↦ (2 : ℝ)⁻¹ • (Ψ₁ z + starConjCLM (Ψ₁ (conj z)))
    set σ : ℂ → F := fun z ↦ (2 : ℝ)⁻¹ • (σ₂ z + star (σ₂ (conj z)))
    have hΨc : ContinuousOn Ψ (ball z₀ r₁) :=
      (continuousOn_const (c := (2 : ℝ)⁻¹)).smul (hΨ₁c.add (starConjCLM.continuous.comp_continuousOn
        (hΨ₁c.comp Complex.continuous_conj.continuousOn hball_conj)))
    have hΨw : MemWkpLoc p (ball z₀ r₁) 1 Ψ :=
      (hΨ₁w.add ((hΨ₁w.comp_conj hball_conj).clm_comp starConjCLM)).const_smul _
    have hσ_conj : DifferentiableOn ℂ (fun z ↦ star (σ₂ (conj z))) (ball z₀ r₁) := fun z hz ↦ by
      have hmaps : MapsTo (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap (ball z₀ r₁) (ball z₀ r₁) :=
        fun w hw ↦ hball_conj hw
      simpa [Function.comp_def] using
        DifferentiableWithinAt.comp_semilinear₂
          (starL ℂ : F ≃L⋆[ℂ] F).toContinuousLinearMap
          (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap
          (x := z) (hσ₂ (conj z) (hball_conj hz)) hmaps
    have hσd : DifferentiableOn ℂ σ (ball z₀ r₁) := by
      have h2 : σ = fun z ↦ ((2 : ℂ)⁻¹) • (σ₂ z + star (σ₂ (conj z))) := by
        ext z
        simp [σ, ← Complex.coe_smul]
      rw [h2]
      exact (hσ₂.add hσ_conj).const_smul _
    have hΨ_Rξ (z : ℂ) (hz : z ∈ ball z₀ r₁) : Ψ z (starSchwarzReflection ξ z) = σ z := by
      have hcz : starConjCLM (Ψ₁ (conj z)) (starSchwarzReflection ξ z) = star (σ₂ (conj z)) := by
        rw [starConjCLM_apply_apply, ← hRξ_conj z hz, hΨ₁_Rξ (conj z) (hball_conj hz)]
      simp [Ψ, σ, hΨ₁_Rξ z hz, hcz]
    have hΨ_z₀ : Ψ z₀ = 1 := by
      simp only [Ψ, hz₀_conj, hΨ₁_z₀, starConjCLM_one, ← two_smul ℝ (1 : F →L[ℂ] F),
        inv_smul_smul₀ (two_ne_zero' ℝ)]
    have hΨ_nhds : ∀ᶠ z in 𝓝 z₀, IsUnit (Ψ z) :=
      (hΨc.continuousAt (ball_mem_nhds z₀ hr₁)).eventually
        (hΨ_z₀ ▸ Units.isOpen.mem_nhds isUnit_one)
    obtain ⟨r₂, hr₂, hr₂u⟩ := Metric.eventually_nhds_iff_ball.1 hΨ_nhds
    set r : ℝ := min r₁ r₂
    have hr : 0 < r := lt_min hr₁ hr₂
    have hr_sub₁ : ball z₀ r ⊆ ball z₀ r₁ := ball_subset_ball (min_le_left _ _)
    have hΨu (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) :=
      hr₂u z (ball_subset_ball (min_le_right _ _) hz)
    set A : ℂ → F →L[ℂ] F := fun z ↦ Ring.inverse (Ψ z)
    have hAu (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (A z) := (hΨu z hz).ringInverse
    have hAc : ContinuousOn A (ball z₀ r) :=
      NormedRing.continuousOn_inverse (hΨc.mono hr_sub₁) hΨu
    have hAw : MemWkpLoc p (ball z₀ r) 1 A :=
      (hΨw.mono hr_sub₁).ring_inverse (hΨc.mono hr_sub₁) hΨu
    set Φ : ℂ → F ≃L[ℂ] F := toContinuousLinearEquivOn (ball z₀ r) A hAu
    have hΦeq : EqOn (fun z ↦ (Φ z : F →L[ℂ] F)) A (ball z₀ r) :=
      fun z hz ↦ coe_toContinuousLinearEquivOn hAu hz
    refine ⟨r, hr, hr_sub₁.trans hr₁Ω, Φ, σ, hAc.congr hΦeq, hAw.congr hΦeq,
      hσd.mono hr_sub₁, fun x hx v ↦ ?_, fun x _ ↦ ?_, fun z hz ↦ ?_⟩
    · have hΨx : starConjCLM (Ψ x) = Ψ x := by
        simp [Ψ, Complex.conj_ofReal, starConjCLM_involutive, add_comm]
      have hAx : starConjCLM (A x) = A x := starConjCLM_ringInverse (hΨu x hx) hΨx
      have hv := congr($hAx (star v))
      rw [starConjCLM_apply_apply, star_star] at hv
      have hΦx : Φ x v = A x v := congr($(hΦeq hx) v)
      have hΦx' : Φ x (star v) = A x (star v) := congr($(hΦeq hx) (star v))
      rw [hΦx, hΦx', hv]
    · simp [σ, Complex.conj_ofReal, star_smul, add_comm]
    · have hco : Φ z (σ z) = A z (σ z) := congr($(hΦeq hz.1) (σ z))
      rw [hco]
      simp [A, ← hΨ_Rξ z (hr_sub₁ hz.1),
        ContinuousLinearMap.ringInverse_apply_apply (hΨu z hz.1),
        starSchwarzReflection_of_im_nonneg hz.2]

/-- **Boundary unique continuation from infinite-order vanishing** for `J = i`. On a
conjugation-invariant preconnected open set `Ω` (such as a disc centred on `ℝ`), if `ξ` is
continuous on `Ω ∩ {0 ≤ im}`, real on `Ω ∩ ℝ`, solves `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on
`Ω ∩ {0 ≤ im}` with the real boundary condition for `C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `p > 2`, and
satisfies `ξ = O((z - z₀)ⁿ)` within `{0 ≤ im}` for every `n` at a point `z₀ ∈ Ω ∩ {0 ≤ im}`
(interior or boundary), then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_forall_isBigO (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  set q : ℝ≥0∞ := min p 3
  have hq : 2 < q := lt_min hp (by norm_num)
  have hq1 : 1 < q := (by norm_num : (1 : ℝ≥0∞) < 2).trans hq
  have hq_top : q ≠ ⊤ := ((min_le_right p 3).trans_lt (by norm_num)).ne
  have hCq := hC.mono_exponent (min_le_left p 3)
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hq1 hq_top hΩ hCq hξc hξr
  have hR₀ := hR.eqOn_zero_of_forall_isBigO hq Ω.isOpen hΩc continuousOn_const (memWkpLoc_const _)
    (fun _ _ ↦ by ext v; simp [smul_smul]) (hCq.starSchwarzReflectionCoeff hΩ) hz₀.1
    fun n ↦ isBigO_starSchwarzReflection_sub_pow hz₀.2 (h₀ n)
  exact fun z hz ↦ by simpa [starSchwarzReflection_of_im_nonneg hz.2] using hR₀ hz.1

/-- **Boundary unique continuation from a relative neighbourhood** for `J = i`. On a
conjugation-invariant preconnected open set `Ω`, if `ξ` is continuous on `Ω ∩ {0 ≤ im}`, real on
`Ω ∩ ℝ`, solves `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition
for `C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `p > 2`, and vanishes in `𝓝[{0 ≤ im}] z₀` at a point
`z₀ ∈ Ω ∩ {0 ≤ im}` (interior or boundary), then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_eventually_eq_zero (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ᶠ z in 𝓝[{z | 0 ≤ z.im}] z₀, ξ z = 0) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
  h.eqOn_zero_of_forall_isBigO hp hΩ hΩc hC hξc hξr hz₀ fun _ ↦
    (EventuallyEq.isBigO h₀).trans (isBigO_zero _ _)

/-- **Boundary unique continuation from a nonempty relatively open subset** for `J = i`. On a
conjugation-invariant preconnected open set `Ω`, if `ξ` is continuous on `Ω ∩ {0 ≤ im}`, real on
`Ω ∩ ℝ`, solves `∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition
for `C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `p > 2`, and vanishes on `U ∩ {0 ≤ im}` for an open set `U`
meeting `{0 ≤ im}` with `U ∩ {0 ≤ im} ⊆ Ω`, then `ξ` vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_eqOn_zero (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    {U : Set ℂ} (hU : IsOpen U) (hUne : (U ∩ {z | 0 ≤ z.im}).Nonempty)
    (hUΩ : U ∩ {z | 0 ≤ z.im} ⊆ Ω) (h₀ : EqOn ξ 0 (U ∩ {z | 0 ≤ z.im})) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨z₁, hz₁⟩ := hUne
  refine h.eqOn_zero_of_eventually_eq_zero hp hΩ hΩc hC hξc hξr ⟨hUΩ hz₁, hz₁.2⟩ ?_
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz₁.1), self_mem_nhdsWithin] with z hzU hzH
  exact h₀ ⟨hzU, hzH⟩

/-- **Isolated interior and boundary zeros** for `J = i`. On a conjugation-invariant preconnected
open set `Ω`, if `ξ` is continuous on `Ω ∩ {0 ≤ im}`, real on `Ω ∩ ℝ`, solves
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition for
`C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `p > 2`, and is not identically zero on `Ω ∩ {0 ≤ im}`, then `ξ` is
nonzero in a punctured half-plane neighbourhood of every point `z₀ ∈ Ω ∩ {0 ≤ im}`, including
points on `ℝ`. -/
theorem eventually_ne_zero (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0)
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∀ᶠ z in 𝓝[{z | 0 ≤ z.im} \ {z₀}] z₀, ξ z ≠ 0 := by
  set q : ℝ≥0∞ := min p 3
  have hq : 2 < q := lt_min hp (by norm_num)
  have hq1 : 1 < q := (by norm_num : (1 : ℝ≥0∞) < 2).trans hq
  have hq_top : q ≠ ⊤ := ((min_le_right p 3).trans_lt (by norm_num)).ne
  have hCq := hC.mono_exponent (min_le_left p 3)
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hq1 hq_top hΩ hCq hξc hξr
  obtain ⟨w, hw, hξw⟩ := hne
  have hRne : ∃ z ∈ (Ω : Set ℂ), starSchwarzReflection ξ z ≠ 0 :=
    ⟨w, hw.1, by rwa [starSchwarzReflection_of_im_nonneg hw.2]⟩
  have hev := hR.eventually_ne_zero hq Ω.isOpen hΩc continuousOn_const (memWkpLoc_const _)
    (fun _ _ ↦ by ext v; simp [smul_smul]) (hCq.starSchwarzReflectionCoeff hΩ) hRne hz₀.1
  have hsub : {z : ℂ | 0 ≤ z.im} \ {z₀} ⊆ ({z₀}ᶜ : Set ℂ) := fun _ hz ↦ hz.2
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono z₀ hsub hev] with z hz hzR
  rwa [starSchwarzReflection_of_im_nonneg hz.1] at hzR

/-- Upgrades a power domination `(z - z₀) ^ k =O (z - z₀) ^ n` along `{0 ≤ im}` at `z₀` with
`0 ≤ z₀.im` to a full neighbourhood of `z₀`. -/
private theorem isBigO_sub_pow_nhds_of_im_nonneg {k n : ℕ} (hz₀ : 0 ≤ z₀.im)
    (h : (fun z ↦ (z - z₀) ^ k) =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    (fun z ↦ (z - z₀) ^ k) =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n := by
  have hR := isBigO_starSchwarzReflection_sub_pow (F := ℂ) hz₀ h
  rcases hz₀.lt_or_eq with hpos | hzero
  · have hnhds : 𝓝[{z : ℂ | 0 ≤ z.im}] z₀ = 𝓝 z₀ :=
      nhdsWithin_eq_nhds.2 (mem_of_superset
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos) fun _ hw ↦ hw.out.le)
    rwa [hnhds] at h
  · have hc : conj z₀ = z₀ := Complex.conj_eq_iff_im.2 hzero.symm
    refine (isBigO_of_le (𝓝 z₀) fun z ↦ ?_).trans hR
    by_cases hz : 0 ≤ z.im
    · simp [starSchwarzReflection_of_im_nonneg hz]
    · rw [starSchwarzReflection_of_im_neg (not_le.1 hz), Complex.star_def, Complex.norm_conj]
      have hsub : conj z - z₀ = conj (z - z₀) := by rw [map_sub, hc]
      rw [hsub, ← map_pow, Complex.norm_conj]

/-- **Positive finite interior and boundary zero orders** for `J = i`. On a conjugation-invariant
preconnected open set `Ω`, if `ξ` is continuous on `Ω ∩ {0 ≤ im}`, real on `Ω ∩ ℝ`, solves
`∂ₛξ + i ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real boundary condition for
`C ∈ Lᵖ_loc(Ω ∩ {0 ≤ im})`, `p > 2`, and is not identically zero on `Ω ∩ {0 ≤ im}`, then at every
zero `z₀ ∈ Ω ∩ {0 ≤ im}` of `ξ` (interior or boundary) there is a positive integer `m` with
`ξ =Θ[𝓝[{0 ≤ im}] z₀] (z - z₀) ^ m`, equal to the analytic order of `σ` in every local
factorization `ξ = Φ σ` on `{0 ≤ im}` near `z₀`. -/
theorem exists_analyticOrderAt_eq (hp : 2 < p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΩc : IsPreconnected (Ω : Set ℂ))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0)
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → F →L[ℝ] F) (σ : ℂ → F), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝[{z | 0 ≤ z.im}] z₀, ξ z = Φ z (σ z)) →
          analyticOrderAt σ z₀ = m := by
  set q : ℝ≥0∞ := min p 3
  have hq : 2 < q := lt_min hp (by norm_num)
  have hq1 : 1 < q := (by norm_num : (1 : ℝ≥0∞) < 2).trans hq
  have hq_top : q ≠ ⊤ := ((min_le_right p 3).trans_lt (by norm_num)).ne
  have hCq := hC.mono_exponent (min_le_left p 3)
  have hR := h.isWeakLinearCauchyRiemannOn_starSchwarzReflection hq1 hq_top hΩ hCq hξc hξr
  obtain ⟨w, hw, hξw⟩ := hne
  have hRne : ∃ z ∈ (Ω : Set ℂ), starSchwarzReflection ξ z ≠ 0 :=
    ⟨w, hw.1, by rwa [starSchwarzReflection_of_im_nonneg hw.2]⟩
  have hR₀ : starSchwarzReflection ξ z₀ = 0 := by
    rw [starSchwarzReflection_of_im_nonneg hz₀.2, hξ₀]
  obtain ⟨m, hm, hRΘ, -⟩ := hR.exists_analyticOrderAt_eq hq Ω.isOpen hΩc continuousOn_const
    (memWkpLoc_const _) (fun _ _ ↦ by ext v; simp [smul_smul]) (hCq.starSchwarzReflectionCoeff hΩ)
    hRne hz₀.1 hR₀
  have hξΘ : ξ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m :=
    (EventuallyEq.trans_isTheta
      (eventually_nhdsWithin_of_forall fun z hz ↦ (starSchwarzReflection_of_im_nonneg hz).symm)
      (hRΘ.mono nhdsWithin_le_nhds))
  refine ⟨m, hm, hξΘ, fun Φ σ hΦ hΦ₀ hσ hξσ ↦ ?_⟩
  have hΦσ : (fun z ↦ Φ z (σ z)) =Θ[𝓝[{z | 0 ≤ z.im}] z₀] σ :=
    (isTheta_clm_apply_of_isUnit hΦ hΦ₀).mono nhdsWithin_le_nhds
  have hσΘ : σ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m :=
    hΦσ.symm.trans ((EventuallyEq.isTheta hξσ).symm.trans hξΘ)
  have htop : analyticOrderAt σ z₀ ≠ ⊤ := by
    intro htop
    have hσ0 : σ =ᶠ[𝓝[{z | 0 ≤ z.im}] z₀] 0 :=
      nhdsWithin_le_nhds (analyticOrderAt_eq_top.1 htop)
    have hpow0 : (fun z ↦ (z - z₀) ^ m) =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ (m + 1) :=
      (hσΘ.symm.isBigO.trans_eventuallyEq hσ0).trans (isBigO_zero _ _)
    have hfull := isBigO_sub_pow_nhds_of_im_nonneg hz₀.2 hpow0
    have hle := ((analyticAt_id.sub analyticAt_const).pow m).analyticOrderAt_le_of_isBigO hfull
    have hpow_eq (k : ℕ) : (fun z : ℂ ↦ (z - z₀) ^ k) = (· - z₀) ^ k := rfl
    rw [hpow_eq, hpow_eq, analyticOrderAt_centeredMonomial, analyticOrderAt_centeredMonomial] at hle
    exact (Nat.not_succ_le_self m) (by exact_mod_cast hle)
  set n : ℕ := analyticOrderNatAt σ z₀
  have hn_eq : analyticOrderAt σ z₀ = n := (Nat.cast_analyticOrderNatAt htop).symm
  have hnΘ : σ =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n :=
    (hσ.analyticOrderAt_eq_natCast_iff_isTheta.1 hn_eq).mono nhdsWithin_le_nhds
  have hnm_half : (fun z ↦ (z - z₀) ^ n) =Θ[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ m :=
    hnΘ.symm.trans hσΘ
  have hnm : n = m := isTheta_pow_sub_pow_sub_iff.1
    ⟨isBigO_sub_pow_nhds_of_im_nonneg hz₀.2 hnm_half.1,
      isBigO_sub_pow_nhds_of_im_nonneg hz₀.2 hnm_half.2⟩
  rw [hn_eq, hnm]

end HasWeakConjWirtingerDerivRealBoundaryOn

/-! ### Converse in `W^{1,p}_loc`: transported complex structures -/

section Converse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- For any continuous `W^{1,p}_loc` family `Φ : ℂ → V ≃L[ℝ] V` on a set `U` into a complete
complex normed space `V`, the transported complex structure `J = Φ i Φ⁻¹` belongs to
`W^{1,p}_loc(U)`. -/
theorem memWkpLoc_transportedComplexStructure {p : ℝ≥0∞} {U : Set ℂ} {Φ : ℂ → V ≃L[ℝ] V}
    (hΦc : ContinuousOn (fun z ↦ (Φ z : V →L[ℝ] V)) U)
    (hΦw : MemWkpLoc p U 1 (fun z ↦ (Φ z : V →L[ℝ] V))) :
    MemWkpLoc p U 1 (transportedComplexStructure Φ) := by
  let ψ : (V →L[ℝ] V) → (V →L[ℝ] V) :=
    fun A ↦ A ∘L ((I • ContinuousLinearMap.id ℝ V) ∘L Ring.inverse A)
  have hinv : ContDiffOn ℝ 1 Ring.inverse {A : V →L[ℝ] V | IsUnit A} :=
    fun _ ⟨u, hu⟩ ↦ hu ▸ (contDiffAt_ringInverse ℝ u).contDiffWithinAt
  have hψ : ContDiffOn ℝ 1 ψ {A : V →L[ℝ] V | IsUnit A} :=
    contDiffOn_id.clm_comp (contDiffOn_const.clm_comp hinv)
  have hcomp : (fun z ↦ ψ (Φ z : V →L[ℝ] V)) = transportedComplexStructure Φ := by
    ext z v
    have hsymm : Ring.inverse (Φ z : V →L[ℝ] V) = ((Φ z).symm : V →L[ℝ] V) := by
      ext w
      simp
    simp [ψ, hsymm, transportedComplexStructure_apply]
  rw [← hcomp]
  exact hΦw.contDiffOn_comp hΦc Units.isOpen hψ fun z _ ↦ (Φ z).toUnit.isUnit

/-- For a continuous family `Φ : ℂ → V ≃L[ℝ] V` on `U` with `DΦ ∈ Lᵖ_loc(U)`, the weak absorbing
coefficient `z ↦ -((DΦ z 1 + J z ∘L DΦ z I) ∘L (Φ z).symm)` lies in `Lᵖ_loc(U)`. -/
theorem memLpLoc_neg_add_transportedComplexStructure_comp_symm {p : ℝ≥0∞} {U : Set ℂ}
    {Φ : ℂ → V ≃L[ℝ] V} {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hΦc : ContinuousOn (fun z ↦ (Φ z : V →L[ℝ] V)) U) (hDΦp : MemLpLoc p U DΦ) :
    MemLpLoc p U (fun z ↦
      -((DΦ z 1 + transportedComplexStructure Φ z ∘L DΦ z I) ∘L ((Φ z).symm : V →L[ℝ] V))) := by
  have hsymm : (fun z ↦ ((Φ z).symm : V →L[ℝ] V)) =
      fun z ↦ Ring.inverse (Φ z : V →L[ℝ] V) := by
    ext z v
    simp
  have hΨc : ContinuousOn (fun z ↦ ((Φ z).symm : V →L[ℝ] V)) U := by
    rw [hsymm]
    exact NormedRing.continuousOn_inverse hΦc fun z _ ↦ (Φ z).toUnit.isUnit
  have hJc : ContinuousOn (transportedComplexStructure Φ) U :=
    continuousOn_transportedComplexStructure hΦc
  have h1 : MemLpLoc p U (fun z ↦ DΦ z 1) :=
    hDΦp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) (1 : ℂ))
  have hI : MemLpLoc p U (fun z ↦ DΦ z I) :=
    hDΦp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  exact ((h1.add (hI.continuousOn_clm_comp hJc)).clm_comp_continuousOn hΨc).neg

/-- **Converse of the Sobolev similarity principle.** On an open set `Ω` and for any exponent `p`,
any continuous frame `Φ : ℂ → V ≃L[ℝ] V` into a complete complex normed space `V` with weak
derivative `DΦ ∈ Lᵖ_loc(Ω)` turns every holomorphic `σ : ℂ → V` on `Ω` into a weak solution
`ξ = Φ σ` of `∂ₛξ + J ∂ₜξ + C ξ = 0`, where `J = transportedComplexStructure Φ` and
`C(z) = -((DΦ(z)(1) + J(z) DΦ(z)(i)) Φ(z)⁻¹)`. -/
theorem isWeakLinearCauchyRiemannOn_transportedComplexStructure {p : ℝ≥0∞} {Ω : Opens ℂ}
    {Φ : ℂ → V ≃L[ℝ] V} {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hΦc : ContinuousOn (fun z ↦ (Φ z : V →L[ℝ] V)) Ω)
    (hDΦ : HasWeakFDerivOn volume Ω (fun z ↦ (Φ z : V →L[ℝ] V)) DΦ)
    (hDΦp : MemLpLoc p Ω DΦ) {σ : ℂ → V} (hσ : DifferentiableOn ℂ σ Ω) :
    IsWeakLinearCauchyRiemannOn p Ω (transportedComplexStructure Φ)
      (fun z ↦ -((DΦ z 1 + transportedComplexStructure Φ z ∘L DΦ z I) ∘L
        ((Φ z).symm : V →L[ℝ] V)))
      (fun z ↦ Φ z (σ z)) := by
  set F : ℂ → V →L[ℝ] V := fun z ↦ (Φ z : V →L[ℝ] V)
  have hFw : MemWkpLoc p Ω 1 F :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hΦc.memLpLoc, DΦ, hDΦ, memWkpLoc_zero_iff.2 hDΦp⟩
  let W : Set (ℂ × (V →L[ℝ] V)) := (Ω : Set ℂ) ×ˢ univ
  have hW : IsOpen W := Ω.isOpen.prod isOpen_univ
  let g : ℂ × (V →L[ℝ] V) → V := fun q ↦ q.2 (σ q.1)
  have hg : ContDiffOn ℝ 1 g W :=
    contDiff_snd.contDiffOn.clm_apply
      (((hσ.contDiffOn Ω.isOpen).restrict_scalars ℝ).comp contDiff_fst.contDiffOn fun _ hq ↦ hq.1)
  have hFW : ∀ z ∈ (Ω : Set ℂ), (z, F z) ∈ W := fun z hz ↦ ⟨hz, trivial⟩
  have hξw : MemWkpLoc p Ω 1 (fun z ↦ Φ z (σ z)) := hFw.contDiffOn_comp_graph hΦc hW hg hFW
  have hDξ := hDΦ.contDiffOn_comp_graph hΦc hW hg hFW
  refine isWeakCauchyRiemannOn_iff_forall_hasWeakFDerivOn.2
    ⟨hΦc.clm_apply hσ.continuousOn, hξw, fun D hD ↦ ?_⟩
  have hD' : HasWeakFDerivOn volume Ω (fun z ↦ Φ z (σ z)) D := by
    rwa [Opens.interior_coe] at hD
  have hae : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ),
      D z = (fderiv ℝ g (z, F z)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (DΦ z)) :=
    hD'.ae_eq hDξ
  rw [Ω.isOpen.interior_eq]
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet, hae] with z hz hDz
  have hdσ : DifferentiableAt ℂ σ z := hσ.differentiableAt (Ω.isOpen.mem_nhds hz)
  have hdg : HasFDerivAt g _ (z, F z) :=
    hasFDerivAt_snd.clm_apply (((hdσ.restrictScalars ℝ).hasFDerivAt).comp (z, F z) hasFDerivAt_fst)
  have hI : fderiv ℝ σ z I = I • fderiv ℝ σ z 1 := by
    rw [hdσ.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars', ← map_smul,
      smul_eq_mul, mul_one]
  rw [hDz, hdg.fderiv]
  simp only [F, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, add_apply, neg_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', hI,
    ContinuousLinearEquiv.coe_coe, map_add, transportedComplexStructure_apply_apply, smul_smul,
    I_mul_I, map_neg, neg_neg, ContinuousLinearEquiv.symm_apply_apply, neg_smul, one_smul]
  abel

end Converse

end TauCeti
