/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
public import TauCeti.Analysis.Complex.Wirtinger.Weak
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Complex.Pompeiu.Pointwise
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Leibniz
import TauCeti.Analysis.Complex.Wirtinger.Weyl
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.RankOne
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The similarity principle for linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, and `ξ : ℂ → V` a
continuous map on `Ω` solving the linear Cauchy–Riemann equation

`∂ₛξ + i ∂ₜξ + C ξ = 0`

on `Ω` distributionally, in the coordinate `z = s + i t`, for a field `C` of *real*-linear
endomorphisms of `V` which is locally `Lᵖ` for some `p > 2`. With `bar∂ = (∂ₛ + i ∂ₜ)/2` the
equation reads `bar∂ξ = ½ (-C ξ)`, in the sense of `TauCeti.HasWeakConjWirtingerDerivOn`; for a
weak solution of `TauCeti.IsWeakLinearCauchyRiemannOn` with the constant structure `i` this is
`TauCeti.IsWeakCauchyRiemannOn.hasWeakConjWirtingerDerivOn`. The **similarity principle** says
that near every point `z₀ ∈ Ω` the solution factors as `ξ = Φ σ` with `Φ` a continuous family of
invertible complex-linear maps and `σ` holomorphic
(`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`). In particular `ξ` has a similarity
factorization in the sense of `TauCeti.HasSimilarityFactorizationAt` at every point of `Ω`
(`TauCeti.hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn`), so it inherits the zero
structure of a holomorphic map: unique continuation from a zero of infinite order
(`TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_forall_isBigO`) and isolated zeros
(`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn`). Some
integrability of `C` is needed: `TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples` has a
smooth solution vanishing to infinite order, and nowhere else, whose coefficient is locally `Lᵖ`
for no `p ≥ 1`.

Classical solutions, of class `C¹` with a measurable, locally bounded coefficient, are the special
case `p = ∞` (`TauCeti.exists_similarity_of_contDiffOn` and its consequences).

A scalar function need not be given with its equation: a `C¹` function `f : ℂ → ℂ` with
`‖\bar∂ f‖ ≤ K ‖f‖` for a locally bounded `K` solves `\bar∂ f = a f` for the bounded coefficient
`a = \bar∂ f / f`, extended by `0` at the zeros of `f`, so its zeros are isolated as well unless it
vanishes identically (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_norm_conjWirtingerDeriv_le`).

The coefficient `C` need not commute with `i`, and a solution is in general not holomorphic.
The proof follows Carleman's argument as presented by McDuff and Salamon, after transporting the
equation along a complex-linear equivalence of `V` with a Euclidean space, whose inner product is
used only in the next step. First the real-linear term `C ξ` is absorbed into a complex-linear
coefficient depending on `ξ`: the rank-one map `D w = ‖ξ‖⁻² ⟪ξ, w⟫ C ξ`
(`TauCeti.rankOneDivNormSq`) is complex-linear, satisfies `D ξ = C ξ` and `‖D‖ ≤ ‖C‖`, and is
merely measurable, since it jumps at the zeros of `ξ`. Then the Cauchy integral equation
`Ψ = 1 + T (½ Ψ D)`, for the Cauchy transform `T` inverting `bar∂`, is solved on a small closed
disc by the contraction mapping theorem in the continuous maps on the disc. For `p > 2` the
Cauchy transform maps `Lᵖ` data on a disc to continuous maps, with a sup bound by the `Lᵖ` norm
(`TauCeti.norm_cauchyTransform_le`, `TauCeti.continuous_cauchyTransform_of_memLp`), and the `Lᵖ`
norm of `C` on a disc tends to `0` with its radius, which makes the map a contraction. Its
solution `Ψ` is continuous, close to `1` and hence invertible, and has weak derivative
`bar∂Ψ = ½ Ψ D`. The Leibniz rule for `bar∂` (`TauCeti.HasWeakConjWirtingerDerivOn.clm_apply`)
then gives `bar∂ (Ψ ξ) = Ψ (bar∂ξ + ½ D ξ) = Ψ (bar∂ξ + ½ C ξ) = 0` weakly, so `σ = Ψ ξ` is
holomorphic by Weyl's lemma, and `ξ = Ψ⁻¹ σ`.

## Main results

* `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`: the local factorization `ξ = Φ σ`
  on a disc, for continuous weak solutions with locally `Lᵖ` coefficient, `p > 2`.
* `TauCeti.hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn`: the factorization in the
  form consumed by `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_forall_isBigO`: unique continuation from a
  zero of infinite order.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn`: a solution that is
  not identically zero on a connected open set has isolated zeros.
* `TauCeti.exists_similarity_of_contDiffOn`, `TauCeti.hasSimilarityFactorizationAt_of_contDiffOn`,
  `TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO` and
  `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`: the same for classical solutions.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_norm_conjWirtingerDeriv_le`: isolated zeros of a
  scalar `C¹` function satisfying `‖\bar∂ f‖ ≤ K ‖f‖` that is not identically zero on a connected
  open set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The Cauchy integral equation -/

/-- The source term `½ Ψ D` of the Cauchy integral equation, for `Ψ` given on the closed disc
and extended by `0`. -/
private def cauchySource {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) (z : ℂ) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (extend Subtype.val Ψ 0 z).comp (D z)

private theorem cauchySource_of_mem {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {z : ℂ} (hz : z ∈ closedBall c r) :
    cauchySource D Ψ z = (2 : ℂ)⁻¹ • (Ψ ⟨z, hz⟩).comp (D z) := by
  rw [cauchySource, Subtype.val_injective.extend_apply Ψ 0 ⟨z, hz⟩]

private theorem cauchySource_of_notMem {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {z : ℂ} (hz : z ∉ closedBall c r) :
    cauchySource D Ψ z = 0 := by
  rw [cauchySource, extend_apply' _ _ _ fun ⟨w, hw⟩ ↦ hz (hw ▸ w.property)]
  simp

private theorem support_cauchySource_subset {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) : support (cauchySource D Ψ) ⊆ closedBall c r :=
  fun _ hz ↦ by_contra fun h ↦ hz (cauchySource_of_notMem D Ψ h)

private theorem cauchySource_sub {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) :
    cauchySource D (Ψ - Ψ') = cauchySource D Ψ - cauchySource D Ψ' := by
  ext1 z
  by_cases hz : z ∈ closedBall c r
  · simp only [Pi.sub_apply, cauchySource_of_mem D _ hz, ContinuousMap.sub_apply,
      ContinuousLinearMap.sub_comp, smul_sub]
  · simp [cauchySource_of_notMem D _ hz]

private theorem norm_cauchySource_le {c : ℂ} {r : ℝ} (D : ℂ → E →L[ℂ] E)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) (z : ℂ) :
    ‖cauchySource D Ψ z‖ ≤ 2⁻¹ * ‖Ψ‖ * ‖D z‖ := by
  by_cases hz : z ∈ closedBall c r
  · rw [cauchySource_of_mem D Ψ hz, norm_smul, norm_inv, Complex.norm_ofNat, mul_assoc]
    gcongr
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (Ψ.norm_coe_le_norm _) (norm_nonneg _))
  · rw [cauchySource_of_notMem D Ψ hz, norm_zero]
    positivity

private theorem aestronglyMeasurable_cauchySource {c : ℂ} {r : ℝ} {D : ℂ → E →L[ℂ] E}
    (hD : AEStronglyMeasurable D (volume.restrict (closedBall c r)))
    (Ψ : C(closedBall c r, E →L[ℂ] E)) : AEStronglyMeasurable (cauchySource D Ψ) volume := by
  have he : ContinuousOn (extend Subtype.val Ψ 0) (closedBall c r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert Ψ.continuous using 1
    ext1 z
    exact Subtype.val_injective.extend_apply Ψ 0 z
  have heq : cauchySource D Ψ = (closedBall c r).indicator (cauchySource D Ψ) :=
    (indicator_eq_self.2 (support_cauchySource_subset D Ψ)).symm
  rw [heq, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
  exact ((ContinuousLinearMap.compL ℂ E E E).aestronglyMeasurable_comp₂
    (he.aestronglyMeasurable measurableSet_closedBall) hD).const_smul (2 : ℂ)⁻¹

/-- The source is `Lᵖ` with `‖½ Ψ D‖_p ≤ ½ ‖Ψ‖ ‖D‖_p`, the `Lᵖ` norm of `D` taken on the disc. -/
private theorem memLp_cauchySource {c : ℂ} {r : ℝ} {p : ℝ≥0∞} {D : ℂ → E →L[ℂ] E}
    (hD : MemLp D p (volume.restrict (closedBall c r))) (Ψ : C(closedBall c r, E →L[ℂ] E)) :
    MemLp (cauchySource D Ψ) p volume ∧ (eLpNorm (cauchySource D Ψ) p volume).toReal ≤
      2⁻¹ * ‖Ψ‖ * (eLpNorm D p (volume.restrict (closedBall c r))).toReal := by
  have hm := aestronglyMeasurable_cauchySource hD.aestronglyMeasurable Ψ
  have hrestr := eLpNorm_restrict_eq_of_support_subset (p := p) hm
    (support_cauchySource_subset D Ψ)
  have hle : eLpNorm (cauchySource D Ψ) p volume ≤
      ENNReal.ofReal (2⁻¹ * ‖Ψ‖) * eLpNorm D p (volume.restrict (closedBall c r)) := by
    rw [← hrestr]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm.restrict
      (ae_of_all _ (norm_cauchySource_le D Ψ)) p
  have hfin : ENNReal.ofReal (2⁻¹ * ‖Ψ‖) * eLpNorm D p (volume.restrict (closedBall c r)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.eLpNorm_ne_top
  have hmem : MemLp (cauchySource D Ψ) p volume := memLp_iff.2 (hle.trans_lt hfin.lt_top)
  refine ⟨hmem, ?_⟩
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2⁻¹ * ‖Ψ‖)] using
    ENNReal.toReal_mono hfin hle

/-- On the disc, the Cauchy transform of the source `½ Ψ D` is at most `‖Ψ‖ / 4`, when `K` bounds
the Cauchy transform there by `K` times the `Lᵖ` norm and `K ‖D‖_p ≤ 1/2`. -/
private theorem norm_cauchyTransform_cauchySource_le {D : ℂ → E →L[ℂ] E} {c : ℂ} {r K : ℝ}
    {p : ℝ≥0∞} (hK : 0 ≤ K)
    (hT : ∀ f : ℂ → E →L[ℂ] E, MemLp f p volume → support f ⊆ closedBall c r →
      ∀ w ∈ closedBall c r, ‖cauchyTransform f w‖ ≤ K * (eLpNorm f p volume).toReal)
    (hD : MemLp D p (volume.restrict (closedBall c r)))
    (hKD : K * (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤ 2⁻¹)
    (Ψ : C(closedBall c r, E →L[ℂ] E)) {w : ℂ} (hw : w ∈ closedBall c r) :
    ‖cauchyTransform (cauchySource D Ψ) w‖ ≤ 4⁻¹ * ‖Ψ‖ :=
  calc ‖cauchyTransform (cauchySource D Ψ) w‖
      ≤ K * (eLpNorm (cauchySource D Ψ) p volume).toReal :=
        hT _ (memLp_cauchySource hD Ψ).1 (support_cauchySource_subset D Ψ) w hw
    _ ≤ K * (2⁻¹ * ‖Ψ‖ * (eLpNorm D p (volume.restrict (closedBall c r))).toReal) := by
        gcongr
        exact (memLp_cauchySource hD Ψ).2
    _ = 2⁻¹ * ‖Ψ‖ * (K * (eLpNorm D p (volume.restrict (closedBall c r))).toReal) := by ring
    _ ≤ 2⁻¹ * ‖Ψ‖ * 2⁻¹ := by gcongr
    _ = 4⁻¹ * ‖Ψ‖ := by ring

/-- The Cauchy transform of the source `½ Ψ D` is linear in `Ψ`. -/
private theorem cauchyTransform_cauchySource_sub {D : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    {p q : ℝ≥0∞} [p.HolderConjugate q] (hq : q < 2)
    (hD : MemLp D p (volume.restrict (closedBall c r))) (Ψ Ψ' : C(closedBall c r, E →L[ℂ] E)) :
    cauchyTransform (cauchySource D Ψ) - cauchyTransform (cauchySource D Ψ') =
      cauchyTransform (cauchySource D (Ψ - Ψ')) := by
  rw [cauchySource_sub, cauchyTransform_sub_of_memLp hq (memLp_cauchySource hD Ψ).1
    (support_cauchySource_subset D Ψ) (memLp_cauchySource hD Ψ').1
    (support_cauchySource_subset D Ψ')]

/-- **The Cauchy integral equation of the similarity principle.** Let `p` be conjugate to some
`q < 2`, so `p > 2`, and let `K` bound the Cauchy transform on the closed disc of radius `r`
about `c` of data supported in it, by `K` times their `Lᵖ` norm. If a measurable field `D` of
complex-linear maps has `K ‖D‖_p ≤ 1/2` on the disc, there is `g ∈ Lᵖ`, vanishing off the disc,
whose Cauchy transform is continuous and satisfies `g = ½ (1 + T g) D` on the disc, with
`‖T g‖ < 1` there. So `Ψ = 1 + T g` is a continuous family of invertible maps on the disc solving
`bar∂Ψ = ½ Ψ D`. It is the fixed point of the contraction `Ψ ↦ 1 + T (½ Ψ D)` of the continuous
maps on the disc. -/
private theorem exists_cauchyTransform_eq [FiniteDimensional ℂ E] {D : ℂ → E →L[ℂ] E} {c : ℂ}
    {r K : ℝ} {p q : ℝ≥0∞} [p.HolderConjugate q] (hq : q < 2) (hK : 0 ≤ K)
    (hT : ∀ f : ℂ → E →L[ℂ] E, MemLp f p volume → support f ⊆ closedBall c r →
      ∀ w ∈ closedBall c r, ‖cauchyTransform f w‖ ≤ K * (eLpNorm f p volume).toReal)
    (hD : MemLp D p (volume.restrict (closedBall c r)))
    (hKD : K * (eLpNorm D p (volume.restrict (closedBall c r))).toReal ≤ 2⁻¹) :
    ∃ g : ℂ → E →L[ℂ] E, MemLp g p volume ∧ support g ⊆ closedBall c r ∧
      Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall c r, g z = (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (D z)) ∧
      ∀ z ∈ closedBall c r, ‖cauchyTransform g z‖ < 1 := by
  have := FiniteDimensional.completeSpace ℂ E
  have hTΨ := norm_cauchyTransform_cauchySource_le hK hT hD hKD
  have hcont (Ψ : C(closedBall c r, E →L[ℂ] E)) :
      Continuous (cauchyTransform (cauchySource D Ψ)) :=
    continuous_cauchyTransform_of_memLp hq (memLp_cauchySource hD Ψ).1
      (support_cauchySource_subset D Ψ)
  let op (Ψ : C(closedBall c r, E →L[ℂ] E)) : C(closedBall c r, E →L[ℂ] E) :=
    ⟨fun w ↦ 1 + cauchyTransform (cauchySource D Ψ) w,
      (continuous_const.add (hcont Ψ)).comp continuous_subtypeVal⟩
  have hop : ContractingWith (4⁻¹ : ℝ).toNNReal op := by
    refine ⟨by rw [Real.toNNReal_lt_one]; norm_num, LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_⟩
    rw [Real.coe_toNNReal _ (by norm_num)]
    refine (ContinuousMap.dist_le (by positivity)).2 fun w ↦ ?_
    simp only [op, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub, ← Pi.sub_apply,
      cauchyTransform_cauchySource_sub hq hD]
    rw [dist_eq_norm Ψ Ψ']
    exact hTΨ (Ψ - Ψ') w.property
  set Ψ₀ := ContractingWith.fixedPoint op hop
  set g := cauchySource D Ψ₀ with hg
  have hfix : op Ψ₀ = Ψ₀ := ContractingWith.fixedPoint_isFixedPt hop
  have hΨ₀ (z : ℂ) (hz : z ∈ closedBall c r) : Ψ₀ ⟨z, hz⟩ = 1 + cauchyTransform g z := by
    rw [← hfix]
    simp only [op, ContinuousMap.coe_mk, hg]
  have hnorm : ‖Ψ₀‖ ≤ 4 / 3 := by
    have h1 : ‖Ψ₀‖ ≤ 1 + 4⁻¹ * ‖Ψ₀‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
      rw [hΨ₀ w w.property]
      exact (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hTΨ Ψ₀ w.property))
    linarith
  refine ⟨g, (memLp_cauchySource hD Ψ₀).1, support_cauchySource_subset D Ψ₀, hcont Ψ₀,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hg, cauchySource_of_mem D Ψ₀ hz, hΨ₀ z hz]
  · calc ‖cauchyTransform g z‖ ≤ 4⁻¹ * ‖Ψ₀‖ := hTΨ Ψ₀ hz
      _ ≤ 4⁻¹ * (4 / 3) := by gcongr
      _ < 1 := by norm_num

/-! ### The similarity principle -/

/-- **The Cauchy integral equation near a point.** For a finite exponent `p > 2`, a locally `Lᵖ`
coefficient `C` and a continuous `ξ` on `Ω`, every point `z₀ ∈ Ω` is the centre of a closed disc
in `Ω` carrying a solution `g ∈ Lᵖ`, vanishing off the disc, of `g = ½ (1 + T g) D` with `T g`
continuous and of norm less than `1` on the disc, where `D = ‖ξ‖⁻² ⟪ξ, ·⟫ C ξ` agrees with `C`
along `ξ`. -/
private theorem exists_closedBall_cauchyTransform_eq [FiniteDimensional ℂ E] {Ω : Opens ℂ}
    {ξ : ℂ → E} {C : ℂ → E →L[ℝ] E} {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hC : MemLpLoc p Ω C) (hξ : ContinuousOn ξ Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ closedBall z₀ r ⊆ Ω ∧ ∃ g : ℂ → E →L[ℂ] E, MemLp g p volume ∧
      support g ⊆ closedBall z₀ r ∧ Continuous (cauchyTransform g) ∧
      (∀ z ∈ closedBall z₀ r, g z =
        (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (rankOneDivNormSq ℂ (C z (ξ z)) (ξ z))) ∧
      ∀ z ∈ closedBall z₀ r, ‖cauchyTransform g z‖ < 1 := by
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  have hq : p.conjExponent < 2 := ENNReal.HolderConjugate.lt_two hp
  -- a closed disc in `Ω`, with the Cauchy transform bound of its double
  obtain ⟨R, hR, hRΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hz₀)
  set K := Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (R + R)) p.conjExponent volume).toReal
  have hK : 0 ≤ K := by positivity
  -- a smaller disc on which `C` has `Lᵖ` norm at most `1 / (2 (K + 1))`
  have hCR : MemLp ((closedBall z₀ R).indicator C) p volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet).2
      (memLpLoc_iff.1 hC _ hRΩ (isCompact_closedBall _ _))
  obtain ⟨r, hCr, hr, hrR⟩ := ((((tendsto_eLpNorm_restrict_closedBall hp_top hCR
    z₀).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < 2⁻¹ / (K + 1) by
      positivity)))).filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hR)).exists
  have hsub : closedBall z₀ r ⊆ closedBall z₀ R := closedBall_subset_closedBall hrR.le
  have hsubΩ : closedBall z₀ r ⊆ Ω := hsub.trans hRΩ
  -- on the smaller disc the cut-off coefficient is `C` itself
  rw [eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_closedBall).2
    (ae_of_all _ fun z hz ↦ indicator_of_mem (hsub hz) C))] at hCr
  -- absorb the real-linear coefficient into a complex-linear one, of no larger norm
  have hCr' : MemLp C p (volume.restrict (closedBall z₀ r)) :=
    memLpLoc_iff.1 hC _ hsubΩ (isCompact_closedBall _ _)
  have hξm : AEStronglyMeasurable ξ (volume.restrict (closedBall z₀ r)) :=
    (hξ.mono hsubΩ).aestronglyMeasurable measurableSet_closedBall
  have hKD : K * (eLpNorm (fun z ↦ rankOneDivNormSq ℂ (C z (ξ z)) (ξ z)) p
      (volume.restrict (closedBall z₀ r))).toReal ≤ 2⁻¹ := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((TauCeti.MeasureTheory.eLpNorm_rankOneDivNormSq_apply_le (𝕜 := ℂ)
        hCr'.aestronglyMeasurable hξm p).trans hCr.le)
    calc _ ≤ K * (2⁻¹ / (K + 1)) := by gcongr
      _ ≤ 2⁻¹ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  -- solve the Cauchy integral equation on the smaller disc
  have hT (f : ℂ → E →L[ℂ] E) (hf : MemLp f p volume) (hfs : support f ⊆ closedBall z₀ r)
      (w : ℂ) (hw : w ∈ closedBall z₀ r) :
      ‖cauchyTransform f w‖ ≤ K * (eLpNorm f p volume).toReal :=
    norm_cauchyTransform_le hq hf (hfs.trans hsub) (hsub hw)
  exact ⟨r, hr, hsubΩ,
    exists_cauchyTransform_eq hq hK hT (hCr'.rankOneDivNormSq_apply (𝕜 := ℂ) hξm) hKD⟩

/-- The value of `bar∂ (Ψ ξ)` vanishes where `bar∂ξ = ½ (-C ξ)` and `bar∂Ψ = ½ Ψ D`, for
`Ψ = 1 + T` and `D ξ = C ξ`. -/
private theorem add_add_eq_zero {C : E →L[ℝ] E} {T G D : E →L[ℂ] E} {x : E}
    (hG : G = (2 : ℂ)⁻¹ • (1 + T).comp D) (hD : D x = C x) :
    (2 : ℂ)⁻¹ • -C x + (G x + T ((2 : ℂ)⁻¹ • -C x)) = 0 := by
  rw [hG]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, hD, add_apply, one_apply_eq_self,
    map_smul, map_neg]
  module

/-- **The integrating factor.** Let `ξ` be continuous on `Ω` with `bar∂ξ = ½ (-C ξ)`, for `C`
locally `Lᵖ`, `p > 2`, and let `g ∈ Lᵖ`, vanishing off a closed disc in `Ω`, solve
`g = ½ (1 + T g) D` on the disc, with `T g` continuous and `D ξ = C ξ`. Then `(1 + T g) ξ` is
holomorphic on the open disc: by the Leibniz rule its `bar∂` is
`(1 + T g) (bar∂ξ) + g ξ = (1 + T g) (½ (-C ξ) + ½ D ξ) = 0`. -/
private theorem differentiableOn_one_add_cauchyTransform_apply [FiniteDimensional ℂ E]
    {Ω : Opens ℂ} {ξ : ℂ → E} {C : ℂ → E →L[ℝ] E} {p : ℝ≥0∞} (hp : 2 < p)
    (hC : MemLpLoc p Ω C) (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z))) {z₀ : ℂ}
    {r : ℝ} (hsubΩ : closedBall z₀ r ⊆ Ω) {g : ℂ → E →L[ℂ] E} (hg : MemLp g p volume)
    (hgs : support g ⊆ closedBall z₀ r) (hTg : Continuous (cauchyTransform g))
    (hgeq : ∀ z ∈ closedBall z₀ r, g z =
      (2 : ℂ)⁻¹ • (1 + cauchyTransform g z).comp (rankOneDivNormSq ℂ (C z (ξ z)) (ξ z))) :
    DifferentiableOn ℂ (fun z ↦ (1 + cauchyTransform g z) (ξ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  have hp1 : 1 < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  let B : Opens ℂ := ⟨ball z₀ r, isOpen_ball⟩
  have hBΩ : (B : Set ℂ) ⊆ Ω := ball_subset_closedBall.trans hsubΩ
  have hgi : Integrable g := by
    have : IsFiniteMeasure (volume.restrict (closedBall z₀ r)) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have hgo : IntegrableOn g (closedBall z₀ r) volume :=
      (hg.restrict (closedBall z₀ r)).integrable hp1.le
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (f := g) hgo fun z hz ↦ ?_
    by_contra h
    exact hz (hgs h)
  have hh : MemLpLoc p B (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z)) := by
    simpa using ((hC.mono_set hBΩ).clm_apply_continuousOn (hξ.mono hBΩ)).clm_comp
      ((-(2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ E : E →L[ℂ] E).restrictScalars ℝ)
  -- `bar∂ (ξ + T g ξ) = ½ (-C ξ) + g ξ + T g (½ (-C ξ))`, which vanishes on the disc
  have hw := (heq.mono hBΩ).add ((hasWeakConjWirtingerDerivOn_cauchyTransform hgi B).clm_apply
    hp1 (heq.mono hBΩ) hTg.continuousOn (hξ.mono hBΩ) (hg.restrict _).memLpLoc hh)
  have hw0 := hw.congr_ae_deriv (k := 0) ((ae_restrict_iff' B.isOpen.measurableSet).2
    (ae_of_all _ fun z hz ↦ add_add_eq_zero (hgeq z (ball_subset_closedBall hz))
      ((C z).rankOneDivNormSq_apply_map (ξ z))))
  have hσ : (ξ + fun z ↦ cauchyTransform g z (ξ z)) = fun z ↦ (1 + cauchyTransform g z) (ξ z) := by
    ext1 z
    simp
  rw [hσ] at hw0
  exact hw0.differentiableOn ((continuous_const.add hTg).continuousOn.clm_apply (hξ.mono hBΩ))

/-- **The similarity principle** on a complex inner product space, for a continuous weak solution
with locally `Lᵖ` coefficient, `p > 2`: the factorization on a disc. -/
private theorem exists_similarity_of_innerProductSpace [FiniteDimensional ℂ E] {Ω : Opens ℂ}
    {ξ : ℂ → E} {C : ℂ → E →L[ℝ] E} {p : ℝ≥0∞} (hp : 2 < p) (hC : MemLpLoc p Ω C)
    (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z))) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ E
  -- the coefficient is also locally `Lᵖ` for the finite exponent `min p 3 ∈ (2, p]`
  have hp₀ : 2 < min p 3 := lt_min hp (by norm_num)
  have hp₀_top : min p 3 ≠ ⊤ := ((min_le_right _ _).trans_lt (by norm_num : (3 : ℝ≥0∞) < ⊤)).ne
  have hC₀ : MemLpLoc (min p 3) Ω C := hC.mono_exponent (min_le_left _ _)
  obtain ⟨r, hr, hsubΩ, g, hg, hgs, hTg, hgeq, hTg1⟩ :=
    exists_closedBall_cauchyTransform_eq hp₀ hp₀_top hC₀ hξ hz₀
  -- `Ψ = 1 + T g` is invertible on the disc, and `ξ = Ψ⁻¹ (Ψ ξ)`
  set Ψ : ℂ → E →L[ℂ] E := fun z ↦ 1 + cauchyTransform g z with hΨ
  have hunit (z : ℂ) (hz : z ∈ ball z₀ r) : IsUnit (Ψ z) := by
    by_contra h
    refine nonunits.subset_compl_ball h ?_
    rw [mem_ball_iff_norm, hΨ, add_sub_cancel_left]
    exact hTg1 z (ball_subset_closedBall hz)
  refine ⟨r, hr, ball_subset_closedBall.trans hsubΩ, fun z ↦ Ring.inverse (Ψ z),
    fun z ↦ Ψ z (ξ z), fun z hz ↦ ?_, fun z hz ↦ ?_,
    differentiableOn_one_add_cauchyTransform_apply hp₀ hC₀ hξ heq hsubΩ hg hgs hTg hgeq,
    fun z hz ↦ ?_⟩
  · have hc := NormedRing.inverse_continuousAt (hunit z hz).unit
    rw [IsUnit.unit_spec] at hc
    exact (hc.comp (continuous_const.add hTg).continuousAt).continuousWithinAt
  · beta_reduce
    rw [← (hunit z hz).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  · beta_reduce
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ (hunit z hz), one_apply_eq_self]

/-! ### Weak solutions with `Lᵖ` coefficients -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Opens ℂ} {ξ : ℂ → V} {C : ℂ → V →L[ℝ] V} {p : ℝ≥0∞}

/-- The disc form of the similarity principle, with complex-linear `Φ`, gives a similarity
factorization at the centre. -/
private theorem hasSimilarityFactorizationAt_of_exists_similarity {s : Set ℂ} {z₀ : ℂ}
    (h : ∃ r, 0 < r ∧ ball z₀ r ⊆ s ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r)) :
    HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ := h
  obtain ⟨u, hu⟩ := hΦu z₀ (mem_ball_self hr)
  -- restricting the scalars of the equivalence `Φ z₀` to `ℝ` keeps it invertible
  refine .of_eqOn_ball hr (Φ := fun z ↦ (Φ z).restrictScalars ℝ)
    ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℂ).continuous.comp_continuousOn hΦ)
    (hu ▸ ⟨((ContinuousLinearEquiv.unitsEquiv ℂ V u).restrictScalars ℝ).toUnit, rfl⟩) hσ hξσ

/-- **The similarity principle** (Carleman) for weak solutions with `Lᵖ` coefficients. Let `ξ` be
continuous on an open set `Ω ⊆ ℂ` and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` distributionally on `Ω`, that
is `bar∂ξ = ½ (-C ξ)`, for a field `C` of real-linear endomorphisms of a finite-dimensional
complex normed space `V` which is locally `Lᵖ` on `Ω` for some `p > 2`. Then every point `z₀ ∈ Ω`
is the centre of a disc in `Ω` on which `ξ = Φ σ`, with `Φ` a continuous family of invertible
complex-linear maps and `σ` holomorphic. -/
theorem exists_similarity_of_hasWeakConjWirtingerDerivOn (hp : 2 < p) (hC : MemLpLoc p Ω C)
    (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z))) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  -- transport the equation to a Euclidean space, whose inner product absorbs `C`
  let e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let eR : V →L[ℝ] E := (e : V →L[ℂ] E).restrictScalars ℝ
  let eR' : E →L[ℝ] V := (e.symm : E →L[ℂ] V).restrictScalars ℝ
  -- conjugation `A ↦ e A e⁻¹` of the coefficients
  let L : (V →L[ℝ] V) →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E V E eR).comp ((ContinuousLinearMap.compL ℝ E V V).flip eR')
  have hL (z : ℂ) : L (C z) (e (ξ z)) = e (C z (ξ z)) := by
    simp [L, eR, eR']
  have heq' : HasWeakConjWirtingerDerivOn volume Ω (fun z ↦ e (ξ z))
      (fun z ↦ (2 : ℂ)⁻¹ • -L (C z) (e (ξ z))) := by
    simpa only [hL, map_smul, map_neg, ContinuousLinearEquiv.coe_coe] using
      heq.clm_comp e.toContinuousLinearMap
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ := exists_similarity_of_innerProductSpace hp
    (hC.clm_comp L) (e.continuous.comp_continuousOn hξ) heq' hz₀
  refine ⟨r, hr, hrΩ, fun z ↦ e.symm.conjContinuousAlgEquiv (Φ z), fun z ↦ e.symm (σ z),
    ?_, fun z hz ↦ (hΦu z hz).map _,
    ((e.symm : _ →L[ℂ] V).differentiable.comp_differentiableOn hσ).congr fun _ _ ↦ rfl,
    fun z hz ↦ ?_⟩
  · simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
    exact continuousOn_const.clm_comp (hΦ.clm_comp continuousOn_const)
  · have h := congrArg e.symm (hξσ hz)
    rw [Function.comp_apply, e.symm_apply_apply] at h
    simp [h]

/-- A continuous weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on an open set `Ω`, with locally `Lᵖ`
real-linear coefficient `C` for some `p > 2`, has a similarity factorization at every point of
`Ω`. -/
theorem hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn (hp : 2 < p)
    (hC : MemLpLoc p Ω C) (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z))) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ :=
  hasSimilarityFactorizationAt_of_exists_similarity
    (exists_similarity_of_hasWeakConjWirtingerDerivOn hp hC hξ heq hz₀)

/-- **Unique continuation** for weak solutions with `Lᵖ` coefficients, `p > 2`. On a connected
open set `Ω`, a continuous weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` that vanishes on a nonempty
open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_eqOn_zero (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C) (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z)))
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero Ω.isOpen hΩc hξ
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn hp hC hξ heq hz)
    hU hUne hUΩ h₀

/-- **Unique continuation from a zero of infinite order** for weak solutions with `Lᵖ`
coefficients, `p > 2`. On a connected open set `Ω`, a continuous weak solution of
`∂ₛξ + i ∂ₜξ + C ξ = 0` that vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_forall_isBigO (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C) (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z))) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO Ω.isOpen hΩc hξ
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn hp hC hξ heq hz)
    hz₀ h₀

/-- **Isolated zeros** of weak solutions with `Lᵖ` coefficients, `p > 2`. On a connected open set
`Ω`, the zeros of a continuous weak solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` that is not identically
zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hC : MemLpLoc p Ω C) (hξ : ContinuousOn ξ Ω)
    (heq : HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z)))
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin (Ω : Set ℂ) := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt Ω.isOpen hΩc hξ
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn hp hC hξ heq hz) hne

/-! ### Classical solutions -/

section Classical

variable {Ω : Set ℂ}

/-- **The similarity principle** (Carleman) for classical solutions. Let `ξ` be of class `C¹` on
an open set `Ω ⊆ ℂ` and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`, for a measurable, locally bounded
field `C` of real-linear endomorphisms of a finite-dimensional complex normed space `V` (for
instance a continuous one). Then every point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which
`ξ = Φ σ`, with `Φ` a continuous family of invertible complex-linear maps and `σ` holomorphic. -/
theorem exists_similarity_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  -- a disc in `Ω` on which `C` is bounded, hence essentially bounded
  obtain ⟨M, hM⟩ := hCb z₀ hz₀
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.mem_nhds_iff.1 (inter_mem hM (hΩ.mem_nhds hz₀))
  let B : Opens ℂ := ⟨ball z₀ ρ, isOpen_ball⟩
  have hBΩ : (B : Set ℂ) ⊆ Ω := fun z hz ↦ (hρΩ hz).2
  have hC : MemLpLoc ⊤ B C := memLpLoc_iff.2 fun K hKB hK ↦
    memLp_top_of_bound ((hCm.mono_measure (Measure.restrict_mono (hKB.trans hBΩ) le_rfl))) M
      ((ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ fun z hz ↦ (hρΩ (hKB hz)).1))
  -- the classical equation is the weak one
  have heqB : HasWeakConjWirtingerDerivOn volume B ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z)) :=
    (hasWeakConjWirtingerDerivOn_of_contDiffOn (hξ.mono hBΩ)).congr_ae_deriv
      ((ae_restrict_iff' B.isOpen.measurableSet).2 (ae_of_all _ fun z hz ↦ by
        beta_reduce
        rw [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, ← neg_eq_of_add_eq_zero_left
          (heq z (hBΩ hz))]))
  obtain ⟨r, hr, hrB, h⟩ := exists_similarity_of_hasWeakConjWirtingerDerivOn (by simp) hC
    (hξ.continuousOn.mono hBΩ) heqB (mem_ball_self hρ)
  exact ⟨r, hr, hrB.trans hBΩ, h⟩

/-- A `C¹` solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on an open set `Ω`, with measurable, locally
bounded real-linear coefficient `C`, has a similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ :=
  hasSimilarityFactorizationAt_of_exists_similarity
    (exists_similarity_of_contDiffOn hΩ hξ hCm hCb heq hz₀)

/-- **Unique continuation** for classical solutions. On a connected open set `Ω`, a `C¹` solution
of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with measurable, locally bounded real-linear coefficient `C`, that
vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_forall_isBigO (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz) hz₀ h₀

/-- **Isolated zeros** of classical solutions. On a connected open set `Ω`, the zeros of a `C¹`
solution of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with measurable, locally bounded real-linear coefficient
`C`, that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz) hne

/-- **Isolated zeros under a differential inequality.** On a connected open set `Ω ⊆ ℂ`, a
function `f : ℂ → ℂ` of class `C¹` with `‖\bar∂ f(z)‖ ≤ K(z) ‖f(z)‖` on `Ω`, for a locally bounded
`K`, that is not identically zero on `Ω` has isolated zeros. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_norm_conjWirtingerDeriv_le (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f Ω) {K : ℂ → ℝ}
    (hK : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, K w ≤ M)
    (hfK : ∀ z ∈ Ω, ‖conjWirtingerDeriv f z‖ ≤ K z * ‖f z‖) (hne : ∃ z ∈ Ω, f z ≠ 0) :
    {z | f z ≠ 0} ∈ codiscreteWithin Ω := by
  -- `f` solves `∂ₛ f + i ∂ₜ f + a f = 0` with `a = -2 \bar∂ f(1) / f`, which is `0` where `f`
  -- vanishes and bounded by `2 K` elsewhere.
  set a : ℂ → ℂ := fun z ↦ -(2 * conjWirtingerDeriv f z 1 / f z) with ha
  have hone : ∀ z, ‖conjWirtingerDeriv f z 1‖ ≤ ‖conjWirtingerDeriv f z‖ := fun z ↦ by
    simpa using (conjWirtingerDeriv f z).le_opNorm 1
  have ha_le : ∀ z ∈ Ω, ‖a z‖ ≤ 2 * max (K z) 0 := by
    intro z hz
    by_cases h0 : f z = 0
    · simp only [ha, h0, div_zero, neg_zero, norm_zero]
      positivity
    · rw [ha, norm_neg, norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.2 h0), Complex.norm_two,
        mul_assoc]
      gcongr
      exact (hone z).trans ((hfK z hz).trans (by gcongr; exact le_max_left _ _))
  have hCm : AEStronglyMeasurable (fun z ↦ a z • ContinuousLinearMap.id ℝ ℂ)
      (volume.restrict Ω) := by
    have h1 : Measurable fun z ↦ conjWirtingerDeriv f z 1 := by
      simp_rw [conjWirtingerDeriv_apply]
      exact ((measurable_fderiv_apply_const ℝ f 1).add
        ((measurable_fderiv_apply_const ℝ f (I • (1 : ℂ))).const_smul I)).const_smul (2 : ℂ)⁻¹
    have h2 : AEMeasurable f (volume.restrict Ω) :=
      (hf.continuousOn.aestronglyMeasurable hΩ.measurableSet).aemeasurable
    exact (((h1.aemeasurable.const_mul 2).div h2).neg.aestronglyMeasurable).smul_const _
  have hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖a w • ContinuousLinearMap.id ℝ ℂ‖ ≤ M := by
    intro z hz
    obtain ⟨M, hM⟩ := hK z hz
    refine ⟨2 * max M 0, ?_⟩
    filter_upwards [hΩ.mem_nhds hz, hM] with w hw hwM
    calc ‖a w • ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖a w‖ :=
          ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ by simp
      _ ≤ 2 * max M 0 := (ha_le w hw).trans (by gcongr)
  refine setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn hΩ hΩc hf hCm hCb (fun z hz ↦ ?_) hne
  have hfz : (a z • ContinuousLinearMap.id ℝ ℂ) (f z) = a z * f z := by simp
  rw [fderiv_apply_one_add_I_smul_fderiv_apply_I, hfz, smul_eq_mul, ha]
  by_cases h0 : f z = 0
  · have h := hfK z hz
    rw [h0, norm_zero, mul_zero] at h
    rw [norm_le_zero_iff.1 ((hone z).trans h), h0]
    simp
  · field_simp
    ring

end Classical

end TauCeti
