/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Haar
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Haar
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Membership and non-membership examples for Euclidean local Sobolev classes

This file tests `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` across finite-dimensional real normed
spaces, arbitrary Borel additive Haar measures, and infinite-dimensional Banach targets:

* The identity map `x ↦ x` belongs to every `MemWkpLoc p U k` (`TauCeti.memWkpLoc_id`), yet fails
  global `Lᵖ` membership for every `0 < p` on any nontrivial space (`TauCeti.not_memLp_id`).
* The norm `x ↦ ‖x‖` belongs to `MemWkpLoc p U 1` on any finite-dimensional real normed space
  (`TauCeti.memWkpLoc_one_norm`), including non-inner-product models such as `ℝ × ℝ` with the
  supremum norm, where the inner-product gradient formula fails (`TauCeti.fderiv_norm_prod_apply`).
* Near the origin of a nontrivial finite-dimensional space `E`, `x ↦ ‖x‖⁻¹` is locally `Lᵖ`
  iff `p < dim E` (`TauCeti.memLpLoc_norm_inv_iff`), and on a real inner product space of
  dimension at least two the unit radial map `x ↦ ‖x‖⁻¹ • x` lies in `MemWkpLoc p U 1` near the
  origin iff `p < dim E` (`TauCeti.memWkpLoc_one_unitRadial_iff`).
* The indicator of a half-space `{x | 0 < ℓ x}` for a nonzero continuous linear functional `ℓ`
  is locally `Lᵖ` everywhere (`TauCeti.memLpLoc_indicator_pos`) but admits no weak derivative on
  any open set meeting `ker ℓ` (`TauCeti.not_hasWeakFDerivOn_indicator_pos`,
  `TauCeti.not_memWkpLoc_indicator_pos`).
* Scaling `volume` by a positive constant (`TauCeti.memWkpLoc_two_smul_volume_iff`) or switching
  between `ℝ × ℝ` (supremum norm, product volume) and `EuclideanSpace ℝ (Fin 2)` via a
  continuous linear equivalence (`TauCeti.memWkpLoc_prod_iff_euclideanSpace`) preserves local
  Sobolev classes.
* For infinite-dimensional Banach targets such as `lp (fun _ : ℕ => ℝ) 2`, scalar local Sobolev
  functions produce vector-valued ones (`TauCeti.memWkpLoc_one_norm_smul_lp`). On the
  non-separable Hilbert space `lp (fun _ : ℝ => ℝ) 2`, however, the bounded map
  `x ↦ lp.single 2 x 1` composes with every continuous linear functional to a function equal
  almost everywhere to zero—hence in every `MemWkpLoc p U k`
  (`TauCeti.weak_memWkpLoc_lpSingle`)—yet fails Bochner strong measurability and therefore belongs
  to no `MemLpLoc p U` on any set with nonempty interior (`TauCeti.not_memLpLoc_lpSingle`).

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2.
-/

public noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Topology Distributions RealInnerProductSpace ENNReal

namespace TauCeti

/-! ### The identity and the norm on general normed spaces -/

section IdentityAndNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The identity of any finite-dimensional real normed space lies in every local Sobolev class on
every set, although for `0 < p` it is not globally `Lᵖ` when `E` is nontrivial
(`TauCeti.not_memLp_id`). -/
theorem memWkpLoc_id (p : ENNReal) (U : Set E) (k : ℕ) : MemWkpLoc p U k (fun x : E => x) :=
  (contDiff_id.contDiffOn : ContDiffOn ℝ k id ((⊤ : Opens E) : Set E)).memWkpLoc (subset_univ U)

/-- On any nontrivial finite-dimensional real normed space, the identity map is not globally `Lᵖ`
for any `0 < p`, showing that `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` impose no decay at
infinity. -/
theorem not_memLp_id [Nontrivial E] {p : ENNReal} (hp : 0 < p) :
    ¬ MemLp (fun x : E => x) p volume := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hv]
  set B₀ : Set E := ball 0 1
  set C : ℝ≥0∞ := volume B₀ ^ (1 / p.toReal)
  have hB₀_pos : 0 < volume B₀ := measure_ball_pos volume 0 one_pos
  have hB₀_lt : volume B₀ < ∞ := measure_ball_lt_top
  have hC_pos : 0 < C := ENNReal.rpow_pos hB₀_pos hB₀_lt.ne
  have hC_ne_top : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hB₀_lt.ne
  set R : ℝ := (eLpNorm (fun x : E => x) p volume / C).toReal + 2
  have hR1 : 1 ≤ R - 1 := by
    have : 0 ≤ (eLpNorm (fun x : E => x) p volume / C).toReal := ENNReal.toReal_nonneg
    linarith
  have hR_pos : 0 < R := by linarith
  set B : Set E := ball (R • e) 1
  have hvolB : volume B = volume B₀ := Measure.addHaar_ball_center volume (R • e) 1
  have hB_ne : volume.restrict B ≠ 0 := by
    intro h0
    have := congrArg (fun μ : Measure E => μ univ) h0
    simp only [Measure.restrict_apply_univ, FunLike.coe_zero, Pi.zero_apply, hvolB] at this
    exact hB₀_pos.ne' this
  have hconst : eLpNorm (fun _ : E => R - 1) p (volume.restrict B) = ‖R - 1‖ₑ * C := by
    rw [eLpNorm_const _ hp.ne' hB_ne, Measure.restrict_apply_univ, hvolB]
  have hle : eLpNorm (fun _ : E => R - 1) p (volume.restrict B) ≤
      eLpNorm (fun x : E => x) p volume := by
    refine (eLpNorm_mono_ae aestronglyMeasurable_const ?_).trans
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx => ?_)
    have hdist : ‖x - R • e‖ < 1 := by simpa [B, dist_eq_norm] using hx
    have hRe : ‖R • e‖ = R := by rw [norm_smul, Real.norm_of_nonneg hR_pos.le, he, mul_one]
    have hnorm : R - 1 ≤ ‖x‖ := by
      have := norm_sub_norm_le (R • e) x
      rw [norm_sub_rev, hRe] at this
      linarith
    rw [Real.norm_of_nonneg (by linarith)]
    exact hnorm
  rw [hconst] at hle
  have hdiv_lt : eLpNorm (fun x : E => x) p volume / C < ‖R - 1‖ₑ := by
    have hfin : eLpNorm (fun x : E => x) p volume / C ≠ ∞ :=
      ENNReal.div_ne_top h.eLpNorm_lt_top.ne hC_pos.ne'
    rw [← ENNReal.ofReal_toReal hfin, ← ofReal_norm, Real.norm_of_nonneg (by linarith)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by simp only [R]; linarith)
  have hlt : eLpNorm (fun x : E => x) p volume < ‖R - 1‖ₑ * C :=
    (ENNReal.div_lt_iff (Or.inl hC_pos.ne') (Or.inl hC_ne_top)).1 hdiv_lt
  exact hlt.not_ge hle

/-- The norm `x ↦ ‖x‖` lies in the local class `W^{1,p}` on every set of any
finite-dimensional real normed space, for every exponent: it is `1`-Lipschitz and requires no
inner product. -/
theorem memWkpLoc_one_norm {p : ENNReal} {U : Set E} :
    MemWkpLoc p U 1 (fun x : E => ‖x‖) :=
  lipschitzWith_one_norm.memWkpLoc_one

/-- On the non-inner-product model space `ℝ × ℝ` (equipped with the supremum norm), the
Fréchet derivative of the norm at `(1, 1 / 2)` vanishes in the second coordinate direction,
illustrating that the inner-product gradient formula does not apply to general normed spaces
even though `TauCeti.memWkpLoc_one_norm` still places `y ↦ ‖y‖` in `MemWkpLoc p U 1`. -/
theorem fderiv_norm_prod_apply :
    fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, (1 / 2 : ℝ)) (0, 1) = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | 0 < y.1 ∧ |y.2| < y.1} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_fst)
  have hmem : ((1 : ℝ), (1 / 2 : ℝ)) ∈ {y : ℝ × ℝ | 0 < y.1 ∧ |y.2| < y.1} := by
    norm_num
  have heq : (fun y : ℝ × ℝ => ‖y‖) =ᶠ[𝓝 ((1 : ℝ), (1 / 2 : ℝ))]
      (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    filter_upwards [hopen.mem_nhds hmem] with y hy
    simp only [Prod.norm_def, Real.norm_eq_abs, ContinuousLinearMap.coe_fst',
      abs_of_pos hy.1, max_eq_left hy.2.le]
  have hfd : HasFDerivAt (fun y : ℝ × ℝ => ‖y‖)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, (1 / 2 : ℝ)) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.congr_of_eventuallyEq heq
  rw [hfd.fderiv]
  rfl

end IdentityAndNorm

/-! ### Critical singularity `‖x‖⁻¹` and the unit radial map `x ↦ ‖x‖⁻¹ • x` -/

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

section UnitRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  {p : ENNReal} {U : Set E}

private theorem memWkpLoc_one_norm_rpow_neg_one_mul_inner (hd : 1 < Module.finrank ℝ E)
    (hp : p < Module.finrank ℝ E) (v : E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, v⟫) := by
  have hs : -(Module.finrank ℝ E : ℝ) < (-1 : ℝ) := by
    have : (1 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
    linarith
  refine memWkpLoc_one_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, _,
    hasWeakFDerivOn_norm_rpow_mul_inner hs v _, memLpLoc_iff.2 fun K _ hK => ?_⟩
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖v‖
      (Eventually.of_forall fun x => by simpa using abs_norm_rpow_mul_inner_le (-1) v x)
  · have hker : MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict K) :=
      hK.isBounded.memLp_norm_inv_restrict hp
    refine (hker.const_mul ((1 + |(-1 : ℝ)|) * ‖v‖)).of_le
      (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_norm_rpow_smul_innerSL_add_le (-1) v x

/-- In dimension `d ≥ 2`, the unit radial map `x ↦ ‖x‖⁻¹ • x` lies in `MemWkpLoc p U 1` on
every set whenever `p < d`. -/
theorem memWkpLoc_one_unitRadial (hd : 1 < Module.finrank ℝ E) (hp : p < Module.finrank ℝ E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) := by
  let b := stdOrthonormalBasis ℝ E
  rw [b.toBasis.memWkpLoc_iff]
  intro i
  have heq : (fun x : E => b.toBasis.repr (‖x‖⁻¹ • x) i) =
      fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫ := by
    funext x
    rw [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply, inner_smul_right,
      real_inner_comm, Real.rpow_neg_one]
  rw [heq]
  exact memWkpLoc_one_norm_rpow_neg_one_mul_inner hd hp (b i)

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
private theorem inv_norm_le_norm_fderiv_unitRadial (hd : 1 < Module.finrank ℝ E) {x : E}
    (hx : x ≠ 0) : ‖x‖⁻¹ ≤ ‖fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x‖ := by
  have hinv :
      HasFDerivAt (fun y : E => ‖y‖⁻¹)
        ((-1 * ‖x‖ ^ (-1 - 2 : ℝ)) • innerSL ℝ x) x := by
    simpa only [Real.rpow_neg_one] using hasFDerivAt_norm_rpow_of_ne (-1) hx
  have hu : HasFDerivAt (fun y : E => ‖y‖⁻¹ • y)
      (hinv.smul (hasFDerivAt_id x) |> fun _ =>
        ‖x‖⁻¹ • ContinuousLinearMap.id ℝ E +
          ((-1 * ‖x‖ ^ (-1 - 2 : ℝ)) • innerSL ℝ x).smulRight x) x :=
    hinv.smul (hasFDerivAt_id x)
  have horth : (Submodule.span ℝ ({x} : Set E))ᗮ ≠ ⊥ := by
    intro hbot
    have hsum := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({x} : Set E))
    rw [hbot, finrank_bot, add_zero] at hsum
    have hle : Module.finrank ℝ (Submodule.span ℝ ({x} : Set E)) ≤ 1 :=
      finrank_span_singleton hx |>.le
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  have hxw : ⟪x, w⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hw
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have happ : fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x w = ‖x‖⁻¹ • w := by
    rw [hu.fderiv]
    simp [hxw]
  have hbound :
      ‖x‖⁻¹ * ‖w‖ ≤
        ‖fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x‖ * ‖w‖ := by
    calc ‖x‖⁻¹ * ‖w‖ = ‖‖x‖⁻¹ • w‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ = ‖fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x w‖ := by rw [happ]
      _ ≤ ‖fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
  exact le_of_mul_le_mul_right hbound hw_pos

/-- In dimension `d ≥ 2`, the unit radial map `x ↦ ‖x‖⁻¹ • x` is not in `MemWkpLoc p U 1` for
any `p ≥ d` when `0 ∈ interior U`. -/
theorem not_memWkpLoc_one_unitRadial (hd : 1 < Module.finrank ℝ E)
    (hp : Module.finrank ℝ E ≤ p) (h0 : (0 : E) ∈ interior U) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (zero_lt_one.trans hd)
  intro h
  obtain ⟨-, D, hD, hDLp⟩ := memWkpLoc_one_iff.1 h
  set u : E → E := fun x => ‖x‖⁻¹ • x
  set Ω' : Opens E := Opens.interior U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hsmooth : ContDiffOn ℝ 1 u (Ω' : Set E) := fun x hx =>
    (((contDiffAt_norm ℝ hx.2 : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).inv
      (norm_ne_zero_iff.2 hx.2)).smul contDiffAt_id).contDiffWithinAt
  have hfu : HasWeakFDerivOn volume Ω' u (fderiv ℝ u) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hsmooth.continuousOn_fderiv_of_isOpen Ω'.isOpen le_rfl).locallyIntegrableOn
        Ω'.isOpen.measurableSet)
      fun x hx => (hsmooth.differentiableOn one_ne_zero).differentiableAt (Ω'.isOpen.mem_nhds hx)
  have hae : D =ᵐ[volume.restrict Ω'] fderiv ℝ u := (hD.mono inf_le_left).ae_eq hfu
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
    exact inv_norm_le_norm_fderiv_unitRadial hd hx0
  exact not_memLp_norm_inv_closedBall (half_pos hr) hp hinvK

/-- **Critical exponent for the unit radial map.** On a finite-dimensional real inner product
space of dimension `d ≥ 2`, `x ↦ ‖x‖⁻¹ • x` lies in `MemWkpLoc p U 1` on any set whose
interior contains the origin iff `p < d`. -/
theorem memWkpLoc_one_unitRadial_iff (hd : 1 < Module.finrank ℝ E) (h0 : (0 : E) ∈ interior U) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_one_unitRadial hd hp h0 h,
    fun hp => memWkpLoc_one_unitRadial hd hp⟩

end UnitRadial

end RadialSingularity

/-! ### Jump across a hyperplane in arbitrary dimension -/

section HalfSpaceJump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
/-- The indicator of any open half-space `{x | 0 < ℓ x}` is locally `Lᵖ` on every set, for every
exponent. -/
theorem memLpLoc_indicator_pos {p : ENNReal} {U : Set E} (ℓ : E →L[ℝ] ℝ) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (measurableSet_lt measurable_const ℓ.continuous.measurable).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

private theorem ae_zero_of_hasWeakFDerivOn_indicator_fst_pos {d : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin d))}
    {D : (ℝ × EuclideanSpace ℝ (Fin d)) → (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ}
    (hD : HasWeakFDerivOn volume Ω ({q | 0 < q.1}.indicator fun _ => (1 : ℝ)) D) :
    D =ᵐ[volume.restrict Ω] 0 := by
  let H := EuclideanSpace ℝ (Fin d)
  have : (volume : Measure (ℝ × H)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  set u : ℝ × H → ℝ := {q | 0 < q.1}.indicator fun _ => (1 : ℝ) with hu
  set Ωp : Opens (ℝ × H) :=
    Ω ⊓ ⟨{q | 0 < q.1}, isOpen_lt continuous_const continuous_fst⟩
  set Ωn : Opens (ℝ × H) :=
    Ω ⊓ ⟨{q | q.1 < 0}, isOpen_lt continuous_fst continuous_const⟩
  have hconst : HasWeakFDerivOn volume Ωp (fun _ => (1 : ℝ)) 0 :=
    hasWeakFDerivOn_iff.2 fun v => by
      simpa using (hasWeakLineDerivOn_const (1 : ℝ) :
        HasWeakLineDerivOn volume Ωp (fun _ => (1 : ℝ)) (fun _ => 0) v)
  have hp : HasWeakFDerivOn volume Ωp u 0 := hconst.congr_ae <|
    (ae_restrict_iff' Ωp.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
      simp [hu, Set.indicator_of_mem (show q ∈ {q : ℝ × H | 0 < q.1} from hq.2)]
  have hn : HasWeakFDerivOn volume Ωn u 0 := (hasWeakFDerivOn_zero (μ := volume)).congr_ae <|
    (ae_restrict_iff' Ωn.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
      have hq' : ¬ 0 < q.1 := not_lt.2 (le_of_lt hq.2)
      simp [hu, hq']
  have hDp := (ae_restrict_iff' Ωp.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hp)
  have hDn := (ae_restrict_iff' Ωn.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hn)
  have hhyper : volume ({q : ℝ × H | q.1 = 0}) = 0 := by
    have hset :
        ({q : ℝ × H | q.1 = 0} : Set (ℝ × H)) = ({0} : Set ℝ) ×ˢ (univ : Set H) := by
      ext q; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
  filter_upwards [hDp, hDn, measure_eq_zero_iff_ae_notMem.1 hhyper] with q hqp hqn hq0 hqΩ
  rcases lt_or_gt_of_ne hq0 with h | h
  · exact hqn ⟨hqΩ, h⟩
  · exact hqp ⟨hqΩ, h⟩

private theorem integral_deriv_bump_indicator_Ioi (a : ContDiffBump (0 : ℝ)) :
    ∫ x : ℝ, deriv a x * (Ioi (0 : ℝ)).indicator 1 x = -1 := by
  have hda : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have hfun : (fun x : ℝ => deriv a x * (Ioi (0 : ℝ)).indicator 1 x) =
      (Ioi (0 : ℝ)).indicator (deriv a) := by
    funext x
    by_cases hx : 0 < x <;> simp [Set.indicator, hx]
  rw [hfun, integral_indicator measurableSet_Ioi]
  have hdc : Continuous (deriv a) := (a.contDiff (n := 1)).continuous_deriv le_rfl
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) a.continuous.continuousWithinAt
    (fun x _ => hda x)
    (hdc.integrable_of_hasCompactSupport a.hasCompactSupport.deriv).integrableOn ?_,
    a.one_of_mem_closedBall (mem_closedBall_self a.rIn_pos.le)]
  · simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop a.rOut] with x hx
    refine (a.zero_of_le_dist ?_).symm
    rw [Real.dist_eq, sub_zero]
    exact hx.trans (le_abs_self x)

private theorem not_hasWeakFDerivOn_indicator_fst_pos {d : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin d))} {p₀ : ℝ × EuclideanSpace ℝ (Fin d)}
    (hp₀ : p₀ ∈ Ω) (hp₀1 : p₀.1 = 0)
    (D : (ℝ × EuclideanSpace ℝ (Fin d)) →
      (ℝ × EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({q | 0 < q.1}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  let H := EuclideanSpace ℝ (Fin d)
  set u : ℝ × H → ℝ := {q | 0 < q.1}.indicator fun _ => (1 : ℝ) with hu
  have hD0 : D =ᵐ[volume.restrict Ω] 0 :=
    ae_zero_of_hasWeakFDerivOn_indicator_fst_pos hD
  have hline := (hD.congr_ae_deriv hD0).hasWeakLineDerivOn ((1 : ℝ), (0 : H))
  -- Test against a product of smooth bump functions centred at `p₀`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen p₀ hp₀
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let b : ContDiffBump p₀.2 := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let f : ℝ × H → ℝ := ((a : ℝ → ℝ) ∘ Prod.fst) * ((b : H → ℝ) ∘ Prod.snd)
  have hfs : tsupport f ⊆ closedBall p₀ (ε / 2) := by
    intro q hq
    have hq1 : q ∈ Prod.fst ⁻¹' tsupport a :=
      tsupport_comp_subset_preimage (a : ℝ → ℝ) continuous_fst (tsupport_mul_subset_left hq)
    have hq2 : q ∈ Prod.snd ⁻¹' tsupport b :=
      tsupport_comp_subset_preimage (b : H → ℝ) continuous_snd (tsupport_mul_subset_right hq)
    rw [mem_preimage, a.tsupport_eq, mem_closedBall] at hq1
    rw [mem_preimage, b.tsupport_eq, mem_closedBall] at hq2
    rw [mem_closedBall, Prod.dist_eq, hp₀1]
    simp only [a, b] at hq1 hq2
    exact max_le (hq1.trans (by linarith)) (hq2.trans (by linarith))
  have hfΩ : tsupport f ⊆ Ω := fun q hq =>
    hball (closedBall_subset_ball (by linarith) (hfs hq))
  let φ : 𝓓(Ω, ℝ) := ⟨f, (a.contDiff.comp (ContinuousLinearMap.fst ℝ ℝ H).contDiff).mul
      (b.contDiff.comp (ContinuousLinearMap.snd ℝ ℝ H).contDiff),
    (isCompact_closedBall p₀ _).of_isClosed_subset (isClosed_tsupport f) hfs, hfΩ⟩
  have hφ : (φ : ℝ × H → ℝ) = f := TestFunction.coe_mk
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  have hda : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have hldf :
      ∀ q : ℝ × H, lineDeriv ℝ (φ : ℝ × H → ℝ) q (1, 0) = deriv a q.1 * b q.2 := by
    intro q
    refine HasLineDerivAt.lineDeriv
      (?_ : HasDerivAt
        (fun t : ℝ => (φ : ℝ × H → ℝ) (q + t • ((1 : ℝ), (0 : H)))) _ 0)
    have h := ((hda (q.1 + 0)).comp_const_add q.1 0).mul_const (b q.2)
    simp only [add_zero] at h
    convert h using 1
    funext t
    simp [hφ, f]
  have hint : (∫ q : ℝ × H, lineDeriv ℝ (φ : ℝ × H → ℝ) q (1, 0) • u q) =
      ∫ q : ℝ × H, (deriv a q.1 * (Ioi (0 : ℝ)).indicator 1 q.1) * b q.2 := by
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hldf, smul_eq_mul, hu]
    by_cases hq : 0 < q.1 <;> simp [Set.indicator, hq]
  have hprod := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure H))
    (fun x => deriv a x * (Ioi (0 : ℝ)).indicator 1 x) (fun y => b y)
  rw [hint, Measure.volume_eq_prod, hprod, integral_deriv_bump_indicator_Ioi a] at hkey
  have hb := b.integral_pos (μ := volume)
  linarith

/-- The indicator of an open half-space `{x | 0 < ℓ x}` (for a nonzero continuous linear
functional `ℓ`) admits no weak derivative on any open set meeting `ker ℓ`. -/
theorem not_hasWeakFDerivOn_indicator_pos {Ω : Opens E} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hx₀' : ℓ x₀ = 0) (D : E → E →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  obtain ⟨w, hw⟩ : ∃ w : E, ℓ w ≠ 0 := by
    by_contra! h
    exact hℓ (ContinuousLinearMap.ext h)
  set v : E := (ℓ w)⁻¹ • w
  have hℓv : ℓ v = 1 := by simp [v, inv_mul_cancel₀ hw]
  set K := LinearMap.ker ℓ.toLinearMap
  let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ K))
  have : (volume : Measure (ℝ × H)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let eK : EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) ≃L[ℝ] K :=
    ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ K)) ℝ).toBasis.equiv
      (Module.finBasis ℝ K) (Equiv.refl _)).toContinuousLinearEquiv
  let eLin : (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) ≃ₗ[ℝ] E :=
    { toFun := fun q => q.1 • v + (eK q.2 : E)
      map_add' := fun q₁ q₂ => by simp [add_smul]; abel
      map_smul' := fun c q => by simp [smul_smul, smul_add]
      invFun := fun x => (ℓ x, eK.symm ⟨x - ℓ x • v, by
        change ℓ (x - ℓ x • v) = 0
        simp [hℓv]⟩)
      left_inv := fun q => by
        have hq2 : ℓ (eK q.2 : E) = 0 := (eK q.2).property
        ext
        · simp [hℓv, hq2]
        · apply congrArg (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) => z _)
          simp only [map_add, map_smul, hℓv, hq2, smul_eq_mul, mul_one, add_zero,
            add_sub_cancel_left, Subtype.coe_eta, ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun x => by simp }
  let e : (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) ≃L[ℝ] E :=
    eLin.toContinuousLinearEquiv
  have hℓe : ∀ q, ℓ (e q) = q.1 := fun q => by
    have hq2 : ℓ (eK q.2 : E) = 0 := (eK q.2).property
    simp [e, eLin, hℓv, hq2]
  let Ω' : Opens (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) :=
    ⟨e ⁻¹' Ω, Ω.isOpen.preimage e.continuous⟩
  have hpull := hD.comp_continuousLinearEquiv_of_isAddHaarMeasure (μ := volume) (U := Ω') e
    (mapsTo_preimage e Ω)
  have hcomp : ({x : E | 0 < ℓ x}.indicator (fun _ => (1 : ℝ))) ∘ e =
      {q | 0 < q.1}.indicator fun _ => (1 : ℝ) := by
    funext q
    simp [Function.comp_apply, Set.indicator, hℓe]
  rw [hcomp] at hpull
  exact not_hasWeakFDerivOn_indicator_fst_pos (Ω := Ω') (p₀ := e.symm x₀)
    (by simpa [Ω'] using hx₀) (by simp [e, eLin, hx₀']) _ hpull

/-- The indicator of an open half-space `{x | 0 < ℓ x}` (for `ℓ ≠ 0`) lies in no local Sobolev
class of positive order on any set whose interior meets `ker ℓ`, although it is locally `Lᵖ`
there. -/
theorem not_memWkpLoc_indicator_pos {p : ENNReal} {U : Set E} {k : ℕ} {ℓ : E →L[ℝ] ℝ}
    (hℓ : ℓ ≠ 0) {x₀ : E} (hx₀ : x₀ ∈ interior U) (hx₀' : ℓ x₀ = 0) :
    ¬ MemWkpLoc p U (k + 1) ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := fun h => by
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_pos hℓ (Ω := Opens.interior U) hx₀ hx₀' D hD

end HalfSpaceJump

/-! ### Haar-measure independence and model-space comparison checks -/

section HaarAndModelChecks

/-- Scaling the ambient Lebesgue measure by `2` yields the exact same local Sobolev classes. -/
theorem memWkpLoc_two_smul_volume_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ ⟨(2 : ℝ≥0∞) • (volume : Measure E)⟩ p U k F _ _ f ↔
      MemWkpLoc p U k f :=
  memWkpLoc_smul_measure_iff (by norm_num) (by norm_num)

/-- Local Sobolev classes on the non-inner-product model `ℝ × ℝ` (with supremum norm and
product measure) agree with those on `EuclideanSpace ℝ (Fin 2)` under any continuous linear
equivalence. -/
theorem memWkpLoc_prod_iff_euclideanSpace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {U : Set (ℝ × ℝ)} {k : ℕ} {u : ℝ × ℝ → F}
    (e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ) :
    MemWkpLoc p (e ⁻¹' U) k (u ∘ e) ↔ MemWkpLoc p U k u := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact e.memWkpLoc_comp_iff

end HaarAndModelChecks

/-! ### Infinite-dimensional Banach targets and non-separable counterexample -/

section BanachTargets

/-- On the infinite-dimensional Hilbert space `lp (fun _ : ℕ => ℝ) 2`, scaling a fixed vector by
the norm yields a `W^{1,p}_loc` map on any finite-dimensional real normed space for every
exponent `p` and every set `U`. -/
theorem memWkpLoc_one_norm_smul_lp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {p : ENNReal} {U : Set E}
    (v : lp (fun _ : ℕ => ℝ) 2) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ • v) :=
  memWkpLoc_one_norm.smul_const v

/-- On the non-separable Hilbert space `lp (fun _ : ℝ => ℝ) 2`, the map `x ↦ lp.single 2 x 1`
has unit norm everywhere. -/
theorem norm_lpSingle_eq_one (x : ℝ) :
    ‖lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)‖ = 1 := by
  rw [lp.norm_single (by norm_num), norm_one]

/-- Composing `x ↦ lp.single 2 x 1` with any continuous linear functional on
`lp (fun _ : ℝ => ℝ) 2` vanishes outside a countable set, hence equals `0` almost everywhere on
`ℝ` and belongs to every local Sobolev class `MemWkpLoc p U k`. -/
theorem weak_memWkpLoc_lpSingle {p : ENNReal} {U : Set ℝ} {k : ℕ}
    (ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2)) :
    MemWkpLoc p U k (ℓ ∘ fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) := by
  set y : lp (fun _ : ℝ => ℝ) 2 :=
    (InnerProductSpace.toDual ℝ (lp (fun _ : ℝ => ℝ) 2)).symm ℓ
  have happly :
      ∀ x : ℝ, ℓ (lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) = y x := fun x => by
    have h := InnerProductSpace.toDual_symm_apply
      (x := lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) (y := ℓ)
    rw [← h, lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul]
  have hsum : Summable (fun x : ℝ => ‖y x‖ ^ (2 : ℝ)) := by
    simpa [ENNReal.toReal_ofNat] using (lp.memℓp y).summable (by norm_num)
  have hcount : ({x : ℝ | y x ≠ 0}).Countable := by
    refine hsum.countable_support.mono fun x hx => ?_
    simp only [Function.mem_support, ne_eq]
    have hpos : 0 < ‖y x‖ := norm_pos_iff.2 hx
    positivity
  have hae :
      (ℓ ∘ fun x : ℝ =>
        lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) =ᵐ[volume] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hcount.measure_zero volume)] with x hx
    have hyx : y x = 0 := not_not.1 hx
    simp [Function.comp_apply, happly, hyx]
  exact (memWkpLoc_zero_fun (p := p) (U := U) (k := k)).congr_ae (ae_restrict_of_ae hae.symm)

/-- **Strong measurability counterexample in a non-separable Banach space.** Although
`x ↦ lp.single 2 x 1` on `lp (fun _ : ℝ => ℝ) 2` is bounded (`TauCeti.norm_lpSingle_eq_one`)
and weakly in every `MemWkpLoc p U k` (`TauCeti.weak_memWkpLoc_lpSingle`), it fails Bochner
strong measurability on every compact set of positive measure and therefore lies in no
`MemLpLoc p U` whenever `interior U` is nonempty. -/
theorem not_memLpLoc_lpSingle {p : ENNReal} {U : Set ℝ} (hU : (interior U).Nonempty) :
    ¬ MemLpLoc p U (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) := by
  intro h
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  set K : Set ℝ := closedBall x₀ (r / 2)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith)).trans (hrU.trans interior_subset)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) (volume.restrict K) :=
    (memLpLoc_iff.1 h K hKU (isCompact_closedBall x₀ _)).aestronglyMeasurable
  obtain ⟨t, ht_sep, ht_ae⟩ := hmeas.isSeparable_ae_range
  obtain ⟨D, hD_count, hDt⟩ := ht_sep
  set u : ℝ → lp (fun _ : ℝ => ℝ) 2 := fun x => lp.single 2 x (1 : ℝ)
  set s : Set ℝ := K ∩ u ⁻¹' t
  have hs_uncount : ¬ s.Countable := by
    intro hs_count
    have hK_le : volume K ≤ volume s + volume (K \ s) := by
      calc volume K ≤ volume (s ∪ (K \ s)) := measure_mono fun x hx => by
            by_cases hxs : x ∈ s
            · exact Or.inl hxs
            · exact Or.inr ⟨hx, hxs⟩
        _ ≤ volume s + volume (K \ s) := measure_union_le _ _
    have hdiff : volume (K \ s) = 0 := by
      have hsub : K \ s ⊆ {x | u x ∉ t} ∩ K :=
        fun x hx => ⟨fun hxt => hx.2 ⟨hx.1, hxt⟩, hx.1⟩
      refine measure_mono_null hsub ?_
      rw [← Measure.restrict_apply' measurableSet_closedBall]
      simpa [ae_iff] using ht_ae
    rw [hs_count.measure_zero, hdiff, add_zero] at hK_le
    exact (measure_closedBall_pos volume x₀ (half_pos hr)).not_ge hK_le
  have hdist : ∀ x y : ℝ, x ≠ y → 1 ≤ dist (u x) (u y) := fun x y hxy => by
    rw [dist_eq_norm]
    have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (u x - u y) x
    have hval : (u x - u y) x = 1 := by
      change (u x) x - (u y) x = 1
      simp [u, Pi.single_eq_same, Pi.single_eq_of_ne hxy]
    rwa [hval, norm_one] at hle
  have hex : ∀ x : s, ∃ d : D, dist (u x.val) d.val < 1 / 2 := fun x => by
    obtain ⟨d, hdD, hdist'⟩ := Metric.mem_closure_iff.1 (hDt x.property.2) (1 / 2) (by norm_num)
    exact ⟨⟨d, hdD⟩, hdist'⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := fun x y hxy => by
    by_contra hne
    have h1 := hdist x.val y.val (Subtype.coe_ne_coe.2 hne)
    have h2 : dist (u x.val) (u y.val) < 1 := by
      calc dist (u x.val) (u y.val) ≤ dist (u x.val) (φ x).val + dist (φ x).val (u y.val) :=
            dist_triangle _ _ _
        _ = dist (u x.val) (φ x).val + dist (u y.val) (φ y).val := by rw [hxy, dist_comm (φ y).val]
        _ < 1 / 2 + 1 / 2 := add_lt_add (hφ x) (hφ y)
        _ = 1 := by norm_num
    linarith
  have : Countable D := hD_count.to_subtype
  exact hs_uncount (hinj.countable.to_set)

end BanachTargets

end TauCeti
