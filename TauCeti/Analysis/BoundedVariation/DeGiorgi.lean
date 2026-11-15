/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.MeasureTheory.Rectifiable.Cone
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import TauCeti.MeasureTheory.Covering.Besicovitch
import TauCeti.MeasureTheory.Covering.DensityTheorem
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# De Giorgi's structure theorem for sets of finite perimeter

Let `Ω` be an open subset of a finite-dimensional real inner product space `F` of dimension `n`,
equipped with Lebesgue measure, and let `s ⊆ F` be a set. De Giorgi's structure theorem describes
the reduced boundary `∂*s` (`TauCeti.reducedBoundary`) and identifies the distributional derivative
of `χ_s` on `Ω` with the `(n - 1)`-dimensional surface measure on `∂*s` weighted by the
measure-theoretic outer unit normal `ν_s` (`TauCeti.outerNormal`):

* `∂*s` is countably `(n - 1)`-rectifiable (`TauCeti.countablyRectifiable_reducedBoundary`), proved
  more generally against any additive Haar measure on the ambient space;
* the perimeter measure `|Dχ_s|` on `Ω` is the restriction of the normalized Euclidean Hausdorff
  measure `Hⁿ⁻¹ = μHE[n - 1]` to `∂*s`
  (`TauCeti.variationMeasure_indicator_eq_restrict_reducedBoundary`,
  `TauCeti.map_variationMeasure_indicator_eq_restrict_reducedBoundary`,
  `TauCeti.variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary`), so for a
  set of locally finite perimeter in `Ω` its perimeter in `U ≤ Ω` is `Hⁿ⁻¹(U ∩ ∂*s)`
  (`TauCeti.perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary`,
  `TauCeti.perimeter_eq_euclideanHausdorffMeasure_reducedBoundary`);
* the **De Giorgi–Gauss–Green formula**
  `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`
  holds for every `C¹` vector field `φ` with compact support in `Ω`
  (`TauCeti.setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal`,
  `TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`,
  `TauCeti.setIntegral_divergenceCLM_eq_setIntegral_inner_outerNormal`).

No dimension restriction `n ≥ 2` is imposed: all statements hold for `n = 0`, `n = 1`, and `n ≥ 2`.

## Proof outline

* **Rectifiability (`n ≥ 2`).** Decompose `∂*s` into the pieces `piece N` on which both lower
  volume density bounds (`TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball` and
  `TauCeti.eventually_ofReal_pow_le_mul_measure_ball_sdiff`) hold uniformly up to radius
  `1 / (N + 1)`. At `x ∈ piece N`, blow-up convergence to the half-space `{z | ⟪z, ν_s x⟫ < 0}`
  (`TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`) prevents nearby
  points `y ∈ piece N` from having `|⟪y - x, ν_s x⟫| > (1 / 2) ‖y - x‖`, since a ball of radius
  `‖y - x‖ / 2` around `y` would otherwise put a definite volume fraction of `s` or `sᶜ` inside the
  symmetric difference with the half-space. Applying the hyperplane normal-cone criterion
  (`TauCeti.CountablyRectifiable.of_forall_exists_inner_le`) to each `piece N` gives countable
  `(n - 1)`-rectifiability.
* **Dimension `n = 1` (and `n = 0`).** In dimension `0` the reduced boundary is empty because there
  is no unit vector. In dimension `1`, pulling back along an isometric coordinate line and applying
  `TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn` between Lebesgue points of `s` and `sᶜ`
  gives `P(s; ball y r) ≥ 1` at every `y ∈ ∂*s`. Finiteness of `|Dχ_s|` on punctured shrinking
  closed balls then forces points of `∂*s` to be isolated, hence countably `0`-rectifiable; on the
  two open half-intervals around `x ∈ ∂*s` the perimeter vanishes, so `s` agrees locally a.e. with
  a half-line and `|Dχ_s|(closedBall x r) = 1` for small `r > 0`.
* **Identification of `|Dχ_s|` with `Hⁿ⁻¹⌊∂*s`.** At every point of `∂*s`, closed balls have
  `k`-dimensional `|Dχ_s|`-density `1` (`k = n - 1`), so the lower Hausdorff density comparison
  (`MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure`) yields `μ₀ ≤ |Dχ_s|` for
  `μ₀ = (Hⁿ⁻¹ : Measure Ω).restrict (∂*s)`. Consequently `μ₀` is locally finite on `Ω`. Applying
  the rectifiable density theorem
  (`TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`) on
  closed balls inside `Ω` shows that `μ₀` also has `k`-dimensional density `1` at `μ₀`-a.e. point.
  Comparing ratios via Besicovitch differentiation (`Besicovitch.ae_tendsto_rnDeriv`) gives
  `|Dχ_s|.rnDeriv μ₀ =ᵐ[μ₀] 1`, while the upper Hausdorff bound
  (`TauCeti.variationMeasure_preimage_le_mul_hausdorffMeasure`) and concentration on `∂*s`
  (`TauCeti.ae_mem_reducedBoundary`) give `|Dχ_s| ≪ μ₀`. Hence `|Dχ_s| = μ₀`.

## References

* E. De Giorgi, *Nuovi teoremi relativi alle misure `(r - 1)`-dimensionali in uno spazio ad `r`
  dimensioni*, Ricerche Mat. **4** (1955), 95–113.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.9 and
  Lemma 15.13.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.3 (Theorem 5.15 and Theorem 5.16) and §5.8 (Theorem 5.17).
* L. Simon, *Lectures on Geometric Measure Theory*, §14 (Theorem 14.3).
-/

public section

noncomputable section

namespace TauCeti

open Filter Function MeasureTheory Metric Module Set TestFunction TopologicalSpace
open scoped Distributions ENNReal NNReal RealInnerProductSpace symmDiff Topology

/-! ### One-dimensional reduced boundary -/

section OneDimReal

/-- On an open interval `(a, b) ⊆ ℝ`, any set `T` whose intersection and complement in `(a, b)`
are null-measurable and both have positive Lebesgue measure has perimeter at least `1`. -/
private theorem one_le_perimeter_Ioo_of_volume_pos {a b : ℝ} {T : Set ℝ}
    (hTm : NullMeasurableSet (T ∩ Ioo a b) volume) (hT1 : 0 < volume (T ∩ Ioo a b))
    (hT0 : 0 < volume (Ioo a b \ T)) :
    1 ≤ perimeter volume ⟨Ioo a b, isOpen_Ioo⟩ T := by
  set T' := T ∩ Ioo a b
  have hu : LocallyIntegrable (T'.indicator (1 : ℝ → ℝ)) volume :=
    (locallyIntegrable_const 1).indicator₀ hTm
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume hu
  obtain ⟨p, hpT', hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hT1.ne'
    (ae_restrict_of_ae hae)
  have hdiff : Ioo a b \ T' = Ioo a b \ T := by ext z; simp [T']
  obtain ⟨q, hqT', hq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := Ioo a b \ T') (by rw [hdiff]; exact hT0.ne') (ae_restrict_of_ae hae)
  let pts : Fin 2 → ℝ := ![min p q, max p q]
  have hmono : Monotone pts := Fin.monotone_iff_le_succ.2 fun i => by
    fin_cases i; exact min_le_max
  have hIcc : Icc (pts 0) (pts (Fin.last 1)) ⊆ Ioo a b :=
    Icc_subset_Ioo (lt_min hpT'.2.1 hqT'.1.1) (max_lt hpT'.2.2 hqT'.1.2)
  have hleb (i : Fin 2) : Tendsto (fun r => ⨍ y in closedBall (pts i) r,
      ‖T'.indicator (1 : ℝ → ℝ) y - T'.indicator (1 : ℝ → ℝ) (pts i)‖) (𝓝[>] 0) (𝓝 0) := by
    fin_cases i
    · rcases min_choice p q with h | h <;> simp only [pts, h] <;> assumption
    · rcases max_choice p q with h | h <;> simp only [pts, h] <;> assumption
  have hbound := Real.ofReal_sum_abs_sub_le_totalVariationOn (Ω := ⟨Ioo a b, isOpen_Ioo⟩)
    (hu.locallyIntegrableOn _) hmono hIcc hleb
  have hval : |T'.indicator (1 : ℝ → ℝ) (max p q) - T'.indicator (1 : ℝ → ℝ) (min p q)| = 1 := by
    rcases le_total p q with hpq | hqp
    · simp [min_eq_left hpq, max_eq_right hpq, hpT', hqT'.2]
    · simp [min_eq_right hqp, max_eq_left hqp, hpT', hqT'.2]
  rw [perimeter_congr_of_inter_eq (t := T') (by simp [T']), perimeter_def]
  simpa [pts, Fin.sum_univ_one, hval] using hbound

/-- An open interval `(a, b) ⊆ ℝ` on which `T` has zero perimeter either misses `T` almost
everywhere or contains `(a, b)` almost everywhere. -/
private theorem volume_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_Ioo_eq_zero {a b : ℝ}
    {T : Set ℝ} (hTm : NullMeasurableSet (T ∩ Ioo a b) volume)
    (hP : perimeter volume ⟨Ioo a b, isOpen_Ioo⟩ T = 0) :
    volume (T ∩ Ioo a b) = 0 ∨ volume (Ioo a b \ T) = 0 := by
  by_contra! h
  have hle := one_le_perimeter_Ioo_of_volume_pos hTm h.1.bot_lt h.2.bot_lt
  simp [hP] at hle

end OneDimReal

section OneDimSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a `1`-dimensional real inner product space, `t ↦ x + t • ν` (for a unit vector `ν`) is an
affine isometry equivalence `ℝ ≃ᵃⁱ[ℝ] E`. -/
private def coordEquivOfFinrankEqOne (hdim : finrank ℝ E = 1) {ν : E} (hν : ‖ν‖ = 1) (x : E) :
    ℝ ≃ᵃⁱ[ℝ] E := by
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
  have htop : ℝ ∙ ν = ⊤ := Submodule.eq_top_of_finrank_eq
    ((finrank_span_singleton hν0).trans hdim.symm)
  have hspan (z : E) : ⟪z, ν⟫ • ν = z := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (htop.symm ▸ Submodule.mem_top : z ∈ ℝ ∙ ν)
    simp [real_inner_smul_left, hν]
  let L : ℝ ≃ₗᵢ[ℝ] E :=
    { toFun := fun t => t • ν
      map_add' := fun a b => add_smul a b ν
      map_smul' := fun a b => mul_smul a b ν
      invFun := fun z => ⟪z, ν⟫
      left_inv := fun t => by simp [real_inner_smul_left, hν]
      right_inv := hspan
      norm_map' := fun t => by simp [norm_smul, hν] }
  exact L.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ E x)

private theorem coordEquivOfFinrankEqOne_apply (hdim : finrank ℝ E = 1) {ν : E} (hν : ‖ν‖ = 1)
    (x : E) (t : ℝ) : coordEquivOfFinrankEqOne hdim hν x t = x + t • ν := by
  simp [coordEquivOfFinrankEqOne]

private theorem coordEquivOfFinrankEqOne_symm_apply (hdim : finrank ℝ E = 1) {ν : E}
    (hν : ‖ν‖ = 1) (x y : E) : (coordEquivOfFinrankEqOne hdim hν x).symm y = ⟪y - x, ν⟫ := by
  let f := coordEquivOfFinrankEqOne hdim hν x
  calc f.symm y = ⟪f (f.symm y) - x, ν⟫ := by
        rw [coordEquivOfFinrankEqOne_apply, add_sub_cancel_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq, hν, one_pow, mul_one]
    _ = ⟪y - x, ν⟫ := by rw [f.apply_symm_apply]

private theorem measurePreserving_coordEquivOfFinrankEqOne [MeasurableSpace E] [BorelSpace E]
    (hdim : finrank ℝ E = 1) {ν : E} (hν : ‖ν‖ = 1) (x : E) :
    MeasurePreserving (coordEquivOfFinrankEqOne hdim hν x) volume volume := by
  let f := coordEquivOfFinrankEqOne hdim hν x
  have hf : (f : ℝ → E) = (x + ·) ∘ f.linearIsometryEquiv := by
    ext t
    have h0 : f 0 = x := by simp [f, coordEquivOfFinrankEqOne_apply]
    simpa [h0, add_comm] using f.map_vadd 0 t
  rw [hf]
  exact (measurePreserving_add_left volume x).comp f.linearIsometryEquiv.measurePreserving

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E}

omit [BorelSpace E] in
/-- Scaling the ambient measure by `c : ℝ≥0` scales the perimeter by `c`. -/
private theorem perimeter_smul_nnreal (c : ℝ≥0) (ν : Measure E) (U : Opens E) (s : Set E) :
    perimeter (c • ν) U s = c * perimeter ν U s := by
  simp_rw [perimeter_def, totalVariationOn_def, ENNReal.mul_iSup]
  refine iSup_congr fun φ => iSup_congr fun _ => ?_
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]

/-- In dimension `1`, at any point `x ∈ reducedBoundary μ Ω s` (for an additive Haar measure `μ`),
every ball `ball x r ⊆ Ω` (`r > 0`) has Euclidean perimeter at least `1`. -/
private theorem one_le_perimeter_volume_ball_of_finrank_eq_one [μ.IsAddHaarMeasure]
    (hdim : finrank ℝ E = 1) {x : E} (hx : x ∈ reducedBoundary μ Ω s) {r : ℝ} (hr : 0 < r)
    (hΩ : ball x r ⊆ Ω) :
    1 ≤ perimeter volume ⟨ball x r, isOpen_ball⟩ s := by
  let f := coordEquivOfFinrankEqOne hdim (norm_outerNormal hx) x
  have hfmp := measurePreserving_coordEquivOfFinrankEqOne hdim (norm_outerNormal hx) x
  have hf0 : f 0 = x := by simp [f, coordEquivOfFinrankEqOne_apply]
  have hball : f ⁻¹' ball x r = Ioo (-r) r := by
    ext t
    simp [← hf0, mem_ball, f.dist_map, abs_lt]
  have hcomap : Opens.comap ⟨f, f.continuous⟩ ⟨ball x r, isOpen_ball⟩ = ⟨Ioo (-r) r, isOpen_Ioo⟩ :=
    Opens.ext hball
  have hveq : (volume : Measure E) = Measure.addHaarScalarFactor volume μ • μ :=
    Measure.isAddLeftInvariant_eq_smul volume μ
  have hpos {A : Set E} (hA : 0 < μ A) : 0 < volume A := by
    rw [hveq, smul_apply, ENNReal.smul_def]
    exact ENNReal.mul_pos
      (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume μ).ne')
      hA.ne'
  have hsbm : NullMeasurableSet (s ∩ ball x r) volume := by
    have hsΩ : NullMeasurableSet (s ∩ Ω) volume :=
      hveq ▸ (nullMeasurableSet_inter_of_mem_reducedBoundary hx).smul_measure _
    have heq : (s ∩ Ω) ∩ ball x r = s ∩ ball x r := by rw [inter_assoc, inter_eq_right.2 hΩ]
    exact heq ▸ hsΩ.inter measurableSet_ball.nullMeasurableSet
  rw [← f.perimeter_comap hfmp, hcomap]
  refine one_le_perimeter_Ioo_of_volume_pos ?_ ?_ ?_
  · rw [← hball, ← preimage_inter]
    exact hsbm.preimage hfmp.quasiMeasurePreserving
  · rw [← hball, ← preimage_inter,
      hfmp.measure_preimage_emb f.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
    exact hpos (measure_inter_ball_pos hx hr)
  · rw [← hball, ← preimage_sdiff,
      hfmp.measure_preimage_emb f.toHomeomorph.toMeasurableEquiv.measurableEmbedding,
      Set.sdiff_eq, inter_comm]
    exact hpos (measure_inter_ball_pos (by rwa [reducedBoundary_compl]) hr)

/-- For any Borel measure `lam` on `Ω` that is finite on compacts, punctured closed balls around
`x ∈ Ω` have arbitrarily small `lam`-measure. -/
private theorem exists_measure_preimage_closedBall_sdiff_singleton_lt (lam : Measure Ω)
    [IsFiniteMeasureOnCompacts lam] {x : E} (hxΩ : x ∈ Ω) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r > 0, closedBall x r ⊆ Ω ∧ lam (((↑) : Ω → E) ⁻¹' (closedBall x r \ {x})) < ε := by
  obtain ⟨R, hR, hRΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hxΩ)
  let A (k : ℕ) : Set Ω := ((↑) : Ω → E) ⁻¹' (closedBall x (R / ((k : ℝ) + 2)) \ {x})
  have hAm (k : ℕ) : NullMeasurableSet (A k) lam :=
    ((measurableSet_closedBall.diff (measurableSet_singleton x)).preimage
      continuous_subtype_val.measurable).nullMeasurableSet
  have hAanti : Antitone A := fun i j hij => preimage_mono (sdiff_subset_sdiff_left
    (closedBall_subset_closedBall (by gcongr)))
  have hA0fin : lam (A 0) ≠ ∞ := by
    have hK : IsCompact (((↑) : Ω → E) ⁻¹' closedBall x R) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x R)
        (by rwa [Subtype.range_coe])
    exact ((measure_mono (preimage_mono (sdiff_subset.trans
      (closedBall_subset_closedBall (div_le_self hR.le (by norm_num)))))).trans_lt
      hK.measure_lt_top).ne
  have hAiInter : ⋂ k, A k = ∅ := eq_empty_iff_forall_notMem.2 fun y hy => by
    have h0 : Tendsto (fun k : ℕ => R / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
    have hle : dist (y : E) x ≤ 0 :=
      ge_of_tendsto' h0 fun k => mem_closedBall.1 (mem_iInter.1 hy k).1
    exact (mem_iInter.1 hy 0).2 (dist_le_zero.1 hle)
  have hlim : Tendsto (fun k => lam (A k)) atTop (𝓝 0) := by
    simpa [Function.comp_def, hAiInter] using tendsto_measure_iInter_atTop hAm hAanti ⟨0, hA0fin⟩
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨R / ((k : ℝ) + 2), div_pos hR (by positivity),
    (closedBall_subset_closedBall (div_le_self hR.le (by linarith))).trans hRΩ, hk⟩

/-- In dimension `1`, every point of `reducedBoundary μ Ω s` (against an additive Haar measure `μ`)
is isolated in `reducedBoundary μ Ω s`. -/
private theorem exists_isolated_reducedBoundary_of_finrank_eq_one [μ.IsAddHaarMeasure]
    (hdim : finrank ℝ E = 1) {x : E} (hx : x ∈ reducedBoundary μ Ω s) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ reducedBoundary μ Ω s ∩ ball x r₀ = {x} := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set c := Measure.addHaarScalarFactor μ volume
  obtain ⟨rk, hrk, hrkΩ, hk⟩ := exists_measure_preimage_closedBall_sdiff_singleton_lt
    (variationMeasure μ Ω (s.indicator 1)) (reducedBoundary_subset hx)
    (ENNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume) :
      0 < (c : ℝ≥0∞))
  refine ⟨rk / 2, half_pos hrk, (closedBall_subset_closedBall (half_le_self hrk.le)).trans hrkΩ,
    Subset.antisymm (fun y ⟨hyB, hyx⟩ => ?_) (singleton_subset_iff.2 ⟨hx, mem_ball_self
      (half_pos hrk)⟩)⟩
  by_contra hyne
  set δ := min (dist y x) (rk / 2)
  have hδ : 0 < δ := lt_min (dist_pos.2 hyne) (half_pos hrk)
  have hsub : ball y δ ⊆ closedBall x rk \ {x} := fun z hz =>
    ⟨mem_closedBall.2 (calc dist z x ≤ dist z y + dist y x := dist_triangle z y x
      _ ≤ rk / 2 + rk / 2 := add_le_add ((mem_ball.1 hz).le.trans (min_le_right _ _))
          (mem_ball.1 hyx).le
      _ = rk := add_halves rk),
      fun hzx => (lt_irrefl (dist x y)) (by
        calc dist x y < δ := (mem_singleton_iff.1 hzx) ▸ mem_ball.1 hz
          _ ≤ dist y x := min_le_left _ _
          _ = dist x y := dist_comm y x)⟩
  have hbΩ : ball y δ ⊆ Ω := (hsub.trans sdiff_subset).trans hrkΩ
  have hlt : perimeter μ ⟨ball y δ, isOpen_ball⟩ s < c := by
    rw [perimeter_def, ← variationMeasure_preimage_coe (U := ⟨ball y δ, isOpen_ball⟩) hu hfin hbΩ]
    exact (measure_mono (preimage_mono hsub)).trans_lt hk
  have hge : (c : ℝ≥0∞) ≤ perimeter μ ⟨ball y δ, isOpen_ball⟩ s := by
    rw [Measure.isAddLeftInvariant_eq_smul μ volume, perimeter_smul_nnreal]
    simpa using mul_le_mul_right
      (one_le_perimeter_volume_ball_of_finrank_eq_one hdim hyB hδ hbΩ) (c : ℝ≥0∞)
  exact hlt.not_ge hge

/-- When `(f '' Ioo a b)` lies inside `ball x r₀ \ {x}` around an isolated point `x` of `∂*s`, the
pulled-back set `f ⁻¹' s` has zero perimeter on `(a, b)`. -/
private theorem perimeter_Ioo_preimage_eq_zero_of_isolated {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {Ω : Opens F} {s : Set F} {x : F} (hdim : finrank ℝ F = 1)
    (hx : x ∈ reducedBoundary volume Ω s) {r₀ : ℝ} (hr₀Ω : closedBall x r₀ ⊆ Ω)
    (hiso : reducedBoundary volume Ω s ∩ ball x r₀ = {x}) {a b : ℝ}
    (hab : ∀ t ∈ Ioo a b, |t| ∈ Ioo 0 r₀) :
    perimeter volume ⟨Ioo a b, isOpen_Ioo⟩
      (coordEquivOfFinrankEqOne hdim (norm_outerNormal hx) x ⁻¹' s) = 0 := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  let f := coordEquivOfFinrankEqOne hdim (norm_outerNormal hx) x
  have hfmp := measurePreserving_coordEquivOfFinrankEqOne hdim (norm_outerNormal hx) x
  have hf0 : f 0 = x := by simp [f, coordEquivOfFinrankEqOne_apply]
  let U : Opens F := Opens.comap ⟨f.symm, f.symm.continuous⟩ ⟨Ioo a b, isOpen_Ioo⟩
  have hcomap : Opens.comap ⟨f, f.continuous⟩ U = ⟨Ioo a b, isOpen_Ioo⟩ :=
    Opens.ext (by ext t; simp [U])
  have hUsub : (U : Set F) ⊆ ball x r₀ \ {x} := fun y hy => by
    have ht := hab (f.symm y) hy
    have hd : dist y x = |f.symm y| := by
      calc dist y x = dist (f (f.symm y)) (f 0) := by rw [f.apply_symm_apply, hf0]
        _ = |f.symm y| := by rw [f.dist_map, Real.dist_0_eq_abs]
    refine ⟨mem_ball.2 (hd ▸ ht.2), fun hyx => ?_⟩
    replace hyx := mem_singleton_iff.1 hyx
    subst hyx
    rw [dist_self] at hd
    exact ht.1.ne' hd.symm
  have hUΩ : U ≤ Ω := (hUsub.trans sdiff_subset).trans (ball_subset_closedBall.trans hr₀Ω)
  rw [← hcomap, f.perimeter_comap hfmp, perimeter_def, ← variationMeasure_preimage_coe hu hfin hUΩ]
  refine measure_mono_null ?_ (ae_iff.1 ae_mem_reducedBoundary)
  intro y hy hyB
  exact (hUsub hy).2 (mem_singleton_iff.1 (hiso.subset ⟨hyB, (hUsub hy).1⟩))

/-- On `(-r₀, r₀) ⊆ ℝ`, a set `T` that charges both `T` and `Tᶜ` and is null or conull on each of
`(-r₀, 0)` and `(0, r₀)` agrees up to null sets on `(-r₀, r₀)` with `(-∞, 0)` or `(0, ∞)`. -/
private theorem volume_symmDiff_Iio_or_Ioi_inter_Ioo_eq_zero {r₀ : ℝ} {T : Set ℝ}
    (hTpos1 : volume (T ∩ Ioo (-r₀) r₀) ≠ 0) (hTpos0 : volume (Ioo (-r₀) r₀ \ T) ≠ 0)
    (hPneg : volume (T ∩ Ioo (-r₀) 0) = 0 ∨ volume (Ioo (-r₀) 0 \ T) = 0)
    (hPpos : volume (T ∩ Ioo 0 r₀) = 0 ∨ volume (Ioo 0 r₀ \ T) = 0) :
    volume ((T ∆ Iio 0) ∩ Ioo (-r₀) r₀) = 0 ∨ volume ((T ∆ Ioi 0) ∩ Ioo (-r₀) r₀) = 0 := by
  have hcov {t : ℝ} (htI : t ∈ Ioo (-r₀) r₀) :
      t ∈ Ioo (-r₀) 0 ∨ t ∈ Ioo 0 r₀ ∨ t ∈ ({0} : Set ℝ) := by
    rcases lt_trichotomy t 0 with h | rfl | h
    exacts [.inl ⟨htI.1, h⟩, .inr (.inr rfl), .inr (.inl ⟨h, htI.2⟩)]
  have hs0 : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
  rcases hPneg with hneg0 | hneg1 <;> rcases hPpos with hpos0 | hpos1
  · refine (hTpos1 (measure_mono_null ?_
      (measure_union_null hneg0 (measure_union_null hpos0 hs0)))).elim
    intro t ht
    rcases hcov ht.2 with h | h | h
    exacts [.inl ⟨ht.1, h⟩, .inr (.inl ⟨ht.1, h⟩), .inr (.inr h)]
  · refine .inr (measure_mono_null ?_
      (measure_union_null hneg0 (measure_union_null hpos1 hs0)))
    intro t ht
    rcases hcov ht.2 with h | h | h
    · rcases ht.1 with ⟨htT, _⟩ | ⟨ht1, _⟩
      exacts [.inl ⟨htT, h⟩, absurd ht1 (not_lt.2 h.2.le)]
    · rcases ht.1 with ⟨_, ht1⟩ | ⟨_, htT⟩
      exacts [absurd h.1 ht1, .inr (.inl ⟨h, htT⟩)]
    · exact .inr (.inr h)
  · refine .inl (measure_mono_null ?_
      (measure_union_null hneg1 (measure_union_null hpos0 hs0)))
    intro t ht
    rcases hcov ht.2 with h | h | h
    · rcases ht.1 with ⟨_, ht1⟩ | ⟨_, htT⟩
      exacts [absurd h.2 ht1, .inl ⟨h, htT⟩]
    · rcases ht.1 with ⟨htT, _⟩ | ⟨ht1, _⟩
      exacts [.inr (.inl ⟨htT, h⟩), absurd ht1 (not_lt.2 h.1.le)]
    · exact .inr (.inr h)
  · refine (hTpos0 (measure_mono_null ?_
      (measure_union_null hneg1 (measure_union_null hpos1 hs0)))).elim
    intro t ht
    rcases hcov ht.1 with h | h | h
    exacts [.inl ⟨h, ht.2⟩, .inr (.inl ⟨h, ht.2⟩), .inr (.inr h)]

/-- In dimension `1`, near every point `x ∈ reducedBoundary volume Ω s`, `s` agrees a.e. on a ball
around `x` with a half-line `{y | ⟪y, w⟫ < ⟪x, w⟫}` for some unit vector `w`. -/
private theorem exists_ae_eq_setOf_inner_lt_ball_of_finrank_eq_one {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {Ω : Opens F} {s : Set F} {x : F} (hdim : finrank ℝ F = 1)
    (hx : x ∈ reducedBoundary volume Ω s) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ reducedBoundary volume Ω s ∩ ball x r₀ = {x} ∧
      ∃ w : F, ‖w‖ = 1 ∧ s =ᵐ[volume.restrict (ball x r₀)] {y | ⟪y, w⟫ < ⟪x, w⟫} := by
  obtain ⟨r₀, hr₀, hr₀Ω, hiso⟩ := exists_isolated_reducedBoundary_of_finrank_eq_one hdim hx
  set ν := outerNormal volume Ω s x
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  let f := coordEquivOfFinrankEqOne hdim hν x
  have hfmp := measurePreserving_coordEquivOfFinrankEqOne hdim hν x
  have hball : f ⁻¹' ball x r₀ = Ioo (-r₀) r₀ := by
    ext t; simp [f, coordEquivOfFinrankEqOne_apply, mem_ball, dist_eq_norm, norm_smul, hν, abs_lt]
  have hTm {a b : ℝ} (hsub : Ioo a b ⊆ Ioo (-r₀) r₀) :
      NullMeasurableSet (f ⁻¹' s ∩ Ioo a b) volume := by
    have hsΩ := nullMeasurableSet_inter_of_mem_reducedBoundary hx
    have h1 : NullMeasurableSet (f ⁻¹' s ∩ Ioo (-r₀) r₀) volume := by
      rw [← hball, ← preimage_inter, show s ∩ ball x r₀ = (s ∩ Ω) ∩ ball x r₀ by
        rw [inter_assoc, inter_eq_right.2 (ball_subset_closedBall.trans hr₀Ω)]]
      exact (hsΩ.inter measurableSet_ball.nullMeasurableSet).preimage hfmp.quasiMeasurePreserving
    exact (by rw [inter_assoc, inter_eq_right.2 hsub] :
      (f ⁻¹' s ∩ Ioo (-r₀) r₀) ∩ Ioo a b = f ⁻¹' s ∩ Ioo a b) ▸
      h1.inter measurableSet_Ioo.nullMeasurableSet
  have hemb := f.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have htrans {w : F} {J : Set ℝ} (hJ : ∀ y : F, (f.symm y ∈ J) ↔ ⟪y, w⟫ < ⟪x, w⟫)
      (h0 : volume (((f ⁻¹' s) ∆ J) ∩ Ioo (-r₀) r₀) = 0) :
      s =ᵐ[volume.restrict (ball x r₀)] {y | ⟪y, w⟫ < ⟪x, w⟫} := by
    rw [ae_eq_set, Measure.restrict_apply' measurableSet_ball,
      Measure.restrict_apply' measurableSet_ball, ← hfmp.measure_preimage_emb hemb,
      ← hfmp.measure_preimage_emb hemb]
    refine ⟨measure_mono_null ?_ h0, measure_mono_null ?_ h0⟩
    · intro t ⟨⟨hts, htw⟩, htb⟩
      exact ⟨.inl ⟨hts, fun htJ => htw ((hJ (f t)).1 (by simpa using htJ))⟩, hball ▸ htb⟩
    · intro t ⟨⟨htw, hts⟩, htb⟩
      exact ⟨.inr ⟨f.symm_apply_apply t ▸ (hJ (f t)).2 htw, hts⟩, hball ▸ htb⟩
  refine ⟨r₀, hr₀, hr₀Ω, hiso, ?_⟩
  rcases volume_symmDiff_Iio_or_Ioi_inter_Ioo_eq_zero
    (by rw [← hball, ← preimage_inter, hfmp.measure_preimage_emb hemb]
        exact (measure_inter_ball_pos hx hr₀).ne')
    (by rw [← hball, ← preimage_sdiff, hfmp.measure_preimage_emb hemb, Set.sdiff_eq, inter_comm]
        exact (measure_inter_ball_pos (by rwa [reducedBoundary_compl]) hr₀).ne')
    (volume_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_Ioo_eq_zero
      (hTm (Ioo_subset_Ioo_right hr₀.le))
      (perimeter_Ioo_preimage_eq_zero_of_isolated hdim hx hr₀Ω hiso fun t ht => by
        rw [abs_of_neg ht.2]; exact ⟨neg_pos.2 ht.2, neg_lt.2 ht.1⟩))
    (volume_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_Ioo_eq_zero
      (hTm (Ioo_subset_Ioo_left (neg_nonpos.2 hr₀.le)))
      (perimeter_Ioo_preimage_eq_zero_of_isolated hdim hx hr₀Ω hiso fun t ht => by
        rw [abs_of_pos ht.1]; exact ht))
    with h0 | h0
  · exact ⟨ν, hν, htrans (fun y => by simp [f, coordEquivOfFinrankEqOne_symm_apply, inner_sub_left])
      h0⟩
  · exact ⟨-ν, by simpa using hν, htrans (fun y => by
      simp [f, coordEquivOfFinrankEqOne_symm_apply, inner_sub_left, inner_neg_right]) h0⟩

/-- In dimension `1`, for small `r > 0` around `x ∈ reducedBoundary volume Ω s`,
`|Dχ_s|(closedBall x r)` equals the `0`-dimensional ball volume (`= 1`). -/
private theorem eventually_variationMeasure_closedBall_eq_volume_of_finrank_eq_one {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {Ω : Opens F} {s : Set F} {x : F} (hdim : finrank ℝ F = 1)
    (hx : x ∈ reducedBoundary volume Ω s) :
    ∀ᶠ r in 𝓝[>] 0,
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → F) ⁻¹' closedBall x r) =
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) r) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨r₀, hr₀, hr₀Ω, hiso, w, hw, hae⟩ :=
    exists_ae_eq_setOf_inner_lt_ball_of_finrank_eq_one hdim hx
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r ⟨hr, hrr₀⟩
  have hdiff0 : variationMeasure volume Ω (s.indicator 1)
      (((↑) : Ω → F) ⁻¹' closedBall x r \ ((↑) : Ω → F) ⁻¹' ball x r) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 ae_mem_reducedBoundary)
    intro y hy hyB
    have hyx : (y : F) = x :=
      mem_singleton_iff.1 (hiso.subset ⟨hyB, closedBall_subset_ball hrr₀ hy.1⟩)
    exact hy.2 (hyx.symm ▸ (mem_ball_self hr : x ∈ ball x r))
  have hbΩ : (⟨ball x r, isOpen_ball⟩ : Opens F) ≤ Ω :=
    (ball_subset_ball hrr₀.le).trans (ball_subset_closedBall.trans hr₀Ω)
  have heq_cb : variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → F) ⁻¹' closedBall x r) =
      perimeter volume ⟨ball x r, isOpen_ball⟩ s := by
    rw [← measure_inter_add_sdiff (((↑) : Ω → F) ⁻¹' closedBall x r)
      (isOpen_ball.preimage continuous_subtype_val).measurableSet, hdiff0, add_zero,
      ← preimage_inter, inter_eq_right.2 ball_subset_closedBall]
    exact (variationMeasure_preimage_coe (U := ⟨ball x r, isOpen_ball⟩) hu hfin hbΩ).trans
      perimeter_def.symm
  have hae_r : s =ᵐ[volume.restrict (ball x r)] {y | ⟪y, w⟫ < ⟪x, w⟫} :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrr₀.le) hae
  rw [heq_cb, perimeter_congr_ae hae_r, perimeter_ball_setOf_inner_lt hw x hr,
    Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le]

end OneDimSpace

/-! ### De Giorgi's rectifiability theorem -/

section Rectifiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {s : Set E}

/-- If the blow-up error `(s_{x,r} ∆ H) ∩ closedBall 0 2` has `C₀ * μ (...)` strictly below
`(1 / 2) ^ n` while `y` satisfies the uniform lower volume density bounds at scale `r / 2` with
`r = dist y x`, then `|⟪y - x, ν⟫| ≤ (1 / 2) * dist y x`. -/
private theorem abs_inner_sub_le_half_dist_of_blowUp {x y ν : E} (hν : ‖ν‖ = 1) {C₀ : ℝ≥0}
    (hlow1 : 0 < dist y x →
      ENNReal.ofReal ((dist y x / 2) ^ finrank ℝ E) ≤ C₀ * μ (s ∩ ball y (dist y x / 2)))
    (hlow0 : 0 < dist y x →
      ENNReal.ofReal ((dist y x / 2) ^ finrank ℝ E) ≤ C₀ * μ (ball y (dist y x / 2) \ s))
    (hblow : 0 < dist y x →
      (C₀ : ℝ≥0∞) * μ ((((fun z => x + dist y x • z) ⁻¹' s) ∆ {z | ⟪z, ν⟫ < 0}) ∩
        closedBall 0 2) < ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E)) :
    |⟪y - x, ν⟫| ≤ (1 / 2) * dist y x := by
  by_contra! hlt
  set r := dist y x
  have hr : 0 < r := by
    by_contra! hr0
    simp [r, dist_le_zero.1 hr0] at hlt
  let g : E → E := fun z => x + r • z
  let w : E := r⁻¹ • (y - x)
  have hw1 : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← dist_eq_norm, inv_mul_cancel₀ hr.ne']
  have hball_pre : g ⁻¹' ball y (r / 2) = ball w (1 / 2) := by
    have hgw : g w = y := by simp [g, w, smul_inv_smul₀ hr.ne']
    ext z
    rw [← hgw]
    simp only [g, mem_preimage, mem_ball, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hr.le]
    rw [show r / 2 = r * (1 / 2) by ring, mul_lt_mul_iff_right₀ hr]
  have hball_sub : ball w (1 / 2) ⊆ closedBall 0 2 := fun z hz => by
    rw [mem_closedBall_zero_iff]
    linarith [norm_sub_norm_le z w, hw1,
      show ‖z - w‖ < 1 / 2 by simpa [mem_ball, dist_eq_norm] using hz]
  have hscale {A : Set E} (hA : ENNReal.ofReal ((r / 2) ^ finrank ℝ E) ≤ C₀ * μ A)
      (hsub : g ⁻¹' A ⊆ ((g ⁻¹' s) ∆ {z | ⟪z, ν⟫ < 0}) ∩ closedBall 0 2) : False := by
    refine (hblow hr).not_ge ((?_ : ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) ≤
      C₀ * μ (g ⁻¹' A)).trans (mul_le_mul_right (measure_mono hsub) _))
    rw [Measure.addHaar_preimage_add_smul μ x hr.ne', abs_of_pos (inv_pos.2 (pow_pos hr _)),
      ← mul_assoc, mul_comm (C₀ : ℝ≥0∞), mul_assoc,
      show ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) =
        ENNReal.ofReal ((r ^ finrank ℝ E)⁻¹) * ENNReal.ofReal ((r / 2) ^ finrank ℝ E) by
        rw [← ENNReal.ofReal_mul (by positivity), div_pow, div_pow, one_pow,
          div_eq_mul_inv (r ^ _), inv_mul_cancel_left₀ (pow_ne_zero _ hr.ne'), one_div]]
    exact mul_le_mul_right hA _
  have hwν : 1 / 2 < |⟪w, ν⟫| := by
    rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.2 hr)]
    exact (lt_inv_mul_iff₀ hr).2 (by linarith)
  have hzw {z : E} (hzb : z ∈ ball w (1 / 2)) : |⟪z - w, ν⟫| < 1 / 2 :=
    (abs_real_inner_le_norm (z - w) ν).trans_lt (by simpa [hν, mem_ball, dist_eq_norm] using hzb)
  rcases lt_abs.1 hwν with hpos | hneg
  · exact hscale (hlow1 hr) (by
      rw [preimage_inter, hball_pre]
      exact fun z ⟨hzs, hzb⟩ => ⟨.inl ⟨hzs, fun (hzν : ⟪z, ν⟫ < 0) => by
        have : ⟪z, ν⟫ = ⟪w, ν⟫ + ⟪z - w, ν⟫ := by rw [← inner_add_left, add_sub_cancel]
        linarith [(abs_lt.1 (hzw hzb)).1]⟩, hball_sub hzb⟩)
  · exact hscale (hlow0 hr) (by
      rw [preimage_sdiff, hball_pre]
      exact fun z ⟨hzb, hzs⟩ => ⟨.inr ⟨show ⟪z, ν⟫ < 0 by
        have : ⟪z, ν⟫ = ⟪w, ν⟫ + ⟪z - w, ν⟫ := by rw [← inner_add_left, add_sub_cancel]
        linarith [(abs_lt.1 (hzw hzb)).2], hzs⟩, hball_sub hzb⟩)


/-- De Giorgi's rectifiability theorem in dimension `n ≥ 2`. -/
private theorem countablyRectifiable_reducedBoundary_of_two_le (hn : 2 ≤ finrank ℝ E) :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  set p := NNReal.conjExponent (finrank ℝ E)
  have hp : NNReal.HolderConjugate (finrank ℝ E) p := .conjExponent (by exact_mod_cast hn)
  set C₁ : ℝ≥0 := (1 + 2) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p
  set C₀ : ℝ≥0 := C₁ ^ finrank ℝ E
  let piece (N : ℕ) : Set E :=
    {x ∈ reducedBoundary μ Ω s | ∀ r ∈ Ioo (0 : ℝ) (1 / ((N : ℝ) + 1)),
      ENNReal.ofReal (r ^ finrank ℝ E) ≤ C₀ * μ (s ∩ ball x r) ∧
      ENNReal.ofReal (r ^ finrank ℝ E) ≤ C₀ * μ (ball x r \ s)}
  have hrect (N : ℕ) : CountablyRectifiable (finrank ℝ E - 1) (piece N) := by
    refine CountablyRectifiable.of_forall_exists_inner_le fun x hx => ?_
    have hlim : Tendsto (fun r : ℝ => (C₀ : ℝ≥0∞) *
        μ ((((fun z => x + r • z) ⁻¹' s) ∆ {z | ⟪z, outerNormal μ Ω s x⟫ < 0}) ∩
          closedBall 0 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul
        (tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx.1
          (isCompact_closedBall 0 2)) (.inr ENNReal.coe_ne_top)
    obtain ⟨δ, hδ, hδb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (pow_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (finrank ℝ E)))))
    refine ⟨outerNormal μ Ω s x, norm_outerNormal hx.1, 1 / 2, by norm_num,
      min δ (1 / ((N : ℝ) + 1)), lt_min hδ (by positivity), fun y hy hyx => ?_⟩
    have hr_mem {r : ℝ} (hr0 : 0 < r) (hrx : r ≤ dist y x) :
        r / 2 ∈ Ioo (0 : ℝ) (1 / ((N : ℝ) + 1)) :=
      ⟨half_pos hr0, (half_lt_self hr0).trans (hrx.trans_lt (hyx.trans_le (min_le_right _ _)))⟩
    exact abs_inner_sub_le_half_dist_of_blowUp (norm_outerNormal hx.1)
      (fun hr0 => (hy.2 _ (hr_mem hr0 le_rfl)).1)
      (fun hr0 => (hy.2 _ (hr_mem hr0 le_rfl)).2)
      (fun hr0 => hδb ⟨hr0, hyx.trans_le (min_le_left _ _)⟩)
  refine (CountablyRectifiable.iUnion hrect).mono fun x hx => mem_iUnion.2 ?_
  obtain ⟨δ, hδ, hδb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    ((eventually_ofReal_pow_le_mul_measure_inter_ball hp hx one_lt_two).and
      (eventually_ofReal_pow_le_mul_measure_ball_sdiff hp hx one_lt_two))
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  have hNδ : 1 / ((N : ℝ) + 1) < δ := by
    simpa using inv_lt_of_inv_lt₀ hδ (hN.trans (lt_add_one _))
  exact ⟨N, hx, fun r hr => by
    have hb : ENNReal.ofReal (r ^ finrank ℝ E) ≤ _ ∧ _ := hδb ⟨hr.1, hr.2.trans hNδ⟩
    simpa only [C₀, C₁, ENNReal.coe_pow] using hb⟩

/-- **De Giorgi's rectifiability theorem.** Let `μ` be an additive Haar measure on a
finite-dimensional real inner product space `E` of dimension `n`, let `Ω` be an open set of `E`,
and let `s ⊆ E`. The reduced boundary `∂*s` (`TauCeti.reducedBoundary μ Ω s`) is countably
`(n - 1)`-rectifiable. No finiteness or measurability hypothesis on `s` and no dimension
restriction on `E` are required. -/
theorem countablyRectifiable_reducedBoundary :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  rcases lt_trichotomy (finrank ℝ E) 1 with h0 | h1 | h2
  · have hempty : reducedBoundary μ Ω s = ∅ := eq_empty_iff_forall_notMem.2 fun x hx => by
      have : Subsingleton E := finrank_zero_iff.1 (Nat.lt_one_iff.1 h0)
      have hν := norm_outerNormal hx
      simp [Subsingleton.elim (outerNormal μ Ω s x) 0] at hν
    rw [hempty]
    exact .empty
  · refine CountablyRectifiable.of_forall_exists_inner_le fun x hx => ?_
    obtain ⟨r₀, hr₀, -, hiso⟩ := exists_isolated_reducedBoundary_of_finrank_eq_one h1 hx
    refine ⟨outerNormal μ Ω s x, norm_outerNormal hx, 0, zero_lt_one, r₀, hr₀, fun y hy hyx => ?_⟩
    have hyx' : y = x := mem_singleton_iff.1 (hiso.subset ⟨hy, hyx⟩)
    simp [hyx']
  · exact countablyRectifiable_reducedBoundary_of_two_le h2

end Rectifiability

/-! ### Identification of the perimeter measure with `Hⁿ⁻¹⌊∂*s` -/

section StructureTheorem

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {Ω : Opens F} {s : Set F}

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem euclideanHausdorffMeasure_image_coe_opens (Ω : Opens F) {k : ℕ} (A : Set Ω) :
    μHE[k] (((↑) : Ω → F) '' A) = μHE[k] A :=
  Isometry.euclideanHausdorffMeasure_image (f := ((↑) : Ω → F)) (fun _ _ => rfl) A

/-- In every dimension `n ≥ 0`, at every point `x ∈ reducedBoundary volume Ω s`,
`|Dχ_s|(closedBall x r) / (ω_{n-1} r ^ (n - 1)) → 1` as `r → 0⁺`. -/
private theorem tendsto_variationMeasure_closedBall_div_all {x : F}
    (hx : x ∈ reducedBoundary volume Ω s) :
    Tendsto (fun r =>
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → F) ⁻¹' closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) r)) (𝓝[>] 0) (𝓝 1) := by
  rcases lt_trichotomy (finrank ℝ F) 1 with h0 | h1 | h2
  · have : Subsingleton F := finrank_zero_iff.1 (Nat.lt_one_iff.1 h0)
    have hν := norm_outerNormal hx
    simp [Subsingleton.elim (outerNormal volume Ω s x) 0] at hν
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_variationMeasure_closedBall_eq_volume_of_finrank_eq_one h1 hx,
      self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
    rw [hr, ENNReal.div_self (measure_closedBall_pos _ _ hr0).ne' measure_closedBall_lt_top.ne]
  · exact tendsto_variationMeasure_closedBall_div_volume_closedBall h2 hx

/-- Lower bound
`(μHE[n - 1] : Measure Ω).restrict (∂*s) ≤ variationMeasure volume Ω (s.indicator 1)`
from the pointwise density `1` of `|Dχ_s|` on `∂*s`. -/
private theorem restrict_preimage_reducedBoundary_le_variationMeasure :
    (μHE[finrank ℝ F - 1] : Measure Ω).restrict (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s) ≤
      variationMeasure volume Ω (s.indicator 1) := by
  have := Ω.isOpen.locallyCompactSpace
  set k := finrank ℝ F - 1
  set BΩ : Set Ω := ((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s
  set lam := variationMeasure volume Ω (s.indicator 1)
  refine Measure.le_iff.2 fun A hAm => ?_
  rw [Measure.restrict_apply hAm]
  set c : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (1 - 1 / ((m : ℝ) + 2))
  have hle (m : ℕ) : c m * μHE[k] (A ∩ BΩ) ≤ lam A := by
    have hc1 : c m < 1 := ENNReal.ofReal_lt_one.2 (sub_lt_self 1 (by positivity))
    refine (Measure.mul_euclideanHausdorffMeasure_le_measure lam k fun y hy => ?_).trans
      (measure_mono inter_subset_left)
    have hlim := tendsto_variationMeasure_closedBall_div_all hy.2
    refine ((hlim.eventually (lt_mem_nhds hc1)).and self_mem_nhdsWithin).frequently.mp
      (.of_forall fun r ⟨hlt, (hr0 : 0 < r)⟩ => ?_)
    rw [Subtype.preimage_closedBall] at hlt
    exact (ENNReal.le_div_iff_mul_le (.inl (measure_closedBall_pos _ _ hr0).ne')
      (.inl measure_closedBall_lt_top.ne)).1 hlt.le
  have hclim : Tendsto (fun m => c m * μHE[k] (A ∩ BΩ)) atTop (𝓝 (μHE[k] (A ∩ BΩ))) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) - 1 / ((m : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds))
    rw [sub_zero] at h1
    have hc : Tendsto c atTop (𝓝 1) := by simpa [c] using ENNReal.tendsto_ofReal h1
    simpa using ENNReal.Tendsto.mul_const hc (.inl (by simp))
  exact le_of_tendsto' hclim hle

/-- On any open ball `ball x ρ` whose closed ball lies in `Ω`, almost every point of `∂*s` for
`μ₀ = (μHE[n - 1] : Measure Ω).restrict (∂*s)` has `μ₀`-density `1`. -/
private theorem measure_setOf_not_tendsto_eq_zero_of_closedBall_subset {x : Ω} {ρ : ℝ}
    (hρΩ : closedBall (x : F) ρ ⊆ Ω) :
    ((μHE[finrank ℝ F - 1] : Measure Ω).restrict (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s))
      {y ∈ ball x ρ | ¬Tendsto (fun r =>
        ((μHE[finrank ℝ F - 1] : Measure Ω).restrict
          (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s)) (closedBall y r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) r))
        (𝓝[>] 0) (𝓝 1)} = 0 := by
  have := Ω.isOpen.locallyCompactSpace
  set k := finrank ℝ F - 1
  set B := reducedBoundary volume Ω s
  set BΩ : Set Ω := ((↑) : Ω → F) ⁻¹' B
  set μ₀ : Measure Ω := (μHE[k] : Measure Ω).restrict BΩ
  have : IsLocallyFiniteMeasure μ₀ :=
    Measure.isLocallyFiniteMeasure_of_le restrict_preimage_reducedBoundary_le_variationMeasure
  set E₀ : Set F := B ∩ closedBall (x : F) ρ
  have hK : IsCompact (closedBall x ρ) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall (x : F) ρ)
      (by rwa [Subtype.range_coe])
  have hE₀img : ((↑) : Ω → F) '' (BΩ ∩ closedBall x ρ) = E₀ := by
    ext z
    exact ⟨by rintro ⟨y, ⟨hyB, hyc⟩, rfl⟩; exact ⟨hyB, hyc⟩,
      fun ⟨hzB, hzc⟩ => ⟨⟨z, hρΩ hzc⟩, ⟨hzB, hzc⟩, rfl⟩⟩
  have hE₀fin : Fact (μHE[k] E₀ < ∞) := ⟨by
    rw [← hE₀img, euclideanHausdorffMeasure_image_coe_opens Ω,
      inter_comm, ← Measure.restrict_apply isClosed_closedBall.measurableSet]
    exact hK.measure_lt_top⟩
  have hae := ((countablyRectifiable_reducedBoundary (μ := volume) (Ω := Ω) (s := s)).mono
    (inter_subset_left : E₀ ⊆ B)).ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    (measurableSet_reducedBoundary.inter isClosed_closedBall.measurableSet).nullMeasurableSet
  let M : Set Ω := {y ∈ ball x ρ ∩ BΩ | ¬Tendsto (fun r =>
    μ₀ (closedBall y r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1)}
  have hM0 : (μHE[k] : Measure Ω) M = 0 := by
    rw [← euclideanHausdorffMeasure_image_coe_opens Ω]
    refine measure_mono_null (by
      rintro z ⟨y, ⟨⟨hyb, hyB⟩, hynot⟩, rfl⟩ hz
      refine hynot ((hz ⟨hyB, ball_subset_closedBall hyb⟩).congr' ?_)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (eventually_closedBall_subset
          (isOpen_ball.mem_nhds (show (y : F) ∈ ball (x : F) ρ from hyb)))] with r hr
      have himg : ((↑) : Ω → F) '' (closedBall y r ∩ BΩ) = E₀ ∩ closedBall (y : F) r := by
        ext w
        exact ⟨by rintro ⟨u, ⟨huc, huB⟩, rfl⟩; exact ⟨⟨huB, ball_subset_closedBall (hr huc)⟩, huc⟩,
          fun ⟨⟨huB, _⟩, huc⟩ => ⟨⟨w, hρΩ (ball_subset_closedBall (hr huc))⟩, ⟨huc, huB⟩, rfl⟩⟩
      rw [Measure.restrict_apply isClosed_closedBall.measurableSet,
        ← euclideanHausdorffMeasure_image_coe_opens Ω, himg])
      (ae_iff.1 hae)
  have hBΩm : MeasurableSet BΩ :=
    measurableSet_reducedBoundary.preimage continuous_subtype_val.measurable
  rw [Measure.restrict_apply' hBΩm]
  refine measure_mono_null ?_ hM0
  exact fun y hy => ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩

/-- Almost every point of `Ω` for `μ₀ = (μHE[n - 1] : Measure Ω).restrict (∂*s)` has `(n - 1)`-ball
density `1`. -/
private theorem ae_tendsto_restrict_reducedBoundary_closedBall_div :
    ∀ᵐ y : Ω ∂(μHE[finrank ℝ F - 1] : Measure Ω).restrict
        (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s),
      Tendsto (fun r =>
        ((μHE[finrank ℝ F - 1] : Measure Ω).restrict
          (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s)) (closedBall y r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) r))
        (𝓝[>] 0) (𝓝 1) := by
  set k := finrank ℝ F - 1
  set μ₀ : Measure Ω := (μHE[k] : Measure Ω).restrict
    (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s)
  choose ρ hρ0 hρΩ using fun x : Ω =>
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds x.2)
  obtain ⟨T, hTc, hTcov⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : Ω => ball x (ρ x)) (fun _ => isOpen_ball)
  have hcover (y : Ω) : ∃ x : T, y ∈ ball x.1 (ρ x.1) := by
    have hy : y ∈ ⋃ i ∈ T, ball i (ρ i) := hTcov.symm ▸ mem_iUnion.2 ⟨y, mem_ball_self (hρ0 y)⟩
    obtain ⟨x, hxT, hxy⟩ := mem_iUnion₂.1 hy
    exact ⟨⟨x, hxT⟩, hxy⟩
  have : Countable T := hTc.to_subtype
  have hall : ∀ᵐ y : Ω ∂μ₀, ∀ x : T, y ∈ ball x.1 (ρ x.1) →
      Tendsto (fun r => μ₀ (closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) :=
    ae_all_iff.2 fun x => ae_iff.2 (by
      simpa [not_imp] using measure_setOf_not_tendsto_eq_zero_of_closedBall_subset (hρΩ x.1))
  filter_upwards [hall] with y hy
  obtain ⟨x, hx⟩ := hcover y
  exact hy x hx

/-- Absolute continuity
`variationMeasure volume Ω (s.indicator 1) ≪ (μHE[n - 1] : Measure Ω).restrict (∂*s)`. -/
private theorem variationMeasure_absolutelyContinuous_restrict_reducedBoundary :
    variationMeasure volume Ω (s.indicator 1) ≪
      (μHE[finrank ℝ F - 1] : Measure Ω).restrict
        (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s) := by
  set BΩ : Set Ω := ((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s
  have hBΩm : MeasurableSet BΩ :=
    measurableSet_reducedBoundary.preimage continuous_subtype_val.measurable
  refine Measure.AbsolutelyContinuous.mk fun A _ hA0 => ?_
  rw [Measure.restrict_apply' hBΩm,
    ← euclideanHausdorffMeasure_image_coe_opens Ω,
    Measure.euclideanHausdorffMeasure_eq_zero_iff] at hA0
  have hAB : variationMeasure volume Ω (s.indicator 1) (A ∩ BΩ) = 0 := by
    have hbound := variationMeasure_preimage_le_mul_hausdorffMeasure (μ := volume) (Ω := Ω)
      (s := s) (A := ((↑) : Ω → F) '' (A ∩ BΩ)) (by rintro _ ⟨y, ⟨_, hyB⟩, rfl⟩; exact hyB)
    rw [preimage_image_eq _ Subtype.val_injective, hA0, mul_zero] at hbound
    exact nonpos_iff_eq_zero.1 hbound
  exact measure_mono_null (fun y hy => by
    by_cases hyB : y ∈ BΩ
    exacts [.inl ⟨hy, hyB⟩, .inr hyB])
    (measure_union_null hAB (ae_iff.1 ae_mem_reducedBoundary))

/-- **De Giorgi's structure theorem, measure form on `Ω`.** For any open set `Ω ⊆ F` of a
finite-dimensional real inner product space `F` of dimension `n` and any `s ⊆ F`, the perimeter
measure `|Dχ_s|` on `Ω` is the restriction of the normalized `(n - 1)`-dimensional Euclidean
Hausdorff measure `μHE[n - 1]` to `∂*s`:
`variationMeasure volume Ω (s.indicator 1) =
  (μHE[finrank ℝ F - 1] : Measure Ω).restrict ((↑) ⁻¹' reducedBoundary volume Ω s)`. -/
theorem variationMeasure_indicator_eq_restrict_reducedBoundary (Ω : Opens F) (s : Set F) :
    variationMeasure volume Ω (s.indicator 1) =
      (μHE[finrank ℝ F - 1] : Measure Ω).restrict
        (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s) := by
  have := Ω.isOpen.locallyCompactSpace
  set k := finrank ℝ F - 1
  set BΩ : Set Ω := ((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s
  set lam := variationMeasure volume Ω (s.indicator 1)
  set μ₀ : Measure Ω := (μHE[k] : Measure Ω).restrict BΩ
  have : IsLocallyFiniteMeasure μ₀ :=
    Measure.isLocallyFiniteMeasure_of_le restrict_preimage_reducedBoundary_le_variationMeasure
  have hBΩm : MeasurableSet BΩ :=
    measurableSet_reducedBoundary.preimage continuous_subtype_val.measurable
  refine (Measure.rnDeriv_eq_one_iff_eq
    variationMeasure_absolutelyContinuous_restrict_reducedBoundary).mp ?_
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv lam μ₀,
    ae_tendsto_restrict_reducedBoundary_closedBall_div, ae_restrict_mem hBΩm]
    with y hrn hμ₀ hyB
  have hlam : Tendsto (fun r => lam (closedBall y r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Subtype.preimage_closedBall] using tendsto_variationMeasure_closedBall_div_all hyB
  have hdiv : Tendsto (fun r => (lam (closedBall y r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) /
      (μ₀ (closedBall y r) / volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using ENNReal.Tendsto.div hlam (.inl one_ne_zero) hμ₀ (.inl ENNReal.one_ne_top)
  refine tendsto_nhds_unique hrn (hdiv.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r (hr0 : 0 < r)
  set ω := volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)
  have hω0 : ω ≠ 0 := (measure_closedBall_pos _ _ hr0).ne'
  have hωtop : ω ≠ ∞ := measure_closedBall_lt_top.ne
  rw [div_eq_mul_inv, div_eq_mul_inv (μ₀ _), div_eq_mul_inv (lam _),
    ENNReal.mul_inv (.inr (ENNReal.inv_ne_top.2 hω0)) (.inr (ENNReal.inv_ne_zero.2 hωtop)),
    inv_inv, mul_assoc, ← mul_assoc ω⁻¹, mul_right_comm ω⁻¹, ENNReal.inv_mul_cancel hω0 hωtop,
    one_mul, ← div_eq_mul_inv]

/-- **De Giorgi's structure theorem, set evaluation form.** For any open set `Ω ⊆ F` and any sets
`s, A ⊆ F`, the perimeter measure of `A` in `Ω` equals the `(n - 1)`-dimensional Euclidean
Hausdorff measure of `A ∩ ∂*s`. Neither `s` nor `A` need be measurable. -/
theorem variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary
    (Ω : Opens F) (s A : Set F) :
    variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → F) ⁻¹' A) =
      μHE[finrank ℝ F - 1] (A ∩ reducedBoundary volume Ω s) := by
  have hBΩm : MeasurableSet (((↑) : Ω → F) ⁻¹' reducedBoundary volume Ω s) :=
    measurableSet_reducedBoundary.preimage continuous_subtype_val.measurable
  have himg : ((↑) : Ω → F) '' (((↑) : Ω → F) ⁻¹' (A ∩ reducedBoundary volume Ω s)) =
      A ∩ reducedBoundary volume Ω s :=
    image_preimage_eq_of_subset (by
      rw [Subtype.range_coe]
      exact inter_subset_right.trans reducedBoundary_subset)
  rw [variationMeasure_indicator_eq_restrict_reducedBoundary, Measure.restrict_apply' hBΩm,
    ← preimage_inter, ← euclideanHausdorffMeasure_image_coe_opens Ω, himg]

/-- **De Giorgi's structure theorem, ambient measure form.** Pushing the perimeter measure on `Ω`
forward to `F` gives `(μHE[finrank ℝ F - 1] : Measure F).restrict (reducedBoundary volume Ω s)`. -/
theorem map_variationMeasure_indicator_eq_restrict_reducedBoundary (Ω : Opens F) (s : Set F) :
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → F) =
      (μHE[finrank ℝ F - 1] : Measure F).restrict (reducedBoundary volume Ω s) := by
  refine Measure.ext fun A hAm => ?_
  rw [Measure.map_apply continuous_subtype_val.measurable hAm,
    variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary,
    Measure.restrict_apply hAm]

/-- **De Giorgi's perimeter formula on open subsets.** If `s` is null-measurable on `Ω` with
locally finite perimeter in `Ω`, then for every open set `U ≤ Ω`,
`P(s; U) = Hⁿ⁻¹(U ∩ ∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary
    (hs : NullMeasurableSet s (volume.restrict Ω))
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens F, K ⊆ (U : Set F) ∧ perimeter volume U s ≠ ∞)
    {U : Opens F} (hU : U ≤ Ω) :
    perimeter volume U s = μHE[finrank ℝ F - 1] ((U : Set F) ∩ reducedBoundary volume Ω s) := by
  have hli : LocallyIntegrableOn (s.indicator (1 : F → ℝ)) Ω volume :=
    locallyIntegrableOn_indicator_const hs 1
  simp_rw [perimeter_def] at hfin ⊢
  rw [← variationMeasure_preimage_coe hli hfin hU,
    variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary]

/-- **De Giorgi's perimeter formula.** If `s` is null-measurable on `Ω` with locally finite
perimeter in `Ω`, then `P(s; Ω) = Hⁿ⁻¹(∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_reducedBoundary
    (hs : NullMeasurableSet s (volume.restrict Ω))
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens F, K ⊆ (U : Set F) ∧ perimeter volume U s ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ F - 1] (reducedBoundary volume Ω s) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary hs hfin le_rfl,
    inter_eq_right.2 reducedBoundary_subset]

/-- **The De Giorgi–Gauss–Green formula, indicator form.** Let `s` be null-measurable on `Ω` with
locally finite perimeter in `Ω`. For every `C¹` vector field `φ : F → F` with compact support in
`Ω`,
`∫ x, div φ x * χ_s x = ∫ x in ∂*s, ⟪φ x, ν_s x⟫ dHⁿ⁻¹`,
where `div φ = tr (Dφ)`. -/
theorem integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal
    (hs : NullMeasurableSet s (volume.restrict Ω))
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens F, K ⊆ (U : Set F) ∧ perimeter volume U s ≠ ∞)
    {φ : F → F} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ F (fderiv ℝ φ x : F →ₗ[ℝ] F) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s,
        ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ F - 1] := by
  have hli : LocallyIntegrableOn (s.indicator (1 : F → ℝ)) Ω volume :=
    locallyIntegrableOn_indicator_const hs 1
  simp_rw [perimeter_def] at hfin
  set B := reducedBoundary volume Ω s
  let g : F → ℝ := fun x => ⟪φ x, B.indicator (outerNormal volume Ω s) x⟫
  have hgm : StronglyMeasurable g :=
    hφ.continuous.stronglyMeasurable.inner measurable_indicator_outerNormal.stronglyMeasurable
  rw [integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hli hfin hφ hc hφΩ]
  have hrhs : ∫ x in B, ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ F - 1] =
      ∫ x, g x ∂(variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → F) := by
    rw [map_variationMeasure_indicator_eq_restrict_reducedBoundary]
    exact setIntegral_congr_fun measurableSet_reducedBoundary fun x hx => by
      simp [g, indicator_of_mem hx]
  rw [hrhs, integral_map continuous_subtype_val.aemeasurable hgm.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_reducedBoundary] with y hy
  simp [g, B, indicator_of_mem hy]

/-- **The De Giorgi–Gauss–Green formula.** Let `s` be null-measurable on `Ω` with locally finite
perimeter in `Ω`. For every `C¹` vector field `φ : F → F` with compact support in `Ω`,
`∫ x in s, div φ x = ∫ x in ∂*s, ⟪φ x, ν_s x⟫ dHⁿ⁻¹`,
where `div φ = tr (Dφ)`. -/
theorem setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal
    (hs : NullMeasurableSet s (volume.restrict Ω))
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens F, K ⊆ (U : Set F) ∧ perimeter volume U s ≠ ∞)
    {φ : F → F} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    ∫ x in s, LinearMap.trace ℝ F (fderiv ℝ φ x : F →ₗ[ℝ] F) =
      ∫ x in reducedBoundary volume Ω s,
        ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ F - 1] := by
  rw [← integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hs hfin hφ hc hφΩ]
  have hsΩ : NullMeasurableSet ((Ω : Set F) ∩ s) volume :=
    inter_comm (Ω : Set F) s ▸
      (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1 hs
  have hzero {x : F} (hx : x ∉ (Ω : Set F)) :
      LinearMap.trace ℝ F (fderiv ℝ φ x : F →ₗ[ℝ] F) = 0 := by
    have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hφΩ h)
    simp [h0.fderiv_eq]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero hx),
    Measure.restrict_restrict Ω.isOpen.measurableSet, ← integral_indicator₀ hsΩ]
  refine integral_congr_ae (.of_forall fun x => ?_)
  by_cases hxΩ : x ∈ (Ω : Set F) <;> by_cases hxs : x ∈ s <;> simp [hxΩ, hxs, hzero]

/-- **The De Giorgi–Gauss–Green formula for test vector fields.** For `s` null-measurable on `Ω`
with locally finite perimeter in `Ω` and `φ ∈ 𝓓(Ω, F)`,
`∫ x in s, divergenceCLM φ x = ∫ x in ∂*s, ⟪φ x, ν_s x⟫ dHⁿ⁻¹`. -/
theorem setIntegral_divergenceCLM_eq_setIntegral_inner_outerNormal
    (hs : NullMeasurableSet s (volume.restrict Ω))
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens F, K ⊆ (U : Set F) ∧ perimeter volume U s ≠ ∞) (φ : 𝓓(Ω, F)) :
    ∫ x in s, divergenceCLM φ x =
      ∫ x in reducedBoundary volume Ω s,
        ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ F - 1] := by
  simp_rw [divergenceCLM_apply]
  exact setIntegral_trace_fderiv_eq_setIntegral_inner_outerNormal hs hfin
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset

end StructureTheorem

end TauCeti
