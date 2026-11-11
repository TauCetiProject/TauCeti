/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.RealBoundaryReflection
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Complex.Wirtinger.Similarity.Examples
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear Cauchy–Riemann equations with a real boundary condition: reflection

Let `F` be a finite-dimensional complex space whose real structure is its `star` operation, so
that `x : F` is real when `star x = x`. A solution `ξ` of the linear Cauchy–Riemann equation
`∂ₛξ + i ∂ₜξ + C(z) ξ = 0` on the closed upper part `Ω ∩ {0 ≤ im}` of a conjugation-invariant
open set `Ω`, real on the real axis, is reflected to a solution on all of `Ω`: the reflection
`TauCeti.starSchwarzReflection ξ` (`ξ z` on `0 ≤ im`, `star (ξ (conj z))` below) solves the same
kind of equation with the reflected coefficient `TauCeti.starSchwarzReflectionCoeff C`, which is
`C z` on `0 ≤ im` and `star ∘ C (conj z) ∘ star` below. This is the reflection step of the
boundary version of the similarity principle and unique continuation (PH3.5 in the
PseudoholomorphicCurveAnalysis roadmap), in the model where the structure is `i` everywhere.

The weak equation on the half-plane part is
`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z))`, the weak
form of `\bar∂ξ = -C ξ / 2` with the real boundary condition encoded by the test functions; in
McDuff–Salamon's normalization `∂ₛ + i ∂ₜ = 2 \bar∂` this is `∂ₛξ + i ∂ₜξ + C ξ = 0`.

## Main results

* `TauCeti.starSchwarzReflectionCoeff`: the reflected coefficient field, and
  `TauCeti.starSchwarzReflection_clm_apply`, the pointwise identity
  `R (C ξ) = (R C) (R ξ)`.
* `TauCeti.MemLpLoc.starSchwarzReflection`, `TauCeti.MemLpLoc.starSchwarzReflectionCoeff`: local
  `Lᵖ` bounds up to the boundary transfer to the doubled domain.
* `TauCeti.continuousOn_starSchwarzReflection_of_symmetric`: continuity up to the boundary and
  real boundary values give continuity of the reflection.
* `HasWeakConjWirtingerDerivRealBoundaryOn.isWeakLinearCauchyRiemannOn_starSchwarzReflection`:
  for `1 < p < ∞`, a continuous solution real on the axis with coefficient locally `Lᵖ` up to the
  boundary reflects to a weak solution
  `TauCeti.IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • id) (R C) (R ξ)` on `Ω`.
* `TauCeti.eqOn_zero_starSchwarzReflection_of_subset` and
  `TauCeti.isBigO_starSchwarzReflection`: vanishing on an open subset of the upper half, and
  vanishing to order `n` at a point of the closed upper half-plane within it, pass to the
  reflection, so the interior unique continuation theorems apply to it.
* Checks: the reflected coefficient of `0` is `0` and the reflection of `z` solves the reflected
  equation; the constant real coefficient `2` and `z e^{-conj z}` are fixed by the reflections, and
  the reflection of `z e^{-conj z}` solves the reflected equation; the constant coefficient `i` is
  reflected to `-i` below the axis, so the coefficient is genuinely conjugated.

Only the structure `i` is treated: a variable structure equal to `i` on the axis is first
trivialized to `i`, which is not done here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Section 2.3 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace Set Filter Topology Asymptotics
open scoped ComplexConjugate ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Products with continuous maps and regularity in finite dimension -/

/-- The product of a locally `Lᵖ` coefficient field and a continuous map is locally `Lᵖ`. -/
private theorem memLpLoc_clm_apply {p : ℝ≥0∞} {U : Set ℂ} {A : ℂ → F →L[ℝ] F} {u : ℂ → F}
    (hA : MemLpLoc p U A) (hu : ContinuousOn u U) : MemLpLoc p U (fun z ↦ A z (u z)) := by
  refine memLpLoc_iff.2 fun K hKU hK ↦ ?_
  have hAK := memLpLoc_iff.1 hA K hKU hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hu.mono hKU)
  have huK : AEStronglyMeasurable u (volume.restrict K) :=
    (hu.mono hKU).aestronglyMeasurable hK.isClosed.measurableSet
  refine hAK.of_le_mul (c := M)
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hAK.aestronglyMeasurable.prodMk huK)) ?_
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
  calc ‖A z (u z)‖ ≤ ‖A z‖ * ‖u z‖ := (A z).le_opNorm _
    _ ≤ ‖A z‖ * M := by gcongr; exact hM z hz
    _ = M * ‖A z‖ := mul_comm _ _

/-- Interior `W^{1,p}` regularity for `\bar∂` with finite-dimensional complex coefficients, by
transport to a Euclidean space. -/
private theorem memWkpLoc_one_of_hasWeakConjWirtingerDerivOn [FiniteDimensional ℂ F]
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ} {u f : ℂ → F}
    (hu : MemLpLoc p Ω u) (hf : MemLpLoc p Ω f)
    (h : HasWeakConjWirtingerDerivOn volume Ω u f) : MemWkpLoc p Ω 1 u := by
  let e : F ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let L : F →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) := e
  have hu' : MemLpLoc p Ω (fun z ↦ L (u z)) := hu.clm_comp (L.restrictScalars ℝ)
  have hf' : MemLpLoc p Ω (fun z ↦ L (f z)) := hf.clm_comp (L.restrictScalars ℝ)
  have h' := (h.clm_comp L).memWkpLoc_one hp hp_top hu' hf'
  have := FiniteDimensional.complete ℂ F
  have h'' := h'.clm_comp ((e.symm : _ →L[ℂ] F).restrictScalars ℝ)
  simpa [L] using h''

variable [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F]

/-! ### The reflected coefficient -/

/-- Conjugation of a real-linear endomorphism by `star`, as a continuous linear map on the space
of endomorphisms: `A ↦ star ∘ A ∘ star`. -/
private def starConjCLM : (F →L[ℝ] F) →L[ℝ] (F →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ F F F (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ F F F).flip (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap)

private theorem starConjCLM_apply_apply (A : F →L[ℝ] F) (x : F) :
    starConjCLM A x = star (A (star x)) := rfl

/-- The reflection of a field of real-linear endomorphisms across the real axis: `C z` on the
closed upper half-plane and `star ∘ C (conj z) ∘ star` below it. It is the coefficient of the
reflected equation, by `TauCeti.starSchwarzReflection_clm_apply`. -/
def starSchwarzReflectionCoeff (C : ℂ → F →L[ℝ] F) (z : ℂ) : F →L[ℝ] F :=
  if 0 ≤ z.im then C z else starConjCLM (C (conj z))

variable {C : ℂ → F →L[ℝ] F} {ξ : ℂ → F}

@[simp]
theorem starSchwarzReflectionCoeff_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    starSchwarzReflectionCoeff C z = C z := ite_eq_left_iff.2 fun h ↦ (h hz).elim

theorem starSchwarzReflectionCoeff_of_im_neg_apply {z : ℂ} (hz : z.im < 0) (x : F) :
    starSchwarzReflectionCoeff C z x = star (C (conj z) (star x)) := by
  rw [starSchwarzReflectionCoeff, ite_eq_right_iff.2 fun h ↦ (hz.not_ge h).elim,
    starConjCLM_apply_apply]

/-- **The reflected equation, pointwise.** Reflecting `z ↦ C z (ξ z)` is applying the reflected
coefficient to the reflected function. -/
theorem starSchwarzReflection_clm_apply (C : ℂ → F →L[ℝ] F) (ξ : ℂ → F) :
    starSchwarzReflection (fun z ↦ C z (ξ z)) =
      fun z ↦ starSchwarzReflectionCoeff C z (starSchwarzReflection ξ z) := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · rw [not_le] at hz
    rw [starSchwarzReflection_of_im_neg hz, starSchwarzReflectionCoeff_of_im_neg_apply hz,
      starSchwarzReflection_of_im_neg hz, star_star]

/-! ### Local `Lᵖ` bounds and continuity on the doubled domain -/

private theorem isClosed_im_nonneg : IsClosed {z : ℂ | 0 ≤ z.im} :=
  isClosed_le continuous_const Complex.continuous_im

omit [NormedSpace ℂ F] [StarModule ℂ F] [ContinuousStar F] in
private theorem starSchwarzReflection_eq_ite (ξ : ℂ → F) :
    starSchwarzReflection ξ = fun z ↦ if 0 ≤ z.im then ξ z else star (ξ (conj z)) := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · simp [starSchwarzReflection_of_im_neg (not_le.1 hz), hz]

/-- Reflecting by a continuous linear map `L` below the axis preserves local `Lᵖ` bounds up to
the boundary. -/
private theorem memLpLoc_ite_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} {Ω : Set ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (L : E →L[ℝ] E) {f : ℂ → E}
    (hf : MemLpLoc p (Ω ∩ {z | 0 ≤ z.im}) f) :
    MemLpLoc p Ω (fun z ↦ if 0 ≤ z.im then f z else L (f (conj z))) := by
  refine memLpLoc_iff.2 fun K hKΩ hK ↦ ?_
  have hH : MeasurableSet {z : ℂ | 0 ≤ z.im} := isClosed_im_nonneg.measurableSet
  have hL : MeasurableSet {z : ℂ | z.im < 0} :=
    measurableSet_lt Complex.measurable_im measurable_const
  have hsplit : (fun z ↦ if 0 ≤ z.im then f z else L (f (conj z))) =
      {z : ℂ | 0 ≤ z.im}.indicator f + {z : ℂ | z.im < 0}.indicator (fun z ↦ L (f (conj z))) := by
    funext z
    by_cases hz : 0 ≤ z.im
    · simp [hz]
    · simp [hz, indicator_of_mem (show z ∈ {z : ℂ | z.im < 0} from not_le.1 hz)]
  rw [hsplit]
  refine MemLp.add ?_ ?_
  · rw [memLp_indicator_iff_restrict hH.nullMeasurableSet, Measure.restrict_restrict hH]
    exact memLpLoc_iff.1 hf _ (fun z hz ↦ ⟨hKΩ hz.2, hz.1⟩) (hK.inter_left isClosed_im_nonneg)
  · rw [memLp_indicator_iff_restrict hL.nullMeasurableSet, Measure.restrict_restrict hL]
    let K' : Set ℂ := (conjLIE : ℂ → ℂ) ⁻¹' K ∩ {z | 0 ≤ z.im}
    have hK' : IsCompact K' :=
      (conjLIE.toHomeomorph.isCompact_preimage.2 hK).inter_right isClosed_im_nonneg
    have hK'Ω : K' ⊆ Ω ∩ {z | 0 ≤ z.im} := fun z hz ↦
      ⟨by simpa using hΩ (hKΩ hz.1), hz.2⟩
    have h1 : MemLp f p (volume.restrict K') := memLpLoc_iff.1 hf _ hK'Ω hK'
    have h2 : MemLp (fun z ↦ f (conj z)) p (volume.restrict ((conjLIE : ℂ → ℂ) ⁻¹' K')) :=
      h1.comp_measurePreserving (conjLIE.measurePreserving.restrict_preimage_emb
        conjLIE.toHomeomorph.measurableEmbedding K')
    refine (L.comp_memLp' (h2.mono_measure (Measure.restrict_mono ?_ le_rfl)))
    exact fun z hz ↦ ⟨by simpa using hz.2, by simpa using hz.1.le⟩

/-- The reflection of a function locally `Lᵖ` up to the boundary is locally `Lᵖ` on the doubled
domain. -/
theorem MemLpLoc.starSchwarzReflection {p : ℝ≥0∞} {Ω : Set ℂ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hξ : MemLpLoc p (Ω ∩ {z | 0 ≤ z.im}) ξ) : MemLpLoc p Ω (starSchwarzReflection ξ) :=
  starSchwarzReflection_eq_ite ξ ▸
    memLpLoc_ite_conj hΩ (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap hξ

/-- The reflection of a coefficient field locally `Lᵖ` up to the boundary is locally `Lᵖ` on the
doubled domain. -/
theorem MemLpLoc.starSchwarzReflectionCoeff {p : ℝ≥0∞} {Ω : Set ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p (Ω ∩ {z | 0 ≤ z.im}) C) :
    MemLpLoc p Ω (starSchwarzReflectionCoeff C) :=
  memLpLoc_ite_conj hΩ (starConjCLM (F := F)) hC

omit [NormedSpace ℂ F] [StarModule ℂ F] in
/-- **Continuity of the reflection.** On a conjugation-invariant set, a map continuous up to the
real axis and real there has a continuous reflection. -/
theorem continuousOn_starSchwarzReflection_of_symmetric {Ω : Set ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hξ : ContinuousOn ξ (Ω ∩ {z | 0 ≤ z.im}))
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x) :
    ContinuousOn (starSchwarzReflection ξ) Ω := by
  have hlower : ContinuousOn (fun z ↦ star (ξ (conj z))) (Ω ∩ {z | z.im ≤ 0}) :=
    continuous_star.comp_continuousOn (hξ.comp Complex.continuous_conj.continuousOn
      fun z hz ↦ ⟨hΩ hz.1, by simpa using hz.2⟩)
  refine (ContinuousOn.if (p := fun z : ℂ ↦ 0 ≤ z.im) (f := ξ)
    (g := fun z ↦ star (ξ (conj z))) (fun z hz ↦ ?_) ?_ ?_).congr fun z _ ↦ ?_
  · rw [Complex.frontier_setOfPred_le_im] at hz
    have hz0 : z.im = 0 := hz.2
    have hzx : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz0)
    have hc : conj z = z := Complex.conj_eq_iff_im.2 hz0
    rw [hc, eq_comm, hzx]
    exact hreal z.re (hzx ▸ hz.1)
  · rwa [isClosed_im_nonneg.closure_eq]
  · simp only [not_le]
    rwa [Complex.closure_setOfPred_im_lt]
  · exact congrFun (starSchwarzReflection_eq_ite ξ) z

/-! ### The reflected equation -/

/-- **Reflection of the linear Cauchy–Riemann equation with a real boundary condition.** Let
`1 < p < ∞`, let `Ω` be conjugation invariant, and let `ξ` be continuous on `Ω ∩ {0 ≤ im}` and
real on `Ω ∩ ℝ`, solving `∂ₛξ + i ∂ₜξ + C(z) ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the real
boundary condition, for a coefficient field `C` locally `Lᵖ` up to the boundary. Then the
reflection of `ξ` is a weak solution on all of `Ω` of the same equation with the reflected
coefficient field. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.isWeakLinearCauchyRiemannOn_starSchwarzReflection
    [FiniteDimensional ℂ F] {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ⊤) {Ω : Opens ℂ}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξc : ContinuousOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hξr : ∀ x : ℝ, (x : ℂ) ∈ Ω → star (ξ x) = ξ x)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ F)
      (starSchwarzReflectionCoeff C) (starSchwarzReflection ξ) := by
  have hc := continuousOn_starSchwarzReflection_of_symmetric hΩ hξc hξr
  have hCξ := memLpLoc_clm_apply (hC.starSchwarzReflectionCoeff hΩ) hc
  have hw := h.hasWeakConjWirtingerDerivOn_starSchwarzReflection hΩ
  have hR : starSchwarzReflection (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) =
      fun z ↦ (2 : ℂ)⁻¹ • -starSchwarzReflectionCoeff C z (starSchwarzReflection ξ z) := by
    have h2 : starSchwarzReflection (fun z ↦ -(2 : ℂ)⁻¹ • C z (ξ z)) =
        fun z ↦ -(2 : ℝ)⁻¹ • starSchwarzReflection (fun z ↦ C z (ξ z)) z := by
      funext z
      have hs (x : F) : -(2 : ℂ)⁻¹ • x = -(2 : ℝ)⁻¹ • x := by
        rw [← Complex.coe_smul]; norm_num
      by_cases hz : 0 ≤ z.im
      · simp only [starSchwarzReflection_of_im_nonneg hz, hs]
      · rw [not_le] at hz
        simp only [starSchwarzReflection_of_im_neg hz, hs, star_smul, star_trivial]
    rw [h2, starSchwarzReflection_clm_apply]
    funext z
    rw [smul_neg, ← neg_smul, ← Complex.coe_smul]
    norm_num
  rw [hR] at hw
  have hf : MemLpLoc p Ω
      (fun z ↦ (2 : ℂ)⁻¹ • -starSchwarzReflectionCoeff C z (starSchwarzReflection ξ z)) := by
    have := hCξ.neg.const_smul (2 : ℝ)⁻¹
    refine this.congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.smul_apply, Pi.neg_apply]
    rw [← Complex.coe_smul]
    norm_num
  refine isWeakCauchyRiemannOn_I_smul_id_iff.2 ⟨hc, ?_, hw⟩
  exact memWkpLoc_one_of_hasWeakConjWirtingerDerivOn hp hp_top hc.memLpLoc hf hw

/-! ### Transfer of zeros -/

omit [NormedSpace ℂ F] [StarModule ℂ F] [ContinuousStar F] in
/-- A map vanishing on a subset of the closed upper half-plane has reflection vanishing there. -/
theorem eqOn_zero_starSchwarzReflection_of_subset {U : Set ℂ} (hU : U ⊆ {z | 0 ≤ z.im})
    (h : EqOn ξ 0 U) : EqOn (starSchwarzReflection ξ) 0 U := fun z hz ↦ by
  rw [starSchwarzReflection_of_im_nonneg (hU hz)]
  exact h hz

/-- **Vanishing order transfers to the reflection.** At a point `z₀` of the closed upper
half-plane, a bound `ξ = O((z - z₀)ⁿ)` within the closed upper half-plane gives the same bound for
the reflection in a full neighbourhood of `z₀`. -/
theorem isBigO_starSchwarzReflection {z₀ : ℂ} (hz₀ : 0 ≤ z₀.im) {n : ℕ}
    (h : ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    starSchwarzReflection ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n := by
  have hup : starSchwarzReflection ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n :=
    h.congr' (eventually_nhdsWithin_of_forall fun z hz ↦
      (starSchwarzReflection_of_im_nonneg hz).symm) EventuallyEq.rfl
  rcases hz₀.lt_or_eq with hpos | hzero
  · rwa [nhdsWithin_eq_nhds.2 (mem_of_superset
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos)
      fun w (hw : 0 < w.im) ↦ (show 0 ≤ w.im from hw.le))] at hup
  · have hc : conj z₀ = z₀ := Complex.conj_eq_iff_im.2 hzero.symm
    have ht : Tendsto (starRingEnd ℂ) (𝓝[{z | z.im < 0}] z₀) (𝓝[{z | 0 ≤ z.im}] z₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz ↦ ?_⟩
      · have := (Complex.continuous_conj.tendsto z₀).mono_left
          (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
        rwa [hc] at this
      · simpa using (show z.im < 0 from hz).le
    have hlow : starSchwarzReflection ξ =O[𝓝[{z | z.im < 0}] z₀] fun z ↦ (z - z₀) ^ n := by
      have h1 := (h.comp_tendsto ht)
      have h2 : (fun z ↦ star (ξ (conj z))) =O[𝓝[{z | z.im < 0}] z₀]
          fun z ↦ (conj z - z₀) ^ n :=
        ((starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.isBigO_comp _ _).trans h1
      refine (h2.trans (isBigO_of_le _ fun z ↦ ?_)).congr'
        (eventually_nhdsWithin_of_forall fun z hz ↦
          (starSchwarzReflection_of_im_neg hz).symm) EventuallyEq.rfl
      have hz : conj z - z₀ = conj (z - z₀) := by rw [map_sub, hc]
      rw [hz, ← map_pow, Complex.norm_conj]
    have hU : {z : ℂ | 0 ≤ z.im} ∪ {z | z.im < 0} = univ := by
      ext z; simp [le_or_gt]
    have := hup.sup hlow
    rwa [← nhdsWithin_union, hU, nhdsWithin_univ] at this

/-! ### Checks -/

@[simp]
theorem starSchwarzReflectionCoeff_zero :
    starSchwarzReflectionCoeff (0 : ℂ → F →L[ℝ] F) = 0 := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext x
    simp [starSchwarzReflectionCoeff_of_im_neg_apply (not_le.1 hz)]

/-- **Check.** For `C = 0` the reflected equation is `\bar∂ = 0`, solved by the reflection of the
real-boundary solution `z`, which is `z` itself. -/
theorem isWeakLinearCauchyRiemannOn_starSchwarzReflection_id {p : ℝ≥0∞} {Ω : Opens ℂ} :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (starSchwarzReflectionCoeff 0) (starSchwarzReflection id) := by
  rw [starSchwarzReflectionCoeff_zero, starSchwarzReflection_id]
  exact isWeakCauchyRiemannOn_of_contDiffOn contDiff_id.contDiffOn fun z _ ↦ by simp

/-- **Check.** A constant real multiple of the identity is its own reflected coefficient. -/
theorem starSchwarzReflectionCoeff_const_real_smul_id (c : ℝ) :
    starSchwarzReflectionCoeff (fun _ ↦ c • ContinuousLinearMap.id ℝ F) =
      fun _ ↦ c • ContinuousLinearMap.id ℝ F := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext x
    simp [starSchwarzReflectionCoeff_of_im_neg_apply (not_le.1 hz), star_smul]

/-- **Check.** The constant coefficient `i` is reflected to `-i` below the axis: the reflected
coefficient is the conjugate, not the even reflection. -/
theorem starSchwarzReflectionCoeff_const_I_smul_id_of_im_neg {z : ℂ} (hz : z.im < 0) :
    starSchwarzReflectionCoeff (fun _ ↦ I • ContinuousLinearMap.id ℝ F) z =
      -(I • ContinuousLinearMap.id ℝ F) := by
  ext x
  simp [starSchwarzReflectionCoeff_of_im_neg_apply hz, star_smul]

/-- **Check.** The solution `z e^{-conj z}` of `∂ₛξ + i ∂ₜξ + 2ξ = 0` is real on the real axis
and is its own reflection. -/
theorem starSchwarzReflection_mul_cexp_neg_conj :
    starSchwarzReflection (fun z : ℂ ↦ z * cexp (-conj z)) = fun z ↦ z * cexp (-conj z) := by
  funext z
  by_cases hz : 0 ≤ z.im
  · rw [starSchwarzReflection_of_im_nonneg hz]
  · rw [starSchwarzReflection_of_im_neg (not_le.1 hz), Complex.star_def, map_mul,
      ← Complex.exp_conj, map_neg, conj_conj]

/-- **Check.** With the nonzero coefficient `C = 2`, the reflection of the real-boundary solution
`z e^{-conj z}` solves the reflected equation `∂ₛξ + i ∂ₜξ + 2ξ = 0` on every open set. -/
theorem isWeakLinearCauchyRiemannOn_starSchwarzReflection_mul_cexp_neg_conj {p : ℝ≥0∞}
    {Ω : Opens ℂ} :
    IsWeakLinearCauchyRiemannOn p Ω (fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ)
      (starSchwarzReflectionCoeff fun _ ↦ (2 : ℝ) • ContinuousLinearMap.id ℝ ℂ)
      (starSchwarzReflection fun z : ℂ ↦ z * cexp (-conj z)) := by
  rw [starSchwarzReflectionCoeff_const_real_smul_id, starSchwarzReflection_mul_cexp_neg_conj]
  have hd : ContDiff ℝ 1 fun z : ℂ ↦ z * cexp (-conj z) :=
    contDiff_id.mul (conjCLE.contDiff.neg.cexp)
  refine isWeakCauchyRiemannOn_of_contDiffOn hd.contDiffOn fun z _ ↦ ?_
  have := fderiv_mul_cexp_neg_conj_add_eq_zero z
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  linear_combination this

end TauCeti
