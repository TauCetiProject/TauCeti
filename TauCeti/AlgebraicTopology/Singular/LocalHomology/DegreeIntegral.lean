/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.MeasurableSpace.DisjointCover

/-!
# The degree of a proper map computes integrals of pullbacks

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, oriented by
a homological orientation `o`, and let `f : E → E` be a proper `C¹` map. The pullback of the top
form `g dμ` along `f` is `g(f x) det Df(x) dμ`, and its integral is the degree of `f` times the
integral of `g`:

`∫ g(f x) det Df(x) dμ(x) = deg f ∫ g dμ`

(`TauCeti.HomologicalOrientation.integral_comp_mul_det_fderiv_eq_degree_mul`). This is the
analytic description of the homological degree (`TauCeti.HomologicalOrientation.degree`), the
integral counterpart of its description as a signed count of the preimages of a regular value
(`TauCeti.HomologicalOrientation.degree_eq_sum_sign_det`).

The proof covers the open set where `det Df ≠ 0` by countably many disjoint measurable pieces on
each of which `f` is injective, by the inverse function theorem, and `det Df` has a constant sign
(`IsOpen.exists_pairwise_disjoint_iUnion_eq`). On each piece the change of variables formula
(`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) turns the integral of
`g(f x) det Df(x)` into the integral of `± g` over the image of the piece. Summing over the
pieces, the integrand at `y` becomes `g(y)` times the sum of the signs `sign det Df(x)` over the
preimages `x` of `y`. By Sard's theorem
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) almost every `y` is a regular
value, where this sum is the degree.

## Main results

* `TauCeti.HomologicalOrientation.integral_comp_mul_det_fderiv_eq_degree_mul`: the integral of
  the pullback of `g dμ` is the degree times the integral of `g`.
* `TauCeti.HomologicalOrientation.integral_comp_mul_det_fderiv_eq_degree_mul_of_hasCompactSupport`:
  the same for continuous compactly supported `g`, for which the pullback is integrable.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Springer, 1982, §4.
-/

public section

open MeasureTheory Set Filter Topology Function

namespace TauCeti

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The open set where a `C¹` map `f : E → E` has invertible derivative is a countable disjoint
union of measurable pieces on each of which `f` is injective and `det Df` has a constant sign. -/
private theorem exists_pieces [MeasurableSpace E] [BorelSpace E] {f : E → E}
    (hf : ContDiff ℝ 1 f) :
    ∃ (t : ℕ → Set E) (ε : ℕ → SignType), (∀ k, MeasurableSet (t k)) ∧
      Pairwise (Disjoint on t) ∧ ⋃ k, t k = {x | (fderiv ℝ f x).det ≠ 0} ∧
      ∀ k, InjOn f (t k) ∧ ∀ x ∈ t k, SignType.sign (fderiv ℝ f x).det = ε k := by
  classical
  have hd : Continuous fun x ↦ (fderiv ℝ f x).det :=
    ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv one_ne_zero)
  -- Near a point with invertible derivative, `f` is injective by the inverse function theorem.
  have hloc : ∀ x ∈ {x | (fderiv ℝ f x).det ≠ 0}, ∃ U ∈ 𝓝 x, InjOn f U ∧
      (U ⊆ {x | 0 < (fderiv ℝ f x).det} ∨ U ⊆ {x | (fderiv ℝ f x).det < 0}) := by
    intro x hx
    have hx' : (fderiv ℝ f x).det ≠ 0 := hx
    have hs : HasStrictFDerivAt f
        ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hx' : E →L[ℝ] E) x := by
      rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      exact hf.hasStrictFDerivAt one_ne_zero
    set Φ := HasStrictFDerivAt.toOpenPartialHomeomorph f hs
    have hΦ : Φ.source ∈ 𝓝 x :=
      Φ.open_source.mem_nhds (HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hs)
    have hinj : InjOn f Φ.source := by
      simpa [Φ, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using Φ.injOn
    rcases hx'.lt_or_gt with hneg | hpos
    · exact ⟨Φ.source ∩ {x | (fderiv ℝ f x).det < 0},
        inter_mem hΦ ((isOpen_lt hd continuous_const).mem_nhds hneg),
        hinj.mono inter_subset_left, Or.inr inter_subset_right⟩
    · exact ⟨Φ.source ∩ {x | 0 < (fderiv ℝ f x).det},
        inter_mem hΦ ((isOpen_lt continuous_const hd).mem_nhds hpos),
        hinj.mono inter_subset_left, Or.inl inter_subset_right⟩
  obtain ⟨t, htm, htd, htU, htp⟩ :=
    (isOpen_ne_fun hd continuous_const).exists_pairwise_disjoint_iUnion_eq
      (fun s t hst ht ↦ ⟨ht.1.mono hst, ht.2.imp hst.trans hst.trans⟩)
      ⟨injOn_empty f, Or.inl (empty_subset _)⟩ hloc
  -- The sign of `det Df` on each piece.
  refine ⟨t, fun k ↦ if t k ⊆ {x | 0 < (fderiv ℝ f x).det} then 1 else -1, htm, htd, htU,
    fun k ↦ ⟨(htp k).1, fun x hx ↦ ?_⟩⟩
  by_cases h : t k ⊆ {x | 0 < (fderiv ℝ f x).det}
  · have hpos : 0 < (fderiv ℝ f x).det := h hx
    simp [h, sign_pos hpos]
  · have hneg : (fderiv ℝ f x).det < 0 := (htp k).2.resolve_left h hx
    simp [h, sign_neg hneg]

/-- **Change of variables on a piece.** On a measurable set `s` where `f` is injective and
`det Df` has the constant sign `ε`, the integral of `g(f x) det Df(x)` is `ε` times the integral of
`g` over `f(s)`. -/
private theorem setIntegral_comp_mul_det_eq [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {f : E → E} (hf : ∀ x, HasFDerivAt f (fderiv ℝ f x) x) {s : Set E}
    (hs : MeasurableSet s) (hinj : InjOn f s) {ε : SignType}
    (hε : ∀ x ∈ s, SignType.sign (fderiv ℝ f x).det = ε) (g : E → ℝ) :
    ∫ x in s, g (f x) * (fderiv ℝ f x).det ∂μ = ∫ y, (ε : ℝ) * (f '' s).indicator g y ∂μ := by
  rw [integral_const_mul, integral_indicator
      (measurable_image_of_fderivWithin hs (fun x _ ↦ (hf x).hasFDerivWithinAt) hinj),
    integral_image_eq_integral_abs_det_fderiv_smul μ hs (fun x _ ↦ (hf x).hasFDerivWithinAt) hinj,
    ← integral_const_mul]
  refine setIntegral_congr_fun hs fun x hx ↦ ?_
  rw [smul_eq_mul, ← hε x hx, ← mul_assoc, sign_mul_abs, mul_comm]

/-- **Finite total mass of the pieces.** If `g(f x) det Df(x)` is integrable and `f` is injective
on each of the pairwise disjoint measurable pieces `t k`, then the integrals of `|ε k g|` over the
images `f(t k)`, for signs `ε k`, have a finite sum. -/
private theorem tsum_lintegral_enorm_mul_indicator_ne_top [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} (hf : ∀ x, HasFDerivAt f (fderiv ℝ f x) x)
    {t : ℕ → Set E} (htm : ∀ k, MeasurableSet (t k)) (htd : Pairwise (Disjoint on t))
    (hinj : ∀ k, InjOn f (t k)) (ε : ℕ → SignType) {g : E → ℝ}
    (hint : Integrable (fun x ↦ g (f x) * (fderiv ℝ f x).det) μ) :
    ∑' k, ∫⁻ y, ‖(ε k : ℝ) * (f '' t k).indicator g y‖ₑ ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top hint.2.ne ?_
  calc ∑' k, ∫⁻ y, ‖(ε k : ℝ) * (f '' t k).indicator g y‖ₑ ∂μ
      ≤ ∑' k, ∫⁻ y in f '' t k, ‖g y‖ₑ ∂μ := by
        refine tsum_le_tsum fun k ↦ ?_
        rw [← lintegral_indicator
          (measurable_image_of_fderivWithin (htm k) (fun x _ ↦ (hf x).hasFDerivWithinAt) (hinj k))]
        refine lintegral_mono fun y ↦ ?_
        rw [eNorm_mul, eNorm_indicator_eq_indicator_eNorm]
        refine mul_le_of_le_one_left' ?_
        cases ε k <;> simp
    _ = ∑' k, ∫⁻ x in t k, ‖g (f x) * (fderiv ℝ f x).det‖ₑ ∂μ := by
        refine tsum_congr fun k ↦ ?_
        rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (htm k)
          (fun x _ ↦ (hf x).hasFDerivWithinAt) (hinj k)]
        refine setLIntegral_congr_fun (htm k) fun x _ ↦ ?_
        simp only [eNorm_mul, Real.eNorm_eq_ofReal_abs, mul_comm]
    _ = ∫⁻ x in ⋃ k, t k, ‖g (f x) * (fderiv ℝ f x).det‖ₑ ∂μ :=
        (lintegral_iUnion htm htd _).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

omit [FiniteDimensional ℝ E] in
/-- **Counting the preimages of a regular value.** If the pieces `t k` are pairwise disjoint and
cover the finite fibre of `f` over `y`, `f` is injective on each piece, and `det Df` has the sign
`ε k` on `t k`, then summing `ε k g(y)` over the pieces whose image contains `y` gives `g(y)` times
the sum of the signs of `det Df` over the fibre. -/
private theorem tsum_mul_indicator_eq_sum_sign_mul {f : E → E} {t : ℕ → Set E} {ε : ℕ → SignType}
    (htd : Pairwise (Disjoint on t)) (hinj : ∀ k, InjOn f (t k))
    (hε : ∀ k, ∀ x ∈ t k, SignType.sign (fderiv ℝ f x).det = ε k) {y : E}
    (hF : (f ⁻¹' {y}).Finite) (hcover : ∀ x ∈ f ⁻¹' {y}, ∃ k, x ∈ t k) (g : E → ℝ) :
    ∑' k, (ε k : ℝ) * (f '' t k).indicator g y =
      ((∑ x ∈ hF.toFinset, (SignType.sign (fderiv ℝ f x).det : ℤ) : ℤ) : ℝ) * g y := by
  -- Each preimage `x` of `y` lies in exactly one piece `t (ν x)`, and these pieces are distinct.
  choose! ν hν using hcover
  have hνeq {x : E} (hx : x ∈ f ⁻¹' {y}) {k : ℕ} (hk : x ∈ t k) : ν x = k := by
    by_contra hne
    exact disjoint_left.1 (htd hne) (hν x hx) hk
  have hνinj : InjOn ν (f ⁻¹' {y}) := fun x hx x' hx' h ↦
    hinj (ν x) (hν x hx) (h ▸ hν x' hx') ((mem_singleton_iff.1 hx).trans
      (mem_singleton_iff.1 hx').symm)
  -- Only the pieces containing a preimage of `y` contribute, each with the sign of `det Df`.
  have hsupp : ∀ k ∉ hF.toFinset.image ν, (ε k : ℝ) * (f '' t k).indicator g y = 0 := by
    intro k hk
    have hyk : y ∉ f '' t k := by
      rintro ⟨x, hxk, hxy⟩
      exact hk (Finset.mem_image.2 ⟨x, hF.mem_toFinset.2 hxy, hνeq hxy hxk⟩)
    rw [indicator_of_notMem hyk, mul_zero]
  rw [tsum_eq_sum hsupp, Finset.sum_image fun x hx x' hx' h ↦
    hνinj (hF.mem_toFinset.1 hx) (hF.mem_toFinset.1 hx') h]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' : x ∈ f ⁻¹' {y} := hF.mem_toFinset.1 hx
  have hyx : y ∈ f '' t (ν x) := ⟨x, hν x hx', hx'⟩
  rw [indicator_of_mem hyx, hε _ x (hν x hx')]

variable {n : ℕ} (o : HomologicalOrientation E E n) (hE : Module.finrank ℝ E = n)
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

include hE in
/-- **The integral of a pullback is the degree times the integral.** Let `f : E → E` be a proper
`C¹` map and `g : E → ℝ` an almost everywhere strongly measurable function whose pullback
`g(f x) det Df(x)` is integrable. Then

`∫ g(f x) det Df(x) dμ(x) = deg f ∫ g dμ`. -/
theorem integral_comp_mul_det_fderiv_eq_degree_mul {f : C(E, E)} (hf : IsProperMap f)
    (hf₁ : ContDiff ℝ 1 f) {g : E → ℝ} (hg : AEStronglyMeasurable g μ)
    (hint : Integrable (fun x ↦ g (f x) * (fderiv ℝ f x).det) μ) :
    ∫ x, g (f x) * (fderiv ℝ f x).det ∂μ = o.degree o hE f * ∫ y, g y ∂μ := by
  have hderiv (x : E) : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf₁.differentiable one_ne_zero x).hasFDerivAt
  obtain ⟨t, ε, htm, htd, htU, htp⟩ := exists_pieces hf₁
  have him (k : ℕ) : MeasurableSet (f '' t k) :=
    measurable_image_of_fderivWithin (htm k) (fun x _ ↦ (hderiv x).hasFDerivWithinAt) (htp k).1
  -- The pullback vanishes where `det Df = 0`, so its integral is the sum over the pieces.
  have hU : ∫ x in ⋃ k, t k, g (f x) * (fderiv ℝ f x).det ∂μ =
      ∫ x, g (f x) * (fderiv ℝ f x).det ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [htU, mem_ofPred_eq, not_not] at hx
      rw [hx, mul_zero]
  -- The sum over the pieces has finite total mass.
  have hfin := tsum_lintegral_enorm_mul_indicator_ne_top μ hderiv htm htd (fun k ↦ (htp k).1) ε
    hint
  rw [← hU, integral_iUnion htm htd hint.integrableOn,
    tsum_congr fun k ↦ setIntegral_comp_mul_det_eq μ hderiv (htm k) (htp k).1 (htp k).2 g,
    ← integral_tsum (fun k ↦ (hg.indicator (him k)).const_mul _) hfin, ← integral_const_mul]
  refine integral_congr_ae ?_
  -- Almost every `y` is a regular value, by Sard's theorem, and there the sum of the signs over
  -- the fibre is the degree.
  have hsard : μ (f '' {x | (fderiv ℝ f x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x _ ↦ (hderiv x).hasFDerivWithinAt) fun _ hx ↦ hx
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsard] with y hy
  have hreg : ∀ x ∈ f ⁻¹' {y}, (fderiv ℝ f x).det ≠ 0 := fun x hx h0 ↦ hy ⟨x, h0, hx⟩
  have hF : (f ⁻¹' {y}).Finite :=
    IsCompact.finite_of_hasFDerivAt (hf.isCompact_preimage isCompact_singleton)
      (fun x _ ↦ hderiv x) fun x hx ↦
        ⟨_, ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hreg x hx)).antilipschitzWith⟩
  rw [o.degree_eq_sum_sign_det hE hf hF (fun x _ ↦ hderiv x) hreg]
  exact tsum_mul_indicator_eq_sum_sign_mul htd (fun k ↦ (htp k).1) (fun k ↦ (htp k).2) hF
    (fun x hx ↦ mem_iUnion.1 (htU ▸ hreg x hx)) g

include hE in
/-- **The integral of a pullback is the degree times the integral**, for a continuous compactly
supported function `g`: for a proper `C¹` map `f : E → E`,

`∫ g(f x) det Df(x) dμ(x) = deg f ∫ g dμ`. -/
theorem integral_comp_mul_det_fderiv_eq_degree_mul_of_hasCompactSupport {f : C(E, E)}
    (hf : IsProperMap f) (hf₁ : ContDiff ℝ 1 f) {g : E → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∫ x, g (f x) * (fderiv ℝ f x).det ∂μ = o.degree o hE f * ∫ y, g y ∂μ := by
  -- The pullback is continuous, and supported in the compact preimage of the support of `g`.
  have hc : HasCompactSupport fun x ↦ g (f x) :=
    (hf.isCompact_preimage hgc).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage g f.continuous)
  refine o.integral_comp_mul_det_fderiv_eq_degree_mul hE μ hf hf₁ hg.aestronglyMeasurable ?_
  exact ((hg.comp f.continuous).mul (ContinuousLinearMap.continuous_det.comp
    (hf₁.continuous_fderiv one_ne_zero))).integrable_of_hasCompactSupport (hc.mul_right)

end HomologicalOrientation

end TauCeti
