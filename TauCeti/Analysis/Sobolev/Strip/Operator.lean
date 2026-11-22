/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.JetOperator
public import TauCeti.Analysis.Sobolev.Strip.Jet
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# First-order operators on `L²` jets over the strip and Peetre's argument

A first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` on sections `ξ : ℝ × ℝ → V` over the strip
`ℝ × [0, 1]`, with an essentially bounded coefficient field `M : ℝ × ℝ → V × V × V →L[ℝ] W`, acts
pointwise on `L²` jets (`TauCeti.jetOperator stripMeasure M`). Restricted to the closure
`TauCeti.StripSobolev.jetClosure S` of the jets of a space `S` of sections, it is the realization
of `D` on a Sobolev space `W^{1,2}`: the space `TauCeti.CylinderSobolev.H1` of the cylinder
`ℝ × S¹`, whose fundamental domain is the strip, and the space `TauCeti.StripSobolev.H1 F₀ F₁` of
the strip with boundary values in subspaces `F₀` and `F₁`. This file develops the functional
analysis of these operators once, for every such `S`.

* The operator depends Lipschitz-continuously on its coefficient field in `L^∞`
  (`TauCeti.StripSobolev.norm_jetOperator_sub_le`), hence continuously along families of
  coefficient fields continuous in `L^∞` (`TauCeti.StripSobolev.continuousOn_jetOperator`).
* **The semi-Fredholm estimate** (`TauCeti.StripSobolev.HasSemiFredholmEstimate S M C T`) asks
  that every `ξ ∈ S` vanishing for `s ∉ (a, b)` satisfy

  `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

  the first two integrals over `[a, b] × [0, 1]`. This is the form in which elliptic estimates for
  linearized Floer operators are proved: an interior estimate on a compact piece and invertibility
  of the asymptotic operators near the ends.
* **Peetre's argument.** When the elements of `S` are `C¹` and vanish for `|s|` large
  (`TauCeti.StripSobolev.IsTestSpace`), the estimate passes to `jetClosure S` with the error term
  `ξ ↦ ξ|_{[-T, T] × [0, 1]}`. That term is compact when Rellich's theorem holds for `S`
  (`TauCeti.StripSobolev.HasCompactRestriction`), as it does on the cylinder and on the strip with
  boundary conditions for a finite-dimensional fibre. Then `D` has finite-dimensional kernel
  (`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`) and closed range
  (`TauCeti.StripSobolev.isClosed_range_jetOperator_comp_subtypeL`), by
  `ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate` and
  `ContinuousLinearMap.isClosed_range_of_compact_estimate`.
* **An estimate from below.** If `D` moreover bounds every element of `S` in `L²` over the whole
  strip, `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`, the compact error term disappears: `‖x‖ ≤ K ‖D x‖` on
  `jetClosure S` (`TauCeti.StripSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`),
  so `D` is injective there (`TauCeti.StripSobolev.ker_jetOperator_comp_subtypeL_eq_bot`). No
  compactness is needed for this.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S` on the
  cylinder.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces, Rellich's theorem and the semi-Fredholm estimate.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Spaces of test sections -/

/-- A space `S` of maps `ξ : ℝ × ℝ → V` whose elements are `C¹` and vanish for `|s|` large, such
as the test sections of the cylinder (`TauCeti.CylinderSobolev.testSection`) and of the strip with
boundary conditions (`TauCeti.StripSobolev.testSection`). Integrals over the strip of quantities
built from the jet of such a section reduce to integrals over compact rectangles, which is how a
semi-Fredholm estimate (`TauCeti.StripSobolev.HasSemiFredholmEstimate`) is applied to it. -/
class IsTestSpace (S : Submodule ℝ (ℝ × ℝ → V)) : Prop where
  /-- The elements of `S` are `C¹`. -/
  contDiff : ∀ ξ ∈ S, ContDiff ℝ 1 ξ
  /-- The elements of `S` vanish for `|s|` large. -/
  exists_forall_le_abs_eq_zero : ∀ ξ ∈ S, ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0

/-- **Rellich's theorem** for a space `S` of sections over the strip: for every `T`, the value on
the compact piece `[-T, T] × [0, 1]` (`TauCeti.StripSobolev.restrictValue T`) is a compact operator
on the Sobolev space `jetClosure S`. It holds on the cylinder
(`TauCeti.CylinderSobolev.isCompactOperator_restrictValue_comp_subtypeL`) and on the strip with
boundary conditions (`TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL`), for a
finite-dimensional fibre. -/
class HasCompactRestriction (S : Submodule ℝ (ℝ × ℝ → V)) [HasL2Jets S] : Prop where
  /-- The value on `[-T, T] × [0, 1]` is a compact operator on `jetClosure S`. -/
  isCompactOperator_restrictValue_comp_subtypeL : ∀ T : ℝ,
    IsCompactOperator ((restrictValue (V := V) T).comp (jetClosure S).subtypeL)

/-! ### First-order operators with bounded coefficients -/

section Operator

/-- The first-order operator depends Lipschitz-continuously on its coefficient field: its operator
norm on `L²` jets is at most the essential supremum of the difference of the coefficients. -/
theorem norm_jetOperator_sub_le {M M' : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) (hM' : MemLp M' ∞ stripMeasure) :
    ‖jetOperator stripMeasure M - jetOperator stripMeasure M'‖ ≤
      (eLpNorm (M - M') ∞ stripMeasure).toReal := by
  rw [jetOperator_of_memLp hM, jetOperator_of_memLp hM', ← map_sub, ← MemLp.toLp_sub,
    ← Lp.norm_toLp _ (hM.sub hM')]
  exact Lp.norm_operatorMultiplication_le _

/-- Coefficient fields depending continuously on a parameter in `L^∞` give first-order operators
on `L²` jets depending continuously on the parameter in the operator norm. -/
theorem continuousOn_jetOperator {X : Type*} [TopologicalSpace X] {s : Set X}
    {M : X → ℝ × ℝ → V × V × V →L[ℝ] W} (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0)) :
    ContinuousOn (fun x ↦ jetOperator stripMeasure (M x)) s := by
  intro x hx
  have hlim : Tendsto (fun y ↦ (eLpNorm (M y - M x) ∞ stripMeasure).toReal) (𝓝[s] x) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcont x hx)
  -- `‖D_y - D_x‖ ≤ ‖M y - M x‖_{L^∞}` for `y ∈ s`.
  have hle : ∀ᶠ y in 𝓝[s] x,
      ‖jetOperator stripMeasure (M y) - jetOperator stripMeasure (M x)‖ ≤
        (eLpNorm (M y - M x) ∞ stripMeasure).toReal := by
    filter_upwards [self_mem_nhdsWithin] with y hy using norm_jetOperator_sub_le (hM y hy) (hM x hx)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hle hlim)

end Operator

/-! ### The semi-Fredholm estimate and Peetre's argument -/

section Peetre

variable {S : Submodule ℝ (ℝ × ℝ → V)}

variable (S) in
/-- The **semi-Fredholm estimate** with constants `C` and `T` for the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` on a space `S` of sections over the strip: for every `ξ ∈ S` that
vanishes for `s ∉ (a, b)`,

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`. For the test sections of the cylinder
(`TauCeti.CylinderSobolev.testSection`) this is the form proved for the linearized Floer operator
in `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`. -/
def HasSemiFredholmEstimate (M : ℝ × ℝ → V × V × V →L[ℝ] W) (C T : ℝ) : Prop :=
  ∀ ξ ∈ S, ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
        ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)

/-- The defining property of `TauCeti.StripSobolev.HasSemiFredholmEstimate`. -/
theorem hasSemiFredholmEstimate_iff {M : ℝ × ℝ → V × V × V →L[ℝ] W} {C T : ℝ} :
    HasSemiFredholmEstimate S M C T ↔
      ∀ ξ ∈ S, ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
            ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  Iff.rfl

variable [HasL2Jets S]

/-- On the jet of an element `ξ` of `S`, the first-order operator of a coefficient field `M` is
`z ↦ M z (ξ z, ∂s ξ z, ∂t ξ z)`. -/
theorem jetOperator_jetLp_ae_eq {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    (ξ : S) :
    jetOperator stripMeasure M (jetLp S ξ) =ᵐ[stripMeasure]
      fun z ↦ M z (jet (ξ : ℝ × ℝ → V) z) := by
  filter_upwards [coeFn_jetOperator hM (jetLp S ξ), coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, h₂]

/-- The squared `L²` norm of the jet of a `C¹` element of `S` is at most its `W^{1,2}` energy. -/
theorem sq_norm_jetLp_le_integral (ξ : S) (hξ : ContDiff ℝ 1 (ξ : ℝ × ℝ → V)) :
    ‖jetLp S ξ‖ ^ 2 ≤ ∫ z, (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 + ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) ∂stripMeasure := by
  have hjm := HasL2Jets.memLp_jet _ ξ.property
  rw [jetLp_apply, hjm.norm_toLp_sq]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z ↦ by positivity) ?_
    (Eventually.of_forall fun z ↦ sq_norm_jet_le _ z)
  refine ((hjm.integrable_norm_pow two_ne_zero).const_mul 3).mono' ?_
    (Eventually.of_forall fun z ↦ ?_)
  · exact (continuous_norm_partialDeriv_sq_add_norm_sq hξ).aestronglyMeasurable
  · have h₁ := norm_fderiv_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) z
    have h₂ := norm_fderiv_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) z
    have h₃ := norm_le_norm_jet (ξ : ℝ × ℝ → V) z
    rw [Real.norm_of_nonneg (by positivity)]
    linarith [pow_le_pow_left₀ (norm_nonneg _) h₁ 2, pow_le_pow_left₀ (norm_nonneg _) h₂ 2,
      pow_le_pow_left₀ (norm_nonneg _) h₃ 2]

/-- The squared `L²` norm of the restricted value of the jet of an element `ξ` of `S` is the
integral of `‖ξ‖²` over `[-T, T] × [0, 1]`. -/
private theorem sq_norm_restrictValue_jetLp (T : ℝ) (ξ : S) :
    ‖restrictValue T (jetLp S ξ)‖ ^ 2 =
      ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 := by
  have hμ : stripMeasure.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) =
      volume.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc),
      inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]
  rw [← Lp.integral_norm_sq_eq_norm_sq, ← hμ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictValue T (jetLp S ξ), ae_restrict_of_ae (coeFn_jetLp ξ)]
    with z h₁ h₂
  rw [h₁, h₂, jet_apply]

/-- A semi-Fredholm estimate gives `‖f‖ ≤ √C (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the jet `f` of
a `C¹` element of `S` vanishing for `|s|` large. -/
private theorem norm_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ} (hest : HasSemiFredholmEstimate S M C T) (ξ : S)
    (hξ : ContDiff ℝ 1 (ξ : ℝ × ℝ → V)) {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0) :
    ‖jetLp S ξ‖ ≤
      √(max C 0) * (‖jetOperator stripMeasure M (jetLp S ξ)‖ + ‖restrictValue T (jetLp S ξ)‖) := by
  set R₀ := max R 0
  have hR₀ : ∀ s t, R₀ ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR s t ((le_max_left R 0).trans hs)
  have hvan : ∀ s t, s ∉ Ioo (-R₀) R₀ → (ξ : ℝ × ℝ → V) (s, t) = 0 :=
    eq_zero_of_notMem_Ioo_neg hR₀
  set x := ‖jetOperator stripMeasure M (jetLp S ξ)‖
  set y := ‖restrictValue T (jetLp S ξ)‖
  -- The squared norms of the two terms of the estimate as integrals.
  have hx : x ^ 2 = ∫ z in Icc (-R₀) R₀ ×ˢ Icc (0 : ℝ) 1,
      ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 := by
    have hae : (fun z ↦ ‖jetOperator stripMeasure M (jetLp S ξ) z‖ ^ 2)
        =ᵐ[stripMeasure] fun z ↦ ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 :=
      (jetOperator_jetLp_ae_eq hM ξ).mono fun z hz ↦ by simp only [hz]
    rw [← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae hae]
    exact integral_strip_eq_setIntegral_of_jet_eq_zero hR₀ fun z hz ↦ by
      rw [hz, map_zero, norm_zero, zero_pow two_ne_zero]
  have hy : y ^ 2 = ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 :=
    sq_norm_restrictValue_jetLp T ξ
  have hmain := hest ξ ξ.property (neg_le_self (le_max_right R 0)) hvan
  rw [← integral_strip_eq_setIntegral_of_jet_eq_zero hR₀
    fun _ ↦ norm_partialDeriv_sq_add_norm_sq_eq_zero_of_jet_eq_zero, ← hx, ← hy] at hmain
  -- Conclude by taking square roots.
  have hsq : ‖jetLp S ξ‖ ^ 2 ≤ (√(max C 0) * (x + y)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
    calc ‖jetLp S ξ‖ ^ 2 ≤ C * (x ^ 2 + y ^ 2) := (sq_norm_jetLp_le_integral ξ hξ).trans hmain
      _ ≤ max C 0 * (x ^ 2 + y ^ 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (x + y) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          nlinarith [norm_nonneg (jetOperator stripMeasure M (jetLp S ξ)),
            norm_nonneg (restrictValue T (jetLp S ξ))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- The estimate of `norm_jetLp_le` extends from the jets of the elements of `S` to
`jetClosure S`, with the compact error term of Rellich's theorem. -/
private theorem exists_compact_estimate [IsTestSpace S] [HasCompactRestriction S]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate S M C T) :
    ∃ K : jetClosure S →L[ℝ] Lp V 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)),
      IsCompactOperator K ∧ ∀ x : jetClosure S,
        ‖x‖ ≤
          √(max C 0) * ‖(jetOperator stripMeasure M).comp (jetClosure S).subtypeL x‖ + ‖K x‖ := by
  set c := √(max C 0)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  set D := jetOperator stripMeasure M
  refine ⟨c • (restrictValue T).comp (jetClosure S).subtypeL,
    (HasCompactRestriction.isCompactOperator_restrictValue_comp_subtypeL T).smul c, ?_⟩
  -- The estimate holds on a closed set containing the jets of all elements of `S`.
  set P : Set (Lp (V × V × V) 2 stripMeasure) := {f | ‖f‖ ≤ c * ‖D f‖ + c * ‖restrictValue T f‖}
  have hP : IsClosed P := isClosed_le continuous_norm
    ((continuous_const.mul (continuous_norm.comp D.continuous)).add
      (continuous_const.mul (continuous_norm.comp (restrictValue T).continuous)))
  have hrange : Set.range (jetLp S) ⊆ P := by
    rintro _ ⟨ξ, rfl⟩
    obtain ⟨R, hR⟩ := IsTestSpace.exists_forall_le_abs_eq_zero _ ξ.property
    have hξ := IsTestSpace.contDiff _ ξ.property
    have := norm_jetLp_le hM hest ξ hξ hR
    simp only [P, mem_ofPred_eq]
    linarith
  intro x
  have := jetClosure_subset_of_isClosed hP hrange x.property
  simp only [P, mem_ofPred_eq] at this
  simpa [smul_apply, norm_smul, Real.norm_of_nonneg hc] using this

/-- **Peetre's argument: finite-dimensional kernel.** Let `S` be a space of `C¹` sections over the
strip vanishing for `|s|` large, for which Rellich's theorem holds: the restrictions to the pieces
`[-T, T] × [0, 1]` are compact operators on `jetClosure S`. If the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` of an essentially bounded coefficient field `M` satisfies the
semi-Fredholm estimate (`TauCeti.StripSobolev.HasSemiFredholmEstimate`), then its extension to
`jetClosure S` has finite-dimensional kernel. -/
theorem finiteDimensional_ker_jetOperator_comp_subtypeL [IsTestSpace S]
    [HasCompactRestriction S] {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ}
    (hest : HasSemiFredholmEstimate S M C T) :
    FiniteDimensional ℝ ((jetOperator stripMeasure M).comp (jetClosure S).subtypeL).ker := by
  obtain ⟨K, hK, hbound⟩ := exists_compact_estimate hM hest
  exact ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate _ hK hbound

/-- **Peetre's argument: closed range.** Under the hypotheses of
`finiteDimensional_ker_jetOperator_comp_subtypeL`, the extension of `D` to
`jetClosure S` has closed range in `L²(ℝ × [0, 1], W)`. -/
theorem isClosed_range_jetOperator_comp_subtypeL [CompleteSpace V] [IsTestSpace S]
    [HasCompactRestriction S] {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ}
    (hest : HasSemiFredholmEstimate S M C T) :
    IsClosed (((jetOperator stripMeasure M).comp (jetClosure S).subtypeL).range :
      Set (Lp W 2 stripMeasure)) := by
  obtain ⟨K, hK, hbound⟩ := exists_compact_estimate hM hest
  exact ContinuousLinearMap.isClosed_range_of_compact_estimate _ hK hbound

/-- An `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` over the strip bounds the restricted value of the jet of
a continuous element `ξ` of `S` by `√C' ‖D ξ‖`. -/
private theorem norm_restrictValue_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C' : ℝ} (T : ℝ) (ξ : S)
    (hξ : Continuous (ξ : ℝ × ℝ → V)) {R : ℝ} (hR : ∀ s t, R ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0)
    (hL2 : ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ‖restrictValue T (jetLp S ξ)‖ ≤ √(max C' 0) * ‖jetOperator stripMeasure M (jetLp S ξ)‖ := by
  have hint := integrable_norm_sq_of_continuous hξ hR
  have hD : ‖jetOperator stripMeasure M (jetLp S ξ)‖ ^ 2 =
      ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    exact integral_congr_ae ((jetOperator_jetLp_ae_eq hM ξ).mono fun z hz ↦ by simp only [hz])
  have hsub : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ≤
      ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure :=
    setIntegral_mono_set hint (Eventually.of_forall fun z ↦ by positivity)
      (Eventually.of_forall (prod_mono (subset_univ _) subset_rfl))
  have hsq : ‖restrictValue T (jetLp S ξ)‖ ^ 2 ≤
      (√(max C' 0) * ‖jetOperator stripMeasure M (jetLp S ξ)‖) ^ 2 := by
    rw [sq_norm_restrictValue_jetLp, mul_pow, Real.sq_sqrt (le_max_right _ _), hD]
    refine hsub.trans (hL2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_))
    exact integral_nonneg fun z ↦ by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **An estimate from below on `jetClosure S`.** Let `S` be a space of `C¹` sections over the
strip vanishing for `|s|` large, and `M` an essentially bounded coefficient field whose
first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm estimate
(`TauCeti.StripSobolev.HasSemiFredholmEstimate`). Suppose that `D` also bounds the value of every
element of `S` in `L²` over the whole strip: `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`. Then the extension of `D` to
`jetClosure S` is bounded below: `‖x‖ ≤ K ‖D x‖` for every `x`. The global `L²` bound removes the
compact error term of the semi-Fredholm estimate. -/
theorem exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL [IsTestSpace S]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ}
    (hest : HasSemiFredholmEstimate S M C T)
    (hL2 : ∀ ξ : S, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ∃ K : ℝ≥0, ∀ x : jetClosure S,
      ‖x‖ ≤ K * ‖(jetOperator stripMeasure M).comp (jetClosure S).subtypeL x‖ := by
  set c := √(max C 0) * (1 + √(max C' 0))
  have hc : 0 ≤ c := by positivity
  refine ⟨⟨c, hc⟩, ?_⟩
  -- The estimate holds on a closed set containing the jets of all elements of `S`.
  set P : Set (Lp (V × V × V) 2 stripMeasure) :=
    {f | ‖f‖ ≤ c * ‖jetOperator stripMeasure M f‖}
  have hP : IsClosed P := isClosed_le continuous_norm
    (continuous_const.mul (continuous_norm.comp (jetOperator stripMeasure M).continuous))
  have hrange : Set.range (jetLp S) ⊆ P := by
    rintro _ ⟨ξ, rfl⟩
    obtain ⟨R, hR⟩ := IsTestSpace.exists_forall_le_abs_eq_zero _ ξ.property
    have hξ := IsTestSpace.contDiff _ ξ.property
    have h₁ := norm_jetLp_le hM hest ξ hξ hR
    have h₂ := norm_restrictValue_jetLp_le hM T ξ hξ.continuous hR (hL2 ξ)
    simp only [P, mem_ofPred_eq]
    calc ‖jetLp S ξ‖
        ≤ √(max C 0) * (‖jetOperator stripMeasure M (jetLp S ξ)‖ +
          ‖restrictValue T (jetLp S ξ)‖) := h₁
      _ ≤ √(max C 0) * (‖jetOperator stripMeasure M (jetLp S ξ)‖ +
          √(max C' 0) * ‖jetOperator stripMeasure M (jetLp S ξ)‖) := by gcongr
      _ = c * ‖jetOperator stripMeasure M (jetLp S ξ)‖ := by ring
  intro x
  have := jetClosure_subset_of_isClosed hP hrange x.property
  simp only [P, mem_ofPred_eq] at this
  exact this

/-- **Injectivity on `jetClosure S`.** Under the hypotheses of
`TauCeti.StripSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`, a semi-Fredholm
estimate together with a global `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` on the elements of `S`, the
extension of `D` to `jetClosure S` has trivial kernel. -/
theorem ker_jetOperator_comp_subtypeL_eq_bot [IsTestSpace S] {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ}
    (hest : HasSemiFredholmEstimate S M C T)
    (hL2 : ∀ ξ : S, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ((jetOperator stripMeasure M).comp (jetClosure S).subtypeL).ker = ⊥ := by
  obtain ⟨K, hK⟩ := exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL hM hest hL2
  exact LinearMap.ker_eq_bot.2 ((ContinuousLinearMap.antilipschitz_of_bound _ hK).injective)

end Peetre

end TauCeti.StripSobolev
