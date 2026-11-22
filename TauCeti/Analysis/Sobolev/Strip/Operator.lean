/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Fredholm.SemiFredholm
public import TauCeti.Analysis.Sobolev.JetOperator
public import TauCeti.Analysis.Sobolev.Strip.Jet
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# First-order operators on `L²` jets of the strip and Peetre's argument

A first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` on sections `ξ : ℝ × ℝ → V` over the strip
`ℝ × [0, 1]`, with an essentially bounded coefficient field
`M : ℝ × ℝ → (V × V × V →L[ℝ] W)`, acts on `L²` jets of the strip by
`TauCeti.jetOperator stripMeasure M`, the operator of `TauCeti.Analysis.Sobolev.JetOperator`
for the strip measure. It serves every Sobolev space built from jets over the strip: the
Sobolev space of the strip with boundary conditions in `TauCeti.Analysis.Sobolev.Strip.Basic`
and that of the cylinder `ℝ × S¹`, whose fundamental domain is the strip, in
`TauCeti.Analysis.Sobolev.Cylinder`. This file proves the steps of Peetre's argument that hold
for any space `S` of sections with square integrable jets (`TauCeti.StripSobolev.HasL2Jets`);
each geometry supplies its own semi-Fredholm estimate and its own Rellich theorem.

* The operator acts pointwise on `L²` jets (`TauCeti.coeFn_jetOperator`), and on the jet of a
  section `ξ` it is `z ↦ M z (ξ z, ∂s ξ z, ∂t ξ z)`
  (`TauCeti.StripSobolev.jetOperator_jetLp_ae_eq`). It depends continuously on its coefficient
  field in `L^∞` (`TauCeti.continuousOn_jetOperator`).
* **The pointwise step of Peetre's argument.** The semi-Fredholm estimate

  `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

  for a single `C¹` section vanishing for `|s|` large bounds its jet
  (`TauCeti.StripSobolev.norm_jetLp_le_of_setIntegral_le`).
* **Peetre's argument.** If restriction to `[-T, T] × [0, 1]` is compact on `jetClosure S`, such
  bounds on the jets of the elements of `S` give finite-dimensional kernel and closed range of
  the realization of `D` on `jetClosure S`
  (`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le`
  and `TauCeti.StripSobolev.isClosed_range_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le`), by
  `ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`.
* **An estimate from below.** A global `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` bounds the restricted
  value (`TauCeti.StripSobolev.norm_restrictValue_jetLp_le`), and then the compact error term
  disappears:
  `TauCeti.StripSobolev.norm_le_mul_norm_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le`.
* **Families.** Along a family of coefficient fields continuous in `L^∞` on a preconnected set,
  whose realizations on a complete subspace of `L²` jets all have finite-dimensional kernel and
  closed range, Fredholmness and the index are constant once one member is Fredholm
  (`TauCeti.StripSobolev.isFredholm_and_index_eq_of_isPreconnected`). Continuity in `L^∞`
  follows from uniform closeness of continuous fields on the strip
  (`TauCeti.StripSobolev.tendsto_eLpNorm_sub_of_forall_dist_lt`). This is the abstract
  stability `ContinuousOn.isFredholm_of_isPreconnected`, which needs the target `L²` space to be a
  Hilbert space, so `W` is an inner product space there.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on the semi-Fredholm estimate.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S`.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1, on the
  stability of the index.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti.StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section Operator

variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {S : Submodule ℝ (ℝ × ℝ → V)} [HasL2Jets S]

/-- On the jet of an element `ξ` of a space of sections with square integrable jets, the
first-order operator of a coefficient field `M` is `z ↦ M z (ξ z, ∂s ξ z, ∂t ξ z)`. -/
theorem jetOperator_jetLp_ae_eq {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    (ξ : S) :
    jetOperator stripMeasure M (jetLp S ξ) =ᵐ[stripMeasure]
      fun z ↦ M z (jet (ξ : ℝ × ℝ → V) z) := by
  filter_upwards [coeFn_jetOperator hM (jetLp S ξ), coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, h₂]

/-- The squared norm of the first-order operator of `M` on the jet of an element `ξ` of a space of
sections with square integrable jets is the integral of `‖M (ξ, ∂s ξ, ∂t ξ)‖²` over the strip. -/
theorem sq_norm_jetOperator_jetLp {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) (ξ : S) :
    ‖jetOperator stripMeasure M (jetLp S ξ)‖ ^ 2 =
      ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  exact integral_congr_ae ((jetOperator_jetLp_ae_eq hM ξ).mono fun z hz ↦ by simp only [hz])

/-! #### Peetre's argument on a space of sections with square integrable jets

The steps below hold for any space `S` of sections with square integrable jets: they produce
estimates on `jetClosure S` from estimates on the jets of the elements of `S`. The Sobolev spaces
of the cylinder and of the strip with boundary conditions are both of the form `jetClosure S`. -/

/-- If `a ^ 2 ≤ max C 0 * b ^ 2` with `0 ≤ b`, then `a ≤ √(max C 0) * b`. -/
private theorem le_sqrt_max_mul_of_sq_le {a b C : ℝ} (hb : 0 ≤ b)
    (h : a ^ 2 ≤ max C 0 * b ^ 2) : a ≤ √(max C 0) * b := by
  rw [← Real.sqrt_sq hb, ← Real.sqrt_mul (le_max_right _ _)]
  exact Real.le_sqrt_of_sq_le h

/-- The squared `L²` norm of the jet of a `C¹` element of `S` vanishing for `|s| ≥ R` is at most
its `W^{1,2}` energy over `[-R, R] × [0, 1]`. -/
private theorem sq_norm_jetLp_le_setIntegral {ξ : S} (hξ : ContDiff ℝ 1 (ξ : ℝ × ℝ → V))
    {R : ℝ} (hR : ∀ s t, R ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0) :
    ‖jetLp S ξ‖ ^ 2 ≤ ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1,
      (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 + ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 +
        ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) := by
  have := hξ.continuous_fderiv (by norm_num)
  have := hξ.continuous
  have hK : IsCompact (Icc (-R) R ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  rw [sq_norm_jetLp, integral_strip_eq_setIntegral_of_jet_eq_zero hR fun z hz ↦ by simp [hz]]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_Icc.prod measurableSet_Icc)
    fun z _ ↦ sq_norm_jet_le _ z
  · exact ((continuous_jet hξ).norm.pow 2).continuousOn.integrableOn_compact hK
  · exact ContinuousOn.integrableOn_compact hK (Continuous.continuousOn (by fun_prop))

/-- **The pointwise step of Peetre's argument.** Let `ξ` be a `C¹` element of a space `S` of
sections with square integrable jets, vanishing for `|s| ≥ R`, and suppose that the first-order
operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm estimate

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for `ξ`, the first two integrals over `[-R, R] × [0, 1]`. Then the jet `f` of `ξ` satisfies
`‖f‖ ≤ √C (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)`. -/
theorem norm_jetLp_le_of_setIntegral_le {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T R : ℝ} {ξ : S} (hξ : ContDiff ℝ 1 (ξ : ℝ × ℝ → V))
    (hR : ∀ s t, R ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0)
    (hest : ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 + ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) ≤
      C * ((∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2) +
        ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2)) :
    ‖jetLp S ξ‖ ≤
      √(max C 0) *
        (‖jetOperator stripMeasure M (jetLp S ξ)‖ + ‖restrictValue T (jetLp S ξ)‖) := by
  set x := ‖jetOperator stripMeasure M (jetLp S ξ)‖
  set y := ‖restrictValue T (jetLp S ξ)‖
  -- The squared norms of the two terms of the estimate as integrals.
  have hx : x ^ 2 = ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 := by
    rw [sq_norm_jetOperator_jetLp hM]
    exact integral_strip_eq_setIntegral_of_jet_eq_zero hR fun z hz ↦ by simp [hz]
  have hy : y ^ 2 = ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 :=
    sq_norm_restrictValue_jetLp T ξ
  rw [← hx, ← hy] at hest
  refine le_sqrt_max_mul_of_sq_le (by positivity) ?_
  calc ‖jetLp S ξ‖ ^ 2 ≤ C * (x ^ 2 + y ^ 2) := (sq_norm_jetLp_le_setIntegral hξ hR).trans hest
    _ ≤ max C 0 * (x ^ 2 + y ^ 2) := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (x + y) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
        nlinarith [norm_nonneg (jetOperator stripMeasure M (jetLp S ξ)),
          norm_nonneg (restrictValue T (jetLp S ξ))]

/-- An `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` over the strip, for a continuous element `ξ` of a space
`S` of sections with square integrable jets vanishing for `|s| ≥ R`, bounds the restricted value
of the jet of `ξ` by `√C' ‖D ξ‖`. -/
theorem norm_restrictValue_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C' : ℝ} (T : ℝ) {ξ : S} (hξ : Continuous (ξ : ℝ × ℝ → V))
    {R : ℝ} (hR : ∀ s t, R ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0)
    (hL2 : ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ‖restrictValue T (jetLp S ξ)‖ ≤
      √(max C' 0) * ‖jetOperator stripMeasure M (jetLp S ξ)‖ := by
  have hint := integrable_of_jet_eq_zero hR (hξ.norm.pow 2)
    fun z h ↦ by rw [jet_apply, Prod.mk_eq_zero] at h; simp [h.1]
  have hsub : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ≤
      ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure :=
    setIntegral_mono_set hint (Eventually.of_forall fun z ↦ by positivity)
      (Eventually.of_forall (prod_mono (subset_univ _) subset_rfl))
  refine le_sqrt_max_mul_of_sq_le (norm_nonneg _) ?_
  rw [sq_norm_restrictValue_jetLp, sq_norm_jetOperator_jetLp hM]
  refine hsub.trans (hL2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_))
  exact integral_nonneg fun z ↦ by positivity

/-- A bound `‖f‖ ≤ c (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the jets `f` of the elements of `S`
extends to `jetClosure S`, with the restricted value as a compact error term. -/
private theorem norm_le_of_forall_norm_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W} {c T : ℝ}
    (hest : ∀ ξ : S, ‖jetLp S ξ‖ ≤
      c * (‖jetOperator stripMeasure M (jetLp S ξ)‖ + ‖restrictValue T (jetLp S ξ)‖))
    (x : jetClosure S) :
    ‖x‖ ≤ c * ‖(jetOperator stripMeasure M).comp (jetClosure S).subtypeL x‖ +
      ‖(c • (restrictValue T).comp (jetClosure S).subtypeL) x‖ := by
  -- The estimate is a closed condition, and it holds on the jets of the elements of `S`.
  have hx := jetClosure_subset_of_isClosed
    (s := {f | ‖f‖ ≤ c * (‖jetOperator stripMeasure M f‖ + ‖restrictValue T f‖)})
    (isClosed_le continuous_norm (by fun_prop)) (by rintro _ ⟨ξ, rfl⟩; exact hest ξ) x.property
  simp only [mem_ofPred_eq] at hx
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, smul_apply, norm_smul,
    Real.norm_eq_abs, ← Submodule.norm_coe]
  nlinarith [mul_le_mul_of_nonneg_right (le_abs_self c)
    (norm_nonneg (restrictValue T (x : Lp (V × V × V) 2 stripMeasure)))]

/-- **Peetre's argument: finite-dimensional kernel.** Let `S` be a space of sections with square
integrable jets such that restriction to `[-T, T] × [0, 1]` is a compact operator on
`jetClosure S`, as Rellich's theorem gives for the Sobolev spaces of the cylinder and the strip.
If the first-order operator `D` of `M` satisfies `‖f‖ ≤ c (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the
jets `f` of the elements of `S`, then its realization on `jetClosure S` has finite-dimensional
kernel. -/
theorem finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} {c T : ℝ}
    (hK : IsCompactOperator ((restrictValue (V := V) T).comp (jetClosure S).subtypeL))
    (hest : ∀ ξ : S, ‖jetLp S ξ‖ ≤
      c * (‖jetOperator stripMeasure M (jetLp S ξ)‖ + ‖restrictValue T (jetLp S ξ)‖)) :
    FiniteDimensional ℝ ((jetOperator stripMeasure M).comp (jetClosure S).subtypeL).ker :=
  ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate _ (hK.smul c)
    (norm_le_of_forall_norm_jetLp_le hest)

/-- **Peetre's argument: closed range.** Under the hypotheses of
`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le`,
the realization on `jetClosure S` of the first-order operator `D` of `M` has closed range. -/
theorem isClosed_range_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le [CompleteSpace V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} {c T : ℝ}
    (hK : IsCompactOperator ((restrictValue (V := V) T).comp (jetClosure S).subtypeL))
    (hest : ∀ ξ : S, ‖jetLp S ξ‖ ≤
      c * (‖jetOperator stripMeasure M (jetLp S ξ)‖ + ‖restrictValue T (jetLp S ξ)‖)) :
    IsClosed (((jetOperator stripMeasure M).comp (jetClosure S).subtypeL).range :
      Set (Lp W 2 stripMeasure)) :=
  ContinuousLinearMap.isClosed_range_of_compact_estimate _ (hK.smul c)
    (norm_le_of_forall_norm_jetLp_le hest)

/-- **An estimate from below on `jetClosure S`.** Suppose that the first-order operator `D` of `M`
satisfies `‖f‖ ≤ c (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` with `0 ≤ c`, and that it bounds the
restricted value, `‖f|_{[-T, T] × [0, 1]}‖ ≤ c' ‖D f‖`, on the jets `f` of the elements of `S`.
Then `‖x‖ ≤ c (1 + c') ‖D x‖` for every `x` in `jetClosure S`. -/
theorem norm_le_mul_norm_jetOperator_comp_subtypeL_of_forall_norm_jetLp_le
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} {c c' T : ℝ} (hc : 0 ≤ c)
    (hest : ∀ ξ : S, ‖jetLp S ξ‖ ≤
      c * (‖jetOperator stripMeasure M (jetLp S ξ)‖ + ‖restrictValue T (jetLp S ξ)‖))
    (hL2 : ∀ ξ : S,
      ‖restrictValue T (jetLp S ξ)‖ ≤ c' * ‖jetOperator stripMeasure M (jetLp S ξ)‖)
    (x : jetClosure S) :
    ‖x‖ ≤ c * (1 + c') * ‖(jetOperator stripMeasure M).comp (jetClosure S).subtypeL x‖ := by
  -- The estimate is a closed condition, and it holds on the jets of the elements of `S`.
  refine jetClosure_subset_of_isClosed
    (s := {f | ‖f‖ ≤ c * (1 + c') * ‖jetOperator stripMeasure M f‖})
    (isClosed_le continuous_norm (by fun_prop)) ?_ x.property
  rintro _ ⟨ξ, rfl⟩
  set d := ‖jetOperator stripMeasure M (jetLp S ξ)‖
  calc ‖jetLp S ξ‖ ≤ c * (d + ‖restrictValue T (jetLp S ξ)‖) := hest ξ
    _ ≤ c * (d + c' * d) := by
        gcongr; exact hL2 ξ
    _ = c * (1 + c') * d := by ring

end Operator

/-- **Continuity in `L^∞` from uniform closeness on the strip.** A family of continuous fields
`M μ` on `ℝ × ℝ` that are uniformly close to `M lam` on the strip `ℝ × [0, 1]` for `μ` close
to `lam` depends continuously on `μ` at `lam` in `L^∞` of the strip. -/
theorem tendsto_eLpNorm_sub_of_forall_dist_lt {E : Type*} [NormedAddCommGroup E]
    {M : ℝ → ℝ × ℝ → E} (hM : ∀ μ, Continuous (M μ)) {lam : ℝ}
    (h : ∀ r > 0, ∃ η > 0, ∀ μ, |μ - lam| < η → ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 →
      dist (M μ z) (M lam z) < r) :
    Tendsto (fun μ ↦ eLpNorm (M μ - M lam) ∞ stripMeasure) (𝓝 lam) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  obtain ⟨η, hη, h⟩ := h r (ENNReal.ofReal_pos.1 hr)
  filter_upwards [Metric.ball_mem_nhds lam hη] with μ hμ
  rw [Metric.mem_ball, Real.dist_eq] at hμ
  refine le_trans ?_ hrε.le
  rw [eLpNorm_exponent_top ((hM μ).sub (hM lam)).aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_bound ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
  rw [Pi.sub_apply, ← dist_eq_norm]
  exact (h μ hμ z hz.2).le

section Family

variable {X : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [TopologicalSpace X]

/-- **Fredholmness and the index along families of first-order operators.** Let `M x` be
essentially bounded coefficient fields on the strip, depending continuously on `x` in `L^∞` on a
preconnected set `s`, and let `H` be a complete subspace of `L²` jets, such as the Sobolev space of
the cylinder or of the strip with boundary conditions. If the realizations of the first-order
operators `D_x ξ = M x (ξ, ∂s ξ, ∂t ξ)` on `H` all have finite-dimensional kernel and closed range,
and `D_{x₀}` is Fredholm for one `x₀ ∈ s`, then every `D_x` with `x ∈ s` is Fredholm, with the same
index. -/
theorem isFredholm_and_index_eq_of_isPreconnected
    {H : Submodule ℝ (Lp (V × V × V) 2 stripMeasure)} [CompleteSpace H] {s : Set X}
    (hs : IsPreconnected s) {M : X → ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0))
    (hker : ∀ x ∈ s, FiniteDimensional ℝ ((jetOperator stripMeasure (M x)).comp H.subtypeL).ker)
    (hrange : ∀ x ∈ s, IsClosed (((jetOperator stripMeasure (M x)).comp H.subtypeL).range :
      Set (Lp W 2 stripMeasure)))
    {x₀ x : X} (hx₀ : x₀ ∈ s) (hx : x ∈ s)
    (h₀ : ((jetOperator stripMeasure (M x₀)).comp H.subtypeL).IsFredholm) :
    ((jetOperator stripMeasure (M x)).comp H.subtypeL).IsFredholm ∧
      ((jetOperator stripMeasure (M x)).comp H.subtypeL).index =
        ((jetOperator stripMeasure (M x₀)).comp H.subtypeL).index := by
  have hT : ContinuousOn (fun y ↦ (jetOperator stripMeasure (M y)).comp H.subtypeL) s :=
    (continuousOn_jetOperator hM hcont).clm_comp continuousOn_const
  have hF : ∀ y ∈ s, ((jetOperator stripMeasure (M y)).comp H.subtypeL).IsFredholm := fun y hy ↦
    hT.isFredholm_of_isPreconnected hker hrange hs hx₀ h₀ hy
  exact ⟨hF x hx, ContinuousOn.index_eq_of_isPreconnected hT hF hs hx hx₀⟩

end Family

end TauCeti.StripSobolev
