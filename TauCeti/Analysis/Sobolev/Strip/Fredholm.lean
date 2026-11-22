/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.SemiFredholm
public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Analysis.Sobolev.Strip.Rellich
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Fredholm.ContinuousFamily
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Peetre's argument for first-order operators on the strip with boundary conditions

The linearized operators of Lagrangian Floer theory act on sections `ξ` of a trivial bundle with
fibre `V` over the strip `ℝ × [0, 1]` whose boundary values lie in two subspaces `F₀` and `F₁` of
`V`, the tangent spaces of the Lagrangians in a trivialization along the strip. Such an operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)`, with an essentially bounded coefficient field
`M : ℝ × ℝ → (V × V × V →L[ℝ] W)`, acts on `L²` jets of the strip by
`TauCeti.CylinderSobolev.jetOperator M`. That operator only involves the strip measure, so it
serves the cylinder and the strip alike, and its restriction to the Sobolev space
`TauCeti.StripSobolev.H1 F₀ F₁` is the realization `W^{1,2}_F(ℝ × [0, 1], V) → L²(ℝ × [0, 1], W)`
of `D`.

This file turns an elliptic estimate for `D` into the functional-analytic properties of that
realization, as `TauCeti.Analysis.Sobolev.Cylinder` does on the cylinder.

* **Peetre's argument.** Suppose that `D` satisfies the semi-Fredholm estimate
  (`TauCeti.StripSobolev.HasSemiFredholmEstimate`)

  `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

  for every `C²` section `ξ` with boundary values in `F₀` and `F₁` that vanishes for `|s|` large.
  Restriction to `[-T, T] × [0, 1]` is compact on `W^{1,2}_F` by Rellich's theorem
  `TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL`, so the estimate is an a
  priori estimate with compact error on `W^{1,2}_F`, and the realization of `D` has
  finite-dimensional kernel (`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`)
  and closed range (`TauCeti.StripSobolev.isClosed_range_jetOperator_comp_subtypeL`).
* **Families.** The realization depends continuously on `M` in `L^∞`
  (`TauCeti.CylinderSobolev.continuousOn_jetOperator`). So along a family of coefficient fields,
  continuous in `L^∞` on a preconnected set and each satisfying a semi-Fredholm estimate, the
  realizations are all Fredholm with the same index as soon as one of them is Fredholm
  (`TauCeti.StripSobolev.isFredholm_and_index_eq_of_hasSemiFredholmEstimate`). This is how the
  Fredholm property and the index of a strip operator are read off from a model operator joined to
  it by such a path, without the regularity of weak solutions of the adjoint equation.
* **An estimate from below.** If `D` moreover bounds every test section in `L²` over the whole
  strip, `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`, as stationary operators at nondegenerate chords do, the compact
  error disappears: `‖x‖ ≤ K ‖D x‖` on `W^{1,2}_F`
  (`TauCeti.StripSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`), and the
  realization is injective (`TauCeti.StripSobolev.ker_jetOperator_comp_subtypeL_eq_bot`).

The estimate is stated, as on the cylinder, for sections vanishing outside `(a, b) × ℝ`, with the
integrals of the left side and of `‖D ξ‖²` over `[a, b] × [0, 1]`. This is the form produced by
patching estimates on the two ends of the strip with an interior estimate.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., §3.1 and
  Appendix B, on the linearized operator with totally real boundary conditions and the
  semi-Fredholm estimate.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of operators `∂s + J ∂t + S`.
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1, on the
  stability of the index.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.StripSobolev

open CylinderSobolev (jetOperator)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {F₀ F₁ : Submodule ℝ V}

/-- The **semi-Fredholm estimate** with constants `C` and `T` for the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` on the strip `ℝ × [0, 1]` with boundary conditions `F₀` and `F₁`: for
every `C²` section `ξ` with `ξ (s, 0) ∈ F₀` and `ξ (s, 1) ∈ F₁` for all `s`, vanishing for
`s ∉ (a, b)`,

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`. -/
def HasSemiFredholmEstimate (F₀ F₁ : Submodule ℝ V) (M : ℝ × ℝ → V × V × V →L[ℝ] W)
    (C T : ℝ) : Prop :=
  ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s, ξ (s, 0) ∈ F₀) → (∀ s, ξ (s, 1) ∈ F₁) →
    ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
        C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
          ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)

/-- The defining property of `TauCeti.StripSobolev.HasSemiFredholmEstimate`. -/
theorem hasSemiFredholmEstimate_iff {M : ℝ × ℝ → V × V × V →L[ℝ] W} {C T : ℝ} :
    HasSemiFredholmEstimate F₀ F₁ M C T ↔
      ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s, ξ (s, 0) ∈ F₀) → (∀ s, ξ (s, 1) ∈ F₁) →
        ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
          ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 +
              ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
            C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖M z (jet ξ z)‖ ^ 2) +
              ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  Iff.rfl

/-- On the jet of a test section `ξ`, the first-order operator of an essentially bounded
coefficient field `M` is `z ↦ M z (ξ z, ∂s ξ z, ∂t ξ z)`. -/
theorem jetOperator_jetLp_ae_eq {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    (ξ : testSection F₀ F₁) :
    jetOperator M (jetLp (testSection F₀ F₁) ξ) =ᵐ[stripMeasure]
      fun z ↦ M z (jet (ξ : ℝ × ℝ → V) z) := by
  filter_upwards [CylinderSobolev.coeFn_jetOperator hM (jetLp (testSection F₀ F₁) ξ),
    coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, h₂]

/-- The squared norm of the restricted value of the jet of a test section is the integral of
`‖ξ‖²` over `[-T, T] × [0, 1]`. -/
private theorem sq_norm_restrictValue_jetLp (T : ℝ) (ξ : testSection F₀ F₁) :
    ‖restrictValue T (jetLp (testSection F₀ F₁) ξ)‖ ^ 2 =
      ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 := by
  -- On subsets of the strip, the strip measure is Lebesgue measure.
  have hμ : stripMeasure.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) =
      volume.restrict (Icc (-T) T ×ˢ Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc),
      inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]
  rw [← Lp.integral_norm_sq_eq_norm_sq, ← hμ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictValue T (jetLp (testSection F₀ F₁) ξ),
    ae_restrict_of_ae (coeFn_jetLp ξ)] with z h₁ h₂
  rw [h₁, h₂, jet_apply]

/-- The squared `L²` norm of the jet of a test section vanishing for `|s| ≥ R` is at most its
`W^{1,2}` energy over `[-R, R] × [0, 1]`. -/
private theorem sq_norm_jetLp_le_setIntegral (ξ : testSection F₀ F₁) {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0) :
    ‖jetLp (testSection F₀ F₁) ξ‖ ^ 2 ≤ ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1,
      (‖fderiv ℝ (ξ : ℝ × ℝ → V) z (1, 0)‖ ^ 2 + ‖fderiv ℝ (ξ : ℝ × ℝ → V) z (0, 1)‖ ^ 2 +
        ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) := by
  have hξ := (mem_testSection_iff.1 ξ.property).1
  have hd := hξ.continuous_fderiv (by norm_num)
  have h0 := hξ.continuous
  have hK : IsCompact (Icc (-R) R ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  rw [sq_norm_jetLp, integral_strip_eq_setIntegral_of_jet_eq_zero hR fun z hz ↦ by simp [hz]]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_Icc.prod measurableSet_Icc)
    fun z _ ↦ sq_norm_jet_le _ z
  · exact ((continuous_jet (contDiff_one_of_mem_testSection ξ.property)).norm.pow 2).continuousOn
      |>.integrableOn_compact hK
  · exact ContinuousOn.integrableOn_compact hK (Continuous.continuousOn (by fun_prop))

/-- A semi-Fredholm estimate gives `‖f‖ ≤ √C (‖D f‖ + ‖f|_{[-T, T] × [0, 1]}‖)` on the jets of
test sections. -/
private theorem norm_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    {C T : ℝ} (hest : HasSemiFredholmEstimate F₀ F₁ M C T) (ξ : testSection F₀ F₁) :
    ‖jetLp (testSection F₀ F₁) ξ‖ ≤
      √(max C 0) * (‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖ +
        ‖restrictValue T (jetLp (testSection F₀ F₁) ξ)‖) := by
  obtain ⟨hξ, hξ₀, hξ₁, R, hR⟩ := mem_testSection_iff.1 ξ.property
  set R₀ := max R 0
  have hR₀ : ∀ s t, R₀ ≤ |s| → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR s t ((le_max_left R 0).trans hs)
  have hvan : ∀ s t, s ∉ Ioo (-R₀) R₀ → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hR₀ s t (by rwa [mem_Ioo, ← abs_lt, not_lt] at hs)
  set x := ‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖
  set y := ‖restrictValue T (jetLp (testSection F₀ F₁) ξ)‖
  -- The squared norms of the two terms of the estimate as integrals.
  have hx : x ^ 2 = ∫ z in Icc (-R₀) R₀ ×ˢ Icc (0 : ℝ) 1,
      ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 := by
    have hae : (fun z ↦ ‖jetOperator M (jetLp (testSection F₀ F₁) ξ) z‖ ^ 2) =ᵐ[stripMeasure]
        fun z ↦ ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 :=
      (jetOperator_jetLp_ae_eq hM ξ).mono fun z hz ↦ by simp only [hz]
    rw [← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae hae]
    exact integral_strip_eq_setIntegral_of_jet_eq_zero hR₀ fun z hz ↦ by simp [hz]
  have hy : y ^ 2 = ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 :=
    sq_norm_restrictValue_jetLp T ξ
  have hmain := hest hξ hξ₀ hξ₁ (neg_le_self (le_max_right R 0)) hvan
  rw [← hx, ← hy] at hmain
  -- Conclude by taking square roots.
  have hsq : ‖jetLp (testSection F₀ F₁) ξ‖ ^ 2 ≤ (√(max C 0) * (x + y)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
    calc ‖jetLp (testSection F₀ F₁) ξ‖ ^ 2 ≤ C * (x ^ 2 + y ^ 2) :=
          (sq_norm_jetLp_le_setIntegral ξ hR₀).trans hmain
      _ ≤ max C 0 * (x ^ 2 + y ^ 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (x + y) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          nlinarith [norm_nonneg (jetOperator M (jetLp (testSection F₀ F₁) ξ)),
            norm_nonneg (restrictValue T (jetLp (testSection F₀ F₁) ξ))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- The estimate of `norm_jetLp_le` extends from the jets of test sections to `W^{1,2}_F`, with a
compact error term. -/
private theorem exists_compact_estimate [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T) :
    ∃ K : H1 F₀ F₁ →L[ℝ] Lp V 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)),
      IsCompactOperator K ∧ ∀ x : H1 F₀ F₁,
        ‖x‖ ≤ √(max C 0) * ‖(jetOperator M).comp (H1 F₀ F₁).subtypeL x‖ + ‖K x‖ := by
  set c := √(max C 0)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  refine ⟨c • (restrictValue T).comp (H1 F₀ F₁).subtypeL,
    (isCompactOperator_restrictValue_comp_subtypeL F₀ F₁ T).smul c, fun x ↦ ?_⟩
  -- The estimate is a closed condition, and it holds on the dense jets of test sections.
  refine H1_induction (P := fun x ↦ ‖x‖ ≤ c * ‖(jetOperator M).comp (H1 F₀ F₁).subtypeL x‖ +
    ‖(c • (restrictValue T).comp (H1 F₀ F₁).subtypeL) x‖)
    (isClosed_le continuous_norm (by fun_prop)) (fun ξ ↦ ?_) x
  have := norm_jetLp_le hM hest ξ
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coe_jetH1,
    smul_apply, norm_smul, Real.norm_of_nonneg hc, ← Submodule.norm_coe]
  linarith

/-- **Peetre's argument on the strip: finite-dimensional kernel.** Let `M` be an essentially
bounded coefficient field on the strip `ℝ × [0, 1]`, and suppose the first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm estimate
(`TauCeti.StripSobolev.HasSemiFredholmEstimate`)

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]` for every `C²` section `ξ` with boundary values in `F₀` and `F₁` vanishing
for `s ∉ (a, b)`. Then the realization of `D` on `W^{1,2}_F(ℝ × [0, 1], V)` has
finite-dimensional kernel. -/
theorem finiteDimensional_ker_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T) :
    FiniteDimensional ℝ ((jetOperator M).comp (H1 F₀ F₁).subtypeL).ker := by
  obtain ⟨K, hK, hbound⟩ := exists_compact_estimate hM hest
  exact ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate _ hK hbound

/-- **Peetre's argument on the strip: closed range.** Under the semi-Fredholm estimate of
`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`, the realization of `D` on
`W^{1,2}_F(ℝ × [0, 1], V)` has closed range in `L²(ℝ × [0, 1], W)`. -/
theorem isClosed_range_jetOperator_comp_subtypeL [FiniteDimensional ℝ V]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T) :
    IsClosed (((jetOperator M).comp (H1 F₀ F₁).subtypeL).range :
      Set (Lp W 2 stripMeasure)) := by
  obtain ⟨K, hK, hbound⟩ := exists_compact_estimate hM hest
  exact ContinuousLinearMap.isClosed_range_of_compact_estimate _ hK hbound

/-- **Fredholmness and the index along families of strip operators.** Let `M x` be essentially
bounded coefficient fields on the strip, depending continuously on `x` in `L^∞` on a
preconnected set `s`, whose first-order operators `D_x ξ = M x (ξ, ∂s ξ, ∂t ξ)` each satisfy a
semi-Fredholm estimate with boundary conditions `F₀` and `F₁`. If the realization
`D_{x₀} : W^{1,2}_F(ℝ × [0, 1], V) → L²(ℝ × [0, 1], W)` is Fredholm for one `x₀ ∈ s`, then every
`D_x` with `x ∈ s` is Fredholm, with the same index. -/
theorem isFredholm_and_index_eq_of_hasSemiFredholmEstimate [FiniteDimensional ℝ V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {M : X → ℝ × ℝ → V × V × V →L[ℝ] W} (hM : ∀ x ∈ s, MemLp (M x) ∞ stripMeasure)
    (hcont : ∀ x ∈ s, Tendsto (fun y ↦ eLpNorm (M y - M x) ∞ stripMeasure) (𝓝[s] x) (𝓝 0))
    (hest : ∀ x ∈ s, ∃ C T, HasSemiFredholmEstimate F₀ F₁ (M x) C T) {x₀ x : X}
    (hx₀ : x₀ ∈ s) (hx : x ∈ s)
    (h₀ : ((jetOperator (M x₀)).comp (H1 F₀ F₁).subtypeL).IsFredholm) :
    ((jetOperator (M x)).comp (H1 F₀ F₁).subtypeL).IsFredholm ∧
      ((jetOperator (M x)).comp (H1 F₀ F₁).subtypeL).index =
        ((jetOperator (M x₀)).comp (H1 F₀ F₁).subtypeL).index := by
  have hT : ContinuousOn (fun y ↦ (jetOperator (M y)).comp (H1 F₀ F₁).subtypeL) s :=
    (CylinderSobolev.continuousOn_jetOperator hM hcont).clm_comp continuousOn_const
  have hF : ∀ y ∈ s, ((jetOperator (M y)).comp (H1 F₀ F₁).subtypeL).IsFredholm := fun y hy ↦
    hT.isFredholm_of_isPreconnected
      (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
        finiteDimensional_ker_jetOperator_comp_subtypeL (hM z hz) h)
      (fun z hz ↦ (hest z hz).elim fun _ ⟨_, h⟩ ↦
        isClosed_range_jetOperator_comp_subtypeL (hM z hz) h) hs hx₀ h₀ hy
  exact ⟨hF x hx, ContinuousOn.index_eq_of_isPreconnected hT hF hs hx hx₀⟩

/-- An `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` over the strip bounds the restricted value of the jet of
a test section by `√C' ‖D ξ‖`. -/
private theorem norm_restrictValue_jetLp_le {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C' : ℝ} (T : ℝ) (ξ : testSection F₀ F₁)
    (hL2 : ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ‖restrictValue T (jetLp (testSection F₀ F₁) ξ)‖ ≤
      √(max C' 0) * ‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖ := by
  obtain ⟨hξ, -, -, R, hR⟩ := mem_testSection_iff.1 ξ.property
  -- `‖ξ‖²` is integrable on the strip: it is continuous and vanishes for `|s| ≥ R`.
  have hint : Integrable (fun z ↦ ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) stripMeasure := by
    have hK : IsCompact (Icc (-R) R ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
    refine (hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact hK
      |>.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ ?_
    obtain ⟨s, t⟩ := z
    have h : s ∉ Icc (-R) R := fun h ↦ hz.2 ⟨h, hz.1.2⟩
    rw [mem_Icc, ← abs_le, not_le] at h
    simp [hR s t h.le]
  have hD : ‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖ ^ 2 =
      ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    exact integral_congr_ae ((jetOperator_jetLp_ae_eq hM ξ).mono fun z hz ↦ by simp only [hz])
  have hsub : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ≤
      ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure :=
    setIntegral_mono_set hint (Eventually.of_forall fun z ↦ by positivity)
      (Eventually.of_forall (prod_mono (subset_univ _) subset_rfl))
  have hsq : ‖restrictValue T (jetLp (testSection F₀ F₁) ξ)‖ ^ 2 ≤
      (√(max C' 0) * ‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖) ^ 2 := by
    rw [sq_norm_restrictValue_jetLp, mul_pow, Real.sq_sqrt (le_max_right _ _), hD]
    refine hsub.trans (hL2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_))
    exact integral_nonneg fun z ↦ by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **An estimate from below on `W^{1,2}_F`.** Let `M` be an essentially bounded coefficient field
on the strip whose first-order operator `D ξ = M (ξ, ∂s ξ, ∂t ξ)` satisfies the semi-Fredholm
estimate (`TauCeti.StripSobolev.HasSemiFredholmEstimate`) with boundary conditions `F₀` and `F₁`,
and suppose that `D` also bounds the value of every test section in `L²` over the whole strip:
`∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²`. Then the realization of `D` on `W^{1,2}_F(ℝ × [0, 1], V)` is bounded
below: `‖x‖ ≤ K ‖D x‖` for every `x`. The global `L²` bound removes the compact error term of the
semi-Fredholm estimate. -/
theorem exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ}
    (hest : HasSemiFredholmEstimate F₀ F₁ M C T)
    (hL2 : ∀ ξ : testSection F₀ F₁, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ∃ K : ℝ≥0, ∀ x : H1 F₀ F₁, ‖x‖ ≤ K * ‖(jetOperator M).comp (H1 F₀ F₁).subtypeL x‖ := by
  set c := √(max C 0) * (1 + √(max C' 0))
  have hc : 0 ≤ c := by positivity
  refine ⟨⟨c, hc⟩, fun x ↦ ?_⟩
  -- The estimate is a closed condition, and it holds on the dense jets of test sections.
  refine H1_induction (P := fun x ↦ ‖x‖ ≤ c * ‖(jetOperator M).comp (H1 F₀ F₁).subtypeL x‖)
    (isClosed_le continuous_norm (by fun_prop)) (fun ξ ↦ ?_) x
  have h₁ := norm_jetLp_le hM hest ξ
  have h₂ := norm_restrictValue_jetLp_le hM T ξ (hL2 ξ)
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coe_jetH1,
    ← Submodule.norm_coe]
  calc ‖jetLp (testSection F₀ F₁) ξ‖
      ≤ √(max C 0) * (‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖ +
        ‖restrictValue T (jetLp (testSection F₀ F₁) ξ)‖) := h₁
    _ ≤ √(max C 0) * (‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖ +
        √(max C' 0) * ‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖) := by gcongr
    _ = c * ‖jetOperator M (jetLp (testSection F₀ F₁) ξ)‖ := by ring

/-- **Injectivity on `W^{1,2}_F`.** Under the hypotheses of
`TauCeti.StripSobolev.exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL`, a semi-Fredholm
estimate together with a global `L²` bound `∫ ‖ξ‖² ≤ C' ∫ ‖D ξ‖²` on test sections, the
realization of `D` on `W^{1,2}_F(ℝ × [0, 1], V)` has trivial kernel. -/
theorem ker_jetOperator_comp_subtypeL_eq_bot {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) {C T C' : ℝ} (hest : HasSemiFredholmEstimate F₀ F₁ M C T)
    (hL2 : ∀ ξ : testSection F₀ F₁, ∫ z, ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 ∂stripMeasure ≤
      C' * ∫ z, ‖M z (jet (ξ : ℝ × ℝ → V) z)‖ ^ 2 ∂stripMeasure) :
    ((jetOperator M).comp (H1 F₀ F₁).subtypeL).ker = ⊥ := by
  obtain ⟨K, hK⟩ := exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL hM hest hL2
  exact LinearMap.ker_eq_bot.2 ((ContinuousLinearMap.antilipschitz_of_bound _ hK).injective)

end TauCeti.StripSobolev
