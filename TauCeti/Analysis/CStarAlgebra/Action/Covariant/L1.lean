/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Vector-valued integrated forms of covariant pairs on Bochner `L¹`

Let `P : CovariantRepresentation α H` be a covariant representation of a point-norm continuous
action `α : CStarAction G A` on a Hilbert space `H`. In
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed`, the integrated form on `C_c(G, A)` is
extended by continuity to `P.integratedOperatorL1 μ` on the abstract `L¹` completion
`UniformSpace.Completion (ConvolutionAlgebra α μ)`.

Here we construct the integrated form directly on the Bochner space `Lp A 1 μ` by Hilbert-space
vector integration,
`(P.integratedLp μ f) v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ`,
for any inner-regular Borel measure (`[R1Space G] [BorelSpace G] [μ.InnerRegularCompactLTTop]`), and
prove that it matches `P.integratedOperatorL1 μ` across `ConvolutionAlgebra.completionEquivL1`.

Strong measurability of the integrand `g ↦ P.coefficient (f g) (P.group g v)` uses neither
separability of `A` or `H`, second countability of `G`, nor operator-norm continuity of `P.group`:
on the σ-finite support of `f`, inner regularity exhausts finite-measure sets by compact sets up to
null sets, on each of which the continuous orbit `g ↦ P.group g v` has compact, hence separable,
image (`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply`). Coefficient algebras
may be nonunital or zero, representations may be degenerate or act on the zero Hilbert space, and
measures need not have full support.

## Main definitions and results

* `CovariantRepresentation.integrable_integrand_of_integrable`: for `hf : Integrable f μ`, the
  Hilbert-space integrand `g ↦ P.coefficient (f g) (P.group g v)` is Bochner integrable.
* `CovariantRepresentation.integratedLp`: the contractive continuous linear map
  `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` given by the vector integral.
* `CovariantRepresentation.exists_integratedOperator`: every Bochner-integrable `f : G → A` has a
  bounded integrated operator `T` with `T ξ = ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ` and
  `‖T‖ ≤ ∫ g, ‖f g‖ ∂μ`.
* `CovariantRepresentation.integratedLp_compLp_mul`,
  `CovariantRepresentation.integratedLp_translateLp`: left coefficient covariance and group
  covariance directly on `Lp A 1 μ`.
* `CovariantRepresentation.integratedLp_completionEquivL1`,
  `CovariantRepresentation.integratedOperatorL1_completionEquivL1_symm`: agreement of
  `P.integratedLp μ` with `P.integratedOperatorL1 μ` across `completionEquivL1`.
* `CovariantRepresentation.integratedLp_convolutionL1`,
  `CovariantRepresentation.integratedOperatorL1_star`,
  `CovariantRepresentation.integratedStarAlgHomL1`,
  `CovariantRepresentation.integratedLp_twistedInvolutionL1`: multiplicativity under
  `CStarAction.convolutionL1` and compatibility with the `⋆`-involution.
* `CovariantRepresentation.integratedLp_smulRight`, `CovariantRepresentation.trivial_integratedLp`:
  comparison with the scalar `ContRepresentation.integratedOperatorL1` on elementary tensors
  `φ ⊗ a` and specialization to the trivial covariant representation.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2 (§2.3, Proposition 2.23).
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

section IntegratedLp

variable {G A H : Type*} [Group G] [TopologicalSpace G] [R1Space G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For a Bochner-integrable coefficient function `f : G → A` against an inner-regular Borel
measure, each Hilbert-space orbit integrand `g ↦ P.coefficient (f g) (P.group g v)` is Bochner
integrable. Neither separability of `H` or `A` nor σ-finiteness of `μ` is assumed. -/
theorem integrable_integrand_of_integrable {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) (v : H) :
    Integrable (fun g => P.coefficient (f g) (P.group g v)) μ := by
  let L : H →L[ℂ] A →L[ℂ] H :=
    ({ toLinearMap := (P.coefficient : A →ₗ[ℂ] H →L[ℂ] H)
       cont := map_continuous P.coefficient } : A →L[ℂ] H →L[ℂ] H).flip
  have hmeas : AEStronglyMeasurable (fun g => L (P.group g v) (f g)) μ :=
    hf.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
      (L.continuous.comp (P.continuous_orbit v))
  refine (hf.norm.mul_const ‖v‖).mono' hmeas (.of_forall fun g => ?_)
  calc
    ‖P.coefficient (f g) (P.group g v)‖ ≤ ‖P.coefficient (f g)‖ * ‖P.group g v‖ :=
      (P.coefficient (f g)).le_opNorm _
    _ ≤ ‖f g‖ * ‖v‖ := by
      rw [P.isUnitary.norm_map]
      exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

omit [R1Space G] [BorelSpace G] in
private theorem norm_integral_integrand_le {μ : Measure G} {f : G → A} (hf : Integrable f μ)
    (v : H) :
    ‖∫ g, P.coefficient (f g) (P.group g v) ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (.of_forall fun g => ?_)
  calc
    ‖P.coefficient (f g) (P.group g v)‖ ≤ ‖P.coefficient (f g)‖ * ‖P.group g v‖ :=
      (P.coefficient (f g)).le_opNorm _
    _ ≤ ‖f g‖ * ‖v‖ := by
      rw [P.isUnitary.norm_map]
      exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

/-- **Vector-valued `L¹` integrated form** of a covariant representation on `Lp A 1 μ`, sending
`f` to the bounded operator `v ↦ ∫ g, P.coefficient (f g) (P.group g v) ∂μ`. -/
def integratedLp (μ : Measure G) [μ.InnerRegularCompactLTTop] :
    Lp A 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (f : Lp A 1 μ) (v : H) => ∫ g, P.coefficient (f g) (P.group g v) ∂μ)
      (fun f₁ f₂ v => by
        rw [← integral_add (P.integrable_integrand_of_integrable (L1.integrable_coeFn f₁) v)
          (P.integrable_integrand_of_integrable (L1.integrable_coeFn f₂) v)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f₁ f₂] with g hg
        rw [hg, Pi.add_apply, map_add, add_apply])
      (fun c f v => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with g hg
        rw [hg, Pi.smul_apply, map_smul, smul_apply])
      (fun f v w => by
        rw [← integral_add (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)
          (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) w)]
        simp_rw [map_add])
      (fun c f v => by
        rw [← integral_smul]
        simp_rw [map_smul]))
    1 fun f v => by
      simpa only [LinearMap.mk₂_apply, one_mul, L1.norm_eq_integral_norm] using
        P.norm_integral_integrand_le (L1.integrable_coeFn f) v

/-- The defining Hilbert-space vector integral for `P.integratedLp μ`. -/
theorem integratedLp_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) (v : H) :
    P.integratedLp μ f v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ :=
  (rfl)

@[simp]
theorem integratedLp_toL1_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) (v : H) :
    P.integratedLp μ (hf.toL1 f) v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ := by
  rw [integratedLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with g hg
  rw [hg]

/-- The `L¹` integrated form is a contraction on each element: `‖(π ⋊ U)(f)‖ ≤ ‖f‖₁`. -/
theorem norm_integratedLp_apply_le {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) : ‖P.integratedLp μ f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun v => ?_
  rw [integratedLp_apply, L1.norm_eq_integral_norm]
  exact P.norm_integral_integrand_le (L1.integrable_coeFn f) v

/-- The operator norm of `P.integratedLp μ` is at most `1`, including zero algebras and zero
Hilbert spaces. -/
theorem norm_integratedLp_le (μ : Measure G) [μ.InnerRegularCompactLTTop] :
    ‖P.integratedLp μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa only [one_mul] using P.norm_integratedLp_apply_le f

/-- **Integrated operator of an integrable coefficient function**: for every Bochner-integrable
`f : G → A`, the vector integrals `ξ ↦ ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ` assemble to a
bounded operator on `H` of norm at most `∫ g, ‖f g‖ ∂μ`. -/
theorem exists_integratedOperator (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (f : G → A) (hf : Integrable f μ) :
    ∃ T : H →L[ℂ] H,
      (∀ ξ, T ξ = ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ) ∧ ‖T‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  refine ⟨P.integratedLp μ (hf.toL1 f), P.integratedLp_toL1_apply hf, ?_⟩
  refine (P.norm_integratedLp_apply_le (hf.toL1 f)).trans_eq ?_
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hf.coeFn_toL1.fun_comp norm)

/-- Matrix coefficients of `P.integratedLp μ f` are integrals of orbit matrix coefficients. -/
theorem inner_integratedLp_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) (w v : H) :
    ⟪w, P.integratedLp μ f v⟫_ℂ =
      ∫ g, ⟪w, P.coefficient (f g) (P.group g v)⟫_ℂ ∂μ := by
  rw [integratedLp_apply,
    integral_inner (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)]

/-- A coefficient operator on the right moves inside the `L¹` vector integral with the action
twist. -/
theorem integratedLp_coefficient_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) (a : A) (v : H) :
    P.integratedLp μ f (P.coefficient a v) =
      ∫ g, P.coefficient (f g * α g a) (P.group g v) ∂μ := by
  rw [integratedLp_apply]
  simp_rw [P.covariance, map_mul, mul_apply_eq_comp]

/-- `P.integratedLp μ` intertwines pointwise left coefficient multiplication on `Lp A 1 μ` with
`P.coefficient`. -/
@[simp]
theorem integratedLp_compLp_mul {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (a : A) (f : Lp A 1 μ) :
    P.integratedLp μ ((ContinuousLinearMap.mul ℂ A a).compLp f) =
      P.coefficient a * P.integratedLp μ f := by
  ext v
  rw [mul_apply_eq_comp, integratedLp_apply, integratedLp_apply,
    ← (P.coefficient a).integral_comp_comm
      (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp f] with g hg
  rw [hg, ContinuousLinearMap.mul_apply', map_mul, mul_apply_eq_comp]

/-- `P.integratedLp μ` intertwines twisted left translation `CStarAction.translateLp` on `Lp A 1 μ`
with the group representation `P.group`. -/
@[simp]
theorem integratedLp_translateLp [MeasurableMul G] {μ : Measure G}
    [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] (r : G) (f : Lp A 1 μ) :
    P.integratedLp μ (α.translateLp μ 1 r f) = P.group r * P.integratedLp μ f := by
  ext v
  calc
    P.integratedLp μ (α.translateLp μ 1 r f) v =
        ∫ s, P.coefficient (α r (f (r⁻¹ * s))) (P.group s v) ∂μ := by
      rw [integratedLp_apply]
      refine integral_congr_ae ?_
      filter_upwards [α.coeFn_translateLp r f] with s hs
      rw [hs]
    _ = ∫ s, P.group r (P.coefficient (f s) (P.group s v)) ∂μ := by
      rw [← integral_mul_left_eq_self _ r]
      refine integral_congr_ae (.of_forall fun s => ?_)
      simp only [inv_mul_cancel_left, map_mul, mul_apply_eq_comp, ← P.covariance]
    _ = (P.group r * P.integratedLp μ f) v := by
      rw [mul_apply_eq_comp, integratedLp_apply,
        (P.group r).integral_comp_comm
          (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)]

/-- On compactly supported continuous coefficient functions, `P.integratedLp μ` agrees with
`P.integratedOperator μ`. -/
@[simp]
theorem integratedLp_toLp {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] (f : C_c(G, A)) :
    P.integratedLp μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      P.integratedOperator μ f := by
  ext v
  rw [integratedLp_apply, integratedOperator_apply]
  refine integral_congr_ae ?_
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ f] with g hg
  rw [hg]

@[simp]
theorem integratedLp_convolutionAlgebra_toL1 {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] (f : ConvolutionAlgebra α μ) :
    P.integratedLp μ (ConvolutionAlgebra.toL1 f) = P.integratedOperator μ f.ofConv := by
  rw [ConvolutionAlgebra.toL1_eq_toLp, P.integratedLp_toLp]

/-- For the trivial covariant representation attached to `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`, the `L¹`
integrated form evaluates `π` at the Bochner integral `∫ g, f g ∂μ`. -/
@[simp]
theorem trivial_integratedLp {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (f : Lp A 1 μ) :
    (trivial (G := G) π).integratedLp μ f = π (∫ g, f g ∂μ) := by
  ext v
  let L : A →L[ℂ] H :=
    (ContinuousLinearMap.apply ℂ H v).comp
      { toLinearMap := (π : A →ₗ[ℂ] H →L[ℂ] H), cont := map_continuous π }
  have hL (a : A) : L a = π a v := rfl
  simpa only [integratedLp_apply, trivial_coefficient, trivial_group,
    ContRepresentation.trivial_apply, one_apply_eq_self, hL] using
    L.integral_comp_comm (L1.integrable_coeFn f)

end IntegratedLp

section CompletionComparison

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- **Agreement of the concrete and abstract `L¹` integrated forms**: `P.integratedLp μ` composed
with `ConvolutionAlgebra.completionEquivL1` equals `P.integratedOperatorL1 μ`. -/
@[simp]
theorem integratedLp_completionEquivL1 (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedLp μ (ConvolutionAlgebra.completionEquivL1 α μ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.integratedLp μ).continuous.comp (ConvolutionAlgebra.completionEquivL1 α μ).continuous)
      (P.continuous_integratedOperatorL1 μ)
  | ih f =>
    rw [ConvolutionAlgebra.completionEquivL1_coe, P.integratedLp_convolutionAlgebra_toL1,
      P.integratedOperatorL1_coe]

@[simp]
theorem integratedOperatorL1_completionEquivL1_symm (f : Lp A 1 μ) :
    P.integratedOperatorL1 μ ((ConvolutionAlgebra.completionEquivL1 α μ).symm f) =
      P.integratedLp μ f := by
  rw [← P.integratedLp_completionEquivL1, LinearIsometryEquiv.apply_symm_apply]

/-- Evaluation of `P.integratedOperatorL1 μ` on the class in the completion corresponding to
`f : Lp A 1 μ` is given by the Hilbert-space vector integral. -/
theorem integratedOperatorL1_completionEquivL1_symm_apply (f : Lp A 1 μ) (v : H) :
    P.integratedOperatorL1 μ ((ConvolutionAlgebra.completionEquivL1 α μ).symm f) v =
      ∫ g, P.coefficient (f g) (P.group g v) ∂μ := by
  rw [P.integratedOperatorL1_completionEquivL1_symm, P.integratedLp_apply]

/-- `P.integratedLp μ` is multiplicative with respect to twisted `L¹` convolution
`CStarAction.convolutionL1`. -/
@[simp]
theorem integratedLp_convolutionL1 (f g : Lp A 1 μ) :
    P.integratedLp μ (α.convolutionL1 μ f g) =
      P.integratedLp μ f * P.integratedLp μ g := by
  rw [← P.integratedOperatorL1_completionEquivL1_symm,
    ConvolutionAlgebra.completionEquivL1_symm_convolutionL1, map_mul,
    P.integratedOperatorL1_completionEquivL1_symm,
    P.integratedOperatorL1_completionEquivL1_symm]

end CompletionComparison

section HaarStar

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For a Haar measure, `P.integratedOperatorL1 μ` preserves the `⋆`-involution on the twisted `L¹`
completion. -/
@[simp]
theorem integratedOperatorL1_star (μ : Measure G) [μ.IsHaarMeasure]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.continuous_integratedOperatorL1 μ).comp continuous_star)
      (continuous_star.comp (P.continuous_integratedOperatorL1 μ))
  | ih f =>
    rw [← Completion.coe_star, P.integratedOperatorL1_coe, P.integratedOperatorL1_coe,
      ConvolutionAlgebra.ofConv_star, P.integratedOperator_twistedInvolution]

/-- The integrated form on `Completion (ConvolutionAlgebra α μ)` bundled as a nonunital complex
`⋆`-algebra homomorphism for a Haar measure. -/
def integratedStarAlgHomL1 (μ : Measure G) [μ.IsHaarMeasure] :
    Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  __ := P.integratedOperatorL1 μ
  map_star' := P.integratedOperatorL1_star μ

@[simp]
theorem integratedStarAlgHomL1_apply {μ : Measure G} [μ.IsHaarMeasure]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  (rfl)

/-- For an inner-regular Haar measure, `P.integratedLp μ` sends `CStarAction.twistedInvolutionL1` to
the operator adjoint. -/
@[simp]
theorem integratedLp_twistedInvolutionL1 {μ : Measure G} [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] (f : Lp A 1 μ) :
    P.integratedLp μ (α.twistedInvolutionL1 μ f) = star (P.integratedLp μ f) := by
  rw [← P.integratedOperatorL1_completionEquivL1_symm,
    ConvolutionAlgebra.completionEquivL1_symm_twistedInvolutionL1, P.integratedOperatorL1_star,
    P.integratedOperatorL1_completionEquivL1_symm]

end HaarStar

section ScalarComparison

variable {G A H : Type*} [Group G] [TopologicalSpace G] [R1Space G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {α : CStarAction G A} (P : CovariantRepresentation α H)
  {μ : Measure G} [μ.InnerRegularCompactLTTop]

/-- Equip `Additive G` with the measurable structure of `G` so `μ` and its `L¹` space transfer
definitionally for the scalar comparison. -/
@[reducible] local instance : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
local instance : R1Space (Additive G) := ‹R1Space G›
local instance : BorelSpace (Additive G) := ‹BorelSpace G›
local instance : Measure.InnerRegularCompactLTTop (α := Additive G) μ :=
  inferInstanceAs (Measure.InnerRegularCompactLTTop (α := G) μ)

/-- On an elementary `L¹` tensor `φ ⊗ a` (`φ : Lp ℂ 1 μ`, `a : A`), `P.integratedLp μ` factors as
`P.coefficient a` times the scalar `ContRepresentation.integratedOperatorL1` of `P.group`. -/
theorem integratedLp_smulRight (φ : Lp ℂ 1 μ) (a : A) :
    P.integratedLp μ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).compLp φ) =
      P.coefficient a *
        (P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
          (G := Additive G) (fun v => P.continuous_orbit v)
          (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
          (μ : Measure (Additive G))
          (Integrable.toL1 (α := Additive G) (φ : Additive G → ℂ) (L1.integrable_coeFn φ)) := by
  ext v
  have hs := ContRepresentation.integratedOperatorL1_toL1
    (G := Additive G)
    (π := P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom)
    (hcont := fun v => P.continuous_orbit v)
    (hbdd := (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le)
    (μ := (μ : Measure (Additive G)))
    (f := (φ : Additive G → ℂ)) (L1.integrable_coeFn φ) v
  have hi : Integrable (fun g => φ g • P.group g v) μ := by
    refine ((L1.integrable_coeFn φ).norm.mul_const ‖v‖).mono'
      ((L1.integrable_coeFn φ).aefinStronglyMeasurable.aestronglyMeasurable_smul
        (P.continuous_orbit v))
      (.of_forall fun g => ?_)
    rw [norm_smul, P.isUnitary.norm_map]
  calc
    P.integratedLp μ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).compLp φ) v =
        P.coefficient a (∫ g, φ g • P.group g v ∂μ) := by
      rw [integratedLp_apply, ← (P.coefficient a).integral_comp_comm hi]
      refine integral_congr_ae ?_
      filter_upwards [(ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).coeFn_compLp φ] with g hg
      rw [hg, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, map_smul, smul_apply,
        ← map_smul]
    _ = _ := by
      rw [mul_apply_eq_comp]
      exact congrArg (P.coefficient a) hs.symm

end ScalarComparison

end TauCeti.CStarAction.CovariantRepresentation
