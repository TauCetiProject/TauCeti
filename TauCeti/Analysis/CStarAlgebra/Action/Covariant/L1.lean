/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.L1
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
public import TauCeti.MeasureTheory.Measure.Regular
public import TauCeti.Topology.Separation.TypeTags
import Mathlib.Analysis.CStarAlgebra.Spectrum
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Vector-valued integrated forms of covariant pairs on Bochner `L¹`

Let `P : CovariantRepresentation α H` be a covariant representation of a point-norm continuous
action `α : CStarAction G A` on a Hilbert space `H`. In
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed` and
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star`, the compact-support integrated form
`P.integratedOperator μ` (from `TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated`) is
extended by continuity to `P.integratedOperatorL1 μ` and `P.integratedStarAlgHomL1 μ` on the
abstract `L¹` completion `UniformSpace.Completion (ConvolutionAlgebra α μ)`.

Here we construct the integrated form directly on the Bochner space `Lp A 1 μ` by Hilbert-space
vector integration,
`(P.integratedOperatorBochnerL1 μ f) v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ`,
for any inner-regular Borel measure (`[R1Space G] [BorelSpace G] [μ.InnerRegularCompactLTTop]`),
and prove that it matches `P.integratedOperatorL1 μ` across
`CompactlySupportedL1.completionEquivL1`. The vector-integral operator construction, covariance
identities, and elementary-tensor comparison
closely adapt the scalar integrated representation `ContRepresentation.integratedOperatorL1` in
`TauCeti.RepresentationTheory.Continuous.Integrated.Basic` and the compact-support covariant form
`CovariantRepresentation.integratedOperator` /
`CovariantRepresentation.integratedOperator_eq_coefficient_mul_integratedOperatorL1` in
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated`.

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
* `CovariantRepresentation.integratedOperatorBochnerL1`: the contractive continuous linear map
  `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` given by the vector integral.
* `CovariantRepresentation.exists_integratedOperator`: every Bochner-integrable `f : G → A` has a
  bounded integrated operator `T` with `T ξ = ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ` and
  `‖T‖ ≤ ∫ g, ‖f g‖ ∂μ`.
* `CovariantRepresentation.integratedOperatorBochnerL1_compLp_mul`,
  `CovariantRepresentation.integratedOperatorBochnerL1_translateLp`,
  `CovariantRepresentation.integratedOperatorBochnerL1_convolutionL1`: left coefficient covariance,
  group covariance, and multiplicativity under `CStarAction.convolutionL1` directly on `Lp A 1 μ`
  without local compactness.
* `CovariantRepresentation.integratedOperatorBochnerL1_completionEquivL1`,
  `CovariantRepresentation.integratedOperatorL1_completionEquivL1_symm`,
  `CovariantRepresentation.integratedOperatorBochnerL1_twistedInvolutionL1`: agreement of
  `P.integratedOperatorBochnerL1 μ` with `P.integratedOperatorL1 μ` across `completionEquivL1` and
  compatibility with `CStarAction.twistedInvolutionL1`.
* `CovariantRepresentation.integratedOperatorBochnerL1_compLp_smulRight`,
  `CovariantRepresentation.integratedOperatorBochnerL1_trivial`: comparison with the scalar
  `ContRepresentation.integratedOperatorL1` on elementary tensors `φ ⊗ a` and specialization to the
  trivial covariant representation.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2 (§2.3, Proposition 2.23).
* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

section IntegratedOperatorBochnerL1

variable {G A H : Type*} [Group G] [TopologicalSpace G] [R1Space G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {α : CStarAction G A} (P : CovariantRepresentation α H)

omit [R1Space G] [MeasurableSpace G] [BorelSpace G] in
private theorem norm_coefficient_group_le (a : A) (g : G) (v : H) :
    ‖P.coefficient a (P.group g v)‖ ≤ ‖a‖ * ‖v‖ := by
  refine ((P.coefficient a).le_opNorm _).trans ?_
  rw [P.isUnitary.norm_map]
  exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

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
  exact (hf.norm.mul_const ‖v‖).mono' hmeas
    (.of_forall fun g => norm_coefficient_group_le P _ g v)

omit [R1Space G] [BorelSpace G] in
private theorem norm_integral_integrand_le {μ : Measure G} {f : G → A} (hf : Integrable f μ)
    (v : H) :
    ‖∫ g, P.coefficient (f g) (P.group g v) ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (hf.norm.mul_const _)
    (.of_forall fun g => norm_coefficient_group_le P _ g v)

/-- **Vector-valued `L¹` integrated form** of a covariant representation on `Lp A 1 μ`, sending
`f` to the bounded operator `v ↦ ∫ g, P.coefficient (f g) (P.group g v) ∂μ`. -/
def integratedOperatorBochnerL1 (μ : Measure G) [μ.InnerRegularCompactLTTop] :
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

/-- The defining Hilbert-space vector integral for `P.integratedOperatorBochnerL1 μ`. -/
theorem integratedOperatorBochnerL1_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) (v : H) :
    P.integratedOperatorBochnerL1 μ f v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ :=
  (rfl)

@[simp]
theorem integratedOperatorBochnerL1_toL1_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) (v : H) :
    P.integratedOperatorBochnerL1 μ (hf.toL1 f) v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ := by
  rw [integratedOperatorBochnerL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with g hg
  rw [hg]

/-- The `L¹` integrated form is a contraction on each element: `‖(π ⋊ U)(f)‖ ≤ ‖f‖₁`. -/
theorem norm_integratedOperatorBochnerL1_apply_le {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) : ‖P.integratedOperatorBochnerL1 μ f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun v => ?_
  rw [integratedOperatorBochnerL1_apply, L1.norm_eq_integral_norm]
  exact P.norm_integral_integrand_le (L1.integrable_coeFn f) v

/-- The operator norm of `P.integratedOperatorBochnerL1 μ` is at most `1`, including zero algebras
and zero Hilbert spaces. -/
theorem norm_integratedOperatorBochnerL1_le (μ : Measure G) [μ.InnerRegularCompactLTTop] :
    ‖P.integratedOperatorBochnerL1 μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa only [one_mul] using P.norm_integratedOperatorBochnerL1_apply_le f

/-- **Integrated operator of an integrable coefficient function**: for every Bochner-integrable
`f : G → A`, the vector integrals `ξ ↦ ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ` assemble to a
bounded operator on `H` of norm at most `∫ g, ‖f g‖ ∂μ`. -/
theorem exists_integratedOperator (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (f : G → A) (hf : Integrable f μ) :
    ∃ T : H →L[ℂ] H,
      (∀ ξ, T ξ = ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ) ∧ ‖T‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  refine ⟨P.integratedOperatorBochnerL1 μ (hf.toL1 f),
    P.integratedOperatorBochnerL1_toL1_apply hf, ?_⟩
  refine (P.norm_integratedOperatorBochnerL1_apply_le (hf.toL1 f)).trans_eq ?_
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hf.coeFn_toL1.fun_comp norm)

/-- Matrix coefficients of `P.integratedOperatorBochnerL1 μ f` are integrals of orbit matrix
coefficients. -/
theorem inner_integratedOperatorBochnerL1_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) (w v : H) :
    ⟪w, P.integratedOperatorBochnerL1 μ f v⟫_ℂ =
      ∫ g, ⟪w, P.coefficient (f g) (P.group g v)⟫_ℂ ∂μ := by
  rw [integratedOperatorBochnerL1_apply,
    integral_inner (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)]

/-- A coefficient operator on the right moves inside the `L¹` vector integral with the action
twist. -/
theorem integratedOperatorBochnerL1_coefficient_apply {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (f : Lp A 1 μ) (a : A) (v : H) :
    P.integratedOperatorBochnerL1 μ f (P.coefficient a v) =
      ∫ g, P.coefficient (f g * α g a) (P.group g v) ∂μ := by
  rw [integratedOperatorBochnerL1_apply]
  simp_rw [P.covariance, map_mul, mul_apply_eq_comp]

/-- `P.integratedOperatorBochnerL1 μ` intertwines pointwise left coefficient multiplication on
`Lp A 1 μ` with `P.coefficient`. -/
@[simp]
theorem integratedOperatorBochnerL1_compLp_mul {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (a : A) (f : Lp A 1 μ) :
    P.integratedOperatorBochnerL1 μ ((ContinuousLinearMap.mul ℂ A a).compLp f) =
      P.coefficient a * P.integratedOperatorBochnerL1 μ f := by
  ext v
  rw [mul_apply_eq_comp, integratedOperatorBochnerL1_apply, integratedOperatorBochnerL1_apply,
    ← (P.coefficient a).integral_comp_comm
      (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp f] with g hg
  rw [hg, ContinuousLinearMap.mul_apply', map_mul, mul_apply_eq_comp]

/-- `P.integratedOperatorBochnerL1 μ` intertwines twisted left translation `CStarAction.translateLp`
on `Lp A 1 μ` with the group representation `P.group`. -/
@[simp]
theorem integratedOperatorBochnerL1_translateLp [MeasurableMul G] {μ : Measure G}
    [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant] (r : G) (f : Lp A 1 μ) :
    P.integratedOperatorBochnerL1 μ (α.translateLp μ 1 r f) =
      P.group r * P.integratedOperatorBochnerL1 μ f := by
  ext v
  calc
    P.integratedOperatorBochnerL1 μ (α.translateLp μ 1 r f) v =
        ∫ s, P.coefficient (α r (f (r⁻¹ * s))) (P.group s v) ∂μ := by
      rw [integratedOperatorBochnerL1_apply]
      refine integral_congr_ae ?_
      filter_upwards [α.coeFn_translateLp r f] with s hs
      rw [hs]
    _ = ∫ s, P.group r (P.coefficient (f s) (P.group s v)) ∂μ := by
      rw [← integral_mul_left_eq_self _ r]
      refine integral_congr_ae (.of_forall fun s => ?_)
      simp only [inv_mul_cancel_left, map_mul, mul_apply_eq_comp, ← P.covariance]
    _ = (P.group r * P.integratedOperatorBochnerL1 μ f) v := by
      rw [mul_apply_eq_comp, integratedOperatorBochnerL1_apply,
        (P.group r).integral_comp_comm
          (P.integrable_integrand_of_integrable (L1.integrable_coeFn f) v)]

/-- On compactly supported continuous coefficient functions, `P.integratedOperatorBochnerL1 μ`
agrees with `P.integratedOperator μ`. -/
@[simp]
theorem integratedOperatorBochnerL1_toLp {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] (f : C_c(G, A)) :
    P.integratedOperatorBochnerL1 μ (CompactlySupportedContinuousMap.toLp 1 μ ℂ f) =
      P.integratedOperator μ f := by
  ext v
  rw [integratedOperatorBochnerL1_apply, integratedOperator_apply]
  refine integral_congr_ae ?_
  filter_upwards [CompactlySupportedContinuousMap.coeFn_toLp (p := 1) (μ := μ) ℂ f] with g hg
  rw [hg]

@[simp]
theorem integratedOperatorBochnerL1_convolutionAlgebra_toL1 {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] (f : ConvolutionAlgebra α μ) :
    P.integratedOperatorBochnerL1 μ (CompactlySupportedL1.toL1 ℂ f) =
      P.integratedOperator μ f.ofConv := by
  rw [CompactlySupportedL1.toL1_eq_toLp, P.integratedOperatorBochnerL1_toLp]

/-- For the trivial covariant representation attached to `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`, the `L¹`
integrated form evaluates `π` at the Bochner integral `∫ g, f g ∂μ`. -/
@[simp]
theorem integratedOperatorBochnerL1_trivial {μ : Measure G} [μ.InnerRegularCompactLTTop]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (f : Lp A 1 μ) :
    (trivial (G := G) π).integratedOperatorBochnerL1 μ f = π (∫ g, f g ∂μ) := by
  -- `π` is a continuous linear map, so it commutes with the Bochner integral.
  let πL : A →L[ℂ] (H →L[ℂ] H) :=
    { toFun := π
      map_add' := map_add π
      map_smul' := map_smul π
      cont := AddMonoidHomClass.continuous_of_bound π 1 fun a ↦ by
        rw [one_mul]
        exact NonUnitalStarAlgHom.norm_apply_le π a }
  have hint := L1.integrable_coeFn f
  have hπ : Integrable (fun g ↦ πL (f g)) μ := πL.integrable_comp hint
  ext v
  simp only [integratedOperatorBochnerL1_apply, trivial_coefficient, trivial_group,
    ContRepresentation.trivial_apply]
  change ∫ g, (πL (f g)) v ∂μ = (πL (∫ g, f g ∂μ)) v
  rw [← ContinuousLinearMap.integral_apply hπ v]
  exact congrArg (· v) (πL.integral_comp_comm hint)

end IntegratedOperatorBochnerL1

section Convolution

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  {μ : Measure G} [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- `P.integratedOperatorBochnerL1 μ` is multiplicative with respect to twisted `L¹` convolution
`CStarAction.convolutionL1`. -/
@[simp]
theorem integratedOperatorBochnerL1_convolutionL1 (f g : Lp A 1 μ) :
    P.integratedOperatorBochnerL1 μ (α.convolutionL1 μ f g) =
      P.integratedOperatorBochnerL1 μ f * P.integratedOperatorBochnerL1 μ g := by
  ext v
  let L : Lp A 1 μ →L[ℂ] H :=
    (ContinuousLinearMap.apply ℂ H v).comp (P.integratedOperatorBochnerL1 μ)
  calc
    P.integratedOperatorBochnerL1 μ (α.convolutionL1 μ f g) v =
        ∫ r, L ((ContinuousLinearMap.mul ℂ A (f r)).compLp (α.translateLp μ 1 r g)) ∂μ := by
      simpa only [L, α.convolutionL1_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply] using
        (L.integral_comp_comm (α.integrable_mul_translateLp (L1.integrable_coeFn f) g)).symm
    _ = (P.integratedOperatorBochnerL1 μ f * P.integratedOperatorBochnerL1 μ g) v := by
      rw [mul_apply_eq_comp, integratedOperatorBochnerL1_apply]
      refine integral_congr_ae (.of_forall fun r => ?_)
      simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        P.integratedOperatorBochnerL1_compLp_mul, P.integratedOperatorBochnerL1_translateLp,
        mul_apply_eq_comp]

end Convolution

section CompletionComparison

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]

/-- **Agreement of the concrete and abstract `L¹` integrated forms**:
`P.integratedOperatorBochnerL1 μ` composed with `CompactlySupportedL1.completionEquivL1` equals
`P.integratedOperatorL1 μ`. -/
@[simp]
theorem integratedOperatorBochnerL1_completionEquivL1 (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorBochnerL1 μ (CompactlySupportedL1.completionEquivL1 α A μ ℂ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.integratedOperatorBochnerL1 μ).continuous.comp
        (CompactlySupportedL1.completionEquivL1 α A μ ℂ).continuous)
      (P.continuous_integratedOperatorL1 μ)
  | ih f =>
    rw [CompactlySupportedL1.completionEquivL1_coe,
      P.integratedOperatorBochnerL1_convolutionAlgebra_toL1, P.integratedOperatorL1_coe]

@[simp]
theorem integratedOperatorL1_completionEquivL1_symm (f : Lp A 1 μ) :
    P.integratedOperatorL1 μ ((CompactlySupportedL1.completionEquivL1 α A μ ℂ).symm f) =
      P.integratedOperatorBochnerL1 μ f := by
  rw [← P.integratedOperatorBochnerL1_completionEquivL1, LinearIsometryEquiv.apply_symm_apply]

/-- Evaluation of `P.integratedOperatorL1 μ` on the class in the completion corresponding to
`f : Lp A 1 μ` is given by the Hilbert-space vector integral. -/
theorem integratedOperatorL1_completionEquivL1_symm_apply (f : Lp A 1 μ) (v : H) :
    P.integratedOperatorL1 μ ((CompactlySupportedL1.completionEquivL1 α A μ ℂ).symm f) v =
      ∫ g, P.coefficient (f g) (P.group g v) ∂μ := by
  rw [P.integratedOperatorL1_completionEquivL1_symm, P.integratedOperatorBochnerL1_apply]

/-- For a left-invariant measure finite on compact sets and inner regular on sets of finite measure,
`P.integratedOperatorBochnerL1 μ` sends `CStarAction.twistedInvolutionL1` to the operator adjoint.
-/
@[simp]
theorem integratedOperatorBochnerL1_twistedInvolutionL1 (f : Lp A 1 μ) :
    P.integratedOperatorBochnerL1 μ (α.twistedInvolutionL1 μ f) =
      star (P.integratedOperatorBochnerL1 μ f) := by
  rw [← P.integratedOperatorL1_completionEquivL1_symm,
    ConvolutionAlgebra.completionEquivL1_symm_twistedInvolutionL1, P.integratedOperatorL1_star,
    P.integratedOperatorL1_completionEquivL1_symm]

end CompletionComparison

section ScalarComparison

variable {G A H : Type*} [Group G] [TopologicalSpace G] [R1Space G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {α : CStarAction G A} (P : CovariantRepresentation α H)
  {μ : Measure G} [μ.InnerRegularCompactLTTop]

/-- On an elementary `L¹` tensor `φ ⊗ a` (`φ : Lp ℂ 1 μ`, `a : A`),
`P.integratedOperatorBochnerL1 μ` factors as `P.coefficient a` times the scalar
`ContRepresentation.integratedOperatorL1` of `P.group`. -/
theorem integratedOperatorBochnerL1_compLp_smulRight (φ : Lp ℂ 1 μ) (a : A) :
    P.integratedOperatorBochnerL1 μ
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).compLp φ) =
      P.coefficient a *
        (P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
          (G := Additive G) (fun v => (P.continuous_orbit v).comp continuous_toMul)
          (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
          (μ.map Additive.ofMul)
          (Lp.compMeasurePreserving Additive.toMul
            (MeasurePreserving.symm MeasurableEquiv.additive (measurable_ofMul.measurePreserving μ))
            φ) := by
  ext v
  let hmp : MeasurePreserving Additive.toMul (μ.map Additive.ofMul) μ :=
    MeasurePreserving.symm MeasurableEquiv.additive (measurable_ofMul.measurePreserving μ)
  have hs := ContRepresentation.integratedOperatorL1_apply
    (G := Additive G)
    (π := P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom)
    (hcont := fun v => (P.continuous_orbit v).comp continuous_toMul)
    (hbdd := (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le)
    (μ := μ.map Additive.ofMul)
    (Lp.compMeasurePreserving Additive.toMul hmp φ) v
  have hmap :
      ∫ x, (Lp.compMeasurePreserving Additive.toMul hmp φ) x • P.group (Additive.toMul x) v
          ∂(μ.map Additive.ofMul) =
        ∫ g, φ g • P.group g v ∂μ := by
    refine (integral_congr_ae ?_).trans
      (integral_map_equiv (MeasurableEquiv.additive (α := G))
        fun x : Additive G => φ (Additive.toMul x) • P.group (Additive.toMul x) v)
    filter_upwards [Lp.coeFn_compMeasurePreserving φ hmp] with x hx
    rw [hx, Function.comp_apply]
  have hi : Integrable (fun g => φ g • P.group g v) μ := by
    refine ((L1.integrable_coeFn φ).norm.mul_const ‖v‖).mono'
      ((L1.integrable_coeFn φ).aefinStronglyMeasurable.aestronglyMeasurable_smul
        (P.continuous_orbit v))
      (.of_forall fun g => ?_)
    rw [norm_smul, P.isUnitary.norm_map]
  calc
    P.integratedOperatorBochnerL1 μ
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).compLp φ) v =
        P.coefficient a (∫ g, φ g • P.group g v ∂μ) := by
      rw [integratedOperatorBochnerL1_apply, ← (P.coefficient a).integral_comp_comm hi]
      refine integral_congr_ae ?_
      filter_upwards [(ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).coeFn_compLp φ] with g hg
      rw [hg, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, map_smul, smul_apply,
        ← map_smul]
    _ = _ := by
      rw [mul_apply_eq_comp, ← hmap]
      exact congrArg (P.coefficient a) hs.symm

end ScalarComparison

end TauCeti.CStarAction.CovariantRepresentation
