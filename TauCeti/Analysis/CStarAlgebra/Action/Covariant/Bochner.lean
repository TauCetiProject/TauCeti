/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Bochner `L¹` integrated representations of covariant pairs

Let `P = (π, U)` be a covariant representation of a C⋆-dynamical system `(G, A, α)` on a Hilbert
space `H`, and let `μ` be a Borel measure on an `R₁` group `G` that is inner regular on sets of
finite measure with respect to compact sets (`[μ.InnerRegularCompactLTTop]`), such as any regular
or inner regular Haar measure. For every integrable coefficient function `f : G → A` and every
vector `v : H`, the Hilbert-space integrand `s ↦ π(f s)(U_s v)` is Bochner integrable, even when
`G` is not σ-compact, `A` and `H` are nonseparable, and `U` is only strongly continuous: `f`
vanishes outside a σ-finite measurable set, on which the continuous orbit `s ↦ U_s v` is almost
everywhere strongly measurable by inner regularity.

Integrating in the Hilbert space defines a contractive linear map
`TauCeti.CStarAction.CovariantRepresentation.integratedBochnerL1` from Bochner `L¹(G, A, μ)`
(`Lp A 1 μ`) into `H →L[ℂ] H`, proving `exists_integratedOperator` for arbitrary integrable
coefficient functions. Under the linear isometric equivalence `ConvolutionAlgebra.toL1Equiv`
identifying the twisted `L¹` completion `UniformSpace.Completion (ConvolutionAlgebra α μ)` with
`Lp A 1 μ`, `integratedBochnerL1` agrees with `CovariantRepresentation.integratedOperatorL1`. For a
Haar measure, `integratedOperatorL1` preserves the involution as well as multiplication, bundling
into `integratedStarAlgHomL1`, and `integratedBochnerL1` therefore turns Bochner twisted
convolution and involution into operator composition and adjoint whenever `μ.inv ≪ μ` (in
particular for both inner regular and regular Haar measures). On a discrete group with counting
measure, the vector integral reduces to the unconditional series `∑' s, π(f s)(U_s v)` for every
norm-summable `f : G → A`, without any countability assumption on `G`.

## Main definitions

* `TauCeti.CStarAction.CovariantRepresentation.integratedBochnerL1`: the contractive integrated map
  `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` defined by Hilbert-space Bochner integration.
* `TauCeti.CStarAction.CovariantRepresentation.integratedStarAlgHomL1`: the integrated nonunital
  ⋆-algebra homomorphism `UniformSpace.Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H)` for
  a Haar measure.

## Main statements

* `TauCeti.CStarAction.CovariantRepresentation.exists_integratedOperator`: every integrable
  `f : G → A` defines a bounded operator `ξ ↦ ∫ s, π(f s)(U_s ξ) ∂μ` of norm at most
  `∫ s, ‖f s‖ ∂μ`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedBochnerL1_toL1Equiv`: `integratedBochnerL1`
  agrees with `integratedOperatorL1` along `ConvolutionAlgebra.toL1Equiv`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedOperatorL1_star`: `integratedOperatorL1`
  maps `star` to the operator adjoint for any Haar measure.
* `TauCeti.CStarAction.CovariantRepresentation.integratedBochnerL1_bochnerConvolution` and
  `TauCeti.CStarAction.CovariantRepresentation.integratedBochnerL1_bochnerInvolution`:
  multiplicativity and star-preservation on integrable functions via `bochnerConvolution` and
  `bochnerInvolution`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedBochnerL1_count_toL1_apply`: counting
  measure specialization `(π ⋊ U)(f) v = ∑' s, π(f s)(U_s v)` for norm-summable `f` on a discrete
  group.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs **134**,
  American Mathematical Society (2007), Proposition 2.23.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

section BochnerIntegral

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [R1Space G]
  [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For an a.e. finitely strongly measurable coefficient function `f : G → A` and any `v : H`,
the vector integrand `s ↦ π(f s)(U_s v)` is a.e. strongly measurable with respect to any Borel
measure inner regular on finite-measure sets. -/
theorem aestronglyMeasurable_integrand_of_aefinStronglyMeasurable {μ : Measure G}
    [μ.InnerRegularCompactLTTop] {f : G → A} (hf : AEFinStronglyMeasurable f μ) (v : H) :
    AEStronglyMeasurable (fun s => P.coefficient (f s) (P.group s v)) μ := by
  let L : A →L[ℂ] (H →L[ℂ] H) :=
    { toLinearMap := (P.coefficient : A →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous P.coefficient }
  exact L.aestronglyMeasurable_comp₂_continuous hf (P.continuous_orbit v)

/-- For an integrable coefficient function `f : G → A` and any `v : H`, the vector integrand
`s ↦ π(f s)(U_s v)` is Bochner integrable. -/
theorem integrable_integrand_of_integrable {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) (v : H) :
    Integrable (fun s => P.coefficient (f s) (P.group s v)) μ := by
  refine (hf.norm.mul_const ‖v‖).mono'
    (P.aestronglyMeasurable_integrand_of_aefinStronglyMeasurable hf.aefinStronglyMeasurable v)
    (.of_forall fun s => ?_)
  calc ‖P.coefficient (f s) (P.group s v)‖
      ≤ ‖P.coefficient (f s)‖ * ‖P.group s v‖ := (P.coefficient (f s)).le_opNorm _
    _ ≤ ‖f s‖ * ‖v‖ := by
      rw [P.isUnitary.norm_map]
      exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

omit [R1Space G] [BorelSpace G] in
private theorem norm_integral_integrand_le {μ : Measure G}
    {f : G → A} (hf : Integrable f μ) (v : H) :
    ‖∫ s, P.coefficient (f s) (P.group s v) ∂μ‖ ≤ (∫ s, ‖f s‖ ∂μ) * ‖v‖ := by
  calc ‖∫ s, P.coefficient (f s) (P.group s v) ∂μ‖
      ≤ ∫ s, ‖f s‖ * ‖v‖ ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const ‖v‖) (.of_forall fun s => ?_)
        calc ‖P.coefficient (f s) (P.group s v)‖
            ≤ ‖P.coefficient (f s)‖ * ‖P.group s v‖ := (P.coefficient (f s)).le_opNorm _
          _ ≤ ‖f s‖ * ‖v‖ := by
            rw [P.isUnitary.norm_map]
            exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _)
              (norm_nonneg _)
    _ = (∫ s, ‖f s‖ ∂μ) * ‖v‖ := integral_mul_const _ _

/-- Auxiliary bounded operator `v ↦ ∫ s, π(u s)(U_s v) ∂μ` for a fixed `u : Lp A 1 μ`. -/
private def integratedBochnerL1Aux (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun v := ∫ s, P.coefficient (u s) (P.group s v) ∂μ
      map_add' v w := by
        simp_rw [map_add]
        exact integral_add (P.integrable_integrand_of_integrable (L1.integrable_coeFn u) v)
          (P.integrable_integrand_of_integrable (L1.integrable_coeFn u) w)
      map_smul' c v := by
        simp_rw [map_smul]
        exact integral_smul c _ }
    ‖u‖ fun v => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, L1.norm_eq_integral_norm] using
        P.norm_integral_integrand_le (L1.integrable_coeFn u) v

@[simp]
private theorem integratedBochnerL1Aux_apply (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) (v : H) :
    P.integratedBochnerL1Aux μ u v = ∫ s, P.coefficient (u s) (P.group s v) ∂μ :=
  (rfl)

private theorem norm_integratedBochnerL1Aux_le (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) :
    ‖P.integratedBochnerL1Aux μ u‖ ≤ 1 * ‖u‖ := by
  rw [one_mul]
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg u) _

/-- **Bochner `L¹` integrated form** of a covariant representation: the contractive continuous
linear map sending `u : Lp A 1 μ` to the bounded operator `v ↦ ∫ s, π(u s)(U_s v) ∂μ`. -/
def integratedBochnerL1 (μ : Measure G) [μ.InnerRegularCompactLTTop] :
    Lp A 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := P.integratedBochnerL1Aux μ
      map_add' u₁ u₂ := by
        ext v
        rw [add_apply, integratedBochnerL1Aux_apply, integratedBochnerL1Aux_apply,
          integratedBochnerL1Aux_apply,
          ← integral_add (P.integrable_integrand_of_integrable (L1.integrable_coeFn u₁) v)
            (P.integrable_integrand_of_integrable (L1.integrable_coeFn u₂) v)]
        exact integral_congr_ae ((Lp.coeFn_add u₁ u₂).mono fun s hs => by
          dsimp only; rw [hs, Pi.add_apply, map_add, add_apply])
      map_smul' c u := by
        ext v
        rw [RingHom.id_apply, smul_apply, integratedBochnerL1Aux_apply,
          integratedBochnerL1Aux_apply, ← integral_smul c]
        exact integral_congr_ae ((Lp.coeFn_smul c u).mono fun s hs => by
          dsimp only; rw [hs, Pi.smul_apply, map_smul, smul_apply]) }
    1 (P.norm_integratedBochnerL1Aux_le μ)

/-- Vector formula for `integratedBochnerL1`. -/
theorem integratedBochnerL1_apply (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) (v : H) :
    P.integratedBochnerL1 μ u v = ∫ s, P.coefficient (u s) (P.group s v) ∂μ :=
  (rfl)

/-- On `hf.toL1 f`, `integratedBochnerL1` evaluates by the vector Bochner integral of `f`. -/
@[simp]
theorem integratedBochnerL1_toL1 {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) (v : H) :
    P.integratedBochnerL1 μ (hf.toL1 f) v = ∫ s, P.coefficient (f s) (P.group s v) ∂μ := by
  rw [integratedBochnerL1_apply]
  exact integral_congr_ae (hf.coeFn_toL1.mono fun s hs => by dsimp only; rw [hs])

/-- The operator norm of `integratedBochnerL1` is at most `1`. -/
theorem norm_integratedBochnerL1_le (μ : Measure G) [μ.InnerRegularCompactLTTop] :
    ‖P.integratedBochnerL1 μ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `integratedBochnerL1` is contractive on `Lp A 1 μ`. -/
theorem norm_integratedBochnerL1_apply_le (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) :
    ‖P.integratedBochnerL1 μ u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using (P.integratedBochnerL1 μ).le_of_opNorm_le
    (P.norm_integratedBochnerL1_le μ) u

/-- On `hf.toL1 f`, the operator norm of `integratedBochnerL1` is bounded by `∫ s, ‖f s‖ ∂μ`. -/
theorem norm_integratedBochnerL1_toL1_le {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) :
    ‖P.integratedBochnerL1 μ (hf.toL1 f)‖ ≤ ∫ s, ‖f s‖ ∂μ :=
  (P.norm_integratedBochnerL1_apply_le μ (hf.toL1 f)).trans_eq (L1.norm_of_fun_eq_integral_norm hf)

/-- **Existence of the vector-integrated operator for integrable coefficients.** Every integrable
function `f : G → A` defines a bounded operator `T : H →L[ℂ] H` acting by
`T ξ = ∫ s, π(f s)(U_s ξ) ∂μ` with operator norm at most `∫ s, ‖f s‖ ∂μ`. -/
theorem exists_integratedOperator {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {f : G → A} (hf : Integrable f μ) :
    ∃ T : H →L[ℂ] H,
      (∀ ξ, T ξ = ∫ s, P.coefficient (f s) (P.group s ξ) ∂μ) ∧
      ‖T‖ ≤ ∫ s, ‖f s‖ ∂μ :=
  ⟨P.integratedBochnerL1 μ (hf.toL1 f), P.integratedBochnerL1_toL1 hf,
    P.norm_integratedBochnerL1_toL1_le hf⟩

/-- Matrix coefficients of `integratedBochnerL1` commute with Bochner integration. -/
theorem inner_integratedBochnerL1_apply (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) (w v : H) :
    ⟪w, P.integratedBochnerL1 μ u v⟫_ℂ =
      ∫ s, ⟪w, P.coefficient (u s) (P.group s v)⟫_ℂ ∂μ := by
  rw [integratedBochnerL1_apply,
    integral_inner (P.integrable_integrand_of_integrable (L1.integrable_coeFn u) v)]

/-- Right multiplication by a coefficient operator moves inside the Bochner integral with the
action twist. -/
theorem integratedBochnerL1_coefficient_apply (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) (a : A) (v : H) :
    P.integratedBochnerL1 μ u (P.coefficient a v) =
      ∫ s, P.coefficient (u s * α s a) (P.group s v) ∂μ := by
  rw [integratedBochnerL1_apply]
  simp_rw [P.covariance, map_mul, mul_apply_eq_comp]

/-- On the `L¹` class of a compactly supported convolution element, `integratedBochnerL1` agrees
with `integratedOperator`. -/
@[simp]
theorem integratedBochnerL1_convolutionAlgebra_toL1 (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] (f : ConvolutionAlgebra α μ) :
    P.integratedBochnerL1 μ (ConvolutionAlgebra.toL1 f) = P.integratedOperator μ f.ofConv := by
  ext v
  rw [integratedBochnerL1_apply, integratedOperator_apply]
  exact integral_congr_ae ((ConvolutionAlgebra.coeFn_toL1 f).mono fun s hs => by
    dsimp only; rw [hs])

end BochnerIntegral

/-! ### Agreement with `integratedOperatorL1` and Banach ⋆-representation properties -/

section CompletionAgreement

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- Along the linear isometry `ConvolutionAlgebra.toL1CompletionLI`, `integratedBochnerL1` agrees
with the completion extension `integratedOperatorL1`. -/
@[simp]
theorem integratedBochnerL1_toL1CompletionLI (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedBochnerL1 μ (ConvolutionAlgebra.toL1CompletionLI α μ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.integratedBochnerL1 μ).continuous.comp
        (ConvolutionAlgebra.toL1CompletionLI α μ).continuous)
      (P.continuous_integratedOperatorL1 μ)
  | ih f => simp

/-- Under `ConvolutionAlgebra.toL1Equiv`, `integratedBochnerL1` agrees with
`integratedOperatorL1`. -/
@[simp]
theorem integratedBochnerL1_toL1Equiv [WeaklyLocallyCompactSpace G] (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedBochnerL1 μ (ConvolutionAlgebra.toL1Equiv α μ x) =
      P.integratedOperatorL1 μ x := by
  rw [ConvolutionAlgebra.toL1Equiv_apply, P.integratedBochnerL1_toL1CompletionLI μ]

/-- Transporting `integratedOperatorL1` across `(ConvolutionAlgebra.toL1Equiv α μ).symm` recovers
`integratedBochnerL1`. -/
@[simp]
theorem integratedOperatorL1_toL1Equiv_symm [WeaklyLocallyCompactSpace G] (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (u : Lp A 1 μ) :
    P.integratedOperatorL1 μ ((ConvolutionAlgebra.toL1Equiv α μ).symm u) =
      P.integratedBochnerL1 μ u := by
  rw [← P.integratedBochnerL1_toL1Equiv μ, LinearIsometryEquiv.apply_symm_apply]

/-- Vector integral formula for `integratedOperatorL1` at any element of the twisted `L¹`
completion, evaluated via its `Lp A 1 μ` representative `ConvolutionAlgebra.toL1Equiv α μ x`. -/
theorem integratedOperatorL1_apply [WeaklyLocallyCompactSpace G] (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (x : Completion (ConvolutionAlgebra α μ)) (v : H) :
    P.integratedOperatorL1 μ x v =
      ∫ s, P.coefficient (ConvolutionAlgebra.toL1Equiv α μ x s) (P.group s v) ∂μ := by
  rw [← P.integratedBochnerL1_toL1Equiv μ, integratedBochnerL1_apply]

end CompletionAgreement

section StarAndBochnerOps

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For any Haar measure, `integratedOperatorL1` preserves the twisted `L¹` involution. -/
@[simp]
theorem integratedOperatorL1_star (μ : Measure G) [μ.IsHaarMeasure]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((P.continuous_integratedOperatorL1 μ).comp continuous_star)
      (continuous_star.comp (P.continuous_integratedOperatorL1 μ))
  | ih f =>
    rw [← Completion.coe_star, integratedOperatorL1_coe, integratedOperatorL1_coe,
      ConvolutionAlgebra.ofConv_star, integratedOperator_twistedInvolution]

/-- The integrated form on the twisted `L¹` Banach ⋆-algebra bundled as a nonunital complex
⋆-algebra homomorphism. -/
def integratedStarAlgHomL1 (μ : Measure G) [μ.IsHaarMeasure] :
    Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toNonUnitalAlgHom := P.integratedOperatorL1 μ
  map_star' := P.integratedOperatorL1_star μ

@[simp]
theorem integratedStarAlgHomL1_apply (μ : Measure G) [μ.IsHaarMeasure]
    (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  (rfl)

/-- `integratedStarAlgHomL1` is contractive for the twisted `L¹` norm. -/
theorem norm_integratedStarAlgHomL1_le (μ : Measure G) [μ.IsHaarMeasure]
    (x : Completion (ConvolutionAlgebra α μ)) :
    ‖P.integratedStarAlgHomL1 μ x‖ ≤ ‖x‖ :=
  P.norm_integratedOperatorL1_le μ x

/-- Multiplicativity of `integratedBochnerL1` for Bochner twisted convolution of integrable
functions when `μ` is left-invariant and `μ.inv ≪ μ`. -/
theorem integratedBochnerL1_bochnerConvolution_of_inv_absolutelyContinuous {μ : Measure G}
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
    (hinv : μ.inv ≪ μ) {f g : G → A} (hf : Integrable f μ) (hg : Integrable g μ) :
    P.integratedBochnerL1 μ
      ((α.integrable_bochnerConvolution_of_inv_absolutelyContinuous hinv hf hg).toL1
        (α.bochnerConvolution μ f g)) =
      P.integratedBochnerL1 μ (hf.toL1 f) * P.integratedBochnerL1 μ (hg.toL1 g) := by
  rw [← α.toL1Equiv_mul_symm_toL1_of_inv_absolutelyContinuous hinv hf hg,
    P.integratedBochnerL1_toL1Equiv μ, map_mul, P.integratedOperatorL1_toL1Equiv_symm μ,
    P.integratedOperatorL1_toL1Equiv_symm μ]

/-- Star-preservation of `integratedBochnerL1` for Bochner twisted involution of integrable
functions when `μ` is a Haar measure with `μ.InnerRegularCompactLTTop` and `μ.inv ≪ μ`. -/
theorem integratedBochnerL1_bochnerInvolution_of_inv_absolutelyContinuous {μ : Measure G}
    [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]
    (hinv : μ.inv ≪ μ) {f : G → A} (hf : Integrable f μ) :
    P.integratedBochnerL1 μ
      ((α.integrable_bochnerInvolution_of_inv_absolutelyContinuous hinv hf).toL1
        (α.bochnerInvolution f)) =
      star (P.integratedBochnerL1 μ (hf.toL1 f)) := by
  rw [← α.toL1Equiv_star_symm_toL1_of_inv_absolutelyContinuous hinv hf,
    P.integratedBochnerL1_toL1Equiv μ, P.integratedOperatorL1_star μ,
    P.integratedOperatorL1_toL1Equiv_symm μ]

/-- Multiplicativity of `integratedBochnerL1` for Bochner twisted convolution against an inner
regular Haar measure. -/
theorem integratedBochnerL1_bochnerConvolution {μ : Measure G}
    [μ.IsHaarMeasure] [μ.InnerRegular] {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    P.integratedBochnerL1 μ ((α.integrable_bochnerConvolution hf hg).toL1
      (α.bochnerConvolution μ f g)) =
      P.integratedBochnerL1 μ (hf.toL1 f) * P.integratedBochnerL1 μ (hg.toL1 g) :=
  P.integratedBochnerL1_bochnerConvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf hg

/-- Star-preservation of `integratedBochnerL1` for Bochner twisted involution against an inner
regular Haar measure. -/
theorem integratedBochnerL1_bochnerInvolution {μ : Measure G}
    [μ.IsHaarMeasure] [μ.InnerRegular] {f : G → A} (hf : Integrable f μ) :
    P.integratedBochnerL1 μ
      ((α.integrable_bochnerInvolution hf).toL1 (α.bochnerInvolution f)) =
      star (P.integratedBochnerL1 μ (hf.toL1 f)) :=
  P.integratedBochnerL1_bochnerInvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_innerRegular hf

/-- Multiplicativity of `integratedBochnerL1` for Bochner twisted convolution against a regular
Haar measure. -/
theorem integratedBochnerL1_bochnerConvolution_of_regular {μ : Measure G}
    [μ.IsHaarMeasure] [μ.Regular] {f g : G → A}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    P.integratedBochnerL1 μ ((α.integrable_bochnerConvolution_of_regular hf hg).toL1
      (α.bochnerConvolution μ f g)) =
      P.integratedBochnerL1 μ (hf.toL1 f) * P.integratedBochnerL1 μ (hg.toL1 g) :=
  P.integratedBochnerL1_bochnerConvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf hg

/-- Star-preservation of `integratedBochnerL1` for Bochner twisted involution against a regular
Haar measure. -/
theorem integratedBochnerL1_bochnerInvolution_of_regular {μ : Measure G}
    [μ.IsHaarMeasure] [μ.Regular] {f : G → A} (hf : Integrable f μ) :
    P.integratedBochnerL1 μ
      ((α.integrable_bochnerInvolution_of_regular hf).toL1 (α.bochnerInvolution f)) =
      star (P.integratedBochnerL1 μ (hf.toL1 f)) :=
  P.integratedBochnerL1_bochnerInvolution_of_inv_absolutelyContinuous
    μ.inv_absolutelyContinuous_of_regular hf

end StarAndBochnerOps

/-! ### Discrete groups and counting-measure series -/

section Discrete

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- On a discrete group (without any countability assumption on `G`), if `f : G → A` has summable
norms, then the Hilbert-space terms `s ↦ π(f s)(U_s v)` are norm-summable. -/
theorem summable_norm_integrand_of_summable_norm {f : G → A}
    (hf : Summable fun s => ‖f s‖) (v : H) :
    Summable fun s => ‖P.coefficient (f s) (P.group s v)‖ :=
  integrable_count_iff.mp (P.integrable_integrand_of_integrable (integrable_count_iff.mpr hf) v)

/-- On a discrete group, if `f : G → A` has summable norms, then `s ↦ π(f s)(U_s v)` is
unconditionally summable in `H`. -/
theorem summable_integrand_of_summable_norm {f : G → A}
    (hf : Summable fun s => ‖f s‖) (v : H) :
    Summable fun s => P.coefficient (f s) (P.group s v) :=
  (P.summable_norm_integrand_of_summable_norm hf v).of_norm

/-- On a discrete group with counting measure, the integrated operator of any norm-summable
`f : G → A` evaluates as the unconditional series `∑' s, π(f s)(U_s v)`. -/
theorem integratedBochnerL1_count_toL1_apply {f : G → A}
    (hf : Summable fun s => ‖f s‖) (v : H) :
    P.integratedBochnerL1 Measure.count ((integrable_count_iff.mpr hf).toL1 f) v =
      ∑' s, P.coefficient (f s) (P.group s v) := by
  rw [P.integratedBochnerL1_toL1 (integrable_count_iff.mpr hf) v]
  exact (P.integrable_integrand_of_integrable (integrable_count_iff.mpr hf) v).integral_count

/-- On a discrete group with counting measure, the operator norm of the integrated form of a
norm-summable `f : G → A` is bounded by `∑' s, ‖f s‖`. -/
theorem norm_integratedBochnerL1_count_toL1_le {f : G → A}
    (hf : Summable fun s => ‖f s‖) :
    ‖P.integratedBochnerL1 Measure.count ((integrable_count_iff.mpr hf).toL1 f)‖ ≤
      ∑' s, ‖f s‖ :=
  (P.norm_integratedBochnerL1_toL1_le (integrable_count_iff.mpr hf)).trans_eq
    (integrable_count_iff.mpr hf).norm.integral_count

end Discrete

end TauCeti.CStarAction.CovariantRepresentation
