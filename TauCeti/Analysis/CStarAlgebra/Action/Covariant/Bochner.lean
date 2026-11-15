/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Bochner
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Bochner `L¹` integrated forms of covariant representations

Let `P = (π, U)` be a covariant representation of a point-norm continuous C⋆-action `α` of a
topological group `G` on a possibly nonunital C⋆-algebra `A`, acting on a complex Hilbert space `H`.
In `TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated` and
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.Normed`, the integrated form `(π ⋊ U)(f)` is built
first on compactly supported continuous coefficient functions `f : C_c(G, A)` by the Hilbert-space
vector integral `v ↦ ∫ g, π (f g) (U g v) dμ(g)` and then extended by continuity to the abstract
completion `UniformSpace.Completion (ConvolutionAlgebra α μ)`.

This file constructs the integrated form `CovariantRepresentation.integratedLp` directly on the
Bochner space `Lp A 1 μ` for any Borel measure `μ` on an `R₁` group that is inner regular with
respect to compact sets on sets of finite measure (`Measure.InnerRegularCompactLTTop`). Even when
`H` is nonseparable and `G` is not second countable, inner regularity makes every integrand
`g ↦ π (f g) (U g v)` strongly measurable on the σ-finite support of an integrable `f : G → A`:
each continuous orbit `g ↦ U g v` has compact, hence metrizable and separable, image on every
compact subset of `G` (`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_clm_apply`). The
resulting operator has norm at most `∫ g, ‖f g‖ dμ(g)` (`exists_integratedOperator`), without
assuming operator-norm continuity of `U`, unitality of `A`, nondegeneracy of `π`, or σ-finiteness
of `μ`.

Along `ConvolutionAlgebra.toL1FromCompletion` (and `ConvolutionAlgebra.completionEquivLp` when `G`
is weakly locally compact and `μ` is regular), `integratedLp` agrees with the completion extension
`CovariantRepresentation.integratedOperatorL1`. For a left-invariant locally finite inner-regular
measure, `integratedLp` intertwines `CStarAction.translateLp` with `U` and is multiplicative with
respect to `CStarAction.convolutionLp`; passing vector-valued evaluation through the `Lp`-valued
Bochner integral avoids any product-measure Fubini hypothesis. On a locally compact group with a
Haar measure, `integratedOperatorL1` preserves the star operation (bundling to
`integratedStarAlgHomL1`), and when `μ` is regular `integratedLp` sends
`CStarAction.twistedInvolutionLp` to the operator adjoint. Specializations cover trivial actions,
equivariant pullbacks, Hilbert direct sums, scalar multiples via
`ContRepresentation.integratedOperatorL1`, the scalar regular representation as `Lp.convolutionL`,
and counting measure on arbitrary discrete groups as absolutely convergent `ℓ¹` operator-vector
series.

## Main definitions

* `TauCeti.CStarAction.CovariantRepresentation.integratedLp`: the contractive continuous linear map
  `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` sending `u` to `v ↦ ∫ g, π (u g) (U g v) dμ(g)`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedStarAlgHomL1`: the integrated form on
  `Completion (ConvolutionAlgebra α μ)` bundled as a nonunital ⋆-algebra homomorphism.

## Main statements

* `TauCeti.CStarAction.CovariantRepresentation.exists_integratedOperator`: every Bochner-integrable
  `f : G → A` defines a bounded operator `ξ ↦ ∫ g, π (f g) (U g ξ) dμ(g)` of norm at most
  `∫ g, ‖f g‖ dμ(g)`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedLp_toL1FromCompletion`,
  `TauCeti.CStarAction.CovariantRepresentation.integratedLp_completionEquivLp`: `integratedLp`
  agrees with `integratedOperatorL1` under the Bochner `L¹` identification.
* `TauCeti.CStarAction.CovariantRepresentation.integratedLp_convolutionLp`:
  `integratedLp (u ⋆ v) = integratedLp u * integratedLp v`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedOperatorL1_star`,
  `TauCeti.CStarAction.CovariantRepresentation.integratedLp_twistedInvolutionLp`: star preservation
  on the `L¹` completion and under `twistedInvolutionLp`.
* `TauCeti.CStarAction.CovariantRepresentation.integratedLp_regular_trivial`: for the trivial
  action on `ℂ`, the integrated regular representation on `L²(G)` is left convolution
  `MeasureTheory.Lp.convolutionL`.
* `TauCeti.CStarAction.CovariantRepresentation.hasSum_integratedLp_count_toL1`,
  `TauCeti.CStarAction.CovariantRepresentation.integratedLp_count_toL1`: for counting measure on a
  discrete group, the `L¹` integrated form acts by the absolutely summable series
  `∑' g, π (f g) (U g v)`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory Topology UniformSpace
open scoped CompactlySupported CStarAlgebra ENNReal InnerProductSpace

namespace TauCeti.CStarAction.CovariantRepresentation

/-! ### Direct vector integration on Bochner `L¹` -/

section IntegratedLp

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- The coefficient representation viewed as a continuous linear map into `H →L[ℂ] H`. -/
private def coefficientCLM : A →L[ℂ] (H →L[ℂ] H) where
  toLinearMap := (P.coefficient : A →ₗ[ℂ] (H →L[ℂ] H))
  cont := map_continuous P.coefficient

/-- For any Bochner-integrable `f : G → A` and vector `v : H`, the orbit integrand
`g ↦ π (f g) (U g v)` is Bochner-integrable in `H`. Inner regularity of `μ` on finite-measure sets
gives strong measurability without separability of `H` or second countability of `G`. -/
theorem integrable_integrand_of_integrable {f : G → A} (hf : Integrable f μ) (v : H) :
    Integrable (fun g => P.coefficient (f g) (P.group g v)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun g => ((P.coefficientCLM).flip (P.group g v)) (f g)) μ :=
    hf.aefinStronglyMeasurable.aestronglyMeasurable_clm_apply
      (((P.coefficientCLM).flip).continuous.comp (P.continuous_orbit v))
  refine (hf.norm.mul_const ‖v‖).mono' hmeas (.of_forall fun g => ?_)
  calc
    ‖P.coefficient (f g) (P.group g v)‖
        ≤ ‖P.coefficient (f g)‖ * ‖P.group g v‖ := (P.coefficient (f g)).le_opNorm _
    _ ≤ ‖f g‖ * ‖v‖ := by
      rw [P.isUnitary.norm_map]
      exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)

omit [R1Space G] [BorelSpace G] [μ.InnerRegularCompactLTTop] in
private theorem norm_integral_integrand_le {f : G → A} (hf : Integrable f μ) (v : H) :
    ‖∫ g, P.coefficient (f g) (P.group g v) ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  calc
    ‖∫ g, P.coefficient (f g) (P.group g v) ∂μ‖ ≤ ∫ g, ‖f g‖ * ‖v‖ ∂μ := by
      refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (.of_forall fun g => ?_)
      calc
        ‖P.coefficient (f g) (P.group g v)‖
            ≤ ‖P.coefficient (f g)‖ * ‖P.group g v‖ := (P.coefficient (f g)).le_opNorm _
        _ ≤ ‖f g‖ * ‖v‖ := by
          rw [P.isUnitary.norm_map]
          exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖v‖ := integral_mul_const _ _

/-- **The Bochner `L¹` integrated form** of a covariant representation `P = (π, U)`: the contractive
continuous linear map `Lp A 1 μ →L[ℂ] (H →L[ℂ] H)` defined pointwise on `v : H` by the Hilbert-space
Bochner integral `∫ g, π (u g) (U g v) dμ(g)`. -/
def integratedLp : Lp A 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun (u : Lp A 1 μ) (v : H) => ∫ g, P.coefficient (u g) (P.group g v) ∂μ)
      (fun u₁ u₂ v => by
        rw [← integral_add (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u₁) v)
          (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u₂) v)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u₁ u₂] with g hg
        rw [hg, Pi.add_apply, map_add, add_apply])
      (fun c u v => by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u] with g hg
        rw [hg, Pi.smul_apply, map_smul, smul_apply])
      (fun u v₁ v₂ => by
        rw [← integral_add (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v₁)
          (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v₂)]
        simp_rw [map_add])
      (fun c u v => by
        rw [← integral_smul]
        simp_rw [map_smul]))
    1 fun u v => by
      simpa [L1.norm_eq_integral_norm] using
        P.norm_integral_integrand_le μ (L1.integrable_coeFn u) v

/-- The defining vector integral for `integratedLp`. -/
theorem integratedLp_apply (u : Lp A 1 μ) (v : H) :
    P.integratedLp μ u v = ∫ g, P.coefficient (u g) (P.group g v) ∂μ :=
  (rfl)

/-- On the `L¹` class of a Bochner-integrable function `f : G → A`, `integratedLp` acts by
`v ↦ ∫ g, π (f g) (U g v) dμ(g)`. -/
@[simp]
theorem integratedLp_toL1 {f : G → A} (hf : Integrable f μ) (v : H) :
    P.integratedLp μ (hf.toL1 f) v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ := by
  rw [integratedLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL1] with g hg
  rw [hg]

/-- `integratedLp` is a contraction on `Lp A 1 μ`: `‖(π ⋊ U)(u)‖ ≤ ‖u‖`. -/
theorem norm_integratedLp_apply_le (u : Lp A 1 μ) :
    ‖P.integratedLp μ u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun v => ?_
  simpa [integratedLp_apply, L1.norm_eq_integral_norm] using
    P.norm_integral_integrand_le μ (L1.integrable_coeFn u) v

/-- The operator norm of `integratedLp` is at most one. -/
theorem norm_integratedLp_le : ‖P.integratedLp μ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using P.norm_integratedLp_apply_le μ u

/-- For an integrable coefficient function `f : G → A`, the operator norm of its `L¹` integrated
form is bounded by `∫ g, ‖f g‖ dμ(g)`. -/
theorem norm_integratedLp_toL1_le {f : G → A} (hf : Integrable f μ) :
    ‖P.integratedLp μ (hf.toL1 f)‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun v => ?_
  rw [integratedLp_toL1]
  exact P.norm_integral_integrand_le μ hf v

/-- **Existence and `L¹` bound for the integrated operator of an integrable coefficient function**:
every Bochner-integrable `f : G → A` defines a bounded operator `T : H →L[ℂ] H` acting on vectors
by `T ξ = ∫ g, π (f g) (U g ξ) dμ(g)` with `‖T‖ ≤ ∫ g, ‖f g‖ dμ(g)`. -/
theorem exists_integratedOperator (f : G → A) (hf : Integrable f μ) :
    ∃ T : H →L[ℂ] H,
      (∀ ξ, T ξ = ∫ g, P.coefficient (f g) (P.group g ξ) ∂μ) ∧ ‖T‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  ⟨P.integratedLp μ (hf.toL1 f), P.integratedLp_toL1 μ hf, P.norm_integratedLp_toL1_le μ hf⟩

/-- Matrix coefficients of `integratedLp` are integrals of vector matrix coefficients. -/
theorem inner_integratedLp_apply (u : Lp A 1 μ) (w v : H) :
    ⟪w, P.integratedLp μ u v⟫_ℂ =
      ∫ g, ⟪w, P.coefficient (u g) (P.group g v)⟫_ℂ ∂μ := by
  rw [integratedLp_apply,
    integral_inner (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v)]

/-- Covariance moves a coefficient operator on the right of `integratedLp` inside the integral with
the action twist. -/
theorem integratedLp_coefficient_apply (u : Lp A 1 μ) (a : A) (v : H) :
    P.integratedLp μ u (P.coefficient a v) =
      ∫ g, P.coefficient (u g * α g a) (P.group g v) ∂μ := by
  rw [integratedLp_apply]
  simp_rw [P.covariance, map_mul, mul_apply_eq_comp]

/-- Left multiplication by `a ∈ A` on `Lp A 1 μ` becomes left multiplication by `π(a)`:
`(π ⋊ U)(a • u) = π(a) (π ⋊ U)(u)`. -/
@[simp]
theorem integratedLp_mul_compLp (a : A) (u : Lp A 1 μ) :
    P.integratedLp μ ((ContinuousLinearMap.mul ℂ A a).compLp u) =
      P.coefficient a * P.integratedLp μ u := by
  ext v
  rw [mul_apply_eq_comp, integratedLp_apply, integratedLp_apply,
    ← (P.coefficient a).integral_comp_comm
      (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v)]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℂ A a).coeFn_compLp u] with g hg
  simp [hg, map_mul]

/-- For the trivial covariant pair associated to `π`, `integratedLp` applies `π` to the Bochner
integral of the coefficient class. -/
@[simp]
theorem trivial_integratedLp (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (u : Lp A 1 μ) :
    (trivial (G := G) π).integratedLp μ u = π (∫ g, u g ∂μ) := by
  ext v
  have h := (trivial (G := G) π).integral_coefficient_apply (L1.integrable_coeFn u) v
  simpa only [integratedLp_apply, trivial_coefficient, trivial_group,
    ContRepresentation.trivial_apply] using h

/-- On compactly supported continuous functions, `integratedLp` agrees with `integratedOperator`. -/
@[simp]
theorem integratedLp_toL1_cc [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) :
    P.integratedLp μ (f.integrable.toL1 f) = P.integratedOperator μ f := by
  ext v
  rw [integratedLp_toL1, integratedOperator_apply]

/-- On `ConvolutionAlgebra α μ`, `integratedLp` composed with `toL1` agrees with
`integratedOperator`. -/
@[simp]
theorem integratedLp_toL1_ofConv [IsFiniteMeasureOnCompacts μ] (f : ConvolutionAlgebra α μ) :
    P.integratedLp μ (ConvolutionAlgebra.toL1 f) = P.integratedOperator μ f.ofConv := by
  have hf : ConvolutionAlgebra.toL1 f = f.ofConv.integrable.toL1 f.ofConv :=
    Lp.ext <| (ConvolutionAlgebra.coeFn_toL1 f).trans f.ofConv.integrable.coeFn_toL1.symm
  rw [hf, integratedLp_toL1_cc]

end IntegratedLp

/-! ### Functoriality, Hilbert direct sums, and scalar comparison -/

section Functoriality

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Pulling back a covariant pair along an equivariant homomorphism `φ : Hom α β` commutes with
`integratedLp`. -/
theorem integratedLp_comap (Q : CovariantRepresentation β H) (φ : Hom α β)
    (μ : Measure G) [μ.InnerRegularCompactLTTop] (u : Lp A 1 μ) :
    (Q.comap φ).integratedLp μ u = Q.integratedLp μ (φ.mapLp μ 1 u) := by
  ext v
  rw [integratedLp_apply, integratedLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [φ.coeFn_mapLp u] with g hg
  simp [hg]

/-- `integratedLp` commutes with evaluation in every summand of a Hilbert direct sum. -/
@[simp]
theorem integratedLp_hilbertSum_apply {ι : Type*} {K : ι → Type*}
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)] [∀ i, CompleteSpace (K i)]
    (Q : ∀ i, CovariantRepresentation α (K i)) (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) (x : lp K 2) (i : ι) :
    (hilbertSum Q).integratedLp μ u x i = (Q i).integratedLp μ u (x i) := by
  let ev := lp.evalCLM ℂ K 2 i
  calc
    (hilbertSum Q).integratedLp μ u x i = ev ((hilbertSum Q).integratedLp μ u x) :=
      (lp.evalCLM_apply i _).symm
    _ = ev (∫ g, (hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x) ∂μ) :=
      congrArg ev ((hilbertSum Q).integratedLp_apply μ u x)
    _ = ∫ g, ev ((hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x)) ∂μ :=
      (ev.integral_comp_comm
        ((hilbertSum Q).integrable_integrand_of_integrable μ (L1.integrable_coeFn u) x)).symm
    _ = ∫ g, (Q i).coefficient (u g) ((Q i).group g (x i)) ∂μ :=
      integral_congr_ae (.of_forall fun g => by simp [ev])
    _ = (Q i).integratedLp μ u (x i) := ((Q i).integratedLp_apply μ u (x i)).symm

/-- The `L¹` integrated operator of a Hilbert direct sum is the Hilbert direct sum of the
component `L¹` integrated operators. -/
theorem integratedLp_hilbertSum {ι : Type*} {K : ι → Type*}
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)] [∀ i, CompleteSpace (K i)]
    (Q : ∀ i, CovariantRepresentation α (K i)) (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (u : Lp A 1 μ) :
    (hilbertSum Q).integratedLp μ u =
      lp.mapCLM 2 (fun i => (Q i).integratedLp μ u) (norm_nonneg u)
        (fun i => (Q i).norm_integratedLp_apply_le μ u) := by
  ext x i
  simp

section ScalarComparison

variable (P : CovariantRepresentation α H) (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- Transport the measurable space structure of `G` to `Additive G` as a reducible local instance
so that `(μ : Measure (Additive G))` and `Lp ℂ 1 μ` remain definitionally compatible. -/
@[reducible] local instance : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
local instance : R1Space (Additive G) := ‹R1Space G›
local instance : BorelSpace (Additive G) := ‹BorelSpace G›
local instance : Measure.InnerRegularCompactLTTop (α := Additive G) μ :=
  inferInstanceAs (Measure.InnerRegularCompactLTTop (α := G) μ)

/-- On scalar `L¹` multiples `g ↦ φ g • a` of a fixed coefficient `a ∈ A`, `integratedLp` factors as
`π(a)` composed with the scalar `L¹` integrated form `ContRepresentation.integratedOperatorL1`. -/
theorem integratedLp_toSpanSingleton_compLp (φ : Lp ℂ 1 μ) (a : A) :
    P.integratedLp μ ((ContinuousLinearMap.toSpanSingleton ℂ a).compLp φ) =
      P.coefficient a *
        (P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
          (G := Additive G) (fun v => P.continuous_orbit v)
          (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
          (μ : Measure (Additive G))
          (φ : Lp ℂ 1 (μ : Measure (Additive G))) := by
  have hs (v : H) := ContRepresentation.integratedOperatorL1_apply
    (G := Additive G)
    (π := P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom)
    (hcont := fun v => P.continuous_orbit v)
    (hbdd := (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le)
    (μ := (μ : Measure (Additive G)))
    (φ : Lp ℂ 1 (μ : Measure (Additive G))) v
  ext v
  have hi : Integrable (fun g => φ g • P.group g v) μ := by
    refine ((L1.integrable_coeFn φ).norm.mul_const ‖v‖).mono'
      ((L1.integrable_coeFn φ).aefinStronglyMeasurable.aestronglyMeasurable_smul
        (P.continuous_orbit v)) (.of_forall fun g => ?_)
    rw [norm_smul, P.isUnitary.norm_map]
  calc
    P.integratedLp μ ((ContinuousLinearMap.toSpanSingleton ℂ a).compLp φ) v
        = P.coefficient a (∫ g, φ g • P.group g v ∂μ) := by
          rw [integratedLp_apply, ← (P.coefficient a).integral_comp_comm hi]
          refine integral_congr_ae ?_
          filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ a).coeFn_compLp φ] with g hg
          simp [hg, map_smul]
    _ = _ := congrArg (P.coefficient a) (hs v).symm

end ScalarComparison

end Functoriality

/-! ### Equivariance under twisted left translation and multiplicativity on `L¹` -/

section TranslateAndConvolution

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- `integratedLp` intertwines twisted left translation `translateLp` with the unitary group
representation: `(π ⋊ U)(translateLp r u) = U_r (π ⋊ U)(u)`. -/
@[simp]
theorem integratedLp_translateLp [MeasurableMul G] [μ.IsMulLeftInvariant]
    (r : G) (u : Lp A 1 μ) :
    P.integratedLp μ (α.translateLp μ 1 r u) = P.group r * P.integratedLp μ u := by
  ext v
  rw [mul_apply_eq_comp, integratedLp_apply, integratedLp_apply,
    ← (P.group r).integral_comp_comm
      (P.integrable_integrand_of_integrable μ (L1.integrable_coeFn u) v),
    ← integral_mul_left_eq_self _ r]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ r).quasiMeasurePreserving.ae
    (α.coeFn_translateLp r u)] with s hs
  simp [hs, P.covariance, map_mul]

/-- Along `ConvolutionAlgebra.toL1FromCompletion`, `integratedLp` agrees with the completion
extension `integratedOperatorL1`. -/
@[simp]
theorem integratedLp_toL1FromCompletion [IsTopologicalGroup G] [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedLp μ (ConvolutionAlgebra.toL1FromCompletion α μ x) =
      P.integratedOperatorL1 μ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((P.integratedLp μ).continuous.comp (ConvolutionAlgebra.toL1FromCompletion α μ).continuous)
      (P.continuous_integratedOperatorL1 μ)
  | ih f => simp

/-- **Multiplicativity of `integratedLp` under twisted `L¹` convolution**:
`(π ⋊ U)(u ⋆ v) = (π ⋊ U)(u) * (π ⋊ U)(v)` for any left-invariant locally finite inner-regular Borel
measure `μ`. -/
@[simp]
theorem integratedLp_convolutionLp [IsTopologicalGroup G] [IsLocallyFiniteMeasure μ]
    [μ.IsMulLeftInvariant] (u v : Lp A 1 μ) :
    P.integratedLp μ (α.convolutionLp μ 1 ENNReal.one_ne_top u v) =
      P.integratedLp μ u * P.integratedLp μ v := by
  ext ξ
  let L : Lp A 1 μ →L[ℂ] H := (ContinuousLinearMap.apply ℂ H ξ).comp (P.integratedLp μ)
  have hL (w : Lp A 1 μ) : L w = P.integratedLp μ w ξ := rfl
  have hcomm := L.integral_comp_comm
    (α.integrable_mul_translateLp μ ENNReal.one_ne_top (L1.integrable_coeFn u) v)
  rw [← hL, α.convolutionLp_apply, ← hcomm]
  simp only [hL, P.integratedLp_mul_compLp, P.integratedLp_translateLp, mul_apply_eq_comp]
  exact P.integratedLp_apply μ u (P.integratedLp μ v ξ)

/-- Under the isometric equivalence `ConvolutionAlgebra.completionEquivLp` for a regular measure on
a weakly locally compact `R₁` group, `integratedLp` agrees with `integratedOperatorL1`. -/
@[simp]
theorem integratedLp_completionEquivLp [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G]
    [μ.Regular] [μ.IsMulLeftInvariant] (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedLp μ (ConvolutionAlgebra.completionEquivLp α μ x) =
      P.integratedOperatorL1 μ x := by
  rw [ConvolutionAlgebra.completionEquivLp_apply, integratedLp_toL1FromCompletion]

/-- Pulling `integratedOperatorL1` back along `(completionEquivLp α μ).symm` recovers
`integratedLp`. -/
@[simp]
theorem integratedOperatorL1_completionEquivLp_symm [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [μ.Regular] [μ.IsMulLeftInvariant] (u : Lp A 1 μ) :
    P.integratedOperatorL1 μ ((ConvolutionAlgebra.completionEquivLp α μ).symm u) =
      P.integratedLp μ u := by
  rw [← P.integratedLp_completionEquivLp μ, LinearIsometryEquiv.apply_symm_apply]

/-- For the trivial action of `G` on `ℂ` and the canonical scalar representation on `ℂ`, the
`L¹` integrated form of the regular covariant representation on `L²(G)` is scalar left convolution
`MeasureTheory.Lp.convolutionL`. -/
theorem integratedLp_regular_trivial [IsTopologicalGroup G] [IsLocallyFiniteMeasure μ]
    [μ.IsMulLeftInvariant] :
    (regular (CStarAction.trivial (G := G) (A := ℂ))
        (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom μ).integratedLp μ =
      Lp.convolutionL μ 2 ENNReal.ofNat_ne_top := by
  let ρ : ℂ →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ) := (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom
  ext f ξ : 2
  rw [integratedLp_apply, Lp.convolutionL_apply]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  refine Lp.ext ?_
  filter_upwards [coeFn_regular_coefficient (CStarAction.trivial (G := G) (A := ℂ)) ρ μ (f g)
      ((regular (CStarAction.trivial (G := G) (A := ℂ)) ρ μ).group g ξ),
    μ.coeFn_leftRegular (𝕜 := ℂ) 2 g ξ,
    Lp.coeFn_smul (f g) (Lp.leftTranslation μ 2 ℂ g ξ),
    Lp.coeFn_leftTranslation (𝕜 := ℂ) g ξ] with r h₁ h₂ h₃ h₄
  rw [h₁, regular_group, h₂, h₃, Pi.smul_apply, h₄]
  simp [ρ, Algebra.algebraMap_eq_smul_one]

end TranslateAndConvolution

/-! ### Star preservation on the `L¹` completion and Bochner `L¹` -/

section Star

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The extended integrated form `integratedOperatorL1` on `Completion (ConvolutionAlgebra α μ)`
preserves the star operation. -/
@[simp]
theorem integratedOperatorL1_star (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedOperatorL1 μ (star x) = star (P.integratedOperatorL1 μ x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    rw [← Completion.coe_star, integratedOperatorL1_coe, integratedOperatorL1_coe,
      ConvolutionAlgebra.ofConv_star, integratedOperator_twistedInvolution]

/-- The integrated form on the twisted `L¹` completion bundled as a nonunital complex ⋆-algebra
homomorphism. -/
def integratedStarAlgHomL1 : Completion (ConvolutionAlgebra α μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toNonUnitalAlgHom := P.integratedOperatorL1 μ
  map_star' := P.integratedOperatorL1_star μ

/-- `integratedStarAlgHomL1` agrees on elements with `integratedOperatorL1`. -/
@[simp]
theorem integratedStarAlgHomL1_apply (x : Completion (ConvolutionAlgebra α μ)) :
    P.integratedStarAlgHomL1 μ x = P.integratedOperatorL1 μ x :=
  (rfl)

/-- For a regular Haar measure on a locally compact group, `integratedLp` sends
`twistedInvolutionLp` to the operator adjoint. -/
@[simp]
theorem integratedLp_twistedInvolutionLp [μ.Regular] (u : Lp A 1 μ) :
    P.integratedLp μ (α.twistedInvolutionLp μ u) = star (P.integratedLp μ u) := by
  rw [← P.integratedOperatorL1_completionEquivLp_symm μ (α.twistedInvolutionLp μ u),
    ConvolutionAlgebra.completionEquivLp_symm_twistedInvolutionLp, integratedOperatorL1_star,
    P.integratedOperatorL1_completionEquivLp_symm μ]

end Star

/-! ### Counting measure on discrete groups -/

section Discrete

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For counting measure on a discrete group (not assumed countable), `integratedLp` acts on a
vector `v` by the unconditionally convergent series `∑ g, π (u g) (U g v)`. -/
theorem hasSum_integratedLp_count_apply (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    HasSum (fun g => P.coefficient (u g) (P.group g v)) (P.integratedLp Measure.count u v) := by
  rw [integratedLp_apply]
  have hint : Integrable (fun g => P.coefficient (u g) (P.group g v))
      (Measure.sum Measure.dirac) :=
    P.integrable_integrand_of_integrable Measure.count (L1.integrable_coeFn u) v
  simpa only [Measure.count, integral_dirac] using hasSum_integral_measure hint

/-- Series formula for `integratedLp` with respect to counting measure on a discrete group. -/
theorem integratedLp_count_apply (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    P.integratedLp Measure.count u v = ∑' g, P.coefficient (u g) (P.group g v) :=
  (P.hasSum_integratedLp_count_apply u v).tsum_eq.symm

/-- For an `ℓ¹` coefficient family `f : G → A` on a discrete group, the vector series
`g ↦ π (f g) (U g v)` converges unconditionally to `integratedLp` applied to
`(integrable_count_iff.2 hf).toL1 f`. -/
theorem hasSum_integratedLp_count_toL1 {f : G → A} (hf : Summable (‖f ·‖)) (v : H) :
    HasSum (fun g => P.coefficient (f g) (P.group g v))
      (P.integratedLp Measure.count ((integrable_count_iff.2 hf).toL1 f) v) := by
  have hcoe : ∀ g, ((integrable_count_iff.2 hf).toL1 f : G → A) g = f g :=
    Measure.ae_count_iff.1 (integrable_count_iff.2 hf).coeFn_toL1
  simpa only [hcoe] using P.hasSum_integratedLp_count_apply ((integrable_count_iff.2 hf).toL1 f) v

/-- For an `ℓ¹` coefficient family `f : G → A` on a discrete group, `integratedLp` acts on vectors
by `∑' g, π (f g) (U g v)`. -/
theorem integratedLp_count_toL1 {f : G → A} (hf : Summable (‖f ·‖)) (v : H) :
    P.integratedLp Measure.count ((integrable_count_iff.2 hf).toL1 f) v =
      ∑' g, P.coefficient (f g) (P.group g v) :=
  (P.hasSum_integratedLp_count_toL1 hf v).tsum_eq.symm

/-- For an `ℓ¹` coefficient family `f : G → A` on a discrete group, the operator norm of its `L¹`
integrated form is bounded by `∑' g, ‖f g‖`. -/
theorem norm_integratedLp_count_toL1_le {f : G → A} (hf : Summable (‖f ·‖)) :
    ‖P.integratedLp Measure.count ((integrable_count_iff.2 hf).toL1 f)‖ ≤ ∑' g, ‖f g‖ := by
  refine (P.norm_integratedLp_toL1_le Measure.count (integrable_count_iff.2 hf)).trans_eq ?_
  have hint : Integrable (‖f ·‖) (Measure.sum Measure.dirac) :=
    (integrable_count_iff.2 hf).norm
  simpa only [Measure.count, integral_dirac] using integral_sum_measure hint

end Discrete

end TauCeti.CStarAction.CovariantRepresentation
