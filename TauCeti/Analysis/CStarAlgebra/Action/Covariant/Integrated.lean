/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Translate
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Basic
public import TauCeti.RepresentationTheory.Continuous.Integrated.Basic
public import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
# Vector-valued integrated forms of covariant pairs

For a compactly supported continuous coefficient function `f`, the integrated form is the bounded
operator `v ↦ ∫ g, π (f g) (U g v)`. Integration is in the Hilbert space, not in the operator-norm
space: strong continuity of `U` does not imply norm continuity. The operator depends linearly on
`f` and has norm at most `∫ g, ‖f g‖`. No separability, second countability, or σ-finiteness is
needed. We first build this construction (`TauCeti.CStarAction.vectorIntegratedOperator`) for any
C⋆-representation `π` and strongly continuous contractive operator family `U`, so that both
untwisted covariant representations and cocycle-twisted covariant pairs share the same analytic
machinery. For the definition, the norm bound and the covariance identity the measure need only be
finite on compact sets; left invariance enters only for multiplicativity under twisted convolution.

Covariance moves a coefficient on the right of an integrated operator inside its integral with
the action twist, while a coefficient on the left comes from the pointwise left multiplier,
`(π ⋊ U)(a • f) = π(a) (π ⋊ U)(f)`. For scalar multiples of a fixed coefficient, the
construction agrees with `ContRepresentation.integratedOperatorL1`, after pulling the group
representation back along `MulEquiv.multiplicativeAdditive`.

For a left-invariant measure the integrated form is multiplicative for twisted convolution,
`(π ⋊ U) (f ⋆ g) = (π ⋊ U) f * (π ⋊ U) g`, and turns the twisted left translation
`CStarAction.translate` into the group representation, `(π ⋊ U)(r • f) = U_r (π ⋊ U)(f)`. The
order of integration is exchanged by Fubini's theorem for compactly supported continuous
functions, so σ-finiteness is still not needed.
Extension to coefficient-valued L¹ and the involution identity require additional arguments.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction

/-! ### Shared vector-valued integration for operator families -/

section VectorIntegral

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Vector evaluation of a C⋆-representation commutes with Bochner integration. -/
theorem integral_representation_apply {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {F : X → A} (hF : Integrable F ν) (w : H) :
    ∫ x, π (F x) w ∂ν = π (∫ x, F x ∂ν) w :=
  ((ContinuousLinearMap.apply ℂ H w).comp
    { toLinearMap := (π : A →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous π }).integral_comp_comm hF

variable {G : Type*} [TopologicalSpace G] (U : G → (H →L[ℂ] H))

/-- The vector integrand `g ↦ π (f g) (U g v)` is continuous when `U` is strongly continuous. -/
@[fun_prop]
theorem continuous_vectorIntegrand (hU_cont : ∀ v, Continuous fun g => U g v)
    (f : C_c(G, A)) (v : H) :
    Continuous fun g => π (f g) (U g v) :=
  (map_continuous π |>.comp f.continuous).clm_apply (hU_cont v)

/-- The vector integrand `g ↦ π (f g) (U g v)` vanishes outside the support of `f`. -/
theorem hasCompactSupport_vectorIntegrand (f : C_c(G, A)) (v : H) :
    HasCompactSupport fun g => π (f g) (U g v) :=
  f.hasCompactSupport.mono fun _ hg hz => hg (by simp [hz])

variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- Compact support makes every vector integrand `g ↦ π (f g) (U g v)` integrable. -/
theorem integrable_vectorIntegrand (hU_cont : ∀ v, Continuous fun g => U g v)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) (v : H) :
    Integrable (fun g => π (f g) (U g v)) μ :=
  (continuous_vectorIntegrand π U hU_cont f v).integrable_of_hasCompactSupport
    (hasCompactSupport_vectorIntegrand π U f v)

private theorem norm_integral_vectorIntegrand_le (hU_norm : ∀ g v, ‖U g v‖ ≤ ‖v‖)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) (v : H) :
    ‖∫ g, π (f g) (U g v) ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun g => ?_)
  exact ((π (f g)).le_opNorm _).trans <|
    mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π (f g)) (hU_norm g v)
      (norm_nonneg _) (norm_nonneg _)

/-- The vector-valued integrated form on `C_c(G, A)` associated to a C⋆-representation `π` and a
strongly continuous contractive operator family `U`, sending `f` to the bounded operator
`v ↦ ∫ g, π (f g) (U g v) ∂μ`. -/
def vectorIntegratedOperator (hU_cont : ∀ v, Continuous fun g => U g v)
    (hU_norm : ∀ g v, ‖U g v‖ ≤ ‖v‖) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] :
    C_c(G, A) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ g, π (f g) (U g v) ∂μ
      map_add' v w := by
        simp_rw [map_add]
        exact integral_add (integrable_vectorIntegrand π U hU_cont μ f v)
          (integrable_vectorIntegrand π U hU_cont μ f w)
      map_smul' c _ := by
        simp_rw [map_smul]
        exact integral_smul c _ }
    (∫ g, ‖f g‖ ∂μ) (norm_integral_vectorIntegrand_le π U hU_norm μ f)
  map_add' f h := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, map_add,
      add_apply]
    exact integral_add (integrable_vectorIntegrand π U hU_cont μ f v)
      (integrable_vectorIntegrand π U hU_cont μ h v)
  map_smul' c f := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.smul_apply, map_smul,
      smul_apply, RingHom.id_apply]
    exact integral_smul c _

/-- The defining vector formula for `vectorIntegratedOperator`. -/
theorem vectorIntegratedOperator_apply {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {U : G → (H →L[ℂ] H)}
    {hU_cont : ∀ v, Continuous fun g => U g v} {hU_norm : ∀ g v, ‖U g v‖ ≤ ‖v‖}
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) (v : H) :
    vectorIntegratedOperator π U hU_cont hU_norm μ f v = ∫ g, π (f g) (U g v) ∂μ :=
  (rfl)

/-- The operator norm of `vectorIntegratedOperator` is bounded by the `L¹` norm of `f`. -/
theorem norm_vectorIntegratedOperator_le {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {U : G → (H →L[ℂ] H)}
    {hU_cont : ∀ v, Continuous fun g => U g v} {hU_norm : ∀ g v, ‖U g v‖ ≤ ‖v‖}
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) :
    ‖vectorIntegratedOperator π U hU_cont hU_norm μ f‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    (norm_integral_vectorIntegrand_le π U hU_norm μ f)

/-- Matrix coefficients of `vectorIntegratedOperator` can be computed by integrating vector
matrix coefficients. -/
theorem inner_vectorIntegratedOperator_apply {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {U : G → (H →L[ℂ] H)}
    {hU_cont : ∀ v, Continuous fun g => U g v} {hU_norm : ∀ g v, ‖U g v‖ ≤ ‖v‖}
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] (f : C_c(G, A)) (w v : H) :
    ⟪w, vectorIntegratedOperator π U hU_cont hU_norm μ f v⟫_ℂ =
      ∫ g, ⟪w, π (f g) (U g v)⟫_ℂ ∂μ := by
  rw [vectorIntegratedOperator_apply, integral_inner (integrable_vectorIntegrand π U hU_cont μ f v)]

/-- Left multiplication by a coefficient pulls out of `vectorIntegratedOperator` as left
multiplication by `π a`. -/
@[simp]
theorem vectorIntegratedOperator_smul {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {U : G → (H →L[ℂ] H)}
    {hU_cont : ∀ v, Continuous fun g => U g v} {hU_norm : ∀ g v, ‖U g v‖ ≤ ‖v‖}
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] (a : A) (f : C_c(G, A)) :
    vectorIntegratedOperator π U hU_cont hU_norm μ (a • f) =
      π a * vectorIntegratedOperator π U hU_cont hU_norm μ f := by
  ext v
  simpa only [vectorIntegratedOperator_apply, CompactlySupportedContinuousMap.smul_apply,
    smul_eq_mul, map_mul, mul_apply_eq_comp] using
    (π a).integral_comp_comm (integrable_vectorIntegrand π U hU_cont μ f v)

end VectorIntegral

namespace CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The vector integrand of the integrated form is continuous. -/
@[fun_prop]
theorem continuous_integrand (f : C_c(G, A)) (v : H) :
    Continuous fun g => P.coefficient (f g) (P.group g v) :=
  continuous_vectorIntegrand P.coefficient (fun g => P.group g) P.continuous_orbit f v

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The vector integrand vanishes outside the support of the coefficient function. -/
theorem hasCompactSupport_integrand (f : C_c(G, A)) (v : H) :
    HasCompactSupport fun g => P.coefficient (f g) (P.group g v) :=
  hasCompactSupport_vectorIntegrand P.coefficient (fun g => P.group g) f v

/-- Compact support makes every vector integrand integrable. -/
theorem integrable_integrand (f : C_c(G, A)) (v : H) :
    Integrable (fun g => P.coefficient (f g) (P.group g v)) μ :=
  integrable_vectorIntegrand P.coefficient (fun g => P.group g) P.continuous_orbit μ f v

/-- The integrated form on compactly supported coefficient functions, defined by vector
integration rather than operator-valued Bochner integration. -/
def integratedOperator : C_c(G, A) →ₗ[ℂ] (H →L[ℂ] H) :=
  vectorIntegratedOperator P.coefficient (fun g => P.group g) P.continuous_orbit
    (fun g v => (P.isUnitary.norm_map g v).le) μ

/-- The defining vector formula for the integrated form. -/
theorem integratedOperator_apply (f : C_c(G, A)) (v : H) :
    P.integratedOperator μ f v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ :=
  vectorIntegratedOperator_apply f v

/-- The integrated form is bounded by the coefficient function's L¹ norm. -/
theorem norm_integratedOperator_le (f : C_c(G, A)) :
    ‖P.integratedOperator μ f‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  norm_vectorIntegratedOperator_le f

/-- Matrix coefficients can be computed by integrating vector matrix coefficients. -/
theorem inner_integratedOperator_apply (f : C_c(G, A)) (w v : H) :
    ⟪w, P.integratedOperator μ f v⟫_ℂ =
      ∫ g, ⟪w, P.coefficient (f g) (P.group g v)⟫_ℂ ∂μ :=
  inner_vectorIntegratedOperator_apply f w v

/-- A coefficient on the right moves inside the integral with the action twist. -/
theorem integratedOperator_coefficient_apply (f : C_c(G, A)) (a : A) (v : H) :
    P.integratedOperator μ f (P.coefficient a v) =
      ∫ g, P.coefficient (f g * α g a) (P.group g v) ∂μ := by
  rw [integratedOperator_apply]
  simp_rw [P.covariance, map_mul, mul_apply_eq_comp]

/-- The integrated form turns left multiplication by a coefficient into the coefficient
representation: `(π ⋊ U)(a • f) = π(a) (π ⋊ U)(f)`. -/
@[simp]
theorem integratedOperator_smul (a : A) (f : C_c(G, A)) :
    P.integratedOperator μ (a • f) = P.coefficient a * P.integratedOperator μ f :=
  vectorIntegratedOperator_smul a f

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- Vector evaluation of the coefficient representation commutes with Bochner integration. -/
theorem integral_coefficient_apply {X : Type*} [MeasurableSpace X] {ν : Measure X} {F : X → A}
    (hF : Integrable F ν) (w : H) :
    ∫ x, P.coefficient (F x) w ∂ν = P.coefficient (∫ x, F x ∂ν) w :=
  integral_representation_apply P.coefficient hF w

section Convolution

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form of a covariant pair is multiplicative for twisted convolution with respect
to a left-invariant measure: `(π ⋊ U) (f ⋆ g) = (π ⋊ U) f * (π ⋊ U) g`. -/
@[simp]
theorem integratedOperator_convolution (f g : C_c(G, A)) :
    P.integratedOperator μ (α.convolution μ f g) =
      P.integratedOperator μ f * P.integratedOperator μ g := by
  ext v
  -- The integrand on `G × G` obtained by expanding the twisted convolution.
  set Ψ : G → G → H := fun s r => P.coefficient (f r * α r (g (r⁻¹ * s))) (P.group s v)
  have hcont : Continuous (Function.uncurry Ψ) := by
    rw [Function.uncurry_def]
    exact ((map_continuous P.coefficient).comp (by fun_prop)).clm_apply
      ((P.continuous_orbit v).comp continuous_fst)
  have hsupp : HasCompactSupport (Function.uncurry Ψ) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
      fun s r h => ⟨subset_tsupport _ fun hf => h (by simp [Ψ, hf]),
        subset_tsupport _ fun hg => h (by simp [Ψ, hg])⟩
  calc P.integratedOperator μ (α.convolution μ f g) v
      = ∫ s, ∫ r, Ψ s r ∂μ ∂μ := by
        rw [integratedOperator_apply]
        congr 1 with s
        rw [convolution_apply, ← P.integral_coefficient_apply (α.integrable_integrand f g μ s)]
    _ = ∫ r, ∫ s, Ψ s r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hcont hsupp
    _ = ∫ r, (P.coefficient (f r) * P.group r) (P.integratedOperator μ g v) ∂μ := by
        congr 1 with r
        -- Substitute `s ↦ r * s`, then use covariance to pull `π (f r) * U r` out of the integral.
        rw [← integral_mul_left_eq_self (Ψ · r) r, integratedOperator_apply,
          ← ContinuousLinearMap.integral_comp_comm _ (P.integrable_integrand μ g v)]
        congr 1 with t
        simp [Ψ, map_mul, P.covariance]
    _ = (P.integratedOperator μ f * P.integratedOperator μ g) v := by
        simp [integratedOperator_apply]

/-- The integrated form turns the twisted left translation into the group representation:
`(π ⋊ U)(r • f) = U_r (π ⋊ U)(f)`. -/
@[simp]
theorem integratedOperator_translate (r : G) (f : C_c(G, A)) :
    P.integratedOperator μ (α.translate r f) = P.group r * P.integratedOperator μ f := by
  ext v
  rw [mul_apply_eq_comp, integratedOperator_apply, integratedOperator_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (P.integrable_integrand μ f v),
    ← integral_mul_left_eq_self _ r]
  -- After substituting `s ↦ r * s`, the integrands agree by covariance.
  congr 1 with s
  simp [P.covariance, map_mul]

end Convolution

section ScalarComparison

variable [R1Space G] [BorelSpace G] [μ.InnerRegularCompactLTTop]

/-- Use the original measurable structure on the additive tag for the scalar comparison.
Reducibility keeps the measure and its L¹ space unchanged. -/
@[reducible] local instance : MeasurableSpace (Additive G) := ‹MeasurableSpace G›
local instance : R1Space (Additive G) := ‹R1Space G›
local instance : BorelSpace (Additive G) := ‹BorelSpace G›
local instance : Measure.InnerRegularCompactLTTop (α := Additive G) μ :=
  inferInstanceAs (Measure.InnerRegularCompactLTTop (α := G) μ)

/-- On scalar multiples of a fixed coefficient, the integrated form factors through the existing
scalar L¹ integrated form. The tagging equivalence permits an arbitrary multiplicative group.
In particular, for the canonical scalar coefficient representation this recovers precisely the
scalar integrated operator. -/
theorem integratedOperator_eq_coefficient_mul_integratedOperatorL1
    (f : C_c(G, A)) (φ : C_c(G, ℂ)) (a : A) (hf : ∀ g, f g = φ g • a) :
    P.integratedOperator μ f = P.coefficient a *
      (P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).integratedOperatorL1
        (G := Additive G) (fun v => P.continuous_orbit v)
        (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le
        (μ : Measure (Additive G))
        (Integrable.toL1 (α := Additive G) (φ : Additive G → ℂ) φ.integrable) := by
  have hs (v : H) := ContRepresentation.integratedOperatorL1_toL1
    (G := Additive G)
    (π := P.group.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom)
    (hcont := fun v => P.continuous_orbit v)
    (hbdd := (P.isUnitary.restrict (MulEquiv.multiplicativeAdditive G).toMonoidHom).exists_norm_le)
    (μ := (μ : Measure (Additive G)))
    (f := (φ : Additive G → ℂ)) φ.integrable v
  ext v
  have hi : Integrable (fun g => φ g • P.group g v) μ :=
    (φ.continuous.smul (P.continuous_orbit v)).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.smul_right)
  calc
    P.integratedOperator μ f v = P.coefficient a (∫ g, φ g • P.group g v ∂μ) := by
      rw [integratedOperator_apply, ← (P.coefficient a).integral_comp_comm hi]
      apply integral_congr_ae
      filter_upwards [] with g
      simp [hf, map_smul]
    -- The tagging equivalence leaves the vector integrand and measure unchanged.
    _ = _ := congrArg (P.coefficient a) (hs v).symm

end ScalarComparison

end CovariantRepresentation

end TauCeti.CStarAction
