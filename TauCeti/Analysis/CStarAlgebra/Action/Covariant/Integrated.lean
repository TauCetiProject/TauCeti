/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Translate
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Basic
public import TauCeti.Analysis.CStarAlgebra.Representation.Integrated
public import TauCeti.RepresentationTheory.Continuous.Integrated.Basic

/-!
# Vector-valued integrated forms of covariant pairs

For a compactly supported continuous coefficient function `f`, the integrated form is the bounded
operator `v ↦ ∫ g, π (f g) (U g v)`, obtained by specializing
`NonUnitalStarAlgHom.integratedOperator` to `(P.coefficient, P.group)`. Integration is in the
Hilbert space, not in the operator-norm space: strong continuity of `U` does not imply norm
continuity. The operator depends linearly on `f` and has norm at most `∫ g, ‖f g‖`. No
separability, second countability, or σ-finiteness is needed. For the definition, the norm bound
and the covariance identity the measure need only be finite on compact sets; left invariance enters
only for multiplicativity under twisted convolution.

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

namespace TauCeti.CStarAction.CovariantRepresentation

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
  P.coefficient.continuous_integrand P.continuous_orbit f v

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The vector integrand vanishes outside the support of the coefficient function. -/
theorem hasCompactSupport_integrand (f : C_c(G, A)) (v : H) :
    HasCompactSupport fun g => P.coefficient (f g) (P.group g v) :=
  P.coefficient.hasCompactSupport_integrand (fun g => P.group g) f v

/-- Compact support makes every vector integrand integrable. -/
theorem integrable_integrand (f : C_c(G, A)) (v : H) :
    Integrable (fun g => P.coefficient (f g) (P.group g v)) μ :=
  P.coefficient.integrable_integrand P.continuous_orbit μ f v

/-- The integrated form on compactly supported coefficient functions, defined by vector
integration rather than operator-valued Bochner integration. -/
@[expose]
def integratedOperator : C_c(G, A) →ₗ[ℂ] (H →L[ℂ] H) :=
  P.coefficient.integratedOperator (fun g => P.group g) P.continuous_orbit
    P.isUnitary.exists_norm_le μ

/-- The defining vector formula for the integrated form. -/
theorem integratedOperator_apply (f : C_c(G, A)) (v : H) :
    P.integratedOperator μ f v = ∫ g, P.coefficient (f g) (P.group g v) ∂μ :=
  P.coefficient.integratedOperator_apply P.continuous_orbit P.isUnitary.exists_norm_le μ f v

/-- The integrated form is bounded by the coefficient function's L¹ norm. -/
theorem norm_integratedOperator_le (f : C_c(G, A)) :
    ‖P.integratedOperator μ f‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  simpa [integratedOperator] using P.coefficient.norm_integratedOperator_le P.continuous_orbit
    P.isUnitary.exists_norm_le μ P.isUnitary.norm_le_one f

/-- Matrix coefficients can be computed by integrating vector matrix coefficients. -/
theorem inner_integratedOperator_apply (f : C_c(G, A)) (w v : H) :
    ⟪w, P.integratedOperator μ f v⟫_ℂ =
      ∫ g, ⟪w, P.coefficient (f g) (P.group g v)⟫_ℂ ∂μ :=
  P.coefficient.inner_integratedOperator_apply P.continuous_orbit
    P.isUnitary.exists_norm_le μ f w v

/-- A coefficient on the right moves inside the integral with the action twist. -/
theorem integratedOperator_coefficient_apply (f : C_c(G, A)) (a : A) (v : H) :
    P.integratedOperator μ f (P.coefficient a v) =
      ∫ g, P.coefficient (f g * α g a) (P.group g v) ∂μ :=
  P.coefficient.integratedOperator_apply_apply P.continuous_orbit
    P.isUnitary.exists_norm_le μ (fun g => P.covariance g a v) f

/-- The integrated form turns left multiplication by a coefficient into the coefficient
representation: `(π ⋊ U)(a • f) = π(a) (π ⋊ U)(f)`. -/
@[simp]
theorem integratedOperator_smul (a : A) (f : C_c(G, A)) :
    P.integratedOperator μ (a • f) = P.coefficient a * P.integratedOperator μ f :=
  P.coefficient.integratedOperator_smul P.continuous_orbit P.isUnitary.exists_norm_le μ a f

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
      fun _ _ h => mem_tsupport_and_inv_mul_mem_tsupport h
        (by intro hf; simp [Ψ, hf]) (by intro hg; simp [Ψ, hg])
  calc P.integratedOperator μ (α.convolution μ f g) v
      = ∫ s, ∫ r, Ψ s r ∂μ ∂μ := by
        rw [integratedOperator_apply]
        congr 1 with s
        rw [convolution_apply,
          ← P.coefficient.integral_apply_apply (α.integrable_integrand f g μ s)]
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

end TauCeti.CStarAction.CovariantRepresentation
