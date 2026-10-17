/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Twisted convolution of compactly supported coefficient functions

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A` and a
measure `μ` on `G`, the twisted convolution of compactly supported continuous functions
`f g : C_c(G, A)` is

`(f ⋆ g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ`.

This is the multiplication of the convolution algebra whose completions are the crossed products
of the C⋆-dynamical system `(A, G, α)`. We show that `f ⋆ g` is again continuous and compactly
supported, with `support (f ⋆ g) ⊆ support f * support g`, and bundle the product as a
`ℂ`-bilinear map. For a left-invariant measure we prove associativity and the `L¹` estimate
`∫ ‖f ⋆ g‖ ≤ (∫ ‖f‖) * ∫ ‖g‖`.

Neither local compactness, separability nor σ-finiteness of `μ` is assumed: the measure only has
to be finite on compact sets. Continuity of the parametric integrals comes from
`continuousOn_integral_of_compact_support`, and the order of integration is exchanged with
`integral_integral_swap_of_hasCompactSupport`, a Fubini theorem for compactly supported continuous
functions which needs no σ-finiteness.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.

## Main definitions

* `TauCeti.CStarAction.convolution`: the twisted convolution as a `ℂ`-bilinear map on `C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.integral_comp_comm`: each automorphism of the action commutes with Bochner
  integrals.
* `TauCeti.CStarAction.support_convolution_subset`: the support of a twisted convolution lies in
  the product of the supports.
* `TauCeti.CStarAction.convolution_assoc`: twisted convolution is associative.
* `TauCeti.CStarAction.integral_norm_convolution_le`: the `L¹` norm is submultiplicative.
-/

public section

open MeasureTheory Function
open scoped CompactlySupported Pointwise

namespace TauCeti

namespace CStarAction

variable {G A : Type*} [Group G] [NonUnitalCStarAlgebra A]

/-! ### Support bookkeeping for twisted integrands -/

section Support

variable {E : Type*} [NormedAddCommGroup E] {F : G → G → E} {K L : Set G}

/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L` has its parametric
integral `s ↦ ∫ r, F s r` supported in `K * L`. -/
private theorem support_integral_subset [NormedSpace ℝ E] [MeasurableSpace G] (μ : Measure G)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    support (fun s => ∫ r, F s r ∂μ) ⊆ K * L := by
  intro s hs
  by_contra h
  refine hs (integral_eq_zero_of_ae (.of_forall fun r => ?_))
  by_contra hr
  obtain ⟨hrK, hrL⟩ := hF s r hr
  exact h ⟨r, hrK, r⁻¹ * s, hrL, mul_inv_cancel_left r s⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A two-variable integrand which vanishes unless `r ∈ K` and `r⁻¹ * s ∈ L`, for compact `K`
and `L`, is compactly supported on `G × G`. -/
private theorem hasCompactSupport_uncurry (hK : IsCompact K) (hL : IsCompact L)
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) : HasCompactSupport (uncurry F) := by
  refine ((hK.mul hL).prod hK).closure_of_subset fun p hp => ?_
  obtain ⟨hrK, hrL⟩ := hF p.1 p.2 hp
  exact ⟨⟨p.2, hrK, p.2⁻¹ * p.1, hrL, mul_inv_cancel_left p.2 p.1⟩, hrK⟩

/-- The parametric integral of a continuous integrand which vanishes unless `r ∈ K` and
`r⁻¹ * s ∈ L`, for compact `K` and `L`, is continuous with compact support. -/
private theorem continuous_integral_and_hasCompactSupport [NormedSpace ℝ E] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (hK : IsCompact K)
    (hL : IsCompact L) (hcont : Continuous (uncurry F))
    (hF : ∀ s r, F s r ≠ 0 → r ∈ K ∧ r⁻¹ * s ∈ L) :
    Continuous (fun s => ∫ r, F s r ∂μ) ∧ HasCompactSupport (fun s => ∫ r, F s r ∂μ) :=
  ⟨continuousOn_univ.mp <| continuousOn_integral_of_compact_support hK hcont.continuousOn
      fun s r _ hr => by_contra fun h => hr (hF s r h).1,
    (hK.mul hL).closure_of_subset (support_integral_subset μ hF)⟩

end Support

variable [TopologicalSpace G]

/-- Each automorphism of a C⋆-action commutes with Bochner integrals. No integrability is needed,
since the automorphism is a linear isometry. -/
theorem integral_comp_comm (α : CStarAction G A) {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (g : G) (F : X → A) : ∫ x, α g (F x) ∂ν = α g (∫ x, F x ∂ν) :=
  LinearIsometry.integral_comp_comm
    { toLinearMap := (α g : A →ₗ[ℂ] A)
      norm_map' := α.norm_apply g } F

/-! ### The twisted integrand -/

section Integrand

variable (α : CStarAction G A) (f g : C_c(G, A))

/-- The twisted integrand `(s, r) ↦ f r * α r (g (r⁻¹ * s))` vanishes unless `r ∈ support f`
and `r⁻¹ * s ∈ support g`. -/
private theorem mem_support_of_integrand_ne_zero {s r : G}
    (hsr : f r * α r (g (r⁻¹ * s)) ≠ 0) : r ∈ support f ∧ r⁻¹ * s ∈ support g := by
  refine ⟨fun hf => hsr (by simp [show f r = 0 from hf]), fun hg => hsr ?_⟩
  simp [show g (r⁻¹ * s) = 0 from hg]

private theorem mem_tsupport_of_integrand_ne_zero {s r : G}
    (hsr : f r * α r (g (r⁻¹ * s)) ≠ 0) : r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
  (mem_support_of_integrand_ne_zero α f g hsr).imp (subset_tsupport _ ·) (subset_tsupport _ ·)

variable [IsTopologicalGroup G]

private theorem continuous_integrand :
    Continuous (uncurry fun s r => f r * α r (g (r⁻¹ * s))) := by
  rw [uncurry_def]
  fun_prop

private theorem integrable_integrand [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (s : G) : Integrable (fun r => f r * α r (g (r⁻¹ * s))) μ :=
  ((continuous_integrand α f g).comp (.prodMk_right s)).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mono' fun _ hr => (mem_tsupport_of_integrand_ne_zero α f g hr).1)

end Integrand

/-! ### The twisted convolution -/

variable [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (α : CStarAction G A) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (f g h : C_c(G, A))

/-- The twisted convolution of two compactly supported coefficient functions, before bundling. -/
private noncomputable def convolutionAux : C_c(G, A) where
  toFun s := ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ
  continuous_toFun :=
    (continuous_integral_and_hasCompactSupport μ f.hasCompactSupport g.hasCompactSupport
      (continuous_integrand α f g) fun _ _ => mem_tsupport_of_integrand_ne_zero α f g).1
  hasCompactSupport' :=
    (continuous_integral_and_hasCompactSupport μ f.hasCompactSupport g.hasCompactSupport
      (continuous_integrand α f g) fun _ _ => mem_tsupport_of_integrand_ne_zero α f g).2

/-- The twisted convolution `(f ⋆ g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ` on `C_c(G, A)`, as a
`ℂ`-bilinear map. -/
noncomputable def convolution : C_c(G, A) →ₗ[ℂ] C_c(G, A) →ₗ[ℂ] C_c(G, A) :=
  LinearMap.mk₂ ℂ (convolutionAux α μ)
    (fun f₁ f₂ g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
        CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_integrand α f₁ g μ s) (integrable_integrand α f₂ g μ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
        CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_mul_assoc]
      exact integral_smul c _)
    (fun f g₁ g₂ => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
        CompactlySupportedContinuousMap.coe_add, Pi.add_apply, map_add, mul_add]
      exact integral_add (integrable_integrand α f g₁ μ s) (integrable_integrand α f g₂ μ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
        CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, map_smul, mul_smul_comm]
      exact integral_smul c _)

@[simp]
theorem convolution_apply (s : G) :
    α.convolution μ f g s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (rfl)

/-- A twisted convolution is supported in the product of the supports. -/
theorem support_convolution_subset : support (α.convolution μ f g) ⊆ support f * support g :=
  support_integral_subset μ fun _ _ => mem_support_of_integrand_ne_zero α f g

/-! ### Left-invariant measures -/

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Twisted convolution with respect to a left-invariant measure is associative. -/
theorem convolution_assoc :
    α.convolution μ (α.convolution μ f g) h = α.convolution μ f (α.convolution μ g h) := by
  ext s
  simp only [convolution_apply]
  calc ∫ t, (∫ r, f r * α r (g (r⁻¹ * t)) ∂μ) * α t (h (t⁻¹ * s)) ∂μ
      = ∫ t, ∫ r, f r * α r (g (r⁻¹ * t)) * α t (h (t⁻¹ * s)) ∂μ ∂μ := by
        congr 1 with t
        exact (integral_mul_const_of_integrable (integrable_integrand α f g μ t)).symm
    _ = ∫ r, ∫ t, f r * α r (g (r⁻¹ * t)) * α t (h (t⁻¹ * s)) ∂μ ∂μ := by
        refine integral_integral_swap_of_hasCompactSupport ?_
          (hasCompactSupport_uncurry f.hasCompactSupport g.hasCompactSupport fun t r htr =>
            mem_tsupport_of_integrand_ne_zero α f g (left_ne_zero_of_mul htr))
        rw [uncurry_def]
        fun_prop
    _ = ∫ r, f r * α r (∫ t, g t * α t (h (t⁻¹ * (r⁻¹ * s))) ∂μ) ∂μ := by
        congr 1 with r
        -- Substitute `t ↦ r * t` in the inner integral, then pull out `f r` and `α r`.
        rw [← integral_comp_comm, ← integral_const_mul_of_integrable, ← integral_mul_left_eq_self
          (fun t => f r * α r (g (r⁻¹ * t)) * α t (h (t⁻¹ * s))) r]
        · simp [mul_apply, mul_assoc]
        · refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
            (g.hasCompactSupport.mono' fun t ht => subset_tsupport _ fun hg => ht ?_)
          simp [show g t = 0 from hg]

/-- The `L¹` norm is submultiplicative for twisted convolution with respect to a left-invariant
measure. -/
theorem integral_norm_convolution_le :
    ∫ s, ‖α.convolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
  -- Dominate pointwise by the scalar convolution `s ↦ ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖`, then use
  -- Fubini and left invariance.
  have hsupp : ∀ s r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ≠ 0 → r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
    fun s r hsr => ⟨subset_tsupport _ fun hf => hsr (by simp [show f r = 0 from hf]),
      subset_tsupport _ fun hg => hsr (by simp [show g (r⁻¹ * s) = 0 from hg])⟩
  have hcont : Continuous (uncurry fun s r => ‖f r‖ * ‖g (r⁻¹ * s)‖) := by
    rw [uncurry_def]
    fun_prop
  obtain ⟨hNcont, hNsupp⟩ := continuous_integral_and_hasCompactSupport μ f.hasCompactSupport
    g.hasCompactSupport hcont hsupp
  calc ∫ s, ‖α.convolution μ f g s‖ ∂μ
      ≤ ∫ s, ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ := by
        refine integral_mono ((α.convolution μ f g).continuous.norm.integrable_of_hasCompactSupport
          (α.convolution μ f g).hasCompactSupport.norm)
          (hNcont.integrable_of_hasCompactSupport hNsupp) fun s => ?_
        rw [convolution_apply]
        refine norm_integral_le_of_norm_le
          ((hcont.comp (.prodMk_right s)).integrable_of_hasCompactSupport
            (f.hasCompactSupport.mono' fun r hr => (hsupp s r hr).1)) (.of_forall fun r => ?_)
        simpa using norm_mul_le (f r) (α r (g (r⁻¹ * s)))
    _ = ∫ r, ∫ s, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hcont
          (hasCompactSupport_uncurry f.hasCompactSupport g.hasCompactSupport hsupp)
    _ = ∫ r, ‖f r‖ * ∫ s, ‖g s‖ ∂μ ∂μ := by
        congr 1 with r
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self (fun s => ‖g s‖) r⁻¹
    _ = (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := integral_mul_const _ _

end CStarAction

end TauCeti
