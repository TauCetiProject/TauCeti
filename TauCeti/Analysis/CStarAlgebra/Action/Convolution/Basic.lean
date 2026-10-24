/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Basic
public import TauCeti.MeasureTheory.Group.ConvolutionSupport
public import TauCeti.MeasureTheory.Integral.Bochner.Set
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

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-! ### The twisted integrand -/

section Integrand

variable (α : CStarAction G A) (f g : C_c(G, A))

/-- The twisted integrand `(s, r) ↦ f r * α r (g (r⁻¹ * s))` vanishes unless `r ∈ support f`
and `r⁻¹ * s ∈ support g`. -/
private theorem mem_support_of_integrand_ne_zero {s r : G}
    (hsr : f r * α r (g (r⁻¹ * s)) ≠ 0) : r ∈ support f ∧ r⁻¹ * s ∈ support g :=
  ⟨mem_support.2 fun hf => hsr (by simp [hf]), mem_support.2 fun hg => hsr (by simp [hg])⟩

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
  continuous_toFun := continuous_integral_of_compact_support μ f.hasCompactSupport
    (continuous_integrand α f g) fun _ _ h => (mem_tsupport_of_integrand_ne_zero α f g h).1
  hasCompactSupport' := hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport
    g.hasCompactSupport fun _ _ => mem_tsupport_of_integrand_ne_zero α f g

private theorem convolutionAux_apply (s : G) :
    convolutionAux α μ f g s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  rfl

/-- The twisted convolution `(f ⋆ g) s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ` on `C_c(G, A)`, as a
`ℂ`-bilinear map. -/
noncomputable def convolution : C_c(G, A) →ₗ[ℂ] C_c(G, A) →ₗ[ℂ] C_c(G, A) :=
  LinearMap.mk₂ ℂ (convolutionAux α μ)
    (fun f₁ f₂ g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
        add_mul]
      exact integral_add (integrable_integrand α f₁ g μ s) (integrable_integrand α f₂ g μ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
        smul_mul_assoc]
      exact integral_smul c _)
    (fun f g₁ g₂ => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
        map_add, mul_add]
      exact integral_add (integrable_integrand α f g₁ μ s) (integrable_integrand α f g₂ μ s))
    (fun c f g => CompactlySupportedContinuousMap.ext fun s => by
      simp only [convolutionAux_apply, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
        map_smul, mul_smul_comm]
      exact integral_smul c _)

@[simp]
theorem convolution_apply (s : G) :
    α.convolution μ f g s = ∫ r, f r * α r (g (r⁻¹ * s)) ∂μ :=
  (rfl)

/-- A twisted convolution is supported in the product of the supports. -/
theorem support_convolution_subset : support (α.convolution μ f g) ⊆ support f * support g :=
  support_integral_subset_mul μ fun _ _ => mem_support_of_integrand_ne_zero α f g

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
          (hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
            fun t r htr =>
            mem_tsupport_of_integrand_ne_zero α f g (left_ne_zero_of_mul htr))
        rw [uncurry_def]
        fun_prop
    _ = ∫ r, f r * α r (∫ t, g t * α t (h (t⁻¹ * (r⁻¹ * s))) ∂μ) ∂μ := by
        congr 1 with r
        -- Substitute `t ↦ r * t` in the inner integral, then pull out `f r` and `α r`.
        rw [← integral_comp_comm, ← integral_const_mul_of_integrable, ← integral_mul_left_eq_self
          (fun t => f r * α r (g (r⁻¹ * t)) * α t (h (t⁻¹ * s))) r]
        · simp [mul_apply, mul_assoc]
        · simpa using
            (α.toContinuousLinearMap r).integrable_comp (integrable_integrand α g h μ (r⁻¹ * s))

/-- The `L¹` norm is submultiplicative for twisted convolution with respect to a left-invariant
measure. -/
theorem integral_norm_convolution_le :
    ∫ s, ‖α.convolution μ f g s‖ ∂μ ≤ (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := by
  -- Dominate pointwise by the scalar convolution `s ↦ ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖`, then use
  -- Fubini and left invariance.
  have hsupp : ∀ s r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ≠ 0 → r ∈ tsupport f ∧ r⁻¹ * s ∈ tsupport g :=
    fun s r hsr => ⟨subset_tsupport _ (mem_support.2 fun hf => hsr (by simp [hf])),
      subset_tsupport _ (mem_support.2 fun hg => hsr (by simp [hg]))⟩
  have hcont : Continuous (uncurry fun s r => ‖f r‖ * ‖g (r⁻¹ * s)‖) := by
    rw [uncurry_def]
    fun_prop
  have hNcont := continuous_integral_of_compact_support μ f.hasCompactSupport hcont
    fun s r h => (hsupp s r h).1
  have hNsupp := hasCompactSupport_integral_of_inv_mul_mem μ f.hasCompactSupport
    g.hasCompactSupport hsupp
  calc ∫ s, ‖α.convolution μ f g s‖ ∂μ
      ≤ ∫ s, ∫ r, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ := by
        refine integral_mono ((α.convolution μ f g).continuous.norm.integrable_of_hasCompactSupport
          (α.convolution μ f g).hasCompactSupport.norm)
          (hNcont.integrable_of_hasCompactSupport hNsupp) fun s => ?_
        rw [convolution_apply]
        refine norm_integral_le_of_norm_le
          ((hcont.comp (.prodMk_right s)).integrable_of_hasCompactSupport
            (f.hasCompactSupport.mono' fun r hr => (hsupp s r hr).1)) (.of_forall fun r => ?_)
        simpa [StarAlgEquiv.norm_map] using norm_mul_le (f r) (α r (g (r⁻¹ * s)))
    _ = ∫ r, ∫ s, ‖f r‖ * ‖g (r⁻¹ * s)‖ ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hcont
          (hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport hsupp)
    _ = ∫ r, ‖f r‖ * ∫ s, ‖g s‖ ∂μ ∂μ := by
        congr 1 with r
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self (fun s => ‖g s‖) r⁻¹
    _ = (∫ s, ‖f s‖ ∂μ) * ∫ s, ‖g s‖ ∂μ := integral_mul_const _ _

end CStarAction

end TauCeti
