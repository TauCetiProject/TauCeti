/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Regular
public import TauCeti.MeasureTheory.Measure.Count.Topology
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Matrix entries of discrete regular representations

For counting measure, the matrix entry of the integrated regular representation between
vectors supported at `s` and `r` is `ρ (α r⁻¹ (f (r * s⁻¹)))`. In particular every coefficient
of `f` is bounded by the regular operator norm when `ρ` is faithful. This is the estimate
that permits Fourier-coefficient maps to extend to the concrete regular crossed product.
No countability of the discrete group or nondegeneracy of `ρ` is needed.

The calculation uses `CovariantRepresentation.regular` and its vector integral, following
Dana Williams, *Crossed Products of C*-Algebras*, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The matrix entry between singleton-supported vectors in a discrete regular representation.
The singleton indicators have exactly the norms of `w` and `v`, respectively. -/
theorem inner_integratedOperator_regular_single (f : C_c(G, A)) (r s : G) (w v : H) :
    ⟪indicatorConstLp 2 (measurableSet_singleton r) (by simp) w,
      (regular α ρ Measure.count).integratedOperator Measure.count f
        (indicatorConstLp 2 (measurableSet_singleton s) (by simp) v)⟫_ℂ =
      ⟪w, ρ (α r⁻¹ (f (r * s⁻¹))) v⟫_ℂ := by
  classical
  let ξ : Lp H 2 (Measure.count : Measure G) :=
    indicatorConstLp 2 (measurableSet_singleton s) (by simp) v
  have hξ (x : G) : ξ x = if x = s then v else 0 := by
    simpa only [Set.indicator_apply, Set.mem_singleton_iff] using
      (Measure.ae_count_iff.mp (indicatorConstLp_coeFn (μ := Measure.count)
        (p := 2) (hs := measurableSet_singleton s) (hμs := by simp) (c := v)) x)
  have hentry (t : G) :
      ⟪indicatorConstLp 2 (measurableSet_singleton r) (by simp) w,
        (regular α ρ Measure.count).coefficient (f t)
          ((regular α ρ Measure.count).group t ξ)⟫_ℂ =
        ({r * s⁻¹} : Set G).indicator (fun _ => ⟪w, ρ (α r⁻¹ (f (r * s⁻¹))) v⟫_ℂ) t := by
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner, integral_singleton]
    have hc := Measure.ae_count_iff.mp (coeFn_regular_coefficient α ρ Measure.count (f t)
      ((regular α ρ Measure.count).group t ξ)) r
    have hg := Measure.ae_count_iff.mp (Measure.count.coeFn_leftRegular (𝕜 := ℂ) 2 t ξ) r
    have ht : t⁻¹ * r = s ↔ t = r * s⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq]
      exact eq_comm
    simp only [count_real_singleton, one_smul]
    rw [hc]
    simp only [regular_group, hg, hξ]
    by_cases h : t = r * s⁻¹
    · simp [h]
    · simp [h, ht]
  rw [integratedOperator_apply, ← integral_inner (integrable_integrand _ _ _ _)]
  trans ∫ t, ({r * s⁻¹} : Set G).indicator
    (fun _ => ⟪w, ρ (α r⁻¹ (f (r * s⁻¹))) v⟫_ℂ) t ∂Measure.count
  · exact integral_congr_ae (.of_forall hentry)
  · rw [integral_indicator (measurableSet_singleton _), integral_singleton]
    simp only [count_real_singleton, one_smul]

/-- Every represented Fourier coefficient is bounded by the integrated regular operator norm. -/
theorem norm_coefficient_le_norm_integratedOperator_regular (f : C_c(G, A)) (g : G) :
    ‖ρ (f g)‖ ≤ ‖(regular α ρ Measure.count).integratedOperator Measure.count f‖ := by
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg _) fun v w hv hw => ?_
  have h := inner_integratedOperator_regular_single α ρ f 1 g⁻¹ w v
  simp only [one_mul, inv_inv, inv_one, one_apply] at h
  have hnorm (s : G) (z : H) :
      ‖(indicatorConstLp 2 (measurableSet_singleton s) (by simp) z :
        Lp H 2 (Measure.count : Measure G))‖ = ‖z‖ := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [count_real_singleton, Real.one_rpow, mul_one]
  calc
    (⟪ρ (f g) v, w⟫_ℂ).re ≤ ‖⟪ρ (f g) v, w⟫_ℂ‖ := Complex.re_le_norm _
    _ = ‖⟪w, ρ (f g) v⟫_ℂ‖ := norm_inner_symm _ _
    _ ≤ ‖(regular α ρ Measure.count).integratedOperator Measure.count f‖ := by
      rw [← h]
      exact (norm_inner_le_norm _ _).trans (by
        simpa only [hnorm, hv, hw, mul_one, one_mul] using
          mul_le_mul_of_nonneg_left
            (((regular α ρ Measure.count).integratedOperator Measure.count f).le_opNorm
              (indicatorConstLp 2 (measurableSet_singleton g⁻¹) (by simp) v))
            (norm_nonneg (indicatorConstLp 2 (measurableSet_singleton (1 : G))
              (μ := Measure.count) (by simp) w)))

/-- For a faithful inducing representation, coefficient evaluation is contractive for the
regular norm, not just for the L¹ norm. -/
theorem norm_apply_le_norm_integratedOperator_regular (hρ : Function.Injective ρ)
    (f : C_c(G, A)) (g : G) :
    ‖f g‖ ≤ ‖(regular α ρ Measure.count).integratedOperator Measure.count f‖ := by
  rw [← NonUnitalStarAlgHom.norm_map ρ hρ (f g)]
  exact norm_coefficient_le_norm_integratedOperator_regular α ρ f g

end TauCeti.CStarAction.CovariantRepresentation
