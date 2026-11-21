/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Fourier coefficients of square-integrable functions on the unit cube

A square-integrable function on the unit cube `[0, 1]ᵈ` all of whose Fourier coefficients
`∫ exp (-2πi ⟨n, x⟩) g(x) dx`, `n ∈ ℤᵈ`, vanish is zero almost everywhere
(`TauCeti.UnitAddTorus.ae_eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero`); in two variables
this is `TauCeti.UnitAddTorus.ae_eq_zero_of_forall_setIntegral_cexp_mul_eq_zero`, for functions on
`[0, 1]² ⊆ ℝ × ℝ`. Equivalently, the exponentials `exp (2πi ⟨n, x⟩)` span a dense subspace of
`L²([0, 1]ᵈ)`. Mathlib proves the corresponding statement on the torus `UnitAddTorus d`, where the
exponentials form the Hilbert basis `UnitAddTorus.mFourierBasis`; the map
`x ↦ (equivIoc 1 0 (x i))ᵢ` identifies the torus with the half-open cube `(0, 1]ᵈ`, preserving
measure, and the half-open cube differs from the closed one by a null set.

This lets the completeness of Fourier series be used for functions given in coordinates on a
fundamental domain of a lattice, such as the sections of a flat line over a torus written in
lattice coordinates.
-/

public section

open MeasureTheory Set Complex
open scoped Real

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

-- Mathlib's Fourier basis `mFourierBasis` lives on `L²` for the product of the Haar probability
-- measures on the circle factors, given by this instance; use it here so that Parseval's identity
-- applies to the same measure.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {d : Type*}

/-- The half-open unit cube `(0, 1]ᵈ`, the image of `measurableEquivPiIoc 0`. -/
private theorem setOf_forall_mem_Ioc_eq_pi :
    {x : d → ℝ | ∀ i, x i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} =
      univ.pi fun _ ↦ Ioc (0 : ℝ) 1 := by
  ext x; simp

private theorem measurableSet_setOf_forall_mem_Ioc [Countable d] :
    MeasurableSet {x : d → ℝ | ∀ i, x i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} := by
  rw [setOf_forall_mem_Ioc_eq_pi]
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

/-- The coordinates of a point of the half-open cube, as a map to `d → ℝ`. -/
private theorem measurePreserving_subtype_coe_setOf_forall_mem_Ioc [Fintype d] :
    MeasurePreserving
      (Subtype.val : {x : d → ℝ // ∀ i, x i ∈ Ioc ((0 : d → ℝ) i) ((0 : d → ℝ) i + 1)} → d → ℝ)
      (Measure.comap Subtype.val volume)
      ((volume : Measure (d → ℝ)).restrict (univ.pi fun _ ↦ Ioc (0 : ℝ) 1)) := by
  rw [← setOf_forall_mem_Ioc_eq_pi]
  exact measurePreserving_subtypeVal measurableSet_setOf_forall_mem_Ioc

/-- The map from the torus to the half-open cube `(0, 1]ᵈ`, read in `d → ℝ`, is a measurable
embedding. -/
theorem measurableEmbedding_coe_measurableEquivPiIoc [Countable d] :
    MeasurableEmbedding fun x : UnitAddTorus d ↦ ((measurableEquivPiIoc 0 x : _) : d → ℝ) :=
  (MeasurableEmbedding.subtypeVal measurableSet_setOf_forall_mem_Ioc).comp
    (measurableEquivPiIoc 0).measurableEmbedding

variable [Fintype d]

/-- The map from the torus to the half-open cube `(0, 1]ᵈ`, read in `d → ℝ`, preserves measure
onto the closed unit cube. The torus carries the product of the Haar probability measures on its
circle factors, the measure on which Mathlib's `mFourierBasis` is defined. -/
theorem measurePreserving_coe_measurableEquivPiIoc :
    MeasurePreserving (fun x : UnitAddTorus d ↦ ((measurableEquivPiIoc 0 x : _) : d → ℝ)) volume
      ((volume : Measure (d → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1)) := by
  have h := measurePreserving_subtype_coe_setOf_forall_mem_Ioc.comp
    (measurePreserving_equivPiIoc (d := d) 0)
  have hae : (univ.pi fun _ : d ↦ Ioc (0 : ℝ) 1) =ᵐ[(volume : Measure (d → ℝ))]
      univ.pi fun _ ↦ Icc (0 : ℝ) 1 :=
    Measure.pi_Ioc_ae_eq_pi_Icc
  rwa [Measure.restrict_congr_set hae] at h

/-- **Fourier coefficients on the unit cube determine square-integrable functions.** If `g` is
square integrable on `[0, 1]ᵈ` and `∫ exp (-2πi ⟨n, x⟩) g(x) dx = 0` over `[0, 1]ᵈ` for every
`n ∈ ℤᵈ`, then `g` vanishes almost everywhere on `[0, 1]ᵈ`. Here `exp (-2πi ⟨n, x⟩)` is the
exponential monomial `mFourier (-n)` evaluated at the image of `x` in the torus. -/
theorem ae_eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero {g : (d → ℝ) → ℂ}
    (hg : MemLp g 2 ((volume : Measure (d → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1)))
    (h : ∀ n : d → ℤ, ∫ x in univ.pi fun _ ↦ Icc (0 : ℝ) 1,
      mFourier (-n) (fun i ↦ (x i : UnitAddCircle)) * g x = 0) :
    g =ᵐ[(volume : Measure (d → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1)] 0 := by
  set T := fun x : UnitAddTorus d ↦ ((measurableEquivPiIoc 0 x : _) : d → ℝ)
  have hT : MeasurePreserving T volume _ := measurePreserving_coe_measurableEquivPiIoc
  have hTe : MeasurableEmbedding T := measurableEmbedding_coe_measurableEquivPiIoc
  have hTx (x : UnitAddTorus d) : (fun i ↦ (T x i : UnitAddCircle)) = x := by
    ext i; simp [T]
  -- Transported to the torus, `g` has vanishing Fourier coefficients.
  have hG := hg.comp_measurePreserving hT
  have hcoeff (n : d → ℤ) : mFourierCoeff (hG.toLp (g ∘ T)) n = 0 := by
    rw [← h n, ← hT.integral_comp hTe]
    refine integral_congr_ae ?_
    filter_upwards [hG.coeFn_toLp] with x hx
    rw [hx, hTx, smul_eq_mul, Function.comp_apply]
  -- By Parseval's identity, `g ∘ T`, and hence `g`, has zero `L²` norm.
  have hzero : ∫ x, ‖(g ∘ T) x‖ ^ 2 = 0 := by
    have hsum := hasSum_sq_mFourierCoeff (hG.toLp (g ∘ T))
    simp only [hcoeff, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsum
    rw [hasSum_zero.unique hsum]
    exact integral_congr_ae (by filter_upwards [hG.coeFn_toLp] with x hx; rw [hx])
  rw [Function.comp_def, hT.integral_comp hTe (fun y ↦ ‖g y‖ ^ 2)] at hzero
  have hint : Integrable (fun y ↦ ‖g y‖ ^ 2)
      ((volume : Measure (d → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1)) :=
    hg.integrable_norm_pow two_ne_zero
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun y ↦ by positivity) hint).1 hzero] with y hy
  simpa using hy

/-- **Fourier coefficients on the unit square determine square-integrable functions.** If `g` is
square integrable on `[0, 1]² ⊆ ℝ × ℝ` and `∫ exp (-2πi (n₁ s + n₂ t)) g(s, t) = 0` over `[0, 1]²`
for all integers `n₁`, `n₂`, then `g` vanishes almost everywhere on `[0, 1]²`. -/
theorem ae_eq_zero_of_forall_setIntegral_cexp_mul_eq_zero {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (h : ∀ n₁ n₂ : ℤ, ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      cexp (-(2 * π * I * (n₁ * p.1 + n₂ * p.2))) * g p = 0) :
    g =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)] 0 := by
  set e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have hpre : e ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
    ext x
    simp only [e, mem_preimage, MeasurableEquiv.finTwoArrow_apply, mem_prod, mem_univ_pi,
      Fin.forall_fin_two]
  have he : MeasurePreserving e ((volume : Measure (Fin 2 → ℝ)).restrict
      (univ.pi fun _ ↦ Icc (0 : ℝ) 1))
      ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
    have h := (volume_preserving_finTwoArrow ℝ).restrict_preimage
      (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (measurableSet_Icc.prod measurableSet_Icc)
    rwa [hpre] at h
  have hge : (g ∘ e) =ᵐ[(volume : Measure (Fin 2 → ℝ)).restrict
      (univ.pi fun _ ↦ Icc (0 : ℝ) 1)] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero
      (hg.comp_measurePreserving he) fun n ↦ ?_
    rw [← h (n 0) (n 1), ← he.integral_comp' (fun p ↦
      cexp (-(2 * π * I * (n 0 * p.1 + n 1 * p.2))) * g p)]
    congr 1 with x
    simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
      Fin.prod_univ_two, Function.comp_apply, e, MeasurableEquiv.finTwoArrow_apply]
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  rw [← he.map_eq, Filter.EventuallyEq, e.measurableEmbedding.ae_map_iff]
  exact hge

end TauCeti.UnitAddTorus
