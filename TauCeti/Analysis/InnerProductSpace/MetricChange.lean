/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.GeometricMean

/-!
# Changing the inner product by an inverse square root

Let `E` be a real Hilbert space with inner product `⟪·, ·⟫`, and let `g` be a second metric on
`E`, given as a bounded symmetric bilinear form `g : E →L[ℝ] E →L[ℝ] ℝ`. Its Riesz operator
`H = continuousLinearMapOfBilin g` is the self-adjoint operator with `g u v = ⟪H u, v⟫`. It is
positive (`InnerProductSpace.isPositive_continuousLinearMapOfBilin`), and strictly positive,
that is positive and invertible, when `g` is positive definite on a finite-dimensional space
(`InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin`) or coercive on an arbitrary
one (`IsCoercive.isStrictlyPositive_continuousLinearMapOfBilin`).

The *metric transport* `ContinuousLinearMap.metricTransport g = H ^ (-1 / 2)` is the inverse
square root of `H`, formed with the continuous functional calculus. For strictly positive `H` it
is an isometry from `(E, ⟪·, ·⟫)` onto `(E, g)`:
`g (metricTransport g u) (metricTransport g v) = ⟪u, v⟫`
(`ContinuousLinearMap.apply_metricTransport_metricTransport`). In particular it carries every
`⟪·, ·⟫`-orthonormal frame to a `g`-orthonormal frame. Its inverse is the square root `√H`, which
carries `g`-orthonormal frames back: `⟪√H u, √H v⟫ = g u v`
(`ContinuousLinearMap.inner_sqrt_apply_sqrt_apply`).

Unlike an orthonormalization of a chosen basis, or a rescaled eigenbasis as in
`TauCeti.exists_continuousLinearEquiv_inner_map_map`, the metric transport involves no choice.
It is the unique positive operator `S` with `S * H * S = 1`
(`ContinuousLinearMap.eq_metricTransport_iff`), it commutes with every isometric change of
coordinates (`ContinuousLinearMap.metricTransport_bilinearComp`), and it depends continuously on
the metric (`Continuous.metricTransport`). These are the properties needed to compare the
orthonormal frames of two metrics on a vector bundle chart by chart.

## Main declarations

* `ContinuousLinearMap.metricTransport`: the inverse square root of the Riesz operator of `g`.
* `ContinuousLinearMap.apply_metricTransport_metricTransport`: it is an isometry from the inner
  product to `g`.
* `ContinuousLinearMap.metricTransport_mul_sqrt`, `ContinuousLinearMap.sqrt_mul_metricTransport`:
  its inverse is `√H`.
* `ContinuousLinearMap.eq_metricTransport_iff`: its characterization as the positive solution of
  `S * H * S = 1`.
* `ContinuousLinearMap.metricTransport_bilinearComp`: naturality under linear isometric
  equivalences.
* `Continuous.metricTransport`: continuous dependence on a parameter.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §2, for Euclidean metrics on
  vector bundles and their orthonormal frames.
-/

public section

open scoped InnerProductSpace
open InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {g : E →L[ℝ] E →L[ℝ] ℝ}

/-! ### The Riesz operator of a metric -/

namespace InnerProductSpace

open ContinuousLinearMap

/-- The Riesz operator of a symmetric bilinear form with nonnegative diagonal is positive. -/
theorem isPositive_continuousLinearMapOfBilin (hsymm : ∀ u v, g u v = g v u)
    (hnonneg : ∀ v, 0 ≤ g v v) : (continuousLinearMapOfBilin g).IsPositive := by
  refine (isPositive_iff _).2 ⟨fun u v => ?_, fun v => ?_⟩
  · simp only [coe_coe]
    rw [continuousLinearMapOfBilin_apply, real_inner_comm, continuousLinearMapOfBilin_apply, hsymm]
  · simpa using hnonneg v

/-- On a finite-dimensional space, the Riesz operator of a positive-definite symmetric bilinear
form is strictly positive. -/
theorem isStrictlyPositive_continuousLinearMapOfBilin [FiniteDimensional ℝ E]
    (hsymm : ∀ u v, g u v = g v u) (hpos : ∀ v ≠ 0, 0 < g v v) :
    IsStrictlyPositive (continuousLinearMapOfBilin g) := by
  refine IsUnit.isStrictlyPositive ?_ (nonneg_iff_isPositive.2 <|
    isPositive_continuousLinearMapOfBilin hsymm fun v => ?_)
  · have hinj : Function.Injective (continuousLinearMapOfBilin g) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      by_contra h
      have := hpos v h
      rw [← continuousLinearMapOfBilin_apply, hv, inner_zero_left] at this
      exact this.false
    exact isUnit_iff_bijective.2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hpos v hv).le

/-- Transporting a bilinear form along a linear isometric equivalence `A` conjugates its Riesz
operator by `A`. -/
@[simp]
theorem continuousLinearMapOfBilin_bilinearComp (A : E ≃ₗᵢ[ℝ] F) :
    continuousLinearMapOfBilin (g.bilinearComp ((A : E ≃L[ℝ] F).symm : F →L[ℝ] E)
      ((A : E ≃L[ℝ] F).symm : F →L[ℝ] E)) =
      A.conjStarAlgEquiv (continuousLinearMapOfBilin g) := by
  ext u
  refine ext_inner_right ℝ fun w => ?_
  rw [continuousLinearMapOfBilin_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    ← A.symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply, continuousLinearMapOfBilin_apply,
    bilinearComp_apply]
  simp

end InnerProductSpace

/-- The Riesz operator of a coercive symmetric bilinear form is strictly positive: it is
invertible by the Lax–Milgram theorem. -/
theorem IsCoercive.isStrictlyPositive_continuousLinearMapOfBilin (hg : IsCoercive g)
    (hsymm : ∀ u v, g u v = g v u) : IsStrictlyPositive (continuousLinearMapOfBilin g) := by
  refine IsUnit.isStrictlyPositive (ContinuousLinearMap.isUnit_iff_bijective.2
    ⟨LinearMap.ker_eq_bot.1 hg.ker_eq_bot, LinearMap.range_eq_top.1 hg.range_eq_top⟩)
    (ContinuousLinearMap.nonneg_iff_isPositive.2 <|
      isPositive_continuousLinearMapOfBilin hsymm fun v => ?_)
  obtain ⟨C, hC, hcoe⟩ := hg
  exact le_trans (by positivity) (hcoe v)

/-! ### The metric transport -/

namespace ContinuousLinearMap

/-- The *metric transport* of a bilinear form `g`: the inverse square root `H ^ (-1 / 2)` of the
Riesz operator `H = continuousLinearMapOfBilin g`, which satisfies `g u v = ⟪H u, v⟫`. When `H`
is strictly positive, it is an isometry from the inner product of `E` to `g`
(`ContinuousLinearMap.apply_metricTransport_metricTransport`). -/
noncomputable def metricTransport (g : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  continuousLinearMapOfBilin g ^ (-(1 / 2) : ℝ)

theorem metricTransport_def (g : E →L[ℝ] E →L[ℝ] ℝ) :
    g.metricTransport = continuousLinearMapOfBilin g ^ (-(1 / 2) : ℝ) := (rfl)

theorem metricTransport_nonneg (g : E →L[ℝ] E →L[ℝ] ℝ) : 0 ≤ g.metricTransport :=
  CFC.rpow_nonneg

theorem isSelfAdjoint_metricTransport (g : E →L[ℝ] E →L[ℝ] ℝ) :
    IsSelfAdjoint g.metricTransport :=
  g.metricTransport_nonneg.isSelfAdjoint

/-- The metric transport of the inner product itself is the identity. -/
@[simp]
theorem metricTransport_innerSL : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).metricTransport = 1 := by
  rw [metricTransport_def, continuousLinearMapOfBilin_innerSL, CFC.one_rpow]

section StrictlyPositive

variable (hg : IsStrictlyPositive (continuousLinearMapOfBilin g))
include hg

theorem isStrictlyPositive_metricTransport : IsStrictlyPositive g.metricTransport :=
  (hg.isUnit.cfcRpow _ hg.nonneg).isStrictlyPositive g.metricTransport_nonneg

/-- The metric transport `T = H ^ (-1 / 2)` of `g` solves `T * H * T = 1`. -/
theorem metricTransport_mul_mul_metricTransport :
    g.metricTransport * continuousLinearMapOfBilin g * g.metricTransport = 1 := by
  set H := continuousLinearMapOfBilin g
  calc H ^ (-(1 / 2) : ℝ) * H * H ^ (-(1 / 2) : ℝ)
      = H ^ (-(1 / 2) : ℝ) * H ^ (1 : ℝ) * H ^ (-(1 / 2) : ℝ) := by rw [CFC.rpow_one H hg.nonneg]
    _ = H ^ ((-(1 / 2) + 1 + -(1 / 2)) : ℝ) := by
        rw [CFC.rpow_add hg.isUnit, CFC.rpow_add hg.isUnit]
    _ = 1 := by norm_num [CFC.rpow_zero H hg.nonneg]

/-- The metric transport is an isometry from the inner product of `E` to the metric `g`. In
particular it carries every orthonormal family of `E` to a `g`-orthonormal family. -/
theorem apply_metricTransport_metricTransport (u v : E) :
    g (g.metricTransport u) (g.metricTransport v) = ⟪u, v⟫_ℝ := by
  rw [← continuousLinearMapOfBilin_apply,
    ← (nonneg_iff_isPositive.1 g.metricTransport_nonneg).inner_left_eq_inner_right]
  simpa using congr(⟪$(metricTransport_mul_mul_metricTransport hg) u, v⟫_ℝ)

/-- The square root of the Riesz operator is a left inverse of the metric transport. -/
theorem sqrt_mul_metricTransport :
    CFC.sqrt (continuousLinearMapOfBilin g) * g.metricTransport = 1 := by
  rw [CFC.sqrt_eq_rpow, metricTransport_def, one_div]
  exact CFC.rpow_mul_rpow_neg _ hg

/-- The square root of the Riesz operator is a right inverse of the metric transport. -/
theorem metricTransport_mul_sqrt :
    g.metricTransport * CFC.sqrt (continuousLinearMapOfBilin g) = 1 := by
  rw [CFC.sqrt_eq_rpow, metricTransport_def, one_div]
  exact CFC.rpow_neg_mul_rpow _ hg

/-- The metric transport of `g` is the unique positive operator `S` with `S * H * S = 1`, where
`H` is the Riesz operator of `g`. -/
theorem eq_metricTransport_iff {S : E →L[ℝ] E} (hS : 0 ≤ S) :
    S = g.metricTransport ↔ S * continuousLinearMapOfBilin g * S = 1 := by
  refine ⟨fun h => h ▸ metricTransport_mul_mul_metricTransport hg, fun h => ?_⟩
  rw [TauCeti.eq_geometricMean_ringInverse_of_mul_mul h hg hS,
    TauCeti.eq_geometricMean_ringInverse_of_mul_mul (metricTransport_mul_mul_metricTransport hg) hg
      g.metricTransport_nonneg]

end StrictlyPositive

/-- The inverse transport: the square root of the Riesz operator of `g` is an isometry from `g`
to the inner product of `E`. -/
theorem inner_sqrt_apply_sqrt_apply (hsymm : ∀ u v, g u v = g v u) (hnonneg : ∀ v, 0 ≤ g v v)
    (u v : E) :
    ⟪CFC.sqrt (continuousLinearMapOfBilin g) u, CFC.sqrt (continuousLinearMapOfBilin g) v⟫_ℝ =
      g u v := by
  set H := continuousLinearMapOfBilin g with hHdef
  have hH : 0 ≤ H := nonneg_iff_isPositive.2 (isPositive_continuousLinearMapOfBilin hsymm hnonneg)
  have h : CFC.sqrt H (CFC.sqrt H v) = H v := by
    rw [← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self H hH]
  rw [(nonneg_iff_isPositive.1 (CFC.sqrt_nonneg H)).inner_left_eq_inner_right, h, real_inner_comm,
    hHdef, continuousLinearMapOfBilin_apply, hsymm]

/-! ### Naturality and continuity -/

/-- The metric transport commutes with linear isometric equivalences: transporting the metric `g`
along `A` conjugates its metric transport by `A`. -/
@[simp]
theorem metricTransport_bilinearComp (A : E ≃ₗᵢ[ℝ] F) :
    (g.bilinearComp ((A : E ≃L[ℝ] F).symm : F →L[ℝ] E)
      ((A : E ≃L[ℝ] F).symm : F →L[ℝ] E)).metricTransport =
      A.conjStarAlgEquiv g.metricTransport := by
  rw [metricTransport_def, metricTransport_def, continuousLinearMapOfBilin_bilinearComp]
  by_cases h : 0 ≤ continuousLinearMapOfBilin g
  · rw [CFC.rpow_eq_cfc_real h, CFC.rpow_eq_cfc_real (map_nonneg _ h),
      cfc_eq_cfc_transfer A.conjStarAlgEquiv
        A.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous
        (p := IsSelfAdjoint) (q := IsSelfAdjoint)
        (fun x => ⟨fun hx => hx.map _, fun hx => by
          simpa only [StarAlgEquiv.symm_apply_apply] using hx.map A.conjStarAlgEquiv.symm⟩),
      StarAlgEquiv.symm_apply_apply]
  · rw [CFC.rpow_def, CFC.rpow_def, cfc_apply_of_not_predicate _ h,
      cfc_apply_of_not_predicate _ fun h' => h ?_, map_zero]
    rwa [← map_zero A.conjStarAlgEquiv, map_le_map_iff] at h'

/-- The metric transport depends continuously on the metric, along continuous families of
metrics whose Riesz operators are strictly positive. -/
theorem _root_.Continuous.metricTransport {X : Type*} [TopologicalSpace X]
    {g : X → E →L[ℝ] E →L[ℝ] ℝ} (hg : Continuous g)
    (hpos : ∀ x, IsStrictlyPositive (continuousLinearMapOfBilin (g x))) :
    Continuous fun x => (g x).metricTransport := by
  have h : (fun x => (g x).metricTransport) =
      fun x => cfc (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (continuousLinearMapOfBilin (g x)) :=
    funext fun x => CFC.rpow_eq_cfc_real (hpos x).nonneg
  rw [h]
  -- The spectra all lie in the open half-line `t > 0`, where `t ^ (-1 / 2)` is continuous.
  exact Continuous.cfc_of_mem_nhdsSet _ (isOpen_Ioi.mem_nhdsSet.2 <|
    Set.iUnion_subset fun x t ht => (hpos x).spectrum_pos ht)
    (continuous_continuousLinearMapOfBilin.comp hg) (fun x => (hpos x).isSelfAdjoint)
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).continuousWithinAt

end ContinuousLinearMap
