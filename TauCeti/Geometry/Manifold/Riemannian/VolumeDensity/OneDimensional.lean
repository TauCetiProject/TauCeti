/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Null
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The Riemannian volume of a one-dimensional manifold

The Riemannian volume of a one-dimensional Riemannian manifold `M` is its arclength measure: in a
parametrization `γ` of a part of `M` by a real parameter, the Riemannian Jacobian of `γ` is the
speed `‖γ'‖`, so that the change of variables formula for the Riemannian volume reads
`∫ φ ∂vol = ∫ ‖γ' t‖ * φ (γ t) dt`.

Two kinds of parametrizations are treated. An arc is parametrized by a `C¹` partial diffeomorphism
from `ℝ` to `M`. A closed curve is parametrized by a periodic local diffeomorphism `γ : ℝ → M`
which is injective on the interior of a period interval. The remaining endpoint of the interval is
sent to a single point, which has volume zero, so `γ` carries the speed-weighted Lebesgue measure
on any period interval to the Riemannian volume on the range of `γ`. A diffeomorphism from
`AddCircle p` onto `M`, read on `ℝ`, is such a parametrization of all of `M`.

The model space of `M` is any one-dimensional real normed space, and `M` may have boundary.

## Main results

* `TauCeti.riemannianJacobian_singleton`: the Riemannian Jacobian of a curve with respect to the
  basis `1` of `ℝ` is its speed.
* `PartialDiffeomorph.map_withDensity_enorm_curveVelocity`: a `C¹` partial diffeomorphism from `ℝ`
  to `M` carries the speed-weighted Lebesgue measure on its source to the Riemannian volume on its
  target.
* `PartialDiffeomorph.setLIntegral_riemannianVolume_eq_enorm_curveVelocity_mul`: the
  corresponding formula for integrals over the target.
* `IsLocalDiffeomorph.map_withDensity_enorm_curveVelocity_of_periodic`: a periodic local
  diffeomorphism `γ : ℝ → M`, injective on the interior of a period interval, carries the
  speed-weighted Lebesgue measure on that interval to the Riemannian volume on its range.
* `IsLocalDiffeomorph.setIntegral_riemannianVolume_range_of_periodic`: the corresponding formula
  for Bochner integrals, as an interval integral over a period.
* `Diffeomorph.map_withDensity_enorm_curveVelocity_addCircle` and
  `Diffeomorph.integral_riemannianVolume_addCircle`: the two formulas for a diffeomorphism from
  `AddCircle p` onto `M`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

open Bundle MeasureTheory Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold

public noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian Jacobian of a curve with respect to the basis `1` of `ℝ` is its speed. -/
@[simp]
theorem riemannianJacobian_singleton {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]
    (γ : ℝ → M) (t : ℝ) :
    riemannianJacobian (I := I) (Module.Basis.singleton ι ℝ) γ t = ‖curveVelocity I γ t‖ := by
  rw [riemannianJacobian_unique, Module.Basis.singleton_apply, curveVelocity_apply]

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

/-! ### Arcs -/

/-- A `C¹` partial diffeomorphism `Φ` from `ℝ` to a one-dimensional Riemannian manifold carries
the Lebesgue measure on its source, weighted by the speed of `Φ`, to the Riemannian volume on its
target. -/
theorem _root_.PartialDiffeomorph.map_withDensity_enorm_curveVelocity
    (Φ : PartialDiffeomorph 𝓘(ℝ) I ℝ M 1) (hdim : Module.finrank ℝ E = 1) :
    Measure.map Φ ((volume.restrict Φ.source).withDensity fun t ↦ ‖curveVelocity I Φ t‖ₑ) =
      (riemannianVolume I M).restrict Φ.target := by
  simpa only [Module.Basis.addHaar_singleton, riemannianJacobian_singleton, ofReal_norm] using
    Φ.map_withDensity_riemannianJacobian (Module.Basis.singleton (Fin 1) ℝ)
      ((Module.finrank_self ℝ).trans hdim.symm)

/-- **Change of variables** over the target of a `C¹` partial diffeomorphism `Φ` from `ℝ` to a
one-dimensional Riemannian manifold: the integral of `φ` over the target against the Riemannian
volume is the integral of `φ ∘ Φ` over the source, weighted by the speed of `Φ`. The nonnegative
weight need not be measurable. -/
theorem _root_.PartialDiffeomorph.setLIntegral_riemannianVolume_eq_enorm_curveVelocity_mul
    (Φ : PartialDiffeomorph 𝓘(ℝ) I ℝ M 1) (hdim : Module.finrank ℝ E = 1) (φ : M → ℝ≥0∞) :
    ∫⁻ y in Φ.target, φ y ∂riemannianVolume I M =
      ∫⁻ t in Φ.source, ‖curveVelocity I Φ t‖ₑ * φ (Φ t) := by
  simpa only [Module.Basis.addHaar_singleton, riemannianJacobian_singleton, ofReal_norm] using
    Φ.setLIntegral_riemannianVolume_eq (Module.Basis.singleton (Fin 1) ℝ)
      ((Module.finrank_self ℝ).trans hdim.symm) φ

/-! ### Closed curves -/

/-- A `p`-periodic `C^n` local diffeomorphism `γ` from `ℝ` to a Riemannian manifold, with `n ≠ 0`,
which is injective on the open interval `(a, a + p)`, carries the Lebesgue measure on the period
interval `(a, a + p]`, weighted by the speed of `γ`, to the Riemannian volume on the range of
`γ`. -/
theorem _root_.IsLocalDiffeomorph.map_withDensity_enorm_curveVelocity_of_periodic
    {n : ℕ∞ω} {γ : ℝ → M} {p : ℝ} (hγ : IsLocalDiffeomorph 𝓘(ℝ) I n γ) (hn : n ≠ 0)
    (hper : γ.Periodic p) (hp : 0 < p) (a : ℝ) (hinj : InjOn γ (Ioo a (a + p))) :
    Measure.map γ ((volume.restrict (Ioc a (a + p))).withDensity
      fun t ↦ ‖curveVelocity I γ t‖ₑ) = (riemannianVolume I M).restrict (range γ) := by
  have hdim : Module.finrank ℝ E = 1 := by
    -- The differential of `γ` at `a` is a linear equivalence from `TangentSpace 𝓘(ℝ) a`, which is
    -- `ℝ`, onto `TangentSpace I (γ a)`, which is `E`.
    have h : Module.finrank ℝ ℝ = Module.finrank ℝ E :=
      ((hγ a).mfderivToContinuousLinearEquiv hn).toLinearEquiv.finrank_eq
    rw [← h, Module.finrank_self]
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  have hrange : range γ = insert (γ (a + p)) (γ '' Ioo a (a + p)) := by
    rw [← hper.image_Ioc hp a, ← insert_right_Ioo (lt_add_of_pos_right a hp), image_insert_eq]
  rw [hrange, Measure.restrict_congr_set (insert_ae_eq_self _ _),
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have h := (((hγ.isLocalDiffeomorphOn _).partialDiffeomorphOfInjOn isOpen_Ioo hinj).ofLE
    (ENat.one_le_iff_ne_zero_withTop.mpr hn)).map_withDensity_enorm_curveVelocity hdim
  rwa [PartialDiffeomorph.ofLE_toPartialEquiv,
    IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn,
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source,
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target] at h

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- For a `p`-periodic `C^n` local diffeomorphism `γ` from `ℝ` to a Riemannian manifold, with
`n ≠ 0`, which is injective on the open interval `(a, a + p)`, the integral of `f` over the range
of `γ` against the Riemannian volume is the integral over a period of `f ∘ γ` weighted by the
speed of `γ`. -/
theorem _root_.IsLocalDiffeomorph.setIntegral_riemannianVolume_range_of_periodic
    {n : ℕ∞ω} {γ : ℝ → M} {p : ℝ} (hγ : IsLocalDiffeomorph 𝓘(ℝ) I n γ) (hn : n ≠ 0)
    (hper : γ.Periodic p) (hp : 0 < p) (a : ℝ) (hinj : InjOn γ (Ioo a (a + p))) {f : M → G}
    (hf : AEStronglyMeasurable f ((riemannianVolume I M).restrict (range γ))) :
    ∫ y in range γ, f y ∂riemannianVolume I M =
      ∫ t in a..a + p, ‖curveVelocity I γ t‖ • f (γ t) :=
  ContMDiff.integral_eq_intervalIntegral_norm_curveVelocity_smul
    (hγ.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn)) (le_add_of_nonneg_right hp.le)
    (hγ.map_withDensity_enorm_curveVelocity_of_periodic hn hper hp a hinj) hf

/-! ### Parametrizations by `AddCircle p` -/

/-- A `C^n` diffeomorphism `e` from `AddCircle p` onto a Riemannian manifold `M`, with `n ≠ 0`,
read on `ℝ`, carries the Lebesgue measure on the period interval `(a, a + p]`, weighted by the
speed of `t ↦ e t`, to the Riemannian volume of `M`. -/
theorem _root_.Diffeomorph.map_withDensity_enorm_curveVelocity_addCircle {n : ℕ∞ω} {p : ℝ}
    [Fact (0 < p)] (e : AddCircle p ≃ₘ^n⟮𝓘(ℝ), I⟯ M) (hn : n ≠ 0) (a : ℝ) :
    Measure.map (fun t : ℝ ↦ e t) ((volume.restrict (Ioc a (a + p))).withDensity
      fun t ↦ ‖curveVelocity I (fun r : ℝ ↦ e r) t‖ₑ) = riemannianVolume I M := by
  have h := IsLocalDiffeomorph.map_withDensity_enorm_curveVelocity_of_periodic
    (γ := fun t : ℝ ↦ e t)
    (fun t ↦ (AddCircle.isLocalDiffeomorph_coe p n t).comp I M (e.isLocalDiffeomorph t)) hn
    (fun t ↦ congrArg e (AddCircle.coe_add_period p t)) Fact.out a
    fun _ hx _ hy h ↦ (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (Ioo_subset_Ico_self hy)).mp (e.injective h)
  have hrange : range (fun t : ℝ ↦ e t) = univ :=
    (e.surjective.comp QuotientAddGroup.mk_surjective).range_eq
  rwa [hrange, Measure.restrict_univ] at h

/-- For a `C^n` diffeomorphism `e` from `AddCircle p` onto a Riemannian manifold `M`, with
`n ≠ 0`, the integral of `f` against the Riemannian volume of `M` is the integral over a period of
`t ↦ f (e t)` weighted by the speed of `t ↦ e t`. -/
theorem _root_.Diffeomorph.integral_riemannianVolume_addCircle {n : ℕ∞ω} {p : ℝ}
    [Fact (0 < p)] (e : AddCircle p ≃ₘ^n⟮𝓘(ℝ), I⟯ M) (hn : n ≠ 0) (a : ℝ) {f : M → G}
    (hf : AEStronglyMeasurable f (riemannianVolume I M)) :
    ∫ y, f y ∂riemannianVolume I M =
      ∫ t in a..a + p, ‖curveVelocity I (fun r : ℝ ↦ e r) t‖ • f (e t) :=
  ContMDiff.integral_eq_intervalIntegral_norm_curveVelocity_smul
    ((e.contMDiff.comp (AddCircle.contMDiff_coe p n)).of_le
      (ENat.one_le_iff_ne_zero_withTop.mpr hn))
    (le_add_of_nonneg_right (Fact.out : 0 < p).le)
    (e.map_withDensity_enorm_curveVelocity_addCircle hn a) hf

end TauCeti
