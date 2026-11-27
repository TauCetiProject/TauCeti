/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
public import TauCeti.Geometry.Calibrated.FundamentalTheorem
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
public import TauCeti.Geometry.Manifold.Riemannian.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
import TauCeti.Geometry.Manifold.DeRham.Wedge

/-!
# Kähler calibrations

Let `(M, g)` be a Riemannian manifold with a smooth almost complex structure `J` that is
orthogonal for `g`, and let `ω(u, w) = g(J u, w)` be its Kähler two-form
(`TauCeti.SmoothAlmostComplexStructure.kahlerTwoForm`). The **normalized Kähler power**
`TauCeti.SmoothAlmostComplexStructure.kahlerPowerForm J hJ r` is the smooth `2r`-form `ω ^ r / r!`.
At every point it is the normalized Kähler power of the tangent space
(`TauCeti.AlmostComplexStructure.kahlerPowerForm`), so by the Wirtinger inequality it has comass at
most one everywhere. When `ω` is closed, which holds on a Kähler manifold, so are its wedge powers,
and `ω ^ r / r!` is a calibration.

Let `f : N → M` be an immersion of a manifold of dimension `2r` with an almost complex structure
`j`, pseudoholomorphic (`df ∘ j = J ∘ df`), and orient `N` by the complex orientation of `j`.
Each tangent space of `N` then has a positive basis, orthonormal for `f^* g`, which `df` carries
to a frame calibrated by `ω ^ r / r!`, so `f` is a calibrated immersion. By the fundamental
theorem of calibrations, a compact pseudoholomorphic immersion has least volume among compact
oriented competitors with the same integrals of every smooth closed `2r`-form, with equality
exactly for the competitors calibrated by `ω ^ r / r!`. Integrability of `J` plays no role: the
statements hold on every almost Kähler manifold, and in particular for compact complex
submanifolds of Kähler manifolds.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.kahlerPowerForm J hJ r`: the smooth `2r`-form
  `ω ^ r / r!`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.kahlerPowerForm_apply`: its value at a point is the
  normalized Kähler power of the tangent space.
* `TauCeti.SmoothAlmostComplexStructure.isClosed_kahlerPowerForm`: it is closed when `ω` is.
* `TauCeti.SmoothAlmostComplexStructure.isCalibration_kahlerPowerForm`: it is a calibration when
  `ω` is closed.
* `TauCeti.SmoothAlmostComplexStructure.isCalibratedImmersion_kahlerPowerForm`: pseudoholomorphic
  immersions, with their complex orientation, are calibrated by it.
* `TauCeti.SmoothAlmostComplexStructure.immersionVolume_le_of_isPseudoholomorphic` and
  `TauCeti.SmoothAlmostComplexStructure.immersionVolume_eq_iff_of_isPseudoholomorphic`: compact
  pseudoholomorphic immersions minimize volume among competitors with the same periods, with
  equality exactly for the competitors calibrated by `ω ^ r / r!`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.4.2 and Section II.6.
-/

public section

noncomputable section

open Bundle Manifold Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {J : SmoothAlmostComplexStructure I M}

/-- The **normalized Kähler power** `ω ^ r / r!` of an orthogonal smooth almost complex structure
`J`: the `r`-th wedge power of the Kähler two-form `ω(u, w) = ⟪J u, w⟫`, divided by `r!`. -/
def kahlerPowerForm (J : SmoothAlmostComplexStructure I M)
    (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫) (r : ℕ) :
    SmoothForm I M ℝ (2 * r) :=
  (r.factorial : ℝ)⁻¹ • (J.kahlerTwoForm hJ).wedgePow r

variable (hJ : ∀ (x : M) (u w : TangentSpace I x), ⟪J x u, J x w⟫ = ⟪u, w⟫)
include hJ

/-- At every point, `ω ^ r / r!` is the normalized Kähler power of the tangent space. -/
theorem kahlerPowerForm_apply (r : ℕ) (x : M) :
    (J.kahlerPowerForm hJ r).val x =
      (letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
       (J.almostComplexStructureAt x).kahlerPowerForm r) := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  rw [kahlerPowerForm, Submodule.coe_smul, Pi.smul_apply, SmoothForm.wedgePow_apply,
    kahlerTwoForm_apply, AlmostComplexStructure.kahlerPowerForm_def]

/-- `ω ^ r / r!` is closed when the Kähler two-form `ω` is. -/
theorem isClosed_kahlerPowerForm (hω : (J.kahlerTwoForm hJ).IsClosed) (r : ℕ) :
    (J.kahlerPowerForm hJ r).IsClosed := by
  have h := SmoothForm.wedgePow_mem_closedForms
    ((mem_closedForms I _).2 ((SmoothForm.isClosed_def _).1 hω)) r
  exact SmoothForm.IsClosed.smul _ ((SmoothForm.isClosed_def _).2 ((mem_closedForms I _).1 h))

/-- **Kähler calibrations.** When the Kähler two-form `ω` of an orthogonal smooth almost complex
structure is closed, `ω ^ r / r!` is a calibration. -/
theorem isCalibration_kahlerPowerForm (hω : (J.kahlerTwoForm hJ).IsClosed) (r : ℕ) :
    IsCalibration
      (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
      (J.kahlerPowerForm hJ r).val := by
  refine (isCalibration_iff _ _).2 ⟨(J.kahlerPowerForm hJ r).isSmoothForm,
    (SmoothForm.isClosed_def _).1 (isClosed_kahlerPowerForm hJ hω r), fun x v hv ↦ ?_⟩
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  have hJx (u w : TangentSpace I x) :
      ⟪J.almostComplexStructureAt x u, J.almostComplexStructureAt x w⟫ = ⟪u, w⟫ := by
    simpa only [almostComplexStructureAt_apply] using hJ x u w
  have hvo : Orthonormal ℝ v := orthonormal_iff_ite.2 fun i i' ↦ by
    rw [← hv i i', ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
    -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
    rfl
  rw [kahlerPowerForm_apply hJ, ← Real.norm_eq_abs]
  exact (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).1
    (AlmostComplexStructure.norm_kahlerPowerForm_le hJx r) v hvo

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {j : SmoothAlmostComplexStructure I' N} {r : ℕ}

/-- **Pseudoholomorphic immersions are calibrated.** An immersion `f` of a manifold of dimension
`2r` with an almost complex structure `j`, pseudoholomorphic for `j` and an orthogonal `J`, is
calibrated by `ω ^ r / r!` for the complex orientation of `j`. -/
theorem isCalibratedImmersion_kahlerPowerForm (hr : finrank ℝ E' = 2 * r) {f : N → M}
    (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (hfj : IsPseudoholomorphic j J f) :
    IsCalibratedImmersion
      (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
      (J.kahlerPowerForm hJ r).val f hf hinj (j.orientation hr) := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨((ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E)).pullback
      f hf hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff]
  funext x
  let _ : FiniteDimensional ℝ (TangentSpace I (f x)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) (f x)
  let _ : FiniteDimensional ℝ (TangentSpace I' x) :=
    VectorBundle.finiteDimensional ℝ E' (TangentSpace I') x
  have hJx (u w : TangentSpace I (f x)) :
      ⟪J.almostComplexStructureAt (f x) u, J.almostComplexStructureAt (f x) w⟫ = ⟪u, w⟫ := by
    simpa only [almostComplexStructureAt_apply] using hJ (f x) u w
  -- The differential carries a positive basis of `T_x N` to a calibrated frame of `T_{f x} M`.
  obtain ⟨b, hb, hcal⟩ :=
    AlmostComplexStructure.exists_basis_orientation_eq_and_isCalibratedFrame_kahlerPowerForm hJx
      (j.almostComplexStructureAt x) hr (L := (mfderiv I' I f x : _ →ₗ[ℝ] _)) (hinj x)
      fun u ↦ by
        simpa only [almostComplexStructureAt_apply, ContinuousLinearMap.coe_coe] using
          (hfj.isPseudoholomorphicAt x).mfderiv_apply_commute u
  have horth : Orthonormal ℝ b := by
    refine (ContMDiffRiemannianMetric.orthonormal_pullback_iff _ f hf hinj x b).2 fun i i' ↦ ?_
    rw [ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
    -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
    exact orthonormal_iff_ite.1 hcal.orthonormal i i'
  refine eq_riemannianVolumeForm_of_apply_of_orthonormal _ x _ b
    (by rw [orientationAt_orientation, hb]) horth ?_
  rw [mpullback_apply, kahlerPowerForm_apply hJ]
  exact hcal.apply_eq_one

variable {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace N']
  [ChartedSpace H'' N'] [IsManifold I'' 1 N'] [CompactSpace N']

/-- **Pseudoholomorphic immersions minimize volume.** On an almost complex manifold whose Kähler
two-form is closed, a pseudoholomorphic immersion `f` of a `2r`-manifold, with its complex
orientation, has volume at most that of every compact oriented competitor `f'` with the same
integrals of every smooth closed `2r`-form. When `N` is compact, the volume of `f` is the
Riemannian total volume of `N` for the pulled-back metric
(`TauCeti.immersionVolume_eq_riemannianTotalVolume`). -/
theorem immersionVolume_le_of_isPseudoholomorphic (hω : (J.kahlerTwoForm hJ).IsClosed)
    (hr : finrank ℝ E' = 2 * r) {f : N → M} (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) (hfj : IsPseudoholomorphic j J f)
    {f' : N' → M} (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin (2 * r)))
    (hhom : ∀ η : RoughForm I M ℝ (2 * r), IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm (j.orientation hr) (mpullback I' I f η) =
        integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume
        (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
        f hf hinj (j.orientation hr) ≤
      immersionVolume
        (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
        f' hf' hinj' o' :=
  immersionVolume_le_of_isCalibratedImmersion _ _ (isCalibration_kahlerPowerForm hJ hω r) f hf
    hinj _ (isCalibratedImmersion_kahlerPowerForm hJ hr hf hinj hfj) f' hf' hinj' o' hhom

/-- **Equality in the volume bound for pseudoholomorphic immersions.** Under the hypotheses of
`immersionVolume_le_of_isPseudoholomorphic`, the competitor `f'` has the same volume as the
pseudoholomorphic immersion `f` exactly when it is calibrated by `ω ^ r / r!` with its
orientation `o'`. -/
theorem immersionVolume_eq_iff_of_isPseudoholomorphic (hω : (J.kahlerTwoForm hJ).IsClosed)
    (hr : finrank ℝ E' = 2 * r) {f : N → M} (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) (hfj : IsPseudoholomorphic j J f)
    {f' : N' → M} (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin (2 * r)))
    (hhom : ∀ η : RoughForm I M ℝ (2 * r), IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm (j.orientation hr) (mpullback I' I f η) =
        integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume
        (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
        f hf hinj (j.orientation hr) =
      immersionVolume
        (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
        f' hf' hinj' o' ↔
      IsCalibratedImmersion
        (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E))
        (J.kahlerPowerForm hJ r).val f' hf' hinj' o' :=
  immersionVolume_eq_iff_isCalibratedImmersion _ _ (isCalibration_kahlerPowerForm hJ hω r) f hf
    hinj _ (isCalibratedImmersion_kahlerPowerForm hJ hr hf hinj hfj) f' hf' hinj' o' hhom

end TauCeti.SmoothAlmostComplexStructure
