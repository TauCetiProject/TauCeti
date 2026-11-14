/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables

/-!
# Immersion volume and calibrated immersions

The **immersion volume** `TauCeti.immersionVolume` of an oriented smooth immersion `f : N → M` into
a Riemannian manifold `(M, g)` is the integral over `N` of the Riemannian volume form of the
pulled-back metric `f^* g`. It is independent of the choice of orientation on `N`. An oriented
immersion `f` is **calibrated** by a `k`-form `φ` (`TauCeti.IsCalibratedImmersion`) when
`f^* φ = dvol_{f^* g}`.

## Main definitions

* `TauCeti.immersionVolume`: the volume of an oriented smooth immersion with respect to the
  pulled-back Riemannian metric.
* `TauCeti.IsCalibratedImmersion`: an oriented smooth immersion whose pullback of `φ` equals the
  Riemannian volume form of the pulled-back metric.

## Main results

* `TauCeti.isCalibratedImmersion_iff_forall_orthonormal_basis` and
  `TauCeti.isCalibratedImmersion_iff_exists_orthonormal_basis`: positive-degree characterizations on
  positively oriented orthonormal tangent frames.
* `TauCeti.immersionVolume_neg` and `TauCeti.isCalibratedImmersion_neg_iff`: orientation-reversal
  properties.
* `TauCeti.integralTopForm_mpullback_eq_immersionVolume`: for a calibrated immersion,
  `∫_N f^* φ = Vol(f)`.
* `TauCeti.immersionVolume_comp_diffeomorph` and `TauCeti.IsCalibratedImmersion.comp_diffeomorph`:
  invariance under orientation-preserving diffeomorphisms of the source.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Definition 2.1.
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped Bundle ContDiff Manifold

namespace TauCeti

/-! ### Calibrated immersions and volume -/

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]

/-- The volume of a smooth immersion `f : N → M` of an oriented `k`-manifold: the integral over
`N`, against its orientation `o`, of the Riemannian volume form of the pulled-back metric `f^* g`.
It does not depend on the orientation chosen. -/
def immersionVolume {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : ℝ :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  integralTopForm o (riemannianVolumeForm o)

/-- Unfolding lemma for `immersionVolume`. -/
theorem immersionVolume_def {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
      integralTopForm o (riemannianVolumeForm o) :=
  (rfl)

/-- The oriented immersion `f` is calibrated by the `k`-form `φ`: `f^* φ` is the Riemannian volume
form of the pulled-back metric `f^* g` for the orientation `o`. -/
def IsCalibratedImmersion {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : Prop :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  mpullback I' I f φ = riemannianVolumeForm o

/-- Unfolding lemma for `IsCalibratedImmersion`. -/
theorem isCalibratedImmersion_iff {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
      mpullback I' I f φ = riemannianVolumeForm o :=
  Iff.rfl

/-- In positive degree, an immersion is calibrated by `φ` iff `φ` evaluates to `1` on the image
of every positively oriented `f^* g`-orthonormal tangent basis. -/
theorem isCalibratedImmersion_iff_forall_orthonormal_basis {k : ℕ} [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      ∀ x (b : Module.Basis (Fin k) ℝ (TangentSpace I' x)),
        b.orientation = o.orientationAt x →
        (∀ i j, g.inner (f x) (mfderiv I' I f x (b i)) (mfderiv I' I f x (b j)) =
          if i = j then 1 else 0) →
        φ (f x) (mfderiv I' I f x ∘ b) = 1 := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  constructor
  · intro h x b hb horth
    let b' : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
      OrthonormalBasis.mk (orthonormal_iff_ite.2 fun i j ↦ by
        rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
          ContMDiffRiemannianMetric.pullback_inner]
        exact horth i j)
        b.span_eq.ge
    have hb'_fun : (⇑b' : Fin k → TangentSpace I' x) = ⇑b := OrthonormalBasis.coe_mk _ _
    have hb_eq : b'.toBasis = b := by
      ext i
      rw [b'.coe_toBasis]
      exact congrFun hb'_fun i
    have hb' : b'.toBasis.orientation = o.orientationAt x := hb_eq ▸ hb
    rw [isCalibratedImmersion_iff] at h
    have hx := DFunLike.congr_fun (congrFun h x) ⇑b'
    rw [mpullback_apply, riemannianVolumeForm_apply_orthonormal o x b' hb', hb'_fun] at hx
    exact hx
  · intro h
    ext x v
    have := o.fact_finrank_tangentSpace x
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
    let b : OrthonormalBasis (Fin (m + 1)) ℝ (TangentSpace I' x) :=
      ((stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex
        (finCongr (by simpa using o.finrank_tangentSpace_eq x))).adjustToOrientation
        (o.orientationAt x)
    have hb : b.toBasis.orientation = o.orientationAt x :=
      OrthonormalBasis.orientation_adjustToOrientation _ _
    have horth : ∀ i j, g.inner (f x) (mfderiv I' I f x (b.toBasis i))
        (mfderiv I' I f x (b.toBasis j)) = if i = j then 1 else 0 := fun i j ↦ by
      rw [← ContMDiffRiemannianMetric.pullback_inner,
        ← ContMDiffRiemannianMetric.inner_riemannianBundle]
      exact orthonormal_iff_ite.mp b.orthonormal i j
    have hEq := eq_riemannianVolumeForm_of_apply_orthonormal o x (mpullback I' I f φ x) b hb (by
      rw [mpullback_apply]
      exact h x b.toBasis hb horth)
    exact DFunLike.congr_fun hEq v

/-- In positive degree, an immersion is calibrated by `φ` iff at every point there exists a
positively oriented `f^* g`-orthonormal tangent basis on whose image `φ` evaluates to `1`. -/
theorem isCalibratedImmersion_iff_exists_orthonormal_basis {k : ℕ} [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      ∀ x, ∃ b : Module.Basis (Fin k) ℝ (TangentSpace I' x),
        b.orientation = o.orientationAt x ∧
        (∀ i j, g.inner (f x) (mfderiv I' I f x (b i)) (mfderiv I' I f x (b j)) =
          if i = j then 1 else 0) ∧
        φ (f x) (mfderiv I' I f x ∘ b) = 1 := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  constructor
  · intro h x
    have := o.fact_finrank_tangentSpace x
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
    let b : OrthonormalBasis (Fin (m + 1)) ℝ (TangentSpace I' x) :=
      ((stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex
        (finCongr (by simpa using o.finrank_tangentSpace_eq x))).adjustToOrientation
        (o.orientationAt x)
    have hb : b.toBasis.orientation = o.orientationAt x :=
      OrthonormalBasis.orientation_adjustToOrientation _ _
    have horth : ∀ i j, g.inner (f x) (mfderiv I' I f x (b.toBasis i))
        (mfderiv I' I f x (b.toBasis j)) = if i = j then 1 else 0 := fun i j ↦ by
      rw [← ContMDiffRiemannianMetric.pullback_inner,
        ← ContMDiffRiemannianMetric.inner_riemannianBundle]
      exact orthonormal_iff_ite.mp b.orthonormal i j
    exact ⟨b.toBasis, hb, horth,
      (isCalibratedImmersion_iff_forall_orthonormal_basis g φ f hf hinj o).1 h x b.toBasis hb horth⟩
  · intro h
    ext x v
    obtain ⟨b, hb, horth, hval⟩ := h x
    let b' : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
      OrthonormalBasis.mk (orthonormal_iff_ite.2 fun i j ↦ by
        rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
          ContMDiffRiemannianMetric.pullback_inner]
        exact horth i j)
        b.span_eq.ge
    have hb'_fun : (⇑b' : Fin k → TangentSpace I' x) = ⇑b := OrthonormalBasis.coe_mk _ _
    have hb_eq : b'.toBasis = b := by
      ext i
      rw [b'.coe_toBasis]
      exact congrFun hb'_fun i
    have hb' : b'.toBasis.orientation = o.orientationAt x := hb_eq ▸ hb
    have hEq := eq_riemannianVolumeForm_of_apply_orthonormal o x (mpullback I' I f φ x) b' hb' (by
      rw [mpullback_apply]
      have hsub : (fun i ↦ mfderiv I' I f x (b' i)) = mfderiv I' I f x ∘ b := by
        rw [hb'_fun]
        rfl
      rw [hsub]
      exact hval)
    exact DFunLike.congr_fun hEq v

/-- Reversing the source orientation reverses the sign of the calibration. -/
@[simp]
theorem isCalibratedImmersion_neg_iff {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g (-φ) f hf hinj (-o) ↔ IsCalibratedImmersion g φ f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have hvol : riemannianVolumeForm (-o) = -riemannianVolumeForm o := by
    ext x v
    simp [riemannianVolumeForm_apply, _root_.Orientation.volumeForm_neg_orientation]
  have hmp : mpullback I' I f (-φ) = -mpullback I' I f φ := by
    ext x v
    simp [mpullback_apply]
  rw [isCalibratedImmersion_iff, hvol, hmp, neg_inj, isCalibratedImmersion_iff]

/-- Reversing the orientation of the source does not change `immersionVolume`. -/
@[simp]
theorem immersionVolume_neg {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj (-o) = immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have hvol : riemannianVolumeForm (-o) = -riemannianVolumeForm o := by
    ext x v
    simp [riemannianVolumeForm_apply, _root_.Orientation.volumeForm_neg_orientation]
  rw [immersionVolume_def, immersionVolume_def, hvol, integralTopForm_neg,
    show -riemannianVolumeForm o = (-1 : ℝ) • riemannianVolumeForm o from (neg_one_smul ℝ _).symm,
    integralTopForm_smul, neg_one_mul, neg_neg]

/-- If `f` is calibrated by `φ` and its pullback `f^* φ` is integrable (in particular on a compact
source), then `∫_N f^* φ = Vol(f)`. -/
theorem integralTopForm_mpullback_eq_immersionVolume {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o := by
  rw [immersionVolume_def]
  exact congrArg (integralTopForm o) hcal

section Transport

variable {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' 1 N']

/-- The Riemannian volume form of a pullback metric along an orientation-preserving diffeomorphism
is the pullback of the Riemannian volume form. -/
private theorem riemannianVolumeForm_pullback_diffeomorph {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationPreservingAt o Φ x) :
    letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) :=
      ⟨(g.pullback (f ∘ Φ) (by simpa using hf.comp Φ.contMDiff) fun x ↦ by
        rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
          (Φ.contMDiff.mdifferentiableAt (by simp))]
        exact (hinj (Φ x)).comp
          (Φ.isInvertible_mfderiv (x := x) (by simp)).injective).toRiemannianMetric⟩
    riemannianVolumeForm o' = mpullback I'' I' Φ (riemannianVolumeForm o) := by
  let hfΦ : ContMDiff I'' I ∞ (f ∘ Φ) := hf.comp Φ.contMDiff
  let hinjΦ : ∀ x, Function.Injective (mfderiv I'' I (f ∘ Φ) x) := fun x ↦ by
    rw [mfderiv_comp x (hf.mdifferentiableAt (by simp)) (Φ.contMDiff.mdifferentiableAt (by simp))]
    exact (hinj (Φ x)).comp (Φ.isInvertible_mfderiv (x := x) (by simp)).injective
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) :=
    ⟨(g.pullback (f ∘ Φ) (by simpa using hfΦ) hinjΦ).toRiemannianMetric⟩
  ext x v
  have := o'.fact_finrank_tangentSpace x
  have := o.fact_finrank_tangentSpace (Φ x)
  obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 (ho x)
  rcases k with - | k
  · have hv : v = ![] := Subsingleton.elim v ![]
    subst hv
    rw [riemannianVolumeForm_apply, mpullback_apply, riemannianVolumeForm_apply]
    have hcomp : (fun i : Fin 0 ↦ mfderiv I'' I' Φ x (![] i)) = ![] := Subsingleton.elim _ _
    rw [hcomp]
    rcases (o'.orientationAt x).eq_or_eq_neg_of_isEmpty with h | h <;>
      simp [← hmap, h]
  · let b : OrthonormalBasis (Fin (k + 1)) ℝ (TangentSpace I'' x) :=
      ((stdOrthonormalBasis ℝ (TangentSpace I'' x)).reindex
        (finCongr (by simpa using o'.finrank_tangentSpace_eq x))).adjustToOrientation
        (o'.orientationAt x)
    have hb : b.toBasis.orientation = o'.orientationAt x :=
      OrthonormalBasis.orientation_adjustToOrientation _ _
    let dΦ : TangentSpace I'' x ≃ₗᵢ[ℝ] TangentSpace I' (Φ x) :=
      { toLinearEquiv := e.toLinearEquiv
        norm_map' := fun u ↦ by
          rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
          congr 1
          rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
            ContMDiffRiemannianMetric.pullback_inner,
            ContMDiffRiemannianMetric.inner_riemannianBundle,
            ContMDiffRiemannianMetric.pullback_inner]
          have heu : mfderiv I'' I' Φ x u = e u := congrFun (congrArg DFunLike.coe he.symm) u
          rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
            (Φ.contMDiff.mdifferentiableAt (by simp)), ContinuousLinearMap.comp_apply, heu]
          rfl }
    let b' : OrthonormalBasis (Fin (k + 1)) ℝ (TangentSpace I' (Φ x)) := b.map dΦ
    have hb' : b'.toBasis.orientation = o.orientationAt (Φ x) := by
      have hb_map : b'.toBasis = b.toBasis.map e.toLinearEquiv := by
        ext i
        rfl
      rw [hb_map, Module.Basis.orientation_map, hb, hmap]
    have hEq := eq_riemannianVolumeForm_of_apply_orthonormal o' x
      (mpullback I'' I' Φ (riemannianVolumeForm o) x) b hb (by
        have h1 := riemannianVolumeForm_apply_orthonormal o (Φ x) b' hb'
        have hcomp : (fun i ↦ mfderiv I'' I' Φ x (b i)) = fun i ↦ b' i := by
          ext i
          exact congrFun (congrArg DFunLike.coe he.symm) (b i)
        simpa [mpullback_apply, hcomp] using h1)
    exact (DFunLike.congr_fun hEq v).symm

/-- Precomposing an immersion with an orientation-preserving diffeomorphism preserves its
volume. -/
theorem immersionVolume_comp_diffeomorph {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationPreservingAt o Φ x) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ by
          rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
            (Φ.contMDiff.mdifferentiableAt (by simp))]
          exact (hinj (Φ x)).comp (Φ.isInvertible_mfderiv (x := x) (by simp)).injective) o' =
      immersionVolume g f hf hinj o := by
  let hfΦ : ContMDiff I'' I ∞ (f ∘ Φ) := hf.comp Φ.contMDiff
  let hinjΦ : ∀ x, Function.Injective (mfderiv I'' I (f ∘ Φ) x) := fun x ↦ by
    rw [mfderiv_comp x (hf.mdifferentiableAt (by simp)) (Φ.contMDiff.mdifferentiableAt (by simp))]
    exact (hinj (Φ x)).comp (Φ.isInvertible_mfderiv (x := x) (by simp)).injective
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) :=
    ⟨(g.pullback (f ∘ Φ) (by simpa using hfΦ) hinjΦ).toRiemannianMetric⟩
  have hvol := riemannianVolumeForm_pullback_diffeomorph g f hf hinj o Φ o' ho
  rw [immersionVolume_def, immersionVolume_def, hvol]
  exact Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
    (by simp)

/-- Precomposing a calibrated immersion with an orientation-preserving diffeomorphism gives a
calibrated immersion. -/
theorem IsCalibratedImmersion.comp_diffeomorph {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)} (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N) (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationPreservingAt o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
      (fun x ↦ by
        rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
          (Φ.contMDiff.mdifferentiableAt (by simp))]
        exact (hinj (Φ x)).comp (Φ.isInvertible_mfderiv (x := x) (by simp)).injective) o' := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) :=
    ⟨(g.pullback (f ∘ Φ) (by simpa using hf.comp Φ.contMDiff) fun x ↦ by
      rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp))]
      exact (hinj (Φ x)).comp
        (Φ.isInvertible_mfderiv (x := x) (by simp)).injective).toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff,
    mpullback_comp (Φ.contMDiff.mdifferentiable (by simp)) (hf.mdifferentiable (by simp)),
    (isCalibratedImmersion_iff g φ f hf hinj o).1 hcal,
    ← riemannianVolumeForm_pullback_diffeomorph g f hf hinj o Φ o' ho]

end Transport

end Immersions

end TauCeti
