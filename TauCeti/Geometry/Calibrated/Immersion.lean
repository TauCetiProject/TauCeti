/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Immersion volume and calibrated immersions

The **immersion volume** `TauCeti.immersionVolume` of an oriented smooth immersion `f : N → M` into
a Riemannian manifold `(M, g)` is defined as `integralTopForm o (riemannianVolumeForm o)` for the
pulled-back metric `f^* g`. On a compact source `N`, it equals the total Riemannian volume
`TauCeti.riemannianTotalVolume` of `N` equipped with `f^* g`
(`TauCeti.immersionVolume_eq_riemannianTotalVolume`); on a noncompact source `N`, it evaluates to
`0` by `TauCeti.integralTopForm`'s compact-support convention
(`TauCeti.immersionVolume_eq_zero_of_not_compactSpace`), even when `f^* g` has finite Riemannian
volume. In all cases it is independent of the choice of orientation on `N`
(`TauCeti.immersionVolume_congr_orientation`).

An oriented immersion `f` is **calibrated** by a `k`-form `φ` (`TauCeti.IsCalibratedImmersion`)
when `f^* φ = dvol_{f^* g}`.

## Main definitions

* `TauCeti.immersionVolume`: the top-form integral over `N` of the Riemannian volume form of the
  pulled-back Riemannian metric `f^* g`.
* `TauCeti.IsCalibratedImmersion`: an oriented smooth immersion whose pullback of `φ` equals the
  Riemannian volume form of the pulled-back metric.

## Main results

* `TauCeti.immersionVolume_eq_riemannianTotalVolume` and
  `TauCeti.immersionVolume_eq_zero_of_not_compactSpace`: identification with
  `riemannianTotalVolume` on compact `N` and `0` fallback on noncompact `N`.
* `TauCeti.immersionVolume_congr_orientation`, `TauCeti.immersionVolume_neg`,
  `TauCeti.immersionVolume_nonneg`, and `TauCeti.immersionVolume_pos`: orientation independence,
  nonnegativity, and positivity on nonempty compact sources.
* `TauCeti.isCalibratedImmersion_iff_forall_orthonormal_basis`,
  `TauCeti.isCalibratedImmersion_iff_exists_orthonormal_basis`, and
  `TauCeti.isCalibratedImmersion_zeroDim_iff`: tangent-frame characterizations in positive degree
  and degree zero.
* `TauCeti.IsCalibratedImmersion.neg` and `TauCeti.isCalibratedImmersion_neg_right_iff`:
  orientation-reversal properties.
* `TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_immersionVolume` and
  `TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_riemannianTotalVolume`: integral of
  `f^* φ` along a calibrated immersion.
* `TauCeti.immersionVolume_comp_diffeomorph`,
  `TauCeti.IsCalibratedImmersion.comp_diffeomorph_of_isOrientationPreservingAt`, and
  `TauCeti.isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt`: invariance of
  `immersionVolume` under arbitrary diffeomorphisms and of `IsCalibratedImmersion` under
  orientation-preserving diffeomorphisms of the source.

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

/-- The volume of a smooth immersion `f : N → M` of an oriented `k`-manifold: the top-form integral
over `N`, against its orientation `o`, of the Riemannian volume form of the pulled-back metric
`f^* g`. On compact `N` this equals the total Riemannian volume of `f^* g`
(`immersionVolume_eq_riemannianTotalVolume`), whereas on noncompact `N` it returns `0` via
`integralTopForm`'s compact-support convention (`immersionVolume_eq_zero_of_not_compactSpace`). It
does not depend on the orientation chosen (`immersionVolume_congr_orientation`). -/
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

/-- On a noncompact source `N`, `immersionVolume` evaluates to `0` via `integralTopForm`'s
compact-support fallback, because `riemannianVolumeForm` has support `Set.univ`. -/
theorem immersionVolume_eq_zero_of_not_compactSpace {k : ℕ} (hnc : ¬CompactSpace N)
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o = 0 := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o hnc

/-- On a compact source `N`, `immersionVolume` equals the total Riemannian volume of `N` equipped
with the pulled-back metric `f^* g` (`WithMetric (g.pullback f ...)`), in every degree `k : ℕ`. -/
theorem immersionVolume_eq_riemannianTotalVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      riemannianTotalVolume I' (WithMetric (g.pullback f (by simpa using hf) hinj)) := by
  set g' := g.pullback f (by simpa using hf) hinj
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨g'.toRiemannianMetric⟩
  let Φ : WithMetric g' ≃ₘ^∞⟮I', I'⟯ N := WithMetric.diffeomorph g' ∞
  let oW : Manifold.Orientation I' (WithMetric g') (Fin k) :=
    o.pullback (Φ.contMDiff.of_le (by simp)) (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o.card_eq
  have ho : ∀ x, oW.IsOrientationPreservingAt o Φ x :=
    o.isOrientationPreservingAt_pullback (Φ.contMDiff.of_le (by simp))
      (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o.card_eq
  have hvol : mpullback I' I' Φ (riemannianVolumeForm o) = riemannianVolumeForm oW :=
    mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho fun x v w ↦ by
      rw [WithMetric.coe_diffeomorph, g'.inner_riemannianBundle]
      exact (WithMetric.inner_def x v w).symm
  rw [immersionVolume_def,
    ← Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
      (by simp),
    Φ.coe_toHomeomorph, hvol, integralTopForm_riemannianVolumeForm_eq_riemannianTotalVolume oW]

/-- `immersionVolume` is independent of the orientation chosen on `N` (even across disconnected
components). -/
theorem immersionVolume_congr_orientation {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o₁ o₂ : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o₁ = immersionVolume g f hf hinj o₂ := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_def, immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_congr o₁ o₂

/-- Reversing the orientation of the source does not change `immersionVolume`. -/
@[simp]
theorem immersionVolume_neg {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj (-o) = immersionVolume g f hf hinj o :=
  immersionVolume_congr_orientation g f hf hinj (-o) o

/-- The volume of an oriented smooth immersion is nonnegative. -/
theorem immersionVolume_nonneg {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_nonneg o

/-- The volume of a nonempty compact oriented smooth immersion is positive. -/
theorem immersionVolume_pos [CompactSpace N] [Nonempty N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 < immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_def]
  exact integralTopForm_riemannianVolumeForm_pos o

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

/-- Equal immersions are calibrated by the same forms regardless of the smoothness and injectivity
proofs supplied. -/
theorem isCalibratedImmersion_congr {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f₁ f₂ : N → M} (h : f₁ = f₂)
    {hf₁ : ContMDiff I' I ∞ f₁} {hinj₁ : ∀ x, Function.Injective (mfderiv I' I f₁ x)}
    {hf₂ : ContMDiff I' I ∞ f₂} {hinj₂ : ∀ x, Function.Injective (mfderiv I' I f₂ x)}
    {o : Manifold.Orientation I' N (Fin k)} :
    IsCalibratedImmersion g φ f₁ hf₁ hinj₁ o ↔ IsCalibratedImmersion g φ f₂ hf₂ hinj₂ o := by
  subst h
  rfl

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
    have hb_orth : Orthonormal ℝ b := orthonormal_iff_ite.2 fun i j ↦ by
      rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
        ContMDiffRiemannianMetric.pullback_inner]
      exact horth i j
    let b' := b.toOrthonormalBasis hb_orth
    have hb' : b'.toBasis.orientation = o.orientationAt x := by
      rwa [b.toBasis_toOrthonormalBasis]
    rw [isCalibratedImmersion_iff] at h
    have hx := DFunLike.congr_fun (congrFun h x) ⇑b'
    rwa [mpullback_apply, riemannianVolumeForm_apply_orthonormal o x b' hb',
      b.coe_toOrthonormalBasis] at hx
  · intro h
    ext x v
    let := o.fact_finrank_tangentSpace x
    let b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
      (o.orientationAt x).finOrthonormalBasis (NeZero.pos k)
        (by simpa using o.finrank_tangentSpace_eq x)
    have hb : b.toBasis.orientation = o.orientationAt x :=
      (o.orientationAt x).finOrthonormalBasis_orientation (NeZero.pos k) _
    have horth : ∀ i j, g.inner (f x) (mfderiv I' I f x (b.toBasis i))
        (mfderiv I' I f x (b.toBasis j)) = if i = j then 1 else 0 := fun i j ↦ by
      rw [← ContMDiffRiemannianMetric.pullback_inner,
        ← ContMDiffRiemannianMetric.inner_riemannianBundle, b.coe_toBasis]
      exact orthonormal_iff_ite.mp b.orthonormal i j
    have hEq := eq_riemannianVolumeForm_of_apply_orthonormal o x (mpullback I' I f φ x) b hb (by
      rw [mpullback_apply, ← b.coe_toBasis]
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
    let := o.fact_finrank_tangentSpace x
    let b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
      (o.orientationAt x).finOrthonormalBasis (NeZero.pos k)
        (by simpa using o.finrank_tangentSpace_eq x)
    have hb : b.toBasis.orientation = o.orientationAt x :=
      (o.orientationAt x).finOrthonormalBasis_orientation (NeZero.pos k) _
    have horth : ∀ i j, g.inner (f x) (mfderiv I' I f x (b.toBasis i))
        (mfderiv I' I f x (b.toBasis j)) = if i = j then 1 else 0 := fun i j ↦ by
      rw [← ContMDiffRiemannianMetric.pullback_inner,
        ← ContMDiffRiemannianMetric.inner_riemannianBundle, b.coe_toBasis]
      exact orthonormal_iff_ite.mp b.orthonormal i j
    rw [isCalibratedImmersion_iff] at h
    have hval := DFunLike.congr_fun (congrFun h x) ⇑b
    rw [mpullback_apply, riemannianVolumeForm_apply_orthonormal o x b hb, ← b.coe_toBasis] at hval
    exact ⟨b.toBasis, hb, horth, hval⟩
  · intro h
    ext x v
    obtain ⟨b, hb, horth, hval⟩ := h x
    have hb_orth : Orthonormal ℝ b := orthonormal_iff_ite.2 fun i j ↦ by
      rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
        ContMDiffRiemannianMetric.pullback_inner]
      exact horth i j
    let b' := b.toOrthonormalBasis hb_orth
    have hb' : b'.toBasis.orientation = o.orientationAt x := by
      rwa [b.toBasis_toOrthonormalBasis]
    have hEq := eq_riemannianVolumeForm_of_apply_orthonormal o x (mpullback I' I f φ x) b' hb' (by
      rwa [mpullback_apply, b.coe_toOrthonormalBasis])
    exact DFunLike.congr_fun hEq v

open scoped Classical in
/-- In degree zero, an oriented immersion is calibrated by `φ` if and only if `φ (f x) ![]` equals
`1` at positively oriented points of `N` and `-1` at negatively oriented points. -/
theorem isCalibratedImmersion_zeroDim_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ 0) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin 0)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      ∀ x, φ (f x) ![] = if o.orientationAt x = positiveOrientation then 1 else -1 := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff]
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · have hx := DFunLike.congr_fun (congrFun h x) ![]
    rw [mpullback_apply, riemannianVolumeForm_zeroDim_apply,
      Subsingleton.elim (fun i : Fin 0 ↦ mfderiv I' I f x (![] i)) ![]] at hx
    exact hx
  · ext x v
    rw [mpullback_apply, riemannianVolumeForm_zeroDim_apply,
      Subsingleton.elim (fun i : Fin 0 ↦ mfderiv I' I f x (v i)) ![], h x]

/-- An immersion is calibrated for the opposite source orientation `-o` by `φ` if and only if it is
calibrated for `o` by `-φ`. -/
@[simp]
theorem isCalibratedImmersion_neg_right_iff {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj (-o) ↔ IsCalibratedImmersion g (-φ) f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff, isCalibratedImmersion_iff, riemannianVolumeForm_neg,
    ← neg_one_smul ℝ φ, mpullback_smul, neg_one_smul, neg_eq_iff_eq_neg.symm]

/-- If `f` is calibrated by `φ` for `o`, then `f` is calibrated by `-φ` for `-o`. -/
theorem IsCalibratedImmersion.neg {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    IsCalibratedImmersion g (-φ) f hf hinj (-o) := by
  simpa using hcal

/-- For an oriented immersion `f` calibrated by `φ`, `integralTopForm o (mpullback I' I f φ)`
unconditionally equals `immersionVolume g f hf hinj o` (evaluating to the total Riemannian volume on
compact `N` and to `0` on noncompact `N`). -/
theorem IsCalibratedImmersion.integralTopForm_mpullback_eq_immersionVolume {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o := by
  rw [immersionVolume_def]
  exact congrArg (integralTopForm o) hcal

/-- On a compact source `N`, the integral of `f^* φ` along an immersion calibrated by `φ` equals the
total Riemannian volume of `N` equipped with `f^* g`. -/
theorem IsCalibratedImmersion.integralTopForm_mpullback_eq_riemannianTotalVolume [CompactSpace N]
    {k : ℕ} {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    integralTopForm o (mpullback I' I f φ) =
      riemannianTotalVolume I' (WithMetric (g.pullback f (by simpa using hf) hinj)) :=
  hcal.integralTopForm_mpullback_eq_immersionVolume.trans
    (immersionVolume_eq_riemannianTotalVolume g f hf hinj o)

section Transport

variable {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' 1 N']

/-- Precomposing an immersion with any diffeomorphism preserves `immersionVolume` (regardless of
whether the diffeomorphism preserves or reverses orientations). -/
theorem immersionVolume_comp_diffeomorph {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N)
    (o' : Manifold.Orientation I'' N' (Fin k)) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x))) o' =
      immersionVolume g f hf hinj o := by
  let oΦ : Manifold.Orientation I'' N' (Fin k) :=
    o.pullback (Φ.contMDiff.of_le (by simp)) (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o'.card_eq
  have ho : ∀ x, oΦ.IsOrientationPreservingAt o Φ x :=
    o.isOrientationPreservingAt_pullback (Φ.contMDiff.of_le (by simp))
      (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o'.card_eq
  rw [immersionVolume_congr_orientation g (f ∘ Φ) _ _ o' oΦ]
  set gN := g.pullback f (by simpa using hf) hinj
  set gN' := g.pullback (f ∘ Φ) (by simpa using hf.comp Φ.contMDiff)
    (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x)))
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) := ⟨gN'.toRiemannianMetric⟩
  have hvol : mpullback I'' I' Φ (riemannianVolumeForm o) = riemannianVolumeForm oΦ :=
    mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho fun x v w ↦ by
      rw [gN.inner_riemannianBundle, gN'.inner_riemannianBundle]
      exact (g.pullback_comp_inner _ (Φ.mdifferentiable (by simp) x) _ _ _ v w).symm
  rw [immersionVolume_def, immersionVolume_def, ← hvol, ← Φ.coe_toHomeomorph]
  exact Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
    (by simp)

/-- Precomposing a calibrated immersion with an orientation-preserving diffeomorphism gives a
calibrated immersion. -/
theorem IsCalibratedImmersion.comp_diffeomorph_of_isOrientationPreservingAt {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)} (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N) (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationPreservingAt o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
      (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x))) o' := by
  set gN := g.pullback f (by simpa using hf) hinj
  set gN' := g.pullback (f ∘ Φ) (by simpa using hf.comp Φ.contMDiff)
    (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x)))
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) := ⟨gN'.toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff,
    mpullback_comp (Φ.contMDiff.mdifferentiable (by simp)) (hf.mdifferentiable (by simp)),
    (isCalibratedImmersion_iff g φ f hf hinj o).1 hcal]
  exact mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho fun x v w ↦ by
    rw [gN.inner_riemannianBundle, gN'.inner_riemannianBundle]
    exact (g.pullback_comp_inner _ (Φ.mdifferentiable (by simp) x) _ _ _ v w).symm

/-- Precomposing an immersion with an orientation-preserving diffeomorphism preserves
`IsCalibratedImmersion` in both directions. -/
theorem isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N) (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationPreservingAt o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x))) o' ↔
      IsCalibratedImmersion g φ f hf hinj o :=
  ⟨fun h ↦ (isCalibratedImmersion_congr (funext fun y ↦ congrArg f (Φ.apply_symm_apply y))).1
    (h.comp_diffeomorph_of_isOrientationPreservingAt Φ.symm o
      fun y ↦ (ho (Φ.symm y)).diffeomorph_symm (by simp)),
   fun h ↦ h.comp_diffeomorph_of_isOrientationPreservingAt Φ o' ho⟩

end Transport

end Immersions

end TauCeti
