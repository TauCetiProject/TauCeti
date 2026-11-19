/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Volume

/-!
# Calibrated immersions

An oriented smooth immersion `f : N → M` into a Riemannian manifold `(M, g)` is **calibrated** by a
`k`-form `φ` (`TauCeti.IsCalibratedImmersion`) when `f^* φ = dvol_{f^* g}`, the Riemannian volume
form of the pulled-back metric `f^* g`. Integrating `f^* φ` over `N` then recovers the immersion
volume `TauCeti.immersionVolume`
(`TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_immersionVolume`), which agrees with
`TauCeti.riemannianTotalVolume` on compact sources and evaluates to `0` on noncompact sources via
`TauCeti.integralTopForm`'s compact-support convention.

## Main definitions

* `TauCeti.IsCalibratedImmersion`: an oriented smooth immersion whose pullback of `φ` equals the
  Riemannian volume form of the pulled-back metric.

## Main results

* `TauCeti.isCalibratedImmersion_iff_forall_orthonormal_basis`,
  `TauCeti.isCalibratedImmersion_iff_exists_orthonormal_basis`, and
  `TauCeti.isCalibratedImmersion_zeroDim_iff`: tangent-frame characterizations in positive degree
  and degree zero.
* `TauCeti.IsCalibratedImmersion.neg` and `TauCeti.isCalibratedImmersion_neg_right_iff`:
  orientation-reversal properties.
* `TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_immersionVolume` and
  `TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_riemannianTotalVolume`: integral of
  `f^* φ` along a calibrated immersion.
* `TauCeti.IsCalibratedImmersion.comp_of_isOrientationPreservingAt`,
  `TauCeti.IsCalibratedImmersion.comp_diffeomorph_of_isOrientationPreservingAt`, and
  `TauCeti.isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt`: invariance of
  `IsCalibratedImmersion` under orientation-preserving smooth maps and diffeomorphisms of the
  source.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Definition 2.1.
-/

public section

noncomputable section

open Bundle Manifold
open scoped Bundle ContDiff Manifold

namespace TauCeti

/-! ### Calibrated immersions -/

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]

/-- The oriented immersion `f` is calibrated by the `k`-form `φ`: `f^* φ` is the Riemannian volume
form of the pulled-back metric `f^* g` for the orientation `o`. -/
def IsCalibratedImmersion {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : Prop :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  mpullback I' I f φ = riemannianVolumeForm o

/-- Unfolding lemma for `IsCalibratedImmersion`. -/
theorem isCalibratedImmersion_iff {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
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
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  constructor
  · intro h x b hb horth
    have hx := DFunLike.congr_fun
      (congrFun ((isCalibratedImmersion_iff g φ f hf hinj o).1 h) x) ⇑b
    rwa [mpullback_apply, riemannianVolumeForm_apply_of_orthonormal o x b hb
      ((g.orthonormal_pullback_iff f hf hinj x b).2 horth)] at hx
  · intro h
    rw [isCalibratedImmersion_iff]
    ext x v
    obtain ⟨b, hb, hb_orth⟩ := o.exists_basis_orientationAt_eq_and_orthonormal x
    have hEq := eq_riemannianVolumeForm_of_apply_of_orthonormal o x (mpullback I' I f φ x) b hb
      hb_orth <| by
        rw [mpullback_apply]
        exact h x b hb ((g.orthonormal_pullback_iff f hf hinj x b).1 hb_orth)
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
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  constructor
  · intro h x
    obtain ⟨b, hb, hb_orth⟩ := o.exists_basis_orientationAt_eq_and_orthonormal x
    have horth := (g.orthonormal_pullback_iff f hf hinj x b).1 hb_orth
    exact ⟨b, hb, horth,
      (isCalibratedImmersion_iff_forall_orthonormal_basis g φ f hf hinj o).1 h x b hb horth⟩
  · intro h
    rw [isCalibratedImmersion_iff]
    ext x v
    obtain ⟨b, hb, horth, hval⟩ := h x
    have hEq := eq_riemannianVolumeForm_of_apply_of_orthonormal o x (mpullback I' I f φ x) b hb
      ((g.orthonormal_pullback_iff f hf hinj x b).2 horth)
      (by rwa [mpullback_apply])
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
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
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
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
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
  exact congrArg (integralTopForm o) ((isCalibratedImmersion_iff g φ f hf hinj o).1 hcal)

/-- On a compact source `N`, the integral of `f^* φ` along an immersion calibrated by `φ` equals the
total Riemannian volume of `N` equipped with `f^* g`. -/
theorem IsCalibratedImmersion.integralTopForm_mpullback_eq_riemannianTotalVolume [CompactSpace N]
    {k : ℕ} {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    integralTopForm o (mpullback I' I f φ) =
      riemannianTotalVolume I' (WithMetric (g.pullback f hf hinj)) :=
  hcal.integralTopForm_mpullback_eq_immersionVolume.trans
    (immersionVolume_eq_riemannianTotalVolume g f hf hinj o)

section Transport

variable {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N'] [ChartedSpace H'' N'] [IsManifold I'' 1 N']

/-- Precomposing a calibrated immersion with any smooth map that preserves orientations everywhere
gives a calibrated immersion. -/
theorem IsCalibratedImmersion.comp_of_isOrientationPreservingAt {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)} (hcal : IsCalibratedImmersion g φ f hf hinj o)
    {h : N' → N} (hh : ContMDiff I'' I' ∞ h) (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationPreservingAt o h x) :
    IsCalibratedImmersion g φ (f ∘ h) (hf.comp hh)
      (fun x ↦ mfderiv_comp x (hf.mdifferentiable (by simp) (h x))
        (hh.mdifferentiable (by simp) x) ▸
          (hinj (h x)).comp (ho x).isInvertible_mfderiv.injective) o' := by
  let hinj' : ∀ x, Function.Injective (mfderiv I'' I (f ∘ h) x) :=
    fun x ↦ mfderiv_comp x (hf.mdifferentiable (by simp) (h x))
      (hh.mdifferentiable (by simp) x) ▸
        (hinj (h x)).comp (ho x).isInvertible_mfderiv.injective
  set gN := g.pullback f hf hinj
  set gN' := g.pullback (f ∘ h) (hf.comp hh) hinj'
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N' ↦ TangentSpace I'' x) := ⟨gN'.toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff,
    mpullback_comp (hh.mdifferentiable (by simp)) (hf.mdifferentiable (by simp)),
    (isCalibratedImmersion_iff g φ f hf hinj o).1 hcal]
  exact mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho fun x v w ↦ by
    rw [gN.inner_riemannianBundle, gN'.inner_riemannianBundle]
    exact (g.pullback_comp_inner _ (hh.mdifferentiable (by simp) x) _ _ _ v w).symm

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
      (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x))) o' :=
  (isCalibratedImmersion_congr rfl).1
    (hcal.comp_of_isOrientationPreservingAt Φ.contMDiff o' ho)

/-- Precomposing an immersion with an orientation-preserving diffeomorphism preserves
`IsCalibratedImmersion` in both directions. -/
theorem isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
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
