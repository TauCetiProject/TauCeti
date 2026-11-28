/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Geometry.Calibrated.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Volume
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Calibrated immersions

An oriented smooth immersion `f : N → M` into a Riemannian manifold `(M, g)` is **calibrated** by a
`k`-form `φ` (`TauCeti.IsCalibratedImmersion`) when `f^* φ = dvol_{f^* g}`, the Riemannian volume
form of the pulled-back metric `f^* g`. Integrating `f^* φ` over `N` then recovers the immersion
volume `TauCeti.immersionVolume`
(`TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_immersionVolume`), which agrees with
`TauCeti.riemannianTotalVolume` on compact sources and evaluates to `0` on noncompact sources via
`TauCeti.integralTopForm`'s compact-support convention.

In positive degree, calibration of `(f, o)` is equivalent to `df_x` carrying positively oriented
`(f^* g)_x`-orthonormal bases of `T_x N` to `φ_{f x}`-calibrated frames of `T_{f x} M`
(`TauCeti.isCalibratedImmersion_iff_forall_isCalibratedFrame`,
`TauCeti.isCalibratedImmersion_iff_exists_isCalibratedFrame`), and in every degree `k ≥ 0` forces
`‖φ (f x)‖ = 1` along the image when `φ` is a calibration
(`TauCeti.IsCalibratedImmersion.opNorm_eq_one`). On any oriented Riemannian manifold the identity
map is calibrated by the Riemannian volume form
(`TauCeti.isCalibratedImmersion_id_riemannianVolumeForm`), and every linear isometry from an
oriented `k`-dimensional inner product space into a finite-dimensional real inner product space is
calibrated by its simple constant calibration
(`TauCeti.isCalibratedImmersion_linearIsometry_const`).

## Main definitions

* `TauCeti.IsCalibratedImmersion`: an oriented smooth immersion whose pullback of `φ` equals the
  Riemannian volume form of the pulled-back metric.

## Main results

* `TauCeti.isCalibratedImmersion_iff_forall_orthonormal_basis`,
  `TauCeti.isCalibratedImmersion_iff_exists_orthonormal_basis`,
  `TauCeti.isCalibratedImmersion_iff_forall_isCalibratedFrame`,
  `TauCeti.isCalibratedImmersion_iff_exists_isCalibratedFrame`, and
  `TauCeti.isCalibratedImmersion_zeroDim_iff`: tangent-frame characterizations in positive degree
  and degree zero.
* `TauCeti.IsCalibratedImmersion.one_le_opNorm` and `TauCeti.IsCalibratedImmersion.opNorm_eq_one`:
  along a calibrated immersion, `φ` has comass at least `1`, hence `1` when `φ` is a calibration.
* `TauCeti.IsCalibratedImmersion.neg` and `TauCeti.isCalibratedImmersion_neg_right_iff`:
  orientation-reversal properties.
* `TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_immersionVolume` and
  `TauCeti.IsCalibratedImmersion.integralTopForm_mpullback_eq_riemannianTotalVolume`: integral of
  `f^* φ` along a calibrated immersion.
* `TauCeti.IsCalibratedImmersion.comp_of_isOrientationPreservingAt`,
  `TauCeti.IsCalibratedImmersion.comp_diffeomorph_of_isOrientationPreservingAt`,
  `TauCeti.isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt`, and
  `TauCeti.isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationReversingAt`: behavior of
  `IsCalibratedImmersion` under orientation-preserving and orientation-reversing reparametrizations.
* `TauCeti.isCalibratedImmersion_id_riemannianVolumeForm` and
  `TauCeti.isCalibratedImmersion_linearIsometry_const`: foundational calibrated immersions.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Definition II.4.1 and §II.4.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Definition 2.1.
-/

public section

noncomputable section

open Bundle Manifold exteriorPower
open scoped Bundle ContDiff Manifold RealInnerProductSpace

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

/-- **Calibrated-frame characterization of calibrated immersions (universal form)**: in positive
degree, `(f, o)` is calibrated by `φ` if and only if at every `x : N` and for every positively
oriented `f^* g`-orthonormal basis `b` of `T_x N`, the pushed-forward frame `df_x ∘ b` is calibrated
by `φ (f x)`. -/
theorem isCalibratedImmersion_iff_forall_isCalibratedFrame {k : ℕ} [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
      ∀ (x : N) (b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x)),
        b.toBasis.orientation = o.orientationAt x →
          (φ (f x)).IsCalibratedFrame (mfderiv I' I f x ∘ b) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff_forall_orthonormal_basis]
  refine ⟨fun h x b hb ↦ ?_, fun h x b hb horth ↦ ?_⟩
  · have horth := (g.orthonormal_pullback_iff f hf hinj x b).1 b.orthonormal
    exact ⟨orthonormal_iff_ite.2 fun i j ↦
      (g.inner_riemannianBundle (f x) _ _).trans (horth i j), h x b.toBasis hb
        (by simpa only [OrthonormalBasis.coe_toBasis] using horth)⟩
  · have hb_orth : Orthonormal ℝ b := (g.orthonormal_pullback_iff f hf hinj x b).2 horth
    let bO : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) := b.toOrthonormalBasis hb_orth
    have hbO : bO.toBasis.orientation = o.orientationAt x := by rwa [b.toBasis_toOrthonormalBasis]
    rw [← b.coe_toOrthonormalBasis hb_orth]
    exact (h x bO hbO).apply_eq_one

/-- **Calibrated-frame characterization of calibrated immersions (existential form)**: in positive
degree, `(f, o)` is calibrated by `φ` if and only if every `x : N` admits a positively oriented
`f^* g`-orthonormal basis `b` of `T_x N` whose image `df_x ∘ b` is calibrated by `φ (f x)`. -/
theorem isCalibratedImmersion_iff_exists_isCalibratedFrame {k : ℕ} [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
      ∀ x : N, ∃ b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x),
        b.toBasis.orientation = o.orientationAt x ∧
          (φ (f x)).IsCalibratedFrame (mfderiv I' I f x ∘ b) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_iff_exists_orthonormal_basis]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨b, hb, horth, hval⟩ := h x
    have hb_orth : Orthonormal ℝ b := (g.orthonormal_pullback_iff f hf hinj x b).2 horth
    let bO : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) := b.toOrthonormalBasis hb_orth
    refine ⟨bO, by rwa [b.toBasis_toOrthonormalBasis], ?_⟩
    rw [ContinuousAlternatingMap.isCalibratedFrame_iff, b.coe_toOrthonormalBasis hb_orth]
    exact ⟨orthonormal_iff_ite.2 fun i j ↦ (g.inner_riemannianBundle (f x) _ _).trans (horth i j),
      hval⟩
  · obtain ⟨b, hb, hcal⟩ := h x
    have horth := (g.orthonormal_pullback_iff f hf hinj x b).1 b.orthonormal
    exact ⟨b.toBasis, hb, by simpa only [OrthonormalBasis.coe_toBasis] using horth,
      by simpa only [OrthonormalBasis.coe_toBasis] using hcal.apply_eq_one⟩

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

/-- Along a `φ`-calibrated immersion (in any degree `k ≥ 0`, including `k = 0`), `φ` has comass at
least `1` at every image point `f x`. -/
theorem IsCalibratedImmersion.one_le_opNorm {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (x : N) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    1 ≤ ‖φ (f x)‖ := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun z : N ↦ TangentSpace I' z) :=
    ⟨(g.pullback f hf hinj).toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  let b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex (finCongr Fact.out)
  have horth : Orthonormal ℝ (mfderiv I' I f x ∘ b) := orthonormal_iff_ite.2 fun i j ↦
    (g.inner_riemannianBundle (f x) _ _).trans
      ((g.orthonormal_pullback_iff f hf hinj x b).1 b.orthonormal i j)
  have habs : |φ (f x) (mfderiv I' I f x ∘ b)| = 1 := by
    rw [Function.comp_def, ← mpullback_apply, (isCalibratedImmersion_iff g φ f hf hinj o).1 hcal]
    exact abs_riemannianVolumeForm_apply_orthonormal o x b
  simpa only [Real.norm_eq_abs, habs] using
    ((φ (f x)).opNorm_le_iff_le_orthonormal (norm_nonneg _)).1 le_rfl _ horth

/-- Along a calibrated immersion (in any degree `k ≥ 0`, including `k = 0`) for a calibration `φ`,
the comass of `φ` attains `1` at every image point `f x`. -/
theorem IsCalibratedImmersion.opNorm_eq_one {k : ℕ}
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
    {hinj : ∀ x, Function.Injective (mfderiv I' I f x)}
    {o : Manifold.Orientation I' N (Fin k)}
    (hφ : IsCalibration g φ) (hcal : IsCalibratedImmersion g φ f hf hinj o) (x : N) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    ‖φ (f x)‖ = 1 :=
  le_antisymm (hφ.opNorm_le_one (f x)) (hcal.one_le_opNorm x)

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

/-- Precomposing an immersion with an orientation-reversing diffeomorphism exchanges calibration by
`φ` with calibration by `-φ`. -/
theorem isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationReversingAt {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
    (Φ : N' ≃ₘ^∞⟮I'', I'⟯ N) (o' : Manifold.Orientation I'' N' (Fin k))
    (ho : ∀ x, o'.IsOrientationReversingAt o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.mfderiv_comp_diffeomorph_injective_iff (by simp)).2 (hinj (Φ x))) o' ↔
      IsCalibratedImmersion g (-φ) f hf hinj o := by
  conv_lhs => rw [← neg_neg o', isCalibratedImmersion_neg_right_iff]
  exact isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt g (-φ) f hf hinj o
    Φ (-o') fun x ↦ (o'.isOrientationPreservingAt_neg_left o Φ x).2 (ho x)

end Transport

end Immersions

section Examples

/-- On any oriented Riemannian manifold `(M, g, o)`, the identity immersion `id : M → M` is
calibrated by `riemannianVolumeForm o` in every dimension `m ≥ 0`. -/
theorem isCalibratedImmersion_id_riemannianVolumeForm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] {m : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibratedImmersion g (riemannianVolumeForm o) id contMDiff_id
      (fun _ ↦ by simpa [mfderiv_id] using Function.injective_id) o := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let hid : ContMDiff I I (∞ + 1) (id : M → M) := by simpa using contMDiff_id
  let hinj : ∀ x : M, Function.Injective (mfderiv I I id x) :=
    fun _ ↦ by simpa [mfderiv_id] using Function.injective_id
  rw [isCalibratedImmersion_iff, mpullback_id]
  exact congrArg (fun g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    riemannianVolumeForm o) (g.pullback_id hid hinj).symm

/-- **Every oriented linear isometric subspace is calibrated**: for any linear isometry
`L : F →ₗᵢ[ℝ] V` from an oriented `k`-dimensional real inner product space `(F, oF)` into a
finite-dimensional real inner product space `V` and any positively oriented orthonormal basis `b` of
`F`, the immersion `L : F → V` is calibrated by the constant simple calibration
`SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))` in every dimension `k ≥ 0`. -/
theorem isCalibratedImmersion_linearIsometry_const
    {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (L : F →ₗᵢ[ℝ] V) (oF : _root_.Orientation ℝ F (Fin k))
    (b : OrthonormalBasis (Fin k) ℝ F) (hb : b.toBasis.orientation = oF) :
    IsCalibratedImmersion ((riemannianMetricVectorSpace V).ofLE le_top)
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))).val
      L L.contDiff.contMDiff L.injective_mfderiv
      (Manifold.Orientation.model (I := 𝓘(ℝ, F)) oF
        (Module.finrank_eq_card_basis b.toBasis).symm) := by
  let hk : Fintype.card (Fin k) = Module.finrank ℝ F :=
    (Module.finrank_eq_card_basis b.toBasis).symm
  let gV := (riemannianMetricVectorSpace V).ofLE (le_top : ∞ ≤ ⊤)
  let gF := gV.pullback L (by simpa using L.contDiff.contMDiff) L.injective_mfderiv
  let : RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) := ⟨gF.toRiemannianMetric⟩
  let oM := Manifold.Orientation.model (I := 𝓘(ℝ, F)) oF hk
  have hmf (x : F) (u : TangentSpace 𝓘(ℝ, F) x) :
      NormedSpace.fromTangentSpace (L x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, V) L x u) =
        L (NormedSpace.fromTangentSpace x u) := by
    have hf : fderiv ℝ (L : F → V) x = L.toContinuousLinearMap := L.toContinuousLinearMap.fderiv
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, hf, LinearIsometry.coe_toContinuousLinearMap]
  have hnorm (x : F) (u : TangentSpace 𝓘(ℝ, F) x) :
      ‖(NormedSpace.fromTangentSpace x u : F)‖ = ‖u‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (Eq.symm ?_)
    rw [← real_inner_self_eq_norm_sq, gF.inner_riemannianBundle,
      ContMDiffRiemannianMetric.pullback_inner, ContMDiffRiemannianMetric.ofLE_inner,
      riemannianMetricVectorSpace_inner, hmf, L.inner_map_map, real_inner_self_eq_norm_sq]
  have : Fact (Module.finrank ℝ F = k) := ⟨by simpa using hk.symm⟩
  let A : F [⋀^Fin k]→L[ℝ] ℝ :=
    (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b))).compContinuousLinearMap L.toContinuousLinearMap
  have hAb : A b = 1 := by
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      LinearIsometry.coe_toContinuousLinearMap]
    exact (L.orthonormal_comp_iff.2 b.orthonormal).isCalibratedFrame_alternatingFormEquiv_ιMulti
      |>.apply_eq_one
  have hAvol : A = oF.volumeFormL := oF.eq_volumeFormL_of_apply_orthonormal A b hb hAb
  rw [isCalibratedImmersion_iff]; funext x; ext v
  let := oM.fact_finrank_tangentSpace x
  let e : TangentSpace 𝓘(ℝ, F) x ≃ₗᵢ[ℝ] F :=
    { (NormedSpace.fromTangentSpace x).toLinearEquiv with norm_map' := hnorm x }
  have hlhs : mpullback 𝓘(ℝ, F) 𝓘(ℝ, V) L
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))).val x v = A (e ∘ v) := by
    rw [mpullback_apply, SmoothForm.const_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact congrArg _ (funext fun i ↦ hmf x (v i))
  have hrhs : riemannianVolumeForm oM x v = oF.volumeFormL (e ∘ v) := by
    rw [riemannianVolumeForm_apply, ← Manifold.Orientation.map_orientationAt_model oF hk x,
      _root_.Orientation.volumeFormL_apply]
    exact ((oM.orientationAt x).volumeForm_map e (e ∘ v)).symm.trans
      (congrArg _ (funext fun i ↦ (e.symm_apply_apply (v i)).symm))
  rw [hlhs, hrhs, hAvol]

end Examples

end TauCeti
