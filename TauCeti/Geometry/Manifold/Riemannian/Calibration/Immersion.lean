/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Calibration.Basic
public import TauCeti.Geometry.Manifold.Riemannian.TopFormDensity
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Integral
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Pullback
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# Immersed Riemannian volume and calibrated immersions

Let `(M, g)` be a smooth Riemannian manifold and `f : N → M` be a smooth immersion of an oriented
`k`-manifold `(N, o)`. Equipping `N` with the pullback metric `f*g`
(`Bundle.ContMDiffRiemannianMetric.pullback`) gives an oriented Riemannian manifold whose volume
form is `riemannianVolumeForm o`.

* The *immersed volume* `TauCeti.immersionVolume g f hf hinj o` is the top-form integral over `N` of
  the Riemannian volume form of `f*g`. It is nonnegative in every dimension, vanishes on noncompact
  sources (`TauCeti.immersionVolume_eq_zero_of_not_compactSpace`), is independent of orientation
  (`TauCeti.immersionVolume_neg_orientation`, `TauCeti.immersionVolume_orientation_congr`),
  and on a compact source `N` coincides with the orientation-free total Riemannian volume
  `TauCeti.riemannianTotalVolume` (`TauCeti.immersionVolume_eq_riemannianTotalVolume`), being
  strictly positive when `N` is nonempty (`TauCeti.immersionVolume_pos`).
* The immersion `(f, o)` is *calibrated* by a `k`-form `φ` (`TauCeti.IsCalibratedImmersion`) when
  `mpullback I' I f φ = riemannianVolumeForm o` for `f*g`. Reversing the orientation exchanges
  calibration by `φ` with calibration by `-φ` (`TauCeti.isCalibratedImmersion_neg_orientation_iff`).
  In positive dimension `1 ≤ k`, calibration of `(f, o)` is equivalent to `df_x` mapping positively
  oriented `(f*g)_x`-orthonormal bases of `T_x N` to `φ_{f x}`-calibrated frames of `T_{f x} M`
  (`TauCeti.isCalibratedImmersion_iff_forall_isCalibratedFrame`,
  `TauCeti.isCalibratedImmersion_iff_exists_isCalibratedFrame`), and forces `‖φ (f x)‖ = 1` along
  the image when `φ` is a calibration (`TauCeti.IsCalibratedImmersion.norm_eq_one`).
* **Integrated calibration inequality**: applying the top-form Hodge density decomposition
  (`TauCeti.eq_topFormDensity_smul_riemannianVolumeForm`) to `f*φ` for a calibration `φ` yields
  `|∫_N f*φ| ≤ immersionVolume g f hf hinj o` on compact sources `N` (possibly with boundary or
  corners, in every dimension `k ≥ 0`; `TauCeti.integralTopForm_mpullback_le_immersionVolume` and
  `TauCeti.abs_integralTopForm_mpullback_le_immersionVolume`).
* **Reparametrization invariance**: `immersionVolume` and `IsCalibratedImmersion` are natural under
  smooth diffeomorphisms `Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N`, allowing distinct model spaces `E''` and `E'`
  and without compactness assumptions (`TauCeti.immersionVolume_comp_diffeomorph`).

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157, §II.4.
* D. Joyce, *Lectures on Special Lagrangian Geometry*, arXiv:math/0111111 (2001), §2.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace TauCeti

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N]

/-- The volume of a smooth immersion `f : N → M` of an oriented `k`-manifold: the integral over
`N`, against its orientation `o`, of the Riemannian volume form of the pulled-back metric `f*g`.
It does not depend on the orientation chosen. -/
def immersionVolume {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : ℝ :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  integralTopForm o (riemannianVolumeForm o)

/-- Unfolding `immersionVolume` as the integral of `riemannianVolumeForm o` for `f*g`. -/
theorem immersionVolume_def {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o =
      (letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩;
        integralTopForm o (riemannianVolumeForm o)) := (rfl)

/-- The oriented immersion `f` is calibrated by the `k`-form `φ`: `f*φ` is the Riemannian volume
form of the pulled-back metric `f*g` for the orientation `o` (Harvey–Lawson 1982, §II.4). -/
def IsCalibratedImmersion {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) : Prop :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  mpullback I' I f φ = riemannianVolumeForm o

/-- Unfolding `IsCalibratedImmersion` as the equality `f*φ = riemannianVolumeForm o` for `f*g`. -/
theorem isCalibratedImmersion_def {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      (letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩;
        mpullback I' I f φ = riemannianVolumeForm o) := Iff.rfl

section VolumeProperties

variable {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
  (o : Manifold.Orientation I' N (Fin k))

/-- Reversing the orientation leaves `immersionVolume` unchanged, without any compactness
assumption. -/
@[simp]
theorem immersionVolume_neg_orientation :
    immersionVolume g f hf hinj (-o) = immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def, immersionVolume_def, riemannianVolumeForm_neg, ← neg_one_smul ℝ,
    integralTopForm_neg, integralTopForm_smul]; ring

/-- The immersed volume is nonnegative in every dimension `k ≥ 0`, without any compactness
assumption. -/
theorem immersionVolume_nonneg : 0 ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  simpa only [one_smul] using integralTopForm_smul_riemannianVolumeForm_nonneg o
    (f := fun _ : N ↦ (1 : ℝ)) fun _ ↦ zero_le_one

/-- On a noncompact source `N`, `immersionVolume` vanishes because the Riemannian volume form is
nowhere zero and therefore does not have compact support. -/
theorem immersionVolume_eq_zero_of_not_compactSpace (hN : ¬CompactSpace N) :
    immersionVolume g f hf hinj o = 0 := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  exact integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o hN

/-- On a compact source `N`, `immersionVolume` agrees with the orientation-free total Riemannian
volume `riemannianTotalVolume` of the pullback metric `f*g`. -/
theorem immersionVolume_eq_riemannianTotalVolume [CompactSpace N] :
    immersionVolume g f hf hinj o =
      (letI : MeasurableSpace N := borel N
       haveI : BorelSpace N := ⟨rfl⟩
       letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
         ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       haveI : IsContMDiffRiemannianBundle I' ∞ E' (fun x : N ↦ TangentSpace I' x) :=
         Bundle.instIsContMDiffRiemannianBundle (g.pullback f (by simpa using hf) hinj)
       haveI : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
         IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
       riemannianTotalVolume I' N) := by
  let : MeasurableSpace N := borel N; have : BorelSpace N := ⟨rfl⟩
  let gN := g.pullback f (by simpa using hf) hinj
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I' ∞ E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  exact integralTopForm_riemannianVolumeForm o

/-- On any source `N` (compact or noncompact, connected or disconnected), `immersionVolume` is
independent of the choice of orientation on `N`. -/
theorem immersionVolume_orientation_congr (o₁ o₂ : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g f hf hinj o₁ = immersionVolume g f hf hinj o₂ := by
  by_cases hN : CompactSpace N
  · rw [immersionVolume_eq_riemannianTotalVolume g f hf hinj o₁,
      immersionVolume_eq_riemannianTotalVolume g f hf hinj o₂]
  · rw [immersionVolume_eq_zero_of_not_compactSpace g f hf hinj o₁ hN,
      immersionVolume_eq_zero_of_not_compactSpace g f hf hinj o₂ hN]

/-- The immersed volume of a nonempty compact oriented `k`-manifold is strictly positive in every
dimension `k ≥ 0`. -/
theorem immersionVolume_pos [CompactSpace N] [Nonempty N] :
    0 < immersionVolume g f hf hinj o := by
  let : MeasurableSpace N := borel N; have : BorelSpace N := ⟨rfl⟩
  let gN := g.pullback f (by simpa using hf) hinj
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I' ∞ E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  rw [immersionVolume_eq_riemannianTotalVolume]; exact riemannianTotalVolume_pos (I := I') (M := N)

end VolumeProperties

section CalibratedImmersionProperties

variable {k : ℕ} {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {φ : RoughForm I M ℝ k} {f : N → M} {hf : ContMDiff I' I ∞ f}
  {hinj : ∀ x, Function.Injective (mfderiv I' I f x)} {o : Manifold.Orientation I' N (Fin k)}

/-- Integrating `f*φ` over a `φ`-calibrated immersion recovers its immersed volume. -/
theorem IsCalibratedImmersion.integralTopForm_mpullback_eq
    (hcal : IsCalibratedImmersion g φ f hf hinj o) :
    integralTopForm o (mpullback I' I f φ) = immersionVolume g f hf hinj o := by
  rw [immersionVolume_def, (isCalibratedImmersion_def g φ f hf hinj o).1 hcal]

/-- Reversing the orientation on `N` exchanges calibration by `φ` with calibration by `-φ`. -/
@[simp]
theorem isCalibratedImmersion_neg_orientation_iff :
    IsCalibratedImmersion g φ f hf hinj (-o) ↔ IsCalibratedImmersion g (-φ) f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have hneg : mpullback I' I f (-φ) = -mpullback I' I f φ := by
    simpa only [neg_one_smul] using mpullback_smul (I := I') (I' := I) f (-1 : ℝ) φ
  rw [isCalibratedImmersion_def, isCalibratedImmersion_def, riemannianVolumeForm_neg, hneg,
    neg_eq_iff_eq_neg]

/-- **Frame characterization of calibrated immersions (universal form)**: in positive dimension
`1 ≤ k`, `(f, o)` is calibrated by `φ` if and only if at every `x : N` and for every positively
oriented `(f*g)_x`-orthonormal basis `b` of `T_x N`, the pushed-forward frame `df_x ∘ b` is a
`φ_{f x}`-calibrated frame of `T_{f x} M`. -/
theorem isCalibratedImmersion_iff_forall_isCalibratedFrame (hk : 1 ≤ k) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
       letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
         ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       ∀ (x : N) (b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x)),
         b.toBasis.orientation = o.orientationAt x →
           IsCalibratedFrame (φ (f x)) (mfderiv I' I f x ∘ b)) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [isCalibratedImmersion_def]
  refine ⟨fun h x b hb ↦ (isCalibratedFrame_def _ _).2
    ⟨(g.orthonormal_mfderiv_comp_iff f (by simpa using hf) hinj x b).2 b.orthonormal, ?_⟩,
    fun h ↦ funext fun x ↦ ?_⟩
  · have hval := congrArg (fun α : TangentSpace I' x [⋀^Fin k]→L[ℝ] ℝ ↦ α b) (congrFun h x)
    rwa [mpullback_apply, riemannianVolumeForm_apply_orthonormal o x b hb] at hval
  · let := o.fact_finrank_tangentSpace x
    let b := (o.orientationAt x).finOrthonormalBasis hk Fact.out
    have hb := (o.orientationAt x).finOrthonormalBasis_orientation hk Fact.out
    refine eq_riemannianVolumeForm_of_apply_orthonormal o x _ b hb ?_
    simpa only [mpullback_apply, Function.comp_def] using (h x b hb).apply_eq_one

/-- **Frame characterization of calibrated immersions (existential form)**: in positive dimension
`1 ≤ k`, `(f, o)` is calibrated by `φ` if and only if every `x : N` admits a positively oriented
`(f*g)_x`-orthonormal basis `b` of `T_x N` whose image `df_x ∘ b` is calibrated by `φ_{f x}`. -/
theorem isCalibratedImmersion_iff_exists_isCalibratedFrame (hk : 1 ≤ k) :
    IsCalibratedImmersion g φ f hf hinj o ↔
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
       letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
         ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
       ∀ x : N, ∃ b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x),
         b.toBasis.orientation = o.orientationAt x ∧
           IsCalibratedFrame (φ (f x)) (mfderiv I' I f x ∘ b)) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  refine ⟨fun h x ↦ ?_, fun h ↦ (isCalibratedImmersion_def g φ f hf hinj o).2 (funext fun x ↦ ?_)⟩
  · let := o.fact_finrank_tangentSpace x
    let b := (o.orientationAt x).finOrthonormalBasis hk Fact.out
    have hb := (o.orientationAt x).finOrthonormalBasis_orientation hk Fact.out
    exact ⟨b, hb, (isCalibratedImmersion_iff_forall_isCalibratedFrame hk).1 h x b hb⟩
  · obtain ⟨b, hb, hcal⟩ := h x
    refine eq_riemannianVolumeForm_of_apply_orthonormal o x _ b hb ?_
    simpa only [mpullback_apply, Function.comp_def] using hcal.apply_eq_one

/-- Along a `φ`-calibrated immersion (in any dimension `k ≥ 0`, including `k = 0`), `φ` has comass
at least `1` at every image point `f x`. -/
theorem IsCalibratedImmersion.one_le_norm
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (x : N) :
    1 ≤ (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖φ (f x)‖) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun z : N ↦ TangentSpace I' z) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  let b : OrthonormalBasis (Fin k) ℝ (TangentSpace I' x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex (finCongr Fact.out)
  have horth := (g.orthonormal_mfderiv_comp_iff f (by simpa using hf) hinj x b).2 b.orthonormal
  have habs : |φ (f x) (mfderiv I' I f x ∘ b)| = 1 := by
    rw [Function.comp_def, ← mpullback_apply, (isCalibratedImmersion_def g φ f hf hinj o).1 hcal]
    exact abs_riemannianVolumeForm_apply_orthonormal o x b
  simpa only [Real.norm_eq_abs, habs] using
    ((φ (f x)).opNorm_le_iff_le_orthonormal (norm_nonneg _)).1 le_rfl _ horth

/-- Along a calibrated immersion (in any dimension `k ≥ 0`, including `k = 0`) for a calibration
`φ`, the comass of `φ` attains `1` at every image point `f x`. -/
theorem IsCalibratedImmersion.norm_eq_one (hφ : IsCalibration g φ)
    (hcal : IsCalibratedImmersion g φ f hf hinj o) (x : N) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖φ (f x)‖) = 1 :=
  le_antisymm (hφ.norm_le_one (f x)) (hcal.one_le_norm x)

end CalibratedImmersionProperties

section Reparametrization

variable {E'' H'' N'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E''] [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace N''] [ChartedSpace H'' N''] [IsManifold I'' ∞ N''] {k : ℕ}

/-- Reparametrizing an immersion by an orientation-preserving smooth diffeomorphism `Φ` preserves
`IsCalibratedImmersion` (in every dimension `k ≥ 0` and without compactness). -/
theorem isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N)
    {o'' : Manifold.Orientation I'' N'' (Fin k)} {o : Manifold.Orientation I' N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o'' o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.injective_mfderiv_comp_diffeomorph_iff (by simp) f x).2 (hinj (Φ x))) o'' ↔
      IsCalibratedImmersion g φ f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N'' ↦ TangentSpace I'' x) :=
    ⟨(g.pullback (f ∘ Φ) (by simpa using hf.comp Φ.contMDiff)
      fun x ↦ (Φ.injective_mfderiv_comp_diffeomorph_iff (by simp) f x).2
        (hinj (Φ x))).toRiemannianMetric⟩
  rw [isCalibratedImmersion_def, isCalibratedImmersion_def,
    mpullback_comp (Φ.contMDiff.mdifferentiable (by simp)) (hf.mdifferentiable (by simp)) φ,
    ← mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho
      (g.inner_mfderiv_pullback_comp (by simpa using hf) (by simpa using Φ.contMDiff) hinj _)]
  exact (mpullback_injective_of_surjective Φ.surjective
    fun x ↦ (Φ.isInvertible_mfderiv (by simp)).surjective).eq_iff

/-- Reparametrizing an immersion by an orientation-reversing smooth diffeomorphism `Φ` exchanges
calibration by `φ` with calibration by `-φ`. -/
theorem isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationReversingAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N)
    {o'' : Manifold.Orientation I'' N'' (Fin k)} {o : Manifold.Orientation I' N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt o'' o Φ x) :
    IsCalibratedImmersion g φ (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.injective_mfderiv_comp_diffeomorph_iff (by simp) f x).2 (hinj (Φ x))) o'' ↔
      IsCalibratedImmersion g (-φ) f hf hinj o := by
  conv_lhs => rw [← neg_neg o'', isCalibratedImmersion_neg_orientation_iff]
  exact isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt g (-φ) f hf hinj Φ
    fun x ↦ (Manifold.Orientation.isOrientationPreservingAt_neg_left o'' o Φ x).2 (ho x)

/-- Reparametrizing an immersion by an orientation-preserving smooth diffeomorphism `Φ` preserves
`immersionVolume` without any compactness assumption. -/
theorem immersionVolume_comp_diffeomorph_of_isOrientationPreservingAt
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N)
    {o'' : Manifold.Orientation I'' N'' (Fin k)} {o : Manifold.Orientation I' N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o'' o Φ x) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.injective_mfderiv_comp_diffeomorph_iff (by simp) f x).2 (hinj (Φ x))) o'' =
      immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : N'' ↦ TangentSpace I'' x) :=
    ⟨(g.pullback (f ∘ Φ) (by simpa using hf.comp Φ.contMDiff)
      fun x ↦ (Φ.injective_mfderiv_comp_diffeomorph_iff (by simp) f x).2
        (hinj (Φ x))).toRiemannianMetric⟩
  rw [immersionVolume_def, immersionVolume_def,
    ← mpullback_riemannianVolumeForm_of_isOrientationPreservingAt ho
      (g.inner_mfderiv_pullback_comp (by simpa using hf) (by simpa using Φ.contMDiff) hinj _)]
  exact Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
    (by simp)

/-- **Diffeomorphism invariance of immersed volume**: reparametrizing an immersion by any smooth
diffeomorphism `Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N` preserves `immersionVolume` for any orientations `o''` of
`N''` and `o` of `N` (compact or noncompact, even across disconnected components or distinct model
spaces `E''` and `E'`). -/
theorem immersionVolume_comp_diffeomorph
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N)
    (o'' : Manifold.Orientation I'' N'' (Fin k)) (o : Manifold.Orientation I' N (Fin k)) :
    immersionVolume g (f ∘ Φ) (hf.comp Φ.contMDiff)
        (fun x ↦ (Φ.injective_mfderiv_comp_diffeomorph_iff (by simp) f x).2 (hinj (Φ x))) o'' =
      immersionVolume g f hf hinj o := by
  let oPull := o.pullback (Φ.contMDiff.of_le (by simp))
    (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o''.card_eq
  have ho := Manifold.Orientation.isOrientationPreservingAt_pullback o (Φ.contMDiff.of_le (by simp))
    (fun x ↦ Φ.isInvertible_mfderiv (by simp)) o''.card_eq
  rw [immersionVolume_orientation_congr g (f ∘ Φ) _ _ o'' oPull,
    immersionVolume_comp_diffeomorph_of_isOrientationPreservingAt g f hf hinj Φ ho]

end Reparametrization

section CalibrationInequality

variable {k : ℕ} [CompactSpace N]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {φ : RoughForm I M ℝ k}
  (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
  (o : Manifold.Orientation I' N (Fin k))

/-- **Integrated calibration inequality**: for any smooth calibration `φ` on `(M, g)` and any
smooth immersion `f : N → M` of a compact oriented `k`-manifold (possibly with boundary or corners,
and in every dimension `k ≥ 0`), `∫_N f*φ ≤ immersionVolume g f hf hinj o`. -/
theorem integralTopForm_mpullback_le_immersionVolume (hφ : IsCalibration g φ) :
    integralTopForm o (mpullback I' I f φ) ≤ immersionVolume g f hf hinj o := by
  let gN := g.pullback f (by simpa using hf) hinj
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I' ∞ E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.instIsContMDiffRiemannianBundle gN
  have : IsContinuousRiemannianBundle E' (fun x : N ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
  have : IsContMDiffRiemannianBundle I' 0 E' (fun x : N ↦ TangentSpace I' x) :=
    Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsManifold I' (∞ + 1) N := by simpa using (inferInstance : IsManifold I' ∞ N)
  have hpull := hφ.mpullback f hf hinj
  have hcont := (hpull.isSmoothForm.contMDiff_topFormDensity o).continuous
  have hle (x : N) :=
    (le_abs_self _).trans ((abs_topFormDensity o _ x).trans_le (hpull.norm_le_one x))
  rw [eq_topFormDensity_smul_riemannianVolumeForm o (mpullback I' I f φ), immersionVolume_def]
  simpa only [one_smul] using
    integralTopForm_smul_riemannianVolumeForm_mono o hcont continuous_const hle

/-- **Two-sided integrated calibration inequality**: on a compact oriented `k`-manifold `N`,
`|∫_N f*φ| ≤ immersionVolume g f hf hinj o` for every calibration `φ` on `(M, g)`. -/
theorem abs_integralTopForm_mpullback_le_immersionVolume (hφ : IsCalibration g φ) :
    |integralTopForm o (mpullback I' I f φ)| ≤ immersionVolume g f hf hinj o := by
  rw [abs_le]
  refine ⟨?_, integralTopForm_mpullback_le_immersionVolume g f hf hinj o hφ⟩
  have hneg := integralTopForm_mpullback_le_immersionVolume g f hf hinj o hφ.neg
  have hmp : mpullback I' I f (-φ) = (-1 : ℝ) • mpullback I' I f φ := by
    simpa only [neg_one_smul] using mpullback_smul (I := I') (I' := I) f (-1 : ℝ) φ
  rw [hmp, integralTopForm_smul] at hneg; linarith

end CalibrationInequality

end Immersions

end TauCeti
