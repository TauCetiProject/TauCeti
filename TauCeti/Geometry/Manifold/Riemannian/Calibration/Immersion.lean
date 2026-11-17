/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
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
* **Foundational examples**: the identity immersion of an oriented Riemannian manifold is calibrated
  by its Riemannian volume form (`TauCeti.isCalibratedImmersion_id_riemannianVolumeForm`), and every
  linear isometric immersion of an oriented inner product space into a finite-dimensional real inner
  product space is calibrated by the associated simple constant calibration
  (`TauCeti.isCalibratedImmersion_linearIsometry_const`).

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157, §II.4.
* D. Joyce, *Lectures on Special Lagrangian Geometry*, arXiv:math/0111111 (2001), §2.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

noncomputable section

open Bundle Set exteriorPower
open scoped Manifold ContDiff Topology

namespace TauCeti

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N]

section VolumeProperties

variable {k : ℕ} (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (φ : RoughForm I M ℝ k) (f : N → M) (hf : ContMDiff I' I ∞ f)
  (hinj : ∀ x, Function.Injective (mfderiv I' I f x)) (o : Manifold.Orientation I' N (Fin k))

/-- The volume of a smooth immersion `f : N → M` of an oriented `k`-manifold: the integral over
`N`, against its orientation `o`, of the Riemannian volume form of the pulled-back metric `f*g`.
It does not depend on the orientation chosen. -/
def immersionVolume : ℝ :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  integralTopForm o (riemannianVolumeForm o)

/-- Unfolding `immersionVolume` as the integral of `riemannianVolumeForm o` for `f*g`. -/
theorem immersionVolume_def :
    immersionVolume g f hf hinj o =
      (letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩;
        integralTopForm o (riemannianVolumeForm o)) := (rfl)

/-- The oriented immersion `f` is calibrated by the `k`-form `φ`: `f*φ` is the Riemannian volume
form of the pulled-back metric `f*g` for the orientation `o` (Harvey–Lawson 1982, §II.4). -/
def IsCalibratedImmersion : Prop :=
  letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  mpullback I' I f φ = riemannianVolumeForm o

/-- Unfolding `IsCalibratedImmersion` as the equality `f*φ = riemannianVolumeForm o` for `f*g`. -/
theorem isCalibratedImmersion_def :
    IsCalibratedImmersion g φ f hf hinj o ↔
      (letI : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
        ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩;
        mpullback I' I f φ = riemannianVolumeForm o) := Iff.rfl

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
  have := Bundle.instIsContMDiffRiemannianBundle gN
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
  have := Bundle.instIsContMDiffRiemannianBundle gN
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
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
  (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
  (Φ : N'' ≃ₘ^∞⟮I'', I'⟯ N)

/-- Reparametrizing an immersion by an orientation-preserving smooth diffeomorphism `Φ` preserves
`IsCalibratedImmersion` (in every dimension `k ≥ 0` and without compactness). -/
theorem isCalibratedImmersion_comp_diffeomorph_iff_of_isOrientationPreservingAt
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
  have := Bundle.instIsContMDiffRiemannianBundle gN
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
  refine abs_le.2 ⟨?_, integralTopForm_mpullback_le_immersionVolume g f hf hinj o hφ⟩
  have hneg := integralTopForm_mpullback_le_immersionVolume g f hf hinj o hφ.neg
  have hmp : mpullback I' I f (-φ) = (-1 : ℝ) • mpullback I' I f φ := by
    simpa only [neg_one_smul] using mpullback_smul (I := I') (I' := I) f (-1 : ℝ) φ
  rw [hmp, integralTopForm_smul] at hneg; linarith

end CalibrationInequality

end Immersions

section Examples

/-- On any oriented Riemannian manifold `(M, g, o)`, the identity immersion `id : M → M` is
calibrated by `riemannianVolumeForm o` in every dimension `m ≥ 0`. -/
theorem isCalibratedImmersion_id_riemannianVolumeForm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {m : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I M (Fin m)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsCalibratedImmersion g (riemannianVolumeForm o) id contMDiff_id
      (fun x ↦ by simpa [mfderiv_id] using Function.injective_id) o := by
  let rb₁ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let hinj : ∀ x : M, Function.Injective (mfderiv I I id x) :=
    fun x ↦ by simpa [mfderiv_id] using Function.injective_id
  let gid := g.pullback id (by simpa using contMDiff_id) hinj
  let rb₂ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨gid.toRiemannianMetric⟩
  rw [isCalibratedImmersion_def]
  exact @mpullback_riemannianVolumeForm_of_isOrientationPreservingAt
    E H M _ _ _ _ I _ _ _ rb₁ m E H M _ _ _ _ I _ _ _ rb₂ o o id
    (Manifold.Orientation.isOrientationPreservingAt_id o) fun x u w ↦ by
      rw [ContMDiffRiemannianMetric.inner_riemannianBundle g,
        ContMDiffRiemannianMetric.inner_riemannianBundle gid,
        ContMDiffRiemannianMetric.pullback_inner]

/-- **Every oriented linear isometric subspace is calibrated**: for any linear isometry
`L : F →ₗᵢ[ℝ] V` from an oriented `k`-dimensional real inner product space `(F, oF)` into a
finite-dimensional real inner product space `V` and any positively oriented orthonormal basis `b` of
`F`, the immersion `L : F → V` is calibrated by the constant simple calibration
`SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))` in every dimension `k ≥ 0`. -/
theorem isCalibratedImmersion_linearIsometry_const
    {F V : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}
    (L : F →ₗᵢ[ℝ] V) (oF : Orientation ℝ F (Fin k))
    (b : OrthonormalBasis (Fin k) ℝ F) (hb : b.toBasis.orientation = oF) :
    IsCalibratedImmersion ((riemannianMetricVectorSpace V).ofLE le_top)
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))).1
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
    let : RiemannianBundle (fun y : V ↦ TangentSpace 𝓘(ℝ, V) y) :=
      ⟨(riemannianMetricVectorSpace V).toRiemannianMetric⟩
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (Eq.symm ?_)
    rw [← real_inner_self_eq_norm_sq, ContMDiffRiemannianMetric.inner_riemannianBundle gF,
      ContMDiffRiemannianMetric.pullback_inner, ContMDiffRiemannianMetric.ofLE_inner,
      ← ContMDiffRiemannianMetric.inner_riemannianBundle (riemannianMetricVectorSpace V),
      real_inner_self_eq_norm_sq, norm_tangentSpace_vectorSpace, hmf, L.norm_map]
  have : Fact (Module.finrank ℝ F = k) := ⟨by simpa using hk.symm⟩
  let A : F [⋀^Fin k]→L[ℝ] ℝ :=
    (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b))).compContinuousLinearMap L.toContinuousLinearMap
  have hAb : A b = 1 := by
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      LinearIsometry.coe_toContinuousLinearMap, alternatingFormEquiv_apply,
      real_inner_self_eq_norm_sq, (L.orthonormal_comp_iff.2 b.orthonormal).norm_ιMulti, one_pow]
  have hAvol : A = oF.volumeFormL := oF.eq_volumeFormL_of_apply_orthonormal A b hb hAb
  rw [isCalibratedImmersion_def]; funext x; ext v
  let := oM.fact_finrank_tangentSpace x
  let e : TangentSpace 𝓘(ℝ, F) x ≃ₗᵢ[ℝ] F :=
    { (NormedSpace.fromTangentSpace x).toLinearEquiv with norm_map' := hnorm x }
  have hlhs : mpullback 𝓘(ℝ, F) 𝓘(ℝ, V) L
      (SmoothForm.const (alternatingFormEquiv V k (ιMulti ℝ k (L ∘ b)))).1 x v = A (e ∘ v) := by
    rw [mpullback_apply, SmoothForm.const_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact congrArg _ (funext fun i ↦ hmf x (v i))
  have hrhs : riemannianVolumeForm oM x v = oF.volumeFormL (e ∘ v) := by
    rw [riemannianVolumeForm_apply, ← Manifold.Orientation.map_orientationAt_model oF hk x,
      Orientation.volumeFormL_apply]
    exact ((oM.orientationAt x).volumeForm_map e (e ∘ v)).symm.trans
      (congrArg _ (funext fun i ↦ (e.symm_apply_apply (v i)).symm))
  rw [hlhs, hrhs, hAvol]

end Examples

end TauCeti
