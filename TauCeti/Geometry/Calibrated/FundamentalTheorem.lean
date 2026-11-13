/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Calibrated.Basic
public import TauCeti.Geometry.Calibrated.Immersion
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The fundamental theorem of calibrations

On any oriented smooth immersion `f : N → M`, a form `φ` of pointwise comass at most `1` satisfies
the pointwise calibration inequality `|f^* φ(c)| ≤ dvol_{f^* g}(c)` on every positively oriented
tangent basis `c`, and hence the integrated calibration inequality `∫_N f^* φ ≤ Vol(f)` whenever
the forms are integrable (in particular on compact sources). Combining this inequality with
closedness of a calibration `φ` yields the **fundamental theorem of calibrations** for closed
sources: calibrated immersions minimize Riemannian volume within their real homology class, and
equality holds if and only if the competing immersion is itself calibrated by `φ`. Both theorems
hold in every degree `k : ℕ`, including degree zero.

## Main results

* `TauCeti.abs_mpullback_apply_le_riemannianVolumeForm` and
  `TauCeti.mpullback_apply_le_riemannianVolumeForm`: pointwise calibration inequalities in positive
  degree.
* `TauCeti.immersionVolume_nonneg` and `TauCeti.immersionVolume_pos`: nonnegativity of immersion
  volume and positivity on nonempty compact sources.
* `TauCeti.integralTopForm_mpullback_le_immersionVolume_of_integrable`,
  `TauCeti.integralTopForm_mpullback_le_immersionVolume`, and
  `TauCeti.abs_integralTopForm_mpullback_le_immersionVolume`: integrated calibration inequalities.
* `TauCeti.immersionVolume_le_of_isCalibratedImmersion`: the fundamental theorem of calibrations
  for closed sources.
* `TauCeti.immersionVolume_eq_iff_isCalibratedImmersion`: equality holds iff the competitor is
  calibrated.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem II.4.2.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2** (2005), arXiv:math/0111111v3, Theorem 2.2.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998), 705–747.
-/

public section

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Bundle ContDiff Manifold

namespace TauCeti

section Immersions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]

/-! ### Pointwise and integrated calibration inequalities -/

/-- **Pointwise calibration inequality** on an oriented immersion of positive dimension: if `φ` has
pointwise comass at most `1` for `g`, then `|f^* φ(c)| ≤ dvol_{f^* g}(c)` on every positively
oriented tangent basis `c` of `T_x N`. -/
theorem abs_mpullback_apply_le_riemannianVolumeForm {k : ℕ} [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I' x)) (hc : c.orientation = o.orientationAt x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    |mpullback I' I f φ x c| ≤ riemannianVolumeForm o x c := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  let := o.fact_finrank_tangentSpace x
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  let b : OrthonormalBasis (Fin (m + 1)) ℝ (TangentSpace I' x) :=
    ((stdOrthonormalBasis ℝ (TangentSpace I' x)).reindex
      (finCongr (by simpa using o.finrank_tangentSpace_eq x))).adjustToOrientation
      (o.orientationAt x)
  have hb : b.toBasis.orientation = o.orientationAt x :=
    OrthonormalBasis.orientation_adjustToOrientation _ _
  have hpos : 0 < b.toBasis.det c := by
    rw [← Module.Basis.orientation_eq_iff_det_pos]
    exact hb.trans hc.symm
  have hφb : |mpullback I' I f φ x b| ≤ 1 := by
    rw [mpullback_apply]
    exact hcomass (f x) (mfderiv I' I f x ∘ b) fun i j ↦ by
      dsimp only [Function.comp_apply]
      rw [← ContMDiffRiemannianMetric.pullback_inner,
        ← ContMDiffRiemannianMetric.inner_riemannianBundle]
      exact orthonormal_iff_ite.mp b.orthonormal i j
  have h1 := ContinuousAlternatingMap.apply_eq_det_mul (mpullback I' I f φ x) b.toBasis c
  have h2 := ContinuousAlternatingMap.apply_eq_det_mul (riemannianVolumeForm o x) b.toBasis c
  rw [show (riemannianVolumeForm o x) b.toBasis = 1 from
    riemannianVolumeForm_apply_orthonormal o x b hb, mul_one] at h2
  rw [h1, h2, abs_mul, abs_of_pos hpos]
  exact mul_le_of_le_one_right hpos.le (by simpa using hφb)

/-- Signed pointwise calibration inequality in positive dimension: `f^* φ(c) ≤ dvol_{f^* g}(c)`
on every positively oriented tangent basis `c` of `T_x N`. -/
theorem mpullback_apply_le_riemannianVolumeForm {k : ℕ} [NeZero k]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (x : N)
    (c : Module.Basis (Fin k) ℝ (TangentSpace I' x)) (hc : c.orientation = o.orientationAt x) :
    letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
    mpullback I' I f φ x c ≤ riemannianVolumeForm o x c :=
  (le_abs_self _).trans
    (abs_mpullback_apply_le_riemannianVolumeForm g hcomass f hf hinj o x c hc)

section ZeroDimHelper

open Classical in
/-- On a compact zero-dimensional manifold, compute the integral of a rough `0`-form as a finite
sum over a disjoint chart partition. -/
private theorem zeroDim_chart_partition_sum
    {E₀ H₀ N₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace N₀]
    [ChartedSpace H₀ N₀] [IsManifold I₀ 1 N₀] [CompactSpace N₀]
    (o : Manifold.Orientation I₀ N₀ (Fin 0)) :
    ∃ (m : ℕ) (α : Fin m → N₀) (s : Fin m → Set N₀)
      (b : Module.Basis (Fin 0) ℝ E₀),
      (∀ i, s i ⊆ {α i}) ∧ Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (⋃ i, s i) = univ ∧
      ∀ (ψ : RoughForm I₀ N₀ ℝ 0), IntegrableTopForm ψ →
        integralTopForm o ψ = ∑ i : Fin m,
          if α i ∈ s i then
            (Orientation.signBasis (o.orientationAt (α i)) b : ℝ) * ψ (α i) ![]
          else 0 := by
  have hcard : Module.finrank ℝ E₀ = 0 := by simpa using o.card_eq.symm
  have : Subsingleton E₀ := Module.finrank_zero_iff.mp hcard
  let : MeasurableSpace E₀ := borel E₀
  have : BorelSpace E₀ := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := Module.finBasisOfFinrankEq ℝ E₀ hcard
  obtain ⟨m, α, s, _, hs_sub, hdisj, huniv, hform⟩ :=
    exists_chart_partition_integralTopForm (I := I₀) (M := N₀) l b
  have hs_singleton (i : Fin m) : s i ⊆ {α i} := by
    intro x hx
    have hxs := hs_sub i hx
    have hαs : α i ∈ (extChartAt I₀ (α i)).source := mem_extChartAt_source (α i)
    exact (extChartAt I₀ (α i)).injOn hxs hαs (Subsingleton.elim _ _)
  refine ⟨m, α, s, b, hs_singleton, hdisj, huniv, fun ψ hψ ↦ ?_⟩
  rw [hform ψ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hmem : α i ∈ s i
  · have himg : (extChartAt I₀ (α i)) '' s i = {0} := by
      ext y
      constructor
      · rintro ⟨x, _, rfl⟩
        exact Subsingleton.elim _ _
      · intro hy
        rw [mem_singleton_iff.1 hy]
        exact ⟨α i, hmem, Subsingleton.elim _ _⟩
    simp only [hmem, ↓reduceIte]
    have hfn : ψ = RoughForm.ofFunction I₀ (fun x ↦ ψ x ![]) := by
      refine (RoughForm.eq_ofFunction ψ).trans ?_
      congr 1
      ext x
      congr 1
      exact Subsingleton.elim _ _
    rw [himg, Module.Basis.addHaar_eq_dirac, MeasureTheory.restrict_dirac]
    simp only [mem_singleton, ↓reduceIte, MeasureTheory.integral_dirac]
    rw [show (0 : E₀) = extChartAt I₀ (α i) (α i) from Subsingleton.elim _ _,
      RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ (mem_extChartAt_source (α i))]
    conv_lhs => rw [hfn, RoughForm.inChartAt_ofFunction]
    dsimp only
    rw [Manifold.Orientation.orientationAt_mk, Manifold.OrientationLift.signBasis_orientationAt,
      (extChartAt I₀ (α i)).left_inv (mem_extChartAt_source (α i))]
    simp only [ContinuousAlternatingMap.constOfIsEmpty_apply, Units.val_mul, Int.cast_mul]
    ring
  · have hempty : s i = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
      obtain rfl : x = α i := mem_singleton_iff.1 (hs_singleton i hx)
      exact hmem hx
    simp only [hmem, ↓reduceIte]
    rw [hempty, image_empty, MeasureTheory.setIntegral_empty, mul_zero]

/-- On a compact zero-dimensional manifold, a `0`-form is smooth and hence integrable. -/
private theorem integrableTopForm_of_zeroDim
    {E₀ H₀ N₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace N₀]
    [ChartedSpace H₀ N₀] [IsManifold I₀ 1 N₀] [CompactSpace N₀]
    (o : Manifold.Orientation I₀ N₀ (Fin 0)) (ψ : RoughForm I₀ N₀ ℝ 0) :
    IntegrableTopForm ψ := by
  have hcard : Module.finrank ℝ E₀ = 0 := by simpa using o.card_eq.symm
  have : Subsingleton E₀ := Module.finrank_zero_iff.mp hcard
  let b := Module.finBasisOfFinrankEq ℝ E₀ hcard
  have hfn : ψ = RoughForm.ofFunction I₀ (fun x ↦ ψ x ![]) := by
    refine (RoughForm.eq_ofFunction ψ).trans ?_
    congr 1
    ext x
    congr 1
    exact Subsingleton.elim _ _
  have hsm : IsSmoothForm I₀ 0 ψ := by
    rw [hfn, isSmoothForm_ofFunction_iff, contMDiff_zero_iff, continuous_iff_continuousAt]
    intro x
    have hopen : IsOpen ((extChartAt I₀ x).source) := isOpen_extChartAt_source x
    have hsub : (extChartAt I₀ x).source ⊆ {x} := fun y hy ↦
      (extChartAt I₀ x).injOn hy (mem_extChartAt_source x) (Subsingleton.elim _ _)
    have hsing : {x} = (extChartAt I₀ x).source :=
      Subset.antisymm (singleton_subset_iff.2 (mem_extChartAt_source x)) hsub
    have hopen_x : IsOpen ({x} : Set N₀) := hsing ▸ hopen
    exact (continuousAt_const (y := ψ x ![])).congr
      (Filter.eventually_of_mem (hopen_x.mem_nhds rfl) fun y hy ↦ by rw [mem_singleton_iff.1 hy])
  exact hsm.integrableTopForm (isClosed_tsupport _).isCompact b

/-- In dimension zero, the Riemannian volume form at `x` evaluates to `signBasis` of the tangent
orientation relative to any `Fin 0` basis of `E₀`. -/
private theorem zeroDim_riemannianVolumeForm_eq_signBasis
    {E₀ H₀ N₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace N₀]
    [ChartedSpace H₀ N₀] [IsManifold I₀ 1 N₀]
    [RiemannianBundle (fun x : N₀ ↦ TangentSpace I₀ x)]
    (o : Manifold.Orientation I₀ N₀ (Fin 0)) (b : Module.Basis (Fin 0) ℝ E₀) (x : N₀) :
    riemannianVolumeForm o x ![] = (Orientation.signBasis (o.orientationAt x) b : ℝ) := by
  have := o.fact_finrank_tangentSpace x
  let bT : Module.Basis (Fin 0) ℝ (TangentSpace I₀ x) := b
  rw [riemannianVolumeForm_apply]
  have hs : (Orientation.signBasis (o.orientationAt x) b : ℝ) =
      (Orientation.signBasis (o.orientationAt x) bT : ℝ) := rfl
  rw [hs]
  rcases (o.orientationAt x).eq_or_eq_neg_of_isEmpty with h | h
  · rw [h, ← Module.Basis.orientation_isEmpty bT, _root_.Orientation.signBasis_orientation]
    simp [Module.Basis.orientation_isEmpty]
  · rw [h, _root_.Orientation.signBasis_neg, ← Module.Basis.orientation_isEmpty bT,
      _root_.Orientation.signBasis_orientation]
    simp [Module.Basis.orientation_isEmpty]

/-- In dimension zero, if `riemannianVolumeForm o` is integrable, the source manifold is
compact. -/
private theorem compactSpace_of_integrableTopForm_zeroDim_volumeForm
    {E₀ H₀ N₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace N₀]
    [ChartedSpace H₀ N₀] [IsManifold I₀ 1 N₀]
    [RiemannianBundle (fun x : N₀ ↦ TangentSpace I₀ x)]
    (o : Manifold.Orientation I₀ N₀ (Fin 0))
    (hvi : IntegrableTopForm (riemannianVolumeForm o)) :
    CompactSpace N₀ := by
  refine ⟨?_⟩
  have hts : _root_.tsupport (α := E₀ [⋀^Fin 0]→L[ℝ] ℝ) (riemannianVolumeForm o) = univ := by
    refine eq_univ_iff_forall.2 fun x ↦ subset_tsupport _ ?_
    intro hz
    have h1 : (riemannianVolumeForm o x : TangentSpace I₀ x [⋀^Fin 0]→L[ℝ] ℝ) ![] =
        (0 : TangentSpace I₀ x [⋀^Fin 0]→L[ℝ] ℝ) ![] := DFunLike.congr_fun hz ![]
    have := o.fact_finrank_tangentSpace x
    rw [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, riemannianVolumeForm_apply] at h1
    exact (_root_.Orientation.volumeForm_apply_ne_zero_iff.2 linearIndependent_empty_type) h1
  rw [← hts]
  exact hvi.isCompact

private theorem zeroDim_signBasis_sq {E₀ : Type*} [AddCommGroup E₀] [Module ℝ E₀]
    (o : _root_.Orientation ℝ E₀ (Fin 0)) (b : Module.Basis (Fin 0) ℝ E₀) :
    (Orientation.signBasis o b : ℝ) ^ 2 = 1 := by
  rw [sq]
  exact_mod_cast Int.units_coe_mul_self (Orientation.signBasis o b)

private theorem zeroDim_signBasis_mul_le_one {E₀ : Type*} [AddCommGroup E₀] [Module ℝ E₀]
    (o : _root_.Orientation ℝ E₀ (Fin 0)) (b : Module.Basis (Fin 0) ℝ E₀)
    {a : ℝ} (ha : |a| ≤ 1) :
    (Orientation.signBasis o b : ℝ) * a ≤ 1 := by
  have hsq : |(Orientation.signBasis o b : ℝ)| ^ 2 = 1 := by
    rw [sq_abs]
    exact zeroDim_signBasis_sq o b
  have h1 : |(Orientation.signBasis o b : ℝ)| = 1 := by
    nlinarith [abs_nonneg (Orientation.signBasis o b : ℝ)]
  exact (le_abs_self _).trans (by rw [abs_mul, h1, one_mul]; exact ha)

end ZeroDimHelper

/-- The volume of an oriented smooth immersion is nonnegative. -/
theorem immersionVolume_nonneg {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  rcases k with - | k
  · by_cases hi : IntegrableTopForm (riemannianVolumeForm o)
    · have : CompactSpace N := compactSpace_of_integrableTopForm_zeroDim_volumeForm o hi
      obtain ⟨m, α, s, b, _, _, _, hform⟩ := zeroDim_chart_partition_sum o
      rw [hform _ hi]
      refine Finset.sum_nonneg fun i _ ↦ ?_
      split_ifs
      · rw [zeroDim_riemannianVolumeForm_eq_signBasis o b (α i), ← sq]
        exact sq_nonneg _
      · exact le_rfl
    · rw [integralTopForm_eq_zero_of_not_integrable _ _ hi]
  · exact integralTopForm_nonneg o fun x c hc ↦ by
      have := o.fact_finrank_tangentSpace x
      rw [riemannianVolumeForm_apply]
      exact (_root_.Orientation.volumeForm_apply_pos_iff.2 hc).le

/-- The volume of a nonempty compact oriented smooth immersion is positive. -/
theorem immersionVolume_pos [CompactSpace N] [Nonempty N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    0 < immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun x : N ↦ TangentSpace I' x) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  rcases k with - | k
  · obtain ⟨m, α, s, b, hs, _, huniv, hform⟩ := zeroDim_chart_partition_sum o
    rw [hform _ (integrableTopForm_of_zeroDim o _)]
    obtain ⟨x₀⟩ := ‹Nonempty N›
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 (huniv.symm ▸ mem_univ x₀)
    obtain rfl : x₀ = α i₀ := mem_singleton_iff.1 (hs i₀ hi₀)
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
    · split_ifs
      · rw [zeroDim_riemannianVolumeForm_eq_signBasis o b (α i), ← sq]
        exact sq_nonneg _
      · exact le_rfl
    · simp only [hi₀, ↓reduceIte]
      rw [zeroDim_riemannianVolumeForm_eq_signBasis o b (α i₀), ← sq,
        zeroDim_signBasis_sq (o.orientationAt (α i₀)) b]
      exact zero_lt_one
  · have : IsContMDiffRiemannianBundle I' 0 E' (fun x : N ↦ TangentSpace I' x) :=
      (IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
        (F := E') (V := fun x : N ↦ TangentSpace I' x)).toIsContMDiffZero
    have : IsManifold I' (0 + 1) N := by simpa using ‹IsManifold I' 1 N›
    obtain ⟨x₀⟩ := ‹Nonempty N›
    have := o.fact_finrank_tangentSpace x₀
    let b : OrthonormalBasis (Fin (k + 1)) ℝ (TangentSpace I' x₀) :=
      ((stdOrthonormalBasis ℝ (TangentSpace I' x₀)).reindex
        (finCongr (by simpa using o.finrank_tangentSpace_eq x₀))).adjustToOrientation
        (o.orientationAt x₀)
    have hb : b.toBasis.orientation = o.orientationAt x₀ :=
      OrthonormalBasis.orientation_adjustToOrientation _ _
    refine integralTopForm_pos o (isSmoothForm_riemannianVolumeForm o)
      (isClosed_tsupport _).isCompact
      (fun x c hc ↦ by
        have := o.fact_finrank_tangentSpace x
        rw [riemannianVolumeForm_apply]
        exact (_root_.Orientation.volumeForm_apply_pos_iff.2 hc).le)
      ⟨x₀, b.toBasis, hb, by
        rw [show riemannianVolumeForm o x₀ b.toBasis = 1 from
          riemannianVolumeForm_apply_orthonormal o x₀ b hb]
        exact zero_lt_one⟩

/-- **Integrated calibration inequality** (integrable form): if `φ` has pointwise comass at most
`1` for `g`, and both `f^* φ` and `dvol_{f^* g}` are integrable, then `∫_N f^* φ ≤ Vol(f)`. -/
theorem integralTopForm_mpullback_le_immersionVolume_of_integrable {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k}
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k))
    (hφi : IntegrableTopForm (mpullback I' I f φ))
    (hvi : letI : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
      ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
      IntegrableTopForm (riemannianVolumeForm o)) :
    integralTopForm o (mpullback I' I f φ) ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  rw [immersionVolume_def]
  rcases k with - | k
  · have : CompactSpace N := compactSpace_of_integrableTopForm_zeroDim_volumeForm o hvi
    obtain ⟨m, α, s, b, _, _, _, hform⟩ := zeroDim_chart_partition_sum o
    rw [hform _ hφi, hform _ hvi]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    split_ifs
    · rw [zeroDim_riemannianVolumeForm_eq_signBasis o b (α i), ← sq,
        zeroDim_signBasis_sq (o.orientationAt (α i)) b, mpullback_apply]
      have hemp : (fun j : Fin 0 ↦ mfderiv I' I f (α i) (![] j)) = ![] := Subsingleton.elim _ _
      rw [hemp]
      exact zeroDim_signBasis_mul_le_one (o.orientationAt (α i)) b
        (by simpa [Subsingleton.elim (fun j : Fin 0 ↦ j.elim0) ![]] using
          hcomass (f (α i)) (fun j ↦ j.elim0) fun j ↦ j.elim0)
    · exact le_rfl
  · have hnonneg : 0 ≤ integralTopForm o (riemannianVolumeForm o - mpullback I' I f φ) :=
      integralTopForm_nonneg o fun x c hc ↦ by
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_nonneg]
        exact mpullback_apply_le_riemannianVolumeForm g hcomass f hf hinj o x c hc
    rw [sub_eq_add_neg, integralTopForm_add_of_integrable o hvi hφi.neg,
      show -mpullback I' I f φ = (-1 : ℝ) • mpullback I' I f φ from (neg_one_smul ℝ _).symm,
      integralTopForm_smul, neg_one_mul, ← sub_eq_add_neg, sub_nonneg] at hnonneg
    exact hnonneg

/-- **Integrated calibration inequality** on a compact source: if `φ` is continuous with
pointwise comass at most `1` for `g`, then `∫_N f^* φ ≤ Vol(f)`. -/
theorem integralTopForm_mpullback_le_immersionVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    integralTopForm o (mpullback I' I f φ) ≤ immersionVolume g f hf hinj o := by
  let : RiemannianBundle (fun y : N ↦ TangentSpace I' y) :=
    ⟨(g.pullback f (by simpa using hf) hinj).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I' 0 E' (fun y : N ↦ TangentSpace I' y) :=
    (IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := ∞)
      (F := E') (V := fun y : N ↦ TangentSpace I' y)).toIsContMDiffZero
  have : IsManifold I' (0 + 1) N := by simpa using ‹IsManifold I' 1 N›
  let b := Module.finBasisOfFinrankEq ℝ E' (by simpa using o.card_eq.symm)
  have hφi : IntegrableTopForm (mpullback I' I f φ) :=
    (hφ.mpullback (by simpa using hf.of_le (by simp))).integrableTopForm
      (isClosed_tsupport _).isCompact b
  have hvi : IntegrableTopForm (riemannianVolumeForm o) :=
    (isSmoothForm_riemannianVolumeForm (n := 0) o).integrableTopForm
      (isClosed_tsupport _).isCompact b
  exact integralTopForm_mpullback_le_immersionVolume_of_integrable g hcomass f hf hinj o hφi hvi

/-- Absolute integrated calibration inequality on a compact source: `|∫_N f^* φ| ≤ Vol(f)`. -/
theorem abs_integralTopForm_mpullback_le_immersionVolume [CompactSpace N] {k : ℕ}
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {φ : RoughForm I M ℝ k} (hφ : IsSmoothForm I 0 φ)
    (hcomass : ∀ y (v : Fin k → TangentSpace I y),
      (∀ i j, g.inner y (v i) (v j) = if i = j then 1 else 0) → |φ y v| ≤ 1)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) :
    |integralTopForm o (mpullback I' I f φ)| ≤ immersionVolume g f hf hinj o := by
  refine abs_le.2 ⟨?_, integralTopForm_mpullback_le_immersionVolume g hφ hcomass f hf hinj o⟩
  have hneg := integralTopForm_mpullback_le_immersionVolume g hφ.neg (fun y v hv ↦ by
    simpa [abs_neg] using hcomass y v hv) f hf hinj o
  have hmp : mpullback I' I f (-φ) = (-1 : ℝ) • mpullback I' I f φ := by
    ext x v
    simp [mpullback_apply]
  rw [hmp, integralTopForm_smul, neg_one_mul] at hneg
  linarith

end Immersions

/-! ### The fundamental theorem of calibrations -/

section FundamentalTheorem

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]
  {E'' H'' N' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace N']
  [ChartedSpace H'' N'] [IsManifold I'' 1 N']

/-- **The fundamental theorem of calibrations** for closed sources: an oriented immersion `f`
calibrated by a smooth calibration `φ` has volume at most that of every compact oriented
immersion `f'` of a closed `k`-manifold that pairs with every smooth closed `k`-form as `f` does,
that is, that is homologous to `f` in real homology (Harvey–Lawson 1982, Theorem II.4.2; McLean
1998). Holds in every degree `k : ℕ`, including degree zero. -/
theorem immersionVolume_le_of_isCalibratedImmersion {k : ℕ} [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o ≤ immersionVolume g f' hf' hinj' o' := by
  calc immersionVolume g f hf hinj o
      = integralTopForm o (mpullback I' I f φ) :=
        (integralTopForm_mpullback_eq_immersionVolume g hcal).symm
    _ = integralTopForm o' (mpullback I'' I f' φ) :=
        hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero
    _ ≤ immersionVolume g f' hf' hinj' o' :=
        integralTopForm_mpullback_le_immersionVolume g (hφ.isSmoothForm.of_le (by simp))
          hφ.abs_apply_le_one f' hf' hinj' o'

/-- **Equality case of the fundamental theorem of calibrations**: under the real-homology
hypothesis on a compact competitor `f'`, `f'` attains the volume of the calibrated immersion `f`
if and only if `f'` is itself calibrated by `φ` with its orientation `o'`. -/
theorem immersionVolume_eq_iff_isCalibratedImmersion {k : ℕ} [CompactSpace N']
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (φ : RoughForm I M ℝ k)
    (hφ : IsCalibration g φ)
    (f : N → M) (hf : ContMDiff I' I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (o : Manifold.Orientation I' N (Fin k)) (hcal : IsCalibratedImmersion g φ f hf hinj o)
    (f' : N' → M) (hf' : ContMDiff I'' I ∞ f')
    (hinj' : ∀ x, Function.Injective (mfderiv I'' I f' x))
    (o' : Manifold.Orientation I'' N' (Fin k))
    (hhom : ∀ η : RoughForm I M ℝ k, IsSmoothForm I ∞ η → mextDeriv η = 0 →
      integralTopForm o (mpullback I' I f η) = integralTopForm o' (mpullback I'' I f' η)) :
    immersionVolume g f hf hinj o = immersionVolume g f' hf' hinj' o' ↔
      IsCalibratedImmersion g φ f' hf' hinj' o' := by
  refine ⟨fun heq ↦ ?_, fun hcal' ↦ ?_⟩
  · have hint : integralTopForm o' (mpullback I'' I f' φ) =
        immersionVolume g f' hf' hinj' o' := by
      rw [← heq, ← hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero,
        integralTopForm_mpullback_eq_immersionVolume g hcal]
    let : RiemannianBundle (fun y : N' ↦ TangentSpace I'' y) :=
      ⟨(g.pullback f' (by simpa using hf') hinj').toRiemannianMetric⟩
    have : IsContMDiffRiemannianBundle I'' 0 E'' (fun y : N' ↦ TangentSpace I'' y) :=
      (IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I'') (n := ∞)
        (F := E'') (V := fun y : N' ↦ TangentSpace I'' y)).toIsContMDiffZero
    have : IsManifold I'' (0 + 1) N' := by simpa using ‹IsManifold I'' 1 N'›
    rcases k with - | k
    · classical
      obtain ⟨m, α, s, b, hs, _, huniv, hform⟩ := zeroDim_chart_partition_sum o'
      have hφi := integrableTopForm_of_zeroDim o' (mpullback I'' I f' φ)
      have hvi := integrableTopForm_of_zeroDim o' (riemannianVolumeForm o')
      rw [immersionVolume_def, hform _ hφi, hform _ hvi] at hint
      -- Every active term in `mpullback` is at most the `1` in `riemannianVolumeForm`, so equality
      -- of sums forces termwise equality at every point.
      let p : Fin m → ℝ := fun i ↦ if α i ∈ s i then
        (Orientation.signBasis (o'.orientationAt (α i)) b : ℝ) * φ (f' (α i)) ![] else 0
      let q : Fin m → ℝ := fun i ↦ if α i ∈ s i then
        (Orientation.signBasis (o'.orientationAt (α i)) b : ℝ) *
          riemannianVolumeForm o' (α i) ![] else 0
      have hpq (i : Fin m) : p i ≤ q i := by
        dsimp only [p, q]
        split_ifs
        · rw [zeroDim_riemannianVolumeForm_eq_signBasis o' b (α i), ← sq,
            zeroDim_signBasis_sq (o'.orientationAt (α i)) b]
          exact zeroDim_signBasis_mul_le_one (o'.orientationAt (α i)) b
            (by simpa [Subsingleton.elim (fun j : Fin 0 ↦ j.elim0) ![]] using
              hφ.abs_apply_le_one (f' (α i)) (fun j ↦ j.elim0) fun j ↦ j.elim0)
        · exact le_rfl
      have hterm : ∀ i, p i = q i := by
        intro i
        by_contra hne
        have hlt : p i < q i := lt_of_le_of_ne (hpq i) hne
        have hsum_lt : ∑ j : Fin m, p j < ∑ j : Fin m, q j :=
          Finset.sum_lt_sum (fun j _ ↦ hpq j) ⟨i, Finset.mem_univ i, hlt⟩
        have hsum_eq : ∑ j : Fin m, p j = ∑ j : Fin m, q j := by
          have hemp (x : N') : (fun i : Fin 0 ↦ mfderiv I'' I f' x (![] i)) = ![] :=
            Subsingleton.elim _ _
          simpa [p, q, mpullback_apply, hemp] using hint
        exact hsum_lt.ne hsum_eq
      rw [isCalibratedImmersion_iff]
      ext x v
      obtain ⟨i, hi⟩ := mem_iUnion.1 (huniv.symm ▸ mem_univ x)
      obtain rfl : x = α i := mem_singleton_iff.1 (hs i hi)
      have hti := hterm i
      simp only [p, q, hi, ↓reduceIte] at hti
      have hsign_ne : ((Orientation.signBasis (o'.orientationAt (α i)) b : ℤ) : ℝ) ≠ 0 := by
        exact_mod_cast (Orientation.signBasis (o'.orientationAt (α i)) b).ne_zero
      have hval := mul_left_cancel₀ hsign_ne hti
      have hv : v = ![] := Subsingleton.elim v ![]
      have hemp : (fun j : Fin 0 ↦ mfderiv I'' I f' (α i) (![] j)) = ![] :=
        Subsingleton.elim _ _
      simpa [mpullback_apply, hv, hemp] using hval
    · rw [immersionVolume_def] at hint
      have hsm1 : IsSmoothForm I'' 0 (riemannianVolumeForm o') :=
        isSmoothForm_riemannianVolumeForm (n := 0) o'
      have hsm2 : IsSmoothForm I'' 0 (mpullback I'' I f' φ) :=
        (hφ.isSmoothForm.of_le (by simp)).mpullback (by simpa using hf'.of_le (by simp))
      have hdiff_zero :
          integralTopForm o' (riemannianVolumeForm o' - mpullback I'' I f' φ) = 0 := by
        rw [sub_eq_add_neg, integralTopForm_add_of_compactSpace o' hsm1 hsm2.neg,
          show -mpullback I'' I f' φ = (-1 : ℝ) • mpullback I'' I f' φ from (neg_one_smul ℝ _).symm,
          integralTopForm_smul, neg_one_mul, ← sub_eq_add_neg, hint, sub_self]
      have := o'.fact_finrank_tangentSpace
      rw [isCalibratedImmersion_iff_forall_orthonormal_basis]
      intro x b hb horth
      by_contra hne
      have hle : φ (f' x) (mfderiv I'' I f' x ∘ b) ≤ 1 :=
        hφ.apply_le_one (f' x) (mfderiv I'' I f' x ∘ b) horth
      have hlt : φ (f' x) (mfderiv I'' I f' x ∘ b) < 1 := lt_of_le_of_ne hle hne
      let b' : OrthonormalBasis (Fin (k + 1)) ℝ (TangentSpace I'' x) :=
        OrthonormalBasis.mk (orthonormal_iff_ite.2 fun i j ↦ by
          rw [ContMDiffRiemannianMetric.inner_riemannianBundle,
            ContMDiffRiemannianMetric.pullback_inner]
          exact horth i j)
          b.span_eq.ge
      have hb'_fun : (⇑b' : Fin (k + 1) → TangentSpace I'' x) = ⇑b := OrthonormalBasis.coe_mk _ _
      have hb_eq : b'.toBasis = b := by
        ext i
        rw [b'.coe_toBasis]
        exact congrFun hb'_fun i
      have hb' : b'.toBasis.orientation = o'.orientationAt x := hb_eq ▸ hb
      have hpos_val : 0 < (riemannianVolumeForm o' - mpullback I'' I f' φ) x b := by
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
          show riemannianVolumeForm o' x b = 1 by
            rw [← hb'_fun]
            exact riemannianVolumeForm_apply_orthonormal o' x b' hb',
          mpullback_apply]
        exact sub_pos.2 hlt
      have hsm : IsSmoothForm I'' 0 (riemannianVolumeForm o' - mpullback I'' I f' φ) := by
        rw [sub_eq_add_neg]
        exact hsm1.add hsm2.neg
      have hpos_int : 0 < integralTopForm o' (riemannianVolumeForm o' - mpullback I'' I f' φ) :=
        integralTopForm_pos o' hsm (isClosed_tsupport _).isCompact
          (fun y c hc ↦ by
            rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_nonneg]
            exact mpullback_apply_le_riemannianVolumeForm g hφ.abs_apply_le_one
              f' hf' hinj' o' y c hc)
          ⟨x, b, hb, hpos_val⟩
      linarith
  · rw [← integralTopForm_mpullback_eq_immersionVolume g hcal,
      ← integralTopForm_mpullback_eq_immersionVolume g hcal',
      hhom φ hφ.isSmoothForm hφ.mextDeriv_eq_zero]

end FundamentalTheorem

end TauCeti
