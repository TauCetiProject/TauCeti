/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ZeroDim
import TauCeti.Geometry.Manifold.Riemannian.FormMetric
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# Integrating functions and top forms against the Riemannian volume form

On an oriented Riemannian manifold `M`, a function `f : M → ℝ` is integrated as the top form
`f vol`, where `vol = TauCeti.riemannianVolumeForm o` is the Riemannian volume form of the
orientation `o`: `∫_M f vol = integralTopForm o (fun x ↦ f x • vol x)`. This file records the
basic properties of this integral that pointwise estimates need: it is nonnegative on nonnegative
functions, it commutes with constant factors, and on a compact manifold it is additive and
monotone on continuous functions. Thus a pointwise inequality `f ≤ g` between continuous functions
integrates to `∫_M f vol ≤ ∫_M g vol`.

In every dimension `m : ℕ` (including `m = 0`), the integral of `vol` itself is nonnegative, forces
compactness of `M` when integrable, is strictly positive on nonempty compact `M` for a continuous
metric, and is independent of the choice of orientation `o`. Moreover, on a compact manifold with a
continuous Riemannian metric, any rough top form `η` bounded by `1` in absolute value on orthonormal
frames satisfies `∫_M η ≤ ∫_M vol` and `|∫_M η| ≤ ∫_M vol`, and for continuous `η` equality holds
if and only if `η = vol`.

## Main results

* `TauCeti.compactSpace_of_integrableTopForm_riemannianVolumeForm` and
  `TauCeti.integrableTopForm_riemannianVolumeForm_iff_compactSpace`: integrability of `vol`
  characterizes compactness of `M`.
* `TauCeti.integralTopForm_riemannianVolumeForm_nonneg`,
  `TauCeti.integralTopForm_riemannianVolumeForm_pos`, and
  `TauCeti.integralTopForm_riemannianVolumeForm_congr`: nonnegativity, strict positivity on
  nonempty compact manifolds, and orientation independence of `∫_M vol` in all dimensions.
* `TauCeti.integralTopForm_le_riemannianVolumeForm`,
  `TauCeti.abs_integralTopForm_le_riemannianVolumeForm`, and
  `TauCeti.integralTopForm_eq_riemannianVolumeForm_iff`: integrated comass bounds and equality
  characterization against `vol` on compact manifolds.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_nonneg`: `0 ≤ f` gives `0 ≤ ∫_M f vol`.
* `TauCeti.integralTopForm_mul_smul_riemannianVolumeForm`: `∫_M c f vol = c ∫_M f vol`.
* `TauCeti.isSmoothForm_zero_riemannianVolumeForm`,
  `TauCeti.isSmoothForm_smul_riemannianVolumeForm`: for a continuous metric, `vol` is a continuous
  top form, and so is `f vol` when `f` is continuous.
* `TauCeti.integralTopForm_add_smul_riemannianVolumeForm`: on a compact manifold,
  `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_mono`: on a compact manifold, `f ≤ g`
  gives `∫_M f vol ≤ ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.abs_integralTopForm_inner_smul_riemannianVolumeForm_le`: on a compact manifold, the
  `L²` pairing of continuous forms satisfies `|∫_M ⟨α, β⟩ vol| ≤ K ∫_M |β| vol` when `|α| ≤ K`
  pointwise.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6 and Proposition 15.29.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ} (o : Manifold.Orientation I M (Fin m))

/-- Because `riemannianVolumeForm o` vanishes nowhere, its integrability forces compactness of the
manifold. -/
theorem compactSpace_of_integrableTopForm_riemannianVolumeForm
    (h : IntegrableTopForm (riemannianVolumeForm o)) : CompactSpace M :=
  ⟨by simpa using h.isCompact⟩

/-- On a noncompact manifold, `riemannianVolumeForm o` is not compactly supported, so its
`integralTopForm` evaluates to `0`. -/
theorem integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace
    (h : ¬ CompactSpace M) :
    integralTopForm o (riemannianVolumeForm o) = 0 :=
  integralTopForm_eq_zero_of_not_integrable o _ fun hi ↦
    h (compactSpace_of_integrableTopForm_riemannianVolumeForm o hi)

/-- In every dimension `m : ℕ` (including `m = 0`), the integral of the Riemannian volume form is
nonnegative. -/
theorem integralTopForm_riemannianVolumeForm_nonneg :
    0 ≤ integralTopForm o (riemannianVolumeForm o) := by
  classical
  by_cases hi : IntegrableTopForm (riemannianVolumeForm o)
  · have : CompactSpace M := compactSpace_of_integrableTopForm_riemannianVolumeForm o hi
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    let σ : Fin (Module.finrank ℝ E) ≃ Fin m := finCongr (by simpa using o.card_eq.symm)
    let b := (Module.finBasis ℝ E).reindex σ
    obtain ⟨l, rfl, hl⟩ := o.exists_lift_modelOrientation_eq b.orientation
    obtain ⟨_, α, s, _, _, _, _, hform⟩ := exists_chart_partition_integralTopForm l b
    rw [hform _ hi, hl, _root_.Orientation.signBasis_orientation, Units.val_one, Int.cast_one,
      one_mul]
    refine Finset.sum_nonneg fun i _ ↦ integral_nonneg fun y ↦ ?_
    by_cases hy : y ∈ (extChartAt I (α i)).target
    · have h := signBasis_mul_signedInChartAt_smul_riemannianVolumeForm l σ (fun _ ↦ (1 : ℝ))
        (α i) ((extChartAt I (α i)).map_target hy)
      simp only [hl, b, _root_.Orientation.signBasis_orientation, Units.val_one, Int.cast_one,
        one_mul, one_smul, (extChartAt I (α i)).right_inv hy, mul_one] at h
      rw [h]
      exact chartVolumeDensity_nonneg _ _
    · rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, Pi.zero_apply]
  · rw [integralTopForm_eq_zero_of_not_integrable _ _ hi]

private theorem zeroDim_summand_le (o : Manifold.Orientation I M (Fin 0))
    (b : Module.Basis (Fin 0) ℝ E) {η : RoughForm I M ℝ 0} (x : M)
    (hcomass : ∀ v : Fin 0 → TangentSpace I x, Orthonormal ℝ v → |η x v| ≤ 1) :
    (Orientation.signBasis (o.orientationAt x) b : ℝ) * η x ![] ≤
      (Orientation.signBasis (o.orientationAt x) b : ℝ) * riemannianVolumeForm o x ![] := by
  have hbdd : |η x ![]| ≤ 1 := hcomass ![] (orthonormal_iff_ite.2 fun i ↦ i.elim0)
  rw [riemannianVolumeForm_zeroDim_apply_eq_signBasis o b x ![]]
  rcases Int.units_eq_one_or (Orientation.signBasis (o.orientationAt x) b) with hs | hs
  · rw [hs, Units.val_one, Int.cast_one, one_mul, one_mul]
    exact (le_abs_self _).trans hbdd
  · rw [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul, neg_one_mul,
      neg_neg]
    exact (neg_le_abs _).trans hbdd

section ContinuousMetric

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous Riemannian metric, `riemannianVolumeForm o` is integrable if and only if the
manifold is compact. -/
theorem integrableTopForm_riemannianVolumeForm_iff_compactSpace :
    IntegrableTopForm (riemannianVolumeForm o) ↔ CompactSpace M := by
  refine ⟨compactSpace_of_integrableTopForm_riemannianVolumeForm o, fun h ↦ ?_⟩
  have : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact (isSmoothForm_riemannianVolumeForm (n := 0) o).integrableTopForm
    (by simp [h.isCompact_univ])
    (Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm))

/-- On a nonempty compact oriented Riemannian manifold of any dimension `m : ℕ`, the integral of the
Riemannian volume form is strictly positive. -/
theorem integralTopForm_riemannianVolumeForm_pos [CompactSpace M] [Nonempty M] :
    0 < integralTopForm o (riemannianVolumeForm o) := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  rw [integralTopForm_riemannianVolumeForm o]
  exact riemannianTotalVolume_pos

/-- For a continuous Riemannian metric, the integral of the Riemannian volume form does not depend
on the choice of orientation (even across disconnected components or noncompact manifolds). -/
theorem integralTopForm_riemannianVolumeForm_congr
    (o₁ o₂ : Manifold.Orientation I M (Fin m)) :
    integralTopForm o₁ (riemannianVolumeForm o₁) =
      integralTopForm o₂ (riemannianVolumeForm o₂) := by
  by_cases hc : CompactSpace M
  · let : MeasurableSpace M := borel M
    have : BorelSpace M := ⟨rfl⟩
    rw [integralTopForm_riemannianVolumeForm o₁, integralTopForm_riemannianVolumeForm o₂]
  · rw [integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o₁ hc,
      integralTopForm_riemannianVolumeForm_eq_zero_of_not_compactSpace o₂ hc]

/-- **Integrated comass inequality** on a compact oriented Riemannian manifold: in every dimension
`m : ℕ`, if a rough top form `η` has absolute value at most `1` on orthonormal frames everywhere,
then `∫_M η ≤ ∫_M dvol_g`. When `η` is not integrable, the left-hand side evaluates to `0` by
`integralTopForm`'s compact-support fallback and the bound holds by nonnegativity of
`∫_M dvol_g`. -/
theorem integralTopForm_le_riemannianVolumeForm [CompactSpace M] {η : RoughForm I M ℝ m}
    (hcomass : ∀ x (v : Fin m → TangentSpace I x), Orthonormal ℝ v → |η x v| ≤ 1) :
    integralTopForm o η ≤ integralTopForm o (riemannianVolumeForm o) := by
  by_cases hηi : IntegrableTopForm η
  · rcases m with - | m
    · have hcard : Module.finrank ℝ E = 0 := by simpa using o.card_eq.symm
      have : Subsingleton E := Module.finrank_zero_iff.mp hcard
      have : DiscreteTopology M := I.discreteTopology M
      have : Finite M := finite_of_compact_of_discrete
      let : Fintype M := Fintype.ofFinite M
      let b := Module.finBasisOfFinrankEq ℝ E hcard
      rw [integralTopForm_finite_zeroDim o b, integralTopForm_finite_zeroDim o b]
      exact Finset.sum_le_sum fun x _ ↦ zeroDim_summand_le o b x (hcomass x)
    · have hvi : IntegrableTopForm (riemannianVolumeForm o) :=
        (integrableTopForm_riemannianVolumeForm_iff_compactSpace o).2 inferInstance
      have hnonneg : 0 ≤ integralTopForm o (riemannianVolumeForm o - η) :=
        integralTopForm_nonneg o fun x c hc ↦ by
          rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_nonneg]
          exact apply_le_riemannianVolumeForm o x (η x) (hcomass x) c hc
      rwa [integralTopForm_sub_of_integrable o hvi hηi, sub_nonneg] at hnonneg
  · rw [integralTopForm_eq_zero_of_not_integrable o _ hηi]
    exact integralTopForm_riemannianVolumeForm_nonneg o

/-- Absolute integrated comass inequality on a compact oriented Riemannian manifold: in every
dimension `m : ℕ`, if `|η(v)| ≤ 1` on orthonormal frames everywhere, then `|∫_M η| ≤ ∫_M dvol_g`. -/
theorem abs_integralTopForm_le_riemannianVolumeForm [CompactSpace M] {η : RoughForm I M ℝ m}
    (hcomass : ∀ x (v : Fin m → TangentSpace I x), Orthonormal ℝ v → |η x v| ≤ 1) :
    |integralTopForm o η| ≤ integralTopForm o (riemannianVolumeForm o) := by
  refine abs_le.2 ⟨?_, integralTopForm_le_riemannianVolumeForm o hcomass⟩
  have hneg := integralTopForm_le_riemannianVolumeForm o (η := -η)
    fun x v hv ↦ by simpa [abs_neg] using hcomass x v hv
  rw [← neg_one_smul ℝ η, integralTopForm_smul, neg_one_mul] at hneg
  linarith

/-- **Equality case of the integrated comass inequality** on a compact oriented Riemannian manifold:
for a continuous top form `η` (`IsSmoothForm I 0 η`) bounded by `1` in absolute value on orthonormal
frames everywhere, `∫_M η = ∫_M dvol_g` holds if and only if `η = dvol_g`. -/
theorem integralTopForm_eq_riemannianVolumeForm_iff [CompactSpace M] {η : RoughForm I M ℝ m}
    (hη : IsSmoothForm I 0 η)
    (hcomass : ∀ x (v : Fin m → TangentSpace I x), Orthonormal ℝ v → |η x v| ≤ 1) :
    integralTopForm o η = integralTopForm o (riemannianVolumeForm o) ↔
      η = riemannianVolumeForm o := by
  refine ⟨fun hint ↦ ?_, fun h ↦ by rw [h]⟩
  rcases m with - | m
  · have hcard : Module.finrank ℝ E = 0 := by simpa using o.card_eq.symm
    have : Subsingleton E := Module.finrank_zero_iff.mp hcard
    have : DiscreteTopology M := I.discreteTopology M
    have : Finite M := finite_of_compact_of_discrete
    let : Fintype M := Fintype.ofFinite M
    let b := Module.finBasisOfFinrankEq ℝ E hcard
    rw [integralTopForm_finite_zeroDim o b, integralTopForm_finite_zeroDim o b] at hint
    ext x v
    have hterm := (Finset.sum_eq_sum_iff_of_le fun y _ ↦
      zeroDim_summand_le o b y (hcomass y)).1 hint x (Finset.mem_univ x)
    have hsign_ne : ((Orientation.signBasis (o.orientationAt x) b : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast (Orientation.signBasis (o.orientationAt x) b).ne_zero
    rw [Subsingleton.elim v ![]]
    exact mul_left_cancel₀ hsign_ne hterm
  · have : IsContMDiffRiemannianBundle I 0 E (fun y : M ↦ TangentSpace I y) :=
      Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero
    have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
    let b₀ := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
    have hsm1 : IsSmoothForm I 0 (riemannianVolumeForm o) :=
      isSmoothForm_riemannianVolumeForm (n := 0) o
    have hvi : IntegrableTopForm (riemannianVolumeForm o) :=
      (integrableTopForm_riemannianVolumeForm_iff_compactSpace o).2 inferInstance
    have hηi : IntegrableTopForm η :=
      hη.integrableTopForm (isClosed_tsupport _).isCompact b₀
    have hdiff_zero : integralTopForm o (riemannianVolumeForm o - η) = 0 := by
      rw [integralTopForm_sub_of_integrable o hvi hηi, hint, sub_self]
    ext x v
    obtain ⟨b, hb, hb_orth⟩ := o.exists_basis_orientationAt_eq_and_orthonormal x
    suffices hval : η x b = 1 from
      DFunLike.congr_fun
        (eq_riemannianVolumeForm_of_apply_of_orthonormal o x (η x) b hb hb_orth hval) v
    by_contra hne
    have hlt : η x b < 1 := lt_of_le_of_ne ((le_abs_self _).trans (hcomass x b hb_orth)) hne
    have hpos_val : 0 < (riemannianVolumeForm o - η) x b := by
      rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
        riemannianVolumeForm_apply_of_orthonormal o x b hb hb_orth]
      exact sub_pos.2 hlt
    have hsm : IsSmoothForm I 0 (riemannianVolumeForm o - η) := by
      rw [sub_eq_add_neg]
      exact hsm1.add hη.neg
    have hpos_int : 0 < integralTopForm o (riemannianVolumeForm o - η) :=
      integralTopForm_pos o hsm (isClosed_tsupport _).isCompact
        (fun y c hc ↦ by
          rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, sub_nonneg]
          exact apply_le_riemannianVolumeForm o y (η y) (hcomass y) c hc)
        ⟨x, b, hb, hpos_val⟩
    linarith

end ContinuousMetric

/-- The integral `∫_M f vol` of a nonnegative function against the Riemannian volume form is
nonnegative, on an oriented Riemannian manifold of positive dimension. -/
theorem integralTopForm_smul_riemannianVolumeForm_nonneg [NeZero m] {f : M → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) :=
  integralTopForm_smul_nonneg o (fun x c hc ↦ (riemannianVolumeForm_apply_pos o x c hc).le) hf

/-- Constant factors come out of the integral against the Riemannian volume form:
`∫_M c f vol = c ∫_M f vol`. -/
theorem integralTopForm_mul_smul_riemannianVolumeForm (c : ℝ) (f : M → ℝ) :
    integralTopForm o (fun x ↦ (c * f x) • riemannianVolumeForm o x) =
      c * integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) :=
  integralTopForm_mul_smul o c f _

section Continuous

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous metric, the Riemannian volume form is a continuous top form. -/
theorem isSmoothForm_zero_riemannianVolumeForm : IsSmoothForm I 0 (riemannianVolumeForm o) := by
  -- `isSmoothForm_riemannianVolumeForm` asks for a `C^(n + 1)` manifold; at `n = 0` instance
  -- search does not reduce `0 + 1` to the `1` of the ambient `IsManifold I 1 M`.
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact isSmoothForm_riemannianVolumeForm o

/-- For a continuous function `f`, the top form `f vol` is continuous. -/
theorem isSmoothForm_smul_riemannianVolumeForm {f : M → ℝ} (hf : Continuous f) :
    IsSmoothForm I 0 (fun x ↦ f x • riemannianVolumeForm o x) :=
  (isSmoothForm_zero_riemannianVolumeForm o).fun_smul_of_continuous hf

variable [CompactSpace M]

/-- On a compact oriented Riemannian manifold, the integral against the Riemannian volume form is
additive on continuous functions: `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol`. -/
theorem integralTopForm_add_smul_riemannianVolumeForm {f g : M → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    integralTopForm o (fun x ↦ (f x + g x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) +
        integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) :=
  integralTopForm_add_smul_of_compactSpace o (isSmoothForm_zero_riemannianVolumeForm o) hf hg

/-- **Monotonicity of the integral against the Riemannian volume form**: on a compact oriented
Riemannian manifold of positive dimension, continuous functions with `f ≤ g` satisfy
`∫_M f vol ≤ ∫_M g vol`. -/
theorem integralTopForm_smul_riemannianVolumeForm_mono [NeZero m] {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) :=
  integralTopForm_smul_mono_of_compactSpace o (isSmoothForm_zero_riemannianVolumeForm o)
    (fun x c hc ↦ (riemannianVolumeForm_apply_pos o x c hc).le) hf hg hfg

/-- **The `L²` pairing against a bounded form.** On a compact oriented Riemannian manifold, if a
continuous `k`-form `α` has pointwise norm `|α| = √⟨α, α⟩ ≤ K`, then its `L²` pairing with a
continuous `k`-form `β` satisfies `|∫_M ⟨α, β⟩ vol| ≤ K ∫_M |β| vol`. This is the fibrewise
Cauchy–Schwarz inequality `|⟨α, β⟩| ≤ |α| |β|`, integrated against the Riemannian measure. -/
theorem abs_integralTopForm_inner_smul_riemannianVolumeForm_le {k : ℕ}
    {α β : RoughForm I M ℝ k} (hα : IsSmoothForm I 0 α) (hβ : IsSmoothForm I 0 β) {K : ℝ}
    (hαK : ∀ x, √(alternatingFormInner (TangentSpace I x) k (α x) (α x)) ≤ K) :
    |integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) k (α x) (β x) • riemannianVolumeForm o x)| ≤
      K * integralTopForm o (fun x ↦
        √(alternatingFormInner (TangentSpace I x) k (β x) (β x)) • riemannianVolumeForm o x) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have hαβ := (hα.contMDiff_alternatingFormInner hβ).continuous
  have hg : Continuous fun x ↦ K * √(alternatingFormInner (TangentSpace I x) k (β x) (β x)) :=
    continuous_const.mul (hβ.contMDiff_alternatingFormInner hβ).continuous.sqrt
  -- Fibrewise Cauchy–Schwarz: `|⟨α, β⟩| ≤ |α| |β| ≤ K |β|`.
  have hpt (x : M) : |alternatingFormInner (TangentSpace I x) k (α x) (β x)| ≤
      K * √(alternatingFormInner (TangentSpace I x) k (β x) (β x)) :=
    (α x).abs_alternatingFormInner_le_sqrt_mul_sqrt (β x) |>.trans
      (mul_le_mul_of_nonneg_right (hαK x) (Real.sqrt_nonneg _))
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0)
  rw [← integralTopForm_mul_smul_riemannianVolumeForm,
    integralTopForm_smul_riemannianVolumeForm o hαβ (.of_compactSpace _),
    integralTopForm_smul_riemannianVolumeForm o hg (.of_compactSpace _), ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hg.integrable_of_hasCompactSupport (.of_compactSpace _))
    (ae_of_all _ hpt)

end Continuous

end TauCeti
