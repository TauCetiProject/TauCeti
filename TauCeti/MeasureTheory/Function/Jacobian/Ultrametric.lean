/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Analysis.Calculus.ApproximatesLinearOn.Ultrametric
import TauCeti.MeasureTheory.Constructions.BorelSpace.Ultra

/-!
# Change of variables for Haar measure over ultrametric spaces

Let `f` be a map between finite-dimensional normed spaces over a nonarchimedean field, injective
on a Borel set `s` and strictly differentiable at every point of `s` with an invertible derivative
`f' x`. If each `f' x` multiplies Haar measure by `J x`, then

```text
ν (f '' s) = ∫⁻ x in s, J x ∂μ.
```

Over `ℝ` this is Mathlib's `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`, with `J x =
|det f' x|`. Over a nonarchimedean local field `K`, for `μ = ν` an additive Haar measure on `K ^ d`,
the linear scaling law gives `J x = |det f' x|_K`, the normalized absolute value. The ultrametric
argument is simpler than the real one, since no error term survives on small balls.

A map approximating a linear equivalence `A` on an ultrametric closed ball maps it onto a
translate of the linear image of a ball
(`ApproximatesLinearOn.image_closedBall_eq_vadd_image_of_isUltrametricDist`), so it multiplies
the Haar measure of that ball and of each of its closed sub-balls by the scaling factor of `A`
(`ApproximatesLinearOn.measure_image_closedBall_eq_mul_of_isUltrametricDist`). By strict
differentiability, `f` approximates `f' x` on a small closed ball around each point `x` of `s`,
and is injective there. On such a ball the scaling factor `J` is constant along `s`, and since
closed balls of an ultrametric space are nested or disjoint, they form a π-system generating the
Borel sets (`IsUltrametricDist.borel_eq_generateFrom_closedBall`), so the image measure agrees
with `J x • μ` on the whole ball. Countably many such balls cover `s`.

## Main results

* `ApproximatesLinearOn.measure_image_closedBall_eq_mul_of_isUltrametricDist`: the measure of the
  image of an ultrametric closed ball under a map approximating a linear equivalence.
* `MeasureTheory.lintegral_eq_addHaar_image_of_isUltrametricDist`: the change of variables
  formula for a map injective on a Borel set, with invertible strict derivatives on it.
* `MeasureTheory.lintegral_eq_addHaar_image_of_isUltrametricDist_of_analyticOnNhd`: the same
  for an analytic map with invertible derivatives.

## References

* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic Groups and Number Theory*, 2nd ed.,
  Vol. I (2023), §3.1, Theorem 3.2 and Proposition 3.3.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. **58** (2012),
  §4.
-/

public section

open Set Metric Filter Topology MeasureTheory Measure
open scoped NNReal ENNReal Pointwise

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ApproximatesLinearOn

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- **The Haar measure of the image of an ultrametric closed ball.** If `f` approximates a linear
equivalence `A` on `closedBall x r` as in `image_closedBall_eq_vadd_image_of_isUltrametricDist`,
and `A` multiplies the Haar measure of `closedBall 0 r` by `J`, then `f` multiplies the Haar
measure of `closedBall x r` by `J`. -/
theorem measure_image_closedBall_eq_mul_of_isUltrametricDist [IsUltrametricDist E] [CompleteSpace E]
    (μ : Measure E) [μ.IsAddLeftInvariant] (ν : Measure F) [ν.IsAddLeftInvariant] {f : E → F}
    {A : E ≃L[𝕜] F} {x : E} {r : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (A : E →L[𝕜] F) (closedBall x r) c)
    (hc : ‖(A.symm : F →L[𝕜] E)‖₊ * c < 1) {J : ℝ≥0∞}
    (hJ : ν (A '' closedBall 0 r) = J * μ (closedBall 0 r)) :
    ν (f '' closedBall x r) = J * μ (closedBall x r) := by
  rw [hf.image_closedBall_eq_vadd_image_of_isUltrametricDist hc, measure_vadd, hJ,
    ← vadd_closedBall_zero r x, measure_vadd]

end ApproximatesLinearOn

namespace MeasureTheory

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

section ChangeOfVariables

variable [IsUltrametricDist E] [ProperSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (ν : Measure F) [ν.IsAddHaarMeasure] {f : E → F} {f' : E → E ≃L[𝕜] F} {J : E → ℝ≥0∞}

/-- A closed ball around `x` of positive radius on which `f` approximates `f' x` closely enough
for `ApproximatesLinearOn.image_closedBall_eq_vadd_image_of_isUltrametricDist`. -/
private def IsGoodBall (f : E → F) (f' : E → E ≃L[𝕜] F) (x : E) (r : ℝ) : Prop :=
  0 < r ∧ ∃ c : ℝ≥0, ‖((f' x).symm : F →L[𝕜] E)‖₊ * c < 1 ∧
    ApproximatesLinearOn f (f' x : E →L[𝕜] F) (closedBall x r) c

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist E]
  [ProperSpace E] in
/-- Every point with an invertible strict derivative is the centre of a good ball. -/
private theorem exists_isGoodBall {x : E} (hf' : HasStrictFDerivAt f (f' x : E →L[𝕜] F) x) :
    ∃ r, IsGoodBall f f' x r := by
  set N := ‖((f' x).symm : F →L[𝕜] E)‖₊
  have hN : 0 < N + 1 := by positivity
  obtain ⟨s, hs, hfs⟩ := hf'.approximates_deriv_on_nhds (Or.inr (inv_pos.2 hN))
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  refine ⟨ε / 2, half_pos hε, (N + 1)⁻¹, ?_,
    hfs.mono_set ((closedBall_subset_ball (half_lt_self hε)).trans hεs)⟩
  rw [← div_eq_mul_inv]
  exact (div_lt_one hN).2 (lt_add_one N)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist E]
  [ProperSpace E] in
/-- A map is injective on a good ball. -/
private theorem injOn_of_isGoodBall {x : E} {r : ℝ} (hgood : IsGoodBall f f' x r) :
    InjOn f (closedBall x r) := by
  obtain ⟨-, c, hc, hf⟩ := hgood
  exact hf.injOn ((f' x).subsingleton_or_nnNorm_symm_pos.imp id fun hpos ↦
    (NNReal.lt_inv_iff_mul_lt hpos.ne').2 (mul_comm c _ ▸ hc))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist E]
  [ProperSpace E] in
/-- A map is continuous on a good ball. -/
private theorem continuousOn_of_isGoodBall {x : E} {r : ℝ} (hgood : IsGoodBall f f' x r) :
    ContinuousOn f (closedBall x r) :=
  hgood.2.choose_spec.2.continuousOn

include μ ν in
/-- On a good ball around `x`, every closed sub-ball has image measure `J x` times its measure. -/
private theorem image_closedBall_of_isGoodBall {x : E} (hJ : ∀ s, ν (f' x '' s) = J x * μ s)
    {r : ℝ} (hgood : IsGoodBall f f' x r) {y : E} (hy : y ∈ closedBall x r) {t : ℝ}
    (ht : t ≤ r) : ν (f '' closedBall y t) = J x * μ (closedBall y t) := by
  obtain ⟨-, c, hc, hf⟩ := hgood
  have hsub : closedBall y t ⊆ closedBall x r :=
    (closedBall_subset_closedBall ht).trans (IsUltrametricDist.closedBall_eq_of_mem hy).symm.subset
  exact (hf.mono_set hsub).measure_image_closedBall_eq_mul_of_isUltrametricDist μ ν hc (hJ _)

include μ ν in
/-- The scaling factor at a point `y` of a good ball around `x` is the one at `x`. -/
private theorem scale_eq_of_isGoodBall {x y : E} (hJx : ∀ s, ν (f' x '' s) = J x * μ s)
    (hJy : ∀ s, ν (f' y '' s) = J y * μ s) (hf' : HasStrictFDerivAt f (f' y : E →L[𝕜] F) y)
    {r : ℝ} (hgood : IsGoodBall f f' x r) (hy : y ∈ closedBall x r) : J y = J x := by
  obtain ⟨r', hgood'⟩ := exists_isGoodBall hf'
  have ht : 0 < min r r' := lt_min hgood.1 hgood'.1
  have h1 := image_closedBall_of_isGoodBall μ ν hJx hgood hy (min_le_left r r')
  have h2 := image_closedBall_of_isGoodBall μ ν hJy hgood'
    (mem_closedBall_self hgood'.1.le) (min_le_right r r')
  rw [h2] at h1
  exact (ENNReal.mul_left_inj (measure_closedBall_pos μ y ht).ne'
    measure_closedBall_lt_top.ne).1 h1

/-- The image measure `s ↦ ν (f '' (s ∩ U))` on `E`, for `f` continuous and injective on a
measurable set `U`. -/
private noncomputable def imageMeasure (U : Set E) (f : E → F) : Measure E :=
  (ν.comap (U.domRestrict f)).map ((↑) : U → E)

omit [IsUltrametricDist E] [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] in
private theorem imageMeasure_apply {U : Set E} (hU : MeasurableSet U) (hcont : ContinuousOn f U)
    (hinj : InjOn f U) (s : Set E) : imageMeasure ν U f s = ν (f '' (s ∩ U)) := by
  have he := hcont.measurableEmbedding hU hinj
  rw [imageMeasure, (MeasurableEmbedding.subtypeVal hU).map_apply, he.comap_apply,
    image_domRestrict]

include μ in
/-- On a good ball `D` around `x`, the image measure of `f` on `D` is `J x • μ` on `D`. -/
private theorem imageMeasure_of_isGoodBall {x : E} (hJ : ∀ s, ν (f' x '' s) = J x * μ s) {r : ℝ}
    (hgood : IsGoodBall f f' x r) :
    imageMeasure ν (closedBall x r) f = (J x • μ).restrict (closedBall x r) := by
  set D := closedBall x r
  have hcont : ContinuousOn f D := continuousOn_of_isGoodBall hgood
  have happly : ∀ s, imageMeasure ν D f s = ν (f '' (s ∩ D)) :=
    imageMeasure_apply ν measurableSet_closedBall hcont (injOn_of_isGoodBall hgood)
  -- On a closed ball `B`, the intersection `B ∩ D` is empty, `D`, or a sub-ball of `D`.
  have hball : ∀ y t, 0 < t → ν (f '' (closedBall y t ∩ D)) = J x * μ (closedBall y t ∩ D) := by
    intro y t ht
    by_cases hy : y ∈ D
    · have hinter : closedBall y t ∩ D = closedBall y (min t r) := by
        simp only [D, IsUltrametricDist.closedBall_eq_of_mem hy]
        ext z
        simp [mem_closedBall, le_min_iff]
      rw [hinter]
      exact image_closedBall_of_isGoodBall μ ν hJ hgood hy (min_le_right t r)
    rcases IsUltrametricDist.closedBall_subset_trichotomy (x := y) (y := x) (r := t) (s := r)
      with h | h | h
    · exact absurd (h (mem_closedBall_self ht.le)) hy
    · rw [inter_eq_right.2 h]
      exact image_closedBall_of_isGoodBall μ ν hJ hgood (mem_closedBall_self hgood.1.le) le_rfl
    · have hD : closedBall y t ∩ D = ∅ := h.inter_eq
      simp [hD]
  have : IsFiniteMeasure (imageMeasure ν D f) := by
    refine ⟨?_⟩
    rw [happly univ, univ_inter]
    exact ((isCompact_closedBall x r).image_of_continuousOn hcont).measure_lt_top
  refine ext_of_generate_finite _
    ((BorelSpace.measurable_eq).trans IsUltrametricDist.borel_eq_generateFrom_closedBall)
    IsUltrametricDist.isPiSystem_closedBall ?_ ?_
  · rintro _ ⟨y, t, ht, rfl⟩
    rw [happly, hball y t ht, Measure.restrict_apply measurableSet_closedBall, smul_apply,
      smul_eq_mul]
  · rw [happly, Measure.restrict_apply MeasurableSet.univ, smul_apply, smul_eq_mul, univ_inter]
    exact image_closedBall_of_isGoodBall μ ν hJ hgood (mem_closedBall_self hgood.1.le) le_rfl

/-- **Change of variables for Haar measure over an ultrametric space.** Let `f` be injective on a
measurable subset `s` of a proper ultrametric normed space `E`, with an invertible strict
derivative `f' x` at every `x ∈ s`, and let `f' x` multiply Haar measure by `J x`, in the sense
that `ν (f' x '' t) = J x * μ t` for every set `t`. Then `∫⁻ x in s, J x ∂μ = ν (f '' s)`.

Over a nonarchimedean local field `K`, with `μ = ν` an additive Haar measure on `K ^ d`, the
linear scaling law makes `J x = |det f' x|_K`; for two different normalizations, `J x` also
carries their ratio. -/
theorem lintegral_eq_addHaar_image_of_isUltrametricDist {s : Set E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasStrictFDerivAt f (f' x : E →L[𝕜] F) x) (hinj : InjOn f s)
    (hJ : ∀ x ∈ s, ∀ t, ν (f' x '' t) = J x * μ t) : ∫⁻ x in s, J x ∂μ = ν (f '' s) := by
  have hcont : ContinuousOn f s := fun z hz ↦ (hf' z hz).continuousAt.continuousWithinAt
  -- Countably many good balls cover `s`; with the complement of their union they cover `E`.
  choose! r hr using fun x (hx : x ∈ s) ↦ exists_isGoodBall (hf' x hx)
  obtain ⟨T, hTs, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable s
    (fun x ↦ closedBall x (r x)) fun x hx ↦ IsUltrametricDist.isOpen_closedBall _ (hr x hx).1.ne'
  set V := ⋃ x ∈ T, closedBall x (r x)
  have hVm : MeasurableSet V := MeasurableSet.biUnion hTc fun _ _ ↦ measurableSet_closedBall
  have hsV : s ⊆ V := fun x hx ↦ hTU ▸ mem_biUnion hx (mem_closedBall_self (hr x hx).1.le)
  have hext : imageMeasure ν s f = (μ.withDensity J).restrict s := by
    refine ext_of_sUnion_eq_univ (S := insert Vᶜ ((fun x ↦ closedBall x (r x)) '' T))
      ((hTc.image _).insert _) ?_ ?_
    · rw [sUnion_insert, sUnion_image, compl_union_self]
    rintro D (rfl | ⟨x, hx, rfl⟩)
    · ext t ht
      have hempty : t ∩ Vᶜ ∩ s = ∅ := eq_empty_of_forall_notMem fun z hz ↦ hz.1.2 (hsV hz.2)
      rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
        imageMeasure_apply ν hs hcont hinj, Measure.restrict_apply (ht.inter hVm.compl), hempty]
      simp
    have hgood := hr x (hTs hx)
    ext t ht
    have h := congrArg (· (t ∩ s)) (imageMeasure_of_isGoodBall μ ν (hJ x (hTs hx)) hgood)
    rw [imageMeasure_apply ν measurableSet_closedBall (continuousOn_of_isGoodBall hgood)
      (injOn_of_isGoodBall hgood), Measure.restrict_apply (ht.inter hs), smul_apply,
      smul_eq_mul] at h
    have hm : MeasurableSet (t ∩ closedBall x (r x) ∩ s) :=
      (ht.inter measurableSet_closedBall).inter hs
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht, imageMeasure_apply ν hs hcont hinj,
      Measure.restrict_apply (ht.inter measurableSet_closedBall), withDensity_apply _ hm]
    -- On the good ball the density `J` is constant, equal to `J x`.
    calc ν (f '' (t ∩ closedBall x (r x) ∩ s))
        = J x * μ (t ∩ closedBall x (r x) ∩ s) := by rwa [inter_right_comm]
      _ = ∫⁻ _ in t ∩ closedBall x (r x) ∩ s, J x ∂μ := by rw [setLIntegral_const, mul_comm]
      _ = ∫⁻ y in t ∩ closedBall x (r x) ∩ s, J y ∂μ :=
        setLIntegral_congr_fun hm fun y hy ↦
          (scale_eq_of_isGoodBall μ ν (hJ x (hTs hx)) (hJ y hy.2) (hf' y hy.2) hgood hy.1.2).symm
  rw [← inter_self s, ← imageMeasure_apply ν hs hcont hinj, hext, Measure.restrict_apply hs,
    withDensity_apply _ (hs.inter hs), inter_self]

/-- **Change of variables for Haar measure under an analytic map over an ultrametric space.**
Let `f` be analytic and injective on a measurable subset `s` of a proper ultrametric normed space
`E`, with invertible derivative `f' x` at every `x ∈ s`, and let `f' x` multiply Haar measure by
`J x`. Then `∫⁻ x in s, J x ∂μ = ν (f '' s)`. -/
theorem lintegral_eq_addHaar_image_of_isUltrametricDist_of_analyticOnNhd {s : Set E}
    (hs : MeasurableSet s) (hf : AnalyticOnNhd 𝕜 f s)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x : E →L[𝕜] F) x) (hinj : InjOn f s)
    (hJ : ∀ x ∈ s, ∀ t, ν (f' x '' t) = J x * μ t) :
    ∫⁻ x in s, J x ∂μ = ν (f '' s) :=
  lintegral_eq_addHaar_image_of_isUltrametricDist μ ν hs
    (fun x hx ↦ (hf' x hx).fderiv ▸ (hf x hx).hasStrictFDerivAt) hinj hJ

end ChangeOfVariables

end MeasureTheory
