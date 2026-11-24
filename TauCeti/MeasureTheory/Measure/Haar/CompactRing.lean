/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Unique
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Haar measure on compact rings

Let `A` be a compact Hausdorff topological ring and `μ` a finite additive Haar measure on it, such
as its additive Haar probability measure. (A locally compact ring carrying a finite additive Haar
measure is compact, so the statements below assume local compactness only.)

* Multiplication by a unit, on either side, is a continuous additive automorphism of `A`, so it
  preserves `μ` (`MeasureTheory.Measure.map_mul_left_eq_self_of_isUnit`,
  `MeasureTheory.Measure.map_mul_right_eq_self_of_isUnit`, and their set-level forms
  `MeasureTheory.Measure.measure_preimage_mul_left_of_isUnit`,
  `MeasureTheory.Measure.measure_preimage_mul_right_of_isUnit`).
* If a compact group `G` embeds continuously and multiplicatively into `A` with open image `U`
  (for instance a compact open subgroup of `A^×`, or `GL_n(O)` inside `M_n(O)`), then the
  normalized Haar measure `haarProb G` is the restriction of `μ` to `U`, pulled back to `G` and
  divided by `μ U` (`MeasureTheory.Measure.haarProb_eq_smul_comap`). Indeed that measure is left
  invariant, because left multiplication by the image of `g` preserves `μ`, and it is a Haar
  probability measure.

## References

* J.-P. Serre, *Quelques applications du théorème de densité de Chebotarev*, Publ. Math. IHÉS 54
  (1981), §6.4, proof of Proposition 13.
-/

public section

open MeasureTheory Set Topology TauCeti

namespace MeasureTheory.Measure

section Units

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
  [IsFiniteMeasure μ]

/-- **Left multiplication by a unit preserves a finite additive Haar measure.** -/
theorem map_mul_left_eq_self_of_isUnit {u : A} (hu : IsUnit u) : μ.map (u * ·) = μ := by
  rw [← AddMonoidHom.coe_mulLeft]
  exact (AddMonoidHom.mulLeft u).map_addHaar_eq_self (continuous_const.mul continuous_id)
    fun y => ⟨↑hu.unit⁻¹ * y, by simp [← mul_assoc]⟩

/-- **Right multiplication by a unit preserves a finite additive Haar measure.** -/
theorem map_mul_right_eq_self_of_isUnit {u : A} (hu : IsUnit u) : μ.map (· * u) = μ := by
  rw [← AddMonoidHom.coe_mulRight]
  exact (AddMonoidHom.mulRight u).map_addHaar_eq_self (continuous_id.mul continuous_const)
    fun y => ⟨y * ↑hu.unit⁻¹, by simp [mul_assoc]⟩

/-- Left multiplication by a unit preserves the finite additive Haar measure of every set. -/
theorem measure_preimage_mul_left_of_isUnit {u : A} (hu : IsUnit u) (s : Set A) :
    μ ((u * ·) ⁻¹' s) = μ s := by
  have he : ⇑(ContinuousAddEquiv.mulLeft hu.unit : A ≃ₜ A) = (u * ·) := by ext; simp
  rw [← he, ← (ContinuousAddEquiv.mulLeft hu.unit : A ≃ₜ A).measurableEmbedding.map_apply,
    he, map_mul_left_eq_self_of_isUnit μ hu]

/-- Right multiplication by a unit preserves the finite additive Haar measure of every set. -/
theorem measure_preimage_mul_right_of_isUnit {u : A} (hu : IsUnit u) (s : Set A) :
    μ ((· * u) ⁻¹' s) = μ s := by
  have he : ⇑(ContinuousAddEquiv.mulRight hu.unit : A ≃ₜ A) = (· * u) := by ext; simp
  rw [← he, ← (ContinuousAddEquiv.mulRight hu.unit : A ≃ₜ A).measurableEmbedding.map_apply,
    he, map_mul_right_eq_self_of_isUnit μ hu]

variable [T2Space A] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **Haar measure on a compact open group of units.** Let `f` be a continuous injective
multiplicative map from a compact group `G` into a compact Hausdorff ring `A`, with open image.
Then the normalized Haar measure of `G` is a finite additive Haar measure `μ` of `A` (for
instance its Haar probability), restricted to the image of `f`, pulled back along `f` and divided
by `μ` of the image. -/
theorem haarProb_eq_smul_comap (f : G →* A) (hf : Continuous f) (hinj : Function.Injective f)
    (hopen : IsOpen (range f)) : haarProb G = (μ (range f))⁻¹ • μ.comap f := by
  have hoe : IsOpenEmbedding f := .mk (hf.isClosedEmbedding hinj).toIsEmbedding hopen
  have hemb : MeasurableEmbedding f := hoe.measurableEmbedding
  have hU0 : μ (range f) ≠ 0 := (hopen.measure_pos μ (range_nonempty f)).ne'
  have hUtop : μ (range f) ≠ ⊤ := measure_ne_top μ _
  let ν : Measure G := (μ (range f))⁻¹ • μ.comap f
  have hν (s : Set G) : ν s = (μ (range f))⁻¹ * μ (f '' s) := by
    simp [ν, hemb.comap_apply]
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν, image_univ, ENNReal.inv_mul_cancel hU0 hUtop]⟩
  have hunit (g : G) : IsUnit (f g) := (Group.isUnit g).map f
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun g => Measure.ext fun s hs => ?_⟩
    have hm : Measurable fun x : G => g * x := by fun_prop
    rw [Measure.map_apply hm hs, hν, hν]
    congr 1
    have himage : f '' ((g * ·) ⁻¹' s) = (f g * ·) ⁻¹' (f '' s) := by
      ext y
      simp only [mem_image, mem_preimage]
      refine ⟨fun ⟨x, hx, hxy⟩ => ⟨g * x, hx, by rw [map_mul, hxy]⟩, fun ⟨x, hx, hxy⟩ => ?_⟩
      refine ⟨g⁻¹ * x, by simpa using hx, ?_⟩
      rw [map_mul, hxy, ← mul_assoc, ← map_mul]
      simp
    rw [himage, measure_preimage_mul_left_of_isUnit μ (hunit g)]
  have := IsOpenPosMeasure.comap μ hoe
  have : ν.IsOpenPosMeasure := isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.2 hUtop)
  have : ν.IsHaarMeasure := { }
  exact (Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν (haarProb G)).symm

end Units

end MeasureTheory.Measure
